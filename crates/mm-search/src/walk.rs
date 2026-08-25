//! The uniform flip-graph random walk (spec §10.5, §10.6, §10.8, §14.6).
//!
//! §10.8 fixes the first search implementation: independent uniform random walks
//! over valid flips with deterministic restarts, one worker per configured
//! performance-core budget, no shared mutable search state, an evaluation-count
//! stopping rule for replay, and a wall-clock safety limit that checkpoints but
//! does not define deterministic progress.
//!
//! Learned guidance is not implemented and is not implementable from here: §10.8
//! defers it until the uniform baseline passes M3, and H6 measures it against
//! exactly this walk.
//!
//! The walk is untrusted. Its output is a candidate; the claim begins when the
//! exact certificate is accepted.

use crate::f2::{F2State, F2Term, F2Vec};
use crate::rng::{ChaCha20Rng, Seed256, derive_worker_seed};
use crate::witness::{Move, Witness, WitnessStep};
use mm_core::codes::ErrorCode;
use mm_core::dims::{MatMulInstance, TensorMode};
use mm_core::error::{CoreError, CoreResult};
use std::collections::HashMap;

/// The two modes other than `mode`, in canonical `A < B < C` order (§10.5).
const fn other_modes(mode: TensorMode) -> [TensorMode; 2] {
    match mode {
        TensorMode::A => [TensorMode::B, TensorMode::C],
        TensorMode::B => [TensorMode::A, TensorMode::C],
        TensorMode::C => [TensorMode::A, TensorMode::B],
    }
}

/// Configuration for one walk (§9.5, §10.8).
#[derive(Clone, Copy, Debug)]
pub struct WalkConfig {
    /// The instance being searched.
    pub instance: MatMulInstance,
    /// The term count that counts as success.
    pub target_terms: usize,
    /// The evaluation budget, which is the deterministic stopping rule (§10.8).
    pub step_budget: u64,
    /// Steps without improvement before a deterministic restart (§10.8).
    pub restart_interval: u64,
    /// Whether to verify the tensor invariant after every move.
    ///
    /// §12.5 requires the incremental invariant in debug search builds, and a
    /// full reconstruction at a configurable interval to validate the
    /// incremental checker itself.
    pub verify_every_move: bool,
    /// How often to run a full reconstruction check (0 disables).
    pub full_check_interval: u64,
    /// Whether plus transitions are enabled. §10.5 disables them in the baseline
    /// and enables them only by explicit config.
    pub allow_plus: bool,
    /// Steps without improvement before a plus transition is attempted.
    ///
    /// Only consulted when `allow_plus` is set. A plus transition raises the term
    /// count by one, which is how a walk leaves a plateau that flips alone cannot
    /// escape; the reductions that follow are what bring it back down further.
    pub plus_interval: u64,
    /// The largest term count a plus transition may grow the state to.
    ///
    /// Without a ceiling the walk drifts upward indefinitely, since raising the
    /// count is always available and lowering it is not.
    pub max_terms: usize,
    /// Where a deterministic restart resumes from.
    pub restart_policy: RestartPolicy,
}

/// Where a deterministic restart resumes from (§10.8).
///
/// Both policies are fully determined by `(seed, step)`, so either keeps replay
/// level R2. They differ only in how the walk diversifies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RestartPolicy {
    /// Resume from the naive `n*m*p`-term state. Maximum diversification, but it
    /// discards every reduction the walk has already found.
    Naive,
    /// Resume from the best state seen so far. Keeps hard-won reductions at the
    /// cost of exploring a narrower region.
    Best,
}

impl WalkConfig {
    /// A baseline configuration for one instance and target.
    #[must_use]
    pub const fn new(instance: MatMulInstance, target_terms: usize, step_budget: u64) -> Self {
        Self {
            instance,
            target_terms,
            step_budget,
            // Plateau walking is the mechanism: reductions are rare and appear
            // only after long stretches at constant term count. A short restart
            // interval throws that progress away, so the default is generous.
            restart_interval: 250_000,
            verify_every_move: false,
            full_check_interval: 100_000,
            allow_plus: false,
            plus_interval: 20_000,
            max_terms: usize::MAX,
            restart_policy: RestartPolicy::Best,
        }
    }
}

/// How a walk finished.
#[derive(Clone, Debug)]
pub enum WalkOutcome {
    /// The target term count was reached.
    Success(Box<Witness>),
    /// The step budget was exhausted without reaching the target.
    ///
    /// §8.4: research failure is not an implementation blocker. An exhausted run
    /// is an honest negative result and still records its best state.
    Exhausted {
        /// The best term count seen.
        best_terms: usize,
        /// The best state's digest.
        best_digest: [u8; 32],
        /// Steps actually taken.
        steps: u64,
    },
}

/// A replayable checkpoint of one worker's walk (§13.2, §12.3 R2).
#[derive(Clone, Debug)]
pub struct WalkSnapshot {
    /// The worker identifier.
    pub worker: u32,
    /// The derived worker seed.
    pub worker_seed: Seed256,
    /// The ChaCha20 block counter, which is the RNG state.
    pub rng_counter: u32,
    /// Steps taken.
    pub steps: u64,
    /// Restart index.
    pub restart: u64,
    /// Steps since the last improvement.
    pub since_improvement: u64,
    /// The current state's terms.
    pub state_terms: Vec<F2Term>,
    /// The best state's terms.
    pub best_terms: Vec<F2Term>,
}

/// A single-worker flip-graph walk.
pub struct Walk {
    config: WalkConfig,
    worker: u32,
    worker_seed: Seed256,
    rng: ChaCha20Rng,
    state: F2State,
    best: F2State,
    steps: u64,
    restart: u64,
    since_improvement: u64,
    history: Vec<WitnessStep>,
    /// Reused grouping buffer, so the hot loop allocates nothing.
    scratch: Vec<(F2Vec, u32)>,
    plus_moves: u64,
}

impl Walk {
    /// Start a walk for one worker, deriving its seed per §10.8.
    ///
    /// # Errors
    ///
    /// Propagates instance failures.
    pub fn new(config: WalkConfig, master_seed: Seed256, worker: u32) -> CoreResult<Self> {
        let worker_seed = derive_worker_seed(master_seed, worker);
        let state = F2State::naive(config.instance)?;
        Ok(Self {
            config,
            worker,
            worker_seed,
            rng: ChaCha20Rng::from_seed(worker_seed),
            best: state.clone(),
            state,
            steps: 0,
            restart: 0,
            since_improvement: 0,
            history: Vec::new(),
            scratch: Vec::new(),
            plus_moves: 0,
        })
    }

    /// The current state.
    #[must_use]
    pub const fn state(&self) -> &F2State {
        &self.state
    }

    /// The best state seen so far.
    #[must_use]
    pub const fn best(&self) -> &F2State {
        &self.best
    }

    /// Steps taken so far, which is the deterministic replay coordinate (§12.3).
    #[must_use]
    pub const fn steps(&self) -> u64 {
        self.steps
    }

    /// Enumerate every valid flip from a state (§10.5).
    ///
    /// A flip needs two terms sharing their factor in one mode. Grouping by that
    /// factor makes enumeration linear in the number of resulting moves rather
    /// than quadratic in the term count.
    #[must_use]
    pub fn enumerate_flips(state: &F2State) -> Vec<Move> {
        let mut moves = Vec::new();
        for mode in TensorMode::ALL {
            let mut groups: HashMap<F2Vec, Vec<usize>> = HashMap::new();
            for (index, term) in state.terms().iter().enumerate() {
                groups.entry(term.factor(mode)).or_default().push(index);
            }
            let mut keys: Vec<&F2Vec> = groups.keys().collect();
            // Deterministic enumeration order: the move list must not depend on
            // hash iteration order, or replay would break (§13.3).
            keys.sort_unstable();
            for key in keys {
                let Some(members) = groups.get(key) else {
                    continue;
                };
                for &first in members {
                    for &second in members {
                        if first != second {
                            moves.push(Move::Flip {
                                mode,
                                first,
                                second,
                            });
                        }
                    }
                }
            }
        }
        moves
    }

    /// Every valid flip, produced by the sampler rather than the reference
    /// enumerator. Used by the §17.4 reference comparison test.
    #[must_use]
    pub fn sample_all_flips(state: &F2State) -> Vec<Move> {
        let mut scratch = Vec::new();
        let counts = Self::count_flips(state, &mut scratch);
        let total: u64 = counts.iter().sum();
        (0..total)
            .filter_map(|index| Self::select_flip(state, &mut scratch, counts, index))
            .collect()
    }

    /// Split one term into two sum-equivalent terms (§10.5, B4).
    ///
    /// `a ⊗ b ⊗ c = a ⊗ b ⊗ c' + a ⊗ b ⊗ (c - c')`. Over `𝔽₂` subtraction is
    /// addition, so the complement of `c'` within `c` is `c + c'`. Restricting
    /// `c'` to a nonempty proper subset of `supp(c)` keeps both halves nonzero,
    /// so the move genuinely adds a term rather than producing a degenerate one
    /// that normalization would drop.
    ///
    /// Returns `None` when the chosen factor has fewer than two support
    /// coordinates, which admits no such split.
    fn sample_plus(
        state: &F2State,
        rng: &mut ChaCha20Rng,
        lengths: [usize; 3],
    ) -> Option<(usize, TensorMode, F2Vec)> {
        if state.term_count() == 0 {
            return None;
        }
        let index = rng.below(state.term_count() as u64) as usize;
        let term = *state.terms().get(index)?;
        let mode = match rng.below(3) {
            0 => TensorMode::A,
            1 => TensorMode::B,
            _ => TensorMode::C,
        };
        let len = *lengths.get(mode.index())?;
        let factor = term.factor(mode);
        let support: Vec<usize> = (0..len).filter(|bit| factor.get(*bit)).collect();
        if support.len() < 2 {
            return None;
        }
        // Draw a uniform nonempty proper subset of the support by rejection.
        for _ in 0..64 {
            let mut part = F2Vec::ZERO;
            let mut chosen = 0usize;
            for bit in &support {
                if rng.below(2) == 1 {
                    part.set(*bit);
                    chosen += 1;
                }
            }
            if chosen > 0 && chosen < support.len() {
                return Some((index, mode, part));
            }
        }
        None
    }

    /// Find one available reduction, if any (§10.5, B3).
    ///
    /// Two terms sharing their other two factors combine into one. Over `𝔽₂` a
    /// duplicated pair cancels entirely, which is the reduction that makes the
    /// term count fall by two.
    #[must_use]
    pub fn find_reduction(state: &F2State) -> Option<Move> {
        for mode in TensorMode::ALL {
            let [left, right] = other_modes(mode);
            let mut groups: HashMap<(F2Vec, F2Vec), Vec<usize>> = HashMap::new();
            for (index, term) in state.terms().iter().enumerate() {
                groups
                    .entry((term.factor(left), term.factor(right)))
                    .or_default()
                    .push(index);
            }
            let mut keys: Vec<&(F2Vec, F2Vec)> = groups.keys().collect();
            keys.sort_unstable();
            for key in keys {
                if let Some(members) = groups.get(key)
                    && let (Some(&first), Some(&second)) = (members.first(), members.get(1))
                {
                    return Some(Move::Reduction {
                        mode,
                        first,
                        second,
                    });
                }
            }
        }
        None
    }

    /// Apply one move, returning the new term list.
    ///
    /// # Errors
    ///
    /// Returns [`ErrorCode::ReconstructionMismatch`] when the move's precondition
    /// does not hold, which would break the sum-preserving guarantee.
    pub fn apply(state: &F2State, applied: Move) -> CoreResult<Vec<F2Term>> {
        let mut terms = state.terms().to_vec();
        let (first, second) = applied.indices();
        let (Some(&a), Some(&b)) = (terms.get(first), terms.get(second)) else {
            return Err(CoreError::new(
                ErrorCode::ReconstructionMismatch,
                "a move referenced a term index that does not exist",
            )
            .equation("§10.5"));
        };
        match applied {
            Move::Flip { mode, .. } => {
                if a.factor(mode) != b.factor(mode) {
                    return Err(CoreError::new(
                        ErrorCode::ReconstructionMismatch,
                        "a flip requires the two terms to share the named factor",
                    )
                    .equation("B2"));
                }
                let [y_mode, z_mode] = other_modes(mode);
                // (s, y1, z1) + (s, y2, z2) -> (s, y1+y2, z1) + (s, y2, z2-z1).
                // Over F2 subtraction is addition, so both updates are XORs.
                let new_first = a.with_factor(y_mode, a.factor(y_mode).xor(b.factor(y_mode)));
                let new_second = b.with_factor(z_mode, b.factor(z_mode).xor(a.factor(z_mode)));
                if let Some(slot) = terms.get_mut(first) {
                    *slot = new_first;
                }
                if let Some(slot) = terms.get_mut(second) {
                    *slot = new_second;
                }
            }
            Move::Plus { .. } => {
                // A plus transition changes the term count, so it is applied by
                // `apply_plus` rather than through the two-index rewrite path.
                return Err(CoreError::new(
                    ErrorCode::ReconstructionMismatch,
                    "a plus transition is applied by apply_plus, not by the pair rewrite",
                )
                .equation("B4"));
            }
            Move::Reduction { mode, .. } => {
                let [left, right] = other_modes(mode);
                if a.factor(left) != b.factor(left) || a.factor(right) != b.factor(right) {
                    return Err(CoreError::new(
                        ErrorCode::ReconstructionMismatch,
                        "a reduction requires the two terms to share their other two factors",
                    )
                    .equation("B3"));
                }
                let combined = a.with_factor(mode, a.factor(mode).xor(b.factor(mode)));
                if let Some(slot) = terms.get_mut(first) {
                    *slot = combined;
                }
                // Removing the absorbed term keeps indices below `second` stable.
                terms.remove(second);
            }
        }
        Ok(terms)
    }

    /// Apply reductions until none remain, which never increases the term count.
    ///
    /// # Errors
    ///
    /// Propagates move failures.
    pub fn reduce_fully(&mut self) -> CoreResult<u64> {
        let mut applied = 0u64;
        while let Some(reduction) = Self::find_reduction(&self.state) {
            let pre = self.state.digest();
            let terms = Self::apply(&self.state, reduction)?;
            self.state.set_terms(terms);
            self.history.push(WitnessStep {
                step: self.steps,
                pre_digest: pre,
                applied: reduction,
                post_digest: self.state.digest(),
                term_count: self.state.term_count(),
            });
            applied += 1;
        }
        Ok(applied)
    }

    fn restart(&mut self) -> CoreResult<()> {
        self.restart += 1;
        self.since_improvement = 0;
        // A restart never reseeds: the RNG keeps advancing, so the whole
        // trajectory stays a function of (seed, step) and replay is unaffected.
        self.state = match self.config.restart_policy {
            RestartPolicy::Naive => F2State::naive(self.config.instance)?,
            RestartPolicy::Best => self.best.clone(),
        };
        self.history.clear();
        Ok(())
    }

    /// Count the valid flips from a state without materializing them.
    ///
    /// Returns the per-mode counts and leaves `scratch` holding the grouping for
    /// the last mode examined; [`Self::select_flip`] repeats the grouping for the
    /// chosen mode. Grouping is done by sorting a reused buffer rather than by
    /// building a hash map, which keeps the hot loop allocation-free.
    fn count_flips(state: &F2State, scratch: &mut Vec<(F2Vec, u32)>) -> [u64; 3] {
        let mut counts = [0u64; 3];
        for (slot, mode) in TensorMode::ALL.into_iter().enumerate() {
            Self::group(state, mode, scratch);
            let mut total = 0u64;
            let mut run = 0u64;
            let mut previous: Option<F2Vec> = None;
            for (factor, _) in scratch.iter() {
                if previous == Some(*factor) {
                    run += 1;
                } else {
                    total += run * run.saturating_sub(1);
                    run = 1;
                    previous = Some(*factor);
                }
            }
            total += run * run.saturating_sub(1);
            counts[slot] = total;
        }
        counts
    }

    fn group(state: &F2State, mode: TensorMode, scratch: &mut Vec<(F2Vec, u32)>) {
        scratch.clear();
        for (index, term) in state.terms().iter().enumerate() {
            scratch.push((term.factor(mode), index as u32));
        }
        scratch.sort_unstable();
    }

    /// Select the `target`-th valid flip in canonical enumeration order.
    fn select_flip(
        state: &F2State,
        scratch: &mut Vec<(F2Vec, u32)>,
        counts: [u64; 3],
        target: u64,
    ) -> Option<Move> {
        let mut remaining = target;
        for (slot, mode) in TensorMode::ALL.into_iter().enumerate() {
            let available = counts[slot];
            if remaining >= available {
                remaining -= available;
                continue;
            }
            Self::group(state, mode, scratch);
            let mut start = 0usize;
            while start < scratch.len() {
                let factor = scratch[start].0;
                let mut end = start + 1;
                while end < scratch.len() && scratch[end].0 == factor {
                    end += 1;
                }
                let size = (end - start) as u64;
                let pairs = size * size.saturating_sub(1);
                if remaining < pairs {
                    // Ordered pairs (a,b) with a != b, in row-major order.
                    let row = remaining / size.saturating_sub(1).max(1);
                    let mut column = remaining % size.saturating_sub(1).max(1);
                    if column >= row {
                        column += 1;
                    }
                    let first = scratch[start + row as usize].1 as usize;
                    let second = scratch[start + column as usize].1 as usize;
                    return Some(Move::Flip {
                        mode,
                        first,
                        second,
                    });
                }
                remaining -= pairs;
                start = end;
            }
            return None;
        }
        None
    }

    /// A replayable snapshot of the walk (§13.2).
    ///
    /// §13.2 requires a checkpoint to include the algorithm state, every worker
    /// RNG state, step counters, and the current best candidate. The config hash
    /// and tool versions are added by the harness that writes the checkpoint.
    #[must_use]
    pub fn snapshot(&self) -> WalkSnapshot {
        WalkSnapshot {
            worker: self.worker,
            worker_seed: self.worker_seed,
            rng_counter: self.rng.counter(),
            steps: self.steps,
            restart: self.restart,
            since_improvement: self.since_improvement,
            state_terms: self.state.terms().to_vec(),
            best_terms: self.best.terms().to_vec(),
        }
    }

    /// Restore a walk from a snapshot.
    ///
    /// # Errors
    ///
    /// Propagates state construction failures.
    pub fn restore(config: WalkConfig, snapshot: &WalkSnapshot) -> CoreResult<Self> {
        let state = F2State::new(config.instance, snapshot.state_terms.clone())?;
        let best = F2State::new(config.instance, snapshot.best_terms.clone())?;
        Ok(Self {
            config,
            worker: snapshot.worker,
            worker_seed: snapshot.worker_seed,
            rng: ChaCha20Rng::with_nonce(snapshot.worker_seed, [0u8; 12], snapshot.rng_counter),
            state,
            best,
            steps: snapshot.steps,
            restart: snapshot.restart,
            since_improvement: snapshot.since_improvement,
            history: Vec::new(),
            scratch: Vec::new(),
            plus_moves: 0,
        })
    }

    /// Run at most `slice` further steps, so the harness can checkpoint and
    /// enforce a wall-clock safety limit between slices (§13.2, §10.8).
    ///
    /// A wall-clock limit checkpoints but never defines deterministic progress:
    /// the step counter does (§10.8).
    ///
    /// # Errors
    ///
    /// Propagates move and invariant failures.
    pub fn run_slice(&mut self, slice: u64) -> CoreResult<Option<WalkOutcome>> {
        let deadline = self
            .steps
            .saturating_add(slice)
            .min(self.config.step_budget);
        let saved = self.config.step_budget;
        self.config.step_budget = deadline;
        let outcome = self.run()?;
        self.config.step_budget = saved;
        match outcome {
            WalkOutcome::Success(witness) => Ok(Some(WalkOutcome::Success(witness))),
            WalkOutcome::Exhausted { .. } if self.steps >= saved => {
                Ok(Some(WalkOutcome::Exhausted {
                    best_terms: self.best.term_count(),
                    best_digest: self.best.digest(),
                    steps: self.steps,
                }))
            }
            WalkOutcome::Exhausted { .. } => Ok(None),
        }
    }

    /// Run the walk to success or budget exhaustion.
    ///
    /// # Errors
    ///
    /// Propagates move and invariant failures. An invariant failure is a defect
    /// in the search, not a research outcome, so it is an error rather than an
    /// exhausted run.
    pub fn run(&mut self) -> CoreResult<WalkOutcome> {
        self.reduce_fully()?;
        self.record_best();

        while self.steps < self.config.step_budget {
            if self.state.term_count() <= self.config.target_terms {
                return Ok(WalkOutcome::Success(Box::new(self.witness())));
            }

            let counts = Self::count_flips(&self.state, &mut self.scratch);
            let total: u64 = counts.iter().sum();
            if total == 0 {
                self.restart()?;
                continue;
            }
            let choice = self.rng.below(total);
            let Some(selected) = Self::select_flip(&self.state, &mut self.scratch, counts, choice)
            else {
                self.restart()?;
                continue;
            };

            let pre = self.state.digest();
            let terms = Self::apply(&self.state, selected)?;
            self.state.set_terms(terms);
            self.steps += 1;
            self.history.push(WitnessStep {
                step: self.steps,
                pre_digest: pre,
                applied: selected,
                post_digest: self.state.digest(),
                term_count: self.state.term_count(),
            });

            self.reduce_fully()?;

            if self.config.verify_every_move && !self.state.reconstructs()? {
                return Err(CoreError::new(
                    ErrorCode::ReconstructionMismatch,
                    "a move broke the tensor invariant",
                )
                .equation("§12.5")
                .value(self.state.digest_hex()));
            }
            if self.config.full_check_interval > 0
                && self.steps.is_multiple_of(self.config.full_check_interval)
                && !self.state.reconstructs()?
            {
                return Err(CoreError::new(
                    ErrorCode::ReconstructionMismatch,
                    "the periodic full reconstruction check failed",
                )
                .equation("§12.5")
                .value(self.state.digest_hex()));
            }

            if self.state.term_count() < self.best.term_count() {
                self.record_best();
                self.since_improvement = 0;
            } else {
                self.since_improvement += 1;
                if self.config.allow_plus
                    && self.config.plus_interval > 0
                    && self
                        .since_improvement
                        .is_multiple_of(self.config.plus_interval)
                    && self.state.term_count() < self.config.max_terms
                {
                    self.apply_plus()?;
                } else if self.since_improvement >= self.config.restart_interval {
                    self.restart()?;
                }
            }
        }

        Ok(WalkOutcome::Exhausted {
            best_terms: self.best.term_count(),
            best_digest: self.best.digest(),
            steps: self.steps,
        })
    }

    /// Apply one plus transition, growing the state by a term (§10.5, B4).
    ///
    /// # Errors
    ///
    /// Propagates mode-length failures.
    fn apply_plus(&mut self) -> CoreResult<()> {
        let lengths = self.state.mode_lengths()?;
        let Some((index, mode, part)) = Self::sample_plus(&self.state, &mut self.rng, lengths)
        else {
            return Ok(());
        };
        let mut terms = self.state.terms().to_vec();
        let Some(&term) = terms.get(index) else {
            return Ok(());
        };
        let remainder = term.factor(mode).xor(part);
        if part.is_zero() || remainder.is_zero() {
            return Ok(());
        }
        let pre = self.state.digest();
        if let Some(slot) = terms.get_mut(index) {
            *slot = term.with_factor(mode, part);
        }
        terms.push(term.with_factor(mode, remainder));
        self.state.set_terms(terms);
        self.plus_moves += 1;
        self.history.push(WitnessStep {
            step: self.steps,
            pre_digest: pre,
            applied: Move::Plus { mode, index },
            post_digest: self.state.digest(),
            term_count: self.state.term_count(),
        });
        Ok(())
    }

    /// The number of plus transitions applied, reported for provenance.
    #[must_use]
    pub const fn plus_moves(&self) -> u64 {
        self.plus_moves
    }

    fn record_best(&mut self) {
        if self.state.term_count() <= self.best.term_count() {
            self.best = self.state.clone();
        }
    }

    fn witness(&self) -> Witness {
        Witness {
            worker: self.worker,
            worker_seed: self.worker_seed,
            restart: self.restart,
            step: self.steps,
            term_count: self.state.term_count(),
            state_digest: self.state.digest(),
            steps: self.history.clone(),
        }
    }
}
