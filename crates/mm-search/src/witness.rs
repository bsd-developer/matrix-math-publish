//! Search witness records (spec §10.8, §12.3).
//!
//! §10.8 fixes what a successful witness must record: worker ID, worker seed,
//! step number, pre-move state digest, the move, and the post-move decomposition
//! digest. That set is exactly what replay level R2 needs to recreate the same
//! CPU search state and reach the same witness at the same step (§12.3).
//!
//! Wall-clock time is deliberately **not** a replay coordinate (§12.3).

use crate::rng::{RNG_ALGORITHM, Seed256};
use mm_core::dims::TensorMode;
use mm_core::error::push_json_string;
use mm_core::hex::encode_hex;

/// A local move on a decomposition state (§10.5).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Move {
    /// A flip (B2) on the pair `(first, second)` sharing their factor in `mode`.
    Flip {
        /// The tensor mode whose factor the two terms share.
        mode: TensorMode,
        /// Index of the term that receives the summed factor.
        first: usize,
        /// Index of the term that receives the differenced factor.
        second: usize,
    },
    /// A plus transition (B4) splitting one term into two sum-equivalent terms.
    ///
    /// §10.5 disables these in the baseline; a witness that contains one was
    /// produced by a configuration that explicitly enabled them.
    Plus {
        /// The tensor mode whose factor was split.
        mode: TensorMode,
        /// Index of the term that was split.
        index: usize,
    },
    /// A reduction (B3) combining two terms that share their other two factors.
    Reduction {
        /// The tensor mode whose factors are added.
        mode: TensorMode,
        /// Index of the retained term.
        first: usize,
        /// Index of the absorbed term.
        second: usize,
    },
}

impl Move {
    /// The canonical name used in witnesses and reports.
    #[must_use]
    pub const fn kind(self) -> &'static str {
        match self {
            Self::Flip { .. } => "flip",
            Self::Plus { .. } => "plus",
            Self::Reduction { .. } => "reduction",
        }
    }

    /// The tensor mode this move acts on.
    #[must_use]
    pub const fn mode(self) -> TensorMode {
        match self {
            Self::Flip { mode, .. } | Self::Reduction { mode, .. } | Self::Plus { mode, .. } => {
                mode
            }
        }
    }

    /// The term indices involved.
    #[must_use]
    pub const fn indices(self) -> (usize, usize) {
        match self {
            Self::Flip { first, second, .. } | Self::Reduction { first, second, .. } => {
                (first, second)
            }
            Self::Plus { index, .. } => (index, index),
        }
    }
}

/// One recorded step of a successful walk (§10.8).
#[derive(Clone, Debug)]
pub struct WitnessStep {
    /// The step number within this worker's walk.
    pub step: u64,
    /// The state digest before the move.
    pub pre_digest: [u8; 32],
    /// The move applied.
    pub applied: Move,
    /// The state digest after the move and renormalization.
    pub post_digest: [u8; 32],
    /// The term count after the move.
    pub term_count: usize,
}

/// A complete successful witness (§10.8).
#[derive(Clone, Debug)]
pub struct Witness {
    /// The worker that found it.
    pub worker: u32,
    /// That worker's derived seed.
    pub worker_seed: Seed256,
    /// The restart index within the worker's schedule.
    pub restart: u64,
    /// The step at which the target was reached.
    pub step: u64,
    /// The term count reached.
    pub term_count: usize,
    /// The final state digest.
    pub state_digest: [u8; 32],
    /// The move history leading to the witness.
    pub steps: Vec<WitnessStep>,
}

impl Witness {
    /// Render the witness as canonical JSON with sorted keys.
    #[must_use]
    pub fn to_canonical_json(&self) -> String {
        let mut out = String::from("{\"rng_algorithm\":");
        push_json_string(&mut out, RNG_ALGORITHM);
        out.push_str(",\"restart\":");
        out.push_str(&self.restart.to_string());
        out.push_str(",\"schema\":\"matrix-math-witness/1\",\"state_digest\":");
        push_json_string(&mut out, &encode_hex(&self.state_digest));
        out.push_str(",\"step\":");
        out.push_str(&self.step.to_string());
        out.push_str(",\"steps\":[");
        for (index, step) in self.steps.iter().enumerate() {
            if index > 0 {
                out.push(',');
            }
            out.push_str("{\"applied\":");
            push_json_string(&mut out, step.applied.kind());
            out.push_str(",\"indices\":[");
            let (first, second) = step.applied.indices();
            out.push_str(&first.to_string());
            out.push(',');
            out.push_str(&second.to_string());
            out.push_str("],\"mode\":");
            push_json_string(&mut out, step.applied.mode().name());
            out.push_str(",\"post_digest\":");
            push_json_string(&mut out, &encode_hex(&step.post_digest));
            out.push_str(",\"pre_digest\":");
            push_json_string(&mut out, &encode_hex(&step.pre_digest));
            out.push_str(",\"step\":");
            out.push_str(&step.step.to_string());
            out.push_str(",\"term_count\":");
            out.push_str(&step.term_count.to_string());
            out.push('}');
        }
        out.push_str("],\"term_count\":");
        out.push_str(&self.term_count.to_string());
        out.push_str(",\"worker\":");
        out.push_str(&self.worker.to_string());
        out.push_str(",\"worker_seed\":");
        push_json_string(&mut out, &encode_hex(&self.worker_seed));
        out.push('}');
        out
    }
}
