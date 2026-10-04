import MatrixMath.Spec.Instance
import Std.Data.HashMap.Lemmas

/-!
# Exact finite-distribution collection bridges

These equalities retain the reference association lists' last-occurrence key
order, including keys with zero or negative weight. They require no probabilistic
well-formedness assumption. They justify replacing intermediate raw expansions
by collected distributions only at observers that provably cannot distinguish them.
-/

namespace MatrixMath.Spec.Dist.Compact

variable {κ : Type} [DecidableEq κ]

@[simp] theorem at_cons (a : κ) (w : ℚ) (d : Dist κ) (k : κ) :
    Dist.at' ((a, w) :: d) k = (if a = k then w else 0) + d.at' k := by
  by_cases h : a = k <;> simp [Dist.at', h]

theorem at_map_nodup (ks : List κ) (hn : ks.Nodup) (f : κ → ℚ) (k : κ) :
    Dist.at' (ks.map fun x => (x, f x)) k = if k ∈ ks then f k else 0 := by
  induction ks with
  | nil => simp [Dist.at']
  | cons a ks ih =>
    obtain ⟨ha, hks⟩ := List.nodup_cons.mp hn
    rw [List.map_cons, at_cons, ih hks]
    by_cases hak : a = k
    · subst a; simp [ha]
    · simp [hak, Ne.symm hak]

theorem at_zero_of_missing (d : Dist κ) (k : κ) (h : k ∉ d.map Prod.fst) :
    d.at' k = 0 := by
  induction d with
  | nil => simp [Dist.at']
  | cons p d ih =>
    obtain ⟨a, w⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [at_cons, ih h.2]
    simp [Ne.symm h.1]

theorem keys_collect (d : Dist κ) : (Dist.collect d).keys = d.keys := by
  simp only [Dist.keys, Dist.collect, List.map_map, Function.comp_def,
    List.map_id', List.dedup_idem]

theorem at_collect (d : Dist κ) (k : κ) : (Dist.collect d).at' k = d.at' k := by
  have hn : d.keys.Nodup := List.nodup_dedup _
  rw [Dist.collect, at_map_nodup _ hn _ k]
  by_cases h : k ∈ d.keys
  · simp [h]
  · have hz : d.at' k = 0 := at_zero_of_missing d k (by simpa [Dist.keys] using h)
    simp [h, hz]

theorem collect_eq_of_keys_at (d e : Dist κ) (hkeys : d.keys = e.keys)
    (hat : ∀ k, d.at' k = e.at' k) : Dist.collect d = Dist.collect e := by
  unfold Dist.collect
  rw [hkeys]
  apply List.map_congr_left
  intro k _
  simp only [hat]

theorem collect_idempotent (d : Dist κ) : Dist.collect (Dist.collect d) = Dist.collect d := by
  exact collect_eq_of_keys_at _ _ (keys_collect d) (at_collect d)


end MatrixMath.Spec.Dist.Compact

namespace MatrixMath.Spec.Dist.Compact
variable {κ : Type} [DecidableEq κ]

def eval (d : Dist κ) (f : κ → ℚ) : ℚ := (d.map fun p => p.2 * f p.1).sum

theorem sum_single (ks : List κ) (hn : ks.Nodup) (a : κ) (v : ℚ) :
    (ks.map fun k => if a = k then v else 0).sum = if a ∈ ks then v else 0 := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    obtain ⟨hk, hks⟩ := List.nodup_cons.mp hn
    by_cases h : a = k
    · subst k; simp [ih hks, hk]
    · simp [h, ih hks]

theorem eval_as_at (ks : List κ) (hn : ks.Nodup) (d : Dist κ)
    (hsub : d.map Prod.fst ⊆ ks) (f : κ → ℚ) :
    (ks.map fun k => d.at' k * f k).sum = eval d f := by
  induction d with
  | nil => simp [Dist.at', eval]
  | cons p d ih =>
    obtain ⟨a, w⟩ := p
    have ha : a ∈ ks := hsub (by simp)
    have hd : d.map Prod.fst ⊆ ks := by
      intro x hx; exact hsub (by simp [hx])
    simp only [at_cons, add_mul]
    rw [List.sum_map_add, ih hd]
    have hs : (ks.map fun k => (if a = k then w else 0) * f k).sum = w * f a := by
      have he : (fun k => (if a = k then w else 0) * f k) =
          (fun k => if a = k then w * f a else 0) := by
        funext k; by_cases h : a = k <;> simp [h]
      rw [he, sum_single ks hn a (w * f a), if_pos ha]
    rw [hs]
    rfl

theorem eval_collect (d : Dist κ) (f : κ → ℚ) : eval (Dist.collect d) f = eval d f := by
  simpa only [Dist.collect, eval, List.map_map, Function.comp_def] using
    eval_as_at d.keys (List.nodup_dedup _) d (by
      intro k hk; simpa [Dist.keys] using hk) f

theorem total_collect (d : Dist κ) : (Dist.collect d).total = d.total := by
  simpa [eval, Dist.total] using eval_collect d (fun _ => 1)

end MatrixMath.Spec.Dist.Compact

namespace MatrixMath.Spec.Dist.Compact
variable {κ : Type} [DecidableEq κ]

omit [DecidableEq κ] in
@[simp] theorem eval_nil (f : κ → ℚ) : eval [] f = 0 := rfl
omit [DecidableEq κ] in
@[simp] theorem eval_cons (p : κ × ℚ) (d : Dist κ) (f : κ → ℚ) :
    eval (p :: d) f = p.2 * f p.1 + eval d f := rfl

omit [DecidableEq κ] in
theorem eval_append (a b : Dist κ) (f : κ → ℚ) :
    eval (a ++ b) f = eval a f + eval b f := by simp [eval]

omit [DecidableEq κ] in
theorem eval_smul (c : ℚ) (d : Dist κ) (f : κ → ℚ) :
    eval (Dist.smul c d) f = c * eval d f := by
  simp only [Dist.smul, eval, List.map_map, Function.comp_def, mul_assoc,
    List.sum_map_mul_left]

omit [DecidableEq κ] in
theorem eval_mul (c : ℚ) (d : Dist κ) (f : κ → ℚ) :
    eval d (fun x => c * f x) = c * eval d f := by
  simp only [eval, mul_left_comm _ c, List.sum_map_mul_left]

theorem at_eq_eval (d : Dist κ) (k : κ) :
    d.at' k = eval d (fun x => if x = k then 1 else 0) := by
  induction d with
  | nil => rfl
  | cons p d ih =>
    obtain ⟨a, w⟩ := p
    rw [at_cons, eval_cons, ih]
    by_cases h : a = k <;> simp [h]

omit [DecidableEq κ] in
theorem eval_mix (parts : List (ℚ × Dist κ)) (f : κ → ℚ) :
    eval (Dist.mix parts) f = (parts.map fun p => p.1 * eval p.2 f).sum := by
  induction parts with
  | nil => rfl
  | cons p parts ih =>
    simp only [Dist.mix, List.flatMap_cons, eval_append, eval_smul,
      List.map_cons, List.sum_cons] at *
    rw [ih]

theorem eval_mix_collect (parts : List (ℚ × Dist κ)) (f : κ → ℚ) :
    eval (Dist.mix (parts.map fun p => (p.1, Dist.collect p.2))) f =
      eval (Dist.mix parts) f := by
  simp only [eval_mix, List.map_map, Function.comp_def, eval_collect]

theorem eval_product (a b : Dist SupportVec) (f : SupportVec → ℚ) :
    eval (betaProduct a b) f = eval a (fun x => eval b (fun y => f (x.concat y))) := by
  induction a with
  | nil => rfl
  | cons p a ih =>
    simp only [betaProduct, List.flatMap_cons, eval_append, eval_cons] at *
    rw [ih]
    congr 1
    simp only [eval, List.map_map, Function.comp_def, mul_assoc,
      List.sum_map_mul_left]

theorem eval_product_collect (a b : Dist SupportVec) (f : SupportVec → ℚ) :
    eval (betaProduct (Dist.collect a) (Dist.collect b)) f = eval (betaProduct a b) f := by
  simp only [eval_product, eval_collect]

end MatrixMath.Spec.Dist.Compact


namespace MatrixMath.Spec.Dist.Compact

variable {α β : Type} [DecidableEq α] [DecidableEq β]

/-- Dropping earlier duplicate inputs preserves the last-occurrence order of
all output keys, even when `f` has overlaps or is non-injective. -/
theorem dedup_flatMap_dedup (xs : List α) (f : α → List β) :
    (xs.dedup.flatMap f).dedup = (xs.flatMap f).dedup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    by_cases h : a ∈ xs
    · rw [List.dedup_cons_of_mem h, List.flatMap_cons]
      have hs : f a ⊆ xs.flatMap f := by
        intro b hb
        exact List.mem_flatMap.mpr ⟨a, h, hb⟩
      rw [List.Subset.dedup_append_right hs]
      exact ih
    · rw [List.dedup_cons_of_notMem h, List.flatMap_cons, List.flatMap_cons,
        List.dedup_append, List.dedup_append, ih]

/-- A non-injective map may introduce duplicates; an outer `dedup` preserves
its ordering whether or not earlier duplicate inputs were already removed. -/
theorem dedup_map_dedup (xs : List α) (f : α → β) :
    (xs.dedup.map f).dedup = (xs.map f).dedup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    by_cases h : a ∈ xs
    · rw [List.dedup_cons_of_mem h, List.map_cons,
        List.dedup_cons_of_mem (List.mem_map_of_mem h)]
      exact ih
    · rw [List.dedup_cons_of_notMem h, List.map_cons, List.map_cons,
        List.dedup_cons', List.dedup_cons', ih]


end MatrixMath.Spec.Dist.Compact

namespace MatrixMath.Spec.Dist.Compact
variable {α β : Type} [DecidableEq α] [DecidableEq β]

theorem dedup_append_left (xs ys : List α) :
    (xs.dedup ++ ys).dedup = (xs ++ ys).dedup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    by_cases h : a ∈ xs
    · rw [List.dedup_cons_of_mem h, List.cons_append,
        List.dedup_cons_of_mem (List.mem_append_left ys h), ih]
    · rw [List.dedup_cons_of_notMem h, List.cons_append, List.cons_append,
        List.dedup_cons', List.dedup_cons', ih]

theorem dedup_append_both (xs ys : List α) :
    (xs.dedup ++ ys.dedup).dedup = (xs ++ ys).dedup := by
  rw [dedup_append_left, List.dedup_append, List.dedup_append, List.dedup_idem]

omit [DecidableEq α] in
theorem dedup_flatMap_congr (xs : List α) (f g : α → List β)
    (h : ∀ x, (f x).dedup = (g x).dedup) :
    (xs.flatMap f).dedup = (xs.flatMap g).dedup := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.flatMap_cons]
    rw [← dedup_append_both, ← dedup_append_both (g a), h a, ih]

theorem keys_mix_collect (parts : List (ℚ × Dist α)) :
    (Dist.mix (parts.map fun p => (p.1, Dist.collect p.2))).keys =
      (Dist.mix parts).keys := by
  simp only [Dist.keys, Dist.mix, List.flatMap_map, List.map_flatMap,
    Dist.smul, Dist.collect, List.map_map, Function.comp_def]
  apply dedup_flatMap_congr
  intro p
  simp only [List.map_id', List.dedup_idem]

theorem keys_product (a b : Dist SupportVec) :
    (betaProduct a b).keys =
      ((a.map Prod.fst).flatMap fun x => (b.map Prod.fst).map fun y => x.concat y).dedup := by
  simp only [Dist.keys, betaProduct, List.map_flatMap, List.map_map,
    List.flatMap_map, Function.comp_def]

theorem keys_product_collect (a b : Dist SupportVec) :
    (betaProduct (Dist.collect a) (Dist.collect b)).keys = (betaProduct a b).keys := by
  rw [keys_product, keys_product]
  simp only [Dist.collect, List.map_map, Function.comp_def, List.map_id', Dist.keys]
  rw [dedup_flatMap_dedup]
  apply dedup_flatMap_congr
  intro x
  simpa only [List.map_map, Function.comp_def] using
    dedup_map_dedup (b.map Prod.fst) (fun y : SupportVec => x.concat y)

theorem collect_mix_collect (parts : List (ℚ × Dist α)) :
    Dist.collect (Dist.mix (parts.map fun p => (p.1, Dist.collect p.2))) =
      Dist.collect (Dist.mix parts) := by
  apply collect_eq_of_keys_at _ _ (keys_mix_collect parts)
  intro k
  simp only [at_eq_eval, eval_mix_collect]

theorem collect_product_collect (a b : Dist SupportVec) :
    Dist.collect (betaProduct (Dist.collect a) (Dist.collect b)) =
      Dist.collect (betaProduct a b) := by
  apply collect_eq_of_keys_at _ _ (keys_product_collect a b)
  intro k
  simp only [at_eq_eval, eval_product_collect]

end MatrixMath.Spec.Dist.Compact

namespace MatrixMath.Spec.Dist.Compact
variable {α κ : Type} [DecidableEq κ]

theorem collect_mix_map_congr (xs : List α) (w : α → ℚ) (f g : α → Dist κ)
    (h : ∀ x, Dist.collect (f x) = Dist.collect (g x)) :
    Dist.collect (Dist.mix (xs.map fun x => (w x, f x))) =
      Dist.collect (Dist.mix (xs.map fun x => (w x, g x))) := by
  rw [← collect_mix_collect, ← collect_mix_collect (xs.map fun x => (w x, g x))]
  simp only [List.map_map, Function.comp_def, h]

end MatrixMath.Spec.Dist.Compact

namespace MatrixMath.Spec.Dist.HashCompact
open MatrixMath.Spec.Dist.Compact
variable {κ : Type} [DecidableEq κ] [BEq κ] [LawfulBEq κ] [Hashable κ]

/-- The separate key list follows the reference last-occurrence order; hash
iteration order is never observed. Zero and signed weights remain explicit. -/
def state (d : Dist κ) : List κ × Std.HashMap κ ℚ :=
  d.foldr (fun p s =>
    (if s.2.contains p.1 then s.1 else p.1 :: s.1,
      s.2.insert p.1 (p.2 + s.2.getD p.1 0))) ([], ∅)

theorem contains_state (d : Dist κ) (k : κ) :
    (state d).2.contains k = decide (k ∈ d.map Prod.fst) := by
  induction d with
  | nil => simp [state]
  | cons p d ih =>
    change ((state d).2.insert p.1 (p.2 + (state d).2.getD p.1 0)).contains k = _
    rw [Std.HashMap.contains_insert, ih]
    simp only [List.map_cons, List.mem_cons, Bool.decide_or, Bool.beq_eq_decide_eq,
      eq_comm]

theorem getD_state (d : Dist κ) (k : κ) :
    (state d).2.getD k 0 = d.at' k := by
  induction d with
  | nil => simp [state, Dist.at']
  | cons p d ih =>
    obtain ⟨a,w⟩ := p
    rw [at_cons]
    change ((state d).2.insert a (w + (state d).2.getD a 0)).getD k 0 = _
    rw [Std.HashMap.getD_insert]
    by_cases h : a = k
    · subst a; simp [ih]
    · simp [h, ih]

theorem keys_state (d : Dist κ) : (state d).1 = d.keys := by
  induction d with
  | nil => rfl
  | cons p d ih =>
    change (if (state d).2.contains p.1 then (state d).1 else p.1 :: (state d).1) = _
    rw [contains_state, ih]
    unfold Dist.keys
    simp only [List.map_cons]
    by_cases h : p.1 ∈ d.map Prod.fst
    · simp [h, List.dedup_cons_of_mem h]
    · simp [h, List.dedup_cons_of_notMem h]

def collectHash (d : Dist κ) : Dist κ :=
  let s := state d
  s.1.map fun k => (k, s.2.getD k 0)

theorem collectHash_eq_collect (d : Dist κ) : collectHash d = Dist.collect d := by
  simp only [collectHash, keys_state, getD_state, Dist.collect]

end MatrixMath.Spec.Dist.HashCompact

namespace MatrixMath.Certificate
open MatrixMath.Spec MatrixMath.Spec.Dist.Compact

/-- A reference collection specialized to support vectors. The compiler uses
only its proved hash implementation; the logical definition stays unchanged. -/
def collectSupport (d : Spec.Dist SupportVec) : Spec.Dist SupportVec := Dist.collect d

def collectSupportHash (d : Spec.Dist SupportVec) : Spec.Dist SupportVec :=
  Spec.Dist.HashCompact.collectHash d

@[csimp] theorem collectSupport_eq_hash : collectSupport = collectSupportHash := by
  funext d
  exact (Spec.Dist.HashCompact.collectHash_eq_collect d).symm

/-- Reference merged weights with the same proved specialization. -/
def weightsSupport (d : Spec.Dist SupportVec) : List ℚ := Dist.weights d

def weightsSupportHash (d : Spec.Dist SupportVec) : List ℚ :=
  (collectSupportHash d).map Prod.snd

@[csimp] theorem weightsSupport_eq_hash : weightsSupport = weightsSupportHash := by
  funext d
  simp only [weightsSupport, weightsSupportHash, collectSupportHash,
    Spec.Dist.HashCompact.collectHash_eq_collect, Dist.weights]

/-- Exact region mixture from already evaluated child occurrences. -/
def regionFromPairs (kids : List ANode) (r : ℕ)
    (ps : List (ANode × Spec.Dist SupportVec)) : Spec.Dist SupportVec :=
  let pr := ps.filter fun p => p.1.region = r
  Dist.mix ((pr.zip pr.reverse).map fun pq =>
    (alphaAt kids r pq.1.1.shape, betaProduct pq.1.2 pq.2.2))

theorem collect_regionFromPairs (kids : List ANode) (r : ℕ)
    (ps : List (ANode × Spec.Dist SupportVec)) :
    Dist.collect (regionFromPairs kids r (ps.map fun p => (p.1, Dist.collect p.2))) =
      Dist.collect (regionFromPairs kids r ps) := by
  have hf : (ps.map fun p => (p.1, Dist.collect p.2)).filter (fun p => p.1.region = r) =
      (ps.filter fun p => p.1.region = r).map (fun p => (p.1, Dist.collect p.2)) := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.map_cons, List.filter_cons]
      by_cases h : p.1.region = r <;> simp [h, ih]
  unfold regionFromPairs
  rw [hf]
  simp only [← List.map_reverse, List.zip_map, List.map_map, Function.comp_def, Prod.map_def]
  apply collect_mix_map_congr
  intro pq
  exact collect_product_collect pq.1.2 pq.2.2

mutual
/-- The reference beta distribution collected at each recursive occurrence.
Child occurrences are evaluated once before any of the six regional mixtures. -/
def betaCompact : ℕ → ANode → Coordinate → Spec.Dist SupportVec
  | ℓ, n@(.zeroLeaf _ _ _ _), W => collectSupport (betaOf ℓ n W)
  | ℓ, n@(.posTwo _ _ _ _), W => collectSupport (betaOf ℓ n W)
  | ℓ, .posBranch _ _ _ A kids, W =>
      let ps := kids.zip (betaCompactList (ℓ - 1) kids W)
      collectSupport (Dist.mix ((List.range 6).map fun r =>
        (A.getD r 0, collectSupport (regionFromPairs kids r ps))))
  termination_by _ n _ => sizeOf n

/-- A compact beta for every child occurrence, in reference list order. -/
def betaCompactList : ℕ → List ANode → Coordinate → List (Spec.Dist SupportVec)
  | _, [], _ => []
  | ℓ, k :: rest, W => betaCompact ℓ k W :: betaCompactList ℓ rest W
  termination_by _ ns _ => sizeOf ns
end

mutual
/-- Collection at every occurrence preserves the full reference observation. -/
theorem betaCompact_eq_collect (ℓ : ℕ) (n : ANode) (W : Coordinate) :
    betaCompact ℓ n W = Dist.collect (betaOf ℓ n W) := by
  cases n with
  | zeroLeaf r s a b => rw [betaCompact]; rfl
  | posTwo r s a mu => rw [betaCompact]; rfl
  | posBranch r s a A kids =>
    rw [betaCompact, betaOf]
    simp only [collectSupport]
    rw [betaCompactList_eq_map]
    simp only [List.zip_map_right, Prod.map_def, id_eq]
    apply collect_mix_map_congr
    intro rr
    rw [collect_idempotent, collect_regionFromPairs]
    rfl
  termination_by sizeOf n

theorem betaCompactList_eq_map (ℓ : ℕ) (kids : List ANode) (W : Coordinate) :
    betaCompactList ℓ kids W = (betaListOf ℓ kids W).map Dist.collect := by
  cases kids with
  | nil => rw [betaCompactList, betaListOf]; rfl
  | cons k rest =>
    rw [betaCompactList, betaListOf, List.map_cons, betaCompact_eq_collect,
      betaCompactList_eq_map]
  termination_by sizeOf kids
end

end MatrixMath.Certificate

namespace MatrixMath.Certificate
open MatrixMath.Spec MatrixMath.Spec.Dist.Compact

/-- A collected A5 region; each child occurrence is evaluated once. -/
def betaRegionCompact (ℓc : ℕ) (kids : List ANode) (r : ℕ) (W : Coordinate) :
    Spec.Dist SupportVec :=
  collectSupport (regionFromPairs kids r (kids.zip (betaCompactList ℓc kids W)))

theorem betaRegionCompact_eq_collect (ℓc : ℕ) (kids : List ANode) (r : ℕ)
    (W : Coordinate) :
    betaRegionCompact ℓc kids r W = Dist.collect (betaRegion ℓc kids r W) := by
  unfold betaRegionCompact collectSupport
  rw [betaCompactList_eq_map]
  simp only [List.zip_map_right, Prod.map_def, id_eq]
  rw [collect_regionFromPairs]
  rfl

/-- A mixture of already compact child distributions, retaining zero keys. -/
def betaBarCompact (ℓc : ℕ) (w : ANode → ℚ) (kids : List ANode) (W : Coordinate) :
    Spec.Dist SupportVec :=
  collectSupport (Dist.mix (kids.map fun k => (w k, betaCompact ℓc k W)))

theorem betaBarCompact_eq_collect (ℓc : ℕ) (w : ANode → ℚ) (kids : List ANode)
    (W : Coordinate) :
    betaBarCompact ℓc w kids W = Dist.collect (betaBar ℓc w kids W) := by
  unfold betaBarCompact betaBar collectSupport
  simp only [betaCompact_eq_collect]
  simpa only [List.map_map, Function.comp_def] using
    collect_mix_collect (kids.map fun k => (w k, betaOf ℓc k W))

/-- Collected unnormalized conditional Y mixture. -/
def etaYMixCompact (ℓc : ℕ) (w : ANode → ℚ) (kids : List ANode)
    (cY cZ : Coordinate) (j : ℕ) : Spec.Dist SupportVec :=
  betaBarCompact ℓc w (kids.filter fun k =>
    AShape.coord k.shape cY = j && 0 < AShape.coord k.shape cZ) cY

/-- Collected unnormalized conditional Z mixture. -/
def etaZMixCompact (ℓc : ℕ) (w : ANode → ℚ) (kids : List ANode)
    (cX cY cZ : Coordinate) (kk : ℕ) : Spec.Dist SupportVec :=
  betaBarCompact ℓc w (kids.filter fun k =>
    0 < AShape.coord k.shape cX && 0 < AShape.coord k.shape cY &&
      AShape.coord k.shape cZ = kk) cZ

theorem etaYMixCompact_eq_collect (ℓc : ℕ) (w : ANode → ℚ) (kids : List ANode)
    (cY cZ : Coordinate) (j : ℕ) :
    etaYMixCompact ℓc w kids cY cZ j = Dist.collect (etaYMix ℓc w kids cY cZ j) := by
  exact betaBarCompact_eq_collect _ _ _ _

theorem etaZMixCompact_eq_collect (ℓc : ℕ) (w : ANode → ℚ) (kids : List ANode)
    (cX cY cZ : Coordinate) (kk : ℕ) :
    etaZMixCompact ℓc w kids cX cY cZ kk =
      Dist.collect (etaZMix ℓc w kids cX cY cZ kk) := by
  exact betaBarCompact_eq_collect _ _ _ _

@[simp] theorem weights_collect {κ : Type} [DecidableEq κ] (d : Spec.Dist κ) :
    Dist.weights (Dist.collect d) = Dist.weights d := by
  simp only [Dist.weights, collect_idempotent]

@[simp] theorem weights_betaCompact (ℓ : ℕ) (n : ANode) (W : Coordinate) :
    Dist.weights (betaCompact ℓ n W) = Dist.weights (betaOf ℓ n W) := by
  rw [betaCompact_eq_collect, weights_collect]

@[simp] theorem weights_betaRegionCompact (ℓc : ℕ) (kids : List ANode) (r : ℕ)
    (W : Coordinate) :
    Dist.weights (betaRegionCompact ℓc kids r W) = Dist.weights (betaRegion ℓc kids r W) := by
  rw [betaRegionCompact_eq_collect, weights_collect]

@[simp] theorem weights_betaBarCompact (ℓc : ℕ) (w : ANode → ℚ)
    (kids : List ANode) (W : Coordinate) :
    Dist.weights (betaBarCompact ℓc w kids W) = Dist.weights (betaBar ℓc w kids W) := by
  rw [betaBarCompact_eq_collect, weights_collect]

@[simp] theorem weights_etaYMixCompact (ℓc : ℕ) (w : ANode → ℚ)
    (kids : List ANode) (cY cZ : Coordinate) (j : ℕ) :
    Dist.weights (etaYMixCompact ℓc w kids cY cZ j) =
      Dist.weights (etaYMix ℓc w kids cY cZ j) := by
  rw [etaYMixCompact_eq_collect, weights_collect]

@[simp] theorem total_etaYMixCompact (ℓc : ℕ) (w : ANode → ℚ)
    (kids : List ANode) (cY cZ : Coordinate) (j : ℕ) :
    (etaYMixCompact ℓc w kids cY cZ j).total = (etaYMix ℓc w kids cY cZ j).total := by
  rw [etaYMixCompact_eq_collect, total_collect]

@[simp] theorem weights_etaZMixCompact (ℓc : ℕ) (w : ANode → ℚ)
    (kids : List ANode) (cX cY cZ : Coordinate) (kk : ℕ) :
    Dist.weights (etaZMixCompact ℓc w kids cX cY cZ kk) =
      Dist.weights (etaZMix ℓc w kids cX cY cZ kk) := by
  rw [etaZMixCompact_eq_collect, weights_collect]

@[simp] theorem total_etaZMixCompact (ℓc : ℕ) (w : ANode → ℚ)
    (kids : List ANode) (cX cY cZ : Coordinate) (kk : ℕ) :
    (etaZMixCompact ℓc w kids cX cY cZ kk).total =
      (etaZMix ℓc w kids cX cY cZ kk).total := by
  rw [etaZMixCompact_eq_collect, total_collect]

end MatrixMath.Certificate
