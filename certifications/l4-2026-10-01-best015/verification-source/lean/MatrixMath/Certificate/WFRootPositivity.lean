import MatrixMath.Certificate.OmegaCheck

/-!
# Root and interior positivity derived from well-formedness

Normative source: `docs/specs/0001_spec.md` §7.2 and Appendix A;
proof evidence: experiments 0096 and 0104; integration: ADR 0027 and 0106.

The compiler replacement removes only positivity checks implied by the retained
WF prefix. Root and interior blocks, interior mass/A signs, array traversal and
all exact values remain. The unconditional equality preserves malformed-input
behavior; it establishes no certificate-specific exponent or runtime bound.
-/

namespace MatrixMath.Certificate.WFRootPositivity

open MatrixMath MatrixMath.Spec MatrixMath.Numeric

private abbrev Nonneg {κ : Type} (d : Spec.Dist κ) : Prop :=
  ∀ p ∈ d, 0 ≤ p.2

private theorem sum_nonneg {κ : Type} {d : Spec.Dist κ} (h : Nonneg d) :
    0 ≤ (d.map Prod.snd).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact h p hp

private theorem push_nonneg {κ κ' : Type} (f : κ → κ')
    {d : Spec.Dist κ} (h : Nonneg d) : Nonneg (Dist.push f d) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact h q hq

private theorem weights_nonneg {κ : Type} [DecidableEq κ]
    {d : Spec.Dist κ} (h : Nonneg d) : ∀ x ∈ Dist.weights d, 0 ≤ x := by
  intro x hx
  simp only [Dist.weights, Dist.collect, List.mem_map] at hx
  obtain ⟨p, ⟨k, hk, rfl⟩, rfl⟩ := hx
  apply sum_nonneg
  intro q hq
  exact h q (List.mem_of_mem_filter hq)

private theorem nonnegList_of {l : List ℚ} (h : ∀ x ∈ l, 0 ≤ x) :
    nonnegList l = true := by
  simpa [nonnegList] using h

private theorem weights_ok {κ : Type} [DecidableEq κ]
    {d : Spec.Dist κ} (h : Nonneg d) : nonnegList (Dist.weights d) = true :=
  nonnegList_of (weights_nonneg h)

private theorem cond_ok {κ : Type} [DecidableEq κ]
    {d : Spec.Dist κ} (h : Nonneg d) : condHOk d = true := by
  have ht : 0 ≤ d.total := sum_nonneg h
  simp only [condHOk, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨ht, nonnegList_of ?_⟩
  intro x hx
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
  exact div_nonneg (weights_nonneg h v hv) ht

private theorem smul_nonneg {κ : Type} {c : ℚ} {d : Spec.Dist κ}
    (hc : 0 ≤ c) (hd : Nonneg d) : Nonneg (Dist.smul c d) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact mul_nonneg hc (hd q hq)

private theorem mix_nonneg {κ : Type} {parts : List (ℚ × Spec.Dist κ)}
    (h : ∀ p ∈ parts, 0 ≤ p.1 ∧ Nonneg p.2) : Nonneg (Dist.mix parts) := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.mp hp
  exact smul_nonneg (h q hq).1 (h q hq).2 p hpq

private theorem product_nonneg {d e : Spec.Dist SupportVec}
    (hd : Nonneg d) (he : Nonneg e) : Nonneg (betaProduct d e) := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.mp hp
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hpq
  exact mul_nonneg (hd q hq) (he r hr)

private theorem alpha_nonneg {ell : ℕ} {n : ANode} (h : n.WF ell) :
    0 ≤ n.alpha := by
  cases n with
  | zeroLeaf r s a b => rw [ANode.WF] at h; exact h.2.2.2.1
  | posTwo r s a mu => rw [ANode.WF] at h; exact h.2.2.2.2.1
  | posBranch r s a A kids => rw [ANode.WF] at h; exact h.2.2.2.2.1

private theorem getD_nonneg {l : List ℚ} (h : ∀ x ∈ l, 0 ≤ x) (i : ℕ) :
    0 ≤ l.getD i 0 := by
  induction l generalizing i with
  | nil => simp
  | cons x xs ih =>
      cases i with
      | zero => simp [h x (by simp)]
      | succ j =>
          simp only [List.getD_cons_succ]
          apply ih
          intro y hy
          exact h y (by simp [hy])

private theorem alphaAt_nonneg (kids : List ANode)
    (h : ∀ k ∈ kids, 0 ≤ k.alpha) (r : ℕ) (s : AShape) :
    0 ≤ alphaAt kids r s := by
  unfold alphaAt
  apply List.sum_nonneg
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  exact h k (List.mem_of_mem_filter hk)

private theorem betaList_nonneg (ell : ℕ) (kids : List ANode) (W : Coordinate)
    (h : ∀ k ∈ kids, Nonneg (betaOf ell k W)) :
    ∀ d ∈ betaListOf ell kids W, Nonneg d := by
  induction kids with
  | nil => simp [betaListOf]
  | cons k rest ih =>
      intro d hd
      rw [betaListOf] at hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact h k (by simp)
      · exact ih (fun q hq => h q (by simp [hq])) d hd

private theorem region_nonneg (ell : ℕ) (kids : List ANode) (r : ℕ)
    (W : Coordinate) (ha : ∀ k ∈ kids, 0 ≤ k.alpha)
    (hb : ∀ k ∈ kids, Nonneg (betaOf ell k W)) :
    Nonneg (betaRegion ell kids r W) := by
  let pr := (kids.zip (betaListOf ell kids W)).filter fun p => p.1.region = r
  change Nonneg (Dist.mix ((pr.zip pr.reverse).map fun pq =>
    (alphaAt kids r pq.1.1.shape, betaProduct pq.1.2 pq.2.2)))
  apply mix_nonneg
  intro p hp
  obtain ⟨pq, hpq, rfl⟩ := List.mem_map.mp hp
  have hleft : pq.1 ∈ pr := (List.of_mem_zip hpq).1
  have hright : pq.2 ∈ pr := List.mem_reverse.mp (List.of_mem_zip hpq).2
  have hl : pq.1.2 ∈ betaListOf ell kids W :=
    (List.of_mem_zip (List.mem_of_mem_filter hleft)).2
  have hr : pq.2.2 ∈ betaListOf ell kids W :=
    (List.of_mem_zip (List.mem_of_mem_filter hright)).2
  exact ⟨alphaAt_nonneg kids ha r _,
    product_nonneg (betaList_nonneg ell kids W hb _ hl)
      (betaList_nonneg ell kids W hb _ hr)⟩

/-- Entrywise nonnegativity of the complete recursive beta distribution. -/
theorem betaOf_nonneg_of_wf {ell : ℕ} {n : ANode} (h : n.WF ell)
    (W : Coordinate) : ∀ p ∈ betaOf ell n W, 0 ≤ p.2 := by
  induction ell using Nat.strong_induction_on generalizing n with
  | h ell ih =>
      cases n with
      | zeroLeaf r s a b =>
          rw [ANode.WF] at h
          have hb : Nonneg b := h.2.2.2.2.1.1
          rw [betaOf]
          split_ifs
          · simp
          · exact hb
          · exact push_nonneg SupportVec.dual hb
      | posTwo r s a mu =>
          rw [ANode.WF] at h
          have hm : 0 ≤ mu := h.2.2.2.2.2.1
          have ht : 0 ≤ 1 - 2 * mu := by linarith [h.2.2.2.2.2.2]
          rw [betaOf]
          split_ifs <;> simp [hm, ht]
      | posBranch r s a A kids =>
          rw [ANode.WF] at h
          have hell : ell - 1 < ell := by omega
          have hk : ∀ k ∈ kids, k.WF (ell - 1) := h.2.2.2.2.2.2.2.2.2.2
          have ha : ∀ k ∈ kids, 0 ≤ k.alpha := fun k hmem => alpha_nonneg (hk k hmem)
          have hb : ∀ k ∈ kids, Nonneg (betaOf (ell - 1) k W) :=
            fun k hmem => ih (ell - 1) hell (hk k hmem)
          rw [betaOf_posBranch]
          apply mix_nonneg
          intro p hp
          obtain ⟨rr, hrr, rfl⟩ := List.mem_map.mp hp
          exact ⟨getD_nonneg h.2.2.2.2.2.2.1 rr,
            region_nonneg (ell - 1) kids rr W ha hb⟩

private theorem mixture_nonneg (ell : ℕ) (kids : List ANode)
    (w : ANode → ℚ) (W : Coordinate)
    (hw : ∀ k ∈ kids, 0 ≤ w k) (hn : ∀ k ∈ kids, k.WF ell) :
    Nonneg (Dist.mix (kids.map fun k => (w k, betaOf ell k W))) := by
  apply mix_nonneg
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  exact ⟨hw k hk, betaOf_nonneg_of_wf (hn k hk) W⟩

private theorem etaY_ok (ell bound : ℕ) (kids : List ANode)
    (w : ANode → ℚ) (cY cZ : Coordinate)
    (hw : ∀ k ∈ kids, 0 ≤ w k) (hn : ∀ k ∈ kids, k.WF ell) :
    etaYOk ell bound w kids cY cZ = true := by
  simp only [etaYOk, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro k hk
    have hk' : k ∈ kids := List.mem_of_mem_filter hk
    simp only [decide_eq_true_eq]
    exact ⟨hw k hk', weights_ok (betaOf_nonneg_of_wf (hn k hk') cY)⟩
  · intro j hj
    apply cond_ok
    unfold etaYMix
    apply mixture_nonneg
    · intro k hk; exact hw k (List.mem_of_mem_filter hk)
    · intro k hk; exact hn k (List.mem_of_mem_filter hk)

private theorem etaZ_ok (ell bound : ℕ) (kids : List ANode)
    (w : ANode → ℚ) (cX cY cZ : Coordinate)
    (hw : ∀ k ∈ kids, 0 ≤ w k) (hn : ∀ k ∈ kids, k.WF ell) :
    etaZOk ell bound w kids cX cY cZ = true := by
  simp only [etaZOk, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro k hk
    have hk' : k ∈ kids := List.mem_of_mem_filter hk
    simp only [decide_eq_true_eq]
    exact ⟨hw k hk', weights_ok (betaOf_nonneg_of_wf (hn k hk') cZ)⟩
  · intro j hj
    apply cond_ok
    unfold etaZMix
    apply mixture_nonneg
    · intro k hk; exact hw k (List.mem_of_mem_filter hk)
    · intro k hk; exact hn k (List.mem_of_mem_filter hk)

/-- For a WF instance, only the original block remains in each root side check. -/
theorem eRootRegionOk_eq_blockOk_of_wf (prec : ℕ) (I : AInstance)
    (r : ℕ) (blk : Block) (h : I.WF) :
    eRootRegionOk prec I r blk = blockOk prec (alphaZip (I.kidsIn r)) blk := by
  have hk : ∀ k ∈ I.kidsIn r, k.WF I.levels := by
    intro k hk
    exact h.2.2.2.2.2.2.2 k (List.mem_of_mem_filter hk)
  have ha : ∀ k ∈ I.kidsIn r, 0 ≤ k.alpha := fun k hmem => alpha_nonneg (hk k hmem)
  have hz : Nonneg (alphaZip (I.kidsIn r)) := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact ha k hk
  have hx := weights_ok (push_nonneg (fun s => AShape.coord s (permOf r .X)) hz)
  have hy := weights_ok (mixture_nonneg I.levels (I.kidsIn r) ANode.alpha (permOf r .Y) ha hk)
  have hzz := weights_ok (mixture_nonneg I.levels (I.kidsIn r) ANode.alpha (permOf r .Z) ha hk)
  have hey := etaY_ok I.levels (2 ^ I.levels) (I.kidsIn r) ANode.alpha
    (permOf r .Y) (permOf r .Z) ha hk
  have hez := etaZ_ok I.levels (2 ^ I.levels) (I.kidsIn r) ANode.alpha
    (permOf r .X) (permOf r .Y) (permOf r .Z) ha hk
  simp only [eRootRegionOk, betaBar, hx, hy, hzz, hey, hez, Bool.and_true]

/-- The same six root blocks, with their original domains and defaults. -/
def rootBlocksOk (prec : ℕ) (I : AInstance) (blks : List Block) : Bool :=
  (List.range 6).all fun r =>
    blockOk prec (alphaZip (I.kidsIn r)) (blks.getD r defaultBlock)

/-- The root checker replacement requires WF; the complete checker retains it. -/
theorem eRootOk_eq_rootBlocksOk_of_wf (prec : ℕ) (I : AInstance)
    (blks : List Block) (h : I.WF) :
    eRootOk prec I blks = rootBlocksOk prec I blks := by
  unfold eRootOk rootBlocksOk
  apply congrArg (fun f : ℕ → Bool => (List.range 6).all f)
  funext r
  have hA : 0 ≤ I.A.getD r 0 := getD_nonneg h.2.2.2.1 r
  have hA' : decide (0 ≤ I.A.getD r 0) = true := by
    simpa only [decide_eq_true_eq] using hA
  rw [eRootRegionOk_eq_blockOk_of_wf prec I r _ h, hA', Bool.true_and]

open MatrixMath.Certificate.TrackACert

/-- The complete checker with WF-derived root positivity checks removed. -/
def checkRootBlocks (c : TrackACert) : Bool :=
  wfInstance c.inst &&
    decide (0 ≤ c.omega) &&
    rootBlocksOk c.precision c.inst c.blocks &&
    interiorOk c.precision c.inst c.blocks &&
    eTwoSumOk c.inst .X && eTwoSumOk c.inst .Y &&
    eTwoSumOk c.inst .Z &&
    mTotalSumOk c.inst .X && mTotalSumOk c.inst .Y &&
    mTotalSumOk c.inst .Z &&
    decide (requirementUpper c.precision c.inst
      ≤ c.eTotalLower + c.mTotalLower * c.omega)

/-- Unconditional Boolean equality, including malformed instances and blocks. -/
theorem check_eq_checkRootBlocks : TrackACert.check = checkRootBlocks := by
  funext c
  cases hw : wfInstance c.inst with
  | false => simp only [TrackACert.check, checkRootBlocks, hw, Bool.false_and]
  | true =>
      have he := eRootOk_eq_rootBlocksOk_of_wf c.precision c.inst c.blocks
        (wfInstance_sound hw)
      simp only [TrackACert.check, checkRootBlocks, he]

/-! Source-only interior extension. No compilation has been attempted. -/

private theorem mem_nodesListOf_exists_interior {ell : ℕ} {ms : List ℚ}
    {kids : List ANode} {t : ℕ × ℚ × ANode}
    (ht : t ∈ nodesListOf ell ms kids) :
    ∃ k ∈ kids, ∃ m : ℚ, t ∈ nodesOf ell m k := by
  induction kids generalizing ms with
  | nil => simp [nodesListOf] at ht
  | cons k ks ih =>
      rw [nodesListOf] at ht
      simp only [List.mem_append] at ht
      rcases ht with ht | ht
      · exact ⟨k, by simp, ms.headD 0, ht⟩
      · obtain ⟨k', hk', m, hm⟩ := ih ht
        exact ⟨k', by simp [hk'], m, hm⟩

/-- A reached node is WF at its recorded level, independently of its mass. -/
theorem wf_of_mem_nodesOf : ∀ {ell : ℕ} {m : ℚ} {n : ANode}
    {t : ℕ × ℚ × ANode}, n.WF ell → t ∈ nodesOf ell m n →
      t.2.2.WF t.1 := by
  intro ell m n
  induction ell using Nat.strong_induction_on generalizing m n with
  | h ell ih =>
      intro t hn ht
      cases n with
      | zeroLeaf r s a b =>
          simp only [nodesOf, List.mem_singleton] at ht
          subst t
          exact hn
      | posTwo r s a mu =>
          simp only [nodesOf, List.mem_singleton] at ht
          subst t
          exact hn
      | posBranch r s a A kids =>
          rw [nodesOf] at ht
          rcases List.mem_cons.mp ht with rfl | ht
          · exact hn
          · rw [ANode.WF] at hn
            have hk : ∀ k ∈ kids, k.WF (ell - 1) :=
              hn.2.2.2.2.2.2.2.2.2.2
            obtain ⟨k, hkMem, m', htk⟩ := mem_nodesListOf_exists_interior ht
            exact ih (ell - 1) (by omega) (hk k hkMem) htk

/-- Selecting a positive record supplies WF of its children one level lower. -/
theorem children_wf_of_mem_posNodesAt {I : AInstance} {ell : ℕ}
    {t : ℕ × ℚ × ANode} {r : ℕ} {s : AShape} {a : ℚ}
    {A : List ℚ} {kids : List ANode} (hI : I.WF)
    (ht : t ∈ I.posNodesAt ell)
    (hBranch : t.2.2 = .posBranch r s a A kids) :
    ∀ k ∈ kids, k.WF (ell - 1) := by
  simp only [AInstance.posNodesAt, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq] at ht
  have hn : t ∈ nodesListOf I.levels (rootMasses I.A I.kids) I.kids := ht.1
  obtain ⟨k, hk, m, htk⟩ := mem_nodesListOf_exists_interior hn
  have hNode := wf_of_mem_nodesOf (hI.2.2.2.2.2.2.2 k hk) htk
  rw [ht.2.1, hBranch, ANode.WF] at hNode
  exact hNode.2.2.2.2.2.2.2.2.2.2

/-- The original cheap signs and regional block, with no positivity work. -/
def eInteriorBlocksOk (prec _ell : ℕ) (m : ℚ) (_s : AShape) (A : List ℚ)
    (kids : List ANode) (r : ℕ) (blk : Block) : Bool :=
  decide (0 ≤ m) && decide (0 ≤ A.getD r 0) &&
    blockOk prec (alphaZip (kids.filter fun k => k.region = r)) blk

/-- Child WF alone removes every trailing regional positivity check. -/
theorem eInteriorRegionOk_eq_blocks_of_children_wf
    (prec ell : ℕ) (m : ℚ) (s : AShape) (A : List ℚ)
    (kids : List ANode) (r : ℕ) (blk : Block)
    (hk : ∀ k ∈ kids, k.WF (ell - 1)) :
    eInteriorRegionOk prec ell m s A kids r blk =
      eInteriorBlocksOk prec ell m s A kids r blk := by
  let kidsR := kids.filter fun k => k.region = r
  let w : ANode → ℚ := fun k =>
    alphaAt kids r k.shape + alphaAt kids r (AShape.sub s k.shape)
  have ha : ∀ k ∈ kids, 0 ≤ k.alpha := fun k hm => alpha_nonneg (hk k hm)
  have hb (W : Coordinate) : ∀ k ∈ kids, Nonneg (betaOf (ell - 1) k W) :=
    fun k hm => betaOf_nonneg_of_wf (hk k hm) W
  have hkR : ∀ k ∈ kidsR, k.WF (ell - 1) :=
    fun k hm => hk k (List.mem_of_mem_filter hm)
  have hw : ∀ k ∈ kidsR, 0 ≤ w k := by
    intro k _
    exact add_nonneg (alphaAt_nonneg kids ha r k.shape)
      (alphaAt_nonneg kids ha r (AShape.sub s k.shape))
  have hz : Nonneg (alphaZip kidsR) := by
    intro p hp
    obtain ⟨k, hm, rfl⟩ := List.mem_map.mp hp
    exact ha k (List.mem_of_mem_filter hm)
  have hx := weights_ok (push_nonneg (fun sh => AShape.coord sh (permOf r .X)) hz)
  have hy := weights_ok (region_nonneg (ell - 1) kids r (permOf r .Y) ha (hb _))
  have hzz := weights_ok (region_nonneg (ell - 1) kids r (permOf r .Z) ha (hb _))
  have hey := etaY_ok (ell - 1) (2 ^ ell) kidsR w
    (permOf r .Y) (permOf r .Z) hw hkR
  have hez := etaZ_ok (ell - 1) (2 ^ ell) kidsR w
    (permOf r .X) (permOf r .Y) (permOf r .Z) hw hkR
  dsimp only [kidsR, w] at hx hey hez
  simp only [eInteriorRegionOk, eInteriorBlocksOk, hx, hy, hzz, hey, hez,
    Bool.and_true]

private theorem all_eq_of_mem_eq_interior {X : Type} (xs : List X)
    (f g : X → Bool) (h : ∀ x ∈ xs, f x = g x) : xs.all f = xs.all g := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true]
  constructor
  · intro hf x hx
    rw [← h x hx]
    exact hf x hx
  · intro hg x hx
    rw [h x hx]
    exact hg x hx

/-- Preserve both arrays, index arithmetic, domains, defaults and fallback. -/
def eLevelBlocksOkArray (prec : ℕ) (I : AInstance) (ell offset : ℕ)
    (blocks : List Block) : Bool :=
  let nodes := (I.posNodesAt ell).toArray
  let blockArray := blocks.toArray
  (List.range 6).all fun r =>
    (List.range nodes.size).all fun j =>
      let t := nodes[j]?.getD defaultEntry
      match t.2.2 with
      | .posBranch _ s _ A kids =>
        eInteriorBlocksOk prec ell t.2.1 s A kids r
          (blockArray[offset + 6 * j + r]?.getD defaultBlock)
      | _ => true

/-- WF-conditional equality at every level, offset and block inventory. -/
theorem eLevelOkArray_eq_blocks_of_wf (prec : ℕ) (I : AInstance)
    (ell offset : ℕ) (blocks : List Block) (hI : I.WF) :
    eLevelOkArray prec I ell offset blocks =
      eLevelBlocksOkArray prec I ell offset blocks := by
  unfold eLevelOkArray eLevelBlocksOkArray
  apply all_eq_of_mem_eq_interior
  intro r _
  apply all_eq_of_mem_eq_interior
  intro j hj
  have hjlt : j < (I.posNodesAt ell).length := by
    simpa only [List.mem_range, List.size_toArray] using hj
  have ht : ((I.posNodesAt ell).toArray[j]?.getD defaultEntry) ∈
      I.posNodesAt ell := by
    simpa only [List.getElem?_toArray, List.getD_eq_getElem?_getD] using
      getD_mem hjlt defaultEntry
  cases hBranch : ((I.posNodesAt ell).toArray[j]?.getD defaultEntry).2.2 with
  | zeroLeaf rr s a b => simp only [hBranch]
  | posTwo rr s a mu => simp only [hBranch]
  | posBranch rr s a A kids =>
      simp only [hBranch]
      exact eInteriorRegionOk_eq_blocks_of_children_wf prec ell _ s A kids r _
        (children_wf_of_mem_posNodesAt hI ht hBranch)

/-- Existing interior levels and blockOffset, with the same array traversal. -/
def interiorBlocksOk (prec : ℕ) (I : AInstance) (blocks : List Block) : Bool :=
  (interiorLevels I).all fun ell =>
    eLevelBlocksOkArray prec I ell (blockOffset I ell) blocks

theorem interiorOk_eq_blocks_of_wf (prec : ℕ) (I : AInstance)
    (blocks : List Block) (hI : I.WF) :
    TrackACert.interiorOk prec I blocks = interiorBlocksOk prec I blocks := by
  unfold TrackACert.interiorOk interiorBlocksOk
  apply congrArg (fun f : ℕ → Bool => (interiorLevels I).all f)
  funext ell
  rw [eLevelOk_eq_array]
  exact eLevelOkArray_eq_blocks_of_wf prec I ell (blockOffset I ell) blocks hI

/-- Only the interior acceptance call changes from the proved root replacement. -/
def checkRootInteriorBlocks (c : TrackACert) : Bool :=
  wfInstance c.inst &&
    decide (0 ≤ c.omega) &&
    rootBlocksOk c.precision c.inst c.blocks &&
    interiorBlocksOk c.precision c.inst c.blocks &&
    eTwoSumOk c.inst .X && eTwoSumOk c.inst .Y &&
    eTwoSumOk c.inst .Z &&
    mTotalSumOk c.inst .X && mTotalSumOk c.inst .Y &&
    mTotalSumOk c.inst .Z &&
    decide (requirementUpper c.precision c.inst
      ≤ c.eTotalLower + c.mTotalLower * c.omega)

/-- The WF prefix preserves the original rejection of every malformed input. -/
theorem checkRootBlocks_eq_checkRootInteriorBlocks :
    checkRootBlocks = checkRootInteriorBlocks := by
  funext c
  cases hw : wfInstance c.inst with
  | false => simp only [checkRootBlocks, checkRootInteriorBlocks, hw, Bool.false_and]
  | true =>
      have hi := interiorOk_eq_blocks_of_wf c.precision c.inst c.blocks
        (wfInstance_sound hw)
      simp only [checkRootBlocks, checkRootInteriorBlocks, hi]

/-- A single direct equality from the original checker; no csimp chain is used. -/
theorem check_eq_checkRootInteriorBlocks : TrackACert.check = checkRootInteriorBlocks :=
  check_eq_checkRootBlocks.trans checkRootBlocks_eq_checkRootInteriorBlocks

end MatrixMath.Certificate.WFRootPositivity

attribute [csimp]
  MatrixMath.Certificate.WFRootPositivity.check_eq_checkRootInteriorBlocks
