module

public import PlanarFlow.DynTree.CmpPot
public import PlanarFlow.Klein.ProgPivot

/-!
# The potential of the forest along a pivot

The sixteen operations `pivotOps` of a pivot (`PlanarFlow/Klein/PivotOps.lean`) with the amount
`c = 0` keep the values of the forest bounded by its potential (`PlanarFlow/DynTree/CmpPot.lean`)
plus the absolute values of the four new values of the isolated nodes of the edges of `a` and `b`
(`pivot_pot`): the four additions `t - v` are made at roots (the node of the edge of `a` after
the two cuts, the node of the edge of `b` after the exchange on the cotree and the two cuts), so
they set the values `t` whatever the old values `v` are; the other operations have amount `0`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap DynTree Klein

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### Generic lemmas -/

lemma addPath_zero (Fo : Forest) (n v : ℕ) : addPath Fo n v 0 = Fo := by
  simp only [addPath, add_zero, ite_self]

lemma addPath2_zero (Fo : Forest) (n v : ℕ) : addPath2 Fo n v 0 = Fo := by
  simp only [addPath2, add_zero, ite_self]

lemma agree_cut' {Fo : Forest} {n v u : ℕ} (h : u ≠ v) : Agree Fo (DynTree.cut Fo n v) u :=
  ⟨by simp [DynTree.cut, h], rfl, rfl⟩

lemma agree_link' {Fo : Forest} {v w u : ℕ} (h : u ≠ v) : Agree Fo (DynTree.link Fo v w) u :=
  ⟨by simp [DynTree.link, h], rfl, rfl⟩

lemma agree_refl' (Fo : Forest) (u : ℕ) : Agree Fo Fo u := ⟨rfl, rfl, rfl⟩

/-- Operations of amount `0` keep the potential, and the values before each are bounded by it. -/
lemma allV_amt0 {n : ℕ} {Fo : Forest} {os : List EOp} (h : amtSum os = 0) {Vb : ℝ}
    (hV : pot n Fo ≤ Vb) : AllV Vb n Fo os ∧ pot n (runOpsE n Fo os).1 ≤ pot n Fo := by
  have h1 := pot_runOpsE_le n os Fo
  rw [h, Int.cast_zero, mul_zero, add_zero] at h1
  exact ⟨allV_of_pot (by rw [h, Int.cast_zero, mul_zero, add_zero]; exact hV), h1⟩

/-- **The two additions at a root** `v`: they set its values to `val v + δ₁` and
`val2 v + δ₂`, raise the potential by at most their absolute values, and keep the other nodes. -/
lemma allV_root_pair {n v : ℕ} {Fo : Forest} (hv : v < n) (hp : Fo.par v = n) (δ₁ δ₂ : ℤ)
    {Vb : ℝ} (hV : pot n Fo + |Fo.val v + δ₁| + |Fo.val2 v + δ₂| ≤ Vb) :
    AllV Vb n Fo [.add v δ₁, .add2 v δ₂] ∧
      pot n (runOpsE n Fo [.add v δ₁, .add2 v δ₂]).1 ≤
        pot n Fo + |Fo.val v + δ₁| + |Fo.val2 v + δ₂| ∧
      ∀ u, u ≠ v → Agree Fo (runOpsE n Fo [.add v δ₁, .add2 v δ₂]).1 u := by
  have h1 := pot_add_root hv hp (δ₁ : ℝ)
  set F1 := addPath Fo n v δ₁ with hF1
  have hp1 : F1.par v = n := hp
  have h2 := pot_add2_root hv hp1 (δ₂ : ℝ)
  have hF2 : (runOpsE n Fo [.add v δ₁, .add2 v δ₂]).1 = addPath2 F1 n v δ₂ := rfl
  have hv2 : F1.val2 v = Fo.val2 v := rfl
  rw [hv2] at h2
  have a1 := abs_nonneg (Fo.val v + δ₁)
  have a2 := abs_nonneg (Fo.val2 v + δ₂)
  refine ⟨⟨vbnd_of_pot (by linarith), vbnd_of_pot ?_, vbnd_of_pot ?_⟩, ?_,
    fun u hu => ?_⟩
  · show pot n F1 ≤ Vb; linarith
  · show pot n (addPath2 F1 n v δ₂) ≤ Vb; linarith
  · rw [hF2]; linarith
  · rw [hF2]
    have hr1 : u ∉ rootPath Fo n v := by rw [rootPath_of_root hv hp]; simpa using hu
    have hr2 : u ∉ rootPath F1 n v := by rw [rootPath_of_root hv hp1]; simpa using hu
    exact (agree_addPath hr1 _).trans (agree_addPath2 hr2 _)

/-! ### The pivot -/

variable {M : CombMap D V F} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

/-- **The values along a pivot with the amount `0`**: from a forest storing the data, the values
of the forests before each of the sixteen operations of the pivot are bounded by the potential
plus `|wt a - φ a| + |wt (rev a) + φ a| + |φ b| + |φ (rev b)|` (`a` the parent dart of `y`), and
so is the potential at the end. -/
theorem pivot_pot (hM : M.IsPlane) (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {fe : F}
    {Lo : ℝ} {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val) {y : V} (hy : y ≠ T.root) {b : D}
    (hby : M.dual.face (M.dual.rev b) = y) (hna : ¬ T.Anc y (M.dual.face b)) (hbT : ¬ T.InT b)
    (wt : D → ℤ) {c : ℤ} (hc0 : c = 0) {v₁ v₂ w₁ w₂ : ℤ} (hv₁ : Fo.val (ιe (T.par y)) = v₁)
    (hv₂ : Fo.val2 (ιe (T.par y)) = v₂) (hw₁ : Fo.val (ιg b) = w₁)
    (hw₂ : Fo.val2 (ιg b) = w₂) {Vb : ℝ}
    (hV : pot n Fo + ((|wt (T.par y) - φ (T.par y) - c| + |wt (M.rev (T.par y)) + φ (T.par y) + c|
      + |φ b| + |φ (M.rev b)| : ℤ) : ℝ) ≤ Vb) :
    AllV Vb n Fo (pivotOps (ιf (M.face (T.par y))) (ιf (M.face (M.rev (T.par y))))
        (ιe (T.par y)) (ιe b)
        (cutNode (runOpsE n Fo (pivotPre (ιf (M.face (T.par y)))
          (ιf (M.face (M.rev (T.par y)))) c)).1 ιf ιe M b)
        (ιf fe) (ιv y) (ιg (T.par y)) (ιg b) (ιv (M.tail b)) c
        (wt (T.par y) - φ (T.par y) - c - v₁) (wt (M.rev (T.par y)) + φ (T.par y) + c - v₂)
        (φ b - w₁) (φ (M.rev b) - w₂)) ∧
      pot n (runOpsE n Fo (pivotOps (ιf (M.face (T.par y))) (ιf (M.face (M.rev (T.par y))))
        (ιe (T.par y)) (ιe b)
        (cutNode (runOpsE n Fo (pivotPre (ιf (M.face (T.par y)))
          (ιf (M.face (M.rev (T.par y)))) c)).1 ιf ιe M b)
        (ιf fe) (ιv y) (ιg (T.par y)) (ιg b) (ιv (M.tail b)) c
        (wt (T.par y) - φ (T.par y) - c - v₁) (wt (M.rev (T.par y)) + φ (T.par y) + c - v₂)
        (φ b - w₁) (φ (M.rev b) - w₂))).1 ≤ pot n Fo +
        ((|wt (T.par y) - φ (T.par y) - c| + |wt (M.rev (T.par y)) + φ (T.par y) + c|
          + |φ b| + |φ (M.rev b)| : ℤ) : ℝ) := by
  classical
  subst hc0
  obtain ⟨C, β, β₂, hroot, hoff, hRc, hIc, hLo⟩ := hS.cot
  obtain ⟨z, hz, hzb, hza⟩ := exists_cut_face hM hoff hy hby hna hbT
  set a := T.par y with ha
  have haT : T.InT a := T.inT_par hy
  have hoffa : ∀ w, w ≠ C.root → a ≠ C.par w ∧ a ≠ M.rev (C.par w) := fun w hw =>
    ⟨fun h => hoff w hw (h ▸ haT), fun h => hoff w hw (by
      have := T.inT_rev (h ▸ haT); simpa [CombMap.dual, M.rev_rev] using this)⟩
  have hba : b ≠ a := fun h => hbT (h ▸ haT)
  have hbra : b ≠ M.rev a := fun h => hbT (by
    have : T.InT (M.rev a) := T.inT_rev haT
    rw [← h] at this; exact this)
  set os1 := cotreeOps ιf ιe C a z fe 0 (wt a - φ a - 0 - v₁)
      (wt (M.rev a) + φ a + 0 - v₂) with hos1
  obtain ⟨-, -, C', -, -, -, hag1, -⟩ :=
    cotreePivot_trep hM hoff hL.dual hL.hf hRc hIc hy hby hna hbT hz hzb hza fe φ wt 0 hv₁ hv₂
      hos1
  -- the cut face (as in `pivot_ops_stored`)
  have hcut : cutNode (runOpsE n Fo (pivotPre (ιf (M.face a)) (ιf (M.face (M.rev a))) 0)).1
      ιf ιe M b = ιf z := by
    set C1 := C.reroot (M.face a) with hC1
    have h1 := evert_trep hRc hL.dual hL.hf (M.face a)
    have h2 := addBoth_trep h1 hL.dual hL.hf (M.face (M.rev a)) (-((0 : ℤ) : ℝ))
    have hF2 : (runOpsE n Fo (pivotPre (ιf (M.face a)) (ιf (M.face (M.rev a))) 0)).1 =
        addPath2 (addPath (evert Fo n (ιf (M.face a))) n (ιf (M.face (M.rev a)))
          (-((0 : ℤ) : ℝ))) n (ιf (M.face (M.rev a))) (-(-((0 : ℤ) : ℝ))) := by
      simp only [pivotPre, runOpsE, EOp.apply, Int.cast_neg, neg_neg]
    have hz' : z ≠ C1.root := hz
    have hpe := h2.pe z hz'
    have hhz := C1.head_par z hz'
    unfold cutNode
    rw [hF2]
    rcases hzb with h | h
    · rw [h] at hpe hhz
      rw [ite_eq_left hpe, hhz]
    · rw [h, hL.dual.e_rev] at hpe
      rw [h, M.rev_rev] at hhz
      rw [hpe]
      by_cases hff : ιf (M.face (M.rev b)) = ιf (M.face b)
      · rw [ite_eq_left hff, hff, hhz]
      · rw [ite_eq_right hff, hhz]
  have e2 : ιe ((C.reroot (M.face a)).par z) = ιe b := by
    rcases hzb with h | h
    · rw [h]
    · rw [h, hL.dual.e_rev]
  have hops : pivotOps (ιf (M.face a)) (ιf (M.face (M.rev a))) (ιe a) (ιe b)
      (cutNode (runOpsE n Fo (pivotPre (ιf (M.face a)) (ιf (M.face (M.rev a))) 0)).1 ιf ιe M b)
      (ιf fe) (ιv y) (ιg a) (ιg b) (ιv (M.tail b)) 0 (wt a - φ a - 0 - v₁)
      (wt (M.rev a) + φ a + 0 - v₂) (φ b - w₁) (φ (M.rev b) - w₂) =
      os1 ++ reparentOps ιv ιg T y b (φ b - w₁) (φ (M.rev b) - w₂) := by
    rw [hcut, hos1]
    simp only [pivotOps, cotreeOps, exchangeOps, reparentOps, e2, hL.dual.e_rev, reroot_root,
      List.cons_append, List.nil_append]
    rfl
  rw [hops]
  -- the cotree part: the first five operations, of amount `0`
  set A : List EOp := [.evert (ιf (M.face a)), .add (ιf (M.face (M.rev a))) (-0),
    .add2 (ιf (M.face (M.rev a))) 0, .cut (ιf z), .cut (ιe ((C.reroot (M.face a)).par z))]
    with hA
  set nea := ιe (M.rev a) with hnea
  set Bl : List EOp := [.link nea (ιf (M.face (M.rev a))),
    .link (ιf (C.reroot (M.face a)).root) nea, .evert (ιf fe)] with hBl
  have hsplit : os1 = A ++ ([.add nea (wt a - φ a - 0 - v₁),
      .add2 nea (wt (M.rev a) + φ a + 0 - v₂)] ++ Bl) := by
    rw [hos1]; rfl
  have hA0 : amtSum A = 0 := by simp [hA, amtSum, EOp.amt]
  have hB0 : amtSum Bl = 0 := by simp [hBl, amtSum, EOp.amt]
  set FA := (runOpsE n Fo A).1 with hFA
  have hFA' : FA = DynTree.cut (DynTree.cut (evert Fo n (ιf (M.face a))) n (ιf z)) n
      (ιe ((C.reroot (M.face a)).par z)) := by
    simp only [hFA, hA, runOpsE, EOp.apply, neg_zero, Int.cast_zero, addPath_zero, addPath2_zero]
  -- the isolated node of the edge of `a`
  have hnea_lt : nea < n := hL.dual.e_lt _
  have hoffra : ∀ w, w ≠ C.root → M.rev a ≠ C.par w ∧ M.rev a ≠ M.rev (C.par w) := fun w hw =>
    ⟨fun h => (hoffa w hw).2 (by rw [← h, M.rev_rev]), fun h => (hoffa w hw).1
      (by have := congrArg M.rev h; rwa [M.rev_rev, M.rev_rev] at this)⟩
  have hnp : nea ∉ rootPath Fo n (ιf (M.face a)) := by
    rw [rootPath_rep hRc hL.dual.f_lt hL.dual.e_lt hL.hf]
    exact not_mem_tpath_off hL.dual hoffra le_rfl
  have hneb : nea ≠ ιe ((C.reroot (M.face a)).par z) := by
    rw [e2]; intro h
    rcases hL.dual.e_eq _ _ h with h | h
    · exact hbra h
    · exact hba (by rw [h, M.rev_rev])
  have hagA : Agree Fo FA nea := by
    rw [hFA']
    exact ((agree_evert hnp).trans (agree_cut' (hL.dual.fe z _).symm)).trans (agree_cut' hneb)
  have hpA : FA.par nea = n := by
    rw [hagA.1]; exact hIc (M.rev a) hoffra
  have hvA : FA.val nea = v₁ := by rw [hagA.2.1, hnea, hL.dual.e_rev, hv₁]
  have hv2A : FA.val2 nea = v₂ := by rw [hagA.2.2, hnea, hL.dual.e_rev, hv₂]
  -- the bounds
  set t₁ : ℤ := |wt a - φ a - 0| with ht₁
  set t₂ : ℤ := |wt (M.rev a) + φ a + 0| with ht₂
  set t₃ : ℤ := |φ b| with ht₃
  set t₄ : ℤ := |φ (M.rev b)| with ht₄
  have n1 : 0 ≤ t₁ := abs_nonneg _
  have n2 : 0 ≤ t₂ := abs_nonneg _
  have n3 : 0 ≤ t₃ := abs_nonneg _
  have n4 : 0 ≤ t₄ := abs_nonneg _
  have hV' : pot n Fo + ((t₁ + t₂ + t₃ + t₄ : ℤ) : ℝ) ≤ Vb := hV
  push_cast at hV'
  have r1 : (0 : ℝ) ≤ t₁ := by exact_mod_cast n1
  have r2 : (0 : ℝ) ≤ t₂ := by exact_mod_cast n2
  have r3 : (0 : ℝ) ≤ t₃ := by exact_mod_cast n3
  have r4 : (0 : ℝ) ≤ t₄ := by exact_mod_cast n4
  obtain ⟨aA, pA⟩ := allV_amt0 (n := n) (Fo := Fo) hA0 (Vb := Vb) (by linarith)
  have e1 : |FA.val nea + ((wt a - φ a - 0 - v₁ : ℤ) : ℝ)| = (t₁ : ℝ) := by
    rw [hvA, ht₁]; push_cast; ring_nf
  have e2' : |FA.val2 nea + ((wt (M.rev a) + φ a + 0 - v₂ : ℤ) : ℝ)| = (t₂ : ℝ) := by
    rw [hv2A, ht₂]; push_cast; ring_nf
  obtain ⟨aP, pP, gP⟩ := allV_root_pair hnea_lt hpA (wt a - φ a - 0 - v₁)
    (wt (M.rev a) + φ a + 0 - v₂) (Vb := Vb) (by rw [e1, e2']; linarith)
  rw [e1, e2'] at pP
  set FP := (runOpsE n FA [.add nea (wt a - φ a - 0 - v₁),
      .add2 nea (wt (M.rev a) + φ a + 0 - v₂)]).1 with hFP
  obtain ⟨aB, pB⟩ := allV_amt0 (n := n) (Fo := FP) hB0 (Vb := Vb) (by linarith)
  have hF1 : (runOpsE n Fo os1).1 = (runOpsE n FP Bl).1 := by
    rw [hsplit, runOpsE_append, runOpsE_append]
  have a1 : AllV Vb n Fo os1 := by
    rw [hsplit]
    refine AllV.append aA (AllV.append aP ?_)
    exact aB
  have p1 : pot n (runOpsE n Fo os1).1 ≤ pot n Fo + t₁ + t₂ := by rw [hF1]; linarith
  -- the tree part
  set F1 := (runOpsE n Fo os1).1 with hF1d
  have hag : Agree Fo F1 (ιg b) := hag1 _ (fun x => hL.gf b x) (hL.ge b)
  have hoffb : ∀ x, x ≠ T.root → b ≠ T.par x ∧ b ≠ M.dual.rev (T.par x) :=
    off_iff_not_inT.2 hbT
  have hngb_lt : ιg b < n := hL.prim.e_lt b
  have hg1 : ιg b ≠ ιv y := (hL.prim.fe y b).symm
  have hg2 : ιg b ≠ ιg a := fun h => by
    rcases hL.prim.e_eq _ _ h with h | h
    · exact hba h.symm
    · exact hbra (by rw [h]; exact (M.rev_rev b).symm)
  set R1 : List EOp := [.cut (ιv y), .cut (ιg a)] with hR1
  set R3 : List EOp := [.link (ιg b) (ιv (M.dual.face b)), .link (ιv y) (ιg b)] with hR3
  have hRsplit : reparentOps ιv ιg T y b (φ b - w₁) (φ (M.rev b) - w₂) =
      R1 ++ ([.add (ιg b) (φ b - w₁), .add2 (ιg b) (φ (M.rev b) - w₂)] ++ R3) := rfl
  have hR10 : amtSum R1 = 0 := by simp [hR1, amtSum, EOp.amt]
  have hR30 : amtSum R3 = 0 := by simp [hR3, amtSum, EOp.amt]
  set G1 := (runOpsE n F1 R1).1 with hG1
  have hagG : Agree Fo G1 (ιg b) := by
    have : G1 = DynTree.cut (DynTree.cut F1 n (ιv y)) n (ιg a) := rfl
    rw [this]
    exact (hag.trans (agree_cut' hg1)).trans (agree_cut' hg2)
  have hpG : G1.par (ιg b) = n := by rw [hagG.1]; exact hS.treeIso b hoffb
  have f1 : |G1.val (ιg b) + ((φ b - w₁ : ℤ) : ℝ)| = (t₃ : ℝ) := by
    rw [hagG.2.1, hw₁, ht₃]; push_cast; ring_nf
  have f2 : |G1.val2 (ιg b) + ((φ (M.rev b) - w₂ : ℤ) : ℝ)| = (t₄ : ℝ) := by
    rw [hagG.2.2, hw₂, ht₄]; push_cast; ring_nf
  obtain ⟨aR1, pR1⟩ := allV_amt0 (n := n) (Fo := F1) hR10 (Vb := Vb) (by linarith)
  obtain ⟨aQ, pQ, -⟩ := allV_root_pair hngb_lt hpG (φ b - w₁) (φ (M.rev b) - w₂) (Vb := Vb)
    (by rw [f1, f2]; linarith)
  rw [f1, f2] at pQ
  set GQ := (runOpsE n G1 [.add (ιg b) (φ b - w₁), .add2 (ιg b) (φ (M.rev b) - w₂)]).1
    with hGQ
  obtain ⟨aR3, pR3⟩ := allV_amt0 (n := n) (Fo := GQ) hR30 (Vb := Vb) (by linarith)
  refine ⟨AllV.append a1 ?_, ?_⟩
  · rw [hRsplit]
    exact AllV.append aR1 (AllV.append aQ aR3)
  · rw [runOpsE_append, hRsplit, runOpsE_append, runOpsE_append]
    push_cast
    have : pot n (runOpsE n GQ R3).1 ≤ pot n GQ := pR3
    linarith

end STFlow

end PlanarFlow
