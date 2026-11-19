module

public import PlanarFlow.BKMNW.MfStepSem

/-!
# The step invariants at the holes of one `sepStep`

At a node call the flow before the hole `i` of the part `j` (`SCtx.hole j πj i`) is the input of
CycleToSingleSinkLimitedMaxFlow, and the flow after it (`SCtx.c2s j πj i H`) the input of
SingleSourceToCycleLimitedMaxFlow. The proof of `sepStep_spec` (Lemmas A.4–A.10) shows that their
preconditions hold there; this file exports them:

* `HoleC2S` (pseudoflow, the part off the hole, the hole a path's vertex set, no vertex of `C⁺`
  with positive outflow — the hypotheses of `c2sG_spec`), `HoleS2C` (the same for `s2c`);
* `ninv_pre1`, **`ninv_pre2`** (the two preconditions from the invariant of lines 9–12);
* `SegPre` (the hypotheses of `nodeStep_core` before the part `j`), **`SCtx.segPre_all`**;
* `SCtx.ninv_hole` (the invariant `NInv` before every hole);
* **`SCtx.holeInv`**: from the hypotheses of `sepStep_spec` (with `P = univ`), at every part `j`
  and every hole `i`, `HoleC2S` for `C.hole j πj i` and `HoleS2C` for `C.c2s j πj i H`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Orbit CombMap

section Inv

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'}

variable (M') in
/-- **The preconditions of CycleToSingleSinkLimitedMaxFlow** at a hole: `g` a pseudoflow, the
part `π` off the hole `H`, `H` the vertex set of a simple path, and no vertex of `C⁺` (reached by
residual paths from the vertices of `π` with positive inflow) with positive outflow. -/
structure HoleC2S (U g : D' → ℤ) (π : SPath M') (H : Finset V') : Prop where
  pseudo : IsPseudo M' U g
  disj : Disjoint π.verts H
  path : ∃ πH : SPath M', πH.verts = H
  pre : ∀ v ∈ fwdReach M' U g (posSet M' g π.verts) π.verts, M'.div g v ≤ 0

variable (M') in
/-- **The preconditions of SingleSourceToCycleLimitedMaxFlow** at a hole. -/
structure HoleS2C (U g : D' → ℤ) (π : SPath M') (H : Finset V') : Prop where
  pseudo : IsPseudo M' U g
  disj : Disjoint π.verts H
  path : ∃ πH : SPath M', πH.verts = H
  pre : ∀ v ∈ bwdReach M' U g (negSet M' g π.verts) π.verts, 0 ≤ M'.div g v

/-- The precondition of `c2s` from the invariant of lines 9–12. -/
lemma ninv_pre1 {U f : D' → ℤ} {S T A C : Finset V'} {Hd : List (Finset V')}
    (h : NInv M' U f S T A C Hd) :
    ∀ v ∈ fwdReach M' U f (posSet M' f C) C, M'.div f v ≤ 0 := by
  obtain ⟨Y₀, hY₀1, hY₀2, hY₀3⟩ := h.pn
  have hCp : fwdReach M' U f (posSet M' f C) C ⊆ Y₀ := fwdReach_sub hY₀3 hY₀1
  intro v hv
  by_contra hpos
  exact disjoint_left.1 hY₀2 (hCp hv) (mem_negSet.2 ⟨fwdReach_subset hv, by omega⟩)

/-- **The precondition of `s2c`** after `c2s`, from the invariant of lines 9–12 (the first half
of the proof of `NInv.hole`). -/
lemma ninv_pre2 {U f f' : D' → ℤ} {S T A C H : Finset V'} {Hd : List (Finset V')}
    (h : NInv M' U f S T A C Hd) (hCH : Disjoint C H) (o1 : C2SOut M' U f f' C H) :
    ∀ v ∈ bwdReach M' U f' (negSet M' f' C) C, 0 ≤ M'.div f' v := by
  classical
  obtain ⟨Y₀, hY₀1, hY₀2, hY₀3⟩ := h.pn
  have hCp : fwdReach M' U f (posSet M' f C) C ⊆ Y₀ := fwdReach_sub hY₀3 hY₀1
  obtain ⟨o1ps, o1eq, o1np, o1sink, o1nopath⟩ := o1
  generalize hCp' : fwdReach M' U f (posSet M' f C) C = Cp at hCp o1eq o1np
  have hposCp : posSet M' f C ⊆ Cp := hCp' ▸ sub_fwdReach posSet_subset
  have hpos' : posSet M' f' C ⊆ Cp := fun v hv => by
    obtain ⟨hvC, hlt⟩ := mem_posSet.1 hv
    by_contra hn
    rw [o1eq v hn (disjoint_left.1 hCH hvC)] at hlt
    exact hn (hposCp (mem_posSet.2 ⟨hvC, hlt⟩))
  have hneg' : negSet M' f' C ⊆ negSet M' f C := fun v hv => by
    obtain ⟨hvC, hlt⟩ := mem_negSet.1 hv
    have hn : v ∉ Cp := fun h' => by have := o1np v h'; omega
    rw [o1eq v hn (disjoint_left.1 hCH hvC)] at hlt
    exact mem_negSet.2 ⟨hvC, hlt⟩
  have pn₁ : NoPath M' U f' (posSet M' f' C) (negSet M' f' C) :=
    ⟨Y₀, hpos'.trans hCp, disjoint_of_subset_right hneg' hY₀2,
      hY₀3.src h.pseudo o1ps hCp o1eq o1sink⟩
  obtain ⟨Y₁, hY₁1, hY₁2, hY₁3⟩ := pn₁
  have hCm : Disjoint (bwdReach M' U f' (negSet M' f' C) C) Y₁ := bwdReach_disj hY₁3 hY₁2
  intro v hv
  by_contra hneg
  exact disjoint_left.1 hCm hv (hY₁1 (mem_posSet.2 ⟨bwdReach_subset hv, by omega⟩))

end Inv

section Step

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'}

/-- The vertices of the parts from the part `j` on. -/
def segRest (L : List (SPath M')) (j : ℕ) : Finset V' := hunion ((L.drop j).map SPath.verts)

/-- **The hypotheses of `nodeStep_core` before the part `j`**. -/
def SegPre (U : D' → ℤ) (S T : Finset V') (Hs : List (Finset V')) (L : List (SPath M'))
    (j : ℕ) (f : D' → ℤ) : Prop :=
  IsPseudo M' U f ∧
    (∀ v, v ∉ S → v ∉ T → v ∉ hunion Hs ∪ segRest L j → M'.div f v = 0) ∧
    NoPath M' U f S (T ∪ (hunion Hs ∪ segRest L j)) ∧
    NoPath M' U f ((hunion Hs ∪ segRest L j) ∪ S) T

lemma segRest_eq {L : List (SPath M')} {j : ℕ} {π : SPath M'} (hj : L[j]? = some π) :
    segRest L j = π.verts ∪ segRest L (j + 1) := by
  have hlt : j < L.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  have e : L.drop j = π :: L.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hlt]
    rw [List.getElem?_eq_getElem hlt] at hj
    cases hj; rfl
  rw [segRest, segRest, e, List.map_cons, hunion_cons]

lemma hunion_sHoles (Hs : List (Finset V')) (L : List (SPath M')) (j : ℕ) :
    hunion (sHoles Hs L j) = hunion Hs ∪ segRest L (j + 1) := by
  rw [sHoles, hunion_append']; rfl

/-- The holes of the step on any part are paths' vertex sets. -/
lemma sHoles_path {Hs : List (Finset V')} (hHs : ∀ H ∈ Hs, ∃ πH : SPath M', πH.verts = H)
    (L : List (SPath M')) (j : ℕ) :
    ∀ H ∈ sHoles Hs L j, ∃ πH : SPath M', πH.verts = H := by
  intro H hH
  rcases List.mem_append.1 hH with hH | hH
  · exact hHs H hH
  · obtain ⟨π', -, rfl⟩ := List.mem_map.1 hH; exact ⟨π', rfl⟩

/-- The part `j` avoids the terminals and the holes of the step on it. -/
lemma seg_disj {S T : Finset V'} {Hs : List (Finset V')} {L : List (SPath M')}
    (hπs : ∀ π ∈ L, Disjoint π.verts (S ∪ T ∪ hunion Hs))
    (hpw : (L.map SPath.verts).Pairwise Disjoint) {j : ℕ} {π : SPath M'} (hj : L[j]? = some π) :
    Disjoint π.verts (S ∪ T ∪ hunion (sHoles Hs L j)) := by
  have hlt : j < L.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  have e : L.drop j = π :: L.drop (j + 1) := by
    rw [List.drop_eq_getElem_cons hlt]
    rw [List.getElem?_eq_getElem hlt] at hj
    cases hj; rfl
  have hπ : π ∈ L := List.mem_of_getElem? hj
  have hpw' : ((L.drop j).map SPath.verts).Pairwise Disjoint := by
    rw [List.map_drop]; exact hpw.drop
  rw [e, List.map_cons, List.pairwise_cons] at hpw'
  have hR : Disjoint π.verts (segRest L (j + 1)) :=
    disjoint_left.2 fun v hv hv' => by
      obtain ⟨H, hH, hvH⟩ := mem_hunion.1 hv'
      exact disjoint_left.1 (hpw'.1 H hH) hv hvH
  rw [hunion_sHoles, ← union_assoc]
  exact disjoint_union_right.2 ⟨hπs π hπ, hR⟩

variable {u : D' → ℤ}

/-- The specification at `P = univ` with the capacities unrestricted. -/
lemma spec_c2s_univ {O : NodeOracles M'} (hO : O.Spec u) {f : D' → ℤ} {π : SPath M'}
    {H : Finset V'} (hf : IsPseudo M' u f) (hCH : Disjoint π.verts H)
    (hH : ∃ πH : SPath M', πH.verts = H)
    (hpre : ∀ v ∈ fwdReach M' u f (posSet M' f π.verts) π.verts, M'.div f v ≤ 0) :
    C2SOut M' u f (O.c2s u f π H) π.verts H := by
  have := hO.c2s univ f π H
  rw [capOn_univ] at this
  exact this hf hCH hH hpre

lemma spec_s2c_univ {O : NodeOracles M'} (hO : O.Spec u) {f : D' → ℤ} {π : SPath M'}
    {H : Finset V'} (hf : IsPseudo M' u f) (hCH : Disjoint π.verts H)
    (hH : ∃ πH : SPath M', πH.verts = H)
    (hpre : ∀ v ∈ bwdReach M' u f (negSet M' f π.verts) π.verts, 0 ≤ M'.div f v) :
    S2COut M' u f (O.s2c u f π H) π.verts H := by
  have := hO.s2c univ f π H
  rw [capOn_univ] at this
  exact this hf hCH hH hpre

lemma spec_fix_univ {O : NodeOracles M'} (hO : O.Spec u) {f : D' → ℤ} (π : SPath M')
    (hf : IsPseudo M' u f) : FixOut M' u f π.verts (O.fix u f π) := by
  have := hO.fix univ f π
  rw [capOn_univ] at this
  exact this hf

/-- `nodeStep_core` at `P = univ`. -/
lemma nodeStep_core_univ {O : NodeOracles M'} (hO : O.Spec u) {S T : Finset V'}
    {Hs : List (Finset V')} (π : SPath M')
    (hHs : ∀ H ∈ Hs, ∃ πH : SPath M', πH.verts = H)
    (hC : Disjoint π.verts (S ∪ T ∪ hunion Hs)) {f : D' → ℤ}
    (hps : IsPseudo M' u f)
    (hcons : ∀ v, v ∉ S → v ∉ T → v ∉ hunion Hs ∪ π.verts → M'.div f v = 0)
    (h1 : NoPath M' u f S (T ∪ (hunion Hs ∪ π.verts)))
    (h2 : NoPath M' u f ((hunion Hs ∪ π.verts) ∪ S) T) :
    MSOut M' u S T (hunion Hs) (nodeStep O u S T Hs univ π f) := by
  have := @nodeStep_core _ _ _ _ _ _ _ _ _ M' O u hO univ (fun d _ => mem_univ _) S T Hs π hHs hC f
  rw [capOn_univ] at this
  exact this hps hcons h1 h2

/-- **The hypotheses of `nodeStep_core` hold before every part.** -/
theorem segPre_all {O : NodeOracles M'} (hO : O.Spec u) {S T : Finset V'}
    {Hs : List (Finset V')} (hHs : ∀ H ∈ Hs, ∃ πH : SPath M', πH.verts = H)
    {L : List (SPath M')} (hπs : ∀ π ∈ L, Disjoint π.verts (S ∪ T ∪ hunion Hs))
    (hpw : (L.map SPath.verts).Pairwise Disjoint) {f : D' → ℤ}
    (h0 : SegPre u S T Hs L 0 f) :
    ∀ j, j ≤ L.length → SegPre u S T Hs L j (sst O u S T Hs univ L f j)
  | 0, _ => h0
  | j + 1, hj => by
    have ih := segPre_all hO hHs hπs hpw h0 j (by omega)
    obtain ⟨hps, hcons, h1, h2⟩ := ih
    have hlt : j < L.length := by omega
    set π := L[j] with hπ
    have hj' : L[j]? = some π := List.getElem?_eq_getElem hlt
    have e : hunion (sHoles Hs L j) ∪ π.verts = hunion Hs ∪ segRest L j := by
      rw [hunion_sHoles, segRest_eq hj']
      ext v; simp only [mem_union]; tauto
    have hstep : sst O u S T Hs univ L f (j + 1) =
        nodeStep O u S T (sHoles Hs L j) univ π (sst O u S T Hs univ L f j) := by
      show segStep O u S T Hs univ L j _ = _
      simp only [segStep, hj']
    rw [← e] at hcons h1 h2
    have o := nodeStep_core_univ hO π (sHoles_path hHs L j) (seg_disj hπs hpw hj') hps hcons h1 h2
    rw [← hstep, hunion_sHoles] at o
    exact ⟨o.pseudo, o.cons, o.st.union_right o.sa, o.at'.union_left o.st⟩

/-- **The invariant of lines 9–12 before every hole of the part `j`.** -/
theorem ninv_hole {O : NodeOracles M'} (hO : O.Spec u) {S T : Finset V'}
    {Hl : List (Finset V')} (hHl : ∀ H ∈ Hl, ∃ πH : SPath M', πH.verts = H) {π : SPath M'}
    (hC : Disjoint π.verts (S ∪ T ∪ hunion Hl)) {g : D' → ℤ}
    (h0 : NInv M' u g S T (hunion Hl) π.verts []) :
    ∀ i, i ≤ Hl.length → NInv M' u (hst O u π Hl g i) S T (hunion Hl) π.verts (Hl.take i)
  | 0, _ => by simpa [hst] using h0
  | i + 1, hi => by
    have ih := ninv_hole hO hHl hC h0 i (by omega)
    have hlt : i < Hl.length := by omega
    set H := Hl[i] with hH
    have hi' : Hl[i]? = some H := List.getElem?_eq_getElem hlt
    have hmem : H ∈ Hl := List.mem_of_getElem? hi'
    have hHA : H ⊆ hunion Hl := subset_hunion hmem
    have hCA : Disjoint π.verts (hunion Hl) := disjoint_of_subset_right subset_union_right hC
    have hCH : Disjoint π.verts H := disjoint_of_subset_right hHA hCA
    have hHp := hHl H hmem
    have hstep : hst O u π Hl g (i + 1) = O.s2c u (O.c2s u (hst O u π Hl g i) π H) π H := by
      show hStep O u π Hl i _ = _
      simp only [hStep, hi']
    have htake : Hl.take (i + 1) = Hl.take i ++ [H] := by
      rw [List.take_add_one, hi']; rfl
    rw [hstep, htake]
    exact ih.hole hHA hCH (fun pre => spec_c2s_univ hO ih.pseudo hCH hHp pre)
      (fun pre => spec_s2c_univ hO (spec_c2s_univ hO ih.pseudo hCH hHp (ninv_pre1 ih)).pseudo hCH hHp pre)

/-- **The step invariants at every hole of every part of one `sepStep`** (with `P = univ`, the
capacities `C.U` meeting the specification), from the hypotheses of `sepStep_spec`. -/
theorem SCtx.holeInv (C : SCtx M') (hO : C.O.Spec C.U) (hP : C.P = univ)
    (hHs : ∀ H ∈ C.Hs, ∃ πH : SPath M', πH.verts = H)
    (hπs : ∀ π ∈ C.L, Disjoint π.verts (C.S ∪ C.T ∪ hunion C.Hs))
    (hpw : (C.L.map SPath.verts).Pairwise Disjoint)
    (hps : IsPseudo M' C.U C.f)
    (hcons : ∀ v, v ∉ C.S → v ∉ C.T → v ∉ hunion C.Hs ∪ hunion (C.L.map SPath.verts) →
      M'.div C.f v = 0)
    (h1 : NoPath M' C.U C.f C.S (C.T ∪ (hunion C.Hs ∪ hunion (C.L.map SPath.verts))))
    (h2 : NoPath M' C.U C.f ((hunion C.Hs ∪ hunion (C.L.map SPath.verts)) ∪ C.S) C.T)
    {j i : ℕ} {πj : SPath M'} {H : Finset V'} (hj : C.L[j]? = some πj)
    (hi : (C.holes j)[i]? = some H) :
    HoleC2S M' C.U (C.hole j πj i) πj H ∧ HoleS2C M' C.U (C.c2s j πj i H) πj H := by
  have hlt : j < C.L.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hj; cases hj
  have hilt : i < (C.holes j).length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hi; cases hi
  have h0 : SegPre C.U C.S C.T C.Hs C.L 0 C.f := ⟨hps, hcons, h1, h2⟩
  obtain ⟨sps, scons, s1, s2⟩ := segPre_all hO hHs hπs hpw h0 j hlt.le
  have hseg : C.seg j = sst C.O C.U C.S C.T C.Hs univ C.L C.f j := by
    rw [SCtx.seg, hP]
  rw [← hseg] at sps scons s1 s2
  have hC := seg_disj hπs hpw hj
  have hHl := sHoles_path hHs C.L j
  have e : hunion (sHoles C.Hs C.L j) ∪ πj.verts = hunion C.Hs ∪ segRest C.L j := by
    rw [hunion_sHoles, segRest_eq hj]
    ext v; simp only [mem_union]; tauto
  rw [← e] at scons s1 s2
  have n0 := NInv.ofFix (A := hunion (sHoles C.Hs C.L j)) sps scons s1 s2
    (spec_fix_univ hO πj sps)
  have n := ninv_hole hO hHl hC n0 i hilt.le
  have hmem : H ∈ C.holes j := List.mem_of_getElem? hi
  have hHA : H ⊆ hunion (sHoles C.Hs C.L j) := subset_hunion hmem
  have hCH : Disjoint πj.verts H :=
    disjoint_of_subset_right hHA (disjoint_of_subset_right subset_union_right hC)
  have hHp := hHl H hmem
  have ehole : C.hole j πj i = hst C.O C.U πj (sHoles C.Hs C.L j) (C.O.fix C.U (C.seg j) πj) i :=
    rfl
  rw [← ehole] at n
  have o1 := spec_c2s_univ hO n.pseudo hCH hHp (ninv_pre1 n)
  exact ⟨⟨n.pseudo, hCH, hHp, (ninv_pre1 n)⟩, ⟨o1.pseudo, hCH, hHp, ninv_pre2 n hCH o1⟩⟩

end Step

end MfDrv

end BKMNW

end PlanarFlow
