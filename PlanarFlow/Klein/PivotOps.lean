module

public import PlanarFlow.Klein.LCTTrip

/-!
# The operations of a pivot, by their nodes

`pivot_stored` gives the sixteen operations of a pivot by their existence: they name the cut face
`z` of `exists_cut_face`, a face of a cotree that `Stored` only gives by its existence. A program
computes them from the stored forest: this file states them by the nodes a program can read.

* `stored_min2v`: **the query `min2` with its value**: when the least second value on the root
  path of the node of the face of the reverse of `e` is below the threshold, it is the value of a
  selected dart `d`, whose edge node is the argmin, oriented by the parent of that node
  (`stored_min2` with the value); the two faces of that dart differ.
* `pivotOps`: the sixteen operations by their nodes and amounts.
* `pivot_ops_stored`: **a pivot on the stored data by its nodes**: from the values `v₁, v₂` of the
  node of the edge of the old parent dart `a = T.par y` and `w₁, w₂` of the node of the edge of
  the new parent dart `b`, read in the forest before the pivot, and the parent of the node of the
  edge of `b` after the first three operations (which names the cut face), the operations
  `pivotOps` are those of `pivot_stored`: valid, printing nothing, storing the reparented tree.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

/-- **The query `min2` on the stored data, with its value**: below the threshold `z ≤ Lo`, the
least second value on the root path of the node of the face of the reverse of `e` is the value
of a dart `d` of least value on the path of the cotree from the face of `e` to the face of its
reverse, whose edge node is the argmin, oriented by the parent of that node; at or above the
threshold, every dart of the path has value at least `z`. -/
theorem stored_min2v (hM : M.IsPlane) (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {e : D}
    {Lo : ℝ} {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ (M.face e) Lo Fo T val) {z : ℤ} (hz : (z : ℝ) ≤ Lo) :
    ((pathMin2 Fo n (ιf (M.face (M.rev e)))).1 < z →
      ∃ d, (pathMin2 Fo n (ιf (M.face (M.rev e)))).2 = ιe d ∧
        (pathMin2 Fo n (ιf (M.face (M.rev e)))).1 = val d ∧
        Fo.par (ιe d) = ιf (M.face d) ∧ M.face d ≠ M.face (M.rev d) ∧
        T.chi (M.face e) (M.face (M.rev e)) d = 1 ∧
        val d < z ∧ ∀ d', T.chi (M.face e) (M.face (M.rev e)) d' = 1 → val d ≤ val d') ∧
      (¬ (pathMin2 Fo n (ιf (M.face (M.rev e)))).1 < z →
        ∀ d', T.chi (M.face e) (M.face (M.rev e)) d' = 1 → z ≤ val d') := by
  obtain ⟨C, β, β₂, hroot, hoff, hR, -, hLo⟩ := hS.cot
  have hβ : ∀ y, (z : ℝ) ≤ β₂ y := fun y => hz.trans (hLo y).2
  obtain ⟨h1, h2⟩ := lct_minpath hM hoff hR hL.dual.f_lt hL.dual.e_lt hL.hf hβ (M.face (M.rev e))
  rw [hroot] at h1 h2
  refine ⟨fun h => ?_, h2⟩
  obtain ⟨d, hd, hpar, hchi, hlt, hmin⟩ := h1 h
  obtain ⟨i, hi, hir, h2', h1', -⟩ := pathMin2_rep hR hL.dual.f_lt hL.dual.e_lt hL.hf
    (M.face (M.rev e)) fun y => lt_of_lt_of_le h (hβ y)
  have : C.par (C.up^[i] (M.face (M.rev e))) = d := by
    rcases hL.dual.e_eq _ _ (hd.symm.trans h2') with h | h
    · exact h
    · exfalso
      set x := C.up^[i] (M.face (M.rev e)) with hx
      have hp := hR.pe _ hir
      rw [h, hL.dual.e_rev, hpar] at hp
      have hf := hL.dual.f_inj hp
      have hrr := C.head_par _ hir
      rw [h, M.rev_rev] at hrr
      have hup : C.up x = x := by rw [C.up_of_ne hir, h, ← hf, hrr]
      have hdep := C.depth_up hir
      rw [hup] at hdep
      omega
  refine ⟨d, hd, by rw [h1', this], hpar, fun hff => ?_, hchi, hlt, hmin⟩
  -- the two faces of an edge of the cotree differ
  have hrr := C.head_par _ hir
  have hup : C.up (C.up^[i] (M.face (M.rev e))) = C.up^[i] (M.face (M.rev e)) := by
    rw [C.up_of_ne hir, this, hff, ← this, hrr]
  have hdep := C.depth_up hir
  rw [hup] at hdep
  omega

/-- **The sixteen operations of a pivot by their nodes**: on the cotree, `evert` at `nfa`, the
additions `-c`, `c` at `nfra`, the exchange of the edge `neb` (below the face `nz`) for the edge
`nea` (amounts `δ₁`, `δ₂`), `evert` at `nfe`; on the spanning tree, the reparenting of `yv` from
the edge `nga` to the edge `ngb` (amounts `δ₃`, `δ₄`) below `ntb`. -/
def pivotOps (nfa nfra nea neb nz nfe yv nga ngb ntb : ℕ) (c δ₁ δ₂ δ₃ δ₄ : ℤ) : List EOp :=
  [.evert nfa, .add nfra (-c), .add2 nfra c, .cut nz, .cut neb, .add nea δ₁, .add2 nea δ₂,
    .link nea nfra, .link nfa nea, .evert nfe, .cut yv, .cut nga, .add ngb δ₃, .add2 ngb δ₄,
    .link ngb ntb, .link yv ngb]

/-- The first three operations of a pivot. -/
def pivotPre (nfa nfra : ℕ) (c : ℤ) : List EOp := [.evert nfa, .add nfra (-c), .add2 nfra c]

/-- The node of the cut face: the face of the edge `b` that is not the parent of its node. -/
def cutNode (Fo : Forest) (ιf : F → ℕ) (ιe : D → ℕ) (M : CombMap D V F) (b : D) : ℕ :=
  if Fo.par (ιe b) = ιf (M.face b) then ιf (M.face (M.rev b)) else ιf (M.face b)

/-- **A pivot on the stored data by its nodes** (`pivot_stored` with the operations named). -/
theorem pivot_ops_stored (hM : M.IsPlane) (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {fe : F}
    {Lo : ℝ} {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val) {y : V} (hy : y ≠ T.root) {b : D}
    (hby : M.dual.face (M.dual.rev b) = y) (hna : ¬ T.Anc y (M.dual.face b)) (hbT : ¬ T.InT b)
    (wt : D → ℤ) (c : ℤ) {v₁ v₂ w₁ w₂ : ℤ} (hv₁ : Fo.val (ιe (T.par y)) = v₁)
    (hv₂ : Fo.val2 (ιe (T.par y)) = v₂) (hw₁ : Fo.val (ιg b) = w₁)
    (hw₂ : Fo.val2 (ιg b) = w₂) :
    ValidOpsE n Fo (pivotOps (ιf (M.face (T.par y))) (ιf (M.face (M.rev (T.par y))))
        (ιe (T.par y)) (ιe b)
        (cutNode (runOpsE n Fo (pivotPre (ιf (M.face (T.par y)))
          (ιf (M.face (M.rev (T.par y)))) c)).1 ιf ιe M b)
        (ιf fe) (ιv y) (ιg (T.par y)) (ιg b) (ιv (M.tail b)) c
        (wt (T.par y) - φ (T.par y) - c - v₁) (wt (M.rev (T.par y)) + φ (T.par y) + c - v₂)
        (φ b - w₁) (φ (M.rev b) - w₂)) ∧
      (runOpsE n Fo (pivotOps (ιf (M.face (T.par y))) (ιf (M.face (M.rev (T.par y))))
        (ιe (T.par y)) (ιe b)
        (cutNode (runOpsE n Fo (pivotPre (ιf (M.face (T.par y)))
          (ιf (M.face (M.rev (T.par y)))) c)).1 ιf ιe M b)
        (ιf fe) (ιv y) (ιg (T.par y)) (ιg b) (ιv (M.tail b)) c
        (wt (T.par y) - φ (T.par y) - c - v₁) (wt (M.rev (T.par y)) + φ (T.par y) + c - v₂)
        (φ b - w₁) (φ (M.rev b) - w₂))).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ fe (Lo - |(c : ℝ)|)
        (runOpsE n Fo (pivotOps (ιf (M.face (T.par y))) (ιf (M.face (M.rev (T.par y))))
          (ιe (T.par y)) (ιe b)
          (cutNode (runOpsE n Fo (pivotPre (ιf (M.face (T.par y)))
            (ιf (M.face (M.rev (T.par y)))) c)).1 ιf ιe M b)
          (ιf fe) (ιv y) (ιg (T.par y)) (ιg b) (ιv (M.tail b)) c
          (wt (T.par y) - φ (T.par y) - c - v₁) (wt (M.rev (T.par y)) + φ (T.par y) + c - v₂)
          (φ b - w₁) (φ (M.rev b) - w₂))).1
        (T.reparent y b hy hby hna) (pivotVal T φ wt val y c) := by
  classical
  obtain ⟨C, β, β₂, hroot, hoff, hRc, hIc, hLo⟩ := hS.cot
  have hRt := hS.tree
  obtain ⟨z, hz, hzb, hza⟩ := exists_cut_face hM hoff hy hby hna hbT
  set a := T.par y with ha
  set os1 := cotreeOps ιf ιe C a z fe c (wt a - φ a - c - v₁)
      (wt (M.rev a) + φ a + c - v₂) with hos1
  obtain ⟨hval1, hout1, C', hroot', hoff', hI', hag1, β', β₂', hR', hLo'⟩ :=
    cotreePivot_trep hM hoff hL.dual hL.hf hRc hIc hy hby hna hbT hz hzb hza fe φ wt c hv₁ hv₂
      hos1
  set F1 := (runOpsE n Fo os1).1 with hF1
  have hRt1 := hRt.congr (fun x => hag1 _ (hL.vf x) (hL.ve x))
    (fun d => hag1 _ (hL.gf d) (hL.ge d))
  have hIt1 := hS.treeIso.congr (fun d => hag1 _ (hL.gf d) (hL.ge d))
  have hint1 := intF_runOpsE (n := n) os1 hS.int
  have hw₁' : F1.val (ιg b) = w₁ := by rw [(hag1 _ (hL.gf b) (hL.ge b)).2.1, hw₁]
  have hw₂' : F1.val2 (ιg b) = w₂ := by rw [(hag1 _ (hL.gf b) (hL.ge b)).2.2, hw₂]
  have hoffb : ∀ x, x ≠ T.root → b ≠ T.par x ∧ b ≠ M.dual.rev (T.par x) :=
    off_iff_not_inT.2 hbT
  obtain ⟨hval2, hout2, hR2, hI2, hag2⟩ := reparent_trep hRt1 hIt1 hL.prim hL.hv hy hby hna
    hoffb (t₁ := φ b) (t₂ := φ (M.rev b)) hw₁' hw₂'
  -- the cut face is named by the parent of the node of the edge of `b`
  have hcut : cutNode (runOpsE n Fo (pivotPre (ιf (M.face a)) (ιf (M.face (M.rev a))) c)).1
      ιf ιe M b = ιf z := by
    set C1 := C.reroot (M.face a) with hC1
    have h1 := evert_trep hRc hL.dual hL.hf (M.face a)
    have h2 := addBoth_trep h1 hL.dual hL.hf (M.face (M.rev a)) (-(c : ℝ))
    have hF2 : (runOpsE n Fo (pivotPre (ιf (M.face a)) (ιf (M.face (M.rev a))) c)).1 =
        addPath2 (addPath (evert Fo n (ιf (M.face a))) n (ιf (M.face (M.rev a))) (-(c : ℝ))) n
          (ιf (M.face (M.rev a))) (-(-(c : ℝ))) := by
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
  have hops : pivotOps (ιf (M.face a)) (ιf (M.face (M.rev a))) (ιe a) (ιe b)
      (cutNode (runOpsE n Fo (pivotPre (ιf (M.face a)) (ιf (M.face (M.rev a))) c)).1 ιf ιe M b)
      (ιf fe) (ιv y) (ιg a) (ιg b) (ιv (M.tail b)) c (wt a - φ a - c - v₁)
      (wt (M.rev a) + φ a + c - v₂) (φ b - w₁) (φ (M.rev b) - w₂) =
      os1 ++ reparentOps ιv ιg T y b (φ b - w₁) (φ (M.rev b) - w₂) := by
    rw [hcut, hos1]
    have e1 : (C.reroot (M.face a)).par z = b ∨ (C.reroot (M.face a)).par z = M.rev b := hzb
    have e2 : ιe ((C.reroot (M.face a)).par z) = ιe b := by
      rcases e1 with h | h
      · rw [h]
      · rw [h, hL.dual.e_rev]
    simp only [pivotOps, cotreeOps, exchangeOps, reparentOps, e2, hL.dual.e_rev, reroot_root,
      List.cons_append, List.nil_append]
    rfl
  rw [hops]
  refine ⟨(validOpsE_append n _ _ _).2 ⟨hval1, hval2⟩, ?_, ?_⟩
  · rw [runOpsE_append, hout1, hout2]; rfl
  · rw [runOpsE_append]
    refine ⟨hR2.congrκ fun d => ?_, hI2, ⟨C', β', β₂', hroot', hoff',
      hR'.congr (fun x => hag2 _ (fun v => (hL.vf v x).symm) (fun d => (hL.gf d x).symm))
        (fun d => hag2 _ (fun v => (hL.ve v d).symm) (fun d' => (hL.ge d' d).symm)),
      hI'.congr (fun d => hag2 _ (fun v => (hL.ve v d).symm) (fun d' => (hL.ge d' d).symm)),
      hLo' Lo hLo⟩, intF_runOpsE _ hint1⟩
    by_cases h1 : d = b
    · rw [ite_eq_left h1, h1]
    · rw [ite_eq_right h1]
      by_cases h2 : d = M.dual.rev b
      · rw [ite_eq_left h2, h2]
        show ((φ b : ℤ) : ℝ) = ((φ (M.rev (M.rev b)) : ℤ) : ℝ)
        rw [M.rev_rev]
      · rw [ite_eq_right h2]

end Klein

end PlanarFlow
