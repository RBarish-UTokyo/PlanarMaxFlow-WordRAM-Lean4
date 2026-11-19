module

public import PlanarFlow.Klein.LCTRep
public import PlanarFlow.Klein.Trip
public import PlanarFlow.DynTree.RunE

/-!
# The two queries of Klein's algorithm on the dynamic trees

The data of a move (`PlanarFlow.Klein.DataRun`) are read from the forest of the dynamic trees
in which the spanning tree `T` and the dual cotree `C` are stored (`PlanarFlow.Klein.TRep`):

* `lct_minpath`: **`MINPATH` is the query `min2`** on the node of the face `x`, when the cotree
  `C` is rooted at the face `C.root` and stored with the values `val` of the darts: if the least
  second value on the root path is below the threshold `z` (and the values at the nodes of the
  faces are at least `z`), it is the value of a dart `d` of value `1` on the path of the cotree from
  the root to `x` (`T.chi C.root x`), the node printed is the node of the edge of `d`, whose parent
  is the node of the face of `d` (which orients it), and `val d` is least among those darts;
  otherwise all those darts have value at least `z`. These are the fields `sel`, `low` and `stop`
  of `DataRun` (with `C.root` the face of the boundary dart `e` and `x` the face of its reverse,
  the threshold `L - 2B`).
* `eop_min2_answer`: the same read from the words printed by the operation `EOp.min2` on the
  machine (`PlanarFlow.DynTree.lctE_runsWithin`).
* `lct_label`: **the labels are the path sums** of the nodes of the vertices in the forest storing
  `T` (values `φ` of the parent darts, `0` at the nodes of the vertices), so at the start of a move
  of a trip they are the distances from its source (`IsTrip.labels`): the query `sum`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-- **`MINPATH` on the forest of the dynamic trees.** -/
theorem lct_minpath (hM : M.IsPlane) {T : DTree M.dual} {C : DTree M}
    (hoff : ∀ y, y ≠ C.root → ¬ T.InT (C.par y)) {n : ℕ} {Fo : Forest} {ιf : F → ℕ}
    {ιe : D → ℕ} {val : D → ℤ} {β β₂ : F → ℝ}
    (hR : TRep n Fo C ιf ιe (fun d => (val d : ℝ)) β β₂) (hf : ∀ y, ιf y < n)
    (he : ∀ d, ιe d < n) (hn : 2 * Fintype.card F ≤ n) {z : ℤ} (hβ : ∀ y, (z : ℝ) ≤ β₂ y)
    (x : F) :
    ((pathMin2 Fo n (ιf x)).1 < z → ∃ d, (pathMin2 Fo n (ιf x)).2 = ιe d ∧
        Fo.par (ιe d) = ιf (M.face d) ∧ T.chi C.root x d = 1 ∧ val d < z ∧
        ∀ d', T.chi C.root x d' = 1 → val d ≤ val d') ∧
      (¬ (pathMin2 Fo n (ιf x)).1 < z → ∀ d', T.chi C.root x d' = 1 → z ≤ val d') := by
  constructor
  · intro h
    obtain ⟨i, hi, hir, h2, h1, hall⟩ :=
      pathMin2_rep hR hf he hn x fun y => lt_of_lt_of_le h (hβ y)
    refine ⟨C.par (C.up^[i] x), h2, hR.pe _ hir, (chi_eq_one_iff hM T C hoff x _).2 ⟨i, hi, rfl⟩,
      ?_, fun d' hd' => ?_⟩
    · rw [h1] at h; exact_mod_cast h
    · obtain ⟨j, hj, rfl⟩ := (chi_eq_one_iff hM T C hoff x d').1 hd'
      have := hall j hj
      rw [h1] at this
      exact_mod_cast this
  · intro h d' hd'
    obtain ⟨j, hj, rfl⟩ := (chi_eq_one_iff hM T C hoff x d').1 hd'
    have := pathMin2_le hR hf he hn x j hj
    push Not at h
    exact_mod_cast h.trans this

/-- **`MINPATH` read from the words printed by the operation `min2` on the machine**: the first
word is the node of the edge of a selected dart (oriented by the parent of that node) when the
second word is `1`; when it is `0`, every dart of the path has value at least the threshold. -/
theorem eop_min2_answer (hM : M.IsPlane) {T : DTree M.dual} {C : DTree M}
    (hoff : ∀ y, y ≠ C.root → ¬ T.InT (C.par y)) {n : ℕ} {Fo : Forest} {ιf : F → ℕ}
    {ιe : D → ℕ} {val : D → ℤ} {β β₂ : F → ℝ}
    (hR : TRep n Fo C ιf ιe (fun d => (val d : ℝ)) β β₂) (hf : ∀ y, ιf y < n)
    (he : ∀ d, ιe d < n) (hn : 2 * Fintype.card F ≤ n) {z : ℤ} (hβ : ∀ y, (z : ℝ) ≤ β₂ y)
    (x : F) :
    (∃ d, (EOp.min2 (ιf x) z).answer n Fo = [ιe d, 1] ∧ Fo.par (ιe d) = ιf (M.face d) ∧
        T.chi C.root x d = 1 ∧ val d < z ∧ ∀ d', T.chi C.root x d' = 1 → val d ≤ val d') ∨
      (∃ w, (EOp.min2 (ιf x) z).answer n Fo = [w, 0] ∧
        ∀ d', T.chi C.root x d' = 1 → z ≤ val d') := by
  obtain ⟨h1, h2⟩ := lct_minpath hM hoff hR hf he hn hβ x
  by_cases h : (pathMin2 Fo n (ιf x)).1 < z
  · obtain ⟨d, hd, rest⟩ := h1 h
    left
    exact ⟨d, by simp [EOp.answer, h, hd], rest⟩
  · right
    exact ⟨(pathMin2 Fo n (ιf x)).2, by simp [EOp.answer, h], h2 h⟩

/-- **The labels are the path sums** at the nodes of the vertices in the forest storing the
spanning tree `T` (the values `φ` of the parent darts on the nodes of the edges, `0` on the
nodes of the vertices). -/
theorem lct_label {T : DTree M.dual} {n : ℕ} {Fo : Forest} {ιv : V → ℕ} {ιg : D → ℕ}
    {φ : D → ℤ} {β₂ : V → ℝ} (hR : TRep n Fo T ιv ιg (fun d => (φ (M.rev d) : ℝ)) 0 β₂)
    (hf : ∀ x, ιv x < n) (he : ∀ d, ιg d < n) (hn : 2 * Fintype.card V ≤ n) (x : V) :
    pathSum Fo n (ιv x) = T.psum φ x :=
  pathSum_rep hR hf he hn (fun _ => rfl) (fun d => by
    change ((φ (M.rev (M.rev d)) : ℤ) : ℝ) = _; rw [M.rev_rev]) x

/-- **At the start of every move of a trip, the path sums at the nodes of the vertices are the
distances from the source** (for a forest storing the tree at the start of the move with the
weights `tripφ`). -/
theorem lct_label_trip {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
    (H : Hyp M k g S ℓ) (hR' : SameReach M k g S ℓ) {R : ℕ → MoveData M S}
    (hT : IsTrip M k g S ℓ R) (j : ℕ) {n : ℕ} {Fo : Forest} {ιv : V → ℕ} {ιg : D → ℕ}
    {β₂ : V → ℝ}
    (hR : TRep n Fo ((R j).T 0) ιv ιg (fun d => (tripφ S ℓ (M.rev d) : ℝ)) 0 β₂)
    (hf : ∀ x, ιv x < n) (he : ∀ d, ιg d < n) (hn : 2 * Fintype.card V ≤ n) {x : V}
    (hx : Reach (pieceGraph M S ℓ) (tripSrc M k g j) x) :
    pathSum Fo n (ιv x) = dist (pieceGraph M S ℓ) (tripSrc M k g j) x := by
  rw [lct_label hR hf he hn x, hT.labels H hR' j hx]

end Klein

end PlanarFlow
