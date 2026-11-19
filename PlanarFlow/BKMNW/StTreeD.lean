module

public import PlanarFlow.BKMNW.StDk

/-!
# The initial dual tree of the s-t flow from Dijkstra's distances

The machine computes the distances `Dv` of the dual graph (the graph of `M.dual`, arcs
`face d → face (rev d)`, lengths `N c + ε`) from the root face, then for every other face the last
tight dart into it (`NegSSSP.tpProg`, `tpW`). Here:

* `reach_dual`: on a plane map every face is reached from every face in the dual graph;
* **`linv_of_dist`**: a parent array of tight darts for these distances gives a dual tree
  (`treeOf`) meeting `LInv` (the validity of the s-t flow's choice of tree, `StChoice.OK`);
* `tpW_tight`: the word `tpW … n y` is a tight dart into `y` when one exists (no uniqueness);
* **`tight_into`**: for positive lengths every face but the root has a tight dart into it.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- The dual graph with the lengths `ℓ`, as the graph of all the darts of `M.dual`. -/
abbrev dG (M : CombMap D V F) (ℓ : D → ℤ) := MSSP.pieceGraph M.dual univ ℓ

lemma dG_src (ℓ : D → ℤ) (a : {d // d ∈ (univ : Finset D)}) : (dG M ℓ).src a = M.face a.1 := rfl
lemma dG_dst (ℓ : D → ℤ) (a : {d // d ∈ (univ : Finset D)}) :
    (dG M ℓ).dst a = M.face (M.rev a.1) := rfl
lemma dG_len (ℓ : D → ℤ) (a : {d // d ∈ (univ : Finset D)}) : (dG M ℓ).len a = ℓ a.1 := rfl

/-- **Every face is reached in the dual graph** of a plane map. -/
theorem reach_dual (hM : M.IsPlane) (ℓ : D → ℤ) (o x : F) : MSSP.Reach (dG M ℓ) o x := by
  induction hM.dualConn o x with
  | refl => exact MSSP.Reach.refl _
  | @tail b x' _ h ih =>
    obtain ⟨d, h1, h2⟩ : ∃ d, M.face d = b ∧ M.face (M.rev d) = x' := h
    subst h1 h2
    exact ih.arc (a := (⟨d, mem_univ d⟩ : {d // d ∈ (univ : Finset D)}))

/-- **A tree of tight parents of Dijkstra's distances is a valid initial tree** of the perturbed
run: positive lengths `N c + ε` (`c ≥ 0`, `ε ≥ 1`, `N ≥ (F + 1) Σ ε + 1`), every face reached, and
for every face `x ≠ o` a dart `par x` into `x` (`face (rev (par x)) = x`) tight for the distances
from `o`. -/
theorem linv_of_dist (hM : M.IsPlane) {c ε : D → ℤ} (hc : ∀ d, 0 ≤ c d) (hε : ∀ d, 1 ≤ ε d)
    {N : ℤ} (hN : (Fintype.card F + 1) * ∑ d, ε d + 1 ≤ N) (o : F) (par : F → D)
    (hhp : ∀ x, x ≠ o → M.face (M.rev (par x)) = x)
    (htp : ∀ x, x ≠ o → MSSP.dist (dG M fun d => N * c d + ε d) o (M.face (par x)) +
      (N * c (par x) + ε (par x)) = MSSP.dist (dG M fun d => N * c d + ε d) o x)
    (s t : V) :
    ∃ hdec : ∀ x, x ≠ o → MSSP.dist (dG M fun d => N * c d + ε d) o (M.face (par x)) <
        MSSP.dist (dG M fun d => N * c d + ε d) o x,
      LInv c ε s t (tSt M c ε (treeOf M o par hhp
        (fun x => MSSP.dist (dG M fun d => N * c d + ε d) o x) hdec)) := by
  have hE0 : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => by have := hε d; omega
  have hN1 : 1 ≤ N := by nlinarith
  have hw : ∀ d, 0 < N * c d + ε d := fun d => by
    have := mul_nonneg (show (0 : ℤ) ≤ N by omega) (hc d); have := hε d; omega
  have hnn : ∀ a, 0 ≤ (dG M fun d => N * c d + ε d).len a := fun a => (hw a.1).le
  refine linv_treeOf hc (fun d => by have := hε d; omega) hN hw o par hhp (fun d => ?_)
    (fun x hx => ?_) s t
  · have h := MSSP.dist_arc hnn (G := dG M fun d => N * c d + ε d) (a := ⟨d, mem_univ d⟩)
      (reach_dual hM _ o (M.face d))
    simp only [dG_src, dG_dst, dG_len] at h
    simp only [cob]; linarith
  · have h := htp x hx
    simp only [cob, hhp x hx]; linarith

/-- **For positive lengths every face but the root has a tight dart into it.** -/
theorem tight_into (hM : M.IsPlane) {ℓ : D → ℤ} (hpos : ∀ d, 0 < ℓ d) (o x : F) (hx : x ≠ o) :
    ∃ d, M.face (M.rev d) = x ∧
      MSSP.dist (dG M ℓ) o (M.face d) + ℓ d = MSSP.dist (dG M ℓ) o x := by
  have hnn : ∀ a, 0 ≤ (dG M ℓ).len a := fun a => (hpos a.1).le
  obtain ⟨a, ht, hd⟩ := MSSP.exists_tight hnn (reach_dual hM ℓ o x) hx
  refine ⟨a.1, hd, ?_⟩
  obtain ⟨hr, he⟩ := ht
  rw [← hd]
  simpa [dG_src, dG_len] using he

end STFlow

namespace NegSSSP

/-- **The word of the tight-parent pass is a tight dart into `y`** whenever there is one. -/
theorem tpW_tight {fl NT NH Lv rb Dv old : ℕ → ℕ} {y : ℕ} :
    ∀ n, (∃ j < n, TightI fl NT NH Lv rb Dv j ∧ NH j = y) →
      tpW fl NT NH Lv rb Dv old n y < n ∧
        TightI fl NT NH Lv rb Dv (tpW fl NT NH Lv rb Dv old n y) ∧
        NH (tpW fl NT NH Lv rb Dv old n y) = y
  | 0, ⟨j, hj, _⟩ => absurd hj (by omega)
  | n + 1, ⟨j, hj, ht, he⟩ => by
    simp only [tpW]
    split_ifs with h
    · exact ⟨by omega, h.1, h.2⟩
    · have hjn : j < n := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h' | rfl
        · exact h'
        · exact absurd ⟨ht, he⟩ h
      obtain ⟨a, b, e⟩ := tpW_tight n ⟨j, hjn, ht, he⟩
      exact ⟨by omega, b, e⟩

end NegSSSP

end PlanarFlow
