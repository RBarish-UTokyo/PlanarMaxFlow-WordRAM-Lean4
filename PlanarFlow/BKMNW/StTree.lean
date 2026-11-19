module

public import PlanarFlow.BKMNW.StExp

/-!
# A valid initial tree of the s-t flow from any shortest-path tree

The s-t flow with explicit choices (`STFlow.pstflowT`, `STFlow.StChoice`) needs an initial dual
tree `T` whose state meets the invariant `LInv` of the perturbed run. `STFlow.exists_linit` builds
one from a shortest-path tree for the lengths `N c + ε` (`N = (F + 1) Σ ε + 1`) and then chooses
it classically. Here the converse direction, for the machine: **every** dual tree whose parent
darts are tight for a feasible potential of `N c + ε` (what Dijkstra's algorithm with a tight-dart
pass computes), for any `N ≥ (F + 1) Σ ε + 1`, is valid:

* **`linv_of_tight`**: `LInv c ε s t (tSt M c ε T)` for every `s`, `t`;
* `reach_of_dec`, **`treeOf`** (the dual tree of a parent array whose parents decrease a
  potential), **`linv_treeOf`** (the tree of tight parents of a feasible potential of the positive
  lengths `N c + ε` is a valid initial tree);
* **`Klein.msspPlaneK_eq_of_isDist`**: by contrast the MSSP subroutine needs no choice: at the
  faces of the path, `msspPlaneK` (through a classically chosen cut) equals any distance function,
  so a machine's Klein run on any cut reproduces it exactly.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **A tight tree of a feasible potential of `N c + ε` is a valid initial tree** of the perturbed
run (for any `N ≥ (F + 1) Σ ε + 1`). -/
theorem linv_of_tight {c ε : D → ℤ} (hc : ∀ d, 0 ≤ c d) (hε : ∀ d, 0 ≤ ε d) {N : ℤ}
    (hN : (Fintype.card F + 1) * ∑ d, ε d + 1 ≤ N) (T : DTree M) {φ : F → ℤ}
    (hpot : ∀ d, M.cob φ d ≤ N * c d + ε d)
    (htight : ∀ x, x ≠ T.root → M.cob φ (T.par x) = N * c (T.par x) + ε (T.par x))
    (s t : V) : LInv c ε s t (tSt M c ε T) := by
  set E := ∑ d, ε d with hE
  have hE0 : 0 ≤ E := sum_nonneg fun d _ => hε d
  have hF0 : (0 : ℤ) ≤ Fintype.card F := by positivity
  have hN0 : 0 < N := by nlinarith
  -- the distances are the path sums
  have hφ : ∀ x, φ x - φ T.root = T.psum (fun d => N * c d + ε d) x := fun x =>
    T.psum_unique _ (k := fun x => φ x - φ T.root) (by simp) (fun y hy => by
      have h1 := htight y hy
      simp only [cob, T.head_par y hy] at h1
      rw [T.up_of_ne hy]
      linarith) x
  have hsplit : ∀ x, T.psum (fun d => N * c d + ε d) x = N * T.psum c x + T.psum ε x := by
    intro x
    have : (fun d => N * c d + ε d) = (fun d => N * c d) + ε := rfl
    rw [this, DTree.psum_add, DTree.psum_smul]
  -- the perturbation part of the slack is small
  have hsmall : ∀ d, |ε d - M.cob (T.psum ε) d| < N := by
    intro d
    have h1 := T.psum_nonneg hε (M.face d)
    have h2 := T.psum_nonneg hε (M.face (M.rev d))
    have h3 := T.psum_le hε (M.face d)
    have h4 := T.psum_le hε (M.face (M.rev d))
    have h5 : ε d ≤ E := single_le_sum (fun d _ => hε d) (mem_univ d)
    have h6 := hε d
    have h7 : (Fintype.card F : ℤ) * E ≥ 0 := by positivity
    simp only [cob]
    rw [abs_lt]
    constructor <;> nlinarith
  -- the slack for `N c + ε` is nonnegative
  have hfeas : ∀ d, 0 ≤ N * (c d - M.cob (T.psum c) d) + (ε d - M.cob (T.psum ε) d) := by
    intro d
    have h1 := hpot d
    have h2 := hφ (M.face d)
    have h3 := hφ (M.face (M.rev d))
    rw [hsplit] at h2 h3
    simp only [cob] at h1 ⊢
    nlinarith
  have hle : ∀ d, M.cob (T.psum c) d ≤ c d := by
    intro d
    by_contra h
    have h1 := hfeas d
    have h2 := (abs_lt.1 (hsmall d)).2
    have : N * (c d - M.cob (T.psum c) d) ≤ -N := by
      have : c d - M.cob (T.psum c) d ≤ -1 := by omega
      nlinarith
    linarith
  have hsatc : ∀ x, x ≠ T.root → M.cob (T.psum c) (T.par x) = c (T.par x) := fun x hx => by
    have h := T.psum_of_ne c (x := x) hx
    simp only [cob, T.head_par x hx]
    rw [T.up_of_ne hx] at h
    linarith
  have hsate : ∀ x, x ≠ T.root → M.cob (T.psum ε) (T.par x) = ε (T.par x) := fun x hx => by
    have h := T.psum_of_ne ε (x := x) hx
    simp only [cob, T.head_par x hx]
    rw [T.up_of_ne hx] at h
    linarith
  refine ⟨⟨⟨M.cob_antisymm _, hle⟩, fun v _ _ => M.div_cob _ v, hsatc⟩, M.cob_antisymm _,
    fun v _ _ => M.div_cob _ v, fun d hd => ?_, hsate⟩
  have h1 := hfeas d
  simp only [tSt] at hd
  rw [hd, sub_self, mul_zero, zero_add] at h1
  simp only [tSt]
  linarith

/-- Iterating the parent map from `x` reaches the root when the parents decrease a potential. -/
theorem reach_of_dec (o : F) (par : F → D) (φ : F → ℤ)
    (hdec : ∀ x, x ≠ o → φ (M.face (par x)) < φ x) (x : F) :
    ∃ n, (upF M o par)^[n] x = o := by
  classical
  induction hn : (univ.filter fun z => φ z < φ x).card using Nat.strong_induction_on
    generalizing x with
  | _ n ih =>
    by_cases hx : x = o
    · exact ⟨0, hx⟩
    · set y := M.face (par x) with hy
      have hyx : φ y < φ x := hdec x hx
      have hlt : (univ.filter fun z => φ z < φ y).card < n := by
        rw [← hn]
        refine Finset.card_lt_card ⟨fun z hz => ?_, fun h => ?_⟩
        · simp only [mem_filter, mem_univ, true_and] at hz ⊢; omega
        · have := h (show y ∈ univ.filter fun z => φ z < φ x by
            simp only [mem_filter, mem_univ, true_and]; exact hyx)
          simp at this
      obtain ⟨k, hk⟩ := ih _ hlt y rfl
      refine ⟨k + 1, ?_⟩
      rw [Function.iterate_succ_apply]
      have : upF M o par x = y := by simp [upF, hx, hy]
      rw [this, hk]

variable (M) in
/-- **The dual tree of a parent array** whose parents decrease a potential. -/
noncomputable def treeOf (o : F) (par : F → D) (hhp : ∀ x, x ≠ o → M.face (M.rev (par x)) = x)
    (φ : F → ℤ) (hdec : ∀ x, x ≠ o → φ (M.face (par x)) < φ x) : DTree M where
  root := o
  par := par
  head_par := hhp
  reach := reach_of_dec o par φ hdec

/-- **The tree of tight parents of a feasible potential of `N c + ε` (positive lengths) is a valid
initial tree** of the perturbed run: what Dijkstra's algorithm on the dual with the lengths
`N c + ε` and a tight-dart pass give. -/
theorem linv_treeOf {c ε : D → ℤ} (hc : ∀ d, 0 ≤ c d) (hε : ∀ d, 0 ≤ ε d) {N : ℤ}
    (hN : (Fintype.card F + 1) * ∑ d, ε d + 1 ≤ N) (hw : ∀ d, 0 < N * c d + ε d) (o : F)
    (par : F → D) (hhp : ∀ x, x ≠ o → M.face (M.rev (par x)) = x) {φ : F → ℤ}
    (hpot : ∀ d, M.cob φ d ≤ N * c d + ε d)
    (htight : ∀ x, x ≠ o → M.cob φ (par x) = N * c (par x) + ε (par x)) (s t : V) :
    ∃ hdec : ∀ x, x ≠ o → φ (M.face (par x)) < φ x,
      LInv c ε s t (tSt M c ε (treeOf M o par hhp φ hdec)) := by
  have hdec : ∀ x, x ≠ o → φ (M.face (par x)) < φ x := fun x hx => by
    have h1 := htight x hx
    have h2 := hw (par x)
    simp only [cob, hhp x hx] at h1
    linarith
  exact ⟨hdec, linv_of_tight hc hε hN (treeOf M o par hhp φ hdec) hpot htight s t⟩

end STFlow

namespace Klein

open BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **The MSSP subroutine has no choice to reproduce**: at every face along the path, the answers
of `msspPlaneK` (defined through a classically chosen cut) are **the** distances of the dual graph
minus the path, so a machine run on any cut (with any isolating lengths) that outputs distances
outputs exactly `msspPlaneK`. -/
theorem msspPlaneK_eq_of_isDist (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (P : SPath M) (ℓ : D → ℤ) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) {x : F} (hx : x ∈ P.faces)
    {δ : F → Option ℤ} (hδ : IsDist ((M.dualGraph ℓ).restrict fun e => e ∉ P.darts) x δ) :
    msspPlaneK M P.darts ℓ x = δ :=
  (msspPlaneK_spec hM hrot hface P ℓ hnn x hx).unique hδ

end Klein

end PlanarFlow
