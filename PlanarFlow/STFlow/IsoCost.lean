module

public import PlanarFlow.STFlow.LexCost
public import PlanarFlow.STFlow.IsoCover
public import PlanarFlow.STFlow.IsoRun

/-!
# The pivot bound and the cost with the word-size perturbation

The pivot bound of `PlanarFlow/STFlow/LexCount.lean` holds for every perturbation whose parent
darts are tight arcs of the cut of the cyclic cover (`TightLev`, `lenterOnce_of`,
`lsteps_le_of`). For the word-size perturbation `isoEps` this is `tight_parW`
(`PlanarFlow/STFlow/IsoCover.lean`), so:

* `tightLev_iso`: the parent darts of the run with `isoEps M t` are tight in the cut of the
  cover with the lengths `covLenW`;
* `lstepsW_le`: **every run with the word-size perturbation takes at most `m + 1` steps**;
* `pstflowWSteps_le`, `pstflowWCost_le`: **`pstflowW` takes at most `m + 1` steps and costs at
  most `36 K m lg m`** (the costs of its subroutines as in `STCosts.Bounds`), on every plane map
  with transitive rotations and faces; `pstflowW_plane`: with `pstflowW_spec`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW MSSP Klein Function

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

lemma covLenW_nonneg (hM : M.IsPlane) [Nonempty D] {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (K : ℕ)
    (t : V) (x : D × ZMod K) : 0 ≤ covLenW M K c t x := by
  rw [covLenW_eq]
  have h1 := (isoEps_bounds hM t x.1).1
  have h2 : 0 ≤ covNW V F (isoEps M t) K := by
    have : 0 ≤ ∑ d, isoEps M t d := sum_nonneg fun d _ => isoEps_nonneg hM t d
    unfold covNW isoL; positivity
  have := mul_nonneg h2 (hc x.1)
  linarith

/-- **The parent darts of the run with the word-size perturbation are tight** in the cut of the
cover with the lengths `covLenW` (`tight_parW` at the sheet of the level). -/
lemma tightLev_iso (hrot : M.RotTrans) (π : SPath M) (hk : 0 < π.k) (hM : M.IsPlane)
    (hface : M.FaceTrans) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) :
    TightLev c (isoEps M (π.p π.k)) hrot π hk (covLenW M (nSheets F) c (π.p π.k)) := by
  intro st hI d₀ hd₀ hroot b hb
  have := tight_parW hrot π hk (nSheets F) hM hface (by unfold nSheets; omega)
    (by unfold nSheets lexBase; omega) hc hI hd₀ hroot hb _ (range_sheetOf π st.T)
  rwa [liftEnd_eq_par π st.T hb] at this

/-- **Every run with the word-size perturbation takes at most `m + 1` steps**, on a plane map
with transitive rotations and faces, from a state satisfying `LInv` rooted at the face of a dart
leaving `t`. -/
theorem lstepsW_le (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {c : D → ℤ}
    (hc : ∀ d, 0 ≤ c d) {s t : V} (hst : s ≠ t) {d₀ : D} (hd₀ : M.tail d₀ = t) {st : LSt M}
    (hI : LInv c (isoEps M t) s t st) (hroot : st.T.root = M.face d₀) (n : ℕ) :
    (lrun M c (isoEps M t) s t n st).2.1 ≤ Fintype.card D + 1 := by
  have : Nonempty D := ⟨d₀⟩
  refine lsteps_le_of hM hrot hface hc hst (fun π hk _ ht => ?_) hd₀ hI hroot n
  subst ht
  exact ⟨_, covLenW_nonneg hM hc _ _, tightLev_iso hrot π hk hM hface hc⟩

/-! ### The implementation -/

variable (M) in
open Classical in
/-- **The number of steps** (augmentations) performed by `pstflowW M c X Y`. -/
noncomputable def pstflowWSteps (c : D → ℤ) (X Y : Finset V) : ℕ :=
  if h : X.Nonempty ∧ ∃ d, M.tail d ∈ Y then
    ((pcoreRunW M (capR M c X Y) h.1.choose (M.tail h.2.choose) (M.face h.2.choose)).map
      fun r => r.2.1).getD 0
  else 0

variable (M) in
/-- **The cost** of `pstflowW M c X Y`, as for `pstflow` (`costOf`). -/
noncomputable def pstflowWCost (cc : STCosts) (c : D → ℤ) (X Y : Finset V) : ℕ :=
  costOf D V F cc (pstflowWSteps M c X Y)

/-- **The implementation with the word-size perturbation takes at most `m + 1` steps** on every
plane map with transitive rotations and faces, for nonnegative capacities. -/
theorem pstflowWSteps_le (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (X Y : Finset V) :
    pstflowWSteps M c X Y ≤ Fintype.card D + 1 := by
  classical
  unfold pstflowWSteps pcoreRunW
  split_ifs with h
  · set t := M.tail h.2.choose
    cases hi : linit M (capR M c X Y) (isoEps M t) h.1.choose t (M.face h.2.choose) with
    | none => simp
    | some st =>
      simp only [Option.map_some, Option.getD_some]
      obtain ⟨hroot, hI⟩ := linit_inv _ _ hi
      by_cases hst : h.1.choose = t
      · have hz : ∀ d, st.T.chi h.1.choose t d = 0 := by
          obtain ⟨ha, hdiv, hoff, -⟩ := st.T.chi_spec hM h.1.choose t
          refine st.T.circ_eq_zero hM ⟨ha, fun v => ?_⟩ hoff
          rw [hdiv]; simp [hst]
        have hne : ¬ (pathSet h.1.choose t st.T).Nonempty := by
          rintro ⟨d, hd⟩; simp [pathSet, hz d] at hd
        have h1 : (lstep M (capR M c X Y) (isoEps M t) h.1.choose t st).2 = true := by
          simp [lstep, hne]
        cases fuel F with
        | zero => simp [lrun]
        | succ n => simp [lrun, h1]
      · exact lstepsW_le hM hrot hface (capR_nonneg hc X Y) hst rfl hI hroot _
  · exact Nat.zero_le _

/-- **The cost of the implementation with the word-size perturbation is `O(n log n)`**: at most
`36 K m lg m` on every plane map with transitive rotations and faces with `m ≥ 1` darts, for
nonnegative capacities. -/
theorem pstflowWCost_le {cc : STCosts} {K : ℕ} (hcc : cc.Bounds K) (hM : M.IsPlane)
    (hrot : M.RotTrans) (hface : M.FaceTrans) (hD : 1 ≤ Fintype.card D) {c : D → ℤ}
    (hc : ∀ d, 0 ≤ c d) (X Y : Finset V) :
    pstflowWCost M cc c X Y ≤ 36 * K * Fintype.card D * lg (Fintype.card D) :=
  costOf_le_of_le hcc hM hD (pstflowWSteps_le hM hrot hface hc X Y)

/-- **The single-source single-sink algorithm with the word-size perturbation on a plane map
with transitive rotations and faces**: it meets `STFlowSpec`, and its cost is at most
`36 K m lg m`. -/
theorem pstflowW_plane (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {cc : STCosts} {K : ℕ} (hcc : cc.Bounds K) (hD : 1 ≤ Fintype.card D) :
    STFlowSpec M (pstflowW M) ∧ ∀ c : D → ℤ, (∀ d, 0 ≤ c d) → ∀ X Y : Finset V,
      pstflowWCost M cc c X Y ≤ 36 * K * Fintype.card D * lg (Fintype.card D) :=
  ⟨pstflowW_spec hM, fun _ hc X Y => pstflowWCost_le hcc hM hrot hface hD hc X Y⟩

end STFlow

end PlanarFlow
