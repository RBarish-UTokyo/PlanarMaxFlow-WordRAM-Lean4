module

public import PlanarFlow.STFlow.Spec
public import PlanarFlow.BKMNW.Cost

/-!
# The cost of the single-source single-sink algorithm

The algorithm (`PlanarFlow.STFlow.stflow`) is charged its true work: one shortest-path computation
in the dual with nonnegative lengths (Dijkstra's algorithm, for the initial tree), linear
bookkeeping, and, for **each step of the run actually performed** (`stflowSteps`, the number of
augmentations), a constant number of dynamic-tree operations.

## The dynamic trees (the stated interface)

Two dynamic forests are maintained, as in Erickson (SODA 2010, Section 3.2):

* **the dual tree `T*`**, rooted at the face `o`, on the faces, in the rooted forest of
  `PlanarFlow/DynTree/Forest.lean` (the link-cut tree of Sleator and Tarjan): a pivot is
  `cut b` (`b` loses its parent), `root a` (the pivot is legal exactly when `findRoot a ≠ b`, that
  is, when `b` is not on the path from `a = face e` to the root, `DTree.Anc`), and `link b a`
  (`b` is a root, `a` is not in its tree: the precondition `Op.Valid` of `link`). Three
  operations of `PlanarFlow.DynTree.Op` per step (`opsT = 3`), and one `link` per face to build
  it.
* **the cotree `C`**, on the vertices, with a value on each dart (its residual capacity
  `c - g`): `pathMin s t` (the bottleneck `bott`), `addPath s t (-δ)` (the augmentation `aug`,
  which adds `δ` to the reverse darts), `cut e` and `link` of the dart leaving `T*`. Four
  operations per step (`opsC = 4`), and one `link` per vertex to build it. This is Erickson's
  *dual forest structure*; it is unrooted, so on link-cut trees it needs, besides the operations
  of `PlanarFlow/DynTree/Forest.lean` on the root paths (`pathMin`, `addPath`, `link`, `cut`), the
  operation `evert` and values on darts (Goldberg, Grigoriadis and Tarjan); with `C` rooted at
  `t`, `pathMin s t` and `addPath s t` are the root-path operations `pathMin s` and `addPath s`.

Their amortised cost on `n` nodes is the parameter `dt n`, assumed `O(log n)` (`STCosts.Bounds`),
as are Dijkstra's algorithm (`O(m log m)`) and the bookkeeping (`O(m)`).

## Results

* `stflowSteps_le`: **unconditionally**, at most `2 F² + 1` steps (the levels, `run_done`).
* `stflowCost_le`: on a plane map with `m ≥ 1` darts, the cost is at most `6 K m lg m` plus
  `15 K lg m` per step.
* `stflowCost_le_sq`: unconditionally, `O((m + F²) log m)`.
* `stflowCost_le_of_pivotBound`: **if the run takes at most `m + 1` steps** (each dart pivots
  into `T*` at most once: Borradaile and Klein; Erickson, SODA 2010; the hypothesis `PivotBound`),
  the cost is at most `36 K m lg m`: `O(n log n)`, within the bound `K m lg² m` of
  `SubCosts.Bounds.stflow` assumed by the maximum-flow algorithm.

`PivotBound` is **not proved** in this development. `PlanarFlow/STFlow/PivotCount.lean` derives it
on every plane map from `EnterOnce` (each dart enters `T*` at most once along a run of pivots;
`pivotBound_of_enterOnce`), which follows from `NoReentry` (a dart that pivots into `T*` is never
again crossed forward by the path of the cotree; `pivotBound_of_noReentry`), itself proved only for
plane maps with at most two faces; it also shows that the stronger monotonicity first proposed for
this step (no dart crossed by the paths of the cotree backward and later forward) is false, and
that `NoReentry` does not extend to the darts of the initial tree.
`NoReentry` reduces to statements on sequences of free pivots,
without capacities (`pivotBound_of_freeNoReentry`, `pivotBound_of_noOvertake`).
**For the perturbed algorithm the bound is proved**: `PlanarFlow/STFlow/Lex.lean` runs the same
algorithm with the capacities perturbed lexicographically (the tie-breaking rule of Cabello,
Chambers and Erickson, Section 6), and `PlanarFlow/STFlow/LexCost.lean` proves that this
implementation (`pstflow`) takes at most `m + 1` steps and costs at most `36 K m lg m` on every
plane map with transitive rotations and faces (`pstflowCost_le`, through `costOf_le_of_le`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
open Classical in
/-- **The number of steps** (augmentations) performed by `stflow M c X Y`. -/
noncomputable def stflowSteps (c : D → ℤ) (X Y : Finset V) : ℕ :=
  if h : X.Nonempty ∧ ∃ d, M.tail d ∈ Y then
    ((coreRun M (capR M c X Y) h.1.choose (M.tail h.2.choose) (M.face h.2.choose)).map
      fun r => r.2.1).getD 0
  else 0

/-- **Unconditionally, at most `2 F² + 1` steps.** -/
theorem stflowSteps_le (c : D → ℤ) (X Y : Finset V) : stflowSteps M c X Y ≤ fuel F := by
  unfold stflowSteps
  split_ifs with h
  · unfold coreRun
    cases init M (capR M c X Y) h.1.choose (M.tail h.2.choose) (M.face h.2.choose) with
    | none => simp
    | some st => simpa using run_steps_le (M := M) _ st
  · exact Nat.zero_le _

/-- The dynamic-tree operations of one step: three on `T*` (`cut`, `root`, `link`). -/
def opsT : ℕ := 3

/-- The dynamic-tree operations of one step: four on the cotree (`pathMin`, `addPath`, `cut`,
`link`). -/
def opsC : ℕ := 4

/-- The costs of the subroutines of the single-source single-sink algorithm. -/
structure STCosts where
  /-- The amortised cost of one dynamic-tree operation on `n` nodes. -/
  dt : ℕ → ℕ
  /-- Dijkstra's algorithm in the dual, on `m` darts. -/
  sssp : ℕ → ℕ
  /-- Linear bookkeeping on `m` darts. -/
  lin : ℕ → ℕ

namespace STCosts

variable (cc : STCosts)

/-- **The bounds assumed**: `O(log n)` per dynamic-tree operation (the interface), Dijkstra in
`O(m log m)`, linear bookkeeping. -/
structure Bounds (K : ℕ) : Prop where
  dt_le : ∀ n, cc.dt n ≤ K * lg n
  sssp_le : ∀ m, cc.sssp m ≤ K * m * lg m
  lin_le : ∀ m, cc.lin m ≤ K * m

end STCosts

variable (M) in
/-- **The cost** of `stflow M c X Y`: the initial shortest-path tree of the dual, the bookkeeping
(the contracted capacities, the restriction), building the two dynamic forests (one `link` per
face and per vertex), and for each step performed `opsT + opsC` dynamic-tree operations and a
constant amount of work. -/
noncomputable def stflowCost (cc : STCosts) (c : D → ℤ) (X Y : Finset V) : ℕ :=
  cc.sssp (Fintype.card D) + cc.lin (Fintype.card D) +
    (Fintype.card F + Fintype.card V) * cc.dt (Fintype.card V + Fintype.card F) +
    stflowSteps M c X Y * ((opsT + opsC) * cc.dt (Fintype.card V + Fintype.card F) + cc.lin 1)

lemma lg_two_mul {m : ℕ} (hm : 1 ≤ m) : lg (2 * m) ≤ 2 * lg m := by
  unfold lg
  rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
  omega

variable (D V F) in
/-- **The cost of a run of `n` steps**: the initial shortest-path tree of the dual, the
bookkeeping, building the two dynamic forests, and for each step `opsT + opsC` dynamic-tree
operations and a constant amount of work. -/
noncomputable def costOf (cc : STCosts) (n : ℕ) : ℕ :=
  cc.sssp (Fintype.card D) + cc.lin (Fintype.card D) +
    (Fintype.card F + Fintype.card V) * cc.dt (Fintype.card V + Fintype.card F) +
    n * ((opsT + opsC) * cc.dt (Fintype.card V + Fintype.card F) + cc.lin 1)

lemma stflowCost_eq (cc : STCosts) (c : D → ℤ) (X Y : Finset V) :
    stflowCost M cc c X Y = costOf D V F cc (stflowSteps M c X Y) := rfl

/-- **The cost of a run of `n` steps**, on a plane map with `m ≥ 1` darts. -/
theorem costOf_le {cc : STCosts} {K : ℕ} (hc : cc.Bounds K) (hM : M.IsPlane)
    (hD : 1 ≤ Fintype.card D) (n : ℕ) :
    costOf D V F cc n ≤ 6 * K * Fintype.card D * lg (Fintype.card D) +
      n * (15 * K * lg (Fintype.card D)) := by
  have he := hM.euler
  generalize hm : Fintype.card D = m at *
  have hVF : Fintype.card V + Fintype.card F ≤ 2 * m := by omega
  have hl1 := one_le_lg m
  have hdt : cc.dt (Fintype.card V + Fintype.card F) ≤ 2 * K * lg m := by
    have := hc.dt_le (Fintype.card V + Fintype.card F)
    have := lg_mono hVF
    have := lg_two_mul hD
    calc cc.dt (Fintype.card V + Fintype.card F) ≤ K * lg (Fintype.card V + Fintype.card F) :=
          hc.dt_le _
      _ ≤ K * (2 * lg m) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * K * lg m := by ring
  unfold costOf
  rw [hm]
  have h1 := hc.sssp_le m
  have h2 : cc.lin m ≤ K * m * lg m := (hc.lin_le m).trans (by nlinarith)
  have h3 := hc.lin_le 1
  have h4 : (Fintype.card F + Fintype.card V) * cc.dt (Fintype.card V + Fintype.card F) ≤
      4 * K * m * lg m := by
    calc (Fintype.card F + Fintype.card V) * cc.dt (Fintype.card V + Fintype.card F)
        ≤ (2 * m) * (2 * K * lg m) := Nat.mul_le_mul (by omega) hdt
      _ = 4 * K * m * lg m := by ring
  have h5 : (opsT + opsC) * cc.dt (Fintype.card V + Fintype.card F) + cc.lin 1 ≤
      15 * K * lg m := by
    simp only [opsT, opsC]; nlinarith
  have h6 := Nat.mul_le_mul_left n h5
  nlinarith

/-- **The cost bound in terms of the number of steps**, on a plane map with `m ≥ 1` darts. -/
theorem stflowCost_le {cc : STCosts} {K : ℕ} (hc : cc.Bounds K) (hM : M.IsPlane)
    (hD : 1 ≤ Fintype.card D) (c : D → ℤ) (X Y : Finset V) :
    stflowCost M cc c X Y ≤ 6 * K * Fintype.card D * lg (Fintype.card D) +
      stflowSteps M c X Y * (15 * K * lg (Fintype.card D)) :=
  costOf_le hc hM hD _

/-- **A run of at most `m + 1` steps costs at most `36 K m lg m`**, on a plane map with `m ≥ 1`
darts. -/
theorem costOf_le_of_le {cc : STCosts} {K : ℕ} (hc : cc.Bounds K) (hM : M.IsPlane)
    (hD : 1 ≤ Fintype.card D) {n : ℕ} (hn : n ≤ Fintype.card D + 1) :
    costOf D V F cc n ≤ 36 * K * Fintype.card D * lg (Fintype.card D) := by
  have h := costOf_le (V := V) (F := F) hc hM hD n
  generalize Fintype.card D = m at *
  generalize lg m = l at *
  have : n * (15 * K * l) ≤ (2 * m) * (15 * K * l) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- **The pivot bound** of Borradaile and Klein (each dart pivots into the dual tree at most once;
Erickson, SODA 2010): at most `m + 1` steps on `m` darts. A hypothesis here; it follows from
`EnterOnce` (`PlanarFlow.STFlow.pivotBound_of_enterOnce`), hence from `NoReentry`
(`PlanarFlow.STFlow.pivotBound_of_noReentry`). -/
def PivotBound (M : CombMap D V F) : Prop :=
  ∀ (c : D → ℤ) (X Y : Finset V), stflowSteps M c X Y ≤ Fintype.card D + 1

/-- **The cost is `O(n log n)`** under the pivot bound: at most `36 K m lg m` on a plane map with
`m ≥ 1` darts. -/
theorem stflowCost_le_of_pivotBound {cc : STCosts} {K : ℕ} (hc : cc.Bounds K) (hM : M.IsPlane)
    (hD : 1 ≤ Fintype.card D) (hpiv : PivotBound M) (c : D → ℤ) (X Y : Finset V) :
    stflowCost M cc c X Y ≤ 36 * K * Fintype.card D * lg (Fintype.card D) := by
  have h := stflowCost_le hc hM hD c X Y
  have hs := hpiv c X Y
  generalize Fintype.card D = m at *
  generalize stflowSteps M c X Y = k at *
  generalize lg m = l at *
  have : k * (15 * K * l) ≤ (2 * m) * (15 * K * l) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-- **Unconditionally**, the cost is `O((m + F²) log m)`. -/
theorem stflowCost_le_sq {cc : STCosts} {K : ℕ} (hc : cc.Bounds K) (hM : M.IsPlane)
    (hD : 1 ≤ Fintype.card D) (c : D → ℤ) (X Y : Finset V) :
    stflowCost M cc c X Y ≤ 6 * K * Fintype.card D * lg (Fintype.card D) +
      (2 * Fintype.card F * Fintype.card F + 1) * (15 * K * lg (Fintype.card D)) :=
  (stflowCost_le hc hM hD c X Y).trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (stflowSteps_le c X Y)) _)

end STFlow

end PlanarFlow
