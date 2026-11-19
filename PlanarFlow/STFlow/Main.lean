module

public import PlanarFlow.STFlow.Cost
public import PlanarFlow.NegSSSP.Main

/-!
# Maximum flow with single-source single-sink maximum flow implemented

The maximum-flow algorithm of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J.
Comput. 46(4), 2017) takes as a subroutine SingleSourceSingleSinkMaxFlow,
specified by `PlanarFlow.BKMNW.STFlowSpec`. Here that subroutine is the augmenting-path algorithm
of Borradaile and Klein with pivots (`PlanarFlow.STFlow.stflow`), which meets the specification on
every plane map (`PlanarFlow.STFlow.stflow_spec`).

* `stflow_plane`: **both results**: `stflow M` meets `STFlowSpec M`, and its counted cost is at
  most `6 K m lg m` plus `15 K lg m` per step, hence `36 K m lg m` under the pivot bound.
* `stflowSpec_family`: the same for every plane map, as a family.

The maximum-flow algorithm (`PlanarFlow.BKMNW.planeOracles`) uses the perturbed variant with the
word-size perturbation `PlanarFlow.STFlow.pstflowW` (`PlanarFlow/STFlow/IsoRun.lean`), which
meets the same specification and whose pivot bound is proved
(`PlanarFlow.STFlow.pstflowWCost_le`; for the lexicographic variant `PlanarFlow.STFlow.pstflow`,
`PlanarFlow.STFlow.pstflowCost_le`); the unperturbed `stflow`
is kept, with its cost bound under the pivot bound `PivotBound` (not proved). The algorithm's
correctness on every plane map is `PlanarFlow.BKMNW.maxflow_plane`
(`PlanarFlow/BKMNW/MaxFlow.lean`), which supersedes the corollaries `bkmnw_isMax_stflow` and
`bkmnw_isMax_ofRotation_stflow` formerly stated here (they assumed a separator subroutine meeting
`PlanarFlow.BKMNW.SepSpec`, which cannot be met in general).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset BKMNW CombMap NegSSSP

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- **Single-source single-sink maximum flow on a plane map**: the implementation meets
`STFlowSpec`, and with the costs of its subroutines bounded by `STCosts.Bounds` (`O(log n)` per
dynamic-tree operation, Dijkstra in `O(m log m)`), its cost on `m ≥ 1` darts is at most
`6 K m lg m + 15 K lg m` per step, hence at most `36 K m lg m` under the pivot bound. -/
theorem stflow_plane (hM : M.IsPlane) {cc : STCosts} {K : ℕ} (hc : cc.Bounds K)
    (hD : 1 ≤ Fintype.card D) :
    STFlowSpec M (stflow M) ∧
      (∀ c X Y, stflowCost M cc c X Y ≤ 6 * K * Fintype.card D * lg (Fintype.card D) +
        stflowSteps M c X Y * (15 * K * lg (Fintype.card D))) ∧
      (PivotBound M → ∀ c X Y,
        stflowCost M cc c X Y ≤ 36 * K * Fintype.card D * lg (Fintype.card D)) :=
  ⟨stflow_spec hM, fun c X Y => stflowCost_le hc hM hD c X Y,
    fun hp c X Y => stflowCost_le_of_pivotBound hc hM hD hp c X Y⟩

universe u in
/-- **Single-source single-sink maximum flow for every plane map**: the family `stflow` meets
`STFlowSpec` on every plane map (the form in which the subroutine is passed to pieces). -/
theorem stflowSpec_family {D V F : Type u} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] (M : CombMap D V F) (hM : M.IsPlane) :
    STFlowSpec M (stflow M) :=
  stflow_spec hM

end STFlow

end PlanarFlow
