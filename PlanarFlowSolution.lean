module

public import PlanarFlow.Main
public import PlanarFlow.BKMNW.Nf9aV

/-!
# Solution for `PlanarFlowChallenge.lean`

The first five theorems of `PlanarFlowChallenge.lean` are the theorems of the same names in
`PlanarFlow/Main.lean`, about the definitions of `PlanarFlow/Spec.lean` and `WordRAM/Spec.lean`.
This module imports the library and never imports `PlanarFlowChallenge`.

* `PlanarFlow.maxflow_mincut : PlanarFlow.MaxFlowMinCut`
* `PlanarFlow.miller_naor : PlanarFlow.MillerNaor`
* `PlanarFlow.feasible_flow_machine : PlanarFlow.FeasibleFlowMachine`
* `PlanarFlow.dijkstra_machine : PlanarFlow.DijkstraMachine`
* `PlanarFlow.bipartite_matching_machine : PlanarFlow.BipartiteMatchingMachine`

The sixth, `PlanarFlow.maxflow_machine : PlanarFlow.MaxFlowMachine` (`PlanarFlow/SpecMaxFlow.lean`),
is proved below from `PlanarFlow.BKMNW.Pp.maxFlowMachine_holds` (`PlanarFlow.BKMNW.Nf9aV`).
-/

public section

/-- **Maximum flow in plane graphs on the machine (BKMNW)**: the theorem of
`PlanarFlowChallenge.lean`, from the library's theorem
`PlanarFlow.BKMNW.Pp.maxFlowMachine_holds`. -/
theorem PlanarFlow.maxflow_machine : PlanarFlow.MaxFlowMachine :=
  PlanarFlow.BKMNW.Pp.maxFlowMachine_holds

end
