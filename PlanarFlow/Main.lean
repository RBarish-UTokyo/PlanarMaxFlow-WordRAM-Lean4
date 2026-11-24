module

public import PlanarFlow.Spec
public import PlanarFlow.Flow.Network
public import PlanarFlow.Plane.Feasible
public import PlanarFlow.Machine.Main
public import PlanarFlow.Dijkstra.Run
public import PlanarFlow.Matching.Main
public import WordRAM.Machine.IsWord

/-!
# The targets of `PlanarFlow/Spec.lean`

The targets are stated in `PlanarFlow/Spec.lean`; this file proves them from the library.

* `PlanarFlow.maxflow_mincut` (`MaxFlowMinCut`): `PlanarFlow.Network.max_flow_min_cut` and weak
  duality `PlanarFlow.Network.value_le_cutCap`.
* `PlanarFlow.miller_naor` (`MillerNaor`): `PlanarFlow.CombMap.bflow_iff_potential`.
* `PlanarFlow.feasible_flow_machine` (`FeasibleFlowMachine`): the program
  `compile Feas.prog 0 ++ [halt]` and `PlanarFlow.Feas.feas_runsWithin`.
* `PlanarFlow.dijkstra_machine` (`DijkstraMachine`): the program `compile Dijk.prog 0 ++ [halt]`
  and `PlanarFlow.Dijk.dijkstra_runsWithin`.
* `PlanarFlow.bipartite_matching_machine` (`BipartiteMatchingMachine`): the program
  `compile BM.prog 0 ++ [halt]` and `PlanarFlow.BM.matching_runsWithin`.
-/

@[expose] public section

namespace PlanarFlow

universe u

/-- **The max-flow min-cut theorem** for multiple sources and sinks. -/
theorem maxflow_mincut : MaxFlowMinCut.{u} := by
  intro V E _ _ _ _ N S T hST hcap
  obtain ⟨f, X, hf, hX, hv⟩ := N.max_flow_min_cut hST hcap
  exact ⟨f, X, hf, hX, hv, fun g hg => hv ▸ Network.value_le_cutCap hg hX,
    fun Y hY => hv ▸ Network.value_le_cutCap hf hY⟩

/-- **Supplies and demands in plane graphs (Miller and Naor).** -/
theorem miller_naor : MillerNaor.{u} := by
  intro D V F _ _ _ _ _ _ M hM b u g hg hgb
  exact CombMap.bflow_iff_potential hM u hg hgb

/-- **Feasible flows in plane graphs on the machine.** -/
theorem feasible_flow_machine : FeasibleFlowMachine :=
  ⟨WordRAM.Machine.Stmt.compile Feas.prog 0 ++ [WordRAM.Instr.halt],
    WordRAM.Machine.Stmt.isWord_compile_halt (by kernel_rfl),
    fun _ _ he => Feas.feas_runsWithin he⟩

/-- **Dijkstra's algorithm on the machine.** -/
theorem dijkstra_machine : DijkstraMachine :=
  ⟨WordRAM.Machine.Stmt.compile Dijk.prog 0 ++ [WordRAM.Instr.halt],
    WordRAM.Machine.Stmt.isWord_compile_halt (by kernel_rfl),
    fun _ _ he => Dijk.dijkstra_runsWithin he⟩

/-- **Maximum bipartite matching on the machine.** -/
theorem bipartite_matching_machine : BipartiteMatchingMachine :=
  ⟨WordRAM.Machine.Stmt.compile BM.prog 0 ++ [WordRAM.Instr.halt],
    WordRAM.Machine.Stmt.isWord_compile_halt (by kernel_rfl),
    fun _ _ he => BM.matching_runsWithin he⟩

end PlanarFlow
