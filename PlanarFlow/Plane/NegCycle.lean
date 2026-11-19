module

public import PlanarFlow.Plane.Feasible
public import PlanarFlow.ShortestPath.BellmanFord

/-!
# Feasibility and negative cycles of the dual graph

The *dual graph* of a map `M` with lengths `ℓ` on the darts (`PlanarFlow.CombMap.dualGraph`) has
the faces as vertices and, for every dart `d`, an arc from `face d` to `face (rev d)` of length
`ℓ d`. A feasible potential for `ℓ` (`PlanarFlow.CombMap.IsPotential`) is exactly a feasible
potential of the dual graph, which exists if and only if the dual graph has no closed walk of
negative length (`PlanarFlow.Digraph.exists_pot_iff`). Hence:

* `PlanarFlow.CombMap.circ_iff_no_neg_cycle` (**Hassin**): on a plane map, a circulation within
  the capacities `u` exists if and only if the dual graph with lengths `u` has no negative cycle.
* `PlanarFlow.CombMap.bflow_iff_no_neg_cycle` (**Miller–Naor**): a flow meeting the supplies and
  demands `b` within the capacities `u` exists if and only if the supplies and demands balance and
  the dual graph with lengths `u - g` has no negative cycle, for any base flow `g` with net flow
  `b`.

## References

* R. Hassin, *Maximum flow in (s,t) planar networks*, Inform. Process. Lett. 13 (1981), 107.
* G. L. Miller, J. Naor, *Flow in planar graphs with multiple sources and sinks*, SIAM J. Comput.
  24 (1995), 1002–1017.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace CombMap

variable {D V F : Type*} {M : CombMap D V F}
variable [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]

/-- The dual graph with lengths `ℓ`: an arc from `face d` to `face (rev d)` of length `ℓ d` for
every dart `d`. -/
def dualGraph (M : CombMap D V F) (ℓ : D → ℤ) : Digraph F D where
  src := M.face
  dst d := M.face (M.rev d)
  len := ℓ

lemma isPotential_iff_isPot (ℓ : D → ℤ) (φ : F → ℤ) :
    M.IsPotential ℓ φ ↔ (M.dualGraph ℓ).IsPot φ := by
  unfold IsPotential Digraph.IsPot
  refine forall_congr' fun d => ?_
  simp only [cob, dualGraph]
  constructor <;> intro h <;> linarith

/-- **Hassin's theorem, with negative cycles.** On a plane map, a circulation within the
capacities `u` exists if and only if no closed walk of the dual graph with lengths `u` has
negative length. -/
theorem circ_iff_no_neg_cycle (hM : M.IsPlane) (u : D → ℤ) :
    (∃ f, M.IsCirc f ∧ ∀ d, f d ≤ u d) ↔
      ∀ m c, (M.dualGraph u).IsClosedWalk m c → 0 ≤ (M.dualGraph u).walkLen m c := by
  rw [circ_iff_potential hM, ← Digraph.exists_pot_iff]
  exact exists_congr fun φ => isPotential_iff_isPot u φ

/-- **Miller–Naor, with negative cycles.** On a plane map, if `g` is antisymmetric with net flow
`b`, a `b`-flow within the capacities `u` exists if and only if no closed walk of the dual graph
with lengths `u - g` has negative length. -/
theorem bflow_iff_no_neg_cycle (hM : M.IsPlane) {b : V → ℤ} (u : D → ℤ) {g : D → ℤ}
    (hg : M.IsAntisymm g) (hgb : ∀ v, M.div g v = b v) :
    (∃ f, M.IsBFlow b u f) ↔
      ∀ m c, (M.dualGraph (u - g)).IsClosedWalk m c → 0 ≤ (M.dualGraph (u - g)).walkLen m c := by
  rw [bflow_iff_potential hM u hg hgb, ← Digraph.exists_pot_iff]
  exact exists_congr fun φ => isPotential_iff_isPot (u - g) φ

end CombMap

end PlanarFlow
