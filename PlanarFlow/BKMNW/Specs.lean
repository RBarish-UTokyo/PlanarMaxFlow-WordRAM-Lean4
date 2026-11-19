module

public import PlanarFlow.BKMNW.Model
public import PlanarFlow.BKMNW.DDG
public import PlanarFlow.Plane.NegCycle

/-!
# Shortest paths with negative lengths

The specification of the shortest-path subroutine with negative lengths used by the fixing
procedure of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput. 46(4), 2017,
Section 3.2, lines 30–33 of Algorithm 6; the algorithm of Mozes and Wulff-Nilsen): for a digraph
with integer lengths (the dual of a plane map), either a feasible potential (for instance the
distances from a root) or a closed walk of negative length (`NegSSSPOut`, `NegSSSPSpec`).

The other specifications: distances, dense distance graphs and FR-Dijkstra
(`PlanarFlow/BKMNW/Dist.lean`, `PlanarFlow/BKMNW/DDG.lean`), multiple-source shortest paths
(`PlanarFlow/BKMNW/FixPath.lean`), the subroutines of the recursion
(`PlanarFlow/BKMNW/Algorithm.lean`), the separators (`PlanarFlow/BKMNW/Sep.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

/-! ### Shortest paths -/

section ShortestPaths

variable {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A]

/-- **The output of shortest paths with negative lengths**: a feasible potential, or (`none`) a
closed walk of negative length. -/
def NegSSSPOut (G : Digraph X A) : Option (X → ℤ) → Prop
  | some p => G.IsPot p
  | none => ∃ m c, G.IsClosedWalk m c ∧ G.walkLen m c < 0

end ShortestPaths

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- **The specification of shortest paths with negative lengths in the dual of a plane map**: for
every choice of lengths on the darts, a feasible potential of the dual graph or a negative closed
walk in it. -/
def NegSSSPSpec [Fintype F] [DecidableEq F] (M : CombMap D V F)
    (negSSSP : (D → ℤ) → Option (F → ℤ)) : Prop :=
  ∀ ℓ, NegSSSPOut (M.dualGraph ℓ) (negSSSP ℓ)

end BKMNW

end PlanarFlow
