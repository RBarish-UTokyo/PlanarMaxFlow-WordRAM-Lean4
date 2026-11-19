module

public import PlanarFlow.BKMNW.MongeBridge
public import PlanarFlow.Monge.FRSpec

/-!
# FR-Dijkstra on the machine and the specifications of the algorithm

`frProg_isDist`: the run of the machine program `PlanarFlow.Monge.FR.frProg` (FR-Dijkstra
with the bipartite Monge heaps, lazy extraction and the range-minimum structures of the half
blocks) computes the distances `IsDist` from the root in the union `(faceDDG β b D).union Ex` of
one dense distance graph (on the corners `0, …, b - 1`, satisfying the crossing inequality) and
the explicit arcs, the input of FR-Dijkstra in the algorithm of Borradaile, Klein, Mozes,
Nussbaum and Wulff-Nilsen, within `PlanarFlow.Monge.FR.frCost` steps
(`PlanarFlow.Monge.FR.frCost_le`: `O(b log² b + (N + m) log N)`;
`PlanarFlow.Monge.FR.frCost_le_fr`: at most `6300 (N lg N ^ 2 + m lg N)`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine Monge.FR

variable {P : Prm} {I : Input}

lemma fv_inj_corner (hL : Lay P) :
    ∀ i < P.b, ∀ j < P.b, fv P hL.N_pos i = fv P hL.N_pos j → i = j :=
  fun i hi j hj h => fv_inj (by have := hL.bN; omega) (by have := hL.bN; omega) h

/-- **FR-Dijkstra on the machine computes the distances of the specification.** -/
theorem frProg_isDist (hL : Lay P) (h0 : P.off 0 = 0) (hDc : Monge.Crossing P.b P.D)
    (hA : Nonempty (Monge.Arc P.b ⊕ Fin (exArcs P hL.N_pos).length))
    (hp : ((faceDDG (fv P hL.N_pos) P.b P.D).union (exArcs P hL.N_pos)).IsPot (fun y => P.p y))
    (c : Config) (hc : WordsBounded P.W c) (hin : Inp P c) (hDa : Data P c) :
    ∃ c' k, Exec I P.W frProg c c' k ∧ k ≤ frCost P ∧ Data P c' ∧ c'.output = c.output ∧
      ∃ δ : Fin P.N → Option ℤ,
        IsDist ((faceDDG (fv P hL.N_pos) P.b P.D).union (exArcs P hL.N_pos)) (fv P hL.N_pos P.r) δ ∧
        ∀ y : Fin P.N, (c'.nmem (P.sb + y) = 1 ↔ δ y ≠ none) ∧
          ∀ ℓ, δ y = some ℓ → c'.rmem (P.db + y) = ℓ := by
  obtain ⟨c', k, e, hk, hDa', hO, δ, hδ, hmem⟩ := frProg_dist (I := I) hL h0 hDc hA
    ((isPot_ddgPlus_iff (fv_inj_corner hL)).2 hp) c hc hin hDa
  exact ⟨c', k, e, hk, hDa', hO, δ, (gdist_ddgPlus_iff (fv_inj_corner hL)).1 hδ, hmem⟩

end BKMNW

end PlanarFlow
