module

public import PlanarFlow.Spec

/-!
# Planar flows: the maximum-flow target with valid output indices

`MaxFlowMachine`: the statement `MaxFlowMachine'` of `PlanarFlow/Spec.lean`, strengthened by the
requirement that the printed indices are valid: the program prints `p ++ Z :: q` with `|p| = n`
and `p[x] < |q|` for every dart `x < n`, so the flow on dart `x` is the entry `q[p[x]]` of `q`
minus `Z`, with no lookup outside a list.
-/

@[expose] public section

namespace PlanarFlow

/-- **Maximum flow in plane graphs on the machine** (Borradaile, Klein, Mozes, Nussbaum,
Wulff-Nilsen). One program for the word RAM computes, for every well-formed input describing a
plane map with `n` darts and `K` vertices (loops allowed), capacities on the darts and sets of
sources and sinks, a maximum flow from the sources to the sinks within
`c (n + K + 1)(⌊log₂ n⌋ + 1)³` steps, whenever the word size is at least `c (7 · size)^k`: it
prints `p ++ Z :: q` with `|p| = n` and `p[x] < |q|` for every dart `x < n`, the flow on dart `x`
being `q[p[x]] - Z` (written `q.getD (p.getD x 0) 0 - Z`; both lookups are in range). -/
def MaxFlowMachine : Prop :=
  ∃ (prog : WordRAM.Program) (c k : ℕ), ∀ (d : List ℕ) (W : ℕ) (he : Feas.MEnc' d W),
    c * (7 * Feas.size' d) ^ k ≤ W →
    ∃ (p : List ℕ) (Z : ℕ) (q : List ℕ), p.length = Feas.nd d ∧
      (∀ x < Feas.nd d, p.getD x 0 < q.length) ∧
      Feas.IsSTFlow' he.wf (fun x => ((q.getD (p.getD x 0) 0 : ℕ) : ℤ) - Z) ∧
      (∀ g, Feas.IsSTFlow' he.wf g →
        Feas.stValue' he.wf g ≤
          Feas.stValue' he.wf (fun x => ((q.getD (p.getD x 0) 0 : ℕ) : ℤ) - Z)) ∧
      WordRAM.RunsWithin prog (Feas.inp d) W
        (c * (Feas.nd d + Feas.nv d + 1) * (Nat.log 2 (Feas.nd d) + 1) ^ 3) (p ++ Z :: q)

end PlanarFlow

end
