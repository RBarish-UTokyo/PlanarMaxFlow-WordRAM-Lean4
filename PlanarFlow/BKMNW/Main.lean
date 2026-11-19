module

public import PlanarFlow.BKMNW.Sep
public import PlanarFlow.BKMNW.CycleSink
public import PlanarFlow.BKMNW.Leaf
public import PlanarFlow.BKMNW.CutBuild

/-!
# The implemented subroutines of Algorithm 1

The algorithm of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput. 46(4),
2017) runs Algorithm 1 (`PlanarFlow/BKMNW/Algorithm.lean`) with **every subroutine implemented**
(`impl`):

* FixConservationOnPath by `fixPath` (`PlanarFlow/BKMNW/FixPath.lean`, Section 3);
* CycleToSingleSinkLimitedMaxFlow and SingleSourceToCycleLimitedMaxFlow by `c2sImpl` and
  `s2cImpl` (`PlanarFlow/BKMNW/CycleSink.lean`, Section 4 and Appendix F);
* the push-backs of line 13 by `retImpl` and `frmImpl` (`PlanarFlow/BKMNW/PushBack.lean`,
  Appendix C);
* the leaves by `leafSolve` (`PlanarFlow/BKMNW/Leaf.lean`).

The implementations use four planar subroutines, given with their specifications: MSSP
(`MSSPSpec`, Klein; Cabello–Chambers–Erickson), FR-Dijkstra (`FRSpec`), shortest paths with
negative lengths (`NegSSSPSpec`, Mozes–Wulff-Nilsen), and SingleSourceSingleSinkMaxFlow
(`STFlowSpec`, Borradaile–Klein); `impl_spec` proves that the implementations meet the
specifications `NodeOracles.Spec` of Algorithm 1.

The recursion runs these implementations on the piece maps (`PlanarFlow.BKMNW.runL`,
`PlanarFlow/BKMNW/Local.lean`). The correctness theorem with no hypothesis beyond planarity,
nonnegative capacities and disjoint terminals is `PlanarFlow.BKMNW.maxflow_plane`
(`PlanarFlow/BKMNW/MaxFlow.lean`). It supersedes the theorems formerly stated here
(`bkmnw_isMax` and its variants, and the cost bounds `bkmnw_cost`, `bkmnw_cost_plane`), which
assumed a separator subroutine meeting `PlanarFlow.BKMNW.SepSpec`, a specification that cannot be
met in general; they have been removed.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- **The subroutines of Algorithm 1**, all implemented, from MSSP, FR-Dijkstra, shortest paths
with negative lengths and single-source single-sink maximum flow. -/
noncomputable def impl (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (negSSSP : (D → ℤ) → Option (F → ℤ))
    (stflow : (D → ℤ) → Finset V → Finset V → D → ℤ) : NodeOracles M where
  leaf U S T A := leafSolve M U S T A
  fix U f π := fixPath M U f π mssp fr negSSSP
  c2s U f π H := c2sImpl M mssp fr negSSSP stflow U f π H
  s2c U f π H := s2cImpl M mssp fr negSSSP stflow U f π H
  ret _ f X S := retImpl M fr f X S
  frm _ f T X := frmImpl M fr f T X

/-- **The implementations meet the specifications of Algorithm 1**, from the specifications of
the planar subroutines. -/
theorem impl_spec (hM : M.IsPlane) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d)
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpec M mssp)
    {fr : FRFun F} (hfr : FRSpec fr) {negSSSP : (D → ℤ) → Option (F → ℤ)}
    (hneg : NegSSSPSpec M negSSSP) {stflow : (D → ℤ) → Finset V → Finset V → D → ℤ}
    (hst : STFlowSpec M stflow) : (impl M mssp fr negSSSP stflow).Spec u := by
  have hcap : ∀ (P : Finset D) d, 0 ≤ capOn u P d := fun P d => by
    unfold capOn; split_ifs
    · exact hu d
    · exact le_rfl
  exact ⟨fun Q S T A hQ hQ2 hST hSA hTA => leafSolve_spec hu hQ hQ2 hST hSA hTA,
    fun P f π hf => fixPath_spec hM (hcap P) hf π (hmssp π) hfr hneg,
    fun P f π H hf h1 h2 h3 => c2s_spec hM (hcap P) hf h1 h2 h3 (hmssp π) hfr hneg hst,
    fun P f π H hf h1 h2 h3 => s2c_spec hM (hcap P) hf h1 h2 h3 (hmssp π) hfr hneg hst,
    fun P f X S hf h1 h2 h3 => ret_spec hM hfr (hcap P) hf h1 h2 h3,
    fun P f T X hf h1 h2 h3 => frm_spec hM hfr (hcap P) hf h1 h2 h3⟩

/-- On a plane map, darts, vertices and faces number at most `2 n + 2`. -/
lemma mapSize_le_of_isPlane (hM : M.IsPlane) : mapSize M ≤ 2 * Fintype.card D + 2 := by
  have := hM.euler; unfold mapSize; omega

end BKMNW

end PlanarFlow
