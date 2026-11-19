module

public import PlanarFlow.Monge.DDGBF2
public import PlanarFlow.NegSSSP.Spec

/-!
# The outcome of Bellman–Ford over the union of two dense distance graphs as a `PotOut` output

The program `PlanarFlow.Monge.bfDDG2` (`PlanarFlow.Monge.bfDDG2_exec`) ends with the flag
`r30 = 0` and values forming a feasible potential of both matrices, or with `r30 = 1` and no
common feasible potential. `potOut_bfDDG2` turns this outcome into the output
`PlanarFlow.NegSSSP.PotOut` of the union digraph `PlanarFlow.Monge.ddg2 b D₁ D₂ π` (the outcome
required of the subroutine `bf` of the negative-length recursion, `BFDDGSpec`, for two complete
dense distance graphs crossing in their own orders), as `potOut_bfDDG` does for one matrix;
`negSSSPOut_bfDDG2` gives the corresponding `NegSSSPOut` (a closed walk of negative length when
there is no potential).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Monge BKMNW

/-- **The outcome of `bfDDG2` is a `PotOut` output of the union digraph.** -/
theorem potOut_bfDDG2 {b : ℕ} {D₁ D₂ : ℕ → ℕ → ℤ} {π : ℕ → ℕ} (hπ : IsPermB b π) {E : ℕ → ℤ}
    {flag : ℕ}
    (h : (flag = 0 ∧ Feas2 b D₁ D₂ π E) ∨ (flag = 1 ∧ ¬ ∃ E', Feas2 b D₁ D₂ π E')) :
    PotOut (ddg2 b D₁ D₂ π) (if flag = 0 then some (fun v => E v) else none) := by
  rcases h with ⟨h0, hp⟩ | ⟨h1, hn⟩
  · simp only [h0, ↓reduceIte]; exact isPot_of_feas2 hπ hp
  · simp only [h1, one_ne_zero, ↓reduceIte]
    exact fun hP => hn ((hasPot2_iff hπ).1 hP)

/-- The outcome of `bfDDG2` as a `NegSSSPOut` output of the union digraph. -/
theorem negSSSPOut_bfDDG2 {b : ℕ} {D₁ D₂ : ℕ → ℕ → ℤ} {π : ℕ → ℕ} (hπ : IsPermB b π)
    {E : ℕ → ℤ} {flag : ℕ}
    (h : (flag = 0 ∧ Feas2 b D₁ D₂ π E) ∨ (flag = 1 ∧ ¬ ∃ E', Feas2 b D₁ D₂ π E')) :
    NegSSSPOut (ddg2 b D₁ D₂ π) (if flag = 0 then some (fun v => E v) else none) :=
  negSSSPOut_of_potOut (potOut_bfDDG2 hπ h)

end NegSSSP

end PlanarFlow
