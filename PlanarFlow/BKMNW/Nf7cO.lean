module

public import PlanarFlow.BKMNW.Nf7cN

/-!
# The prologue and step 2 at a node call: semantic facts

* **`msW_le`**: the answers of the MSSP call with the lengths `c − f₀` of a pseudoflow are at
  most `absSum c` (a distance with nonnegative lengths is at most their sum, `Σ f₀ = 0`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep SPath
  WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Gen

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **The answers of the MSSP call are at most `absSum c`.** -/
theorem msW_le (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) (P : SPath M)
    {c f₀ : D → ℤ} (hf₀ : IsPseudo M c f₀) {t t' : D} (ht : M.face t ∈ P.faces) :
    (MsCall.msW M P (c - f₀) t t' : ℤ) ≤ absSum c := by
  classical
  have hnn : ∀ e, 0 ≤ (c - f₀) e := fun e => by
    simp only [Pi.sub_apply]; linarith [hf₀.le_cap e]
  have hAS := absSum_nonneg c
  unfold MsCall.msW
  rcases e : Klein.msspPlaneK M P.darts (c - f₀) (M.face t) (M.face t') with _ | a
  · simpa using hAS
  · have hD := Klein.msspPlaneK_spec hM hrot hface P (c - f₀) (fun e _ => hnn e) _ ht
    obtain ⟨h0, h1⟩ := hD.le_sum_len (fun x => hnn x.1) e
    have h2 : ∑ x : {e // e ∉ P.darts}, (c - f₀) x.1 ≤ ∑ e, (c - f₀) e := by
      rw [← Finset.sum_subtype (univ.filter fun e => e ∉ P.darts) (by simp)]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun e _ _ => hnn e
    have h3 : ∑ e, (c - f₀) e = ∑ e, c e := by
      simp only [Pi.sub_apply, sum_sub_distrib, sum_univ_antisymm hf₀.antisymm, sub_zero]
    have h4 : ∑ e, c e ≤ absSum c := sum_le_sum fun e _ => le_abs_self _
    simp only [Option.getD_some, Int.toNat_of_nonneg h0]
    exact h1.trans (h2.trans (h3 ▸ h4))

end Gen

end BKMNW

end PlanarFlow
