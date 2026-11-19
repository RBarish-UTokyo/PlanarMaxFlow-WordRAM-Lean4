module

public import PlanarFlow.BKMNW.NfBound
public import PlanarFlow.BKMNW.MachNeg

/-!
# The precondition of the final call of FixConservationOnPath

**`fixPath_negPre`**: the lengths `c - s.1` of the negative-length shortest-path call at the end
of `fixPath` (`s` the state after the `k` stages) meet `MfDrv.NegPre` on a plane map with
transitive rotations and faces: the loops of the dual (darts whose two sides are one face) have
nonnegative length (`EffInvB.loop_nonneg`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **`NegPre` of the final call of `fixPath`.** -/
theorem fixPath_negPre (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀)
    {P : SPath M} {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    {fr : FRFun F} (hfr : FRSpec fr) :
    MfDrv.NegPre M (c - (fpState M c f₀ P mssp fr P.k).1) :=
  ⟨hM, hrot, hface, fun d hd =>
    (fixPath_invB hM hc hf₀ hmssp hfr P.k le_rfl).loop_nonneg hd⟩

end BKMNW

end PlanarFlow
