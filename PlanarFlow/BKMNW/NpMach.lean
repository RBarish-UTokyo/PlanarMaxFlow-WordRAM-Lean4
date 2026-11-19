module

public import PlanarFlow.BKMNW.NpMain
public import PlanarFlow.BKMNW.StExp

/-!
# The node subroutines of the machine at every call

The family of node subroutines whose outputs the five subroutine programs must produce
(`FixPSpecN` … `FrmPSpecN` relative to it): at the call `x` (proof `h` of its piece-map
invariant),

  **`machNF gid I chs pch x h = implG (pmap h) (pch x h) (Klein.msspPlaneK (pmap h)) (frRef _)
  (negLay gid I x h) (chs x h).flow`**

— Klein's MSSP and `frRef` (no choice: distances are unique, `msspPlaneK_eq_of_isDist`,
`frSpec_agree`), the machine's negative-length shortest paths `negLay` (the outcome of the run of
`negFix`), the s-t flow of the machine's explicit choices `chs x h` (`StExp.lean`), and the
machine's push-back `pch x h` (e.g. `pushFwdL` with the machine's root, vertex order and dart
order, `NpPushL.lean`).

* **`nSpecOn_machNF`**: wherever the s-t flow choices are valid (`StChoice.OK`) and the push-back
  meets `PushSpec`, the family meets `NSpecOn`, so `mfMain_cMachXGEN (NF := machNF gid I chs pch)`
  gives the whole program with only the program hypotheses (separator, parts, five subroutines)
  and the validity of the choices;
* `pushSpec_of_L`: the push-back of explicit orders meets `PushSpec` (`pushSpec_pushFwdL`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset Function Equiv CombMap MfDrv

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The node subroutines of the machine at every call.** -/
noncomputable def machNF (gid : D → ℕ) (I : WordRAM.Input)
    (chs : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → STFlow.StChoice (pmap h))
    (pch : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      PushFn (Orbit.SDart (pdarts M x.1.piece x.2.1)) (Orbit.SVert x.2.2 (pdarts M x.1.piece x.2.1))) :
    NFam M :=
  fun x h => implG (pmap h) (pch x h) (Klein.msspPlaneK (pmap h)) (frRef _) (negLay gid I x h)
    (chs x h).flow

/-- **The machine's node subroutines meet their specifications** at the calls where the s-t flow
choices are valid and the push-back meets `PushSpec`. -/
theorem nSpecOn_machNF (gid : D → ℕ) (I : WordRAM.Input)
    (chs : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → STFlow.StChoice (pmap h))
    (pch : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      PushFn (Orbit.SDart (pdarts M x.1.piece x.2.1)) (Orbit.SVert x.2.2 (pdarts M x.1.piece x.2.1)))
    (Reach : MCall M → Prop) (hok : ∀ x, Reach x → ∀ h, (chs x h).OK)
    (hpush : ∀ x, Reach x → ∀ h, (pmap h).IsPlane → PushSpec (pmap h) (pch x h)) :
    NSpecOn M (machNF gid I chs pch) Reach :=
  fun x hx h hpl hrot hface _ hu => implG_spec hpl hu (hpush x hx h hpl)
    (Klein.msspPlaneK_spec hpl hrot hface) (frRef_spec _) (negLay_spec _ _ _ _)
    (STFlow.StChoice.spec hpl (hok x hx h))

/-- The push-back of explicit choices (root, order of the visits, order of the darts) meets
`PushSpec` on a plane map. -/
theorem pushSpec_of_L {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'} (hM : M'.IsPlane)
    (r : F') {ord : (D' → ℤ) → List V'} (hord : TopoOK M' ord) {outs : V' → List D'}
    (houts : OutsOK M' outs) : PushSpec M' (pushFwdL M' (frRef _) r ord outs) :=
  pushSpec_pushFwdL hM (frRef_spec _) r hord houts

end NsStep

end BKMNW

end PlanarFlow
