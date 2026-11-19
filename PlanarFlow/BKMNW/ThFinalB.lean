module

public import PlanarFlow.BKMNW.ThFinal
public import PlanarFlow.BKMNW.NcPbHyp
public import PlanarFlow.BKMNW.MsEncJ

/-!
# The maximum flow: the final assembly with the MSSP encoder and the cycle-to-sink programs filled in

`maxFlowMachine_final` (`ThFinal.lean`) left four parameters open: the MSSP encoder `msEnc`, the
fix program `fixP` and the two cycle/sink programs `c2sP`, `s2cP`. This file fills in

* `msEnc := MsEnc.msEnc` (`MsEnc.msEnc_spec`, every plane map, with `MsEnc.Rm`, `MsEnc.wzm`);
* `c2sP := c2sP fzP pbP`, `s2cP := s2cP fzP pbP` (`pbP_spec'`, `c2sHypF_of_fz`,
  `s2cHypF_of_fz`), with the `fixFrozen` program `fzP` still a parameter.

**`maxFlowMachine_of_fix_fz`**: `FixHypF fixP …` and `FzHypF fzP …` (both for the call program
`msspCall' msEnc`), `noEmit` of `fixP` and `fzP`, and polynomial bounds on the zero areas and
rooms give `MaxFlowMachine'`.
-/

@[expose] public section

namespace PlanarFlow

namespace BKMNW

namespace Pp

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv NcStep

theorem c2sP_noEmit {fzP : Stmt} (h : Stmt.noEmit fzP = true) :
    Stmt.noEmit (c2sP fzP pbP) = true := by
  simp only [c2sP, c2cP, c2tP, Stmt.noEmit, h, pbP_noEmit, Bool.true_and]
  decide +kernel

theorem s2cP_noEmit {fzP : Stmt} (h : Stmt.noEmit fzP = true) :
    Stmt.noEmit (s2cP fzP pbP) = true := by
  simp only [s2cP, c2cP, c2tP, Stmt.noEmit, h, pbP_noEmit, Bool.true_and]
  decide +kernel

/-- **The maximum flow from the fix program and the `fixFrozen` program.** With the MSSP encoder
`MsEnc.msEnc` and the push-back program `pbP`, a fix program `fixP` meeting `FixHypF` and a
`fixFrozen` program `fzP` meeting `FzHypF` (both for `msspCall' msEnc`, scratch
`EScr ∨ msScr`), emitting nothing, with polynomial zero areas and rooms, give one program for
`MaxFlowMachine'`. -/
theorem maxFlowMachine_of_fix_fz {fixP fzP : Stmt} {C C₀ : ℕ} (hC : 3200000 ≤ C)
    {wzF rF wzz rFz : ℕ → ℕ → ℕ} {a p r q : ℕ}
    (hfix : FixHypF fixP (MsCall.msspCall' MsEnc.msEnc)
      (fun x => MsEnc.EScr x ∨ MsCall.msScr x) MsEnc.Rm MsEnc.wzm C C₀ wzF rF)
    (hfz : FzHypF fzP (MsCall.msspCall' MsEnc.msEnc)
      (fun x => MsEnc.EScr x ∨ MsCall.msScr x) MsEnc.Rm MsEnc.wzm C C₀ wzz rFz)
    (hE3 : Stmt.noEmit fixP = true) (hEz : Stmt.noEmit fzP = true)
    (hwz : ∀ m Z, wzF m Z + (wzc m Z + wzz m Z) + (wzc m Z + wzz m Z) ≤ a * (m + Z + 1) ^ p)
    (hr : ∀ N Z, rF N Z + c2sRC rFz N Z + c2sRC rFz N Z ≤ r * (N + Z + 1) ^ q) :
    MaxFlowMachine' :=
  maxFlowMachine_final hC (fun M => MsEnc.msEnc_spec (M := M)) hfix
    (c2sHypF_of_fz hfz (by omega)) (s2cHypF_of_fz hfz (by omega)) hE3 (c2sP_noEmit hEz)
    (s2cP_noEmit hEz) hwz hr

end Pp

end BKMNW

end PlanarFlow
