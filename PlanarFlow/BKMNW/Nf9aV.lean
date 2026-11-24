module

public import PlanarFlow.BKMNW.Nf9aH
public import PlanarFlow.BKMNW.ThPipeV
public import PlanarFlow.BKMNW.NfWord

/-!
# The maximum-flow machine with valid output indices

**`Pp.maxFlowMachine_holds : MaxFlowMachine`** (no hypotheses): `Nf9aH.lean`'s proof of
`MaxFlowMachine'`, for the program of `ThPipeV.lean`, with the stronger conclusion
`MaxFlowMachine` of `PlanarFlow/SpecMaxFlow.lean` (every printed index `p[x]`, `x < n`, lies in
`q`, and the program is a word program: the subroutine programs have no real instruction,
`NfWord.lean`).

* `Pp.maxFlowMachine_finalV`: `Pp.maxFlowMachine_final'` (`Nf7dJ.lean`) through
  `Pp.maxFlowMachineV_of_spec`;
* `Pp.maxFlowMachine_of_frameV`: `Pp.maxFlowMachine_of_frame` (`Nf9aE.lean`) through
  `Pp.maxFlowMachine_finalV`;
* **`Pp.maxFlowMachine_holds`**: `Pp.maxFlowMachine'_holds` (`Nf9aH.lean`) through
  `Pp.maxFlowMachine_of_frameV`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver MfDrv
  PlanarSeparator.StDart NcStep

/-- **The maximum-flow theorem from one hypothesis per remaining program, with valid output
indices**: `maxFlowMachine_final'` for the program of `ThPipeV.lean`, concluding
`MaxFlowMachine`. -/
theorem maxFlowMachine_finalV {fixP c2sP s2cP msEnc : Stmt} {C C₀ : ℕ} (hC : 3200000 ≤ C)
    {cost : ℕ → ℕ → ℕ → ℕ}
    {EScr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    {wzF wzC wzS rF rC rS : ℕ → ℕ → ℕ} {a p r q : ℕ}
    (hE : ∀ {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
      [DecidableEq F] (M : CombMap D V F), MsCall.MsEncSpec' M msEnc EScr MsEnc.msEncCost
        (fun m k _ => MsEnc.KCf m k) (fun m _ _ => MsEnc.ZCf m) Rm wzm)
    (hMSc : ∀ {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
      [DecidableEq F] (M : CombMap D V F), MsCall.MsspCallSpec M (MsCall.msspCall' msEnc)
        (fun x => EScr x ∨ MsCall.msScr x) cost Rm wzm)
    (hcost : ∀ m k q, 1 ≤ m → q ≤ 2 * k →
      cost m k q + 200 * k ^ 2 + 2000 * k + 2000 ≤ (cMachS C C₀).mssp m k)
    (hEScr : ∀ r, EScr r → r < 9300)
    (hfix : FixHypF' fixP (MsCall.msspCall' msEnc) (fun x => EScr x ∨ MsCall.msScr x) cost Rm wzm
      C C₀ wzF rF)
    (hc2s : C2SHypF c2sP (MsCall.msspCall' msEnc) (fun x => EScr x ∨ MsCall.msScr x) Rm wzm C C₀
      wzC rC)
    (hs2c : S2CHypF s2cP (MsCall.msspCall' msEnc) (fun x => EScr x ∨ MsCall.msScr x) Rm wzm C C₀
      wzS rS)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true)
    (hN3 : Klein.natOnly fixP = true) (hN4 : Klein.natOnly c2sP = true)
    (hN5 : Klein.natOnly s2cP = true)
    (hwz : ∀ m Z, wzF m Z + wzC m Z + wzS m Z ≤ a * (m + Z + 1) ^ p)
    (hr : ∀ N Z, rF N Z + rC N Z + rS N Z ≤ r * (N + Z + 1) ^ q) :
    MaxFlowMachine :=
  maxFlowMachineV_of_spec
    (mfMainSpecS''_final' hC (fun M' => MsEnc.msspCall'_cMachS C C₀ (hE M')) hMSc hcost
      (fun r hr => hr.elim (hEScr r) (fun h => by unfold MsCall.msScr at h; omega)) hfix hc2s hs2c
      hwz hr)
    (by omega) sepL_noEmit sepX_noEmit hE3 hE4 hE5 sepL_natOnly sepX_natOnly hN3 hN4 hN5
    (rowR_mono r q) (rowR_le r q) (fun N Z => le_rfl)


/-- **The maximum flow from a frame-level frozen-fix program, with valid output indices**:
`maxFlowMachine_of_frame` concluding `MaxFlowMachine`. -/
theorem maxFlowMachine_of_frameV {fixC : Stmt} {C₀ : ℕ} {fxT : ℕ → ℕ → ℕ → ℕ}
    {fxR wzf : ℕ → ℕ → ℕ} {a p r q : ℕ}
    (hFF : (∀ x, (MsEnc.EScr x ∨ MsCall.msScr x) → x < 9300) →
      NcFz.FixFrameSpec fixC (MsCall.msspCall' MsEnc.msEnc)
        (fun x => MsEnc.EScr x ∨ MsCall.msScr x) MsEnc.Rm MsEnc.wzm 3200000 C₀ fxT fxR wzf)
    (hT : ∀ m xf k L, 1 ≤ m → m ≤ L →
      NcFz.pfT m + 3 + fxT m xf k + (24 * m + 40) ≤ (cMachS 3200000 C₀).fixRun m xf k (3 * L))
    (hE : Stmt.noEmit fixC = true) (hN : Klein.natOnly fixC = true)
    (hwz : ∀ m Z, wzf m Z ≤ a * (m + Z + 1) ^ p)
    (hr : ∀ m Z, fxR m Z ≤ r * (m + Z + 1) ^ q) :
    MaxFlowMachine := by
  have hF := hFF fun x hx => escr_lt hx
  exact maxFlowMachine_finalV (C := 3200000) (C₀ := C₀) le_rfl
    (cost := MsCall.msCost' MsEnc.msEncCost (fun m k _ => MsEnc.KCf m k)
      (fun m _ _ => MsEnc.ZCf m))
    (a := 10 ^ 65 + 6 * a) (p := 2 * p + 33) (r := 10 ^ 42 + 6 * r) (q := 2 * q + 33)
    (fun M => MsEnc.msEnc_spec) (fun M => MsCall.msspCall'_spec MsEnc.msEnc_spec)
    (fun m k q hm hq => MsEnc.msCost'_slack_cMachS 3200000 C₀ hm hq)
    (fun x hx => escr_lt (Or.inl hx))
    (fixHypF'_fixP7 (by norm_num) _ _ _ _ _)
    (NcFz.c2sHypF_of_frame hF hT (by norm_num))
    (NcFz.s2cHypF_of_frame hF hT (by norm_num))
    (fixP7_noEmit msspCall'_msEnc_noEmit) (c2sP_noEmit (fzP_noEmit hE))
    (s2cP_noEmit (fzP_noEmit hE))
    (fixP7_natOnly msspCall'_msEnc_natOnly) (c2sP_natOnly (fzP_natOnly hN))
    (s2cP_natOnly (fzP_natOnly hN))
    (fun m Z => wz_total_le hwz m Z) (fun N Z => r_total_le hr C₀ N Z)

/-- **The maximum-flow machine exists, with valid output indices** (no hypotheses). -/
theorem maxFlowMachine_holds : MaxFlowMachine :=
  maxFlowMachine_of_frameV (C₀ := 0) (fun h => F9b.fixFrame_spec (by norm_num) h)
    (F9b.fxT9_le_fixRun (by norm_num)) (F9b.fixC_noEmit msspCall'_msEnc_noEmit)
    (F9b.fixC_natOnly msspCall'_msEnc_natOnly)
    (fun m Z => F9b.wzF9_wzm_le m Z) (fun m Z => F9b.rOF9_Rm_le 0 m Z)

end Pp

end BKMNW

end PlanarFlow
