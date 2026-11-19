module

public import PlanarFlow.BKMNW.Nf9bO
public import PlanarFlow.BKMNW.Nf9aF
public import PlanarFlow.BKMNW.Nf9aE

/-!
# The maximum flow, unconditionally: the frozen fix in `maxFlowMachine_of_frame`

This module imports `Nf9bO` and the files below it.

* **`F9b.wzF9_wzm_le`**: `wzF9 MsEnc.wzm m Z ≤ 10 ^ 42 * (m + Z + 1) ^ 33`;
* **`F9b.rOF9_Rm_le`**: `rOF9 3200000 C₀ MsEnc.Rm m Z ≤ 10 ^ 42 * (m + Z + 1) ^ 33`
  (the envelopes are `rfl`-equal to the copies `P9.wzF9c`, `P9.rOF9c`, `Nf9aF`);
* **`Pp.maxFlowMachine'_holds : MaxFlowMachine'`**: `Pp.maxFlowMachine_of_frame` with
  `F9b.fixFrame_spec`, `F9b.fxT9_le_fixRun`, `F9b.fixC_noEmit` and the two bounds (`C₀ = 0`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace F9b

/-- **The zero area of the frozen fix for the MSSP encoder.** -/
theorem wzF9_wzm_le (m Z : ℕ) : wzF9 MsEnc.wzm m Z ≤ 10 ^ 42 * (m + Z + 1) ^ 33 :=
  P9.wzF9c_wzm_le m Z

/-- **The room of the frozen fix for the MSSP encoder.** -/
theorem rOF9_Rm_le (C₀ m Z : ℕ) : rOF9 3200000 C₀ MsEnc.Rm m Z ≤ 10 ^ 42 * (m + Z + 1) ^ 33 :=
  P9.rOF9c_Rm_le C₀ m Z

end F9b

namespace Pp

/-- **The maximum-flow machine exists** (no hypotheses). -/
theorem maxFlowMachine'_holds : MaxFlowMachine' :=
  maxFlowMachine_of_frame (C₀ := 0) (fun h => F9b.fixFrame_spec (by norm_num) h)
    (F9b.fxT9_le_fixRun (by norm_num)) (F9b.fixC_noEmit msspCall'_msEnc_noEmit)
    (fun m Z => F9b.wzF9_wzm_le m Z) (fun m Z => F9b.rOF9_Rm_le 0 m Z)

end Pp

end BKMNW

end PlanarFlow
