module

public import PlanarFlow.BKMNW.Nf7fE
public import PlanarFlow.BKMNW.Nf7eWH
public import PlanarFlow.BKMNW.Nf7eWI

/-!
# `FixHypF'` for `fixP7`, unconditionally

* **`fixPosW_holds`**, **`fixZeroW_holds`**: the propositions `FixPosW`, `FixZeroW` (`Nf7fC`)
  are the theorems `fixPos_execW` (`Nf7eWH`) and
  `fixZero_execW` (`Nf7eWI`), one line each;
* **`Pp.fixHypF'_fixP7`**: for `200000 ≤ C`, the program `fixP7 msP` meets
  `FixHypF' (fixP7 msP) msP Scr cost Rm wzm C C₀ (wzF7 wzm) (rF7 C C₀ Rm)` for every MSSP call
  program `msP`, scratch `Scr`, step bound `cost`, room `Rm` and zero area `wzm`
  (`fixHypF'_fixP7_of` with the two bridges).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine

universe w

/-- **`fixPos_execW` is `FixPosW`.** -/
theorem fixPosW_holds : FixPosW.{w} := by
  unfold FixPosW
  intro D V F _ _ _ _ _ _ M gid u S T Z x m en d
  exact fixPos_execW

/-- **`fixZero_execW` is `FixZeroW`.** -/
theorem fixZeroW_holds : FixZeroW.{w} := by
  unfold FixZeroW
  intro D V F _ _ _ _ _ _ M gid u S T Z x m en d
  exact fixZero_execW

namespace Pp

/-- **`fixP7` meets `FixHypF'`** (for `200000 ≤ C`; every `msP`, `Scr`, `cost`, `Rm`, `wzm`). -/
theorem fixHypF'_fixP7 {C C₀ : ℕ} (hC : 200000 ≤ C) (msP : Stmt) (Scr : ℕ → Prop)
    (cost Rm : ℕ → ℕ → ℕ → ℕ) (wzm : ℕ → ℕ → ℕ) :
    FixHypF' (fixP7 msP) msP Scr cost Rm wzm C C₀ (wzF7 wzm) (rF7 C C₀ Rm) :=
  fixHypF'_fixP7_of fixPosW_holds.{0} fixZeroW_holds.{0} hC

end Pp

end BKMNW

end PlanarFlow
