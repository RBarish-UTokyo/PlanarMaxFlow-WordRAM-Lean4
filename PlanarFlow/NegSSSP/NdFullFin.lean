module

public import PlanarFlow.NegSSSP.NdFullPrep2

/-!
# The full branch: the last part of the preparation

* **`fbK`**: `r2267 := h + 138k` (the base of the gather index `J` of `fbJ`, read by `fbC1`;
  `fbJ_exec` does not export it).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- `r2267 := r3003 + 138 · r2475` (scratch `2296`, `2297`). -/
def fbK : Stmt := block [.constN 2297 138, .mulN 2296 2297 2475, .addN 2267 3003 2296]

theorem fbK_natOnly : Klein.natOnly fbK = true := by decide

theorem fbK_exec (c : Config) (hc : WordsBounded W c) {h k : ℕ} (r03 : c.nreg 3003 = h)
    (r75 : c.nreg 2475 = k) (hW : h + 138 * k ≤ W) (h138 : 138 ≤ W) :
    ∃ c' t, Exec P W fbK c c' t ∧ t = 3 ∧ c'.nreg 2267 = h + 138 * k ∧
      (∀ r, r ≠ 2267 → r ≠ 2296 → r ≠ 2297 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fbK
  exec_block
  all_goals try ((try config_simp); (try simp only [r03, r75]); omega)
  refine ⟨rfl, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [r03, r75]
  all_goals try (simp (disch := omega) only [upd_other])
  all_goals try ring

end NegSSSP

end PlanarFlow
