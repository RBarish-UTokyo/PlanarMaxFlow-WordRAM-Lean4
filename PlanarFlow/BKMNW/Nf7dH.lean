module

public import PlanarFlow.BKMNW.Nf7dG

/-!
# `fixP7 = kTst ; if 0 < k then fixPos else fixZero`

* **`fixP7_branch`**: the run of `fixP7 msP` from runs of the two branches from any configuration
  that `kTst` may leave (memory, reals, output and the registers outside `9437 … 9439` as before);
  (`t + 9` steps for a branch run of `t` steps).
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
  WordRAM WordRAM.Machine WordRAM.Programs

/-- **`fixP7` from its two branches.** -/
theorem fixP7_branch {I : Input} {W : ℕ} (msP : Stmt) (c : Config) (hc : WordsBounded W c)
    {Gb j ns k : ℕ} (r07 : c.nreg 6807 = Gb) (r00 : c.nreg 6800 = j) (hns : c.nmem Gb = ns)
    (hk : c.nmem (Gb + 1 + j + ns) = k) (hW : Gb + 1 + j + ns ≤ W) (Q : Config → ℕ → Prop)
    (hpos : 0 < k → ∀ c₁ : Config, WordsBounded W c₁ → c₁.nmem = c.nmem →
      (∀ r, (r < 9437 ∨ 9439 < r) → c₁.nreg r = c.nreg r) → c₁.rreg = c.rreg →
      c₁.rmem = c.rmem → c₁.output = c.output → ∃ c' t, Exec I W (fixPos msP) c₁ c' t ∧ Q c' t)
    (hzero : k = 0 → ∀ c₁ : Config, WordsBounded W c₁ → c₁.nmem = c.nmem →
      (∀ r, (r < 9437 ∨ 9439 < r) → c₁.nreg r = c.nreg r) → c₁.rreg = c.rreg →
      c₁.rmem = c.rmem → c₁.output = c.output → ∃ c' t, Exec I W fixZero c₁ c' t ∧ Q c' t) :
    ∃ c' t s, Exec I W (fixP7 msP) c c' s ∧ s ≤ t + 9 ∧ Q c' t := by
  obtain ⟨c₁, t₁, e₁, ht₁, a37, a38, ak, am, ar, arm, ao⟩ :=
    kTst_exec (P := I) c hc r07 r00 hns hk hW
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · obtain ⟨c', t, e, hQ⟩ := hzero h0 c₁ e₁.wb_right am ak ar arm ao
    exact ⟨c', t, _, e₁.seq (.ifLtN_false (by clear * - a37 a38 h0; omega) e),
      by clear * - ht₁; omega, hQ⟩
  · obtain ⟨c', t, e, hQ⟩ := hpos h0 c₁ e₁.wb_right am ak ar arm ao
    exact ⟨c', t, _, e₁.seq (.ifLtN_true (by clear * - a37 a38 h0; omega) e),
      by clear * - ht₁; omega, hQ⟩

end BKMNW

end PlanarFlow
