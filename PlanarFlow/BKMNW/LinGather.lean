module

public import PlanarFlow.BKMNW.LinLoops

/-!
# The gather with its arguments in registers

`ggProg a b c d` = `r6210 := ra; r6211 := rb; r6212 := rc; r6213 := rd; lgProg`: the gather
`OUT[j] := A[IX[j]]` (`j < m`) with `m`, `IXb`, `Ab`, `OUTb` read from the registers `a`, `b`,
`c`, `d` (outside `6210 … 6217`). **`ggProg_exec`** (`9 m + 8` steps): as `lgProg_exec`, the
registers outside `6210 … 6217` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- **The gather with its arguments in the registers `a`, `b`, `c`, `d`.** -/
def ggProg (a b c d : ℕ) : Stmt :=
  .seq (block [.copyN 6210 a, .copyN 6211 b, .copyN 6212 c, .copyN 6213 d]) lgProg

section Exec

variable {P : Input} {W : ℕ}

/-- **The gather with its arguments in registers**: within `9 m + 8` steps `OUT[j] = A[IX[j]]`
for `j < m`; memory outside `[OUTb, OUTb + m)`, registers outside `6210 … 6217`, reals and output
kept. -/
theorem ggProg_exec (c : Config) (hc : WordsBounded W c) {a b cc dd m IXb Ab OUTb : ℕ}
    (ha : a < 6210 ∨ 6217 < a) (hb : b < 6210 ∨ 6217 < b) (hcc : cc < 6210 ∨ 6217 < cc)
    (hdd : dd < 6210 ∨ 6217 < dd)
    (r0 : c.nreg a = m) (r1 : c.nreg b = IXb) (r2 : c.nreg cc = Ab) (r3 : c.nreg dd = OUTb)
    (w1 : IXb + m ≤ W) (w3 : OUTb + m ≤ W) (w4 : m + 1 ≤ W)
    (hIX : ∀ j < m, Ab + c.nmem (IXb + j) ≤ W)
    (d1 : ∀ j < m, ¬ (OUTb ≤ IXb + j ∧ IXb + j < OUTb + m))
    (d2 : ∀ j < m, ¬ (OUTb ≤ Ab + c.nmem (IXb + j) ∧ Ab + c.nmem (IXb + j) < OUTb + m)) :
    ∃ c' k, Exec P W (ggProg a b cc dd) c c' k ∧ k ≤ 9 * m + 8 ∧
      (∀ j < m, c'.nmem (OUTb + j) = c.nmem (Ab + c.nmem (IXb + j))) ∧
      (∀ x, ¬ (OUTb ≤ x ∧ x < OUTb + m) → c'.nmem x = c.nmem x) ∧
      (∀ x, (x < 6210 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, g3, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 6210 a, .copyN 6211 b, .copyN 6212 cc, .copyN 6213 dd]) c c₁ k₁ ∧
      k₁ = 4 ∧ c₁.nreg 6210 = m ∧ c₁.nreg 6211 = IXb ∧ c₁.nreg 6212 = Ab ∧ c₁.nreg 6213 = OUTb ∧
      (∀ x, (x < 6210 ∨ 6217 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same])
      try omega
  have hw₁ := e₁.wb_right
  rw [← gm₁] at hIX d2
  obtain ⟨c₂, k₂, e₂, hk₂, o1, o2, o3, o4, o5, o6⟩ := lgProg_exec (P := P) c₁ hw₁ g0 g1 g2 g3 w1
    w3 w4 hIX d1 d2
  rw [gm₁] at o1 o2
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, o1, o2, fun x hx => ?_, by rw [o4, gr₁],
    by rw [o5, grm₁], by rw [o6, go₁]⟩
  rw [o3 x (by omega), gn₁ x hx]

end Exec

end BKMNW

end PlanarFlow
