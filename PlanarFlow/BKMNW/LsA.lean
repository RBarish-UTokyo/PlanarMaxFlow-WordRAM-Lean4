module

public import PlanarFlow.BKMNW.LsW
public import PlanarFlow.BKMNW.LrV
public import PlanarFlow.BKMNW.SgRun

/-!
# `sepL`: the set-up block and its registers

`sepL` starts from `3004 = d` (the frame), `6500 = Sb` (the output base). The set-up block
`lsA` reads `m = mem d`, `k = mem (d + 1)`, `R = mem (d + 7 m + 4)` (the record), `n = mem R`,
and keeps them in registers above `8540` (kept by every stage of `sepL`, `lrecT` included):

| register | value |
| --- | --- |
| `8550 … 8554` | `m`, `k`, `R`, `n`, `Sb` |
| `8555` | `E = Sb + 21 m + 38 n + 8 k + 24` (the end of `lrecT`'s area; `IX'` at `E`) |
| `8556` | `U = E + 4 n + 3` (the scratch of stages 5–8) |
| `8568` | `0` |

Layout above `Sb`: outputs and records in `[Sb, E)`, the path's core indices `IX'` at `E`, its
darts `PD'` at `E + n`, the parts (`SegsOut'`) at `Gb = E + 2 n`, scratch from `U`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

/-- **The set-up of `sepL`** (see the module docstring); also `3100 = R`, `3101 = U`,
`3102 = k` for stage 5. -/
def lsA : Stmt := block [.copyN 8554 6500, .loadN 8550 3004, .constN 8562 1,
  .addN 8563 3004 8562, .loadN 8551 8563, .constN 8564 7, .mulN 8565 8564 8550,
  .addN 8565 8565 3004, .constN 8564 4, .addN 8565 8565 8564, .loadN 8552 8565,
  .loadN 8553 8552, .constN 8564 21, .mulN 8566 8564 8550, .constN 8564 38,
  .mulN 8567 8564 8553, .addN 8566 8566 8567, .constN 8564 8, .mulN 8567 8564 8551,
  .addN 8566 8566 8567, .constN 8564 24, .addN 8566 8566 8564, .addN 8555 8566 8554,
  .constN 8564 4, .mulN 8567 8564 8553, .addN 8567 8567 8555, .constN 8564 3,
  .addN 8556 8567 8564, .copyN 3100 8552, .copyN 3101 8556, .copyN 3102 8551, .constN 8568 0]

/-- **The registers of `sepL`** (kept through all its stages). -/
structure LsR (c : Config) (m k R n Sb : ℕ) : Prop where
  r50 : c.nreg 8550 = m
  r51 : c.nreg 8551 = k
  r52 : c.nreg 8552 = R
  r53 : c.nreg 8553 = n
  r54 : c.nreg 8554 = Sb
  r55 : c.nreg 8555 = Sb + 21 * m + 38 * n + 8 * k + 24
  r56 : c.nreg 8556 = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3
  r68 : c.nreg 8568 = 0

lemma LsR.congr {c c' : Config} {m k R n Sb : ℕ} (h : LsR c m k R n Sb)
    (he : ∀ x, ((8550 ≤ x ∧ x ≤ 8556) ∨ x = 8568) → c'.nreg x = c.nreg x) : LsR c' m k R n Sb :=
  ⟨by rw [he _ (by omega)]; exact h.r50, by rw [he _ (by omega)]; exact h.r51,
    by rw [he _ (by omega)]; exact h.r52, by rw [he _ (by omega)]; exact h.r53,
    by rw [he _ (by omega)]; exact h.r54, by rw [he _ (by omega)]; exact h.r55,
    by rw [he _ (by omega)]; exact h.r56, by rw [he _ (by omega)]; exact h.r68⟩

section Exec

variable {I : Input} {W : ℕ}

theorem lsA_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb : ℕ}
    (r4 : c.nreg 3004 = d) (r50 : c.nreg 6500 = Sb) (hm : c.nmem d = m)
    (hk : c.nmem (d + 1) = k) (hR : c.nmem (d + 7 * m + 4) = R) (hn : c.nmem R = n)
    (w0 : d + 7 * m + 4 ≤ W) (w : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 ≤ W)
    (wR : R ≤ W) (w2 : 40 ≤ W) :
    ∃ c' t, Exec I W lsA c c' t ∧ t = 32 ∧ LsR c' m k R n Sb ∧ c'.nreg 3100 = R ∧
      c'.nreg 3101 = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 ∧ c'.nreg 3102 = k ∧
      (∀ x, (x < 3100 ∨ (3102 < x ∧ x < 8550)) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e1 : d + 7 * m + 4 = 7 * m + d + 4 := by omega
  rw [e1] at hR
  unfold lsA
  exec_block
  all_goals try (config_simp; (try simp only [r4, r50, hm, hk, hR, hn]); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r4, r50, hm, hk, hR, hn]; omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r4, r50, hm, hk, hR, hn])
    try omega

end Exec

end MfDrv

end BKMNW

end PlanarFlow
