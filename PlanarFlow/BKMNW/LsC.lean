module

public import PlanarFlow.BKMNW.LsS
public import PlanarFlow.BKMNW.LsP

/-!
# `sepL`: the register blocks between the stages

Bases above `U` (`n` darts of the record, `k` holes): `Y = U` (stage 6, `NF` at `U + n + k + 1`),
`Yb = U + 2 n + k + 1` (`lgPF`: `VK` at `Yb`, `DF` at `Yb + 2 n + 1`, `VF` at `Yb + 3 n + 2`),
`Z = U + 10 n + k + 3` (stage 7: hole flags at `Z + n + 1`, `LF` at `Z + 34 n + 8 k + 11`),
`CCb = U + 45 n + 9 k + 15` (the core's flags), `Z' = U + 46 n + 9 k + 15` (`sgProg`'s scratch).

* `lsC` (`3111 = U`; `8582 = Yb`, `8584 = Z`, `8585 = CCb`, `8586 = Z'`: **`LsL`**), `lsCC`
  (the core's flags: zero table, marks of `IX'`), `lsD` (`lgPF`), `lsE` (`s7`), `lsF` (`lrecT`),
  `lsH` (`s7O1 ; s7G` again after `lrecT`), `lsG` (`sgProg`), `lsS0` (no parts), with exec
  lemmas.
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

/-- The bases of stages 6–8. -/
def lsC : Stmt := block [.copyN 3111 8556, .constN 8564 2, .mulN 8582 8564 8553,
  .addN 8582 8582 8556, .addN 8582 8582 8551, .constN 8564 1, .addN 8582 8582 8564,
  .constN 8564 8, .mulN 8584 8564 8553, .addN 8584 8584 8582, .constN 8564 2,
  .addN 8584 8584 8564, .constN 8564 35, .mulN 8585 8564 8553, .addN 8585 8585 8584,
  .constN 8564 8, .mulN 8586 8564 8551, .addN 8585 8585 8586, .constN 8564 12,
  .addN 8585 8585 8564, .addN 8586 8585 8553]

/-- **The bases of stages 6–8** (registers `8582`, `8584 … 8586`). -/
structure LsL (c : Config) (n k U : ℕ) : Prop where
  r82 : c.nreg 8582 = U + 2 * n + k + 1
  r84 : c.nreg 8584 = U + 10 * n + k + 3
  r85 : c.nreg 8585 = U + 45 * n + 9 * k + 15
  r86 : c.nreg 8586 = U + 46 * n + 9 * k + 15

lemma LsL.congr {c c' : Config} {n k U : ℕ} (h : LsL c n k U)
    (he : ∀ x, (x = 8582 ∨ (8584 ≤ x ∧ x ≤ 8586)) → c'.nreg x = c.nreg x) : LsL c' n k U :=
  ⟨by rw [he _ (by omega)]; exact h.r82, by rw [he _ (by omega)]; exact h.r84,
    by rw [he _ (by omega)]; exact h.r85, by rw [he _ (by omega)]; exact h.r86⟩

/-- The core's flags: `CC[i] = [i ∈ IX'[0 … #B)]` at `CCb`. -/
def lsCC : Stmt := .seq (block [.constN 6521 1]) (.seq (zfill 8553 8585)
  (.seq (block [.copyN 6030 8558, .copyN 6031 8555, .copyN 6032 8585]) pfMk))

/-- The registers of `lgPF`. -/
def lsD : Stmt := block [.copyN 6000 8553, .copyN 6017 8557, .constN 8564 3,
  .addN 6001 8552 8564, .addN 6001 6001 8553, .copyN 6002 8555, .copyN 6003 8571,
  .copyN 6011 8582, .constN 8564 4, .mulN 6012 8564 8553, .addN 6012 6012 8552,
  .constN 8564 3, .addN 6012 6012 8564]

/-- The registers of `s7`. -/
def lsE : Stmt := block [.copyN 7100 8553, .constN 8564 1, .addN 7105 8551 8564,
  .copyN 7199 8584, .copyN 7193 8554, .copyN 7130 8550, .constN 6521 1, .constN 8564 3,
  .addN 8587 8552 8564, .addN 7106 8587 8553, .addN 7101 7106 8553, .constN 8564 3,
  .mulN 8588 8564 8553, .addN 8588 8588 8582, .constN 8564 2, .addN 7102 8588 8564,
  .copyN 7109 8582, .addN 7142 8556 8553, .addN 7142 7142 8551, .constN 8564 1,
  .addN 7142 7142 8564, .copyN 7143 8560, .copyN 7153 8561, .constN 8564 6,
  .mulN 8588 8564 8553, .addN 7131 8587 8588, .constN 8564 2, .mulN 8588 8564 8553,
  .addN 7132 8588 8582, .constN 8564 1, .addN 7132 7132 8564]

/-- The registers of `lrecT`. -/
def lsF : Stmt := block [.constN 8564 34, .mulN 8588 8564 8553, .addN 8500 8588 8584,
  .constN 8564 8, .mulN 8588 8564 8551, .addN 8500 8500 8588, .constN 8564 11,
  .addN 8500 8500 8564, .constN 8564 3, .mulN 8588 8564 8553, .addN 8501 8588 8582,
  .constN 8564 2, .addN 8501 8501 8564, .addN 8502 8584 8553, .constN 8564 1,
  .addN 8502 8502 8564, .constN 8564 2, .mulN 8588 8564 8553, .addN 8503 8588 8582,
  .constN 8564 1, .addN 8503 8503 8564, .copyN 8504 8585, .copyN 8505 8559, .copyN 6500 8554]

/-- The registers of `s7O1 ; s7G` (run again after `lrecT`). -/
def lsH : Stmt := block [.copyN 7130 8550, .constN 8564 3, .addN 8587 8552 8564,
  .constN 8564 6, .mulN 8588 8564 8553, .addN 7131 8587 8588, .constN 8564 33,
  .mulN 8588 8564 8553, .addN 7186 8588 8584, .constN 8564 8, .mulN 8588 8564 8551,
  .addN 7186 7186 8588, .constN 8564 11, .addN 7186 7186 8564, .copyN 7100 8553,
  .copyN 7193 8554, .constN 8564 2, .mulN 8588 8564 8553, .addN 7132 8588 8582,
  .constN 8564 1, .addN 7132 7132 8564, .constN 8564 3, .mulN 8588 8564 8553,
  .addN 7102 8588 8582, .constN 8564 2, .addN 7102 7102 8564, .addN 7133 8554 8550,
  .addN 7134 7133 8550, .copyN 7135 8551, .addN 7136 8584 8553, .constN 8564 1,
  .addN 7136 7136 8564, .addN 7137 7134 8550]

/-- The registers of `sgProg`. -/
def lsG : Stmt := block [.copyN 7200 8557, .copyN 7201 8571, .copyN 7202 8555,
  .constN 8564 3, .addN 8587 8552 8564, .constN 8564 2, .mulN 8588 8564 8553,
  .addN 7203 8587 8588, .copyN 7204 8550, .constN 8564 6, .mulN 8588 8564 8553,
  .addN 7205 8587 8588, .copyN 7206 8586, .addN 7207 8571 8553, .copyN 7208 8553,
  .constN 6521 1]

/-- No parts (an empty piece map): `mem Gb := 0`, `6502 := Gb`. -/
def lsS0 : Stmt := block [.constN 8564 0, .storeN 7207 8564, .copyN 6502 7207]

/-- The parts: `sgProg` if the piece map is nonempty. -/
def lsSg : Stmt := .ifLtN 8568 8550 sgProg lsS0

section Exec

variable {I : Input} {W : ℕ}

theorem lsC_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb U : ℕ}
    (hR : LsR c m k R n Sb) (hU : U = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3)
    (w : U + 46 * n + 9 * k + 15 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsC c c' t ∧ t = 21 ∧ LsL c' n k U ∧ c'.nreg 3111 = U ∧
      (∀ x, (x < 3111 ∨ (3111 < x ∧ x < 8564) ∨ (8564 < x ∧ x < 8582) ∨ 8586 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hR.r53; have := hR.r51; have := hR.r56
  subst hU
  unfold lsC
  exec_block
  all_goals try (config_simp; (try simp only [hR.r53, hR.r51, hR.r56]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_⟩, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, hR.r53, hR.r51, hR.r56])
    try omega

theorem lsD_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb U : ℕ}
    (hR : LsR c m k R n Sb) (hL : LsL c n k U) (wR : R + 3 + 5 * n ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsD c c' t ∧ t = 13 ∧ c'.nreg 6000 = n ∧ c'.nreg 6017 = c.nreg 8557 ∧
      c'.nreg 6001 = R + 3 + n ∧ c'.nreg 6002 = c.nreg 8555 ∧ c'.nreg 6003 = c.nreg 8571 ∧
      c'.nreg 6011 = U + 2 * n + k + 1 ∧ c'.nreg 6012 = R + 3 + 4 * n ∧
      (∀ x, (x < 6000 ∨ (6003 < x ∧ x < 6011) ∨ (6012 < x ∧ x < 6017) ∨ (6017 < x ∧ x < 8564) ∨
        8564 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hR.r53; have := hR.r52; have := hL.r82
  have := hc.1 8557; have := hc.1 8555; have := hc.1 8571
  unfold lsD
  exec_block
  all_goals try (config_simp; (try simp only [hR.r53, hR.r52, hL.r82]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, hR.r53, hR.r52, hL.r82])
    try omega

theorem lsE_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb U : ℕ}
    (hR : LsR c m k R n Sb) (hL : LsL c n k U) (hU : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 = U)
    (wR : R + 3 + 6 * n ≤ W) (w : U + 46 * n + 9 * k + 15 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsE c c' t ∧ t = 31 ∧ c'.nreg 7100 = n ∧ c'.nreg 7105 = k + 1 ∧
      c'.nreg 7199 = U + 10 * n + k + 3 ∧ c'.nreg 7193 = Sb ∧ c'.nreg 7130 = m ∧
      c'.nreg 6521 = 1 ∧ c'.nreg 7101 = R + 3 + 2 * n ∧ c'.nreg 7102 = U + 5 * n + k + 3 ∧
      c'.nreg 7106 = R + 3 + n ∧ c'.nreg 7109 = U + 2 * n + k + 1 ∧
      c'.nreg 7142 = U + n + k + 1 ∧ c'.nreg 7143 = c.nreg 8560 ∧ c'.nreg 7153 = c.nreg 8561 ∧
      c'.nreg 7131 = R + 3 + 6 * n ∧ c'.nreg 7132 = U + 4 * n + k + 2 ∧
      (∀ x, (x < 6521 ∨ (6521 < x ∧ x < 7100) ∨ (7199 < x ∧ x < 8564) ∨ (8564 < x ∧ x < 8587) ∨
        8588 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hR.r50; have := hR.r51; have := hR.r52; have := hR.r53; have := hR.r54
  have := hR.r56; have := hL.r82; have := hL.r84
  have := hc.1 8560; have := hc.1 8561
  unfold lsE
  exec_block
  all_goals try (config_simp; (try simp only [hR.r50, hR.r51, hR.r52, hR.r53, hR.r54, hR.r56, hL.r82, hL.r84]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl,
    rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, hR.r50, hR.r51, hR.r52, hR.r53,
      hR.r54, hR.r56, hL.r82, hL.r84])
    try omega

theorem lsF_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb U : ℕ}
    (hR : LsR c m k R n Sb) (hL : LsL c n k U) (w : U + 46 * n + 9 * k + 15 ≤ W)
    (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsF c c' t ∧ t = 24 ∧ c'.nreg 8500 = U + 44 * n + 9 * k + 14 ∧
      c'.nreg 8501 = U + 5 * n + k + 3 ∧ c'.nreg 8502 = U + 11 * n + k + 4 ∧
      c'.nreg 8503 = U + 4 * n + k + 2 ∧ c'.nreg 8504 = U + 45 * n + 9 * k + 15 ∧
      c'.nreg 8505 = c.nreg 8559 ∧ c'.nreg 6500 = Sb ∧
      (∀ x, (x < 6500 ∨ (6500 < x ∧ x < 8500) ∨ (8505 < x ∧ x < 8564) ∨ (8564 < x ∧ x < 8588) ∨
        8588 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hR.r51; have := hR.r53; have := hR.r54; have := hL.r82; have := hL.r84; have := hL.r85
  have := hc.1 8559
  unfold lsF
  exec_block
  all_goals try (config_simp; (try simp only [hR.r51, hR.r53, hR.r54, hL.r82, hL.r84, hL.r85]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, hR.r51, hR.r53, hR.r54, hL.r82,
      hL.r84, hL.r85])
    try omega

theorem lsH_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb U : ℕ}
    (hR : LsR c m k R n Sb) (hL : LsL c n k U) (hU : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 = U)
    (wR : R + 3 + 6 * n ≤ W) (w : U + 46 * n + 9 * k + 15 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsH c c' t ∧ t = 33 ∧ c'.nreg 7130 = m ∧ c'.nreg 7131 = R + 3 + 6 * n ∧
      c'.nreg 7186 = U + 43 * n + 9 * k + 14 ∧ c'.nreg 7100 = n ∧ c'.nreg 7193 = Sb ∧
      c'.nreg 7132 = U + 4 * n + k + 2 ∧ c'.nreg 7102 = U + 5 * n + k + 3 ∧
      c'.nreg 7133 = Sb + m ∧ c'.nreg 7134 = Sb + 2 * m ∧ c'.nreg 7135 = k ∧
      c'.nreg 7136 = U + 11 * n + k + 4 ∧ c'.nreg 7137 = Sb + 3 * m ∧
      (∀ x, (x < 7100 ∨ (7199 < x ∧ x < 8564) ∨ (8564 < x ∧ x < 8587) ∨ 8588 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hR.r50; have := hR.r51; have := hR.r52; have := hR.r53; have := hR.r54
  have := hL.r82; have := hL.r84
  unfold lsH
  exec_block
  all_goals try (config_simp; (try simp only [hR.r50, hR.r51, hR.r52, hR.r53, hR.r54, hL.r82, hL.r84]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, hR.r50, hR.r51, hR.r52, hR.r53,
      hR.r54, hL.r82, hL.r84])
    try omega

theorem lsG_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb U : ℕ}
    (hR : LsR c m k R n Sb) (hL : LsL c n k U)
    (r71 : c.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n)
    (wR : R + 3 + 6 * n ≤ W) (w : Sb + 21 * m + 38 * n + 8 * k + 24 + 2 * n ≤ W)
    (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsG c c' t ∧ t = 16 ∧ c'.nreg 7200 = c.nreg 8557 ∧
      c'.nreg 7201 = Sb + 21 * m + 38 * n + 8 * k + 24 + n ∧
      c'.nreg 7202 = Sb + 21 * m + 38 * n + 8 * k + 24 ∧ c'.nreg 7203 = R + 3 + 2 * n ∧
      c'.nreg 7204 = m ∧ c'.nreg 7205 = R + 3 + 6 * n ∧ c'.nreg 7206 = U + 46 * n + 9 * k + 15 ∧
      c'.nreg 7207 = Sb + 21 * m + 38 * n + 8 * k + 24 + 2 * n ∧ c'.nreg 7208 = n ∧
      c'.nreg 6521 = 1 ∧
      (∀ x, (x < 6521 ∨ (6521 < x ∧ x < 7200) ∨ (7208 < x ∧ x < 8564) ∨ (8564 < x ∧ x < 8587) ∨
        8588 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hR.r50; have := hR.r52; have := hR.r53; have := hR.r55; have := hL.r86
  have := hc.1 8557; have := hc.1 8586
  unfold lsG
  exec_block
  all_goals try (config_simp; (try simp only [hR.r50, hR.r52, hR.r53, hR.r55, hL.r86, r71]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, hR.r50, hR.r52, hR.r53, hR.r55,
      hL.r86, r71])
    try omega

theorem lsS0_exec (c : Config) (hc : WordsBounded W c) {Gb : ℕ} (r07 : c.nreg 7207 = Gb)
    (w : Gb ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsS0 c c' t ∧ t = 3 ∧ c'.nmem = upd c.nmem Gb 0 ∧ c'.nreg 6502 = Gb ∧
      (∀ x, x ≠ 8564 → x ≠ 6502 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lsS0
  exec_block
  all_goals try (config_simp; (try simp only [r07]); omega)
  refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r07])

end Exec

end MfDrv

end BKMNW

end PlanarFlow
