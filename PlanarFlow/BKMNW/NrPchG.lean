module

public import PlanarFlow.BKMNW.NrPchM

/-!
# The glue blocks of the push-back program `pchP`

Straight-line blocks (generated mechanically) setting the bases of the scratch arrays of
`pchP` (registers `9204 … 9231`, from `r3004 = d` and `r9200 = A`) and the input registers of its
subprograms (`dvP`, `decL`, `dvL`, `lgProg`, `cstL`, `olProg`, `cntL`, `osProg`, `nrPass`, `negL`,
`kahnP`, `pushP`), each with its `*_exec` lemma (the values of the written registers, all others
and the memory kept).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- Glue block `pG0a` of `pchP`. -/
def pG0a : Stmt :=
  block [.loadN 9204 3004, .constN 9230 3, .addN 9231 3004 9230, .loadN 9205 9231, .constN 9230 4, .addN 9206 3004 9230, .addN 9206 9206 9204, .addN 9207 9206 9204, .copyN 8430 9200]

/-- Glue block `pG0b` of `pchP`. -/
def pG0b : Stmt :=
  block [.addN 9208 9207 9204, .addN 9208 9208 9204, .addN 9208 9208 9204, .addN 9208 9208 9204, .addN 9210 9200 9204, .addN 9210 9210 9204, .addN 9210 9210 9204, .addN 9211 9210 9204, .addN 9212 9211 9204, .addN 9213 9212 9204]

/-- Glue block `pG0c` of `pchP`. -/
def pG0c : Stmt :=
  block [.addN 9214 9213 9204, .addN 9215 9214 9204, .addN 9216 9215 9204, .addN 9217 9216 9204, .addN 9218 9217 9204, .addN 9219 9218 9204, .addN 9220 9219 9204, .addN 9221 9220 9204, .addN 9222 9221 9204]

/-- Glue block `pG0d` of `pchP`. -/
def pG0d : Stmt :=
  block [.constN 9230 1, .addN 9223 9222 9204, .addN 9223 9223 9230, .addN 9224 9222 9204, .addN 9224 9224 9204, .addN 9224 9224 9204, .addN 9225 9224 9204]

/-- Glue block `pG1` of `pchP`. -/
def pG1 : Stmt :=
  block [.copyN 9241 9204, .copyN 9242 9200, .copyN 9243 9210]

/-- Glue block `pG2` of `pchP`. -/
def pG2 : Stmt :=
  block [.copyN 9261 9204, .addN 9262 9200 9204, .addN 9263 9262 9204, .copyN 9264 9211, .copyN 9265 9203, .copyN 9266 9205]

/-- Glue block `pG3` of `pchP`. -/
def pG3 : Stmt :=
  block [.copyN 6210 9204, .copyN 6211 9206, .copyN 6212 9207, .copyN 6213 9212]

/-- Glue block `pG4` of `pchP`. -/
def pG4 : Stmt :=
  block [.copyN 9251 9204, .copyN 9252 9213, .constN 9253 0]

/-- Glue block `pG5` of `pchP`. -/
def pG5 : Stmt :=
  block [.copyN 7350 9212, .copyN 7351 9213, .copyN 7352 9204]

/-- Glue block `pG6` of `pchP`. -/
def pG6 : Stmt :=
  block [.copyN 9241 9204, .copyN 9242 9213, .copyN 9243 9214]

/-- Glue block `pG7` of `pchP`. -/
def pG7 : Stmt :=
  block [.copyN 9272 9204, .copyN 9273 9214, .copyN 9274 9215]

/-- Glue block `pG8` of `pchP`. -/
def pG8 : Stmt :=
  block [.copyN 9226 9275, .copyN 6210 9204, .copyN 6211 9214, .copyN 6212 9215, .copyN 6213 9216]

/-- Glue block `pG9` of `pchP`. -/
def pG9 : Stmt :=
  block [.copyN 6210 9204, .copyN 6211 9206, .copyN 6212 9216, .copyN 6213 9217]

/-- Glue block `pG10` of `pchP`. -/
def pG10 : Stmt :=
  block [.copyN 9251 9204, .copyN 9252 9218, .constN 9253 1]

/-- Glue block `pG11` of `pchP`. -/
def pG11 : Stmt :=
  block [.copyN 1500 9204, .copyN 1501 9204, .copyN 1502 9210, .copyN 1504 9218, .copyN 1505 9222, .copyN 1506 9223, .copyN 1507 9219, .copyN 1508 9220, .copyN 1509 9221]

/-- Glue block `pG12` of `pchP`. -/
def pG12 : Stmt :=
  block [.copyN 9272 9204, .copyN 9273 9210, .copyN 9274 9224]

/-- Glue block `pG13a` of `pchP`. -/
def pG13a : Stmt :=
  block [.copyN 9227 9275, .copyN 9000 9204, .copyN 9001 9226, .copyN 9002 9208, .copyN 9003 9216, .copyN 9004 9217, .copyN 9005 9205, .copyN 9006 9225, .loadN 9007 9216]

/-- Glue block `pG13b` of `pchP`. -/
def pG13b : Stmt :=
  block [.mulN 9008 9204 9205, .constN 9230 1, .addN 9008 9008 9230]

/-- Glue block `pG14` of `pchP`. -/
def pG14 : Stmt :=
  block [.copyN 9281 9204, .copyN 9282 9208, .addN 9283 9205 9205]

/-- Glue block `pG15` of `pchP`. -/
def pG15 : Stmt :=
  block [.copyN 9100 9204, .copyN 9101 9210, .copyN 9102 9206, .copyN 9103 9208, .copyN 9104 9205, .copyN 9105 9225]

/-- Glue block `pG16a` of `pchP`. -/
def pG16a : Stmt :=
  block [.copyN 9151 9208, .copyN 9152 9206, .copyN 9153 9210, .copyN 9154 9205, .copyN 9155 9211, .copyN 9156 9201, .copyN 9157 9202, .addN 9158 9225 9204, .addN 9158 9158 9204]

/-- Glue block `pG16b` of `pchP`. -/
def pG16b : Stmt :=
  block [.copyN 9159 9227, .copyN 9160 9219, .copyN 9161 9220, .copyN 9162 9221]

section Exec

variable {P : Input} {W : ℕ}

theorem pG0a_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 3004 ≤ W) (w1 : 3 ≤ W) (w2 : c.nreg 3004 + 3 ≤ W) (w3 : (c.nreg 3004 + 3) ≤ W) (w4 : 4 ≤ W) (w5 : c.nreg 3004 + 4 ≤ W) (w6 : (c.nreg 3004 + 4) + c.nmem (c.nreg 3004) ≤ W) (w7 : ((c.nreg 3004 + 4) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004) ≤ W) :
    ∃ c' t, Exec P W pG0a c c' t ∧ t = 9 ∧ c'.nreg 8430 = c.nreg 9200 ∧ c'.nreg 9204 = c.nmem (c.nreg 3004) ∧ c'.nreg 9205 = c.nmem ((c.nreg 3004 + 3)) ∧ c'.nreg 9206 = (c.nreg 3004 + 4) + c.nmem (c.nreg 3004) ∧ c'.nreg 9207 = ((c.nreg 3004 + 4) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004) ∧ c'.nreg 9230 = 4 ∧ c'.nreg 9231 = c.nreg 3004 + 3 ∧
      (∀ x, x ≠ 8430 → x ≠ 9204 → x ≠ 9205 → x ≠ 9206 → x ≠ 9207 → x ≠ 9230 → x ≠ 9231 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG0a
  exec_block
  all_goals try (clear * - hc w0 w1 w2 w3 w4 w5 w6 w7; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG0b_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9207 + c.nreg 9204 ≤ W) (w1 : (c.nreg 9207 + c.nreg 9204) + c.nreg 9204 ≤ W) (w2 : ((c.nreg 9207 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w3 : (((c.nreg 9207 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w4 : c.nreg 9200 + c.nreg 9204 ≤ W) (w5 : (c.nreg 9200 + c.nreg 9204) + c.nreg 9204 ≤ W) (w6 : ((c.nreg 9200 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w7 : (((c.nreg 9200 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w8 : ((((c.nreg 9200 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w9 : (((((c.nreg 9200 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) :
    ∃ c' t, Exec P W pG0b c c' t ∧ t = 10 ∧ c'.nreg 9208 = (((c.nreg 9207 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9210 = ((c.nreg 9200 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9211 = (((c.nreg 9200 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9212 = ((((c.nreg 9200 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9213 = (((((c.nreg 9200 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧
      (∀ x, x ≠ 9208 → x ≠ 9210 → x ≠ 9211 → x ≠ 9212 → x ≠ 9213 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG0b
  exec_block
  all_goals try (clear * - hc w0 w1 w2 w3 w4 w5 w6 w7 w8 w9; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG0c_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9213 + c.nreg 9204 ≤ W) (w1 : (c.nreg 9213 + c.nreg 9204) + c.nreg 9204 ≤ W) (w2 : ((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w3 : (((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w4 : ((((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w5 : (((((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w6 : ((((((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w7 : (((((((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w8 : ((((((((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) :
    ∃ c' t, Exec P W pG0c c c' t ∧ t = 9 ∧ c'.nreg 9214 = c.nreg 9213 + c.nreg 9204 ∧ c'.nreg 9215 = (c.nreg 9213 + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9216 = ((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9217 = (((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9218 = ((((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9219 = (((((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9220 = ((((((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9221 = (((((((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9222 = ((((((((c.nreg 9213 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧
      (∀ x, x ≠ 9214 → x ≠ 9215 → x ≠ 9216 → x ≠ 9217 → x ≠ 9218 → x ≠ 9219 → x ≠ 9220 → x ≠ 9221 → x ≠ 9222 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG0c
  exec_block
  all_goals try (clear * - hc w0 w1 w2 w3 w4 w5 w6 w7 w8; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 h5 h6 h7 h8 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG0d_exec (c : Config) (hc : WordsBounded W c) (w0 : 1 ≤ W) (w1 : c.nreg 9222 + c.nreg 9204 ≤ W) (w2 : (c.nreg 9222 + c.nreg 9204) + 1 ≤ W) (w3 : (c.nreg 9222 + c.nreg 9204) + c.nreg 9204 ≤ W) (w4 : ((c.nreg 9222 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) (w5 : (((c.nreg 9222 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ≤ W) :
    ∃ c' t, Exec P W pG0d c c' t ∧ t = 7 ∧ c'.nreg 9223 = (c.nreg 9222 + c.nreg 9204) + 1 ∧ c'.nreg 9224 = ((c.nreg 9222 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9225 = (((c.nreg 9222 + c.nreg 9204) + c.nreg 9204) + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9230 = 1 ∧
      (∀ x, x ≠ 9223 → x ≠ 9224 → x ≠ 9225 → x ≠ 9230 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG0d
  exec_block
  all_goals try (clear * - hc w0 w1 w2 w3 w4 w5; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG1_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG1 c c' t ∧ t = 3 ∧ c'.nreg 9241 = c.nreg 9204 ∧ c'.nreg 9242 = c.nreg 9200 ∧ c'.nreg 9243 = c.nreg 9210 ∧
      (∀ x, x ≠ 9241 → x ≠ 9242 → x ≠ 9243 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG1
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG2_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9200 + c.nreg 9204 ≤ W) (w1 : (c.nreg 9200 + c.nreg 9204) + c.nreg 9204 ≤ W) :
    ∃ c' t, Exec P W pG2 c c' t ∧ t = 6 ∧ c'.nreg 9261 = c.nreg 9204 ∧ c'.nreg 9262 = c.nreg 9200 + c.nreg 9204 ∧ c'.nreg 9263 = (c.nreg 9200 + c.nreg 9204) + c.nreg 9204 ∧ c'.nreg 9264 = c.nreg 9211 ∧ c'.nreg 9265 = c.nreg 9203 ∧ c'.nreg 9266 = c.nreg 9205 ∧
      (∀ x, x ≠ 9261 → x ≠ 9262 → x ≠ 9263 → x ≠ 9264 → x ≠ 9265 → x ≠ 9266 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG2
  exec_block
  all_goals try (clear * - hc w0 w1; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG3_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG3 c c' t ∧ t = 4 ∧ c'.nreg 6210 = c.nreg 9204 ∧ c'.nreg 6211 = c.nreg 9206 ∧ c'.nreg 6212 = c.nreg 9207 ∧ c'.nreg 6213 = c.nreg 9212 ∧
      (∀ x, x ≠ 6210 → x ≠ 6211 → x ≠ 6212 → x ≠ 6213 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG3
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG4_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG4 c c' t ∧ t = 3 ∧ c'.nreg 9251 = c.nreg 9204 ∧ c'.nreg 9252 = c.nreg 9213 ∧ c'.nreg 9253 = 0 ∧
      (∀ x, x ≠ 9251 → x ≠ 9252 → x ≠ 9253 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG4
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG5_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG5 c c' t ∧ t = 3 ∧ c'.nreg 7350 = c.nreg 9212 ∧ c'.nreg 7351 = c.nreg 9213 ∧ c'.nreg 7352 = c.nreg 9204 ∧
      (∀ x, x ≠ 7350 → x ≠ 7351 → x ≠ 7352 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG5
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG6_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG6 c c' t ∧ t = 3 ∧ c'.nreg 9241 = c.nreg 9204 ∧ c'.nreg 9242 = c.nreg 9213 ∧ c'.nreg 9243 = c.nreg 9214 ∧
      (∀ x, x ≠ 9241 → x ≠ 9242 → x ≠ 9243 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG6
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG7_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG7 c c' t ∧ t = 3 ∧ c'.nreg 9272 = c.nreg 9204 ∧ c'.nreg 9273 = c.nreg 9214 ∧ c'.nreg 9274 = c.nreg 9215 ∧
      (∀ x, x ≠ 9272 → x ≠ 9273 → x ≠ 9274 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG7
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG8_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG8 c c' t ∧ t = 5 ∧ c'.nreg 6210 = c.nreg 9204 ∧ c'.nreg 6211 = c.nreg 9214 ∧ c'.nreg 6212 = c.nreg 9215 ∧ c'.nreg 6213 = c.nreg 9216 ∧ c'.nreg 9226 = c.nreg 9275 ∧
      (∀ x, x ≠ 6210 → x ≠ 6211 → x ≠ 6212 → x ≠ 6213 → x ≠ 9226 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG8
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG9_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG9 c c' t ∧ t = 4 ∧ c'.nreg 6210 = c.nreg 9204 ∧ c'.nreg 6211 = c.nreg 9206 ∧ c'.nreg 6212 = c.nreg 9216 ∧ c'.nreg 6213 = c.nreg 9217 ∧
      (∀ x, x ≠ 6210 → x ≠ 6211 → x ≠ 6212 → x ≠ 6213 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG9
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG10_exec (c : Config) (hc : WordsBounded W c) (w0 : 1 ≤ W) :
    ∃ c' t, Exec P W pG10 c c' t ∧ t = 3 ∧ c'.nreg 9251 = c.nreg 9204 ∧ c'.nreg 9252 = c.nreg 9218 ∧ c'.nreg 9253 = 1 ∧
      (∀ x, x ≠ 9251 → x ≠ 9252 → x ≠ 9253 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG10
  exec_block
  all_goals try (clear * - hc w0; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG11_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG11 c c' t ∧ t = 9 ∧ c'.nreg 1500 = c.nreg 9204 ∧ c'.nreg 1501 = c.nreg 9204 ∧ c'.nreg 1502 = c.nreg 9210 ∧ c'.nreg 1504 = c.nreg 9218 ∧ c'.nreg 1505 = c.nreg 9222 ∧ c'.nreg 1506 = c.nreg 9223 ∧ c'.nreg 1507 = c.nreg 9219 ∧ c'.nreg 1508 = c.nreg 9220 ∧ c'.nreg 1509 = c.nreg 9221 ∧
      (∀ x, x ≠ 1500 → x ≠ 1501 → x ≠ 1502 → x ≠ 1504 → x ≠ 1505 → x ≠ 1506 → x ≠ 1507 → x ≠ 1508 → x ≠ 1509 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG11
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 h5 h6 h7 h8 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG12_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG12 c c' t ∧ t = 3 ∧ c'.nreg 9272 = c.nreg 9204 ∧ c'.nreg 9273 = c.nreg 9210 ∧ c'.nreg 9274 = c.nreg 9224 ∧
      (∀ x, x ≠ 9272 → x ≠ 9273 → x ≠ 9274 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG12
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG13a_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9216 ≤ W) :
    ∃ c' t, Exec P W pG13a c c' t ∧ t = 9 ∧ c'.nreg 9000 = c.nreg 9204 ∧ c'.nreg 9001 = c.nreg 9226 ∧ c'.nreg 9002 = c.nreg 9208 ∧ c'.nreg 9003 = c.nreg 9216 ∧ c'.nreg 9004 = c.nreg 9217 ∧ c'.nreg 9005 = c.nreg 9205 ∧ c'.nreg 9006 = c.nreg 9225 ∧ c'.nreg 9007 = c.nmem (c.nreg 9216) ∧ c'.nreg 9227 = c.nreg 9275 ∧
      (∀ x, x ≠ 9000 → x ≠ 9001 → x ≠ 9002 → x ≠ 9003 → x ≠ 9004 → x ≠ 9005 → x ≠ 9006 → x ≠ 9007 → x ≠ 9227 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG13a
  exec_block
  all_goals try (clear * - hc w0; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 h5 h6 h7 h8 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG13b_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9204 * c.nreg 9205 ≤ W) (w1 : 1 ≤ W) (w2 : (c.nreg 9204 * c.nreg 9205) + 1 ≤ W) :
    ∃ c' t, Exec P W pG13b c c' t ∧ t = 3 ∧ c'.nreg 9008 = (c.nreg 9204 * c.nreg 9205) + 1 ∧ c'.nreg 9230 = 1 ∧
      (∀ x, x ≠ 9008 → x ≠ 9230 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG13b
  exec_block
  all_goals try (clear * - hc w0 w1 w2; config_simp; omega)
  refine ⟨rfl, ?_, ?_, fun x h0 h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG14_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9205 + c.nreg 9205 ≤ W) :
    ∃ c' t, Exec P W pG14 c c' t ∧ t = 3 ∧ c'.nreg 9281 = c.nreg 9204 ∧ c'.nreg 9282 = c.nreg 9208 ∧ c'.nreg 9283 = c.nreg 9205 + c.nreg 9205 ∧
      (∀ x, x ≠ 9281 → x ≠ 9282 → x ≠ 9283 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG14
  exec_block
  all_goals try (clear * - hc w0; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG15_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG15 c c' t ∧ t = 6 ∧ c'.nreg 9100 = c.nreg 9204 ∧ c'.nreg 9101 = c.nreg 9210 ∧ c'.nreg 9102 = c.nreg 9206 ∧ c'.nreg 9103 = c.nreg 9208 ∧ c'.nreg 9104 = c.nreg 9205 ∧ c'.nreg 9105 = c.nreg 9225 ∧
      (∀ x, x ≠ 9100 → x ≠ 9101 → x ≠ 9102 → x ≠ 9103 → x ≠ 9104 → x ≠ 9105 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG15
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG16a_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9225 + c.nreg 9204 ≤ W) (w1 : (c.nreg 9225 + c.nreg 9204) + c.nreg 9204 ≤ W) :
    ∃ c' t, Exec P W pG16a c c' t ∧ t = 9 ∧ c'.nreg 9151 = c.nreg 9208 ∧ c'.nreg 9152 = c.nreg 9206 ∧ c'.nreg 9153 = c.nreg 9210 ∧ c'.nreg 9154 = c.nreg 9205 ∧ c'.nreg 9155 = c.nreg 9211 ∧ c'.nreg 9156 = c.nreg 9201 ∧ c'.nreg 9157 = c.nreg 9202 ∧ c'.nreg 9158 = (c.nreg 9225 + c.nreg 9204) + c.nreg 9204 ∧
      (∀ x, x ≠ 9151 → x ≠ 9152 → x ≠ 9153 → x ≠ 9154 → x ≠ 9155 → x ≠ 9156 → x ≠ 9157 → x ≠ 9158 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG16a
  exec_block
  all_goals try (clear * - hc w0 w1; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem pG16b_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W pG16b c c' t ∧ t = 4 ∧ c'.nreg 9159 = c.nreg 9227 ∧ c'.nreg 9160 = c.nreg 9219 ∧ c'.nreg 9161 = c.nreg 9220 ∧ c'.nreg 9162 = c.nreg 9221 ∧
      (∀ x, x ≠ 9159 → x ≠ 9160 → x ≠ 9161 → x ≠ 9162 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pG16b
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

end Exec

end BKMNW

end PlanarFlow
