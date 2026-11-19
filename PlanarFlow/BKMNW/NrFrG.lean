module

public import PlanarFlow.BKMNW.NrFrM

/-!
# The glue blocks of the push-back steps `retP`, `frmP`

Straight-line blocks (generated mechanically) setting the bases of the scratch arrays of
the core `fcore` of `retP`/`frmP` (registers `9180 … 9199`, from `r3004 = d`, `r3006 = b + 5`), the
part of the separator (`r6807`, `r6800`) and the input registers of its subprograms, each with its
`*_exec` lemma (the values of the written registers, all others kept; the memory kept, or one
store).
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

/-- Glue block `fA` of `pchP`. -/
def fA : Stmt :=
  block [.copyN 9180 3004, .loadN 9181 3004, .constN 9199 3, .addN 9198 3004 9199, .loadN 9182 9198, .constN 9199 5, .subN 9183 3006 9199, .mulN 9184 9181 9182, .addN 9184 9184 9182, .copyN 8430 9183]

/-- Glue block `fB` of `pchP`. -/
def fB : Stmt :=
  block [.copyN 9241 9181, .copyN 9242 9183, .addN 9186 9183 9181, .addN 9186 9186 9181, .addN 9186 9186 9181, .copyN 9243 9186]

/-- Glue block `fC` of `pchP`. -/
def fC : Stmt :=
  block [.copyN 9261 9181, .addN 9262 9183 9181, .addN 9263 9262 9181, .addN 9187 9186 9181, .copyN 9264 9187, .copyN 9265 9184, .copyN 9266 9182]

/-- Glue block `fD` of `pchP`. -/
def fD : Stmt :=
  block [.addN 9188 9187 9181, .copyN 6210 9181, .copyN 6211 9186, .copyN 6212 9187, .copyN 6213 9188]

/-- Glue block `fE1` of `pchP`. -/
def fE1 : Stmt :=
  block [.addN 9189 9188 9181, .copyN 9288 9181, .constN 9199 4, .addN 9198 9180 9199, .addN 9198 9198 9181, .addN 9198 9198 9181, .addN 9198 9198 9181, .addN 9198 9198 9181]

/-- Glue block `fE2` of `pchP`. -/
def fE2 : Stmt :=
  block [.copyN 9289 9198, .copyN 9290 9189, .copyN 9291 9185]

/-- Glue block `fF` of `pchP`. -/
def fF : Stmt :=
  block [.addN 9190 9189 9181, .copyN 9251 9181, .copyN 9252 9190, .constN 9253 0]

/-- Glue block `fG1` of `pchP`. -/
def fG1 : Stmt :=
  block [.copyN 9191 6807, .loadN 9192 9191, .constN 9199 1, .addN 9198 9191 9199, .addN 9193 9198 6800, .loadN 9193 9193, .addN 9194 9198 9192, .addN 9195 9194 6800, .loadN 9195 9195, .addN 9196 9194 9192]

/-- Glue block `fG2` of `pchP`. -/
def fG2 : Stmt :=
  block [.addN 9197 9196 9193, .addN 9198 9191 9192, .loadN 9198 9198, .addN 9199 9191 9192, .addN 9199 9199 9192, .loadN 9199 9199, .addN 9198 9198 9199, .addN 9198 9196 9198, .addN 9198 9198 6800, .loadN 9198 9198]

/-- Glue block `fG3` of `pchP`. -/
def fG3 : Stmt :=
  block [.addN 9198 9186 9198, .loadN 9198 9198, .addN 9198 9190 9198, .constN 9199 1, .storeN 9198 9199]

/-- Glue block `fH` of `pchP`. -/
def fH : Stmt :=
  block [.copyN 9288 9195, .copyN 9289 9197, .constN 9199 4, .addN 9198 9180 9199, .addN 9290 9198 9181, .copyN 9291 9186, .copyN 9292 9190]

/-- Glue block `fI` of `pchP`. -/
def fI : Stmt :=
  block [.copyN 6210 9181, .copyN 6211 9186, .copyN 6212 9190, .addN 6213 9190 9181]

/-- Glue block `fJ` of `pchP`. -/
def fJ : Stmt :=
  block [.copyN 9288 9181, .copyN 9289 9188, .addN 9290 9190 9181, .addN 9291 9290 9181, .copyN 9293 9184]

/-- Glue block `fK` of `pchP`. -/
def fK : Stmt :=
  block [.addN 9200 9291 9181, .copyN 9201 9291, .copyN 9202 9189, .copyN 9203 9184]

/-- Glue block `fFrm` of `pchP`. -/
def fFrm : Stmt :=
  block [.constN 9185 2]

/-- Glue block `fRet` of `pchP`. -/
def fRet : Stmt :=
  block [.constN 9185 0]

/-- Glue block `fN1` of `pchP`. -/
def fN1 : Stmt :=
  block [.loadN 9281 3004, .constN 9199 4, .addN 9282 3004 9199, .addN 9282 9282 9281, .addN 9282 9282 9281, .addN 9282 9282 9281, .addN 9282 9282 9281, .addN 9282 9282 9281, .addN 9282 9282 9281]

/-- Glue block `fN2` of `pchP`. -/
def fN2 : Stmt :=
  block [.constN 9199 3, .addN 9198 3004 9199, .loadN 9198 9198, .addN 9283 9198 9198]

section Exec

variable {P : Input} {W : ℕ}

theorem fA_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 3004 ≤ W) (w1 : 3 ≤ W) (w2 : c.nreg 3004 + 3 ≤ W) (w3 : (c.nreg 3004 + 3) ≤ W) (w4 : 5 ≤ W) (w5 : c.nmem (c.nreg 3004) * c.nmem ((c.nreg 3004 + 3)) ≤ W) (w6 : (c.nmem (c.nreg 3004) * c.nmem ((c.nreg 3004 + 3))) + c.nmem ((c.nreg 3004 + 3)) ≤ W) :
    ∃ c' t, Exec P W fA c c' t ∧ t = 10 ∧ c'.nreg 8430 = c.nreg 3006 - 5 ∧ c'.nreg 9180 = c.nreg 3004 ∧ c'.nreg 9181 = c.nmem (c.nreg 3004) ∧ c'.nreg 9182 = c.nmem ((c.nreg 3004 + 3)) ∧ c'.nreg 9183 = c.nreg 3006 - 5 ∧ c'.nreg 9184 = (c.nmem (c.nreg 3004) * c.nmem ((c.nreg 3004 + 3))) + c.nmem ((c.nreg 3004 + 3)) ∧ c'.nreg 9198 = c.nreg 3004 + 3 ∧ c'.nreg 9199 = 5 ∧
      (∀ x, x ≠ 8430 → x ≠ 9180 → x ≠ 9181 → x ≠ 9182 → x ≠ 9183 → x ≠ 9184 → x ≠ 9198 → x ≠ 9199 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fA
  exec_block
  all_goals try (clear * - hc w0 w1 w2 w3 w4 w5 w6; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fB_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9183 + c.nreg 9181 ≤ W) (w1 : (c.nreg 9183 + c.nreg 9181) + c.nreg 9181 ≤ W) (w2 : ((c.nreg 9183 + c.nreg 9181) + c.nreg 9181) + c.nreg 9181 ≤ W) :
    ∃ c' t, Exec P W fB c c' t ∧ t = 6 ∧ c'.nreg 9186 = ((c.nreg 9183 + c.nreg 9181) + c.nreg 9181) + c.nreg 9181 ∧ c'.nreg 9241 = c.nreg 9181 ∧ c'.nreg 9242 = c.nreg 9183 ∧ c'.nreg 9243 = ((c.nreg 9183 + c.nreg 9181) + c.nreg 9181) + c.nreg 9181 ∧
      (∀ x, x ≠ 9186 → x ≠ 9241 → x ≠ 9242 → x ≠ 9243 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fB
  exec_block
  all_goals try (clear * - hc w0 w1 w2; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fC_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9183 + c.nreg 9181 ≤ W) (w1 : (c.nreg 9183 + c.nreg 9181) + c.nreg 9181 ≤ W) (w2 : c.nreg 9186 + c.nreg 9181 ≤ W) :
    ∃ c' t, Exec P W fC c c' t ∧ t = 7 ∧ c'.nreg 9187 = c.nreg 9186 + c.nreg 9181 ∧ c'.nreg 9261 = c.nreg 9181 ∧ c'.nreg 9262 = c.nreg 9183 + c.nreg 9181 ∧ c'.nreg 9263 = (c.nreg 9183 + c.nreg 9181) + c.nreg 9181 ∧ c'.nreg 9264 = c.nreg 9186 + c.nreg 9181 ∧ c'.nreg 9265 = c.nreg 9184 ∧ c'.nreg 9266 = c.nreg 9182 ∧
      (∀ x, x ≠ 9187 → x ≠ 9261 → x ≠ 9262 → x ≠ 9263 → x ≠ 9264 → x ≠ 9265 → x ≠ 9266 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fC
  exec_block
  all_goals try (clear * - hc w0 w1 w2; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fD_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9187 + c.nreg 9181 ≤ W) :
    ∃ c' t, Exec P W fD c c' t ∧ t = 5 ∧ c'.nreg 6210 = c.nreg 9181 ∧ c'.nreg 6211 = c.nreg 9186 ∧ c'.nreg 6212 = c.nreg 9187 ∧ c'.nreg 6213 = c.nreg 9187 + c.nreg 9181 ∧ c'.nreg 9188 = c.nreg 9187 + c.nreg 9181 ∧
      (∀ x, x ≠ 6210 → x ≠ 6211 → x ≠ 6212 → x ≠ 6213 → x ≠ 9188 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fD
  exec_block
  all_goals try (clear * - hc w0; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fE1_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9188 + c.nreg 9181 ≤ W) (w1 : 4 ≤ W) (w2 : c.nreg 9180 + 4 ≤ W) (w3 : (c.nreg 9180 + 4) + c.nreg 9181 ≤ W) (w4 : ((c.nreg 9180 + 4) + c.nreg 9181) + c.nreg 9181 ≤ W) (w5 : (((c.nreg 9180 + 4) + c.nreg 9181) + c.nreg 9181) + c.nreg 9181 ≤ W) (w6 : ((((c.nreg 9180 + 4) + c.nreg 9181) + c.nreg 9181) + c.nreg 9181) + c.nreg 9181 ≤ W) :
    ∃ c' t, Exec P W fE1 c c' t ∧ t = 8 ∧ c'.nreg 9189 = c.nreg 9188 + c.nreg 9181 ∧ c'.nreg 9198 = ((((c.nreg 9180 + 4) + c.nreg 9181) + c.nreg 9181) + c.nreg 9181) + c.nreg 9181 ∧ c'.nreg 9199 = 4 ∧ c'.nreg 9288 = c.nreg 9181 ∧
      (∀ x, x ≠ 9189 → x ≠ 9198 → x ≠ 9199 → x ≠ 9288 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fE1
  exec_block
  all_goals try (clear * - hc w0 w1 w2 w3 w4 w5 w6; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fE2_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W fE2 c c' t ∧ t = 3 ∧ c'.nreg 9289 = c.nreg 9198 ∧ c'.nreg 9290 = c.nreg 9189 ∧ c'.nreg 9291 = c.nreg 9185 ∧
      (∀ x, x ≠ 9289 → x ≠ 9290 → x ≠ 9291 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fE2
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fF_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9189 + c.nreg 9181 ≤ W) :
    ∃ c' t, Exec P W fF c c' t ∧ t = 4 ∧ c'.nreg 9190 = c.nreg 9189 + c.nreg 9181 ∧ c'.nreg 9251 = c.nreg 9181 ∧ c'.nreg 9252 = c.nreg 9189 + c.nreg 9181 ∧ c'.nreg 9253 = 0 ∧
      (∀ x, x ≠ 9190 → x ≠ 9251 → x ≠ 9252 → x ≠ 9253 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fF
  exec_block
  all_goals try (clear * - hc w0; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fG1_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 6807 ≤ W) (w1 : 1 ≤ W) (w2 : c.nreg 6807 + 1 ≤ W) (w3 : (c.nreg 6807 + 1) + c.nreg 6800 ≤ W) (w4 : ((c.nreg 6807 + 1) + c.nreg 6800) ≤ W) (w5 : (c.nreg 6807 + 1) + c.nmem (c.nreg 6807) ≤ W) (w6 : ((c.nreg 6807 + 1) + c.nmem (c.nreg 6807)) + c.nreg 6800 ≤ W) (w7 : (((c.nreg 6807 + 1) + c.nmem (c.nreg 6807)) + c.nreg 6800) ≤ W) (w8 : ((c.nreg 6807 + 1) + c.nmem (c.nreg 6807)) + c.nmem (c.nreg 6807) ≤ W) :
    ∃ c' t, Exec P W fG1 c c' t ∧ t = 10 ∧ c'.nreg 9191 = c.nreg 6807 ∧ c'.nreg 9192 = c.nmem (c.nreg 6807) ∧ c'.nreg 9193 = c.nmem (((c.nreg 6807 + 1) + c.nreg 6800)) ∧ c'.nreg 9194 = (c.nreg 6807 + 1) + c.nmem (c.nreg 6807) ∧ c'.nreg 9195 = c.nmem ((((c.nreg 6807 + 1) + c.nmem (c.nreg 6807)) + c.nreg 6800)) ∧ c'.nreg 9196 = ((c.nreg 6807 + 1) + c.nmem (c.nreg 6807)) + c.nmem (c.nreg 6807) ∧ c'.nreg 9198 = c.nreg 6807 + 1 ∧ c'.nreg 9199 = 1 ∧
      (∀ x, x ≠ 9191 → x ≠ 9192 → x ≠ 9193 → x ≠ 9194 → x ≠ 9195 → x ≠ 9196 → x ≠ 9198 → x ≠ 9199 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fG1
  exec_block
  all_goals try (clear * - hc w0 w1 w2 w3 w4 w5 w6 w7 w8; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 h5 h6 h7 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fG2_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9196 + c.nreg 9193 ≤ W) (w1 : c.nreg 9191 + c.nreg 9192 ≤ W) (w2 : (c.nreg 9191 + c.nreg 9192) ≤ W) (w3 : (c.nreg 9191 + c.nreg 9192) + c.nreg 9192 ≤ W) (w4 : ((c.nreg 9191 + c.nreg 9192) + c.nreg 9192) ≤ W) (w5 : c.nmem ((c.nreg 9191 + c.nreg 9192)) + c.nmem (((c.nreg 9191 + c.nreg 9192) + c.nreg 9192)) ≤ W) (w6 : c.nreg 9196 + (c.nmem ((c.nreg 9191 + c.nreg 9192)) + c.nmem (((c.nreg 9191 + c.nreg 9192) + c.nreg 9192))) ≤ W) (w7 : (c.nreg 9196 + (c.nmem ((c.nreg 9191 + c.nreg 9192)) + c.nmem (((c.nreg 9191 + c.nreg 9192) + c.nreg 9192)))) + c.nreg 6800 ≤ W) (w8 : ((c.nreg 9196 + (c.nmem ((c.nreg 9191 + c.nreg 9192)) + c.nmem (((c.nreg 9191 + c.nreg 9192) + c.nreg 9192)))) + c.nreg 6800) ≤ W) :
    ∃ c' t, Exec P W fG2 c c' t ∧ t = 10 ∧ c'.nreg 9197 = c.nreg 9196 + c.nreg 9193 ∧ c'.nreg 9198 = c.nmem (((c.nreg 9196 + (c.nmem ((c.nreg 9191 + c.nreg 9192)) + c.nmem (((c.nreg 9191 + c.nreg 9192) + c.nreg 9192)))) + c.nreg 6800)) ∧ c'.nreg 9199 = c.nmem (((c.nreg 9191 + c.nreg 9192) + c.nreg 9192)) ∧
      (∀ x, x ≠ 9197 → x ≠ 9198 → x ≠ 9199 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fG2
  exec_block
  all_goals try (clear * - hc w0 w1 w2 w3 w4 w5 w6 w7 w8; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fG3_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9186 + c.nreg 9198 ≤ W) (w1 : (c.nreg 9186 + c.nreg 9198) ≤ W) (w2 : c.nreg 9190 + c.nmem ((c.nreg 9186 + c.nreg 9198)) ≤ W) (w3 : 1 ≤ W) (w4 : (c.nreg 9190 + c.nmem ((c.nreg 9186 + c.nreg 9198))) ≤ W) :
    ∃ c' t, Exec P W fG3 c c' t ∧ t = 5 ∧ c'.nreg 9198 = c.nreg 9190 + c.nmem ((c.nreg 9186 + c.nreg 9198)) ∧ c'.nreg 9199 = 1 ∧
      (∀ x, x ≠ 9198 → x ≠ 9199 → c'.nreg x = c.nreg x) ∧ c'.nmem = upd c.nmem (c.nreg 9190 + c.nmem ((c.nreg 9186 + c.nreg 9198))) (1) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fG3
  exec_block
  all_goals try (clear * - hc w0 w1 w2 w3 w4; config_simp; omega)
  refine ⟨rfl, ?_, ?_, fun x h0 h1 => ?_, ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fH_exec (c : Config) (hc : WordsBounded W c) (w0 : 4 ≤ W) (w1 : c.nreg 9180 + 4 ≤ W) (w2 : (c.nreg 9180 + 4) + c.nreg 9181 ≤ W) :
    ∃ c' t, Exec P W fH c c' t ∧ t = 7 ∧ c'.nreg 9198 = c.nreg 9180 + 4 ∧ c'.nreg 9199 = 4 ∧ c'.nreg 9288 = c.nreg 9195 ∧ c'.nreg 9289 = c.nreg 9197 ∧ c'.nreg 9290 = (c.nreg 9180 + 4) + c.nreg 9181 ∧ c'.nreg 9291 = c.nreg 9186 ∧ c'.nreg 9292 = c.nreg 9190 ∧
      (∀ x, x ≠ 9198 → x ≠ 9199 → x ≠ 9288 → x ≠ 9289 → x ≠ 9290 → x ≠ 9291 → x ≠ 9292 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fH
  exec_block
  all_goals try (clear * - hc w0 w1 w2; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fI_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9190 + c.nreg 9181 ≤ W) :
    ∃ c' t, Exec P W fI c c' t ∧ t = 4 ∧ c'.nreg 6210 = c.nreg 9181 ∧ c'.nreg 6211 = c.nreg 9186 ∧ c'.nreg 6212 = c.nreg 9190 ∧ c'.nreg 6213 = c.nreg 9190 + c.nreg 9181 ∧
      (∀ x, x ≠ 6210 → x ≠ 6211 → x ≠ 6212 → x ≠ 6213 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fI
  exec_block
  all_goals try (clear * - hc w0; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fJ_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9190 + c.nreg 9181 ≤ W) (w1 : (c.nreg 9190 + c.nreg 9181) + c.nreg 9181 ≤ W) :
    ∃ c' t, Exec P W fJ c c' t ∧ t = 5 ∧ c'.nreg 9288 = c.nreg 9181 ∧ c'.nreg 9289 = c.nreg 9188 ∧ c'.nreg 9290 = c.nreg 9190 + c.nreg 9181 ∧ c'.nreg 9291 = (c.nreg 9190 + c.nreg 9181) + c.nreg 9181 ∧ c'.nreg 9293 = c.nreg 9184 ∧
      (∀ x, x ≠ 9288 → x ≠ 9289 → x ≠ 9290 → x ≠ 9291 → x ≠ 9293 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fJ
  exec_block
  all_goals try (clear * - hc w0 w1; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fK_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 9291 + c.nreg 9181 ≤ W) :
    ∃ c' t, Exec P W fK c c' t ∧ t = 4 ∧ c'.nreg 9200 = c.nreg 9291 + c.nreg 9181 ∧ c'.nreg 9201 = c.nreg 9291 ∧ c'.nreg 9202 = c.nreg 9189 ∧ c'.nreg 9203 = c.nreg 9184 ∧
      (∀ x, x ≠ 9200 → x ≠ 9201 → x ≠ 9202 → x ≠ 9203 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fK
  exec_block
  all_goals try (clear * - hc w0; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x h0 h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fFrm_exec (c : Config) (hc : WordsBounded W c) (w0 : 2 ≤ W) :
    ∃ c' t, Exec P W fFrm c c' t ∧ t = 1 ∧ c'.nreg 9185 = 2 ∧
      (∀ x, x ≠ 9185 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fFrm
  exec_block
  all_goals try (clear * - hc w0; config_simp; omega)
  refine ⟨rfl, ?_, fun x h0 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fRet_exec (c : Config) (hc : WordsBounded W c)  :
    ∃ c' t, Exec P W fRet c c' t ∧ t = 1 ∧ c'.nreg 9185 = 0 ∧
      (∀ x, x ≠ 9185 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fRet
  exec_block
  all_goals try (clear * - hc ; config_simp; omega)
  refine ⟨rfl, ?_, fun x h0 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fN1_exec (c : Config) (hc : WordsBounded W c) (w0 : c.nreg 3004 ≤ W) (w1 : 4 ≤ W) (w2 : c.nreg 3004 + 4 ≤ W) (w3 : (c.nreg 3004 + 4) + c.nmem (c.nreg 3004) ≤ W) (w4 : ((c.nreg 3004 + 4) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004) ≤ W) (w5 : (((c.nreg 3004 + 4) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004) ≤ W) (w6 : ((((c.nreg 3004 + 4) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004) ≤ W) (w7 : (((((c.nreg 3004 + 4) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004) ≤ W) (w8 : ((((((c.nreg 3004 + 4) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004) ≤ W) :
    ∃ c' t, Exec P W fN1 c c' t ∧ t = 9 ∧ c'.nreg 9199 = 4 ∧ c'.nreg 9281 = c.nmem (c.nreg 3004) ∧ c'.nreg 9282 = ((((((c.nreg 3004 + 4) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004)) + c.nmem (c.nreg 3004) ∧
      (∀ x, x ≠ 9199 → x ≠ 9281 → x ≠ 9282 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fN1
  exec_block
  all_goals try (clear * - hc w0 w1 w2 w3 w4 w5 w6 w7 w8; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

theorem fN2_exec (c : Config) (hc : WordsBounded W c) (w0 : 3 ≤ W) (w1 : c.nreg 3004 + 3 ≤ W) (w2 : (c.nreg 3004 + 3) ≤ W) (w3 : c.nmem ((c.nreg 3004 + 3)) + c.nmem ((c.nreg 3004 + 3)) ≤ W) :
    ∃ c' t, Exec P W fN2 c c' t ∧ t = 4 ∧ c'.nreg 9198 = c.nmem ((c.nreg 3004 + 3)) ∧ c'.nreg 9199 = 3 ∧ c'.nreg 9283 = c.nmem ((c.nreg 3004 + 3)) + c.nmem ((c.nreg 3004 + 3)) ∧
      (∀ x, x ≠ 9198 → x ≠ 9199 → x ≠ 9283 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fN2
  exec_block
  all_goals try (clear * - hc w0 w1 w2 w3; config_simp; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x h0 h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [upd_apply]; split_ifs <;> omega)

end Exec

end BKMNW

end PlanarFlow
