module

public import PlanarFlow.BKMNW.LrK
public import PlanarFlow.BKMNW.SmStep

/-!
# The tags of the large split: one child (machine)

The tag `ntag` of a child `y.1 = ds.dec S T X Hs' st' b'` of a large split: `1` if the child is
large (`ds.s < #X`; then it is a node of the guarded decomposition — a hypothesis here,
discharged by `decS_guard_isNode` for the headline), otherwise the tag of `smD pk S T X Hs'`,
which the classification scan `smA` of the small separator computes on the parent record with
the child's flags `LP` (at `A + n`), hole labels `HC` and ranks `KC` (from `lrOneA`)
(`SmArr.node`).

* `lrTgR` (the inputs of `smA`, the tags' base `Sb + 3 m + k` in `8522`), `tgV` (the tag from
  the counts of the scan and `s`), `tgV_eq`, **`lrTgB s`** (the tag stored at
  `Sb + 3 m + k + t`), with exec lemmas;
* **`lrTag s = lrOneA ; lrTgR ; smA ; lrTgB s`**.
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

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

/-- The inputs of the classification scan on the parent record, the tags' base. -/
def lrTgR : Stmt := block [.copyN 5300 5504, .copyN 5301 5507, .copyN 5302 5512,
  .copyN 5303 6534, .copyN 5304 6533, .copyN 5305 5515, .constN 8530 3, .mulN 8531 8530 5501,
  .addN 8522 5505 8531, .addN 8522 8522 5502]

/-- **The tag of a child** from the counts of the scan: `1` if `s < cP`, else the node bit. -/
def tgV (s cP cI gX gY gB : ℕ) : ℕ :=
  smNode cP cI gX gY gB + (smSg (cP - s) - smNode cP cI gX gY gB)

lemma smNode_le_one (cP cI gX gY gB : ℕ) : smNode cP cI gX gY gB ≤ 1 := by
  unfold smNode smAnd smSg; omega

lemma tgV_eq (s cP cI gX gY gB : ℕ) :
    tgV s cP cI gX gY gB = if s < cP then 1 else smNode cP cI gX gY gB := by
  have := smNode_le_one cP cI gX gY gB
  unfold tgV smSg
  split_ifs with h <;> omega

/-- **The tag stored at `Sb + 3 m + k + t`.** -/
def lrTgB (s : ℕ) : Stmt := block [.constN 8530 1, .constN 8540 2, .subN 8531 5315 8540,
  .subN 8532 8531 8530, .subN 8531 8531 8532, .subN 8532 8530 5327, .subN 8531 8531 8532,
  .subN 8533 5316 8530, .subN 8533 5316 8533, .subN 8534 8530 5323, .addN 8534 8534 5317,
  .addN 8534 8534 8533, .subN 8535 8534 8530, .subN 8534 8534 8535, .subN 8535 8530 8534,
  .subN 8524 8531 8535, .constN 8536 s, .subN 8537 5315 8536, .subN 8538 8537 8530,
  .subN 8537 8537 8538, .subN 8538 8537 8524, .addN 8538 8524 8538, .addN 8539 8522 8508,
  .storeN 8539 8538]

/-- **The tag of one child** (`t = r8508`). -/
def lrTag (s : ℕ) : Stmt := .seq lrOneA (.seq lrTgR (.seq smA (lrTgB s)))

section Exec

variable {I : Input} {W : ℕ}

theorem lrTgR_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb A : ℕ}
    (hR : SmRegs c d m k R n Sb A) (w : Sb + 3 * m + k ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec I W lrTgR c c' t ∧ t = 10 ∧ c'.nreg 5300 = n ∧ c'.nreg 5301 = A + n ∧
      c'.nreg 5302 = R + 3 + n ∧ c'.nreg 5303 = c.nreg 6534 ∧ c'.nreg 5304 = c.nreg 6533 ∧
      c'.nreg 5305 = R + 3 + 4 * n ∧ c'.nreg 8522 = Sb + 3 * m + k ∧
      (∀ x, (x < 5300 ∨ (5305 < x ∧ x < 8522) ∨ (8522 < x ∧ x < 8530) ∨ 8531 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have r04 := hR.r04; have r07 := hR.r07; have r12 := hR.r12; have r15 := hR.r15
  have r05 := hR.r05; have r01 := hR.r01; have r02 := hR.r02
  have := hc.1 6534; have := hc.1 6533; have := hc.1 5507; have := hc.1 5512; have := hc.1 5515
  unfold lrTgR
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r04, r07, r12, r15, r05, r01, r02]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r04, r07, r12, r15, r05, r01, r02])
    try omega

theorem lrTgB_exec (c : Config) (hc : WordsBounded W c) {s cP cI gX gY gB a t : ℕ}
    (r15 : c.nreg 5315 = cP) (r16 : c.nreg 5316 = cI) (r17 : c.nreg 5317 = gX)
    (r23 : c.nreg 5323 = gY) (r27 : c.nreg 5327 = gB) (r22 : c.nreg 8522 = a)
    (r08 : c.nreg 8508 = t) (hX : gX ≤ 1) (hY : gY ≤ 1) (hB : gB ≤ 1)
    (hs : s ≤ W) (w : a + t ≤ W) (hW : 21 ≤ W) :
    ∃ c' t', Exec I W (lrTgB s) c c' t' ∧ t' = 24 ∧
      c'.nmem (a + t) = tgV s cP cI gX gY gB ∧
      (∀ b, b ≠ a + t → c'.nmem b = c.nmem b) ∧
      (∀ x, (x < 8524 ∨ (8524 < x ∧ x < 8530) ∨ 8540 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h15 := hc.1 5315; have h16 := hc.1 5316
  have e1 : smNode cP cI gX gY gB ≤ 1 := smNode_le_one _ _ _ _ _
  unfold lrTgB
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r15, r16, r17, r23, r27, r22, r08]; omega)
  refine ⟨rfl, ?_, fun b hb => ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r15, r16, r17, r23, r27, r22, r08]
    unfold tgV smNode smAnd smSg
    omega
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r15, r16, r17, r23, r27, r22, r08])
    try omega

end Exec

end MfDrv

end BKMNW

end PlanarFlow
