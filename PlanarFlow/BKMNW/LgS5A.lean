module

public import PlanarFlow.BKMNW.LgLv
public import PlanarFlow.BKMNW.EbProg
public import PlanarFlow.BKMNW.PcWt

/-!
# The large-piece separator, stage 5: the program and its set-up blocks

The program of stage 5 (`lgS5`), from three input registers `3100 = R` (the record), `3101 = U`
(the base of the scratch, above the record) and `3102 = k` (the number of holes):

`s5A ; lgPrep ; s5B ; lgPar ; s5Sv ; if 0 < n' then s5Body`, with
`s5Body = s5Mid ; s5Fin`, `s5Mid = s5K ; lgKey ; s5C ; lgWt ; s5D ; ebProg`,
`s5Fin = s5E1 ; s5E2 ; s5E3 ; s5E4 ; tfProg ; scProg mbBase`.

Layout (`n = mem R` darts of the record, `n'` darts of the core's piece map, `k` holes):

| what | base |
| --- | --- |
| `CF`, `CI` (`lgPrep`) | `U`, `U + n` |
| `IX` (the core's enumeration) | `U + 2n` |
| `SG` (its rotation) | `U + 3n` |
| `b` (`LvIn`: `NF`, `TH`, `RV0`, `EX`, `TK`) | `U + 4n` |
| `lgKey`'s scratch | `[b + 20n + 3, b + 27n + 6)` |
| `Yb` (`lgWt`'s scratch) | `U + 31n + 7` |
| `Zb` (`lgPar`'s scratch) | `U + 42n + 2k + 11` |
| `RECb` (`scProg`; also `tfProg`'s `Zb`) | `U + 42n + 5k + 13` |
| `IX0`, `ITEMb`, `NHb` | `RECb + 18`, `IX0 + 7n' + 1`, `ITEMb + n'` |
| `Hb`, `SVb` | `NHb + n' + Bz + 25n' + 3W₀ + 15`, `Hb + 13 n'` |

Saved below `700 … 4400` (kept by the certificate, `scProgT_frame`): `3103 = n'`, `3104 = nTouch`,
`3105` = the flag of `holeStep`, `3106 = K`, `3107 = A`, `3108 = W₀`, `3109 = Bz`.

This file: the definitions and the exec lemmas of the set-up blocks.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.tacticAnalysis.rwaSuggestion false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

/-- The registers of `lgPrep` from `3100 = R`, `3101 = U`. -/
def s5A : Stmt := block [.loadN 5800 3100, .constN 5806 1, .constN 5807 2, .constN 6521 1,
  .constN 5940 3, .addN 5941 3100 5940, .addN 5801 5941 5800, .addN 5802 5801 5800,
  .addN 5942 5802 5800, .addN 5803 5942 5800, .addN 5805 5803 5800, .copyN 5804 3101,
  .addN 5808 5804 5800, .addN 5809 5808 5800, .addN 5814 5809 5800, .addN 5810 5814 5800]

/-- The registers of `lgPar`: `5870 = k`, `5915 = mem (R + 2)`, `5916 = Zb`. -/
def s5B : Stmt := block [.copyN 5870 3102, .constN 5943 2, .addN 5944 3100 5943,
  .loadN 5915 5944, .constN 5943 38, .mulN 5945 5943 5800, .addN 5945 5945 5810,
  .addN 5945 5945 3102, .addN 5945 5945 3102, .constN 5943 11, .addN 5916 5945 5943,
  .constN 6521 1]

/-- Save the parameters below `4400`; the zero of the test. -/
def s5Sv : Stmt := block [.copyN 3103 5811, .copyN 3104 5914, .copyN 3105 5913,
  .copyN 3106 5910, .copyN 3107 5911, .copyN 3108 5912, .constN 5947 0]

/-- Before `lgKey`. -/
def s5K : Stmt := block [.constN 6521 1]

/-- The registers of `lgWt`: `5871 = K`, `5872 = Yb`. -/
def s5C : Stmt := block [.copyN 5871 5910, .constN 5943 27, .mulN 5946 5943 5800,
  .addN 5946 5946 5810, .constN 5943 7, .addN 5872 5946 5943, .constN 6521 1]

/-- The input of `ebProg`. -/
def s5D : Stmt := block [.copyN 5850 5912]

/-- `LvRegs`, part 1: the bases `b + j n'`. -/
def s5E1 : Stmt := block [.copyN 4881 5810, .addN 4882 4881 5811, .addN 4843 4882 5811,
  .addN 4883 4843 5811, .addN 4847 4883 5811, .addN 4848 4847 5811, .addN 4422 4848 5811,
  .addN 4846 4422 5811, .addN 4866 4846 5811, .addN 4425 4866 5811, .addN 5948 4425 5811,
  .constN 4633 1, .addN 4426 5948 4633, .addN 5948 4426 5811, .addN 5948 5948 5811,
  .addN 4849 5948 5811, .addN 4404 4849 5811, .addN 5948 4404 5811, .addN 4885 5948 4633,
  .addN 4886 4885 5811, .addN 4887 4886 5811, .addN 4888 4887 5811, .addN 5948 4888 5811,
  .addN 4824 5948 4633]

/-- `LvRegs`, part 2. -/
def s5E2 : Stmt := block [.copyN 4840 5811, .copyN 4841 5810, .copyN 4842 4882,
  .copyN 4420 5811, .copyN 4421 4848, .copyN 4423 4846, .copyN 4424 4866, .copyN 4400 5811,
  .copyN 4401 4425, .copyN 4402 4426, .copyN 4403 4849, .copyN 4760 5811, .copyN 4761 4847,
  .copyN 4762 4849, .copyN 4874 3102, .copyN 4880 5811, .copyN 4630 5811, .copyN 4631 4849,
  .copyN 4632 4887, .copyN 4634 4888]

/-- `LvRegs`, part 3. -/
def s5E3 : Stmt := block [.copyN 4780 5811, .copyN 4781 5810, .copyN 4782 4849,
  .copyN 4783 4888, .copyN 4784 5911, .copyN 4785 5912, .copyN 4800 5811, .copyN 4820 5811,
  .copyN 4821 5810, .copyN 4822 4849, .copyN 4910 5811, .copyN 4911 4824, .copyN 4912 5810]

/-- The bases of `scProg` and `tfProg`. -/
def s5E4 : Stmt := block [.copyN 5200 5814, .copyN 5202 5858, .copyN 3109 5858,
  .constN 5949 38, .mulN 5950 5949 5800, .addN 5950 5950 5810, .addN 5950 5950 3102,
  .addN 5950 5950 3102, .addN 5950 5950 3102, .addN 5950 5950 3102, .addN 5950 5950 3102,
  .constN 5949 13, .addN 4936 5950 5949, .copyN 5830 4936, .constN 5949 18,
  .addN 4937 4936 5949, .constN 5949 7, .mulN 5951 5949 5811, .addN 5951 5951 4937,
  .constN 5949 1, .addN 4955 5951 5949, .addN 4956 4955 5811, .addN 5952 4956 5811,
  .addN 5952 5952 5858, .constN 5949 25, .mulN 5953 5949 5811, .addN 5952 5952 5953,
  .addN 5952 5952 5912, .addN 5952 5952 5912, .addN 5952 5952 5912, .constN 5949 15,
  .addN 5201 5952 5949, .constN 5949 13, .mulN 5954 5949 5811, .addN 5203 5201 5954]

/-- The keys, the weights and the base of the certificate. -/
def s5Mid : Stmt := .seq (.seq s5K lgKey) (.seq (.seq s5C lgWt) (.seq s5D ebProg))

/-- The set-up of the levels and the certificate. -/
def s5Fin : Stmt :=
  .seq (.seq s5E1 (.seq s5E2 (.seq s5E3 s5E4))) (.seq tfProg (scProg mbBase))

/-- The body of stage 5 (a nonempty piece map of the core). -/
def s5Body : Stmt := .seq s5Mid s5Fin

/-- The part of stage 5 before the test. -/
def s5Pre : Stmt := .seq (.seq s5A lgPrep) (.seq (.seq s5B lgPar) s5Sv)

/-- **Stage 5 of the large-piece separator.** -/
def lgS5 : Stmt := .seq s5Pre (.ifLtN 5947 5811 s5Body .skip)

section Exec

variable {I : Input} {W : ℕ}

theorem s5A_exec (c : Config) (hc : WordsBounded W c) {R U n : ℕ} (r0 : c.nreg 3100 = R)
    (r1 : c.nreg 3101 = U) (hn : c.nmem R = n) (w : U + 5 * n + R + 3 ≤ W) (w2 : 3 ≤ W) :
    ∃ c' t, Exec I W s5A c c' t ∧ t = 16 ∧ c'.nreg 5800 = n ∧ c'.nreg 5801 = R + 3 + n ∧
      c'.nreg 5802 = R + 3 + 2 * n ∧ c'.nreg 5803 = R + 3 + 4 * n ∧ c'.nreg 5804 = U ∧
      c'.nreg 5805 = R + 3 + 5 * n ∧ c'.nreg 5806 = 1 ∧ c'.nreg 5807 = 2 ∧
      c'.nreg 5808 = U + n ∧ c'.nreg 5809 = U + 2 * n ∧ c'.nreg 5814 = U + 3 * n ∧
      c'.nreg 5810 = U + 4 * n ∧ c'.nreg 6521 = 1 ∧
      (∀ x, (x < 5800 ∨ (5814 < x ∧ x < 5940) ∨ (5942 < x ∧ x < 6521) ∨ 6521 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5A
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r1, hn]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r0, r1, hn])
    try omega

theorem s5B_exec (c : Config) (hc : WordsBounded W c) {R n k b bfl : ℕ} (r0 : c.nreg 3100 = R)
    (r2 : c.nreg 3102 = k) (r00 : c.nreg 5800 = n) (r10 : c.nreg 5810 = b)
    (hb : c.nmem (R + 2) = bfl) (w : b + 38 * n + 2 * k + 11 + R ≤ W) (w2 : 100 ≤ W) :
    ∃ c' t, Exec I W s5B c c' t ∧ t = 12 ∧ c'.nreg 5870 = k ∧ c'.nreg 5915 = bfl ∧
      c'.nreg 5916 = b + 38 * n + 2 * k + 11 ∧ c'.nreg 6521 = 1 ∧
      (∀ x, x ≠ 5870 → x ≠ 5915 → x ≠ 5916 → x ≠ 6521 → (x < 5943 ∨ 5945 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5B
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r2, r00, r10]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r0, r2, r00, r10,
      show R + 2 = 2 + R by omega] at hb ⊢)
    try omega
  all_goals (rw [show R + 2 = 2 + R by omega] at hb; exact hb)

theorem s5Sv_exec (c : Config) (hc : WordsBounded W c) (w2 : 100 ≤ W) :
    ∃ c' t, Exec I W s5Sv c c' t ∧ t = 7 ∧ c'.nreg 3103 = c.nreg 5811 ∧
      c'.nreg 3104 = c.nreg 5914 ∧ c'.nreg 3105 = c.nreg 5913 ∧ c'.nreg 3106 = c.nreg 5910 ∧
      c'.nreg 3107 = c.nreg 5911 ∧ c'.nreg 3108 = c.nreg 5912 ∧ c'.nreg 5947 = 0 ∧
      (∀ x, (x < 3103 ∨ 3108 < x) → x ≠ 5947 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5Sv
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x a1 a2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

theorem s5K_exec (c : Config) (hc : WordsBounded W c) (w2 : 100 ≤ W) :
    ∃ c' t, Exec I W s5K c c' t ∧ t = 1 ∧ c'.nreg 6521 = 1 ∧
      (∀ x, x ≠ 6521 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5K
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, fun x a1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

theorem s5C_exec (c : Config) (hc : WordsBounded W c) {n b K : ℕ} (r00 : c.nreg 5800 = n)
    (r10 : c.nreg 5810 = b) (r910 : c.nreg 5910 = K) (w : b + 27 * n + 7 ≤ W)
    (w2 : 100 ≤ W) :
    ∃ c' t, Exec I W s5C c c' t ∧ t = 7 ∧ c'.nreg 5871 = K ∧
      c'.nreg 5872 = b + 27 * n + 7 ∧ c'.nreg 6521 = 1 ∧
      (∀ x, x ≠ 5871 → x ≠ 5872 → x ≠ 5943 → x ≠ 5946 → x ≠ 6521 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5C
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r10, r910]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r00, r10, r910])
    try omega

theorem s5D_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec I W s5D c c' t ∧ t = 1 ∧ c'.nreg 5850 = c.nreg 5912 ∧
      (∀ x, x ≠ 5850 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5D
  exec_block
  refine ⟨rfl, ?_, fun x a1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

/-- The registers written by `s5E1`. -/
def s5E1w : List ℕ := [4881, 4882, 4843, 4883, 4847, 4848, 4422, 4846, 4866, 4425, 5948, 4633,
  4426, 4849, 4404, 4885, 4886, 4887, 4888, 4824]

/-- The registers written by `s5E2`. -/
def s5E2w : List ℕ := [4840, 4841, 4842, 4420, 4421, 4423, 4424, 4400, 4401, 4402, 4403, 4760,
  4761, 4762, 4874, 4880, 4630, 4631, 4632, 4634]

/-- The registers written by `s5E3`. -/
def s5E3w : List ℕ := [4780, 4781, 4782, 4783, 4784, 4785, 4800, 4820, 4821, 4822, 4910, 4911,
  4912]

/-- The registers written by `s5E4`. -/
def s5E4w : List ℕ := [5200, 5202, 3109, 5949, 5950, 4936, 5830, 4937, 5951, 4955, 4956, 5952,
  5953, 5201, 5954, 5203]

theorem s5E1_exec (c : Config) (hc : WordsBounded W c) {b n' : ℕ} (r10 : c.nreg 5810 = b)
    (r11 : c.nreg 5811 = n') (w : b + 19 * n' + 3 ≤ W) (w2 : 100 ≤ W) :
    ∃ c' t, Exec I W s5E1 c c' t ∧ t = 24 ∧ c'.nreg 4881 = b ∧ c'.nreg 4882 = b + n' ∧
      c'.nreg 4843 = b + 2 * n' ∧ c'.nreg 4883 = b + 3 * n' ∧ c'.nreg 4847 = b + 4 * n' ∧
      c'.nreg 4848 = b + 5 * n' ∧ c'.nreg 4422 = b + 6 * n' ∧ c'.nreg 4846 = b + 7 * n' ∧
      c'.nreg 4866 = b + 8 * n' ∧ c'.nreg 4425 = b + 9 * n' ∧ c'.nreg 4633 = 1 ∧
      c'.nreg 4426 = b + 10 * n' + 1 ∧ c'.nreg 4849 = b + 13 * n' + 1 ∧
      c'.nreg 4404 = b + 14 * n' + 1 ∧ c'.nreg 4885 = b + 15 * n' + 2 ∧
      c'.nreg 4886 = b + 16 * n' + 2 ∧ c'.nreg 4887 = b + 17 * n' + 2 ∧
      c'.nreg 4888 = b + 18 * n' + 2 ∧ c'.nreg 4824 = b + 19 * n' + 3 ∧
      (∀ x, x ∉ s5E1w → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5E1
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r10, r11]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try (simp only [s5E1w, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx)
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r10, r11])
    try omega

theorem s5E2_exec (c : Config) (hc : WordsBounded W c) {b n' k : ℕ} (r10 : c.nreg 5810 = b)
    (r11 : c.nreg 5811 = n') (r2 : c.nreg 3102 = k) (q4882 : c.nreg 4882 = b + n')
    (q4848 : c.nreg 4848 = b + 5 * n') (q4846 : c.nreg 4846 = b + 7 * n')
    (q4866 : c.nreg 4866 = b + 8 * n') (q4425 : c.nreg 4425 = b + 9 * n')
    (q4426 : c.nreg 4426 = b + 10 * n' + 1) (q4849 : c.nreg 4849 = b + 13 * n' + 1)
    (q4847 : c.nreg 4847 = b + 4 * n') (q4887 : c.nreg 4887 = b + 17 * n' + 2)
    (q4888 : c.nreg 4888 = b + 18 * n' + 2) :
    ∃ c' t, Exec I W s5E2 c c' t ∧ t = 20 ∧ c'.nreg 4840 = n' ∧ c'.nreg 4841 = b ∧
      c'.nreg 4842 = b + n' ∧ c'.nreg 4420 = n' ∧ c'.nreg 4421 = b + 5 * n' ∧
      c'.nreg 4423 = b + 7 * n' ∧ c'.nreg 4424 = b + 8 * n' ∧ c'.nreg 4400 = n' ∧
      c'.nreg 4401 = b + 9 * n' ∧ c'.nreg 4402 = b + 10 * n' + 1 ∧
      c'.nreg 4403 = b + 13 * n' + 1 ∧ c'.nreg 4760 = n' ∧ c'.nreg 4761 = b + 4 * n' ∧
      c'.nreg 4762 = b + 13 * n' + 1 ∧ c'.nreg 4874 = k ∧ c'.nreg 4880 = n' ∧
      c'.nreg 4630 = n' ∧ c'.nreg 4631 = b + 13 * n' + 1 ∧ c'.nreg 4632 = b + 17 * n' + 2 ∧
      c'.nreg 4634 = b + 18 * n' + 2 ∧
      (∀ x, x ∉ s5E2w → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5E2
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try (simp only [s5E2w, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx)
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r10, r11, r2, q4882, q4848, q4846, q4866,
      q4425, q4426, q4849, q4847, q4887, q4888])
    try omega

theorem s5E3_exec (c : Config) (hc : WordsBounded W c) {b n' A W₀ : ℕ} (r10 : c.nreg 5810 = b)
    (r11 : c.nreg 5811 = n') (r911 : c.nreg 5911 = A) (r912 : c.nreg 5912 = W₀)
    (q4849 : c.nreg 4849 = b + 13 * n' + 1) (q4888 : c.nreg 4888 = b + 18 * n' + 2)
    (q4824 : c.nreg 4824 = b + 19 * n' + 3) :
    ∃ c' t, Exec I W s5E3 c c' t ∧ t = 13 ∧ c'.nreg 4780 = n' ∧ c'.nreg 4781 = b ∧
      c'.nreg 4782 = b + 13 * n' + 1 ∧ c'.nreg 4783 = b + 18 * n' + 2 ∧ c'.nreg 4784 = A ∧
      c'.nreg 4785 = W₀ ∧ c'.nreg 4800 = n' ∧ c'.nreg 4820 = n' ∧ c'.nreg 4821 = b ∧
      c'.nreg 4822 = b + 13 * n' + 1 ∧ c'.nreg 4910 = n' ∧ c'.nreg 4911 = b + 19 * n' + 3 ∧
      c'.nreg 4912 = b ∧
      (∀ x, x ∉ s5E3w → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5E3
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try (simp only [s5E3w, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx)
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r10, r11, r911, r912, q4849, q4888,
      q4824])
    try omega

theorem s5E4_exec (c : Config) (hc : WordsBounded W c) {n b n' k SGb Bz W₀ : ℕ}
    (r00 : c.nreg 5800 = n) (r10 : c.nreg 5810 = b) (r11 : c.nreg 5811 = n')
    (r2 : c.nreg 3102 = k) (r14 : c.nreg 5814 = SGb) (r58 : c.nreg 5858 = Bz)
    (r912 : c.nreg 5912 = W₀)
    (w : b + 38 * n + 5 * k + 13 + 18 + 7 * n' + 1 + n' + n' + Bz + 25 * n' + 3 * W₀ + 15 +
      13 * n' ≤ W) (w2 : 100 ≤ W) :
    ∃ c' t, Exec I W s5E4 c c' t ∧ t = 35 ∧ c'.nreg 5200 = SGb ∧ c'.nreg 5202 = Bz ∧
      c'.nreg 3109 = Bz ∧ c'.nreg 4936 = b + 38 * n + 5 * k + 13 ∧
      c'.nreg 5830 = b + 38 * n + 5 * k + 13 ∧ c'.nreg 4937 = b + 38 * n + 5 * k + 13 + 18 ∧
      c'.nreg 4955 = b + 38 * n + 5 * k + 13 + 18 + 7 * n' + 1 ∧
      c'.nreg 4956 = b + 38 * n + 5 * k + 13 + 18 + 7 * n' + 1 + n' ∧
      c'.nreg 5201 = b + 38 * n + 5 * k + 13 + 18 + 7 * n' + 1 + n' + n' + Bz + 25 * n' +
        3 * W₀ + 15 ∧
      c'.nreg 5203 = b + 38 * n + 5 * k + 13 + 18 + 7 * n' + 1 + n' + n' + Bz + 25 * n' +
        3 * W₀ + 15 + 13 * n' ∧
      (∀ x, x ∉ s5E4w → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold s5E4
  exec_block
  all_goals try ((try config_simp); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r00, r10, r11, r2, r14, r58, r912]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try (simp only [s5E4w, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx)
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r00, r10, r11, r2, r14, r58, r912])
    try omega

/-- **`LvRegs` and the bases of `scProg`** after `s5E1 ; s5E2 ; s5E3 ; s5E4`. -/
theorem s5E_exec (c : Config) (hc : WordsBounded W c) {n b n' k SGb Bz A W₀ : ℕ}
    (r00 : c.nreg 5800 = n) (r10 : c.nreg 5810 = b) (r11 : c.nreg 5811 = n')
    (r2 : c.nreg 3102 = k) (r14 : c.nreg 5814 = SGb) (r58 : c.nreg 5858 = Bz)
    (r911 : c.nreg 5911 = A) (r912 : c.nreg 5912 = W₀)
    (w : b + 38 * n + 5 * k + 13 + 18 + 7 * n' + 1 + n' + n' + Bz + 25 * n' + 3 * W₀ + 15 +
      13 * n' ≤ W) (w1 : b + 19 * n' + 3 ≤ W) (w2 : 100 ≤ W) :
    ∃ c' t, Exec I W (.seq s5E1 (.seq s5E2 (.seq s5E3 s5E4))) c c' t ∧ t = 92 ∧
      LvRegs c' n' b k A W₀ ∧ c'.nreg 5200 = SGb ∧ c'.nreg 5202 = Bz ∧
      c'.nreg 3109 = Bz ∧ c'.nreg 4936 = b + 38 * n + 5 * k + 13 ∧
      c'.nreg 5830 = b + 38 * n + 5 * k + 13 ∧ c'.nreg 4937 = b + 38 * n + 5 * k + 13 + 18 ∧
      c'.nreg 4955 = b + 38 * n + 5 * k + 13 + 18 + 7 * n' + 1 ∧
      c'.nreg 4956 = b + 38 * n + 5 * k + 13 + 18 + 7 * n' + 1 + n' ∧
      c'.nreg 5201 = b + 38 * n + 5 * k + 13 + 18 + 7 * n' + 1 + n' + n' + Bz + 25 * n' +
        3 * W₀ + 15 ∧
      c'.nreg 5203 = b + 38 * n + 5 * k + 13 + 18 + 7 * n' + 1 + n' + n' + Bz + 25 * n' +
        3 * W₀ + 15 + 13 * n' ∧
      (∀ x, x ∉ s5E1w → x ∉ s5E2w → x ∉ s5E3w → x ∉ s5E4w → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a4881, a4882, a4843, a4883, a4847, a4848, a4422, a4846, a4866, a4425,
    a4633, a4426, a4849, a4404, a4885, a4886, a4887, a4888, a4824, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    s5E1_exec (I := I) c hc r10 r11 w1 w2
  obtain ⟨c₂, t₂, e₂, ht₂, b4840, b4841, b4842, b4420, b4421, b4423, b4424, b4400, b4401, b4402,
    b4403, b4760, b4761, b4762, b4874, b4880, b4630, b4631, b4632, b4634, f₂, m₂, rr₂, rm₂, o₂⟩ :=
    s5E2_exec (I := I) c₁ e₁.wb_right ((f₁ 5810 (by decide)).trans r10)
      ((f₁ 5811 (by decide)).trans r11) ((f₁ 3102 (by decide)).trans r2) a4882 a4848 a4846
      a4866 a4425 a4426 a4849 a4847 a4887 a4888
  obtain ⟨c₃, t₃, e₃, ht₃, d4780, d4781, d4782, d4783, d4784, d4785, d4800, d4820, d4821, d4822,
    d4910, d4911, d4912, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    s5E3_exec (I := I) c₂ e₂.wb_right (((f₂ 5810 (by decide)).trans (f₁ 5810 (by decide))).trans r10)
      (((f₂ 5811 (by decide)).trans (f₁ 5811 (by decide))).trans r11)
      (((f₂ 5911 (by decide)).trans (f₁ 5911 (by decide))).trans r911)
      (((f₂ 5912 (by decide)).trans (f₁ 5912 (by decide))).trans r912)
      ((f₂ 4849 (by decide)).trans a4849) ((f₂ 4888 (by decide)).trans a4888)
      ((f₂ 4824 (by decide)).trans a4824)
  have g : ∀ x, x ∉ s5E1w → x ∉ s5E2w → x ∉ s5E3w → c₃.nreg x = c.nreg x := fun x h1 h2 h3 => by
    rw [f₃ x h3, f₂ x h2, f₁ x h1]
  obtain ⟨c₄, t₄, e₄, ht₄, v5200, v5202, v3109, v4936, v5830, v4937, v4955, v4956, v5201, v5203,
    f₄, m₄, rr₄, rm₄, o₄⟩ :=
    s5E4_exec (I := I) c₃ e₃.wb_right ((g 5800 (by decide) (by decide) (by decide)).trans r00)
      ((g 5810 (by decide) (by decide) (by decide)).trans r10)
      ((g 5811 (by decide) (by decide) (by decide)).trans r11)
      ((g 3102 (by decide) (by decide) (by decide)).trans r2)
      ((g 5814 (by decide) (by decide) (by decide)).trans r14)
      ((g 5858 (by decide) (by decide) (by decide)).trans r58)
      ((g 5912 (by decide) (by decide) (by decide)).trans r912) w w2
  have t1 : ∀ x, x ∉ s5E2w → x ∉ s5E3w → x ∉ s5E4w → c₄.nreg x = c₁.nreg x := fun x h2 h3 h4 => by
    rw [f₄ x h4, f₃ x h3, f₂ x h2]
  have t2 : ∀ x, x ∉ s5E3w → x ∉ s5E4w → c₄.nreg x = c₂.nreg x := fun x h3 h4 => by
    rw [f₄ x h4, f₃ x h3]
  have t3 : ∀ x, x ∉ s5E4w → c₄.nreg x = c₃.nreg x := fun x h4 => f₄ x h4
  have hL : LvRegs c₄ n' b k A W₀ := {
    p0 := by rw [t2 4840 (by decide) (by decide)]; assumption
    p1 := by rw [t2 4841 (by decide) (by decide)]; assumption
    p2 := by rw [t2 4842 (by decide) (by decide)]; assumption
    p3 := by rw [t1 4843 (by decide) (by decide) (by decide)]; assumption
    p6 := by rw [t1 4846 (by decide) (by decide) (by decide)]; assumption
    p7 := by rw [t1 4847 (by decide) (by decide) (by decide)]; assumption
    p8 := by rw [t1 4848 (by decide) (by decide) (by decide)]; assumption
    p9 := by rw [t1 4849 (by decide) (by decide) (by decide)]; assumption
    p10 := by rw [t1 4866 (by decide) (by decide) (by decide)]; assumption
    r0 := by rw [t2 4420 (by decide) (by decide)]; assumption
    r1 := by rw [t2 4421 (by decide) (by decide)]; assumption
    r2 := by rw [t1 4422 (by decide) (by decide) (by decide)]; assumption
    r3 := by rw [t2 4423 (by decide) (by decide)]; assumption
    r4 := by rw [t2 4424 (by decide) (by decide)]; assumption
    r5 := by rw [t1 4425 (by decide) (by decide) (by decide)]; assumption
    r6 := by rw [t1 4426 (by decide) (by decide) (by decide)]; assumption
    s0 := by rw [t2 4400 (by decide) (by decide)]; assumption
    s1 := by rw [t2 4401 (by decide) (by decide)]; assumption
    s2 := by rw [t2 4402 (by decide) (by decide)]; assumption
    s3 := by rw [t2 4403 (by decide) (by decide)]; assumption
    s4 := by rw [t1 4404 (by decide) (by decide) (by decide)]; assumption
    u0 := by rw [t2 4760 (by decide) (by decide)]; assumption
    u1 := by rw [t2 4761 (by decide) (by decide)]; assumption
    u2 := by rw [t2 4762 (by decide) (by decide)]; assumption
    v4 := by rw [t2 4874 (by decide) (by decide)]; assumption
    l0 := by rw [t2 4880 (by decide) (by decide)]; assumption
    l1 := by rw [t1 4881 (by decide) (by decide) (by decide)]; assumption
    l2 := by rw [t1 4882 (by decide) (by decide) (by decide)]; assumption
    l3 := by rw [t1 4883 (by decide) (by decide) (by decide)]; assumption
    l5 := by rw [t1 4885 (by decide) (by decide) (by decide)]; assumption
    l6 := by rw [t1 4886 (by decide) (by decide) (by decide)]; assumption
    l7 := by rw [t1 4887 (by decide) (by decide) (by decide)]; assumption
    l8 := by rw [t1 4888 (by decide) (by decide) (by decide)]; assumption
    a0 := by rw [t2 4630 (by decide) (by decide)]; assumption
    a1 := by rw [t2 4631 (by decide) (by decide)]; assumption
    a2 := by rw [t2 4632 (by decide) (by decide)]; assumption
    a3 := by rw [t1 4633 (by decide) (by decide) (by decide)]; assumption
    a4 := by rw [t2 4634 (by decide) (by decide)]; assumption
    h0 := by rw [t3 4780 (by decide)]; assumption
    h1 := by rw [t3 4781 (by decide)]; assumption
    h2 := by rw [t3 4782 (by decide)]; assumption
    h3 := by rw [t3 4783 (by decide)]; assumption
    h4 := by rw [t3 4784 (by decide)]; assumption
    h5 := by rw [t3 4785 (by decide)]; assumption
    c0 := by rw [t3 4800 (by decide)]; assumption
    k0 := by rw [t3 4820 (by decide)]; assumption
    k1 := by rw [t3 4821 (by decide)]; assumption
    k2 := by rw [t3 4822 (by decide)]; assumption
    k4 := by rw [t1 4824 (by decide) (by decide) (by decide)]; assumption
    y0 := by rw [t3 4910 (by decide)]; assumption
    y1 := by rw [t3 4911 (by decide)]; assumption
    y2 := by rw [t3 4912 (by decide)]; assumption }
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, hL, v5200, v5202, v3109, v4936, v5830,
    v4937, v4955, v4956, v5201, v5203, fun x h1 h2 h3 h4 => by rw [f₄ x h4, g x h1 h2 h3],
    by rw [m₄, m₃, m₂, m₁], by rw [rr₄, rr₃, rr₂, rr₁], by rw [rm₄, rm₃, rm₂, rm₁],
    by rw [o₄, o₃, o₂, o₁]⟩

end Exec

end MfDrv

end BKMNW

end PlanarFlow
