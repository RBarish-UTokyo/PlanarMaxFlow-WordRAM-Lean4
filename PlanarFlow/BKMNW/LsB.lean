module

public import PlanarFlow.BKMNW.LsA

/-!
# `sepL`: the path's darts after stage 5 (the three branches)

After stage 5 the path `ρ` of the certificate is on the machine in three ways:

* **Miller's case** (core's piece map nonempty, `4900 = 0`): its darts as `1 +` core indices at
  `Hb' + 6 #B` (`PathNHD`), `Hb' + 6 #B = U + 42 n + 5 k + 40 #B + Bz + 3 W₀ + 47`;
* **the cut case** (nonempty, `4900 = 2`): a point at the tail of the core dart `r4902`;
* **the empty case** (`#B = 0`, `pemptyD`): a point at the tail of `pick (pdarts P)` (reversed if
  that tail is in `Q`), or of `pick P` when the piece map is empty.

`lsB` writes the path uniformly for the later stages: `n'` (register `8557`), the core indices
`IX'` at `E` (`n'` cells) and the darts `PD'` at `E + n` (`n'` cells, `PathPD`'s shape):

* nonempty: `n' = #B`, `IX' = IX` (copied from `U + 2 n`); Miller: `PD'` copied from
  `Hb' + 6 #B`; cut: `PD' = [r4902 + 1, 0, …, 0]`;
* empty: `n' = 1`, `IX' = [i*]`, `PD' = [1]`, `i* = q · RP[i₀] + (1 - q) · i₀` with
  `i₀ = FX[0] · [0 < m]`, `q = (VP[i₀] mod 2) · [0 < m]`.

Also saved: `8558 = #B`, `8559 = [holeStep]`, `8560 = K`, `8561 = A`, `8569 = U + 2 n`,
`8571 = E + n`.
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

/-- The saves and the bases. -/
def lsB0 : Stmt := block [.copyN 8558 3103, .copyN 8559 3105, .copyN 8560 3106,
  .copyN 8561 3107, .addN 8571 8555 8553, .constN 8564 2, .mulN 8569 8564 8553,
  .addN 8569 8569 8556, .constN 6521 1]

/-- `n' = #B`. -/
def lsBn1 : Stmt := block [.copyN 8557 3103]

/-- The base of Miller's path darts: `U + 42 n + 5 k + 40 #B + Bz + 3 W₀ + 47`. -/
def lsBm : Stmt := block [.constN 8564 42, .mulN 8570 8564 8553, .addN 8570 8570 8556,
  .constN 8564 5, .mulN 8572 8564 8551, .addN 8570 8570 8572, .constN 8564 40,
  .mulN 8572 8564 8558, .addN 8570 8570 8572, .addN 8570 8570 3109, .addN 8570 8570 3108,
  .addN 8570 8570 3108, .addN 8570 8570 3108, .constN 8564 47, .addN 8570 8570 8564]

/-- The cut vertex: `PD'[0] := r4902 + 1`. -/
def lsBc : Stmt := block [.constN 8564 1, .addN 8573 4902 8564, .storeN 8571 8573]

/-- The empty case, part 1: `n' = 1`, `i₀ = FX[0] · [0 < m]` (`8576`), `[0 < m]` (`8577`). -/
def lsBe1 : Stmt := block [.constN 8557 1, .constN 8564 3, .addN 8575 8552 8564,
  .constN 8564 6, .mulN 8576 8564 8553, .addN 8575 8575 8576, .loadN 8576 8575,
  .constN 8564 1, .subN 8577 8564 8550, .subN 8577 8564 8577, .mulN 8576 8576 8577]

/-- The empty case, part 2: `q = (VP[i₀] mod 2) · [0 < m]` (`8578`). -/
def lsBe2 : Stmt := block [.constN 8564 3, .addN 8578 8552 8564, .constN 8564 4,
  .mulN 8579 8564 8553, .addN 8578 8578 8579, .addN 8578 8578 8576, .loadN 8578 8578,
  .constN 8564 2, .modN 8578 8578 8564, .mulN 8578 8578 8577]

/-- The empty case, part 3: `i* = q · RP[i₀] + (1 - q) · i₀` (`8574`). -/
def lsBe3 : Stmt := block [.constN 8564 3, .addN 8579 8552 8564, .addN 8579 8579 8553,
  .addN 8579 8579 8576, .loadN 8579 8579, .mulN 8579 8579 8578, .constN 8564 1,
  .subN 8580 8564 8578, .mulN 8580 8580 8576, .addN 8574 8579 8580]

/-- The empty case, part 4: `IX'[0] := i*`, `PD'[0] := 1`. -/
def lsBe4 : Stmt := block [.storeN 8555 8574, .constN 8564 1, .storeN 8571 8564]

/-- The empty case. -/
def lsBe : Stmt := .seq lsBe1 (.seq lsBe2 (.seq lsBe3 lsBe4))

/-- Miller's case: copy the darts. -/
def lsMil : Stmt := .seq lsBm (lrCp 8557 8570 8571)

/-- The cut case. -/
def lsCut : Stmt := .seq (zfill 8557 8571) lsBc

/-- The nonempty case. -/
def lsBne : Stmt := .seq lsBn1 (.seq (lrCp 8557 8569 8555) (.ifLtN 8568 4900 lsCut lsMil))

/-- **The path after stage 5** (see the module docstring). -/
def lsB : Stmt := .seq lsB0 (.ifLtN 8568 3103 lsBne lsBe)

/-- The index of the empty case's dart. -/
def lsIs (f v p m : ℕ) : ℕ :=
  v % 2 * (1 - (1 - m)) * p + (1 - v % 2 * (1 - (1 - m))) * (f * (1 - (1 - m)))

section Exec

variable {I : Input} {W : ℕ}

theorem lsB0_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb : ℕ} (hR : LsR c m k R n Sb)
    (w : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n ≤ W) (w2 : 40 ≤ W) :
    ∃ c' t, Exec I W lsB0 c c' t ∧ t = 9 ∧ LsR c' m k R n Sb ∧
      c'.nreg 8558 = c.nreg 3103 ∧ c'.nreg 8559 = c.nreg 3105 ∧ c'.nreg 8560 = c.nreg 3106 ∧
      c'.nreg 8561 = c.nreg 3107 ∧ c'.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n ∧
      c'.nreg 8569 = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n ∧ c'.nreg 6521 = 1 ∧
      (∀ x, (x < 6521 ∨ (6521 < x ∧ x < 8557) ∨ x = 8568 ∨ 8571 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hR.r53; have := hR.r55; have := hR.r56
  unfold lsB0
  exec_block
  all_goals try (config_simp; (try simp only [hR.r53, hR.r55, hR.r56]); omega)
  refine ⟨rfl, hR.congr fun x hx => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl,
    rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, hR.r53, hR.r55, hR.r56])
    try omega

theorem lsBn1_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec I W lsBn1 c c' t ∧ t = 1 ∧ c'.nreg 8557 = c.nreg 3103 ∧
      (∀ x, x ≠ 8557 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 3103
  unfold lsBn1
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])

theorem lsBm_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb nB : ℕ}
    (hR : LsR c m k R n Sb) (r58 : c.nreg 8558 = nB)
    (w : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 42 * n + 5 * k + 40 * nB +
      c.nreg 3109 + 3 * c.nreg 3108 + 47 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsBm c c' t ∧ t = 15 ∧
      c'.nreg 8570 = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 42 * n + 5 * k + 40 * nB +
        c.nreg 3109 + 3 * c.nreg 3108 + 47 ∧
      (∀ x, (x < 8564 ∨ (8564 < x ∧ x < 8570) ∨ x = 8571 ∨ 8572 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hR.r53; have := hR.r51; have := hR.r56
  unfold lsBm
  exec_block
  all_goals try (config_simp; (try simp only [hR.r53, hR.r51, hR.r56, r58]); omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, hR.r53, hR.r51, hR.r56, r58])
    try omega

theorem lsBc_exec (c : Config) (hc : WordsBounded W c) {a v : ℕ} (r71 : c.nreg 8571 = a)
    (r02 : c.nreg 4902 = v) (wv : v + 1 ≤ W) (wa : a ≤ W) :
    ∃ c' t, Exec I W lsBc c c' t ∧ t = 3 ∧ c'.nmem = upd c.nmem a (v + 1) ∧
      (∀ x, x ≠ 8564 → x ≠ 8573 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lsBc
  exec_block
  all_goals try (config_simp; (try simp only [r71, r02]); omega)
  refine ⟨rfl, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp (disch := omega) only [upd_other, upd_same, r71, r02]
  · config_simp; simp (disch := omega) only [upd_other]

theorem lsBe1_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb f : ℕ}
    (hR : LsR c m k R n Sb) (hf : c.nmem (R + 3 + 6 * n) = f) (wR : R + 3 + 6 * n ≤ W)
    (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsBe1 c c' t ∧ t = 11 ∧ c'.nreg 8557 = 1 ∧
      c'.nreg 8576 = f * (1 - (1 - m)) ∧ c'.nreg 8577 = 1 - (1 - m) ∧
      (∀ x, (x < 8557 ∨ (8557 < x ∧ x < 8564) ∨ (8564 < x ∧ x < 8575) ∨ 8577 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hR.r50; have := hR.r52; have := hR.r53
  have bf := hc.2 (R + 3 + 6 * n)
  rw [hf] at bf
  have h3 : f * (1 - (1 - m)) ≤ f := by
    have h1 : 1 - (1 - m) ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h | h <;> rw [h] <;> simp
  have e : R + 3 + 6 * n = R + 3 + 6 * n := rfl
  unfold lsBe1
  exec_block
  all_goals try (config_simp; (try simp only [hR.r50, hR.r52, hR.r53, hf]); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, hR.r50, hR.r52, hR.r53, hf]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, hR.r50, hR.r52, hR.r53, hf])
    try omega

theorem lsBe2_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb i0 b v : ℕ}
    (hR : LsR c m k R n Sb) (r76 : c.nreg 8576 = i0) (r77 : c.nreg 8577 = b) (hb : b ≤ 1)
    (hv : c.nmem (R + 3 + 4 * n + i0) = v) (wR : R + 3 + 4 * n + i0 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsBe2 c c' t ∧ t = 10 ∧ c'.nreg 8578 = v % 2 * b ∧
      (∀ x, (x < 8564 ∨ (8564 < x ∧ x < 8578) ∨ 8579 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hR.r52; have := hR.r53
  have bv := hc.2 (R + 3 + 4 * n + i0)
  rw [hv] at bv
  have h2 : v % 2 * b ≤ 1 := by
    have : v % 2 < 2 := Nat.mod_lt _ (by norm_num)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h <;> rw [h] <;> omega
  have hv2 : v % 2 ≤ W := (Nat.mod_le v 2).trans bv
  unfold lsBe2
  exec_block
  all_goals try (config_simp; (try simp only [hR.r52, hR.r53, r76, r77, hv]); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, hR.r52, hR.r53, r76, r77, hv]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, hR.r52, hR.r53, r76, r77, hv])
    try omega

theorem lsBe3_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb i0 q p : ℕ}
    (hR : LsR c m k R n Sb) (r76 : c.nreg 8576 = i0) (r78 : c.nreg 8578 = q) (hq : q ≤ 1)
    (hp : c.nmem (R + 3 + n + i0) = p) (wR : R + 3 + n + i0 ≤ W) (wi : i0 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsBe3 c c' t ∧ t = 10 ∧ c'.nreg 8574 = q * p + (1 - q) * i0 ∧
      (∀ x, (x < 8564 ∨ (8564 < x ∧ x < 8574) ∨ (8574 < x ∧ x < 8579) ∨ 8580 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hR.r52; have := hR.r53
  have bp := hc.2 (R + 3 + n + i0)
  rw [hp] at bp
  have h4 : p * q ≤ W := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hq with h | h <;> rw [h] <;> simp <;> omega
  have h5 : (1 - q) * i0 ≤ W := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hq with h | h <;> rw [h] <;> simp <;> omega
  have h6 : p * q + (1 - q) * i0 ≤ W := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hq with h | h <;> rw [h] <;> simp <;> omega
  unfold lsBe3
  exec_block
  all_goals try (config_simp; (try simp only [hR.r52, hR.r53, r76, r78, hp]); omega)
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, hR.r52, hR.r53, r76, r78, hp]; omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, hR.r52, hR.r53, r76, r78, hp])
    try (rw [Nat.mul_comm p q])
    try omega

theorem lsBe4_exec (c : Config) (hc : WordsBounded W c) {a b : ℕ} (r55 : c.nreg 8555 = a)
    (r71 : c.nreg 8571 = b) (wa : a ≤ W) (wb : b ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsBe4 c c' t ∧ t = 3 ∧
      c'.nmem = upd (upd c.nmem a (c.nreg 8574)) b 1 ∧
      (∀ x, x ≠ 8564 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 8574
  unfold lsBe4
  exec_block
  all_goals try (config_simp; (try simp only [r55, r71]); omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r55, r71])

end Exec

end MfDrv

end BKMNW

end PlanarFlow
