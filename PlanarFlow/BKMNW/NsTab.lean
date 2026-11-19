module

public import PlanarFlow.BKMNW.LinLoops
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.Ring

/-!
# The grouping of the darts by the ends of their dual darts, on the machine

The kept darts `repsN` and the least lengths `minLen` of a negSSSP call are decided per group of
darts with the same (tail face, head face). The groups are found in linear time with a
**direct-address table** of `2 (m + 1)²` cells inside the zero memory below `Wz` (only the
`2 m` cells of the keys that occur are touched, and they are cleared again): the key of dart
`i` is `(LAB[i]) · (m + 1) + LAB[RV[i]]` (`LAB = label + 1`), its two cells hold the maxima over
the group of `m - min(i, RV[i])` (so the edge key is least exactly at the dart with
`v ≥ T[2 key]`) and of `Zl - LN[i]` (so the least length is `Zl - T[2 key + 1]`). All bodies
are straight-line (maxima by `t + (v - t)`, flags by truncated subtractions).

* pass 1 `tbL1` (`tb1`): the maxima; **`tbL1_exec`**;
* pass 2 `tbL2` (`tb2`): `KEEP[i]` (`1` iff not a loop of the dual and the maximum reached),
  `MLN[i] = Zl - T[2 key + 1]`, the sum `Σ (MLN - K) + (K - MLN)` in `r7525`; **`tbL2_exec`**;
* pass 3 `tbL3` (`tb3`): the touched cells cleared; **`tbL3_exec`**;
* **`tbProg`** `= tbL1 ; tbL2 ; tbL3`, **`tbProg_exec`**: within `91 m + 9` steps, the arrays
  `KEEP`, `MLN` and the sum, all other memory kept when the table was zero.

Registers: `7500 = m`, `7501 = RVb`, `7503 = LNb`, `7504 = K`, `7512 = LABb`, `7514 = KPb`,
`7515 = MLb`, `7519 = Tb`, `7520 = Q = m + 1`, `7521 = Zl`; written: `7522 = 1`, `7524 = 0`,
`7525` (the sum), `7530` (the index), scratch `7531 … 7548`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The pure description -/

/-- The key of dart `x`. -/
def keyG (lab rv : ℕ → ℕ) (Q x : ℕ) : ℕ := (lab x + 1) * Q + (lab (rv x) + 1)

/-- The darts below `i` with the key of `x`. -/
def grpP (lab rv : ℕ → ℕ) (Q i x : ℕ) : Finset ℕ :=
  (range i).filter fun j => keyG lab rv Q j = keyG lab rv Q x

/-- The value maximized for the kept dart: `m - min(j, rv j)`. -/
def vE (rv : ℕ → ℕ) (m j : ℕ) : ℕ := m - (j - (j - rv j))

/-- The value maximized for the least length: `Zl - ln j`. -/
def vL (ln : ℕ → ℕ) (Zl j : ℕ) : ℕ := Zl - ln j

/-- The keep flag computed by pass 2. -/
def kflag (xa xb t0 v : ℕ) : ℕ := (1 - (1 - ((xa - xb) + (xb - xa)))) - (1 - (1 - (t0 - v)))

lemma kflag_eq (xa xb t0 v : ℕ) : kflag xa xb t0 v = if xa ≠ xb ∧ t0 ≤ v then 1 else 0 := by
  unfold kflag; split_ifs with h <;> omega

/-- The term of the sum of pass 2. -/
def lterm (K x : ℕ) : ℕ := (x - K) + (K - x)

lemma grpP_zero (lab rv : ℕ → ℕ) (Q x : ℕ) : grpP lab rv Q 0 x = ∅ := by simp [grpP]

lemma grpP_succ (lab rv : ℕ → ℕ) (Q i x : ℕ) :
    grpP lab rv Q (i + 1) x = if keyG lab rv Q i = keyG lab rv Q x then
      insert i (grpP lab rv Q i x) else grpP lab rv Q i x := by
  unfold grpP
  rw [range_add_one, filter_insert]

lemma key_lt {lab rv : ℕ → ℕ} {m x : ℕ} (h1 : lab x < m) (h2 : lab (rv x) < m) :
    keyG lab rv (m + 1) x + 1 ≤ (m + 1) * (m + 1) := by
  unfold keyG
  have : (lab x + 1) * (m + 1) ≤ m * (m + 1) := Nat.mul_le_mul_right _ (by omega)
  have e : (m + 1) * (m + 1) = m * (m + 1) + (m + 1) := by ring
  omega

lemma max_eq' (t v : ℕ) : t + (v - t) = max t v := by omega

/-! ### Pass 1: the maxima -/

/-- One dart of pass 1. -/
def tb1 : Stmt := block [
  .addN 7531 7512 7530, .loadN 7532 7531,
  .addN 7531 7501 7530, .loadN 7533 7531,
  .addN 7531 7512 7533, .loadN 7534 7531,
  .mulN 7535 7532 7520, .addN 7535 7535 7534,
  .addN 7536 7519 7535, .addN 7536 7536 7535, .addN 7543 7536 7522,
  .subN 7537 7530 7533, .subN 7537 7530 7537, .subN 7538 7500 7537,
  .addN 7531 7503 7530, .loadN 7541 7531, .subN 7542 7521 7541,
  .loadN 7539 7536, .loadN 7544 7543,
  .subN 7540 7538 7539, .addN 7539 7539 7540, .storeN 7536 7539,
  .subN 7540 7542 7544, .addN 7544 7544 7540, .storeN 7543 7544,
  .addN 7530 7530 7522]

/-- Pass 1. -/
def tbL1 : Stmt := .seq (block [.constN 7522 1, .constN 7530 0]) (.whileLtN 7530 7500 tb1)

/-- One dart of pass 2. -/
def tb2 : Stmt := block [
  .addN 7531 7512 7530, .loadN 7532 7531,
  .addN 7531 7501 7530, .loadN 7533 7531,
  .addN 7531 7512 7533, .loadN 7534 7531,
  .mulN 7535 7532 7520, .addN 7535 7535 7534,
  .addN 7536 7519 7535, .addN 7536 7536 7535, .addN 7543 7536 7522,
  .subN 7537 7530 7533, .subN 7537 7530 7537, .subN 7538 7500 7537,
  .loadN 7539 7536, .loadN 7544 7543,
  .subN 7545 7521 7544, .addN 7531 7515 7530, .storeN 7531 7545,
  .subN 7546 7532 7534, .subN 7547 7534 7532, .addN 7546 7546 7547,
  .subN 7547 7522 7546, .subN 7546 7522 7547,
  .subN 7547 7539 7538, .subN 7547 7522 7547,
  .subN 7548 7522 7547, .subN 7546 7546 7548,
  .addN 7531 7514 7530, .storeN 7531 7546,
  .subN 7547 7545 7504, .subN 7548 7504 7545, .addN 7547 7547 7548, .addN 7525 7525 7547,
  .addN 7530 7530 7522]

/-- Pass 2. -/
def tbL2 : Stmt :=
  .seq (block [.constN 7522 1, .constN 7525 0, .constN 7530 0]) (.whileLtN 7530 7500 tb2)

/-- One dart of pass 3. -/
def tb3 : Stmt := block [
  .addN 7531 7512 7530, .loadN 7532 7531,
  .addN 7531 7501 7530, .loadN 7533 7531,
  .addN 7531 7512 7533, .loadN 7534 7531,
  .mulN 7535 7532 7520, .addN 7535 7535 7534,
  .addN 7536 7519 7535, .addN 7536 7536 7535, .addN 7543 7536 7522,
  .storeN 7536 7524, .storeN 7543 7524,
  .addN 7530 7530 7522]

/-- Pass 3. -/
def tbL3 : Stmt :=
  .seq (block [.constN 7522 1, .constN 7524 0, .constN 7530 0]) (.whileLtN 7530 7500 tb3)

/-- **The grouping**: the three passes. -/
def tbProg : Stmt := .seq tbL1 (.seq tbL2 tbL3)

variable {P : Input} {W : ℕ}

/-- The registers of the passes. -/
def TbRegs (c : Config) (m RVb LNb K LABb KPb MLb Tb Zl : ℕ) : Prop :=
  c.nreg 7500 = m ∧ c.nreg 7501 = RVb ∧ c.nreg 7503 = LNb ∧ c.nreg 7504 = K ∧
    c.nreg 7512 = LABb ∧ c.nreg 7514 = KPb ∧ c.nreg 7515 = MLb ∧ c.nreg 7519 = Tb ∧
    c.nreg 7520 = m + 1 ∧ c.nreg 7521 = Zl

lemma TbRegs.of {c d : Config} {m RVb LNb K LABb KPb MLb Tb Zl : ℕ}
    (h : TbRegs c m RVb LNb K LABb KPb MLb Tb Zl)
    (hd : ∀ r, r < 7522 → d.nreg r = c.nreg r) :
    TbRegs d m RVb LNb K LABb KPb MLb Tb Zl := by
  obtain ⟨a0, a1, a3, a4, a12, a14, a15, a19, a20, a21⟩ := h
  exact ⟨by rw [hd _ (by omega), a0], by rw [hd _ (by omega), a1], by rw [hd _ (by omega), a3],
    by rw [hd _ (by omega), a4], by rw [hd _ (by omega), a12], by rw [hd _ (by omega), a14],
    by rw [hd _ (by omega), a15], by rw [hd _ (by omega), a19], by rw [hd _ (by omega), a20],
    by rw [hd _ (by omega), a21]⟩

lemma TbRegs.w {c : Config} {m RVb LNb K LABb KPb MLb Tb Zl : ℕ}
    (h : TbRegs c m RVb LNb K LABb KPb MLb Tb Zl) : c.nreg 7500 = m := h.1

theorem tb1_exec (c : Config) (hc : WordsBounded W c) {m RVb LNb K LABb KPb MLb Tb Zl i xa r xb ln : ℕ}
    (hR : TbRegs c m RVb LNb K LABb KPb MLb Tb Zl) (r22 : c.nreg 7522 = 1)
    (r30 : c.nreg 7530 = i)
    (hxa : c.nmem (LABb + i) = xa) (hr : c.nmem (RVb + i) = r) (hxb : c.nmem (LABb + r) = xb)
    (hln : c.nmem (LNb + i) = ln)
    (w1 : LABb + i ≤ W) (w2 : RVb + i ≤ W) (w3 : LABb + r ≤ W) (w4 : LNb + i ≤ W)
    (w5 : Tb + 2 * (xa * (m + 1) + xb) + 1 ≤ W) (w6 : i + 1 ≤ W) (w7 : m ≤ W) (w8 : Zl ≤ W) :
    ∃ c' k, Exec P W tb1 c c' k ∧ k = 26 ∧ c'.nreg 7530 = i + 1 ∧
      c'.nmem = upd (upd c.nmem (Tb + 2 * (xa * (m + 1) + xb))
          (max (c.nmem (Tb + 2 * (xa * (m + 1) + xb))) (m - (i - (i - r)))))
        (Tb + 2 * (xa * (m + 1) + xb) + 1)
          (max (c.nmem (Tb + 2 * (xa * (m + 1) + xb) + 1)) (Zl - ln)) ∧
      (∀ x, (x < 7530 ∨ 7548 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨r00, r01, r03, r04, r12, r14, r15, r19, r20, r21⟩ := hR
  have v0 := hc.2 (Tb + 2 * (xa * (m + 1) + xb))
  have v1 := hc.2 (Tb + 2 * (xa * (m + 1) + xb) + 1)
  have e2 : Tb + (xa * (m + 1) + xb) + (xa * (m + 1) + xb) = Tb + 2 * (xa * (m + 1) + xb) := by
    omega
  unfold tb1
  exec_block
  all_goals try (config_simp; simp only [r00, r01, r03, r04, r12, r19, r20, r21, r22, r30, hxa,
    hr, hxb, hln, e2]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r22, r30]
  · config_simp; simp only [r00, r01, r03, r04, r12, r19, r20, r21, r22, r30, hxa, hr, hxb, hln]
    rw [e2, max_eq', max_eq']
  · config_simp; simp (disch := omega) only [Machine.upd_other]

theorem tb2_exec (c : Config) (hc : WordsBounded W c) {m RVb LNb K LABb KPb MLb Tb Zl i xa r xb L : ℕ}
    (hR : TbRegs c m RVb LNb K LABb KPb MLb Tb Zl) (r22 : c.nreg 7522 = 1)
    (r30 : c.nreg 7530 = i) (r25 : c.nreg 7525 = L)
    (hxa : c.nmem (LABb + i) = xa) (hr : c.nmem (RVb + i) = r) (hxb : c.nmem (LABb + r) = xb)
    (w1 : LABb + i ≤ W) (w2 : RVb + i ≤ W) (w3 : LABb + r ≤ W) (w4 : MLb + i ≤ W)
    (w4' : KPb + i ≤ W)
    (w5 : Tb + 2 * (xa * (m + 1) + xb) + 1 ≤ W) (w6 : i + 1 ≤ W)
    (w8 : L + lterm K (Zl - c.nmem (Tb + 2 * (xa * (m + 1) + xb) + 1)) ≤ W) :
    ∃ c' k, Exec P W tb2 c c' k ∧ k = 35 ∧ c'.nreg 7530 = i + 1 ∧
      c'.nreg 7525 = L + lterm K (Zl - c.nmem (Tb + 2 * (xa * (m + 1) + xb) + 1)) ∧
      c'.nmem = upd (upd c.nmem (MLb + i) (Zl - c.nmem (Tb + 2 * (xa * (m + 1) + xb) + 1)))
        (KPb + i) (kflag xa xb (c.nmem (Tb + 2 * (xa * (m + 1) + xb))) (m - (i - (i - r)))) ∧
      (∀ x, (x < 7530 ∨ 7548 < x) → x ≠ 7525 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨r00, r01, r03, r04, r12, r14, r15, r19, r20, r21⟩ := hR
  have e2 : Tb + (xa * (m + 1) + xb) + (xa * (m + 1) + xb) = Tb + 2 * (xa * (m + 1) + xb) := by
    omega
  have bxa := hc.2 (LABb + i)
  have bxb := hc.2 (LABb + r)
  rw [hxa] at bxa
  rw [hxb] at bxb
  unfold tb2
  exec_block
  all_goals try (config_simp; simp only [r00, r01, r03, r04, r12, r14, r15, r19, r20, r21, r22,
    r25, r30, hxa, hr, hxb, e2]; unfold lterm at w8; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx hx' => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r22, r30]
  · config_simp; simp only [r00, r01, r03, r04, r12, r14, r15, r19, r20, r21, r22, r25, r30, hxa,
      hr, hxb, e2]; unfold lterm; omega
  · config_simp; simp only [r00, r01, r03, r04, r12, r14, r15, r19, r20, r21, r22, r25, r30, hxa,
      hr, hxb]
    rw [e2]; rfl
  · config_simp; simp (disch := omega) only [Machine.upd_other]

theorem tb3_exec (c : Config) (hc : WordsBounded W c) {m RVb LNb K LABb KPb MLb Tb Zl i xa r xb : ℕ}
    (hR : TbRegs c m RVb LNb K LABb KPb MLb Tb Zl) (r22 : c.nreg 7522 = 1)
    (r24 : c.nreg 7524 = 0) (r30 : c.nreg 7530 = i)
    (hxa : c.nmem (LABb + i) = xa) (hr : c.nmem (RVb + i) = r) (hxb : c.nmem (LABb + r) = xb)
    (w1 : LABb + i ≤ W) (w2 : RVb + i ≤ W) (w3 : LABb + r ≤ W)
    (w5 : Tb + 2 * (xa * (m + 1) + xb) + 1 ≤ W) (w6 : i + 1 ≤ W) :
    ∃ c' k, Exec P W tb3 c c' k ∧ k = 14 ∧ c'.nreg 7530 = i + 1 ∧
      c'.nmem = upd (upd c.nmem (Tb + 2 * (xa * (m + 1) + xb)) 0)
        (Tb + 2 * (xa * (m + 1) + xb) + 1) 0 ∧
      (∀ x, (x < 7530 ∨ 7548 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨r00, r01, r03, r04, r12, r14, r15, r19, r20, r21⟩ := hR
  have e2 : Tb + (xa * (m + 1) + xb) + (xa * (m + 1) + xb) = Tb + 2 * (xa * (m + 1) + xb) := by
    omega
  unfold tb3
  exec_block
  all_goals try (config_simp; simp only [r00, r01, r03, r04, r12, r19, r20, r21, r22, r24, r30,
    hxa, hr, hxb, e2]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r22, r30]
  · config_simp; simp only [r00, r01, r03, r04, r12, r19, r20, r21, r22, r24, r30, hxa, hr, hxb]
    rw [e2]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega


/-! ### The loops -/

/-- The size of the table. -/
def tsz (m : ℕ) : ℕ := 2 * ((m + 1) * (m + 1))

lemma tsz_pos (m : ℕ) : 2 ≤ tsz m := by
  unfold tsz; have : 0 < (m + 1) * (m + 1) := Nat.mul_pos (by omega) (by omega); omega

/-- The hypotheses of the passes on the arrays: labels `LAB = lab + 1`, reverses `RV = rv`,
both below `m`; the table above the scratch arrays, the input arrays above the table. -/
structure TbArr (mem : ℕ → ℕ) (m RVb LABb Tb : ℕ) (lab rv : ℕ → ℕ) : Prop where
  hlab : ∀ j < m, mem (LABb + j) = lab j + 1
  hrv : ∀ j < m, mem (RVb + j) = rv j
  rvm : ∀ j < m, rv j < m
  labm : ∀ j < m, lab j < m
  dL : LABb + m ≤ Tb
  dR : Tb + tsz m ≤ RVb

lemma TbArr.key_lt {mem : ℕ → ℕ} {m RVb LABb Tb : ℕ} {lab rv : ℕ → ℕ}
    (h : TbArr mem m RVb LABb Tb lab rv) {x : ℕ} (hx : x < m) :
    2 * keyG lab rv (m + 1) x + 1 < tsz m := by
  have := NsStep.key_lt (h.labm x hx) (h.labm _ (h.rvm x hx))
  unfold tsz; omega

lemma TbArr.of {mem mem' : ℕ → ℕ} {m RVb LABb Tb : ℕ} {lab rv : ℕ → ℕ}
    (h : TbArr mem m RVb LABb Tb lab rv)
    (e : ∀ j < m, mem' (LABb + j) = mem (LABb + j) ∧ mem' (RVb + j) = mem (RVb + j)) :
    TbArr mem' m RVb LABb Tb lab rv :=
  ⟨fun j hj => by rw [(e j hj).1]; exact h.hlab j hj, fun j hj => by rw [(e j hj).2]; exact h.hrv j hj,
    h.rvm, h.labm, h.dL, h.dR⟩

/-- Off the key cells. -/
def OffKeys (lab rv : ℕ → ℕ) (m Tb a : ℕ) : Prop :=
  ∀ x < m, a ≠ Tb + 2 * keyG lab rv (m + 1) x ∧ a ≠ Tb + 2 * keyG lab rv (m + 1) x + 1

lemma offKeys_of_lt {lab rv : ℕ → ℕ} {m Tb a : ℕ} (h : a < Tb) : OffKeys lab rv m Tb a :=
  fun x _ => ⟨by omega, by omega⟩

lemma offKeys_of_ge {mem : ℕ → ℕ} {m RVb LABb Tb : ℕ} {lab rv : ℕ → ℕ}
    (hA : TbArr mem m RVb LABb Tb lab rv) {a : ℕ} (h : Tb + tsz m ≤ a) :
    OffKeys lab rv m Tb a :=
  fun x hx => by have := hA.key_lt hx; exact ⟨by omega, by omega⟩

/-- **Pass 1**: within `28 m + 4` steps the key cells hold the maxima over the groups. -/
theorem tbL1_exec (c : Config) (hc : WordsBounded W c) {m RVb LNb K LABb KPb MLb Tb Zl : ℕ}
    {lab rv ln : ℕ → ℕ} (hR : TbRegs c m RVb LNb K LABb KPb MLb Tb Zl)
    (hA : TbArr c.nmem m RVb LABb Tb lab rv) (hln : ∀ j < m, c.nmem (LNb + j) = ln j)
    (hT0 : ∀ x < m, c.nmem (Tb + 2 * keyG lab rv (m + 1) x) = 0 ∧
      c.nmem (Tb + 2 * keyG lab rv (m + 1) x + 1) = 0)
    (dN : Tb + tsz m ≤ LNb) (wR : RVb + m ≤ W) (wN : LNb + m ≤ W) (wT : Tb + tsz m ≤ W)
    (wZ : Zl ≤ W) :
    ∃ c' k, Exec P W tbL1 c c' k ∧ k ≤ 28 * m + 4 ∧
      (∀ x < m, c'.nmem (Tb + 2 * keyG lab rv (m + 1) x) =
          (grpP lab rv (m + 1) m x).sup (vE rv m) ∧
        c'.nmem (Tb + 2 * keyG lab rv (m + 1) x + 1) = (grpP lab rv (m + 1) m x).sup (vL ln Zl)) ∧
      (∀ a, OffKeys lab rv m Tb a → c'.nmem a = c.nmem a) ∧
      c'.nreg 7522 = 1 ∧ (∀ r, (r < 7522 ∨ 7548 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have r00 := hR.1
  unfold tbL1
  obtain ⟨c₁, k₁, e₁, hk₁, g22, g30, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 7522 1, .constN 7530 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 7522 = 1 ∧ c₁.nreg 7530 = 0 ∧
      (∀ x, x ≠ 7522 → x ≠ 7530 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have : 1 ≤ W := by have := tsz_pos m; omega
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp (disch := omega) only [Machine.upd_other]
  have hw₁ := e₁.wb_right
  have hR₁ : TbRegs c₁ m RVb LNb K LABb KPb MLb Tb Zl := hR.of fun r hr => gn₁ r (by omega) (by omega)
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 7530 ∨ 7548 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ x < m, c'.nmem (Tb + 2 * keyG lab rv (m + 1) x) =
        (grpP lab rv (m + 1) i x).sup (vE rv m) ∧
      c'.nmem (Tb + 2 * keyG lab rv (m + 1) x + 1) = (grpP lab rv (m + 1) i x).sup (vL ln Zl)) ∧
    (∀ a, OffKeys lab rv m Tb a → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h30, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 7530)
    (b := 7500) (body := tb1) J (B := 26) c₁ hw₁ g30
    (by rw [gn₁ _ (by omega) (by omega), r00]) (Nat.zero_le m)
    ⟨fun _ _ => rfl, fun x hx => by rw [grpP_zero, sup_empty, sup_empty, gm₁]; exact hT0 x hx,
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h30 h00 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 7530 ∨ 7548 < x) → c'.nreg x = c₁.nreg x := j1
      have hR' : TbRegs c' m RVb LNb K LABb KPb MLb Tb Zl := hR₁.of fun r hr => f r (by omega)
      have hri := hA.rvm i hhi
      have ea : c'.nmem (LABb + i) = lab i + 1 := by
        rw [j3 _ (offKeys_of_lt (by have := hA.dL; omega))]; exact hA.hlab i hhi
      have eb : c'.nmem (RVb + i) = rv i := by
        rw [j3 _ (offKeys_of_ge hA (by have := hA.dR; omega))]; exact hA.hrv i hhi
      have ec : c'.nmem (LABb + rv i) = lab (rv i) + 1 := by
        rw [j3 _ (offKeys_of_lt (by have := hA.dL; omega))]; exact hA.hlab _ hri
      have ed : c'.nmem (LNb + i) = ln i := by
        rw [j3 _ (offKeys_of_ge hA (by omega))]; exact hln i hhi
      have hk := hA.key_lt hhi
      have hkey : keyG lab rv (m + 1) i = (lab i + 1) * (m + 1) + (lab (rv i) + 1) := rfl
      obtain ⟨c'', t, ex, ht, h30', hm', hn', hr', hrm', ho'⟩ := tb1_exec (P := P) c' hw hR'
        (by rw [f _ (by omega), g22]) h30 ea eb ec ed (by have := hA.dL; omega)
        (by omega) (by have := hA.dL; omega) (by omega) (by rw [← hkey]; omega) (by omega)
        (by omega) wZ
      rw [← hkey] at hm'
      refine ⟨c'', t, ex, ht.le, h30', by rw [hn' _ (by omega)]; exact h00,
        fun x hx => by rw [hn' x hx, f x hx], fun x hx => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [grpP_succ]
        by_cases hxi : keyG lab rv (m + 1) i = keyG lab rv (m + 1) x
        · rw [iteT hxi, sup_insert, sup_insert, hm', ← hxi, upd_same,
            upd_other _ _ _ (by omega), upd_same]
          have g0 := (j2 i hhi).1
          have g1 := (j2 i hhi).2
          have e' : grpP lab rv (m + 1) i x = grpP lab rv (m + 1) i i := by
            unfold grpP; rw [hxi]
          rw [e', g0, g1]
          exact ⟨by unfold vE; simp [max_comm], by unfold vL; simp [max_comm]⟩
        · rw [iteF hxi, hm']
          refine ⟨?_, ?_⟩
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact (j2 x hx).1
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact (j2 x hx).2
      · obtain ⟨a1, a2⟩ := ha i hhi
        rw [hm', upd_other _ _ _ a2, upd_other _ _ _ a1]
        exact j3 a ha)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, by rw [j1 _ (by omega), g22],
    fun x hx => ?_, by rw [j4, gr₁], by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega)]
  rcases hx with hx | hx
  · by_cases h22 : x = 7522
    · subst h22; omega
    · exact gn₁ x h22 (by omega)
  · exact gn₁ x (by omega) (by omega)

/-- **Pass 2**: within `37 m + 5` steps the flags, the least lengths and the sum. -/
theorem tbL2_exec (c : Config) (hc : WordsBounded W c) {m RVb LNb K LABb KPb MLb Tb Zl : ℕ}
    {lab rv s0 s1 : ℕ → ℕ} (hR : TbRegs c m RVb LNb K LABb KPb MLb Tb Zl)
    (hA : TbArr c.nmem m RVb LABb Tb lab rv)
    (hT : ∀ x < m, c.nmem (Tb + 2 * keyG lab rv (m + 1) x) = s0 x ∧
      c.nmem (Tb + 2 * keyG lab rv (m + 1) x + 1) = s1 x)
    (dK : LABb + m ≤ KPb) (dM : KPb + m ≤ MLb) (dT : MLb + m ≤ Tb) (wR : RVb + m ≤ W)
    (wT : Tb + tsz m ≤ W) (wL : ∑ j ∈ range m, lterm K (Zl - s1 j) ≤ W) :
    ∃ c' k, Exec P W tbL2 c c' k ∧ k ≤ 37 * m + 5 ∧
      (∀ j < m, c'.nmem (KPb + j) = kflag (lab j + 1) (lab (rv j) + 1) (s0 j) (vE rv m j) ∧
        c'.nmem (MLb + j) = Zl - s1 j) ∧
      c'.nreg 7525 = ∑ j ∈ range m, lterm K (Zl - s1 j) ∧
      (∀ a, ¬ (KPb ≤ a ∧ a < KPb + m) → ¬ (MLb ≤ a ∧ a < MLb + m) → c'.nmem a = c.nmem a) ∧
      c'.nreg 7522 = 1 ∧ (∀ r, (r < 7522 ∨ 7548 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have r00 := hR.1
  unfold tbL2
  obtain ⟨c₁, k₁, e₁, hk₁, g22, g25, g30, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 7522 1, .constN 7525 0, .constN 7530 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 7522 = 1 ∧ c₁.nreg 7525 = 0 ∧ c₁.nreg 7530 = 0 ∧
      (∀ x, x ≠ 7522 → x ≠ 7525 → x ≠ 7530 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have : 1 ≤ W := by have := tsz_pos m; omega
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp
    · config_simp; simp (disch := omega) only [Machine.upd_other]
  have hw₁ := e₁.wb_right
  have hR₁ : TbRegs c₁ m RVb LNb K LABb KPb MLb Tb Zl :=
    hR.of fun r hr => gn₁ r (by omega) (by omega) (by omega)
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 7530 ∨ 7548 < x) → x ≠ 7525 → c'.nreg x = c₁.nreg x) ∧
    c'.nreg 7525 = ∑ j ∈ range i, lterm K (Zl - s1 j) ∧
    (∀ j < i, c'.nmem (KPb + j) = kflag (lab j + 1) (lab (rv j) + 1) (s0 j) (vE rv m j) ∧
        c'.nmem (MLb + j) = Zl - s1 j) ∧
    (∀ a, ¬ (KPb ≤ a ∧ a < KPb + i) → ¬ (MLb ≤ a ∧ a < MLb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h30, j1, j7, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 7530)
    (b := 7500) (body := tb2) J (B := 35) c₁ hw₁ g30
    (by rw [gn₁ _ (by omega) (by omega) (by omega), r00]) (Nat.zero_le m)
    ⟨fun _ _ _ => rfl, by rw [g25]; rfl, fun j hj => absurd hj (by omega),
      fun a _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h30 h00 ⟨j1, j7, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 7530 ∨ 7548 < x) → x ≠ 7525 → c'.nreg x = c₁.nreg x := j1
      have hR' : TbRegs c' m RVb LNb K LABb KPb MLb Tb Zl :=
        hR₁.of fun r hr => f r (by omega) (by omega)
      have hri := hA.rvm i hhi
      have ea : c'.nmem (LABb + i) = lab i + 1 := by
        rw [j3 _ (by omega) (by omega)]; exact hA.hlab i hhi
      have eb : c'.nmem (RVb + i) = rv i := by
        rw [j3 _ (by have := hA.dR; omega) (by have := hA.dR; omega)]; exact hA.hrv i hhi
      have ec : c'.nmem (LABb + rv i) = lab (rv i) + 1 := by
        rw [j3 _ (by omega) (by omega)]; exact hA.hlab _ hri
      have hk := hA.key_lt hhi
      have hkey : keyG lab rv (m + 1) i = (lab i + 1) * (m + 1) + (lab (rv i) + 1) := rfl
      have e0 : c'.nmem (Tb + 2 * keyG lab rv (m + 1) i) = s0 i := by
        rw [j3 _ (by omega) (by omega)]; exact (hT i hhi).1
      have e1 : c'.nmem (Tb + 2 * keyG lab rv (m + 1) i + 1) = s1 i := by
        rw [j3 _ (by omega) (by omega)]; exact (hT i hhi).2
      have hsum : ∑ j ∈ range (i + 1), lterm K (Zl - s1 j) ≤ W :=
        le_trans (Finset.sum_le_sum_of_subset (range_subset_range.2 (by omega))) wL
      rw [sum_range_succ] at hsum
      obtain ⟨c'', t, ex, ht, h30', h25', hm', hn', hr', hrm', ho'⟩ := tb2_exec (P := P) c' hw hR'
        (by rw [f _ (by omega) (by omega), g22]) h30 j7 ea eb ec (by omega) (by omega)
        (by omega) (by omega) (by omega) (by rw [← hkey]; omega) (by omega)
        (by rw [← hkey, e1]; omega)
      rw [← hkey, e0, e1] at hm'
      rw [← hkey, e1] at h25'
      refine ⟨c'', t, ex, ht.le, h30', by rw [hn' _ (by omega) (by omega)]; exact h00,
        fun x hx hx' => by rw [hn' x hx hx', f x hx hx'], by rw [h25', sum_range_succ],
        fun j hj => ?_, fun a ha1 ha2 => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · refine ⟨?_, ?_⟩
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact (j2 j hj).1
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact (j2 j hj).2
        · rw [upd_same, upd_other _ _ _ (by omega), upd_same]
          exact ⟨rfl, rfl⟩
      · rw [hm', upd_other _ _ _ (fun h => ha1 ⟨by omega, by omega⟩),
          upd_other _ _ _ (fun h => ha2 ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha1 ⟨h.1, by omega⟩) (fun h => ha2 ⟨h.1, by omega⟩))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j7, j3, by rw [j1 _ (by omega) (by omega), g22],
    fun x hx => ?_, by rw [j4, gr₁], by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega) (by omega)]
  exact gn₁ x (by omega) (by omega) (by omega)

/-- **Pass 3**: within `16 m + 5` steps the key cells are cleared. -/
theorem tbL3_exec (c : Config) (hc : WordsBounded W c) {m RVb LNb K LABb KPb MLb Tb Zl : ℕ}
    {lab rv : ℕ → ℕ} (hR : TbRegs c m RVb LNb K LABb KPb MLb Tb Zl)
    (hA : TbArr c.nmem m RVb LABb Tb lab rv) (wR : RVb + m ≤ W) (wT : Tb + tsz m ≤ W) :
    ∃ c' k, Exec P W tbL3 c c' k ∧ k ≤ 16 * m + 5 ∧
      (∀ x < m, c'.nmem (Tb + 2 * keyG lab rv (m + 1) x) = 0 ∧
        c'.nmem (Tb + 2 * keyG lab rv (m + 1) x + 1) = 0) ∧
      (∀ a, OffKeys lab rv m Tb a → c'.nmem a = c.nmem a) ∧
      c'.nreg 7522 = 1 ∧ c'.nreg 7524 = 0 ∧ c'.nreg 7525 = c.nreg 7525 ∧
      (∀ r, (r < 7522 ∨ 7548 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have r00 := hR.1
  unfold tbL3
  obtain ⟨c₁, k₁, e₁, hk₁, g22, g24, g30, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 7522 1, .constN 7524 0, .constN 7530 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 7522 = 1 ∧ c₁.nreg 7524 = 0 ∧ c₁.nreg 7530 = 0 ∧
      (∀ x, x ≠ 7522 → x ≠ 7524 → x ≠ 7530 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have : 1 ≤ W := by have := tsz_pos m; omega
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp
    · config_simp; simp (disch := omega) only [Machine.upd_other]
  have hw₁ := e₁.wb_right
  have hR₁ : TbRegs c₁ m RVb LNb K LABb KPb MLb Tb Zl :=
    hR.of fun r hr => gn₁ r (by omega) (by omega) (by omega)
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 7530 ∨ 7548 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (Tb + 2 * keyG lab rv (m + 1) j) = 0 ∧
        c'.nmem (Tb + 2 * keyG lab rv (m + 1) j + 1) = 0) ∧
    (∀ a, (∀ j < i, a ≠ Tb + 2 * keyG lab rv (m + 1) j ∧ a ≠ Tb + 2 * keyG lab rv (m + 1) j + 1) →
      c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h30, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 7530)
    (b := 7500) (body := tb3) J (B := 14) c₁ hw₁ g30
    (by rw [gn₁ _ (by omega) (by omega) (by omega), r00]) (Nat.zero_le m)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h30 h00 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 7530 ∨ 7548 < x) → c'.nreg x = c₁.nreg x := j1
      have hR' : TbRegs c' m RVb LNb K LABb KPb MLb Tb Zl := hR₁.of fun r hr => f r (by omega)
      have hri := hA.rvm i hhi
      have off : ∀ a, OffKeys lab rv m Tb a → c'.nmem a = m₀ a := fun a ha =>
        j3 a fun j hj => ha j (by omega)
      have ea : c'.nmem (LABb + i) = lab i + 1 := by
        rw [off _ (offKeys_of_lt (by have := hA.dL; omega))]; exact hA.hlab i hhi
      have eb : c'.nmem (RVb + i) = rv i := by
        rw [off _ (offKeys_of_ge hA (by have := hA.dR; omega))]; exact hA.hrv i hhi
      have ec : c'.nmem (LABb + rv i) = lab (rv i) + 1 := by
        rw [off _ (offKeys_of_lt (by have := hA.dL; omega))]; exact hA.hlab _ hri
      have hk := hA.key_lt hhi
      have hkey : keyG lab rv (m + 1) i = (lab i + 1) * (m + 1) + (lab (rv i) + 1) := rfl
      obtain ⟨c'', t, ex, ht, h30', hm', hn', hr', hrm', ho'⟩ := tb3_exec (P := P) c' hw hR'
        (by rw [f _ (by omega), g22]) (by rw [f _ (by omega), g24]) h30 ea eb ec
        (by have := hA.dL; omega) (by omega) (by have := hA.dL; omega) (by rw [← hkey]; omega)
        (by omega)
      rw [← hkey] at hm'
      refine ⟨c'', t, ex, ht.le, h30', by rw [hn' _ (by omega)]; exact h00,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · by_cases e : keyG lab rv (m + 1) j = keyG lab rv (m + 1) i
          · rw [← e, upd_same, upd_other _ _ _ (by omega), upd_same]; exact ⟨rfl, rfl⟩
          · refine ⟨?_, ?_⟩
            · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact (j2 j hj).1
            · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact (j2 j hj).2
        · rw [upd_same, upd_other _ _ _ (by omega), upd_same]; exact ⟨rfl, rfl⟩
      · obtain ⟨a1, a2⟩ := ha i (by omega)
        rw [hm', upd_other _ _ _ a2, upd_other _ _ _ a1]
        exact j3 a fun j hj => ha j (by omega))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, fun a ha => j3 a ha,
    by rw [j1 _ (by omega), g22], by rw [j1 _ (by omega), g24],
    by rw [j1 _ (by omega), gn₁ _ (by omega) (by omega) (by omega)],
    fun x hx => ?_, by rw [j4, gr₁], by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega)]
  exact gn₁ x (by omega) (by omega) (by omega)

/-- **The grouping**: from a zero table, within `81 m + 14` steps, `KEEP[j]` (`1` iff the dart is
not a loop of the dual and the maximum of `vE` over its group is reached at it), `MLN[j] = Zl -`
the maximum of `vL` over its group, the sum of `lterm K MLN` in `r7525`; all memory but `KEEP`
and `MLN` kept (the table is zero again). -/
theorem tbProg_exec (c : Config) (hc : WordsBounded W c) {m RVb LNb K LABb KPb MLb Tb Zl : ℕ}
    {lab rv ln : ℕ → ℕ} (hR : TbRegs c m RVb LNb K LABb KPb MLb Tb Zl)
    (hA : TbArr c.nmem m RVb LABb Tb lab rv) (hln : ∀ j < m, c.nmem (LNb + j) = ln j)
    (hT0 : ∀ a, Tb ≤ a → a < Tb + tsz m → c.nmem a = 0)
    (dK : LABb + m ≤ KPb) (dM : KPb + m ≤ MLb) (dT : MLb + m ≤ Tb) (dN : Tb + tsz m ≤ LNb)
    (wR : RVb + m ≤ W) (wN : LNb + m ≤ W) (wT : Tb + tsz m ≤ W) (wZ : Zl ≤ W)
    (wL : ∑ j ∈ range m, lterm K (Zl - (grpP lab rv (m + 1) m j).sup (vL ln Zl)) ≤ W) :
    ∃ c' k, Exec P W tbProg c c' k ∧ k ≤ 81 * m + 14 ∧
      (∀ j < m, c'.nmem (KPb + j) = kflag (lab j + 1) (lab (rv j) + 1)
          ((grpP lab rv (m + 1) m j).sup (vE rv m)) (vE rv m j) ∧
        c'.nmem (MLb + j) = Zl - (grpP lab rv (m + 1) m j).sup (vL ln Zl)) ∧
      c'.nreg 7525 = ∑ j ∈ range m, lterm K (Zl - (grpP lab rv (m + 1) m j).sup (vL ln Zl)) ∧
      (∀ a, ¬ (KPb ≤ a ∧ a < KPb + m) → ¬ (MLb ≤ a ∧ a < MLb + m) → c'.nmem a = c.nmem a) ∧
      c'.nreg 7522 = 1 ∧ c'.nreg 7524 = 0 ∧ (∀ r, (r < 7522 ∨ 7548 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hT0' : ∀ x < m, c.nmem (Tb + 2 * keyG lab rv (m + 1) x) = 0 ∧
      c.nmem (Tb + 2 * keyG lab rv (m + 1) x + 1) = 0 := fun x hx => by
    have := hA.key_lt hx
    exact ⟨hT0 _ (by omega) (by omega), hT0 _ (by omega) (by omega)⟩
  obtain ⟨c₁, k₁, e₁, hk₁, a1, a2, -, a4, a5, a6, a7⟩ :=
    tbL1_exec (P := P) c hc hR hA hln hT0' dN wR wN wT wZ
  have hR₁ := hR.of fun r hr => a4 r (by omega)
  have hA₁ := hA.of fun j hj => ⟨a2 _ (offKeys_of_lt (by have := hA.dL; omega)),
    a2 _ (offKeys_of_ge hA (by have := hA.dR; omega))⟩
  obtain ⟨c₂, k₂, e₂, hk₂, b1, b2, b3, -, b4, b5, b6, b7⟩ :=
    tbL2_exec (P := P) c₁ e₁.wb_right hR₁ hA₁ a1 dK dM dT wR wT wL
  have hR₂ := hR₁.of fun r hr => b4 r (by omega)
  have hA₂ := hA₁.of fun j hj => ⟨b3 _ (by omega) (by omega),
    b3 _ (by have := hA.dR; omega) (by have := hA.dR; omega)⟩
  obtain ⟨c₃, k₃, e₃, hk₃, d1, d2, d3, d4, d25, d5, d6, d7, d8⟩ :=
    tbL3_exec (P := P) c₂ e₂.wb_right hR₂ hA₂ wR wT
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, fun j hj => ?_, ?_,
    fun a ha1 ha2 => ?_, d3, d4, fun r hr => ?_, by rw [d6, b5, a5], by rw [d7, b6, a6],
    by rw [d8, b7, a7]⟩
  · rw [d2 _ (offKeys_of_lt (by omega)), d2 _ (offKeys_of_lt (by omega))]
    exact b1 j hj
  · rw [d25]; exact b2
  · by_cases hoff : OffKeys lab rv m Tb a
    · rw [d2 a hoff, b3 a ha1 ha2, a2 a hoff]
    · simp only [OffKeys, not_forall] at hoff
      obtain ⟨x, hx, hne⟩ := hoff
      have hk := hA.key_lt hx
      by_cases e : a = Tb + 2 * keyG lab rv (m + 1) x
      · rw [e, (d1 x hx).1, hT0 _ (by omega) (by omega)]
      · have e' : a = Tb + 2 * keyG lab rv (m + 1) x + 1 := by tauto
        rw [e', (d1 x hx).2, hT0 _ (by omega) (by omega)]
  · rw [d5 r hr, b4 r hr, a4 r hr]

end NsStep

end BKMNW

end PlanarFlow
