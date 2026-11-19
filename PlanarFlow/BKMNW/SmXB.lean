module

public import PlanarFlow.BKMNW.SmXA3

/-!
# The small separator program, stage B (first part): the children's data over the record

After stage A (`SmRegs`, the flags over the record from `Ob = A + n`: `LP` (left piece), `CV`
(tail on the path) at `A + 3 n`, `HM` (holes meeting the path) at `A + 4 n`), over **all** the
darts of the piece:

* `smB0` (the registers of the flag loops), `smBF = sfFlagsA ; sfFlagsB` (the per-dart data
  `NH`, `HC`, `KC` of the children as for the frame, `MfFrameFlags.lean`, here on the record from
  `Wb' = A + 4 n + k + 2`), **`smBF_exec`**;
* `smB1` (the compaction of `LP`: `CI` at `B2`, `IX` at `B2 + n`, `nl = cnt LP n` in `5540`),
  **`smB1_exec`**;
* `cfV` (the dart in the left child's piece map: in `l.piece` and not inside a hole of the
  child, `0 < HC ∧ HC = HC ∘ RP`), `vbCF`, `smB2` (the map `CF` at `B3`), **`smB2_exec`**;
* `smB3` (the compaction of `CF`: `CI2` at `B3 + n`, `IX2` at `B3 + 2 n`, `ml` in `5541`),
  **`smB3_exec`**.
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

/-- The registers of the flag loops on the record. -/
def smB0 : Stmt := block [.copyN 6510 5504, .copyN 6511 5502, .constN 6539 0,
  .copyN 6540 5522, .copyN 6541 5513, .copyN 6542 5523, .copyN 6544 5508, .addN 6531 6544 5504,
  .addN 6532 6531 5504, .addN 6533 6532 5504, .addN 6534 6533 5504, .addN 6535 6534 5504,
  .addN 6536 6535 5504, .addN 6536 6536 5504, .addN 6547 6536 5502, .addN 6537 6547 5502,
  .copyN 6543 5507, .copyN 6545 5512, .copyN 6546 5514]

/-- The children's data over the record. -/
def smBF : Stmt := .seq sfFlagsA sfFlagsB

/-- A compaction with its arguments in registers, the count copied to `rout`. -/
def smLk (rn rF rCI rIX rout : ℕ) : Stmt := .seq (block [.copyN 6300 rn, .copyN 6301 rF,
  .copyN 6302 rCI, .copyN 6303 rIX]) (.seq lkProg (block [.copyN rout 6306]))

/-- The compaction of `LP`. -/
def smB1 : Stmt := smLk 5504 5507 5509 5528 5540

/-- **The dart in the left child's piece map**: `lp > 0` and not `0 < a ∧ a = b` (`a`, `b` the
child's hole labels of the two ends), by truncated subtraction. -/
def cfV (lp a b : ℕ) : ℕ := (1 - (1 - lp)) - ((1 - (1 - a)) + (1 - ((a - b) + (b - a))) - 1)

/-- `r6523 := cfV LP[i] HC[i] HC[RP[i]]` (bases `5507 = LP`, `6534 = HC`, `5512 = RP`). -/
def vbCF : Stmt := block [.addN 6524 5507 6520, .loadN 6525 6524, .addN 6524 6534 6520,
  .loadN 6526 6524, .addN 6524 5512 6520, .loadN 6527 6524, .addN 6524 6534 6527,
  .loadN 6527 6524, .subN 6528 6526 6527, .subN 6529 6527 6526, .addN 6528 6528 6529,
  .subN 6528 6521 6528, .subN 6529 6521 6526, .subN 6529 6521 6529, .addN 6528 6529 6528,
  .subN 6528 6528 6521, .subN 6529 6521 6525, .subN 6529 6521 6529, .subN 6523 6529 6528]

/-- The map `CF` at `B3`. -/
def smB2 : Stmt := mapRunS vbCF 5504 5510

/-- The compaction of `CF`. -/
def smB3 : Stmt := smLk 5504 5510 5530 5531 5541

/-- The kept-hole flag of the hole `j` (from `HM` at `HMb`). -/
def hfR (mem : ℕ → ℕ) (HMb j : ℕ) : ℕ := hfF (mem (HMb + j))

/-- The machine's flag of the tail of the record's dart `i` in the new hole. -/
def nhR (mem : ℕ → ℕ) (CVb HLb HMb i : ℕ) : ℕ :=
  nhF (mem (CVb + i)) (mem (HLb + i)) (mem (HMb + (mem (HLb + i) - 1)))

section Exec

variable {I : Input} {W : ℕ}

theorem smB0_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb A : ℕ}
    (hR : SmRegs c d m k R n Sb A) (w : A + 11 * n + 4 * k + 2 ≤ W) :
    ∃ c' t, Exec I W smB0 c c' t ∧ t = 19 ∧ c'.nreg 6510 = n ∧ c'.nreg 6511 = k ∧
      c'.nreg 6539 = 0 ∧ c'.nreg 6540 = A + 3 * n ∧ c'.nreg 6541 = R + 3 + 2 * n ∧
      c'.nreg 6542 = A + 4 * n ∧ c'.nreg 6544 = A + 4 * n + k + 2 ∧
      c'.nreg 6531 = A + 4 * n + k + 2 + n ∧ c'.nreg 6532 = A + 4 * n + k + 2 + 2 * n ∧
      c'.nreg 6533 = A + 4 * n + k + 2 + 3 * n ∧ c'.nreg 6534 = A + 4 * n + k + 2 + 4 * n ∧
      c'.nreg 6535 = A + 4 * n + k + 2 + 5 * n ∧ c'.nreg 6536 = A + 4 * n + k + 2 + 7 * n ∧
      c'.nreg 6547 = A + 4 * n + k + 2 + 7 * n + k ∧
      c'.nreg 6537 = A + 4 * n + k + 2 + 7 * n + 2 * k ∧ c'.nreg 6543 = A + n ∧
      c'.nreg 6545 = R + 3 + n ∧ c'.nreg 6546 = R + 3 + 3 * n ∧
      (∀ x, (x < 6510 ∨ (6511 < x ∧ x < 6531 ∧ x ≠ 6539) ∨ 6547 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have r04 := hR.r04; have r02 := hR.r02; have r22 := hR.r22; have r13 := hR.r13
  have r23 := hR.r23; have r08 := hR.r08; have r07 := hR.r07; have r12 := hR.r12
  have r14 := hR.r14
  have := hc.1 5513; have := hc.1 5512; have := hc.1 5514; have := hc.1 5507
  have := hc.1 5522; have := hc.1 5523; have := hc.1 5508
  unfold smB0
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r04, r02, r22, r13, r23, r08, r07, r12, r14]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r04, r02, r22, r13, r23, r08, r07, r12,
      r14])
    try omega

set_option maxHeartbeats 2000000 in
/-- **The children's data over the record** (`sfFlagsA ; sfFlagsB`): `NH`, `KC`, `HC` from `Wb`. -/
theorem smBF_exec (c : Config) (hc : WordsBounded W c) {n k Wb CVb HLb HMb LPb RVb KRb : ℕ}
    (r10 : c.nreg 6510 = n) (r11 : c.nreg 6511 = k) (r21 : c.nreg 6521 = 1)
    (r39 : c.nreg 6539 = 0) (r40 : c.nreg 6540 = CVb) (r41 : c.nreg 6541 = HLb)
    (r42 : c.nreg 6542 = HMb) (r44 : c.nreg 6544 = Wb) (r31 : c.nreg 6531 = Wb + n)
    (r32 : c.nreg 6532 = Wb + 2 * n) (r33 : c.nreg 6533 = Wb + 3 * n)
    (r34 : c.nreg 6534 = Wb + 4 * n) (r35 : c.nreg 6535 = Wb + 5 * n)
    (r36 : c.nreg 6536 = Wb + 7 * n) (r47 : c.nreg 6547 = Wb + 7 * n + k)
    (r37 : c.nreg 6537 = Wb + 7 * n + 2 * k) (r43 : c.nreg 6543 = LPb)
    (r45 : c.nreg 6545 = RVb) (r46 : c.nreg 6546 = KRb)
    (o1 : CVb + n ≤ Wb) (o2 : HLb + n ≤ Wb) (o3 : HMb + k ≤ Wb) (o4 : LPb + n ≤ Wb)
    (o5 : RVb + n ≤ Wb) (o6 : KRb + n ≤ Wb) (w : Wb + 7 * n + 3 * k ≤ W) (w' : n + k + 2 ≤ W)
    (hrv : ∀ i < n, c.nmem (RVb + i) < n) (hHL : ∀ i < n, c.nmem (HLb + i) ≤ k) :
    ∃ c' t, Exec I W smBF c c' t ∧ t ≤ 91 * n + 21 * k + 32 ∧
      (∀ i < n, c'.nmem (Wb + 3 * n + i) = kcF (nhR c.nmem CVb HLb HMb i) (c.nmem (KRb + i))) ∧
      (∀ i < n, c'.nmem (Wb + 4 * n + i) = hcF (nhR c.nmem CVb HLb HMb i) (c.nmem (HLb + i))
        (cnt (hfR c.nmem HMb) (c.nmem (HLb + i) - 1)) (cnt (hfR c.nmem HMb) k + 1)) ∧
      (∀ a, (a < Wb ∨ Wb + 7 * n + 3 * k ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6300 ∨ (6309 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x ≠ 6548)) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₃, t₃, e₃, ht₃, f1, f2, f3, f4, m3, n3, rr3, rm3, o3'⟩ := sfFlagsA_exec (P := I) c hc
    (m := n) (k := k) (Wb := Wb) (CVb := CVb) (HLb := HLb) (HMb := HMb)
    r10 r11 r21 r39 r40 r41 r42 r44 r36 r47 r37 o1 o2 o3 w w' hHL
  have q3 : ∀ x, (x < 6300 ∨ (6309 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x ≠ 6548)) →
      c₃.nreg x = c.nreg x := n3
  have m3' : ∀ a, a < Wb → c₃.nmem a = c.nmem a := fun a ha => m3 a (Or.inl ha)
  have NH : ∀ i < n, c₃.nmem (Wb + i) = nhR c.nmem CVb HLb HMb i := f1
  have hl3 : ∀ i < n, c₃.nmem (HLb + i) = c.nmem (HLb + i) := fun i hi =>
    m3' _ (by clear * - hi o2; omega)
  obtain ⟨c₄, t₄, e₄, ht₄, g1, g2, g3, g4, g5, m4, n4, rr4, rm4, o4'⟩ := sfFlagsB_exec (P := I) c₃
    e₃.wb_right (m := n) (k := k) (Wb := Wb) (HLb := HLb) (LPb := LPb)
    (RVb := RVb) (KRb := KRb) (nd1 := cnt (hfR c.nmem HMb) k + 1)
    ((q3 6510 (by decide)).trans r10) ((q3 6521 (by decide)).trans r21)
    ((q3 6539 (by decide)).trans r39) ((q3 6541 (by decide)).trans r41)
    ((q3 6543 (by decide)).trans r43) ((q3 6544 (by decide)).trans r44)
    ((q3 6545 (by decide)).trans r45) ((q3 6546 (by decide)).trans r46)
    ((q3 6547 (by decide)).trans r47) f3 ((q3 6531 (by decide)).trans r31)
    ((q3 6532 (by decide)).trans r32) ((q3 6533 (by decide)).trans r33)
    ((q3 6534 (by decide)).trans r34) ((q3 6535 (by decide)).trans r35) o2 o4 o5 o6 w
    (by clear * - w'; omega)
    (fun i hi => by rw [m3' _ (by clear * - hi o5; omega)]; exact hrv i hi)
    (fun i hi => by rw [hl3 i hi]; exact hHL i hi)
    (fun i hi h1 h2 => by
      rw [NH i hi] at h1
      rw [hl3 i hi] at h2 ⊢
      have hl := hHL i hi
      have hz : hfR c.nmem HMb (c.nmem (HLb + i) - 1) = 1 := by
        unfold nhR nhF at h1; unfold hfR hfF; split_ifs at h1 <;> simp_all
      rw [f4 _ (by clear * - hl h2; omega) (by unfold hfR at hz; omega)]
      have := cnt_le (fun j => hfF (c.nmem (HMb + j))) (c.nmem (HLb + i) - 1)
      have : cnt (fun j => hfF (c.nmem (HMb + j))) (c.nmem (HLb + i) - 1) ≤ k := by
        clear * - this hl; omega
      clear * - this w w' hl h2; omega)
  refine ⟨c₄, _, .seq e₃ e₄, by clear * - ht₃ ht₄; omega, fun i hi => ?_, fun i hi => ?_,
    fun a ha => ?_, fun x hx => ?_, by rw [rr4, rr3], by rw [rm4, rm3], by rw [o4', o3']⟩
  · rw [g4 i hi, NH i hi, m3' _ (by clear * - hi o6; omega)]
  · have hl := hHL i hi
    rw [g1 i hi, NH i hi, hl3 i hi]
    unfold hcF
    split_ifs with h1 h2
    · rfl
    · have hz : hfR c.nmem HMb (c.nmem (HLb + i) - 1) = 1 := by
        unfold nhR nhF at h1; unfold hfR hfF; split_ifs at h1 <;> simp_all
      rw [f4 _ (by clear * - hl h2; omega) (by unfold hfR at hz; omega)]
      rfl
    · rfl
  · rw [m4 _ (by clear * - ha; omega), m3 a (by clear * - ha; omega)]
  · rw [n4 x (by clear * - hx; unfold vscr; omega) (by clear * - hx; omega)
      (by clear * - hx; omega), q3 x (by clear * - hx; omega)]

theorem smLkA_exec (c : Config) (hc : WordsBounded W c) {rn rF rCI rIX : ℕ}
    (h1 : rn < 6300) (h2 : rF < 6300) (h3 : rCI < 6300) (h4 : rIX < 6300) :
    ∃ c' t, Exec I W (block [.copyN 6300 rn, .copyN 6301 rF, .copyN 6302 rCI, .copyN 6303 rIX])
      c c' t ∧ t = 4 ∧ c'.nreg 6300 = c.nreg rn ∧ c'.nreg 6301 = c.nreg rF ∧
      c'.nreg 6302 = c.nreg rCI ∧ c'.nreg 6303 = c.nreg rIX ∧
      (∀ x, (x < 6300 ∨ 6303 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 rn; have := hc.1 rF; have := hc.1 rCI; have := hc.1 rIX
  exec_block
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

theorem cpyR_exec (c : Config) (hc : WordsBounded W c) {r a : ℕ} :
    ∃ c' t, Exec I W (block [.copyN r a]) c c' t ∧ t = 1 ∧ c'.nreg r = c.nreg a ∧
      (∀ x, x ≠ r → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output :=
  cpy_exec (P := I) c hc

/-- **A compaction with its arguments in registers** (`lkProg`): `CI[i] = cnt F i`,
`IX[cnt F i] = i` for the flagged `i < m`, the count `cnt F m` in `rout`. -/
theorem smLk_exec (c : Config) (hc : WordsBounded W c) {rn rF rCI rIX rout m Fb CIb IXb : ℕ}
    (h1 : rn < 6300) (h2 : rF < 6300) (h3 : rCI < 6300) (h4 : rIX < 6300) (h5 : rout < 6300)
    (r0 : c.nreg rn = m) (r1 : c.nreg rF = Fb) (r2 : c.nreg rCI = CIb) (r3 : c.nreg rIX = IXb)
    (l1 : Fb + m ≤ CIb) (l2 : CIb + m ≤ IXb) (l3 : IXb + m ≤ W) (w4 : m + 1 ≤ W) :
    ∃ c' t, Exec I W (smLk rn rF rCI rIX rout) c c' t ∧ t ≤ 11 * m + 11 ∧
      c'.nreg rout = cnt (fun j => c.nmem (Fb + j)) m ∧
      (∀ i < m, 0 < c.nmem (Fb + i) →
        c'.nmem (CIb + i) = cnt (fun j => c.nmem (Fb + j)) i ∧
        c'.nmem (IXb + cnt (fun j => c.nmem (Fb + j)) i) = i) ∧
      (∀ a, ¬ (CIb ≤ a ∧ a < IXb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ rout → (x < 6300 ∨ 6309 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, a3, n1, m1, rr1, rm1, o1⟩ := smLkA_exec (I := I) c hc
    (rn := rn) (rF := rF) (rCI := rCI) (rIX := rIX) h1 h2 h3 h4
  obtain ⟨c₂, t₂, e₂, ht₂, b6, k2, mm2, n2, rr2, rm2, o2⟩ := lkProg_exec (P := I) c₁ e₁.wb_right
    (a0.trans r0) (a1.trans r1) (a2.trans r2) (a3.trans r3) l1 l2 l3 w4
  obtain ⟨c₃, t₃, e₃, ht₃, v3, n3, m3, rr3, rm3, o3⟩ := cpyR_exec (I := I) c₂ e₂.wb_right
    (r := rout) (a := 6306)
  rw [m1] at b6 k2
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by clear * - ht₁ ht₂ ht₃; omega, by rw [v3, b6], ?_,
    fun a ha => by rw [m3, mm2 a ha, m1], fun x hx1 hx2 => ?_, by rw [rr3, rr2, rr1],
    by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
  · intro i hi hf
    rw [m3]
    exact k2 i hi hf
  · rw [n3 x hx1, n2 x (by clear * - hx2; omega), n1 x (by clear * - hx2; omega)]

/-- **The value block `vbCF`.** -/
theorem vbCF_exec (c : Config) (hc : WordsBounded W c) {i LPb HCb RPb : ℕ}
    (r20 : c.nreg 6520 = i) (r21 : c.nreg 6521 = 1) (r07 : c.nreg 5507 = LPb)
    (r34 : c.nreg 6534 = HCb) (r12 : c.nreg 5512 = RPb) (w1 : LPb + i ≤ W) (w2 : HCb + i ≤ W)
    (w3 : RPb + i ≤ W) (w4 : HCb + c.nmem (RPb + i) ≤ W) (hW : 2 ≤ W) :
    ∃ c' k, Exec I W vbCF c c' k ∧ k ≤ 19 ∧
      c'.nreg 6523 = cfV (c.nmem (LPb + i)) (c.nmem (HCb + i))
        (c.nmem (HCb + c.nmem (RPb + i))) ∧
      (∀ x, ¬ vscr x → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have ha := hc.2 (HCb + i)
  have hb := hc.2 (HCb + c.nmem (RPb + i))
  unfold vbCF
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r20, r21, r07, r34, r12]; omega)
  refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
    simp (disch := omega) only [upd_other, upd_same, r20, r21, r07, r34, r12]
    unfold cfV; rfl
  · unfold vscr at hx
    config_simp; simp (disch := omega) only [upd_other, upd_same]

/-- **The map `CF` on the machine**: `CF[i] = cfV LP[i] HC[i] HC[RP[i]]` at `B3`. -/
theorem smB2_exec (c : Config) (hc : WordsBounded W c) {n LPb HCb RPb Ob : ℕ}
    (r04 : c.nreg 5504 = n) (r21 : c.nreg 6521 = 1) (r07 : c.nreg 5507 = LPb)
    (r34 : c.nreg 6534 = HCb) (r12 : c.nreg 5512 = RPb) (r10 : c.nreg 5510 = Ob)
    (o1 : LPb + n ≤ Ob) (o2 : HCb + n ≤ Ob) (o3 : RPb + n ≤ Ob) (w : Ob + n ≤ W) (hW : 2 ≤ W)
    (hrp : ∀ i < n, c.nmem (RPb + i) < n) :
    ∃ c' t, Exec I W smB2 c c' t ∧ t ≤ 24 * n + 3 ∧
      (∀ i < n, c'.nmem (Ob + i) = cfV (c.nmem (LPb + i)) (c.nmem (HCb + i))
        (c.nmem (HCb + c.nmem (RPb + i)))) ∧
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', t, e, ht, h1, h2, h3, h4, h5, h6⟩ := mapRun_exec (P := I) c hc (vb := vbCF)
    (bnd := 5504) (ob := 5510) (m := n) (Ob := Ob) (B := 19)
    (fun i => cfV (c.nmem (LPb + i)) (c.nmem (HCb + i)) (c.nmem (HCb + c.nmem (RPb + i))))
    r04 r21 r10 w (by clear * - w o1 hW; omega) (by unfold vscr; decide) (by unfold vscr; decide)
    (by decide) (by decide) (by decide) (by decide)
    (fun i hi c' hw h20 hr hm => by
      have R : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x := hr
      have e1 : c'.nmem (LPb + i) = c.nmem (LPb + i) := hm _ (by clear * - hi o1; omega)
      have e2 : c'.nmem (HCb + i) = c.nmem (HCb + i) := hm _ (by clear * - hi o2; omega)
      have e3 : c'.nmem (RPb + i) = c.nmem (RPb + i) := hm _ (by clear * - hi o3; omega)
      have hr' := hrp i hi
      have e4 : c'.nmem (HCb + c.nmem (RPb + i)) = c.nmem (HCb + c.nmem (RPb + i)) :=
        hm _ (by clear * - hr' o2; omega)
      obtain ⟨c'', k, ex, hk, v, nn, mm, rr, rm, oo⟩ := vbCF_exec (I := I) c' hw h20
        ((R 6521 (by unfold vscr; decide) (by decide) (by decide)).trans r21)
        ((R 5507 (by unfold vscr; decide) (by decide) (by decide)).trans r07)
        ((R 6534 (by unfold vscr; decide) (by decide) (by decide)).trans r34)
        ((R 5512 (by unfold vscr; decide) (by decide) (by decide)).trans r12)
        (by clear * - hi o1 w; omega) (by clear * - hi o2 w; omega) (by clear * - hi o3 w; omega)
        (by rw [e3]; clear * - hr' o2 w; omega) hW
      refine ⟨c'', k, ex, hk, ?_, nn, mm, rr, rm, oo⟩
      rw [v, e1, e2, e3, e4])
  exact ⟨c', t, e, by clear * - ht; omega, h1, h2, h3, h4, h5, h6⟩

end Exec

end MfDrv

end BKMNW

end PlanarFlow
