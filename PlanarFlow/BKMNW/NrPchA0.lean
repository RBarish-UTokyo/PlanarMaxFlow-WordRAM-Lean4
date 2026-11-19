module

public import PlanarFlow.BKMNW.NrPchG

/-!
# `pchP`, phase A: the bases, the vertex labels and the net outflows

* **`PchR`**: the registers of `pchP` after its set-up (`r3004 = d`, `9200 = A`, `9201 = BT`,
  `9202 = FR`, `9203 = Kd`, `9204 = m`, `9205 = Z`, the frame's `RV`, `SG`, `FL` bases and the
  scratch bases `A + k m`); `PchR.congr`;
* `pG0 = pG0a ; pG0b ; pG0c ; pG0d`, **`pG0_exec`**;
* **`pchA = pG0 ; dvP ; pG1 ; decL ; pG2 ; dvL`**, **`pchA_exec`**: within `68 m + 100` steps,
  `VL[i] = olab SG i` at `A + 3m`, `DV[v] = Kd + dvS … v - Z · dvC … v` at `A + 4m`, memory
  changed only in `[A, A + 5m)`.

Scratch layout of `pchP` (from `A`, `m` cells each unless stated): `LAB`, `DVs`, `DG` (`dvP`),
`VL` (`3m`), `DV` (`4m`), `NX` (`5m`), `FLB` (`6m`), `F0` (`7m`), `CR` (`8m`), `KY` (`9m`),
`NH` (`10m`), `ONE` (`11m`), `OB`, `OE`, `OL` (`12m … 15m`), `osProg`'s scratch (`15m`, `2m+1`
cells), `CRV` (`18m`), the scratch `R` of `nrPass`/`kahnP` (`19m`, `11m + 1` cells).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

/-- **The registers of `pchP` after the set-up.** -/
structure PchR (c : Config) (d A BT FR Kd m Z : ℕ) : Prop where
  r3004 : c.nreg 3004 = d
  r00 : c.nreg 9200 = A
  r01 : c.nreg 9201 = BT
  r02 : c.nreg 9202 = FR
  r03 : c.nreg 9203 = Kd
  r04 : c.nreg 9204 = m
  r05 : c.nreg 9205 = Z
  r06 : c.nreg 9206 = d + 4 + m
  r07 : c.nreg 9207 = d + 4 + 2 * m
  r08 : c.nreg 9208 = d + 4 + 6 * m
  r10 : c.nreg 9210 = A + 3 * m
  r11 : c.nreg 9211 = A + 4 * m
  r12 : c.nreg 9212 = A + 5 * m
  r13 : c.nreg 9213 = A + 6 * m
  r14 : c.nreg 9214 = A + 7 * m
  r15 : c.nreg 9215 = A + 8 * m
  r16 : c.nreg 9216 = A + 9 * m
  r17 : c.nreg 9217 = A + 10 * m
  r18 : c.nreg 9218 = A + 11 * m
  r19 : c.nreg 9219 = A + 12 * m
  r20 : c.nreg 9220 = A + 13 * m
  r21 : c.nreg 9221 = A + 14 * m
  r22 : c.nreg 9222 = A + 15 * m
  r23 : c.nreg 9223 = A + 16 * m + 1
  r24 : c.nreg 9224 = A + 18 * m
  r25 : c.nreg 9225 = A + 19 * m

lemma PchR.congr {c c' : Config} {d A BT FR Kd m Z : ℕ} (h : PchR c d A BT FR Kd m Z)
    (hk : ∀ x, 9200 ≤ x → x ≤ 9225 → c'.nreg x = c.nreg x)
    (h3 : c'.nreg 3004 = c.nreg 3004) : PchR c' d A BT FR Kd m Z where
  r3004 := by rw [h3, h.r3004]
  r00 := by rw [hk _ (by omega) (by omega), h.r00]
  r01 := by rw [hk _ (by omega) (by omega), h.r01]
  r02 := by rw [hk _ (by omega) (by omega), h.r02]
  r03 := by rw [hk _ (by omega) (by omega), h.r03]
  r04 := by rw [hk _ (by omega) (by omega), h.r04]
  r05 := by rw [hk _ (by omega) (by omega), h.r05]
  r06 := by rw [hk _ (by omega) (by omega), h.r06]
  r07 := by rw [hk _ (by omega) (by omega), h.r07]
  r08 := by rw [hk _ (by omega) (by omega), h.r08]
  r10 := by rw [hk _ (by omega) (by omega), h.r10]
  r11 := by rw [hk _ (by omega) (by omega), h.r11]
  r12 := by rw [hk _ (by omega) (by omega), h.r12]
  r13 := by rw [hk _ (by omega) (by omega), h.r13]
  r14 := by rw [hk _ (by omega) (by omega), h.r14]
  r15 := by rw [hk _ (by omega) (by omega), h.r15]
  r16 := by rw [hk _ (by omega) (by omega), h.r16]
  r17 := by rw [hk _ (by omega) (by omega), h.r17]
  r18 := by rw [hk _ (by omega) (by omega), h.r18]
  r19 := by rw [hk _ (by omega) (by omega), h.r19]
  r20 := by rw [hk _ (by omega) (by omega), h.r20]
  r21 := by rw [hk _ (by omega) (by omega), h.r21]
  r22 := by rw [hk _ (by omega) (by omega), h.r22]
  r23 := by rw [hk _ (by omega) (by omega), h.r23]
  r24 := by rw [hk _ (by omega) (by omega), h.r24]
  r25 := by rw [hk _ (by omega) (by omega), h.r25]

/-- The set-up of `pchP`. -/
def pG0 : Stmt := .seq (.seq pG0a pG0b) (.seq pG0c pG0d)


section Exec

variable {P : Input} {W : ℕ}

/-- The first half of the set-up. -/
theorem pG0ab_exec (c : Config) (hc : WordsBounded W c) {d A m : ℕ} (r3004 : c.nreg 3004 = d)
    (r00 : c.nreg 9200 = A) (hm : c.nmem d = m) (w : A + 19 * m + 10 ≤ W)
    (hA : d + 4 + 7 * m ≤ A) :
    ∃ c' t, Exec P W (.seq pG0a pG0b) c c' t ∧ t = 19 ∧
      c'.nreg 9204 = m ∧ c'.nreg 9205 = c.nmem (d + 3) ∧ c'.nreg 9206 = d + 4 + m ∧
      c'.nreg 9207 = d + 4 + 2 * m ∧ c'.nreg 9208 = d + 4 + 6 * m ∧
      c'.nreg 9210 = A + 3 * m ∧ c'.nreg 9211 = A + 4 * m ∧ c'.nreg 9212 = A + 5 * m ∧
      c'.nreg 9213 = A + 6 * m ∧ c'.nreg 8430 = A ∧
      (∀ x, (x < 9204 ∨ 9231 < x) → x ≠ 8430 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a8430, a04, a05, a06, a07, a30, a31, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    pG0a_exec (P := P) c hc (by clear * - w hA r3004; omega) (by clear * - w hA; omega)
      (by clear * - w hA r3004; omega) (by clear * - w hA r3004; omega) (by clear * - w hA; omega)
      (by clear * - w hA r3004; omega) (by rw [r3004, hm]; clear * - w hA; omega)
      (by rw [r3004, hm]; clear * - w hA; omega)
  simp only [r3004, hm] at a04 a06 a07
  simp only [r3004] at a05
  have q₁ : ∀ x, (x < 9204 ∨ 9231 < x) → x ≠ 8430 → c₁.nreg x = c.nreg x := fun x h1 h2 =>
    f₁ x h2 (by clear * - h1; omega) (by clear * - h1; omega) (by clear * - h1; omega)
      (by clear * - h1; omega) (by clear * - h1; omega) (by clear * - h1; omega)
  have b00 : c₁.nreg 9200 = A := by rw [q₁ _ (by decide) (by decide), r00]
  clear f₁ a30 a31
  obtain ⟨c₂, t₂, e₂, ht₂, b08, b10, b11, b12, b13, f₂, m₂, rr₂, rm₂, o₂⟩ :=
    pG0b_exec (P := P) c₁ e₁.wb_right
      (by rw [a07, a04]; clear * - w hA; omega) (by rw [a07, a04]; clear * - w hA; omega)
      (by rw [a07, a04]; clear * - w hA; omega) (by rw [a07, a04]; clear * - w hA; omega)
      (by rw [b00, a04]; clear * - w hA; omega) (by rw [b00, a04]; clear * - w hA; omega)
      (by rw [b00, a04]; clear * - w hA; omega) (by rw [b00, a04]; clear * - w hA; omega)
      (by rw [b00, a04]; clear * - w hA; omega) (by rw [b00, a04]; clear * - w hA; omega)
  simp only [a07, a04, b00] at b08 b10 b11 b12 b13
  have K : ∀ x, x ≠ 9208 → x ≠ 9210 → x ≠ 9211 → x ≠ 9212 → x ≠ 9213 →
      c₂.nreg x = c₁.nreg x := f₂
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by rw [ht₁, ht₂],
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide), a04],
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide), a05],
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide), a06],
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide), a07]; clear * -; omega,
    by rw [b08]; clear * -; omega, by rw [b10]; clear * -; omega,
    by rw [b11]; clear * -; omega, by rw [b12]; clear * -; omega,
    by rw [b13]; clear * -; omega,
    by rw [K _ (by decide) (by decide) (by decide) (by decide) (by decide), a8430, r00],
    fun x h1 h2 => ?_, by rw [m₂, m₁], by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  rw [K x (by clear * - h1; omega) (by clear * - h1; omega) (by clear * - h1; omega)
    (by clear * - h1; omega) (by clear * - h1; omega), q₁ x h1 h2]

/-- The second half of the set-up. -/
theorem pG0cd_exec (c : Config) (hc : WordsBounded W c) {A m : ℕ} (r04 : c.nreg 9204 = m)
    (r13 : c.nreg 9213 = A + 6 * m) (w : A + 19 * m + 10 ≤ W) (hA : 0 ≤ A) :
    ∃ c' t, Exec P W (.seq pG0c pG0d) c c' t ∧ t = 16 ∧
      c'.nreg 9214 = A + 7 * m ∧ c'.nreg 9215 = A + 8 * m ∧ c'.nreg 9216 = A + 9 * m ∧
      c'.nreg 9217 = A + 10 * m ∧ c'.nreg 9218 = A + 11 * m ∧ c'.nreg 9219 = A + 12 * m ∧
      c'.nreg 9220 = A + 13 * m ∧ c'.nreg 9221 = A + 14 * m ∧ c'.nreg 9222 = A + 15 * m ∧
      c'.nreg 9223 = A + 16 * m + 1 ∧ c'.nreg 9224 = A + 18 * m ∧ c'.nreg 9225 = A + 19 * m ∧
      (∀ x, (x < 9214 ∨ 9231 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₃, t₃, e₃, ht₃, d14, d15, d16, d17, d18, d19, d20, d21, d22, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    pG0c_exec (P := P) c hc
      (by rw [r13, r04]; clear * - w hA; omega) (by rw [r13, r04]; clear * - w hA; omega)
      (by rw [r13, r04]; clear * - w hA; omega) (by rw [r13, r04]; clear * - w hA; omega)
      (by rw [r13, r04]; clear * - w hA; omega) (by rw [r13, r04]; clear * - w hA; omega)
      (by rw [r13, r04]; clear * - w hA; omega) (by rw [r13, r04]; clear * - w hA; omega)
      (by rw [r13, r04]; clear * - w hA; omega)
  simp only [r13, r04] at d14 d15 d16 d17 d18 d19 d20 d21 d22
  have q₃ : ∀ x, (x < 9214 ∨ 9222 < x) → c₃.nreg x = c.nreg x := fun x hx =>
    f₃ x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
      (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
  have e04 : c₃.nreg 9204 = m := by rw [q₃ _ (by decide), r04]
  have e22 : c₃.nreg 9222 = A + 15 * m := by rw [d22]; clear * -; omega
  clear f₃
  obtain ⟨c₄, t₄, e₄, ht₄, g23, g24, g25, g30, f₄, m₄, rr₄, rm₄, o₄⟩ :=
    pG0d_exec (P := P) c₃ e₃.wb_right (by clear * - w hA; omega)
      (by rw [e22, e04]; clear * - w hA; omega) (by rw [e22, e04]; clear * - w hA; omega)
      (by rw [e22, e04]; clear * - w hA; omega)
      (by rw [e22, e04]; clear * - w hA; omega) (by rw [e22, e04]; clear * - w hA; omega)
  simp only [e22, e04] at g23 g24 g25
  have q₄ : ∀ x, x ≠ 9223 → x ≠ 9224 → x ≠ 9225 → x ≠ 9230 → c₄.nreg x = c₃.nreg x := f₄
  have K3 : ∀ x, 9214 ≤ x → x ≤ 9222 → c₄.nreg x = c₃.nreg x := fun x h1 h2 =>
    q₄ x (by clear * - h2; omega) (by clear * - h2; omega) (by clear * - h2; omega)
      (by clear * - h2; omega)
  refine ⟨c₄, t₃ + t₄, .seq e₃ e₄, by rw [ht₃, ht₄],
    by rw [K3 _ (by decide) (by decide), d14]; clear * -; omega,
    by rw [K3 _ (by decide) (by decide), d15]; clear * -; omega,
    by rw [K3 _ (by decide) (by decide), d16]; clear * -; omega,
    by rw [K3 _ (by decide) (by decide), d17]; clear * -; omega,
    by rw [K3 _ (by decide) (by decide), d18]; clear * -; omega,
    by rw [K3 _ (by decide) (by decide), d19]; clear * -; omega,
    by rw [K3 _ (by decide) (by decide), d20]; clear * -; omega,
    by rw [K3 _ (by decide) (by decide), d21]; clear * -; omega,
    by rw [K3 _ (by decide) (by decide), d22]; clear * -; omega,
    by rw [g23]; clear * -; omega, by rw [g24]; clear * -; omega,
    by rw [g25]; clear * -; omega, fun x hx => ?_, by rw [m₄, m₃], by rw [rr₄, rr₃],
    by rw [rm₄, rm₃], by rw [o₄, o₃]⟩
  rw [q₄ x (by clear * - hx; omega) (by clear * - hx; omega) (by clear * - hx; omega)
    (by clear * - hx; omega), q₃ x (by clear * - hx; omega)]

/-- **The set-up of `pchP`.** -/
theorem pG0_exec (c : Config) (hc : WordsBounded W c) {d A m : ℕ} (r3004 : c.nreg 3004 = d)
    (r00 : c.nreg 9200 = A) (hm : c.nmem d = m) (w : A + 19 * m + 10 ≤ W)
    (hA : d + 4 + 7 * m ≤ A) :
    ∃ c' t, Exec P W pG0 c c' t ∧ t = 35 ∧
      PchR c' d A (c.nreg 9201) (c.nreg 9202) (c.nreg 9203) m (c.nmem (d + 3)) ∧
      c'.nreg 8430 = A ∧
      (∀ x, (x < 9204 ∨ 9231 < x) → x ≠ 8430 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₂, t₂, e₂, ht₂, a04, a05, a06, a07, a08, a10, a11, a12, a13, a84, f₂, m₂, rr₂, rm₂,
    o₂⟩ := pG0ab_exec (P := P) c hc r3004 r00 hm w hA
  obtain ⟨c₄, t₄, e₄, ht₄, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, f₄, m₄,
    rr₄, rm₄, o₄⟩ := pG0cd_exec (P := P) c₂ e₂.wb_right a04 a13 (by clear * - w hA; omega) (Nat.zero_le _)
  have q : ∀ x, 9204 ≤ x → x ≤ 9213 → c₄.nreg x = c₂.nreg x := fun x h1 h2 =>
    f₄ x (by clear * - h2; omega)
  refine ⟨c₄, t₂ + t₄, .seq e₂ e₄, by rw [ht₂, ht₄],
    ⟨by rw [f₄ _ (by decide), f₂ _ (by decide) (by decide), r3004],
      by rw [f₄ _ (by decide), f₂ _ (by decide) (by decide), r00],
      by rw [f₄ _ (by decide), f₂ _ (by decide) (by decide)],
      by rw [f₄ _ (by decide), f₂ _ (by decide) (by decide)],
      by rw [f₄ _ (by decide), f₂ _ (by decide) (by decide)],
      by rw [q _ (by decide) (by decide), a04], by rw [q _ (by decide) (by decide), a05],
      by rw [q _ (by decide) (by decide), a06], by rw [q _ (by decide) (by decide), a07],
      by rw [q _ (by decide) (by decide), a08], by rw [q _ (by decide) (by decide), a10],
      by rw [q _ (by decide) (by decide), a11], by rw [q _ (by decide) (by decide), a12],
      by rw [q _ (by decide) (by decide), a13], b14, b15, b16, b17, b18, b19, b20, b21, b22, b23,
      b24, b25⟩,
    by rw [f₄ _ (by decide), a84], fun x h1 h2 => ?_, by rw [m₄, m₂], by rw [rr₄, rr₂],
    by rw [rm₄, rm₂], by rw [o₄, o₂]⟩
  rw [f₄ x (by clear * - h1; omega), f₂ x h1 h2]

end Exec

end BKMNW

end PlanarFlow
