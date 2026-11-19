module

public import PlanarFlow.BKMNW.LrD

/-!
# The children's records of the large split: one child, second half composed

**`lrOneB_exec`**: `lrB4b ; smB6 ; lrSP ; smB5 ; lrHd` from the state after `lrOneA` and
`lrCr`: the record of the child at `R' = XX + 2` (`XX = r8509`) in terms of the memory at the
start (the parent record at `R`, `LP` at `A + n` with its compaction `CI`/`IX`, the compaction `IX2`
of `CF`, `KC`, `HC`, the flags `Bc` at `Y + 3 n`, the rotation `CN` at `Y + 6 n`); memory below
`XX + 2` and from `XX + 7 n + 6` on kept; within `64 n + 120` steps.
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

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **One child's record, second half** (see the module docstring). -/
theorem lrOneB_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb A Y XX nX mX hb : ℕ}
    (hR : SmRegs c d m k R n Sb A) (r21 : c.nreg 6521 = 1)
    (r33 : c.nreg 6533 = A + 4 * n + k + 2 + 3 * n) (r34 : c.nreg 6534 = A + 4 * n + k + 2 + 4 * n)
    (r40 : c.nreg 5540 = nX) (r41 : c.nreg 5541 = mX) (r05 : c.nreg 8505 = hb)
    (r09 : c.nreg 8509 = XX) (r16 : c.nreg 8516 = Y + 3 * n) (r17 : c.nreg 8517 = Y + 6 * n)
    (hci : ∀ i < n, 0 < c.nmem (A + n + i) →
      c.nmem (A + 11 * n + 4 * k + 2 + i) = cnt (fun j => c.nmem (A + n + j)) i ∧
      c.nmem (A + 12 * n + 4 * k + 2 + cnt (fun j => c.nmem (A + n + j)) i) = i)
    (hnX : nX = cnt (fun j => c.nmem (A + n + j)) n) (hmX : mX ≤ n)
    (hix2 : ∀ j < mX, c.nmem (A + 15 * n + 4 * k + 2 + j) < n)
    (hrp : ∀ i < n, c.nmem (R + 3 + n + i) < n)
    (hBF : ∀ i < n, 0 < c.nmem (Y + 3 * n + i) → 0 < c.nmem (A + n + i))
    (hCN : ∀ i < n, 0 < c.nmem (Y + 3 * n + i) → c.nmem (Y + 6 * n + i) < n)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (oY : A + 16 * n + 4 * k + 2 ≤ Y) (oX : Y + 8 * n ≤ XX)
    (w : XX + 7 * n + 8 ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec I W lrOneB c c' t ∧ t ≤ 80 * n + 100 ∧
      SmRegs c' d m k R n Sb A ∧ c'.nreg 6521 = 1 ∧
      c'.nreg 8510 = 6 * nX + mX + 3 ∧
      c'.nmem (XX + 2) = nX ∧ c'.nmem (XX + 2 + 1) = 0 ∧ c'.nmem (XX + 2 + 2) = 1 - hb ∧
      (∀ j < nX, c'.nmem (XX + 2 + 3 + j) =
        c.nmem (R + 3 + c.nmem (A + 12 * n + 4 * k + 2 + j))) ∧
      (∀ i < n, 0 < c.nmem (A + n + i) →
        c'.nmem (XX + 2 + 3 + nX + c.nmem (A + 11 * n + 4 * k + 2 + i)) =
          c.nmem (A + 11 * n + 4 * k + 2 + c.nmem (R + 3 + n + i))) ∧
      (∀ j < nX, c'.nmem (XX + 2 + 3 + 2 * nX + j) =
        c.nmem (A + 4 * n + k + 2 + 4 * n + c.nmem (A + 12 * n + 4 * k + 2 + j))) ∧
      (∀ j < nX, c'.nmem (XX + 2 + 3 + 3 * nX + j) =
        c.nmem (A + 4 * n + k + 2 + 3 * n + c.nmem (A + 12 * n + 4 * k + 2 + j))) ∧
      (∀ j < nX, c'.nmem (XX + 2 + 3 + 4 * nX + j) =
        c.nmem (R + 3 + 4 * n + c.nmem (A + 12 * n + 4 * k + 2 + j))) ∧
      (∀ i < n, 0 < c.nmem (Y + 3 * n + i) →
        c'.nmem (XX + 2 + 3 + 5 * nX + c.nmem (A + 11 * n + 4 * k + 2 + i)) =
          c.nmem (A + 11 * n + 4 * k + 2 + c.nmem (Y + 6 * n + i))) ∧
      (∀ j < mX, c'.nmem (XX + 2 + 3 + 6 * nX + j) =
        c.nmem (A + 11 * n + 4 * k + 2 + c.nmem (A + 15 * n + 4 * k + 2 + j))) ∧
      (∀ a, a < XX + 2 → c'.nmem a = c.nmem a) ∧
      (∀ a, XX + 7 * n + 6 ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 3013 ∨ (8000 ≤ x ∧ x ≠ 8510)) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hA := hR.hA
  set F : ℕ → ℕ := fun j => c.nmem (A + n + j) with hF
  have cntlt : ∀ i < n, 0 < F i → cnt F i < nX := fun i hi hf => by
    rw [hnX]; exact cnt_lt_of F hi hf
  have hnXn : nX ≤ n := by rw [hnX]; exact cnt_le F n
  have hIX : ∀ j < nX, c.nmem (A + 12 * n + 4 * k + 2 + j) < n := fun j hj => by
    obtain ⟨i, hi, hfi, rfl⟩ := cnt_surj F n j (by omega)
    rw [(hci i hi hfi).2]; exact hi
  -- the bases
  obtain ⟨c₁, t₁, e₁, ht₁, b42, b54, b55, b56, b57, b58, b59, b60, n1, m1, rr1, rm1, o1'⟩ :=
    lrB4b_exec (I := I) c hc r09 r40 (by clear * - w hnXn; omega)
  have q1 : ∀ x, (x < 5519 ∨ (5519 < x ∧ x < 5542) ∨ (5542 < x ∧ x < 5554) ∨ 5560 < x) →
      c₁.nreg x = c.nreg x := n1
  have hR1 : SmRegs c₁ d m k R n Sb A := hR.congr fun x hx =>
    q1 x (by clear * - hx; unfold smReg at hx; omega)
  -- the reverse indices
  obtain ⟨c₂, t₂, e₂, ht₂, rp2, m2, n2, rr2, rm2, o2⟩ := smB6_exec (I := I) c₁ e₁.wb_right
    hR1.r04 hR1.r07 hR1.r09 hR1.r12 b55 (by clear * - hA oY oX; omega)
    (by clear * - hA oY oX; omega) (by clear * - hA oY oX o1; omega)
    (by clear * - w hnXn; omega) hW
    (fun i hi hf => by rw [m1] at hf ⊢; exact hrp i hi)
    (fun i hi hf => by
      rw [m1] at hf ⊢; rw [(hci i hi hf).1]; have := cnt_le F i; clear * - this hi; omega)
    (fun i hi j hj hfi hfj e => by
      rw [m1] at hfi hfj e; rw [(hci i hi hfi).1, (hci j hj hfj).1] at e
      exact cnt_inj F hfi hfj e)
  have q2 : ∀ x, (x < 6310 ∨ 6319 < x) → c₂.nreg x = c₁.nreg x := n2
  have M2 : ∀ a, a < XX + 2 + 3 + nX → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m2 a (by clear * - ha; omega), m1]
  -- the state array
  have r16' : c₂.nreg 8516 = Y + 3 * n := by rw [q2 _ (by decide), q1 _ (by decide)]; exact r16
  have r17' : c₂.nreg 8517 = Y + 6 * n := by rw [q2 _ (by decide), q1 _ (by decide)]; exact r17
  have hR2 : SmRegs c₂ d m k R n Sb A := hR1.congr fun x hx =>
    q2 x (by clear * - hx; unfold smReg at hx; omega)
  obtain ⟨c₃, t₃, e₃, ht₃, sp3, m3, n3, rr3, rm3, o3⟩ := lrSP_exec (I := I) c₂ e₂.wb_right (OUTb := XX + 2 + 3 + 5 * nX)
    hR2.r04 r16' hR2.r09 r17' (by rw [q2 _ (by decide)]; exact b59)
    (by clear * - oX; omega) (by clear * - hA oY oX; omega) (by clear * - oX; omega)
    (by clear * - w hnXn; omega) (by clear * - w; omega)
    (fun i hi hf => by
      rw [M2 _ (by clear * - hi oX; omega)] at hf ⊢; exact hCN i hi hf)
    (fun i hi hf => by
      rw [M2 _ (by clear * - hi oX; omega)] at hf
      rw [M2 _ (by clear * - hi hA oY oX; omega), (hci i hi (hBF i hi hf)).1]
      have := cnt_le F i; clear * - this hi; omega)
    (fun i hi j hj hfi hfj e => by
      rw [M2 _ (by clear * - hi oX; omega)] at hfi
      rw [M2 _ (by clear * - hj oX; omega)] at hfj
      rw [M2 _ (by clear * - hi hA oY oX; omega), M2 _ (by clear * - hj hA oY oX; omega),
        (hci i hi (hBF i hi hfi)).1, (hci j hj (hBF j hj hfj)).1] at e
      exact cnt_inj F (hBF i hi hfi) (hBF j hj hfj) e)
  have q3 : ∀ x, (x < 6310 ∨ 6319 < x) → c₃.nreg x = c₂.nreg x := n3
  have M3 : ∀ a, a < XX + 2 + 3 + 5 * nX → c₃.nmem a = c₂.nmem a := fun a ha =>
    m3 a (by clear * - ha; omega)
  have hR3 : SmRegs c₃ d m k R n Sb A := hR2.congr fun x hx =>
    q3 x (by clear * - hx; unfold smReg at hx; omega)
  have Q31 : ∀ x, (x < 5519 ∨ (5519 < x ∧ x < 5542) ∨ (5542 < x ∧ x < 5554) ∨ 5560 < x) →
      x < 6310 → c₃.nreg x = c.nreg x := fun x h1 h2 => by
    rw [q3 x (Or.inl h2), q2 x (Or.inl h2), q1 x h1]
  -- the five gathers
  have M31 : ∀ a, a < XX + 2 + 3 → c₃.nmem a = c.nmem a := fun a ha => by
    rw [M3 a (by clear * - ha; omega), M2 a (by clear * - ha; omega)]
  obtain ⟨c₄, t₄, e₄, ht₄, g1, g2, g3, g4, g5, m4, n4, rr4, rm4, o4⟩ := smB5_exec (I := I) c₃
    e₃.wb_right (n := n) (Rp := XX + 2) (nl := nX) (ml := mX)
    (IXb := A + 12 * n + 4 * k + 2) (IX2b := A + 15 * n + 4 * k + 2) (GPb := R + 3)
    (HCb := A + 4 * n + k + 2 + 4 * n) (KCb := A + 4 * n + k + 2 + 3 * n) (VPb := R + 3 + 4 * n)
    (CIb := A + 11 * n + 4 * k + 2)
    (by rw [Q31 _ (by decide) (by decide)]; exact r40)
    (by rw [Q31 _ (by decide) (by decide)]; exact r41) hR3.r28 hR3.r31 hR3.r17
    (by rw [q3 _ (by decide), q2 _ (by decide), q1 _ (by decide)]; exact r34)
    (by rw [q3 _ (by decide), q2 _ (by decide), q1 _ (by decide)]; exact r33) hR3.r15 hR3.r09
    (by rw [q3 _ (by decide), q2 _ (by decide)]; exact b54)
    (by rw [q3 _ (by decide), q2 _ (by decide)]; exact b56)
    (by rw [q3 _ (by decide), q2 _ (by decide)]; exact b57)
    (by rw [q3 _ (by decide), q2 _ (by decide)]; exact b58)
    (by rw [q3 _ (by decide), q2 _ (by decide)]; exact b60)
    (fun j hj => by
      rw [M31 _ (by clear * - hj hnXn hA oY oX; omega)]; exact hIX j hj)
    (fun j hj => by
      rw [M31 _ (by clear * - hj hmX hA oY oX; omega)]; exact hix2 j hj)
    (by clear * - hA oY oX o1; omega) (by clear * - hA oY oX; omega)
    (by clear * - hA oY oX; omega) (by clear * - hA oY oX o1; omega)
    (by clear * - hA oY oX; omega) (by clear * - hA oY oX hnXn; omega)
    (by clear * - hA oY oX hmX; omega) (by clear * - w hnXn hmX; omega)
  have q4 : ∀ x, (x < 6210 ∨ 6217 < x) → c₄.nreg x = c₃.nreg x := n4
  -- the header
  have hR4 : SmRegs c₄ d m k R n Sb A := hR3.congr fun x hx =>
    q4 x (by clear * - hx; unfold smReg at hx; omega)
  obtain ⟨c₅, t₅, e₅, ht₅, h10, h0, h1, h2, m5, n5, rr5, rm5, o5⟩ := lrHd_exec (I := I) c₄
    e₄.wb_right (XX := XX) (nl := nX) (ml := mX) (hb := hb)
    (by rw [q4 _ (by decide), q3 _ (by decide), q2 _ (by decide)]; exact b42)
    (by rw [q4 _ (by decide), Q31 _ (by decide) (by decide)]; exact r40)
    (by rw [q4 _ (by decide), Q31 _ (by decide) (by decide)]; exact r41)
    (by rw [q4 _ (by decide), q3 _ (by decide), q2 _ (by decide), q1 _ (by decide)]; exact r21)
    (by rw [q4 _ (by decide), q3 _ (by decide), q2 _ (by decide), q1 _ (by decide)]; exact r05)
    (by clear * - w hnXn hmX; omega)
  have q5 : ∀ x, (x < 5519 ∨ (5519 < x ∧ x < 5546) ∨ (5549 < x ∧ x ≠ 8510)) →
      c₅.nreg x = c₄.nreg x := n5
  have hR5 : SmRegs c₅ d m k R n Sb A := hR4.congr fun x hx =>
    q5 x (by clear * - hx; unfold smReg at hx; omega)
  have M5 : ∀ a, XX + 4 < a → c₅.nmem a = c₄.nmem a := fun a ha => m5 a (Or.inr ha)
  have ht : t₁ + (t₂ + (t₃ + (t₄ + t₅))) ≤ 80 * n + 100 := by
    clear * - ht₁ ht₂ ht₃ ht₄ ht₅ hnXn hmX; omega
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ht, hR5, ?_, h10, h0, h1, h2,
    fun j hj => ?_, fun i hi hf => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun i hi hf => ?_, fun j hj => ?_, fun a ha => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [rr5, rr4, rr3, rr2, rr1], by rw [rm5, rm4, rm3, rm2, rm1],
    by rw [o5, o4, o3, o2, o1']⟩
  · rw [q5 _ (by decide), q4 _ (by decide), q3 _ (by decide), q2 _ (by decide),
      q1 _ (by decide)]; exact r21
  · have e1 := M31 (A + 12 * n + 4 * k + 2 + j) (by clear * - hj hnXn hA oY oX; omega)
    have e2 := M31 (R + 3 + c.nmem (A + 12 * n + 4 * k + 2 + j))
      (by have := hIX j hj; clear * - this hA oY oX o1; omega)
    rw [M5 _ (by clear * - hj; omega), g1 j hj, e1, e2]
  · have hlt := cntlt i hi hf
    have hci1 := (hci i hi hf).1
    rw [M5 _ (by clear * - hi; omega),
      m4 _ (Or.inr (Or.inl (by rw [hci1]; clear * - hlt; omega))),
      M3 _ (by rw [hci1]; clear * - hlt; omega)]
    have := rp2 i hi (by rw [m1]; exact hf)
    rw [m1] at this
    exact this
  · have e1 := M31 (A + 12 * n + 4 * k + 2 + j) (by clear * - hj hnXn hA oY oX; omega)
    have e2 := M31 (A + 4 * n + k + 2 + 4 * n + c.nmem (A + 12 * n + 4 * k + 2 + j))
      (by have := hIX j hj; clear * - this hA oY oX; omega)
    rw [M5 _ (by clear * - hj; omega), g2 j hj, e1, e2]
  · have e1 := M31 (A + 12 * n + 4 * k + 2 + j) (by clear * - hj hnXn hA oY oX; omega)
    have e2 := M31 (A + 4 * n + k + 2 + 3 * n + c.nmem (A + 12 * n + 4 * k + 2 + j))
      (by have := hIX j hj; clear * - this hA oY oX; omega)
    rw [M5 _ (by clear * - hj; omega), g3 j hj, e1, e2]
  · have e1 := M31 (A + 12 * n + 4 * k + 2 + j) (by clear * - hj hnXn hA oY oX; omega)
    have e2 := M31 (R + 3 + 4 * n + c.nmem (A + 12 * n + 4 * k + 2 + j))
      (by have := hIX j hj; clear * - this hA oY oX o1; omega)
    rw [M5 _ (by clear * - hj; omega), g4 j hj, e1, e2]
  · have hfF := hBF i hi hf
    have hlt := cntlt i hi hfF
    have hci1 := (hci i hi hfF).1
    have hcn := hCN i hi hf
    rw [M5 _ (by clear * - hi; omega),
      m4 _ (Or.inr (Or.inr (Or.inl (by rw [hci1]; clear * - hlt; omega))))]
    have := sp3 i hi (by rw [M2 _ (by clear * - hi oX; omega)]; exact hf)
    rw [M2 (A + 11 * n + 4 * k + 2 + i) (by clear * - hi hA oY oX; omega),
      M2 (Y + 6 * n + i) (by clear * - hi oX; omega),
      M2 (A + 11 * n + 4 * k + 2 + c.nmem (Y + 6 * n + i)) (by clear * - hcn hA oY oX; omega)]
      at this
    exact this
  · have e1 := M31 (A + 15 * n + 4 * k + 2 + j) (by clear * - hj hmX hA oY oX; omega)
    have e2 := M31 (A + 11 * n + 4 * k + 2 + c.nmem (A + 15 * n + 4 * k + 2 + j))
      (by have := hix2 j hj; clear * - this hA oY oX; omega)
    rw [M5 _ (by clear * - hj; omega), g5 j hj, e1, e2]
  · rw [m5 a (Or.inl ha), m4 a (Or.inl (by clear * - ha; omega)), M31 a (by clear * - ha; omega)]
  · rw [M5 _ (by clear * - ha; omega), m4 a (Or.inr (Or.inr (Or.inr
      (by clear * - ha w hnXn hmX; omega)))),
      m3 a (by clear * - ha hnXn; omega), m2 a (by clear * - ha hnXn; omega), m1]
  · rw [q5 x (by clear * - hx; omega), q4 x (by clear * - hx; omega),
      q3 x (by clear * - hx; omega), q2 x (by clear * - hx; omega), q1 x (by clear * - hx; omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
