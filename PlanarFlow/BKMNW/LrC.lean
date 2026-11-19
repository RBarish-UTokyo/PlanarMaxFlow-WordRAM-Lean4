module

public import PlanarFlow.BKMNW.LrB

/-!
# The children's records of the large split: one child, first half

**`lrOneA = lrLP ; smXB1 ; lrBc`** (registers of `LrB.lean`): the flags `LP` of the child `t` at
`A + n`, the children's data of stage B (`smXB1`: `KC`, `HC`, the compactions of `LP` and of
`CF = smCF`), and the flags of the child's core piece map `CF · CC` at `Y + 3 n`.

* `cfV_le_one`;
* **`lrOneA_exec`**: within `216 n + 21 k + 130` steps; all the values in terms of the memory
  `mem₁` after `lrLP` (the memory at the start with `LP` at `A + n`).
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

lemma cfV_le_one (lp a b : ℕ) : cfV lp a b ≤ 1 := by unfold cfV; omega

/-- **One child's data, first half.** -/
def lrOneA : Stmt := .seq lrLP (.seq smXB1 lrBc)

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **One child's data, first half** (see the module docstring). -/
theorem lrOneA_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb A Y LFb CCb t : ℕ}
    (hR : SmRegs c d m k R n Sb A) (r21 : c.nreg 6521 = 1)
    (r00 : c.nreg 8500 = LFb) (r08 : c.nreg 8508 = t) (r84 : c.nreg 8504 = CCb)
    (r16 : c.nreg 8516 = Y + 3 * n)
    (hrp : ∀ i < n, c.nmem (R + 3 + n + i) < n) (hhp : ∀ i < n, c.nmem (R + 3 + 2 * n + i) ≤ k)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (oY : A + 16 * n + 4 * k + 2 ≤ Y)
    (oL : Y + 4 * n ≤ LFb) (oC : Y + 4 * n ≤ CCb)
    (w : A + 22 * n + m + 4 * k + 20 ≤ W) (wY : Y + 4 * n ≤ W) (wL : LFb + n ≤ W)
    (wC : CCb + n ≤ W) (hW : 21 ≤ W) :
    ∃ c' t' mem₁, Exec I W lrOneA c c' t' ∧ t' ≤ 216 * n + 21 * k + 130 ∧
      SmRegs c' d m k R n Sb A ∧ c'.nreg 6521 = 1 ∧
      c'.nreg 6533 = A + 4 * n + k + 2 + 3 * n ∧ c'.nreg 6534 = A + 4 * n + k + 2 + 4 * n ∧
      (∀ i < n, mem₁ (A + n + i) = (t - c.nmem (LFb + i)) + (c.nmem (LFb + i) - t)) ∧
      (∀ a, ¬ (A + n ≤ a ∧ a < A + 2 * n) → mem₁ a = c.nmem a) ∧
      (∀ a, a < A + 4 * n + k + 2 → c'.nmem a = mem₁ a) ∧
      (∀ i < n, c'.nmem (A + 4 * n + k + 2 + 3 * n + i) = smKC mem₁ A R n i) ∧
      (∀ i < n, c'.nmem (A + 4 * n + k + 2 + 4 * n + i) = smHC mem₁ A R n k i) ∧
      c'.nreg 5540 = cnt (fun j => mem₁ (A + n + j)) n ∧
      (∀ i < n, 0 < mem₁ (A + n + i) →
        c'.nmem (A + 11 * n + 4 * k + 2 + i) = cnt (fun j => mem₁ (A + n + j)) i ∧
        c'.nmem (A + 12 * n + 4 * k + 2 + cnt (fun j => mem₁ (A + n + j)) i) = i) ∧
      c'.nreg 5541 = cnt (fun j => smCF mem₁ A R n k j) n ∧
      (∀ i < n, 0 < smCF mem₁ A R n k i →
        c'.nmem (A + 15 * n + 4 * k + 2 + cnt (fun j => smCF mem₁ A R n k j) i) = i) ∧
      (∀ i < n, c'.nmem (Y + 3 * n + i) = smCF mem₁ A R n k i * c.nmem (CCb + i)) ∧
      (∀ a, a < A + n → c'.nmem a = c.nmem a) ∧
      (∀ a, A + 2 * n ≤ a → a < A + 4 * n + k + 2 → c'.nmem a = c.nmem a) ∧
      (∀ a, A + 16 * n + 4 * k + 2 ≤ a → ¬ (Y + 3 * n ≤ a ∧ a < Y + 4 * n) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 3013 ∨ 8000 ≤ x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hA := hR.hA
  -- the flags of the child
  obtain ⟨c₁, t₁, e₁, ht₁, f1, m1, n1, rr1, rm1, o1'⟩ := lrLP_exec (I := I) c hc hR.r04 r21 hR.r07
    r00 r08 (Or.inr (by clear * - oY oL; omega)) (by clear * - w; omega) wL
    (by clear * - w; omega)
  have q1 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₁.nreg x = c.nreg x := n1
  have hR1 : SmRegs c₁ d m k R n Sb A := hR.congr fun x hx =>
    q1 x (by clear * - hx; unfold smReg at hx; unfold vscr; omega)
      (by clear * - hx; unfold smReg at hx; omega) (by clear * - hx; unfold smReg at hx; omega)
  have M1 : ∀ a, ¬ (A + n ≤ a ∧ a < A + 2 * n) → c₁.nmem a = c.nmem a := fun a ha =>
    m1 a (by clear * - ha; omega)
  -- stage B, first part
  obtain ⟨c₂, t₂, e₂, ht₂, hR2, s21, s33, s34, KC, HC, s40, CIX, s41, IX2, lo2, hi2, CF, n2, rr2,
    rm2, o2⟩ := smXB1_exec' (I := I) c₁ e₁.wb_right hR1
      ((q1 6521 (by unfold vscr; decide) (by decide) (by decide)).trans r21)
      (fun i hi => by rw [M1 _ (by clear * - hi hA o1; omega)]; exact hrp i hi)
      (fun i hi => by rw [M1 _ (by clear * - hi hA o1; omega)]; exact hhp i hi) o1 w hW
  -- the flags of the child's core piece map
  have q2 : ∀ x, (x < 3013 ∨ 8000 ≤ x) → c₂.nreg x = c₁.nreg x := n2
  have r84' : c₂.nreg 8504 = CCb := by
    rw [q2 _ (by decide), q1 _ (by unfold vscr; decide) (by decide) (by decide)]; exact r84
  have r16' : c₂.nreg 8516 = Y + 3 * n := by
    rw [q2 _ (by decide), q1 _ (by unfold vscr; decide) (by decide) (by decide)]; exact r16
  have CC2 : ∀ i < n, c₂.nmem (CCb + i) = c.nmem (CCb + i) := fun i hi => by
    rw [hi2 _ (by clear * - hi oY oC; omega), M1 _ (by clear * - hi hA oY oC; omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, b3, m3, n3, rr3, rm3, o3⟩ := lrBc_exec (I := I) c₂ e₂.wb_right
    hR2.r04 s21 hR2.r10 r84' r16' (Or.inl (by clear * - hA oY; omega))
    (Or.inr (by clear * - oC; omega)) (by clear * - wY; omega) (by clear * - w hA; omega) wC
    (by clear * - w; omega) (fun i hi => by rw [CF i hi]; exact cfV_le_one _ _ _)
  have q3 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₃.nreg x = c₂.nreg x := n3
  have hR3 : SmRegs c₃ d m k R n Sb A := hR2.congr fun x hx =>
    q3 x (by clear * - hx; unfold smReg at hx; unfold vscr; omega)
      (by clear * - hx; unfold smReg at hx; omega) (by clear * - hx; unfold smReg at hx; omega)
  have M3 : ∀ a, a < Y + 3 * n → c₃.nmem a = c₂.nmem a := fun a ha => m3 a (by clear * - ha; omega)
  have ht : t₁ + (t₂ + t₃) ≤ 216 * n + 21 * k + 130 := by clear * - ht₁ ht₂ ht₃; omega
  refine ⟨c₃, _, c₁.nmem, .seq e₁ (.seq e₂ e₃), ht, hR3,
    (q3 6521 (by unfold vscr; decide) (by decide) (by decide)).trans s21,
    (q3 6533 (by unfold vscr; decide) (by decide) (by decide)).trans s33,
    (q3 6534 (by unfold vscr; decide) (by decide) (by decide)).trans s34, f1, M1,
    fun a ha => by rw [M3 _ (by clear * - ha hA oY; omega), lo2 _ ha],
    fun i hi => by rw [M3 _ (by clear * - hi hA oY; omega)]; exact KC i hi,
    fun i hi => by rw [M3 _ (by clear * - hi hA oY; omega)]; exact HC i hi,
    by rw [q3 5540 (by unfold vscr; decide) (by decide) (by decide)]; exact s40,
    fun i hi hf => ?_,
    by rw [q3 5541 (by unfold vscr; decide) (by decide) (by decide)]; exact s41,
    fun i hi hf => ?_,
    fun i hi => by rw [b3 i hi, CF i hi, CC2 i hi],
    fun a ha => ?_, fun a h1 h2 => ?_, fun a h1 h2 => ?_, fun x hx => ?_,
    by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1], by rw [o3, o2, o1']⟩
  · obtain ⟨k1, k2⟩ := CIX i hi hf
    have := cnt_le (fun j => c₁.nmem (A + n + j)) i
    exact ⟨by rw [M3 _ (by clear * - hi hA oY; omega)]; exact k1,
      by rw [M3 _ (by clear * - this hi hA oY; omega)]; exact k2⟩
  · have := cnt_le (fun j => smCF c₁.nmem A R n k j) i
    rw [M3 _ (by clear * - this hi hA oY; omega)]; exact IX2 i hi hf
  · rw [M3 _ (by clear * - ha hA oY; omega), lo2 _ (by clear * - ha; omega),
      M1 _ (by clear * - ha; omega)]
  · rw [M3 _ (by clear * - h2 hA oY; omega), lo2 _ (by clear * - h2; omega),
      M1 _ (by clear * - h1; omega)]
  · rw [m3 a (by clear * - h2; omega), hi2 a h1, M1 _ (by clear * - h1 hA; omega)]
  · rw [q3 x (by clear * - hx; unfold vscr; omega) (by clear * - hx; omega)
      (by clear * - hx; omega), q2 x hx,
      q1 x (by clear * - hx; unfold vscr; omega) (by clear * - hx; omega) (by clear * - hx; omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
