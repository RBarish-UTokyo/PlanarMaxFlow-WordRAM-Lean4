module

public import PlanarFlow.BKMNW.SmXB

/-!
# The small separator program, stage B (first part) composed

**`smXB1 = smB0 ; smBF ; smB1 ; smB2 ; smB3`**, **`smXB1_exec`**: from the state after stage A
(`SmRegs`, `r6521 = 1`), over the record's `n` darts (memory `mem` at the start): the children's
ranks `smKC` and hole labels `smHC` at `Wb' + 3 n`, `Wb' + 4 n` (`Wb' = A + 4 n + k + 2`), the
compaction of `LP` (`CI` at `B2`, `IX` at `B2 + n`, `nl = cnt LP n` in `5540`), the flags `smCF`
of the left child's piece map, their compaction (`CI2` at `B3 + n`, `IX2` at `B3 + 2 n`,
`ml = cnt CF n` in `5541`); memory below `Wb'` kept; within `196 n + 21 k + 120` steps.
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

/-- The tail of the record's dart `i` in the new hole (machine's value). -/
def smNH (mem : ℕ → ℕ) (A R n i : ℕ) : ℕ := nhR mem (A + 3 * n) (R + 3 + 2 * n) (A + 4 * n) i

/-- The child's hole label of the tail of the record's dart `i` (machine's value). -/
def smHC (mem : ℕ → ℕ) (A R n k i : ℕ) : ℕ :=
  hcF (smNH mem A R n i) (mem (R + 3 + 2 * n + i))
    (cnt (hfR mem (A + 4 * n)) (mem (R + 3 + 2 * n + i) - 1)) (cnt (hfR mem (A + 4 * n)) k + 1)

/-- The child's rank of the tail of the record's dart `i` (machine's value). -/
def smKC (mem : ℕ → ℕ) (A R n i : ℕ) : ℕ := kcF (smNH mem A R n i) (mem (R + 3 + 3 * n + i))

/-- The flag of the record's dart `i` in the left child's piece map (machine's value). -/
def smCF (mem : ℕ → ℕ) (A R n k i : ℕ) : ℕ :=
  cfV (mem (A + n + i)) (smHC mem A R n k i) (smHC mem A R n k (mem (R + 3 + n + i)))

/-- **Stage B, first part.** -/
def smXB1 : Stmt := .seq smB0 (.seq smBF (.seq smB1 (.seq smB2 smB3)))

section Exec

variable {I : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Stage B, first part, on the machine** (see the module docstring). -/
theorem smXB1_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb A : ℕ}
    (hR : SmRegs c d m k R n Sb A) (r21 : c.nreg 6521 = 1)
    (hrp : ∀ i < n, c.nmem (R + 3 + n + i) < n) (hhp : ∀ i < n, c.nmem (R + 3 + 2 * n + i) ≤ k)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (w : A + 22 * n + m + 4 * k + 20 ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec I W smXB1 c c' t ∧ t ≤ 196 * n + 21 * k + 120 ∧
      SmRegs c' d m k R n Sb A ∧ c'.nreg 6521 = 1 ∧
      c'.nreg 6533 = A + 4 * n + k + 2 + 3 * n ∧ c'.nreg 6534 = A + 4 * n + k + 2 + 4 * n ∧
      (∀ i < n, c'.nmem (A + 4 * n + k + 2 + 3 * n + i) = smKC c.nmem A R n i) ∧
      (∀ i < n, c'.nmem (A + 4 * n + k + 2 + 4 * n + i) = smHC c.nmem A R n k i) ∧
      c'.nreg 5540 = cnt (fun j => c.nmem (A + n + j)) n ∧
      (∀ i < n, 0 < c.nmem (A + n + i) →
        c'.nmem (A + 11 * n + 4 * k + 2 + i) = cnt (fun j => c.nmem (A + n + j)) i ∧
        c'.nmem (A + 12 * n + 4 * k + 2 + cnt (fun j => c.nmem (A + n + j)) i) = i) ∧
      c'.nreg 5541 = cnt (fun j => smCF c.nmem A R n k j) n ∧
      (∀ i < n, 0 < smCF c.nmem A R n k i →
        c'.nmem (A + 15 * n + 4 * k + 2 + cnt (fun j => smCF c.nmem A R n k j) i) = i) ∧
      (∀ a, a < A + 4 * n + k + 2 → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 3013 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hA := hR.hA
  obtain ⟨c₁, t₁, e₁, ht₁, b10, b11, b39, b40, b41, b42, b44, b31, b32, b33, b34, b35, b36, b47,
    b37, b43, b45, b46, n1, m1, rr1, rm1, o1'⟩ := smB0_exec (I := I) c hc hR
      (by clear * - w; omega)
  have q1 : ∀ x, (x < 6510 ∨ (6511 < x ∧ x < 6531 ∧ x ≠ 6539) ∨ 6547 < x) →
      c₁.nreg x = c.nreg x := n1
  -- the flags
  obtain ⟨c₂, t₂, e₂, ht₂, fKC, fHC, mm2, nn2, rr2, rm2, o2⟩ := smBF_exec (I := I) c₁ e₁.wb_right
    b10 b11 ((q1 6521 (by decide)).trans r21) b39 b40 b41 b42 b44 b31 b32 b33 b34 b35 b36 b47 b37
    b43 b45 b46 (by clear * - hA; omega) (by clear * - hA o1; omega) (by clear * - hA; omega)
    (by clear * - hA; omega) (by clear * - hA o1; omega) (by clear * - hA o1; omega)
    (by clear * - w; omega) (by clear * - w; omega)
    (fun i hi => by rw [m1]; exact hrp i hi) (fun i hi => by rw [m1]; exact hhp i hi)
  have q2 : ∀ x, (x < 6300 ∨ (6309 < x ∧ x < 6520) ∨ x = 6521 ∨ (6529 < x ∧ x ≠ 6548)) →
      c₂.nreg x = c₁.nreg x := nn2
  have M2 : ∀ a, a < A + 4 * n + k + 2 → c₂.nmem a = c.nmem a := fun a ha => by
    rw [mm2 a (Or.inl ha), m1]
  have hR2 : SmRegs c₂ d m k R n Sb A := hR.congr fun x hx => by
    rw [q2 x (by clear * - hx; unfold smReg at hx; omega), q1 x (by clear * - hx; unfold smReg at hx; omega)]
  rw [m1] at fKC fHC
  -- the compaction of `LP`
  obtain ⟨c₃, t₃, e₃, ht₃, v40, k3, mm3, nn3, rr3, rm3, o3⟩ := smLk_exec (I := I) c₂ e₂.wb_right
    (rn := 5504) (rF := 5507) (rCI := 5509) (rIX := 5528) (rout := 5540) (by decide) (by decide)
    (by decide) (by decide) (by decide) hR2.r04 hR2.r07 hR2.r09 hR2.r28 (by clear * - hA; omega)
    (by clear * - hA; omega) (by clear * - hA w; omega) (by clear * - w; omega)
  have q3 : ∀ x, x ≠ 5540 → (x < 6300 ∨ 6309 < x) → c₃.nreg x = c₂.nreg x := nn3
  have hR3 : SmRegs c₃ d m k R n Sb A := hR2.congr fun x hx =>
    q3 x (by clear * - hx; unfold smReg at hx; omega) (by clear * - hx; unfold smReg at hx; omega)
  have M3 : ∀ a, a < A + 11 * n + 4 * k + 2 → c₃.nmem a = c₂.nmem a := fun a ha =>
    mm3 a (by clear * - ha; omega)
  have LP2 : ∀ j, j < n → c₂.nmem (A + n + j) = c.nmem (A + n + j) := fun j hj =>
    M2 _ (by clear * - hj hA; omega)
  -- the map `CF`
  have r34 : c₃.nreg 6534 = A + 4 * n + k + 2 + 4 * n := by
    rw [q3 6534 (by decide) (by decide), q2 6534 (by decide)]; exact b34
  have r21' : c₃.nreg 6521 = 1 := by
    rw [q3 6521 (by decide) (by decide), q2 6521 (by decide), q1 6521 (by decide)]; exact r21
  obtain ⟨c₄, t₄, e₄, ht₄, cf4, mm4, nn4, rr4, rm4, o4⟩ := smB2_exec (I := I) c₃ e₃.wb_right
    hR3.r04 r21' hR3.r07 r34 hR3.r12 hR3.r10 (by clear * - hA; omega) (by clear * - hA; omega)
    (by clear * - hA o1; omega) (by clear * - hA w; omega) (by clear * - hW; omega)
    (fun i hi => by
      rw [M3 _ (by clear * - hi hA o1; omega), M2 _ (by clear * - hi hA o1; omega)]
      exact hrp i hi)
  have q4 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₄.nreg x = c₃.nreg x := nn4
  have hR4 : SmRegs c₄ d m k R n Sb A := hR3.congr fun x hx =>
    q4 x (by clear * - hx; unfold smReg at hx; unfold vscr; omega)
      (by clear * - hx; unfold smReg at hx; omega) (by clear * - hx; unfold smReg at hx; omega)
  -- the values of `CF`
  have CF : ∀ i < n, c₄.nmem (A + 13 * n + 4 * k + 2 + i) = smCF c.nmem A R n k i := fun i hi => by
    have hr := hrp i hi
    have e1 : c₃.nmem (A + n + i) = c.nmem (A + n + i) :=
      (M3 _ (by clear * - hi; omega)).trans (M2 _ (by clear * - hi; omega))
    have e2 : c₃.nmem (A + 4 * n + k + 2 + 4 * n + i) = smHC c.nmem A R n k i :=
      (M3 _ (by clear * - hi; omega)).trans (fHC i hi)
    have e3 : c₃.nmem (R + 3 + n + i) = c.nmem (R + 3 + n + i) :=
      (M3 _ (by clear * - hi hA o1; omega)).trans (M2 _ (by clear * - hi hA o1; omega))
    have e4 : c₃.nmem (A + 4 * n + k + 2 + 4 * n + c.nmem (R + 3 + n + i)) =
        smHC c.nmem A R n k (c.nmem (R + 3 + n + i)) :=
      (M3 _ (by clear * - hr; omega)).trans (fHC _ hr)
    rw [cf4 i hi, e1, e2, e3, e4]
    rfl
  -- the compaction of `CF`
  obtain ⟨c₅, t₅, e₅, ht₅, v41, k5, mm5, nn5, rr5, rm5, o5⟩ := smLk_exec (I := I) c₄ e₄.wb_right
    (rn := 5504) (rF := 5510) (rCI := 5530) (rIX := 5531) (rout := 5541) (by decide) (by decide)
    (by decide) (by decide) (by decide) hR4.r04 hR4.r10 hR4.r30 hR4.r31 (by clear * - hA; omega)
    (by clear * - hA; omega) (by clear * - hA w; omega) (by clear * - w; omega)
  have q5 : ∀ x, x ≠ 5541 → (x < 6300 ∨ 6309 < x) → c₅.nreg x = c₄.nreg x := nn5
  have hcfe : (fun j => c₄.nmem (A + 13 * n + 4 * k + 2 + j)) = fun j =>
      if j < n then smCF c.nmem A R n k j else c₄.nmem (A + 13 * n + 4 * k + 2 + j) := by
    funext j; split_ifs with hj
    · exact CF j hj
    · rfl
  have cntCF : ∀ i ≤ n, cnt (fun j => c₄.nmem (A + 13 * n + 4 * k + 2 + j)) i =
      cnt (fun j => smCF c.nmem A R n k j) i := fun i hi =>
    cnt_congr fun j hj => CF j (by clear * - hi hj; omega)
  have cntLP : ∀ i ≤ n, cnt (fun j => c₂.nmem (A + n + j)) i =
      cnt (fun j => c.nmem (A + n + j)) i := fun i hi =>
    cnt_congr fun j hj => LP2 j (by clear * - hi hj; omega)
  have ht : t₁ + (t₂ + (t₃ + (t₄ + t₅))) ≤ 196 * n + 21 * k + 120 := by
    clear * - ht₁ ht₂ ht₃ ht₄ ht₅; omega
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ht,
    hR4.congr fun x hx => q5 x (by clear * - hx; unfold smReg at hx; omega)
      (by clear * - hx; unfold smReg at hx; omega), ?_, ?_, ?_, fun i hi => ?_, fun i hi => ?_,
    ?_, fun i hi hf => ?_, ?_, fun i hi hf => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [rr5, rr4, rr3, rr2, rr1], by rw [rm5, rm4, rm3, rm2, rm1],
    by rw [o5, o4, o3, o2, o1']⟩
  · rw [q5 6521 (by decide) (by decide), q4 6521 (by unfold vscr; decide) (by decide)
      (by decide)]; exact r21'
  · rw [q5 6533 (by decide) (by decide), q4 6533 (by unfold vscr; decide) (by decide)
      (by decide), q3 6533 (by decide) (by decide), q2 6533 (by decide)]; exact b33
  · rw [q5 6534 (by decide) (by decide), q4 6534 (by unfold vscr; decide) (by decide)
      (by decide)]; exact r34
  · rw [mm5 _ (by clear * - hi hA; omega), mm4 _ (by clear * - hi hA; omega),
      M3 _ (by clear * - hi hA; omega)]; exact fKC i hi
  · rw [mm5 _ (by clear * - hi hA; omega), mm4 _ (by clear * - hi hA; omega),
      M3 _ (by clear * - hi hA; omega)]; exact fHC i hi
  · rw [q5 5540 (by decide) (by decide), q4 5540 (by unfold vscr; decide) (by decide)
      (by decide), v40, cntLP n le_rfl]
  · have hf2 : 0 < c₂.nmem (A + n + i) := by rw [LP2 i hi]; exact hf
    obtain ⟨k1, k2⟩ := k3 i hi hf2
    rw [cntLP i (by clear * - hi; omega)] at k1 k2
    refine ⟨?_, ?_⟩
    · rw [mm5 _ (by clear * - hi hA; omega), mm4 _ (by clear * - hi hA; omega)]; exact k1
    · have := cnt_le (fun j => c.nmem (A + n + j)) i
      rw [mm5 _ (by clear * - this hi hA; omega), mm4 _ (by clear * - this hi hA; omega)]
      exact k2
  · rw [v41, cntCF n le_rfl]
  · have hf4 : 0 < c₄.nmem (A + 13 * n + 4 * k + 2 + i) := by rw [CF i hi]; exact hf
    obtain ⟨-, k2⟩ := k5 i hi hf4
    rw [cntCF i (by clear * - hi; omega)] at k2
    exact k2
  · rw [mm5 _ (by clear * - ha; omega), mm4 _ (by clear * - ha hA; omega),
      M3 _ (by clear * - ha; omega), M2 a ha]
  · rw [q5 x (by clear * - hx; omega) (by clear * - hx; omega),
      q4 x (by clear * - hx; unfold vscr; omega) (by clear * - hx; omega) (by clear * - hx; omega),
      q3 x (by clear * - hx; omega) (by clear * - hx; omega), q2 x (by clear * - hx; omega),
      q1 x (by clear * - hx; omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
