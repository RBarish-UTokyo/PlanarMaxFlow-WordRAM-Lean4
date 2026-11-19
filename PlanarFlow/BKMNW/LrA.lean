module

public import PlanarFlow.BKMNW.SmXB4
public import PlanarFlow.BKMNW.LrRot

/-!
# The children's records of the large split: the set-up and the children's data, with frames

Copies of `smXA0_exec` and `smXB1_exec` with stronger frames (needed to run them inside the large
separator program, whose other data live in registers `≥ 8000` and above the scratch of stage B):

* **`smXA0_exec'`**: as `smXA0_exec`, registers `< 3013` **and `≥ 8000`** kept;
* **`smXB1_exec'`**: as `smXB1_exec`, plus the memory from `A + 16 n + 4 k + 2` on kept, the map
  `CF = smCF` at `A + 13 n + 4 k + 2`, and the registers `≥ 8000` kept.
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

set_option maxHeartbeats 2000000 in
theorem smXA0_exec' (c : Config) (hc : WordsBounded W c) {d m k R n Sb : ℕ}
    (r4 : c.nreg 3004 = d) (r50 : c.nreg 6500 = Sb) (hm : c.nmem d = m)
    (hk : c.nmem (d + 1) = k) (hR : c.nmem (d + 7 * m + 4) = R) (hn : c.nmem R = n)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (o2 : d + 7 * m + 4 < R)
    (w : Sb + 22 * m + 22 * n + 8 * k + 20 ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec I W smXA0 c c' t ∧ t ≤ 6 * n + 70 ∧
      SmRegs c' d m k R n Sb (Sb + 21 * m + 4 * k + 2) ∧ c'.nreg 6521 = 1 ∧
      c'.nreg 5300 = n ∧ c'.nreg 5301 = Sb + 21 * m + 4 * k + 2 ∧ c'.nreg 5302 = R + 3 + n ∧
      c'.nreg 5303 = R + 3 + 2 * n ∧ c'.nreg 5304 = R + 3 + 3 * n ∧
      c'.nreg 5305 = R + 3 + 4 * n ∧ c'.nreg 5306 = Sb + 21 * m + 4 * k + 2 + n ∧
      c'.nreg 5307 = k ∧
      (∀ i < n, c'.nmem (Sb + 21 * m + 4 * k + 2 + i) = 1) ∧
      (∀ a, (a < Sb + 21 * m + 4 * k + 2 ∨ Sb + 21 * m + 4 * k + 2 + n ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 3013 ∨ 8000 ≤ x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a01, a02, a03, a04, a05, n1, m1, rr1, rm1, o1'⟩ :=
    smA0_exec (I := I) c hc r4 r50 hm hk hR hn (by omega) hW
  obtain ⟨c₂, t₂, e₂, ht₂, a06, a07, a21, a22, a23, a08, a09, a28, a10, a30, a31, a11, n2, m2, rr2,
    rm2, o2'⟩ := smA1_exec (I := I) c₁ e₁.wb_right a01 a02 a04 a05 (by omega) hW
  have q21 : ∀ x, (5500 ≤ x ∧ x ≤ 5505) → c₂.nreg x = c₁.nreg x := fun x hx =>
    n2 x (by clear * - hx; omega)
  obtain ⟨c₃, t₃, e₃, ht₃, a17, a12, a13, a14, a15, a16, a24, a25, a26, a27, s0, s1, s2, s3, s4,
    s5, s6, s7, o21, n3, m3, rr3, rm3, o3'⟩ := smA2_exec (I := I) c₂ e₂.wb_right
    ((q21 5501 (by decide)).trans a01) ((q21 5502 (by decide)).trans a02)
    ((q21 5503 (by decide)).trans a03) ((q21 5504 (by decide)).trans a04)
    ((q21 5505 (by decide)).trans a05) a06 a07 (by omega) (by omega) hW
  have E1 : ∀ x, 5500 ≤ x → x ≤ 5505 → c₃.nreg x = c₁.nreg x := fun x h1 h2 => by
    rw [n3 x (by clear * - h1 h2; omega), n2 x (by clear * - h1 h2; omega)]
  have E2 : ∀ x, ((5506 ≤ x ∧ x ≤ 5511) ∨ (5521 ≤ x ∧ x ≤ 5523) ∨ x = 5528 ∨ x = 5530 ∨
      x = 5531) → c₃.nreg x = c₂.nreg x := fun x hx => n3 x (by clear * - hx; omega)
  have hR3 : SmRegs c₃ d m k R n Sb (Sb + 21 * m + 4 * k + 2) :=
    ⟨rfl, (E1 5500 (by decide) (by decide)).trans a00, (E1 5501 (by decide) (by decide)).trans a01,
      (E1 5502 (by decide) (by decide)).trans a02, (E1 5503 (by decide) (by decide)).trans a03,
      (E1 5504 (by decide) (by decide)).trans a04, (E1 5505 (by decide) (by decide)).trans a05,
      (E2 5506 (by decide)).trans a06, (E2 5507 (by decide)).trans a07,
      (E2 5521 (by decide)).trans a21, (E2 5522 (by decide)).trans a22,
      (E2 5523 (by decide)).trans a23, (E2 5508 (by decide)).trans a08,
      (E2 5509 (by decide)).trans a09, (E2 5528 (by decide)).trans a28,
      (E2 5510 (by decide)).trans a10, (E2 5530 (by decide)).trans a30,
      (E2 5531 (by decide)).trans a31, (E2 5511 (by decide)).trans a11,
      a17, a12, a13, a14, a15, a16, a24, a25, a26, a27⟩
  -- the ones
  clear E1 E2
  have wf : Sb + 21 * m + 4 * k + 2 + n + 1 ≤ W := by clear * - w; omega
  obtain ⟨c₄, t₄, e₄, ht₄, f4, mm4, nn4, rr4, rm4, o4⟩ := smFill_exec (I := I) c₃ e₃.wb_right
    hR3.r04 hR3.r06 o21 wf
  have q43 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₄.nreg x = c₃.nreg x := nn4
  have Q : ∀ x, (5299 < x ∧ x < 5308) → c₄.nreg x = c₃.nreg x := fun x hx =>
    q43 x (by clear * - hx; unfold vscr; omega) (by clear * - hx; omega) (by clear * - hx; omega)
  have hR4 : SmRegs c₄ d m k R n Sb (Sb + 21 * m + 4 * k + 2) :=
    hR3.congr fun x hx => q43 x (by clear * - hx; unfold vscr; unfold smReg at hx; omega)
      (by clear * - hx; unfold smReg at hx; omega) (by clear * - hx; unfold smReg at hx; omega)
  have ht : t₁ + (t₂ + (t₃ + t₄)) ≤ 6 * n + 70 := by
    clear * - ht₁ ht₂ ht₃ ht₄; omega
  refine ⟨c₄, _, by unfold smXA0; exact .seq e₁ (.seq e₂ (.seq e₃ e₄)), ht, hR4,
    (q43 6521 (by unfold vscr; decide) (by decide) (by decide)).trans o21,
    (Q 5300 (by decide)).trans s0, (Q 5301 (by decide)).trans s1,
    (Q 5302 (by decide)).trans s2, (Q 5303 (by decide)).trans s3,
    (Q 5304 (by decide)).trans s4, (Q 5305 (by decide)).trans s5,
    (Q 5306 (by decide)).trans s6, (Q 5307 (by decide)).trans s7, f4,
    fun a ha => by rw [mm4 a (by clear * - ha; omega), m3, m2, m1], fun x hx => ?_,
    by rw [rr4, rr3, rr2, rr1], by rw [rm4, rm3, rm2, rm1], by rw [o4, o3', o2', o1']⟩
  rw [q43 x (by clear * - hx; unfold vscr; omega) (by clear * - hx; omega)
    (by clear * - hx; omega), n3 x (by clear * - hx; omega), n2 x (by clear * - hx; omega),
    n1 x (by clear * - hx; omega)]

set_option maxHeartbeats 4000000 in
theorem smXB1_exec' (c : Config) (hc : WordsBounded W c) {d m k R n Sb A : ℕ}
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
      (∀ a, A + 16 * n + 4 * k + 2 ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ i < n, c'.nmem (A + 13 * n + 4 * k + 2 + i) = smCF c.nmem A R n k i) ∧
      (∀ x, (x < 3013 ∨ 8000 ≤ x) → c'.nreg x = c.nreg x) ∧
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
    ?_, fun i hi hf => ?_, ?_, fun i hi hf => ?_, fun a ha => ?_, fun a ha => ?_, fun i hi => ?_,
    fun x hx => ?_,
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
  · rw [mm5 _ (by clear * - ha; omega), mm4 _ (by clear * - ha; omega),
      mm3 _ (by clear * - ha; omega), mm2 _ (Or.inr (by clear * - ha; omega)), m1]
  · rw [mm5 _ (by clear * - hi; omega)]; exact CF i hi
  · rw [q5 x (by clear * - hx; omega) (by clear * - hx; omega),
      q4 x (by clear * - hx; unfold vscr; omega) (by clear * - hx; omega) (by clear * - hx; omega),
      q3 x (by clear * - hx; omega) (by clear * - hx; omega), q2 x (by clear * - hx; omega),
      q1 x (by clear * - hx; omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
