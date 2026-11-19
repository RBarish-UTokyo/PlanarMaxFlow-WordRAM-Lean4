module

public import PlanarFlow.BKMNW.SmXB3

/-!
# The small separator program, stage B (second part) composed

**`smXB2_exec`**: `smB4b ; smB6 ; smB5 ; smB4a` from the state after `smXB1`: the children's
records from `Xb = A + 16 n + 4 k + 2` in terms of the arrays at the start (the record, `KC`, `HC`,
`CI`, `IX`, `IX2`); the memory below `Xb` kept; within `60 n + 90` steps.
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
/-- **Stage B, second part, on the machine** (see the module docstring). -/
theorem smXB2_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb A nl ml : ℕ}
    (hR : SmRegs c d m k R n Sb A) (r40 : c.nreg 5540 = nl) (r41 : c.nreg 5541 = ml)
    (r33 : c.nreg 6533 = A + 4 * n + k + 2 + 3 * n) (r34 : c.nreg 6534 = A + 4 * n + k + 2 + 4 * n)
    (hnl : nl ≤ n) (hml : ml ≤ n)
    (hix : ∀ j < nl, c.nmem (A + 12 * n + 4 * k + 2 + j) < n)
    (hix2 : ∀ j < ml, c.nmem (A + 15 * n + 4 * k + 2 + j) < n)
    (hrp : ∀ i < n, 0 < c.nmem (A + n + i) → c.nmem (R + 3 + n + i) < n)
    (hCI : ∀ i < n, 0 < c.nmem (A + n + i) → c.nmem (A + 11 * n + 4 * k + 2 + i) < nl)
    (hinj : ∀ i < n, ∀ j < n, 0 < c.nmem (A + n + i) → 0 < c.nmem (A + n + j) →
      c.nmem (A + 11 * n + 4 * k + 2 + i) = c.nmem (A + 11 * n + 4 * k + 2 + j) → i = j)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (w : A + 23 * n + m + 4 * k + 20 ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec I W smXB2 c c' t ∧ t ≤ 60 * n + 90 ∧
      c'.nreg 6501 = A + 16 * n + 4 * k + 2 ∧
      c'.nmem (A + 16 * n + 4 * k + 2) = 6 * nl + ml + 3 ∧
      c'.nmem (A + 16 * n + 4 * k + 2 + 1) = 3 ∧
      c'.nmem (A + 16 * n + 4 * k + 2 + 2) = nl ∧
      c'.nmem (A + 16 * n + 4 * k + 2 + 2 + 1) = 1 ∧
      c'.nmem (A + 16 * n + 4 * k + 2 + 2 + 2) = 0 ∧
      c'.nmem (A + 16 * n + 4 * k + 2 + 2 + (6 * nl + ml + 3)) = 0 ∧
      c'.nmem (A + 16 * n + 4 * k + 2 + 2 + (6 * nl + ml + 3) + 1) = 2 ∧
      c'.nmem (A + 16 * n + 4 * k + 2 + 2 + (6 * nl + ml + 3) + 2) = 0 ∧
      (∀ j < nl, c'.nmem (A + 16 * n + 4 * k + 2 + 2 + 3 + j) =
        c.nmem (R + 3 + c.nmem (A + 12 * n + 4 * k + 2 + j))) ∧
      (∀ i < n, 0 < c.nmem (A + n + i) →
        c'.nmem (A + 16 * n + 4 * k + 2 + 2 + 3 + nl + c.nmem (A + 11 * n + 4 * k + 2 + i)) =
          c.nmem (A + 11 * n + 4 * k + 2 + c.nmem (R + 3 + n + i))) ∧
      (∀ j < nl, c'.nmem (A + 16 * n + 4 * k + 2 + 2 + 3 + 2 * nl + j) =
        c.nmem (A + 4 * n + k + 2 + 4 * n + c.nmem (A + 12 * n + 4 * k + 2 + j))) ∧
      (∀ j < nl, c'.nmem (A + 16 * n + 4 * k + 2 + 2 + 3 + 3 * nl + j) =
        c.nmem (A + 4 * n + k + 2 + 3 * n + c.nmem (A + 12 * n + 4 * k + 2 + j))) ∧
      (∀ j < nl, c'.nmem (A + 16 * n + 4 * k + 2 + 2 + 3 + 4 * nl + j) =
        c.nmem (R + 3 + 4 * n + c.nmem (A + 12 * n + 4 * k + 2 + j))) ∧
      (∀ j < ml, c'.nmem (A + 16 * n + 4 * k + 2 + 2 + 3 + 6 * nl + j) =
        c.nmem (A + 11 * n + 4 * k + 2 + c.nmem (A + 15 * n + 4 * k + 2 + j))) ∧
      (∀ a, a < A + 16 * n + 4 * k + 2 → c'.nmem a = c.nmem a) ∧
      (∀ x, x < 3013 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hA := hR.hA
  -- the bases
  obtain ⟨c₁, t₁, e₁, ht₁, a42, a54, a55, a56, a57, a58, a60, n1, m1, rr1, rm1, o1'⟩ :=
    smB4b_exec (I := I) c hc hR.r11 r40 (by clear * - hnl w; omega)
  have q1 : ∀ x, (x < 5519 ∨ (5519 < x ∧ x < 5542) ∨ (5542 < x ∧ x < 5554) ∨ 5560 < x) →
      c₁.nreg x = c.nreg x := n1
  -- the reverse indices
  obtain ⟨c₂, t₂, e₂, ht₂, rp2, mm2, nn2, rr2, rm2, o2⟩ := smB6_exec (I := I) c₁ e₁.wb_right
    ((q1 5504 (by decide)).trans hR.r04) ((q1 5507 (by decide)).trans hR.r07)
    ((q1 5509 (by decide)).trans hR.r09) ((q1 5512 (by decide)).trans hR.r12) a55
    (by clear * - hA; omega) (by clear * - hA; omega) (by clear * - hA o1; omega)
    (by clear * - hA hnl w; omega) hW
    (fun i hi hf => by rw [m1] at hf ⊢; exact hrp i hi hf)
    (fun i hi hf => by rw [m1] at hf ⊢; have := hCI i hi hf; clear * - this hnl; omega)
    (fun i hi j hj hfi hfj e => by rw [m1] at hfi hfj e; exact hinj i hi j hj hfi hfj e)
  rw [m1] at rp2 mm2
  have q2 : ∀ x, (x < 6310 ∨ 6319 < x) → c₂.nreg x = c₁.nreg x := nn2
  have L2 : ∀ a, a < A + 16 * n + 4 * k + 2 + 2 + 3 + nl → c₂.nmem a = c.nmem a := fun a ha =>
    mm2 a (by clear * - ha; omega)
  -- the gathers
  obtain ⟨c₃, t₃, e₃, ht₃, g1, g2, g3, g4, g5, mm3, nn3, rr3, rm3, o3⟩ := smB5_exec (I := I) c₂
    e₂.wb_right (n := n) (Rp := A + 16 * n + 4 * k + 2 + 2)
    ((q2 5540 (by decide)).trans ((q1 5540 (by decide)).trans r40))
    ((q2 5541 (by decide)).trans ((q1 5541 (by decide)).trans r41))
    ((q2 5528 (by decide)).trans ((q1 5528 (by decide)).trans hR.r28))
    ((q2 5531 (by decide)).trans ((q1 5531 (by decide)).trans hR.r31))
    ((q2 5517 (by decide)).trans ((q1 5517 (by decide)).trans hR.r17))
    ((q2 6534 (by decide)).trans ((q1 6534 (by decide)).trans r34))
    ((q2 6533 (by decide)).trans ((q1 6533 (by decide)).trans r33))
    ((q2 5515 (by decide)).trans ((q1 5515 (by decide)).trans hR.r15))
    ((q2 5509 (by decide)).trans ((q1 5509 (by decide)).trans hR.r09))
    ((q2 5554 (by decide)).trans a54) ((q2 5556 (by decide)).trans a56)
    ((q2 5557 (by decide)).trans a57) ((q2 5558 (by decide)).trans a58)
    ((q2 5560 (by decide)).trans a60)
    (fun j hj => by rw [L2 (A + 12 * n + 4 * k + 2 + j) (by clear * - hj hnl; omega)]; exact hix j hj)
    (fun j hj => by rw [L2 (A + 15 * n + 4 * k + 2 + j) (by clear * - hj hml; omega)]; exact hix2 j hj)
    (by clear * - hA o1; omega) (by clear * - hA; omega) (by clear * - hA; omega)
    (by clear * - hA o1; omega) (by clear * - hA; omega) (by clear * - hA hnl; omega)
    (by clear * - hA hml; omega) (by clear * - hA hnl hml w; omega)
  have q3 : ∀ x, (x < 6210 ∨ 6217 < x) → c₃.nreg x = c₂.nreg x := nn3
  -- the headers
  obtain ⟨c₄, t₄, e₄, ht₄, h01, h0, h1, h2, h3, h4, h5, h6, h7, mm4, nn4, rr4, rm4, o4⟩ :=
    smB4a_exec (I := I) c₃ e₃.wb_right
    ((q3 5511 (by decide)).trans ((q2 5511 (by decide)).trans ((q1 5511 (by decide)).trans
      hR.r11)))
    ((q3 5540 (by decide)).trans ((q2 5540 (by decide)).trans ((q1 5540 (by decide)).trans r40)))
    ((q3 5541 (by decide)).trans ((q2 5541 (by decide)).trans ((q1 5541 (by decide)).trans r41)))
    ((q3 5542 (by decide)).trans ((q2 5542 (by decide)).trans a42))
    (by clear * - hA hnl hml w; omega)
  have K4 : ∀ a, (A + 16 * n + 4 * k + 2 + 4 < a ∧
      a < A + 16 * n + 4 * k + 2 + 2 + (6 * nl + ml + 3)) → c₄.nmem a = c₃.nmem a := fun a ha =>
    mm4 a (Or.inr (Or.inl ha))
  have L3 : ∀ a, a < A + 16 * n + 4 * k + 2 + 2 + 3 → c₃.nmem a = c₂.nmem a := fun a ha =>
    mm3 a (Or.inl ha)
  have ht : t₁ + (t₂ + (t₃ + t₄)) ≤ 60 * n + 90 := by
    clear * - ht₁ ht₂ ht₃ ht₄ hnl hml; omega
  refine ⟨c₄, _, by unfold smXB2; exact .seq e₁ (.seq e₂ (.seq e₃ e₄)), ht, h01, h0, h1, h2, h3,
    h4, h5, h6, h7, fun j hj => ?_, fun i hi hf => ?_, fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_, fun a ha => ?_, fun x hx => ?_, by rw [rr4, rr3, rr2, rr1],
    by rw [rm4, rm3, rm2, rm1], by rw [o4, o3, o2, o1']⟩
  · have hx := hix j hj
    rw [K4 _ (by clear * - hj hnl; omega), g1 j hj, L2 (A + 12 * n + 4 * k + 2 + j) (by clear * - hj hnl; omega),
      L2 _ (by clear * - hx hA o1; omega)]
  · have hci := hCI i hi hf
    have hci' : c.nmem (A + 11 * n + 4 * k + 2 + i) < nl := hci
    rw [K4 _ (by clear * - hci'; omega), mm3 _ (Or.inr (Or.inl (by clear * - hci'; omega))),
      rp2 i hi hf]
  · have hx := hix j hj
    rw [K4 _ (by clear * - hj hnl; omega), g2 j hj, L2 (A + 12 * n + 4 * k + 2 + j) (by clear * - hj hnl; omega),
      L2 _ (by clear * - hx hA; omega)]
  · have hx := hix j hj
    rw [K4 _ (by clear * - hj hnl; omega), g3 j hj, L2 (A + 12 * n + 4 * k + 2 + j) (by clear * - hj hnl; omega),
      L2 _ (by clear * - hx hA; omega)]
  · have hx := hix j hj
    rw [K4 _ (by clear * - hj hnl; omega), g4 j hj, L2 (A + 12 * n + 4 * k + 2 + j) (by clear * - hj hnl; omega),
      L2 _ (by clear * - hx hA o1; omega)]
  · have hx := hix2 j hj
    rw [K4 _ (by clear * - hj hml; omega), g5 j hj, L2 (A + 15 * n + 4 * k + 2 + j) (by clear * - hj hml; omega),
      L2 _ (by clear * - hx hA; omega)]
  · rw [mm4 a (Or.inl ha), L3 a (by clear * - ha; omega), L2 a (by clear * - ha; omega)]
  · rw [nn4 x (by clear * - hx; omega), q3 x (by clear * - hx; omega), q2 x (by clear * - hx; omega),
      q1 x (by clear * - hx; omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
