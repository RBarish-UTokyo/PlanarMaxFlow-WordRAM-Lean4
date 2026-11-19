module

public import PlanarFlow.BKMNW.SmXB2

/-!
# The small separator program, stage B (second part): the children's records

After `smXB1` (`nl` in `5540`, `ml` in `5541`, the compactions at `B2`, `B3`), from
`Xb = A + 16 n + 4 k + 2` (`R' = Xb + 2`, `zl = 3 + 6 nl + ml`, `R'' = R' + zl`):

* `smB4b` (the bases `R' + 3 + j nl`), `smB6` (`lrProg`: the left child's `RP'` in its own
  indices), `smB5` (five gathers: `GP' = GP ∘ IX`, `HP' = HC ∘ IX`, `KP' = KC ∘ IX`,
  `VP' = VP ∘ IX`, `FX' = CI ∘ IX2`), `smB4a` (the sizes `zl`, `3` at `Xb`, `Xb + 1`, the headers
  `nl | 1 | 0` at `R'` and `0 | 2 | 0` at `R''`, `r6501 := Xb`);
* **`smXB2 = smB4b ; smB6 ; smB5 ; smB4a`**, the exec lemmas.
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

/-- The bases of the left child's record. -/
def smB4b : Stmt := block [.constN 5519 2, .addN 5542 5511 5519, .constN 5519 3,
  .addN 5554 5542 5519, .addN 5555 5554 5540, .addN 5556 5555 5540, .addN 5557 5556 5540,
  .addN 5558 5557 5540, .addN 5559 5558 5540, .addN 5560 5559 5540]

/-- The left child's reverse indices (`lrProg`). -/
def smB6 : Stmt := .seq (block [.copyN 6310 5504, .copyN 6311 5507, .copyN 6312 5509,
  .copyN 6313 5512, .copyN 6314 5555]) lrProg

/-- The five gathers of the left child's record. -/
def smB5 : Stmt := .seq (ggProg 5540 5528 5517 5554) (.seq (ggProg 5540 5528 6534 5556)
  (.seq (ggProg 5540 5528 6533 5557) (.seq (ggProg 5540 5528 5515 5558)
    (ggProg 5541 5531 5509 5560))))

/-- The sizes and the headers of the children's records. -/
def smB4a : Stmt := block [.constN 5519 6, .mulN 5543 5519 5540, .addN 5543 5543 5541,
  .constN 5519 3, .addN 5543 5543 5519, .storeN 5511 5543, .constN 5519 1, .addN 5544 5511 5519,
  .constN 5545 3, .storeN 5544 5545, .storeN 5542 5540, .addN 5546 5542 5519, .constN 5547 1,
  .storeN 5546 5547, .constN 5519 2, .addN 5548 5542 5519, .constN 5549 0, .storeN 5548 5549,
  .addN 5550 5542 5543, .storeN 5550 5549, .constN 5519 1, .addN 5551 5550 5519,
  .constN 5552 2, .storeN 5551 5552, .constN 5519 2, .addN 5553 5550 5519, .storeN 5553 5549,
  .copyN 6501 5511]

/-- **Stage B, second part.** -/
def smXB2 : Stmt := .seq smB4b (.seq smB6 (.seq smB5 smB4a))

section Exec

variable {I : Input} {W : ℕ}

theorem smB4b_exec (c : Config) (hc : WordsBounded W c) {Xb nl : ℕ}
    (r11 : c.nreg 5511 = Xb) (r40 : c.nreg 5540 = nl) (w : Xb + 5 + 6 * nl ≤ W) :
    ∃ c' t, Exec I W smB4b c c' t ∧ t = 10 ∧ c'.nreg 5542 = Xb + 2 ∧
      c'.nreg 5554 = Xb + 2 + 3 ∧ c'.nreg 5555 = Xb + 2 + 3 + nl ∧
      c'.nreg 5556 = Xb + 2 + 3 + 2 * nl ∧ c'.nreg 5557 = Xb + 2 + 3 + 3 * nl ∧
      c'.nreg 5558 = Xb + 2 + 3 + 4 * nl ∧ c'.nreg 5560 = Xb + 2 + 3 + 6 * nl ∧
      (∀ x, (x < 5519 ∨ (5519 < x ∧ x < 5542) ∨ (5542 < x ∧ x < 5554) ∨ 5560 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smB4b
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r11, r40]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r11, r40])
    try omega

theorem smB6r_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec I W (block [.copyN 6310 5504, .copyN 6311 5507, .copyN 6312 5509,
      .copyN 6313 5512, .copyN 6314 5555]) c c' t ∧ t = 5 ∧ c'.nreg 6310 = c.nreg 5504 ∧
      c'.nreg 6311 = c.nreg 5507 ∧ c'.nreg 6312 = c.nreg 5509 ∧ c'.nreg 6313 = c.nreg 5512 ∧
      c'.nreg 6314 = c.nreg 5555 ∧ (∀ x, (x < 6310 ∨ 6314 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 5504; have := hc.1 5507; have := hc.1 5509; have := hc.1 5512; have := hc.1 5555
  exec_block
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same])
    try omega

/-- **The left child's reverse indices on the machine** (`lrProg` over the parent's record:
`OUT[CI[i]] = CI[RP[i]]` for the flagged `i`). -/
theorem smB6_exec (c : Config) (hc : WordsBounded W c) {n LPb CIb RPb OUTb : ℕ}
    (r04 : c.nreg 5504 = n) (r07 : c.nreg 5507 = LPb) (r09 : c.nreg 5509 = CIb)
    (r12 : c.nreg 5512 = RPb) (r55 : c.nreg 5555 = OUTb)
    (l1 : LPb + n ≤ OUTb) (l2 : CIb + n ≤ OUTb) (l3 : RPb + n ≤ OUTb) (l4 : OUTb + n ≤ W)
    (hW : 21 ≤ W) (hrp : ∀ i < n, 0 < c.nmem (LPb + i) → c.nmem (RPb + i) < n)
    (hCI : ∀ i < n, 0 < c.nmem (LPb + i) → c.nmem (CIb + i) < n)
    (hinj : ∀ i < n, ∀ j < n, 0 < c.nmem (LPb + i) → 0 < c.nmem (LPb + j) →
      c.nmem (CIb + i) = c.nmem (CIb + j) → i = j) :
    ∃ c' t, Exec I W smB6 c c' t ∧ t ≤ 14 * n + 10 ∧
      (∀ i < n, 0 < c.nmem (LPb + i) →
        c'.nmem (OUTb + c.nmem (CIb + i)) = c.nmem (CIb + c.nmem (RPb + i))) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6310 ∨ 6319 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, a3, a4, n1, m1, rr1, rm1, o1⟩ := smB6r_exec (I := I) c hc
  rw [r04] at a0; rw [r07] at a1; rw [r09] at a2; rw [r12] at a3; rw [r55] at a4
  obtain ⟨c₂, t₂, e₂, ht₂, g2, mm2, nn2, rr2, rm2, o2⟩ := lrProg_exec (P := I) c₁ e₁.wb_right
    a0 a1 a2 a3 a4 l1 l2 l3 l4 (by clear * - l1 l4 hW; omega)
    (fun i hi hf => by rw [m1] at hf ⊢; exact hrp i hi hf)
    (fun i hi hf => by rw [m1] at hf ⊢; exact hCI i hi hf)
    (fun i hi j hj hfi hfj e => by rw [m1] at hfi hfj e; exact hinj i hi j hj hfi hfj e)
  rw [m1] at g2 mm2
  refine ⟨c₂, _, .seq e₁ e₂, by clear * - ht₁ ht₂; omega, g2, mm2, fun x hx => ?_,
    by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
  rw [nn2 x (by clear * - hx; omega), n1 x (by clear * - hx; omega)]

set_option maxHeartbeats 2000000 in
/-- **The five gathers of the left child's record on the machine.** -/
theorem smB5_exec (c : Config) (hc : WordsBounded W c) {n nl ml IXb IX2b GPb HCb KCb VPb CIb Rp : ℕ}
    (r40 : c.nreg 5540 = nl) (r41 : c.nreg 5541 = ml) (r28 : c.nreg 5528 = IXb)
    (r31 : c.nreg 5531 = IX2b) (r17 : c.nreg 5517 = GPb) (r34 : c.nreg 6534 = HCb)
    (r33 : c.nreg 6533 = KCb) (r15 : c.nreg 5515 = VPb) (r09 : c.nreg 5509 = CIb)
    (r54 : c.nreg 5554 = Rp + 3) (r56 : c.nreg 5556 = Rp + 3 + 2 * nl)
    (r57 : c.nreg 5557 = Rp + 3 + 3 * nl) (r58 : c.nreg 5558 = Rp + 3 + 4 * nl)
    (r60 : c.nreg 5560 = Rp + 3 + 6 * nl)
    (hix : ∀ j < nl, c.nmem (IXb + j) < n) (hix2 : ∀ j < ml, c.nmem (IX2b + j) < n)
    (s1 : GPb + n ≤ Rp + 3) (s2 : HCb + n ≤ Rp + 3) (s3 : KCb + n ≤ Rp + 3) (s4 : VPb + n ≤ Rp + 3)
    (s5 : CIb + n ≤ Rp + 3) (s6 : IXb + nl ≤ Rp + 3) (s7 : IX2b + ml ≤ Rp + 3)
    (w : Rp + 3 + 6 * nl + ml + 1 ≤ W) :
    ∃ c' t, Exec I W smB5 c c' t ∧ t ≤ 36 * nl + 9 * ml + 40 ∧
      (∀ j < nl, c'.nmem (Rp + 3 + j) = c.nmem (GPb + c.nmem (IXb + j))) ∧
      (∀ j < nl, c'.nmem (Rp + 3 + 2 * nl + j) = c.nmem (HCb + c.nmem (IXb + j))) ∧
      (∀ j < nl, c'.nmem (Rp + 3 + 3 * nl + j) = c.nmem (KCb + c.nmem (IXb + j))) ∧
      (∀ j < nl, c'.nmem (Rp + 3 + 4 * nl + j) = c.nmem (VPb + c.nmem (IXb + j))) ∧
      (∀ j < ml, c'.nmem (Rp + 3 + 6 * nl + j) = c.nmem (CIb + c.nmem (IX2b + j))) ∧
      (∀ a, (a < Rp + 3 ∨ (Rp + 3 + nl ≤ a ∧ a < Rp + 3 + 2 * nl) ∨
        (Rp + 3 + 5 * nl ≤ a ∧ a < Rp + 3 + 6 * nl) ∨ Rp + 3 + 6 * nl + ml ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6210 ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hIX : ∀ j < nl, c.nmem (IXb + j) < n := hix
  -- gather 1
  obtain ⟨c₁, t₁, e₁, ht₁, g1, mm1, nn1, rr1, rm1, o1⟩ := ggProg_exec (P := I) c hc
    (a := 5540) (b := 5528) (cc := 5517) (dd := 5554) (by decide) (by decide) (by decide)
    (by decide) r40 r28 r17 r54 (by clear * - s6 w; omega) (by clear * - w; omega)
    (by clear * - w; omega) (fun j hj => by have := hIX j hj; clear * - this s1 w; omega)
    (fun j hj => by clear * - hj s6; omega)
    (fun j hj => by have := hIX j hj; clear * - this s1; omega)
  have q1 : ∀ x, (x < 6210 ∨ 6217 < x) → c₁.nreg x = c.nreg x := nn1
  have M1 : ∀ a, (a < Rp + 3 ∨ Rp + 3 + nl ≤ a) → c₁.nmem a = c.nmem a := fun a ha =>
    mm1 a (by clear * - ha; omega)
  have X1 : ∀ j < nl, c₁.nmem (IXb + j) = c.nmem (IXb + j) := fun j hj =>
    M1 _ (Or.inl (by clear * - hj s6; omega))
  -- gather 2
  obtain ⟨c₂, t₂, e₂, ht₂, g2, mm2, nn2, rr2, rm2, o2⟩ := ggProg_exec (P := I) c₁ e₁.wb_right
    (a := 5540) (b := 5528) (cc := 6534) (dd := 5556) (by decide) (by decide) (by decide)
    (by decide) ((q1 5540 (by decide)).trans r40) ((q1 5528 (by decide)).trans r28)
    ((q1 6534 (by decide)).trans r34) ((q1 5556 (by decide)).trans r56)
    (by clear * - s6 w; omega) (by clear * - w; omega) (by clear * - w; omega)
    (fun j hj => by rw [X1 j hj]; have := hIX j hj; clear * - this s2 w; omega)
    (fun j hj => by clear * - hj s6; omega)
    (fun j hj => by rw [X1 j hj]; have := hIX j hj; clear * - this s2; omega)
  have q2 : ∀ x, (x < 6210 ∨ 6217 < x) → c₂.nreg x = c₁.nreg x := nn2
  have M2 : ∀ a, (a < Rp + 3 + 2 * nl ∨ Rp + 3 + 3 * nl ≤ a) → c₂.nmem a = c₁.nmem a :=
    fun a ha => mm2 a (by clear * - ha; omega)
  have X2 : ∀ j < nl, c₂.nmem (IXb + j) = c.nmem (IXb + j) := fun j hj =>
    (M2 _ (Or.inl (by clear * - hj s6; omega))).trans (X1 j hj)
  -- gather 3
  obtain ⟨c₃, t₃, e₃, ht₃, g3, mm3, nn3, rr3, rm3, o3⟩ := ggProg_exec (P := I) c₂ e₂.wb_right
    (a := 5540) (b := 5528) (cc := 6533) (dd := 5557) (by decide) (by decide) (by decide)
    (by decide) ((q2 5540 (by decide)).trans ((q1 5540 (by decide)).trans r40))
    ((q2 5528 (by decide)).trans ((q1 5528 (by decide)).trans r28))
    ((q2 6533 (by decide)).trans ((q1 6533 (by decide)).trans r33))
    ((q2 5557 (by decide)).trans ((q1 5557 (by decide)).trans r57))
    (by clear * - s6 w; omega) (by clear * - w; omega) (by clear * - w; omega)
    (fun j hj => by rw [X2 j hj]; have := hIX j hj; clear * - this s3 w; omega)
    (fun j hj => by clear * - hj s6; omega)
    (fun j hj => by rw [X2 j hj]; have := hIX j hj; clear * - this s3; omega)
  have q3 : ∀ x, (x < 6210 ∨ 6217 < x) → c₃.nreg x = c₂.nreg x := nn3
  have M3 : ∀ a, (a < Rp + 3 + 3 * nl ∨ Rp + 3 + 4 * nl ≤ a) → c₃.nmem a = c₂.nmem a :=
    fun a ha => mm3 a (by clear * - ha; omega)
  have X3 : ∀ j < nl, c₃.nmem (IXb + j) = c.nmem (IXb + j) := fun j hj =>
    (M3 _ (Or.inl (by clear * - hj s6; omega))).trans (X2 j hj)
  -- gather 4
  obtain ⟨c₄, t₄, e₄, ht₄, g4, mm4, nn4, rr4, rm4, o4⟩ := ggProg_exec (P := I) c₃ e₃.wb_right
    (a := 5540) (b := 5528) (cc := 5515) (dd := 5558) (by decide) (by decide) (by decide)
    (by decide)
    ((q3 5540 (by decide)).trans ((q2 5540 (by decide)).trans ((q1 5540 (by decide)).trans r40)))
    ((q3 5528 (by decide)).trans ((q2 5528 (by decide)).trans ((q1 5528 (by decide)).trans r28)))
    ((q3 5515 (by decide)).trans ((q2 5515 (by decide)).trans ((q1 5515 (by decide)).trans r15)))
    ((q3 5558 (by decide)).trans ((q2 5558 (by decide)).trans ((q1 5558 (by decide)).trans r58)))
    (by clear * - s6 w; omega) (by clear * - w; omega) (by clear * - w; omega)
    (fun j hj => by rw [X3 j hj]; have := hIX j hj; clear * - this s4 w; omega)
    (fun j hj => by clear * - hj s6; omega)
    (fun j hj => by rw [X3 j hj]; have := hIX j hj; clear * - this s4; omega)
  have q4 : ∀ x, (x < 6210 ∨ 6217 < x) → c₄.nreg x = c₃.nreg x := nn4
  have M4 : ∀ a, (a < Rp + 3 + 4 * nl ∨ Rp + 3 + 5 * nl ≤ a) → c₄.nmem a = c₃.nmem a :=
    fun a ha => mm4 a (by clear * - ha; omega)
  -- the memory below `Rp + 3` is that of the start
  have L4 : ∀ a, a < Rp + 3 → c₄.nmem a = c.nmem a := fun a ha => by
    rw [M4 a (Or.inl (by clear * - ha; omega)), M3 a (Or.inl (by clear * - ha; omega)),
      M2 a (Or.inl (by clear * - ha; omega)), M1 a (Or.inl ha)]
  have Y4 : ∀ j < ml, c₄.nmem (IX2b + j) = c.nmem (IX2b + j) := fun j hj =>
    L4 _ (by clear * - hj s7; omega)
  -- gather 5
  obtain ⟨c₅, t₅, e₅, ht₅, g5, mm5, nn5, rr5, rm5, o5⟩ := ggProg_exec (P := I) c₄ e₄.wb_right
    (a := 5541) (b := 5531) (cc := 5509) (dd := 5560) (by decide) (by decide) (by decide)
    (by decide)
    ((q4 5541 (by decide)).trans ((q3 5541 (by decide)).trans ((q2 5541 (by decide)).trans
      ((q1 5541 (by decide)).trans r41))))
    ((q4 5531 (by decide)).trans ((q3 5531 (by decide)).trans ((q2 5531 (by decide)).trans
      ((q1 5531 (by decide)).trans r31))))
    ((q4 5509 (by decide)).trans ((q3 5509 (by decide)).trans ((q2 5509 (by decide)).trans
      ((q1 5509 (by decide)).trans r09))))
    ((q4 5560 (by decide)).trans ((q3 5560 (by decide)).trans ((q2 5560 (by decide)).trans
      ((q1 5560 (by decide)).trans r60))))
    (by clear * - s7 w; omega) (by clear * - w; omega) (by clear * - w; omega)
    (fun j hj => by rw [Y4 j hj]; have := hix2 j hj; clear * - this s5 w; omega)
    (fun j hj => by clear * - hj s7; omega)
    (fun j hj => by rw [Y4 j hj]; have := hix2 j hj; clear * - this s5; omega)
  have M5 : ∀ a, (a < Rp + 3 + 6 * nl ∨ Rp + 3 + 6 * nl + ml ≤ a) → c₅.nmem a = c₄.nmem a :=
    fun a ha => mm5 a (by clear * - ha; omega)
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
    by clear * - ht₁ ht₂ ht₃ ht₄ ht₅; omega, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
    fun j hj => ?_, fun j hj => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [rr5, rr4, rr3, rr2, rr1], by rw [rm5, rm4, rm3, rm2, rm1],
    by rw [o5, o4, o3, o2, o1]⟩
  · rw [M5 _ (Or.inl (by clear * - hj; omega)), M4 _ (Or.inl (by clear * - hj; omega)),
      M3 _ (Or.inl (by clear * - hj; omega)), M2 _ (Or.inl (by clear * - hj; omega)), g1 j hj]
  · have := hIX j hj
    rw [M5 _ (Or.inl (by clear * - hj; omega)), M4 _ (Or.inl (by clear * - hj; omega)),
      M3 _ (Or.inl (by clear * - hj; omega)), g2 j hj, X1 j hj, M1 _ (Or.inl (by clear * - this s2; omega))]
  · have := hIX j hj
    rw [M5 _ (Or.inl (by clear * - hj; omega)), M4 _ (Or.inl (by clear * - hj; omega)), g3 j hj,
      X2 j hj, M2 _ (Or.inl (by clear * - this s3; omega)), M1 _ (Or.inl (by clear * - this s3; omega))]
  · have := hIX j hj
    rw [M5 _ (Or.inl (by clear * - hj; omega)), g4 j hj, X3 j hj,
      M3 _ (Or.inl (by clear * - this s4; omega)), M2 _ (Or.inl (by clear * - this s4; omega)),
      M1 _ (Or.inl (by clear * - this s4; omega))]
  · have := hix2 j hj
    rw [g5 j hj, Y4 j hj, L4 _ (by clear * - this s5; omega)]
  · have e5 : c₅.nmem a = c₄.nmem a := M5 a (by clear * - ha; omega)
    have e4 : c₄.nmem a = c₃.nmem a := M4 a (by clear * - ha; omega)
    have e3 : c₃.nmem a = c₂.nmem a := M3 a (by clear * - ha; omega)
    have e2 : c₂.nmem a = c₁.nmem a := M2 a (by clear * - ha; omega)
    have e1 : c₁.nmem a = c.nmem a := M1 a (by clear * - ha; omega)
    rw [e5, e4, e3, e2, e1]
  · rw [nn5 x hx, q4 x hx, q3 x hx, q2 x hx, q1 x hx]

theorem smB4a_exec (c : Config) (hc : WordsBounded W c) {Xb nl ml : ℕ}
    (r11 : c.nreg 5511 = Xb) (r40 : c.nreg 5540 = nl) (r41 : c.nreg 5541 = ml)
    (r42 : c.nreg 5542 = Xb + 2) (w : Xb + 2 + (6 * nl + ml + 3) + 3 ≤ W) :
    ∃ c' t, Exec I W smB4a c c' t ∧ t = 28 ∧ c'.nreg 6501 = Xb ∧
      c'.nmem Xb = 6 * nl + ml + 3 ∧ c'.nmem (Xb + 1) = 3 ∧ c'.nmem (Xb + 2) = nl ∧
      c'.nmem (Xb + 2 + 1) = 1 ∧ c'.nmem (Xb + 2 + 2) = 0 ∧
      c'.nmem (Xb + 2 + (6 * nl + ml + 3)) = 0 ∧ c'.nmem (Xb + 2 + (6 * nl + ml + 3) + 1) = 2 ∧
      c'.nmem (Xb + 2 + (6 * nl + ml + 3) + 2) = 0 ∧
      (∀ a, a < Xb ∨ (Xb + 4 < a ∧ a < Xb + 2 + (6 * nl + ml + 3)) ∨
        Xb + 2 + (6 * nl + ml + 3) + 2 < a → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5519 ∨ (5519 < x ∧ x < 5543) ∨ (5553 < x ∧ x ≠ 6501)) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smB4a
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r11, r40, r41, r42]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r11, r40, r41, r42])
    try omega

end Exec

end MfDrv

end BKMNW

end PlanarFlow
