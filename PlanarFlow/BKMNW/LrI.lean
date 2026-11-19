module

public import PlanarFlow.BKMNW.LrH

/-!
# The children's records of the large split: the set-up

* `lrIniR` (the bases: `Y = A + 16 n + 4 k + 2` (`= r5511`), `Xb = Y + 8 n`, `R + 3 + 5 n`,
  `Y + n`, `Y + 2 n`, `Y + 3 n`, `Y + 6 n`), `lrCp a b cc` (a copy `cpArr` of `r a` words from
  `r b` to `r cc`), **`lrIni = lrIniR ; CV → A + 3 n ; HM → A + 4 n ; lrSG ; RP → Y + n ;
  PF → Y + 2 n`**, **`lrIni_exec`** (`50 n + 7 k + 60` steps).
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

/-- The bases of the records' set-up. -/
def lrIniR : Stmt := block [.copyN 8506 5511, .constN 8518 8, .mulN 8519 8518 5504,
  .addN 8507 8506 8519, .addN 8513 5515 5504, .addN 8514 8506 5504, .addN 8515 8514 5504,
  .addN 8516 8515 5504, .constN 8518 3, .mulN 8519 8518 5504, .addN 8517 8516 8519]

/-- A copy of `r a` words from `r b` to `r cc`. -/
def lrCp (a b cc : ℕ) : Stmt := .seq (block [.copyN 4910 a, .copyN 4911 b, .copyN 4912 cc]) cpArr

/-- **The set-up of the records.** -/
def lrIni : Stmt := .seq lrIniR (.seq (lrCp 5504 8501 5522) (.seq (lrCp 5502 8502 5523)
  (.seq lrSG (.seq (lrCp 5504 5512 8514) (lrCp 5504 8503 8515)))))

section Exec

variable {I : Input} {W : ℕ}

theorem lrIniR_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb A : ℕ}
    (hR : SmRegs c d m k R n Sb A) (w : A + 16 * n + 4 * k + 2 + 8 * n ≤ W) (hW : 21 ≤ W)
    (w2 : R + 3 + 5 * n ≤ W) :
    ∃ c' t, Exec I W lrIniR c c' t ∧ t = 11 ∧ c'.nreg 8506 = A + 16 * n + 4 * k + 2 ∧
      c'.nreg 8507 = A + 16 * n + 4 * k + 2 + 8 * n ∧ c'.nreg 8513 = R + 3 + 4 * n + n ∧
      c'.nreg 8514 = A + 16 * n + 4 * k + 2 + n ∧
      c'.nreg 8515 = A + 16 * n + 4 * k + 2 + n + n ∧
      c'.nreg 8516 = A + 16 * n + 4 * k + 2 + n + n + n ∧
      c'.nreg 8517 = A + 16 * n + 4 * k + 2 + n + n + n + 3 * n ∧
      (∀ x, (x < 8506 ∨ 8519 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have r11 := hR.r11; have r04 := hR.r04; have r15 := hR.r15
  have := hc.1 5515
  unfold lrIniR
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r11, r04, r15]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r11, r04, r15])
    try omega

theorem lrCp_exec (c : Config) (hc : WordsBounded W c) {a b cc len Sb' Db : ℕ}
    (ha : a < 4910 ∨ 4916 < a) (hb : 4916 < b ∨ b < 4910) (hcc : cc < 4910 ∨ 4916 < cc)
    (r0 : c.nreg a = len) (r1 : c.nreg b = Sb') (r2 : c.nreg cc = Db)
    (lay : (Sb' + len ≤ Db ∨ Db + len ≤ Sb') ∧ Sb' + len ≤ W ∧ Db + len ≤ W ∧ len + 1 ≤ W) :
    ∃ c' t, Exec I W (lrCp a b cc) c c' t ∧ t ≤ 7 * len + 7 ∧
      (∀ i < len, c'.nmem (Db + i) = c.nmem (Sb' + i)) ∧
      (∀ a, (a < Db ∨ Db + len ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ 4916 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, n1, m1, rr1, rm1, o1⟩ : ∃ c₁ t₁,
      Exec I W (block [.copyN 4910 a, .copyN 4911 b, .copyN 4912 cc]) c c₁ t₁ ∧ t₁ = 3 ∧
      c₁.nreg 4910 = len ∧ c₁.nreg 4911 = Sb' ∧ c₁.nreg 4912 = Db ∧
      (∀ x, (x < 4910 ∨ 4912 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have := hc.1 a; have := hc.1 b; have := hc.1 cc
    exec_block
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r0, r1, r2]; omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r0, r1, r2])
      try omega
  obtain ⟨c₂, t₂, e₂, ht₂, v2, m2, n2, rr2, rm2, o2⟩ := cpArr_exec (P := I) c₁ e₁.wb_right
    a0 a1 a2 lay
  rw [m1] at v2 m2
  refine ⟨c₂, _, .seq e₁ e₂, by clear * - ht₁ ht₂; omega, v2, m2, fun x hx => ?_,
    by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
  rw [n2 x (by clear * - hx; omega), n1 x (by clear * - hx; omega)]

set_option maxHeartbeats 4000000 in
/-- **The set-up of the records** (see the module docstring). -/
theorem lrIni_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb A CVb HMb PFb CCb : ℕ}
    (hR : SmRegs c d m k R n Sb A) (r21 : c.nreg 6521 = 1)
    (r01 : c.nreg 8501 = CVb) (r02 : c.nreg 8502 = HMb) (r03 : c.nreg 8503 = PFb)
    (r04 : c.nreg 8504 = CCb)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (oV : A + 24 * n + 4 * k + 2 ≤ CVb)
    (oH : A + 24 * n + 4 * k + 2 ≤ HMb) (oP : A + 24 * n + 4 * k + 2 ≤ PFb)
    (oC : A + 24 * n + 4 * k + 2 ≤ CCb)
    (wV : CVb + n ≤ W) (wH : HMb + k ≤ W) (wP : PFb + n ≤ W) (wC : CCb + n ≤ W)
    (w : A + 24 * n + 4 * k + 2 ≤ W) (hW : 21 ≤ W)
    (hcc : ∀ i < n, c.nmem (CCb + i) ≤ 1) :
    ∃ c' t, Exec I W lrIni c c' t ∧ t ≤ 50 * n + 7 * k + 60 ∧
      SmRegs c' d m k R n Sb A ∧ c'.nreg 6521 = 1 ∧
      c'.nreg 8506 = A + 16 * n + 4 * k + 2 ∧ c'.nreg 8507 = A + 16 * n + 4 * k + 2 + 8 * n ∧
      c'.nreg 8513 = R + 3 + 5 * n ∧ c'.nreg 8516 = A + 16 * n + 4 * k + 2 + 3 * n ∧
      c'.nreg 8517 = A + 16 * n + 4 * k + 2 + 6 * n ∧
      (∀ i < n, c'.nmem (A + 3 * n + i) = c.nmem (CVb + i)) ∧
      (∀ j < k, c'.nmem (A + 4 * n + j) = c.nmem (HMb + j)) ∧
      (∀ i < n, c'.nmem (A + 16 * n + 4 * k + 2 + i) =
        if c.nmem (CCb + i) = 0 then i else c.nmem (R + 3 + 5 * n + i)) ∧
      (∀ i < n, c'.nmem (A + 16 * n + 4 * k + 2 + n + i) = c.nmem (R + 3 + n + i)) ∧
      (∀ i < n, c'.nmem (A + 16 * n + 4 * k + 2 + 2 * n + i) = c.nmem (PFb + i)) ∧
      (∀ a, ¬ (A + 3 * n ≤ a ∧ a < A + 4 * n + k) →
        ¬ (A + 16 * n + 4 * k + 2 ≤ a ∧ a < A + 16 * n + 4 * k + 2 + 3 * n) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ (4916 < x ∧ x < 6520) ∨ (6529 < x ∧ x < 8506) ∨ 8519 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hA := hR.hA
  set Y := A + 16 * n + 4 * k + 2 with hY
  obtain ⟨c₁, t₁, e₁, ht₁, b06, b07, b13, b14, b15, b16, b17, n1, m1, rr1, rm1, o1'⟩ :=
    lrIniR_exec (I := I) c hc hR (by omega) hW (by omega)
  have q1 : ∀ x, (x < 8506 ∨ 8519 < x) → c₁.nreg x = c.nreg x := n1
  have hR1 : SmRegs c₁ d m k R n Sb A := hR.congr fun x hx =>
    q1 x (by clear * - hx; unfold smReg at hx; omega)
  -- CV
  obtain ⟨c₂, t₂, e₂, ht₂, v2, m2, n2, rr2, rm2, o2⟩ := lrCp_exec (I := I) c₁ e₁.wb_right
    (a := 5504) (b := 8501) (cc := 5522) (len := n) (Sb' := CVb) (Db := A + 3 * n) (by decide) (by decide) (by decide) hR1.r04
    ((q1 _ (by decide)).trans r01) hR1.r22
    ⟨Or.inr (by omega), wV, by omega, by omega⟩
  have q2 : ∀ x, (x < 4910 ∨ 4916 < x) → c₂.nreg x = c₁.nreg x := n2
  have hR2 : SmRegs c₂ d m k R n Sb A := hR1.congr fun x hx =>
    q2 x (by clear * - hx; unfold smReg at hx; omega)
  -- HM
  obtain ⟨c₃, t₃, e₃, ht₃, v3, m3, n3, rr3, rm3, o3⟩ := lrCp_exec (I := I) c₂ e₂.wb_right
    (a := 5502) (b := 8502) (cc := 5523) (len := k) (Sb' := HMb) (Db := A + 4 * n) (by decide) (by decide) (by decide) hR2.r02
    ((q2 _ (by decide)).trans ((q1 _ (by decide)).trans r02)) hR2.r23
    ⟨Or.inr (by omega), wH, by omega, by omega⟩
  have q3 : ∀ x, (x < 4910 ∨ 4916 < x) → c₃.nreg x = c₂.nreg x := n3
  have hR3 : SmRegs c₃ d m k R n Sb A := hR2.congr fun x hx =>
    q3 x (by clear * - hx; unfold smReg at hx; omega)
  have M3 : ∀ a, (a < A + 3 * n ∨ A + 4 * n + k ≤ a) → c₃.nmem a = c₁.nmem a := fun a ha => by
    rw [m3 a (by clear * - ha; omega), m2 a (by clear * - ha; omega)]
  -- SG
  have Q31 : ∀ x, (x < 4910 ∨ 4916 < x) → x < 8506 ∨ 8519 < x → c₃.nreg x = c.nreg x :=
    fun x h1 h2 => by rw [q3 x h1, q2 x h1, q1 x h2]
  obtain ⟨c₄, t₄, e₄, ht₄, v4, m4, n4, rr4, rm4, o4⟩ := lrSG_exec (I := I) c₃ e₃.wb_right (CCb := CCb) (SPb := R + 3 + 4 * n + n) (Ob := Y)
    hR3.r04 ((Q31 _ (by decide) (by decide)).trans r21) ((Q31 _ (by decide) (by decide)).trans r04)
    (by rw [q3 _ (by decide), q2 _ (by decide)]; exact b13)
    (by rw [q3 _ (by decide), q2 _ (by decide)]; exact b06)
    (Or.inr (by omega)) (Or.inl (by omega)) (by omega) wC (by omega) (by omega)
    (fun i hi => by rw [M3 _ (Or.inr (by omega)), m1]; exact hcc i hi)
  have q4 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₄.nreg x = c₃.nreg x := n4
  have hR4 : SmRegs c₄ d m k R n Sb A := hR3.congr fun x hx =>
    q4 x (by clear * - hx; unfold smReg at hx; unfold vscr; omega)
      (by clear * - hx; unfold smReg at hx; omega) (by clear * - hx; unfold smReg at hx; omega)
  have Q4 : ∀ x, (8000 ≤ x ∧ x < 8520) → c₄.nreg x = c₁.nreg x := fun x hx => by
    rw [q4 x (by unfold vscr; omega) (by omega) (by omega), q3 x (by omega), q2 x (by omega)]
  -- RP
  obtain ⟨c₅, t₅, e₅, ht₅, v5, m5, n5, rr5, rm5, o5⟩ := lrCp_exec (I := I) c₄ e₄.wb_right
    (a := 5504) (b := 5512) (cc := 8514) (len := n) (Sb' := R + 3 + n)
    (Db := A + 16 * n + 4 * k + 2 + n) (by decide) (by decide) (by decide) hR4.r04
    hR4.r12 ((Q4 _ (by decide)).trans b14)
    ⟨Or.inl (by omega), by omega, by omega, by omega⟩
  have q5 : ∀ x, (x < 4910 ∨ 4916 < x) → c₅.nreg x = c₄.nreg x := n5
  have hR5 : SmRegs c₅ d m k R n Sb A := hR4.congr fun x hx =>
    q5 x (by clear * - hx; unfold smReg at hx; omega)
  -- PF
  obtain ⟨c₆, t₆, e₆, ht₆, v6, m6, n6, rr6, rm6, o6⟩ := lrCp_exec (I := I) c₅ e₅.wb_right
    (a := 5504) (b := 8503) (cc := 8515) (len := n) (Sb' := PFb)
    (Db := A + 16 * n + 4 * k + 2 + n + n) (by decide) (by decide) (by decide) hR5.r04
    (by rw [q5 _ (by decide), Q4 _ (by decide), q1 _ (by decide)]; exact r03)
    (by rw [q5 _ (by decide), Q4 _ (by decide)]; exact b15)
    ⟨Or.inr (by omega), wP, by omega, by omega⟩
  have q6 : ∀ x, (x < 4910 ∨ 4916 < x) → c₆.nreg x = c₅.nreg x := n6
  have hR6 : SmRegs c₆ d m k R n Sb A := hR5.congr fun x hx =>
    q6 x (by clear * - hx; unfold smReg at hx; omega)
  have Q6 : ∀ x, (8000 ≤ x ∧ x < 8520) → c₆.nreg x = c₁.nreg x := fun x hx => by
    rw [q6 x (by omega), q5 x (by omega), Q4 x hx]
  have ht : t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))) ≤ 50 * n + 7 * k + 60 := by
    clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆; omega
  have MY : ∀ a, (a < Y ∨ Y + 3 * n ≤ a) → c₆.nmem a = c₃.nmem a := fun a ha => by
    rw [m6 a (by clear * - ha; omega), m5 a (by clear * - ha; omega),
      m4 a (by clear * - ha; omega)]
  refine ⟨c₆, _, by
      unfold lrIni; exact .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ht, hR6, ?_,
    (Q6 _ (by decide)).trans b06, (Q6 _ (by decide)).trans b07,
    by rw [Q6 _ (by decide), b13]; ring, by rw [Q6 _ (by decide), b16]; ring,
    by rw [Q6 _ (by decide), b17]; ring,
    fun i hi => ?_, fun j hj => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun a h1 h2 => ?_, fun x hx => ?_,
    by rw [rr6, rr5, rr4, rr3, rr2, rr1], by rw [rm6, rm5, rm4, rm3, rm2, rm1],
    by rw [o6, o5, o4, o3, o2, o1']⟩
  · rw [q6 _ (by decide), q5 _ (by decide),
      q4 _ (by unfold vscr; decide) (by decide) (by decide), Q31 _ (by decide) (by decide)]
    exact r21
  · rw [MY _ (Or.inl (by omega)), m3 _ (by omega), v2 i hi, m1]
  · rw [MY _ (Or.inl (by omega)), v3 j hj, m2 _ (by omega), m1]
  · rw [m6 _ (by omega), m5 _ (by omega), v4 i hi, M3 _ (Or.inr (by omega)),
      M3 _ (Or.inl (by omega)), m1, show R + 3 + 4 * n + n + i = R + 3 + 5 * n + i by ring]
  · have := v5 i hi
    rw [m6 _ (by omega), show A + 16 * n + 4 * k + 2 + n + i = Y + n + i by rfl, this,
      m4 _ (by omega), M3 _ (Or.inl (by omega)), m1]
  · have := v6 i hi
    rw [show A + 16 * n + 4 * k + 2 + 2 * n + i = Y + n + n + i by ring, this,
      m5 _ (by omega), m4 _ (by omega), M3 _ (Or.inr (by omega)), m1]
  · rw [MY a (by clear * - h2; omega), M3 a (by clear * - h1; omega), m1]
  · have h1 : x < 8506 ∨ 8519 < x := by omega
    rw [q6 x (by omega), q5 x (by omega)]
    rcases hx with hx | hx | hx | hx
    · rw [q4 x (by unfold vscr; omega) (by omega) (by omega), Q31 x (by omega) h1]
    · rw [q4 x (by unfold vscr; omega) (by omega) (by omega), Q31 x (by omega) h1]
    · rw [q4 x (by unfold vscr; omega) (by omega) (by omega), Q31 x (by omega) h1]
    · rw [q4 x (by unfold vscr; omega) (by omega) (by omega), Q31 x (by omega) h1]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
