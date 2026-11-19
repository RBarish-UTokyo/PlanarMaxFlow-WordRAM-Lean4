module

public import PlanarFlow.BKMNW.LsB

/-!
# `sepL`: the three branches of `lsB`, composed

* `lsMil_exec`, `lsCut_exec`, **`lsBne_exec`** (the core's piece map nonempty), **`lsBe_exec`**
  (empty), **`lsB_exec`** (all cases): within `30 n + 120` steps the path's core indices `IX'` at
  `E`, its darts `PD'` at `E + n` and `n'` in `8557` as described in `LsB.lean`; memory outside
  `[E, E + 2 n)` kept.
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

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

section Exec

variable {I : Input} {W : ℕ}

/-- Miller's case: the darts copied from `Hb' + 6 #B` to `E + n`. -/
theorem lsMil_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb nB : ℕ}
    (hR : LsR c m k R n Sb) (r58 : c.nreg 8558 = nB) (r57 : c.nreg 8557 = nB)
    (r71 : c.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n) (hnB : nB ≤ n)
    (w : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 42 * n + 5 * k + 40 * nB +
      c.nreg 3109 + 3 * c.nreg 3108 + 47 + nB ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsMil c c' t ∧ t ≤ 7 * nB + 22 ∧
      (∀ j < nB, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + n + j) =
        c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 42 * n + 5 * k + 40 * nB +
          c.nreg 3109 + 3 * c.nreg 3108 + 47 + j)) ∧
      (∀ a, (a < Sb + 21 * m + 38 * n + 8 * k + 24 + n ∨
        Sb + 21 * m + 38 * n + 8 * k + 24 + n + nB ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ (4916 < x ∧ x < 8564) ∨ (8564 < x ∧ x < 8570) ∨ x = 8571 ∨ 8572 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, v70, n1, m1, rr1, rm1, o1⟩ := lsBm_exec (I := I) c hc hR r58
    (by omega) w2
  obtain ⟨c₂, t₂, e₂, ht₂, v2, m2, n2, rr2, rm2, o2⟩ := lrCp_exec (I := I) c₁ e₁.wb_right
    (a := 8557) (b := 8570) (cc := 8571) (len := nB)
    (Sb' := Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 42 * n + 5 * k + 40 * nB +
      c.nreg 3109 + 3 * c.nreg 3108 + 47)
    (Db := Sb + 21 * m + 38 * n + 8 * k + 24 + n) (by decide) (by decide) (by decide)
    (by rw [n1 _ (by omega)]; exact r57) v70 (by rw [n1 8571 (by omega)]; exact r71)
    ⟨Or.inr (by omega), w, by omega, by omega⟩
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, fun j hj => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
  · rw [v2 j hj, m1]
  · rw [m2 a ha, m1]
  · rw [n2 x (by omega), n1 x (by omega)]

/-- The cut case: `PD' = [r4902 + 1, 0, …, 0]` (`nB` cells). -/
theorem lsCut_exec (c : Config) (hc : WordsBounded W c) {a nB v : ℕ}
    (r57 : c.nreg 8557 = nB) (r71 : c.nreg 8571 = a) (r21 : c.nreg 6521 = 1)
    (r02 : c.nreg 4902 = v) (hnB : 0 < nB) (w : a + nB + 1 ≤ W) (wv : v + 1 ≤ W) :
    ∃ c' t, Exec I W lsCut c c' t ∧ t ≤ 6 * nB + 6 ∧ c'.nmem a = v + 1 ∧
      (∀ j, 0 < j → j < nB → c'.nmem (a + j) = 0) ∧
      (∀ x, ¬ (a ≤ x ∧ x < a + nB) → c'.nmem x = c.nmem x) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → x ≠ 8564 → x ≠ 8573 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, z1, m1, n1, rr1, rm1, o1⟩ := zfill_exec (P := I) c hc
    (bnd := 8557) (ob := 8571) (m := nB) (Ob := a) r57 r21 r71 (by omega) (by omega)
    (by unfold vscr; decide) (by unfold vscr; decide) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨c₂, t₂, e₂, ht₂, m2, n2, rr2, rm2, o2⟩ := lsBc_exec (I := I) c₁ e₁.wb_right
    (a := a) (v := v) (by rw [n1 _ (by unfold vscr; decide) (by decide) (by decide)]; exact r71)
    (by rw [n1 _ (by unfold vscr; decide) (by decide) (by decide)]; exact r02) wv (by omega)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, by rw [m2, upd_same], fun j h1 h2 => ?_,
    fun x hx => ?_, fun x h1 h2 h3 h4 h5 => ?_, by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
  · rw [m2, upd_other _ _ _ (by omega)]; exact z1 j h2
  · rw [m2, upd_other _ _ _ (by omega), m1 x hx]
  · rw [n2 x h4 h5, n1 x h1 h2 h3]

/-- **The nonempty case** (after `lsB0`). -/
theorem lsBne_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb nB : ℕ}
    (hR : LsR c m k R n Sb) (r58 : c.nreg 8558 = nB) (r03 : c.nreg 3103 = nB)
    (r71 : c.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n)
    (r69 : c.nreg 8569 = Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n)
    (r21 : c.nreg 6521 = 1) (hnB : 0 < nB) (hnBn : nB ≤ n)
    (wM : c.nreg 4900 = 0 → Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 42 * n + 5 * k +
      40 * nB + c.nreg 3109 + 3 * c.nreg 3108 + 47 + nB ≤ W)
    (wC : c.nreg 4900 ≠ 0 → c.nreg 4902 + 1 ≤ W)
    (w : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 3 * n ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsBne c c' t ∧ t ≤ 30 * n + 100 ∧ c'.nreg 8557 = nB ∧
      (∀ q < nB, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) =
        c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n + q)) ∧
      (c.nreg 4900 = 0 → ∀ j < nB, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + n + j) =
        c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 42 * n + 5 * k + 40 * nB +
          c.nreg 3109 + 3 * c.nreg 3108 + 47 + j)) ∧
      (c.nreg 4900 ≠ 0 → c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + n) = c.nreg 4902 + 1 ∧
        ∀ j, 0 < j → j < nB → c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + n + j) = 0) ∧
      (∀ a, (a < Sb + 21 * m + 38 * n + 8 * k + 24 ∨
        Sb + 21 * m + 38 * n + 8 * k + 24 + 2 * n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ (4916 < x ∧ x < 6520) ∨ (6529 < x ∧ x < 8557) ∨ (8557 < x ∧ x < 8564) ∨
        (8564 < x ∧ x < 8570) ∨ x = 8571 ∨ 8573 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lsBne
  obtain ⟨c₁, t₁, e₁, ht₁, v57, n1, m1, rr1, rm1, o1⟩ := lsBn1_exec (I := I) c hc
  rw [r03] at v57
  have q1 : ∀ x, x ≠ 8557 → c₁.nreg x = c.nreg x := n1
  obtain ⟨c₂, t₂, e₂, ht₂, v2, m2, n2, rr2, rm2, o2⟩ := lrCp_exec (I := I) c₁ e₁.wb_right
    (a := 8557) (b := 8569) (cc := 8555) (len := nB)
    (Sb' := Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n)
    (Db := Sb + 21 * m + 38 * n + 8 * k + 24) (by decide) (by decide) (by decide) v57
    (by rw [q1 _ (by decide)]; exact r69) (by rw [q1 _ (by decide)]; exact hR.r55)
    ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  have q2 : ∀ x, (x < 4910 ∨ 4916 < x) → x ≠ 8557 → c₂.nreg x = c.nreg x := fun x h1 h2 => by
    rw [n2 x h1, q1 x h2]
  have hR2 : LsR c₂ m k R n Sb := hR.congr fun x hx => q2 x (by omega) (by omega)
  have M2 : ∀ a, (a < Sb + 21 * m + 38 * n + 8 * k + 24 ∨
      Sb + 21 * m + 38 * n + 8 * k + 24 + nB ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m2 a ha, m1]
  have c57 : c₂.nreg 8557 = nB := by rw [n2 _ (by omega)]; exact v57
  by_cases h49 : c.nreg 4900 = 0
  · -- Miller's case
    have hf : ¬ c₂.nreg 8568 < c₂.nreg 4900 := by
      rw [hR2.r68, q2 _ (by omega) (by omega), h49]; omega
    obtain ⟨c₃, t₃, e₃, ht₃, v3, m3, n3, rr3, rm3, o3⟩ := lsMil_exec (I := I) c₂ e₂.wb_right hR2
      (by rw [q2 _ (by omega) (by omega)]; exact r58) c57
      (by rw [q2 _ (by omega) (by omega)]; exact r71) hnBn
      (by rw [q2 _ (by omega) (by omega), q2 _ (by omega) (by omega)]; exact wM h49) w2
    refine ⟨c₃, t₁ + (t₂ + (t₃ + 2)), .seq e₁ (.seq e₂ (.ifLtN_false hf e₃)), by omega,
      by rw [n3 _ (by omega)]; exact c57, fun q hq => ?_, fun _ j hj => ?_, fun h => absurd h49 h,
      fun a ha => ?_, fun x hx => ?_, by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1],
      by rw [o3, o2, o1]⟩
    · rw [m3 _ (Or.inl (by omega)), v2 q hq, m1]
    · rw [v3 j hj, q2 _ (by omega) (by omega), q2 _ (by omega) (by omega), M2 _ (Or.inr (by omega))]
    · rw [m3 a (by omega), M2 a (by omega)]
    · rw [n3 x (by omega), q2 x (by omega) (by omega)]
  · -- the cut case
    have ht : c₂.nreg 8568 < c₂.nreg 4900 := by
      rw [hR2.r68, q2 _ (by omega) (by omega)]; omega
    obtain ⟨c₃, t₃, e₃, ht₃, v3, z3, m3, n3, rr3, rm3, o3⟩ := lsCut_exec (I := I) c₂ e₂.wb_right
      (a := Sb + 21 * m + 38 * n + 8 * k + 24 + n) (v := c.nreg 4902) c57
      (by rw [q2 _ (by omega) (by omega)]; exact r71)
      (by rw [q2 _ (by omega) (by omega)]; exact r21)
      (q2 _ (by omega) (by omega)) hnB (by omega) (wC h49)
    refine ⟨c₃, t₁ + (t₂ + (t₃ + 1)), .seq e₁ (.seq e₂ (.ifLtN_true ht e₃)), by omega,
      by rw [n3 _ (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)]; exact c57,
      fun q hq => ?_, fun h => absurd h h49, fun _ => ⟨v3, z3⟩, fun a ha => ?_, fun x hx => ?_,
      by rw [rr3, rr2, rr1], by rw [rm3, rm2, rm1], by rw [o3, o2, o1]⟩
    · rw [m3 _ (by omega), v2 q hq, m1]
    · rw [m3 a (by omega), M2 a (by omega)]
    · rw [n3 x (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega),
        q2 x (by omega) (by omega)]

/-- **The empty case** (after `lsB0`). -/
theorem lsBe_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb : ℕ}
    (hR : LsR c m k R n Sb) (r71 : c.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n)
    (hfn : c.nmem (R + 3 + 6 * n) * (1 - (1 - m)) < n) (wR : R + 3 + 6 * n ≤ W)
    (w : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsBe c c' t ∧ t ≤ 40 ∧ c'.nreg 8557 = 1 ∧
      c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24) =
        lsIs (c.nmem (R + 3 + 6 * n))
          (c.nmem (R + 3 + 4 * n + c.nmem (R + 3 + 6 * n) * (1 - (1 - m))))
          (c.nmem (R + 3 + n + c.nmem (R + 3 + 6 * n) * (1 - (1 - m)))) m ∧
      c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + n) = 1 ∧
      (∀ a, a ≠ Sb + 21 * m + 38 * n + 8 * k + 24 → a ≠ Sb + 21 * m + 38 * n + 8 * k + 24 + n →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 8557 ∨ (8557 < x ∧ x < 8564) ∨ (8564 < x ∧ x < 8574) ∨ 8580 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lsBe
  obtain ⟨c₁, t₁, e₁, ht₁, a57, a76, a77, n1, m1, rr1, rm1, o1⟩ := lsBe1_exec (I := I) c hc hR rfl
    wR w2
  have hR1 : LsR c₁ m k R n Sb := hR.congr fun x hx => n1 x (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, a78, n2, m2, rr2, rm2, o2⟩ := lsBe2_exec (I := I) c₁ e₁.wb_right hR1
    a76 a77 (by omega) (by rw [m1]) (by omega) w2
  have hR2 : LsR c₂ m k R n Sb := hR1.congr fun x hx => n2 x (by omega)
  have hq : c.nmem (R + 3 + 4 * n + c.nmem (R + 3 + 6 * n) * (1 - (1 - m))) % 2 *
      (1 - (1 - m)) ≤ 1 := by
    have : c.nmem (R + 3 + 4 * n + c.nmem (R + 3 + 6 * n) * (1 - (1 - m))) % 2 < 2 :=
      Nat.mod_lt _ (by norm_num)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (show 1 - (1 - m) ≤ 1 by omega) with h | h <;>
      rw [h] <;> omega
  obtain ⟨c₃, t₃, e₃, ht₃, a74, n3, m3, rr3, rm3, o3⟩ := lsBe3_exec (I := I) c₂ e₂.wb_right hR2
    (i0 := c.nmem (R + 3 + 6 * n) * (1 - (1 - m)))
    (q := c.nmem (R + 3 + 4 * n + c.nmem (R + 3 + 6 * n) * (1 - (1 - m))) % 2 * (1 - (1 - m)))
    (p := c.nmem (R + 3 + n + c.nmem (R + 3 + 6 * n) * (1 - (1 - m))))
    (by rw [n2 _ (by omega)]; exact a76) a78 hq (by rw [m2, m1]) (by omega) (by omega) w2
  obtain ⟨c₄, t₄, e₄, ht₄, m4, n4, rr4, rm4, o4⟩ := lsBe4_exec (I := I) c₃ e₃.wb_right (a := Sb + 21 * m + 38 * n + 8 * k + 24)
    (b := Sb + 21 * m + 38 * n + 8 * k + 24 + n)
    (by rw [n3 _ (by omega), n2 _ (by omega), n1 _ (by omega)]; exact hR.r55)
    (by rw [n3 _ (by omega), n2 _ (by omega), n1 _ (by omega)]; exact r71) (by omega) (by omega) w2
  have hE : ∀ a, c₄.nmem a = upd (upd c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24) (c₃.nreg 8574))
      (Sb + 21 * m + 38 * n + 8 * k + 24 + n) 1 a := fun a => by rw [m4, m3, m2, m1]
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega,
    by rw [n4 _ (by omega), n3 _ (by omega), n2 _ (by omega)]; exact a57, ?_, ?_,
    fun a h1 h2 => ?_, fun x hx => ?_, by rw [rr4, rr3, rr2, rr1], by rw [rm4, rm3, rm2, rm1],
    by rw [o4, o3, o2, o1]⟩
  · rw [hE, upd_other _ _ _ (by omega), upd_same, a74]
    unfold lsIs; ring
  · rw [hE, upd_same]
  · rw [hE, upd_other _ _ _ h2, upd_other _ _ _ h1]
  · rw [n4 x (by omega), n3 x (by omega), n2 x (by omega), n1 x (by omega)]

/-- **The path after stage 5, all cases** (see `LsB.lean`). -/
theorem lsB_exec (c : Config) (hc : WordsBounded W c) {m k R n Sb nB : ℕ}
    (hR : LsR c m k R n Sb) (r03 : c.nreg 3103 = nB) (hnBn : nB ≤ n)
    (wM : 0 < nB → c.nreg 4900 = 0 → Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 42 * n +
      5 * k + 40 * nB + c.nreg 3109 + 3 * c.nreg 3108 + 47 + nB ≤ W)
    (wC : 0 < nB → c.nreg 4900 ≠ 0 → c.nreg 4902 + 1 ≤ W)
    (hfn : nB = 0 → c.nmem (R + 3 + 6 * n) * (1 - (1 - m)) < n) (wR : R + 3 + 6 * n ≤ W)
    (w : Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 3 * n ≤ W) (w2 : 50 ≤ W) :
    ∃ c' t, Exec I W lsB c c' t ∧ t ≤ 30 * n + 120 ∧ LsR c' m k R n Sb ∧
      c'.nreg 8558 = nB ∧ c'.nreg 8559 = c.nreg 3105 ∧ c'.nreg 8560 = c.nreg 3106 ∧
      c'.nreg 8561 = c.nreg 3107 ∧ c'.nreg 8571 = Sb + 21 * m + 38 * n + 8 * k + 24 + n ∧
      (0 < nB → c'.nreg 8557 = nB ∧ ∀ q < nB, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + q) =
        c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 2 * n + q)) ∧
      (0 < nB → c.nreg 4900 = 0 → ∀ j < nB, c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + n + j) =
        c.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + 4 * n + 3 + 42 * n + 5 * k + 40 * nB +
          c.nreg 3109 + 3 * c.nreg 3108 + 47 + j)) ∧
      (0 < nB → c.nreg 4900 ≠ 0 →
        c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + n) = c.nreg 4902 + 1 ∧
        ∀ j, 0 < j → j < nB → c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + n + j) = 0) ∧
      (nB = 0 → c'.nreg 8557 = 1 ∧
        c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24) =
          lsIs (c.nmem (R + 3 + 6 * n))
            (c.nmem (R + 3 + 4 * n + c.nmem (R + 3 + 6 * n) * (1 - (1 - m))))
            (c.nmem (R + 3 + n + c.nmem (R + 3 + 6 * n) * (1 - (1 - m)))) m ∧
        c'.nmem (Sb + 21 * m + 38 * n + 8 * k + 24 + n) = 1) ∧
      (∀ a, (a < Sb + 21 * m + 38 * n + 8 * k + 24 ∨
        Sb + 21 * m + 38 * n + 8 * k + 24 + 2 * n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ (4916 < x ∧ x < 6520) ∨ (6529 < x ∧ x < 8550)) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lsB
  obtain ⟨c₁, t₁, e₁, ht₁, hR1, v58, v59, v60, v61, v71, v69, v21, n1, m1, rr1, rm1, o1⟩ :=
    lsB0_exec (I := I) c hc hR (by omega) (by omega)
  rw [r03] at v58
  have q1 : ∀ x, (x < 6520 ∨ (6529 < x ∧ x < 8550)) → c₁.nreg x = c.nreg x := fun x hx =>
    n1 x (by omega)
  rcases Nat.eq_zero_or_pos nB with h0 | hpos
  · -- empty
    have hf : ¬ c₁.nreg 8568 < c₁.nreg 3103 := by rw [hR1.r68, q1 _ (by omega), r03, h0]; omega
    obtain ⟨c₂, t₂, e₂, ht₂, a57, aE, aEn, m2, n2, rr2, rm2, o2⟩ := lsBe_exec (I := I) c₁
      e₁.wb_right hR1 v71 (by rw [m1]; exact hfn h0) wR (by omega) w2
    have hR2 : LsR c₂ m k R n Sb := hR1.congr fun x hx => n2 x (by omega)
    refine ⟨c₂, t₁ + (t₂ + 2), .seq e₁ (.ifLtN_false hf e₂), by omega, hR2,
      by rw [n2 _ (by omega)]; exact v58, by rw [n2 _ (by omega)]; exact v59,
      by rw [n2 _ (by omega)]; exact v60, by rw [n2 _ (by omega)]; exact v61,
      by rw [n2 _ (by omega)]; exact v71, fun h => absurd h0 (by omega),
      fun h => absurd h0 (by omega), fun h => absurd h0 (by omega),
      fun _ => ⟨a57, by rw [aE, m1], aEn⟩, fun a ha => ?_, fun x hx => ?_,
      by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
    · rw [m2 a (by omega) (by omega), m1]
    · rw [n2 x (by omega), q1 x (by omega)]
  · -- nonempty
    have ht : c₁.nreg 8568 < c₁.nreg 3103 := by rw [hR1.r68, q1 _ (by omega), r03]; exact hpos
    have e49 : c₁.nreg 4900 = c.nreg 4900 := q1 _ (by omega)
    have e02 : c₁.nreg 4902 = c.nreg 4902 := q1 _ (by omega)
    have e09 : c₁.nreg 3109 = c.nreg 3109 := q1 _ (by omega)
    have e08 : c₁.nreg 3108 = c.nreg 3108 := q1 _ (by omega)
    obtain ⟨c₂, t₂, e₂, ht₂, a57, aIX, aM, aC, m2, n2, rr2, rm2, o2⟩ := lsBne_exec (I := I) c₁
      e₁.wb_right hR1 v58 (by rw [q1 _ (by omega)]; exact r03) v71 v69 v21 hpos hnBn
      (by rw [e49, e09, e08]; exact wM hpos) (by rw [e49, e02]; exact wC hpos) (by omega) w2
    have hR2 : LsR c₂ m k R n Sb := hR1.congr fun x hx => n2 x (by omega)
    refine ⟨c₂, t₁ + (t₂ + 1), .seq e₁ (.ifLtN_true ht e₂), by omega, hR2,
      by rw [n2 _ (by omega)]; exact v58, by rw [n2 _ (by omega)]; exact v59,
      by rw [n2 _ (by omega)]; exact v60, by rw [n2 _ (by omega)]; exact v61,
      by rw [n2 _ (by omega)]; exact v71, fun _ => ⟨a57, fun q hq => by rw [aIX q hq, m1]⟩,
      fun _ h j hj => by rw [aM (by rw [e49]; exact h) j hj, m1, e09, e08],
      fun _ h => by rw [← e02]; exact aC (by rw [e49]; exact h),
      fun h => absurd h (by omega), fun a ha => ?_, fun x hx => ?_,
      by rw [rr2, rr1], by rw [rm2, rm1], by rw [o2, o1]⟩
    · rw [m2 a ha, m1]
    · rw [n2 x (by omega), q1 x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
