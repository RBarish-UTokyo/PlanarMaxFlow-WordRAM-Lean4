module

public import PlanarFlow.BKMNW.StMapC

/-!
# The map part of the s-t flow encoding: the edge arrays and the whole program on arrays

* **`smED_exec`**: `edgProg` on `RV` (at `β`) and `NT` (at `β + 4m`): `NH` at `β + 5m`, `NG` at
  `β + 6m`, `NE` at `β + 7m`, `ED` at `β + 8m` (node offset `3m + 1`);
* **`smE_exec`**: `NG`, `NE` moved to `β + 3m`, `β + 2m`; `[β + 6m, β + 8m)` and the scratch
  `[S, S + 3m)` zero;
* **`smP_exec`**: the whole program, on index arrays `RV` (values `< m`) and `RT` (with `RT` and
  `NX = RT ∘ RV` permutations of `[0, m)`), within `140 m + 150` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset Function CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  OrbLab NsStep

variable {P : Input} {W : ℕ}

/-- **Stage D**: the edge arrays. -/
theorem smED_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb S β : ℕ}
    (hL : SmRegs c m RVb RTb S β) (hRV : ∀ x < m, c.nmem (β + x) < m)
    (w : β + 12 * m + 1 ≤ W) :
    ∃ c' t, Exec P W smED c c' t ∧ t ≤ 19 * m + 13 ∧
      (∀ x < m, c'.nmem (β + 5 * m + x) = c.nmem (β + 4 * m + c.nmem (β + x)) ∧
        c'.nmem (β + 6 * m + x) = m + 1 + min x (c.nmem (β + x)) ∧
        c'.nmem (β + 7 * m + x) = 3 * m + 1 + min x (c.nmem (β + x))) ∧
      (∀ x < m, ∃ x' < m, min x' (c.nmem (β + x')) = min x (c.nmem (β + x)) ∧
        c'.nmem (β + 8 * m + (3 * m + 1 + min x (c.nmem (β + x)))) = x') ∧
      (∀ a, a < β + 5 * m ∨ β + 12 * m + 1 ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ SmScr r → c'.nreg r = c.nreg r) ∧ SmRegs c' m RVb RTb S β ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have l1 : β + m ≤ β + 5 * m := by omega
  have l2 : β + 4 * m + m ≤ β + 5 * m := by omega
  have l3 : β + 5 * m + m ≤ β + 6 * m := by omega
  have l4 : β + 6 * m + m ≤ β + 7 * m := by omega
  have l5 : β + 7 * m + m ≤ β + 8 * m + (3 * m + 1) := by omega
  have w4 : m + 1 + m ≤ W := by omega
  have w6 : β + 8 * m + (3 * m + 1) + m ≤ W := by omega
  have w1 : 1 ≤ W := by omega
  obtain ⟨a0, -, -, -, a4, -, -, -, -, -, a9, a10, a11, a12, a13, -, a14, a15, -⟩ := id hL
  unfold smED
  obtain ⟨c₁, t₁, e₁, ht₁, b0, b1, b2, b3, b4, b5, b6, b7, b8, n₁, m₁, rr₁, rm₁, o₁⟩ :=
    setED_exec (P := P) c hc
  obtain ⟨c₂, t₂, e₂, ht₂, h1, h2, h3, n₂, rr₂, rm₂, o₂⟩ := NegSSSP.edgProg_exec (P := P) c₁
    e₁.wb_right (nD := m) (RVb := β) (NTb := β + 4 * m) (NHb := β + 5 * m) (ag := m + 1)
    (NGb := β + 6 * m) (ae := 3 * m + 1) (NEb := β + 7 * m) (EDb := β + 8 * m)
    (fun x hx => by rw [m₁]; exact hRV x hx) (by rw [b0, a0]) (by rw [b1, a4])
    (by rw [b2, a9]) (by rw [b3, a10]) (by rw [b4, a14]) (by rw [b5, a11]) (by rw [b6, a15])
    (by rw [b7, a12]) (by rw [b8, a13]) l1 l2 l3 l4 l5 w4 w6 w1
  rw [m₁] at h1 h2
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by clear * - ht₁ ht₂; omega, h1, h2, fun a ha => ?_,
    fun r hr => ?_, ?_, by rw [rr₂, rr₁], by rw [rm₂, rm₁], by rw [o₂, o₁]⟩
  · rw [h3 a (by clear * - ha; omega), m₁]
  · obtain ⟨-, -, -, -, -, -, q7⟩ := smScr_of hr
    rw [n₂ r (by clear * - q7; omega), n₁ r (by clear * - q7; omega)]
  · exact hL.of fun r h1 h2 => by
      rw [n₂ r (by clear * - h1 h2; omega), n₁ r (by clear * - h1 h2; omega)]

/-- **Stage E**: `NG`, `NE` in place, `IS` and `LN` zero, the scratch zero. -/
theorem smE_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb S β : ℕ}
    (hL : SmRegs c m RVb RTb S β) (l3 : S + 3 * m ≤ β) (w : β + 12 * m + 1 ≤ W) :
    ∃ c' t, Exec P W smE c c' t ∧ t ≤ 40 * m + 40 ∧
      (∀ i < m, c'.nmem (β + 3 * m + i) = c.nmem (β + 6 * m + i)) ∧
      (∀ i < m, c'.nmem (β + 2 * m + i) = c.nmem (β + 7 * m + i)) ∧
      (∀ i < 2 * m, c'.nmem (β + 6 * m + i) = 0) ∧ (∀ i < 3 * m, c'.nmem (S + i) = 0) ∧
      (∀ a, ¬ (S ≤ a ∧ a < S + 3 * m) → ¬ (β + 2 * m ≤ a ∧ a < β + 4 * m) →
        ¬ (β + 6 * m ≤ a ∧ a < β + 8 * m) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ SmScr r → c'.nreg r = c.nreg r) ∧ SmRegs c' m RVb RTb S β ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨a0, -, -, a3, -, -, -, -, a19, a18, -, -, a11, a12, -, a16, -, -, a20⟩ := id hL
  unfold smE smNG smNE smZI smZS
  obtain ⟨c₁, t₁, e₁, ht₁, b0, b1, b2, n₁, m₁, rr₁, rm₁, o₁⟩ := setC3_exec (P := P) c hc 7700 7711
    7718 (by omega) (by omega) (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, g1, g2, n₂, rr₂, rm₂, o₂⟩ := cpArr_exec (P := P) c₁ e₁.wb_right
    (n := m) (Sb := β + 6 * m) (Db := β + 3 * m) (by rw [b0, a0]) (by rw [b1, a11])
    (by rw [b2, a18]) ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  have q2 : ∀ r, 7700 ≤ r → r ≤ 7722 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [n₂ r (by omega), n₁ r (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, d0, d1, d2, n₃, m₃, rr₃, rm₃, o₃⟩ := setC3_exec (P := P) c₂
    e₂.wb_right 7700 7712 7719 (by omega) (by omega) (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, k1, k2, n₄, rr₄, rm₄, o₄⟩ := cpArr_exec (P := P) c₃ e₃.wb_right
    (n := m) (Sb := β + 7 * m) (Db := β + 2 * m) (by rw [d0, q2 _ (by omega) (by omega), a0])
    (by rw [d1, q2 _ (by omega) (by omega), a12]) (by rw [d2, q2 _ (by omega) (by omega), a19])
    ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  have q4 : ∀ r, 7700 ≤ r → r ≤ 7722 → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    rw [n₄ r (by omega), n₃ r (by omega), q2 r h1 h2]
  obtain ⟨c₅, t₅, e₅, ht₅, z0, z1, n₅, m₅, rr₅, rm₅, o₅⟩ := setZ_exec (P := P) c₄ e₄.wb_right
    7716 7711
  obtain ⟨c₆, t₆, e₆, ht₆, y1, y2, n₆, rr₆, rm₆, o₆⟩ := mzFill_exec (P := P) c₅ e₅.wb_right
    (len := 2 * m) (Zb := β + 6 * m) (by rw [z0, q4 _ (by omega) (by omega), a16])
    (by rw [z1, upd_other _ _ _ (by omega), q4 _ (by omega) (by omega), a11]) (by omega)
    (by omega)
  have q6 : ∀ r, 7700 ≤ r → r ≤ 7722 → c₆.nreg r = c.nreg r := fun r h1 h2 => by
    rw [n₆ r (by omega), n₅ r (by omega), q4 r h1 h2]
  obtain ⟨c₇, t₇, e₇, ht₇, x0, x1, n₇, m₇, rr₇, rm₇, o₇⟩ := setZ_exec (P := P) c₆ e₆.wb_right
    7720 7703
  obtain ⟨c₈, t₈, e₈, ht₈, v1, v2, n₈, rr₈, rm₈, o₈⟩ := mzFill_exec (P := P) c₇ e₇.wb_right
    (len := 3 * m) (Zb := S) (by rw [x0, q6 _ (by omega) (by omega), a20])
    (by rw [x1, upd_other _ _ _ (by omega), q6 _ (by omega) (by omega), a3]) (by omega)
    (by omega)
  -- the memory after each stage
  have M8 : ∀ a, ¬ (S ≤ a ∧ a < S + 3 * m) → c₈.nmem a = c₆.nmem a := fun a ha => by
    rw [v2 a (by omega), m₇]
  have M6 : ∀ a, ¬ (β + 6 * m ≤ a ∧ a < β + 8 * m) → c₆.nmem a = c₄.nmem a := fun a ha => by
    rw [y2 a (by omega), m₅]
  have M4 : ∀ a, ¬ (β + 2 * m ≤ a ∧ a < β + 3 * m) → c₄.nmem a = c₂.nmem a := fun a ha => by
    rw [k2 a (by omega), m₃]
  have M2 : ∀ a, ¬ (β + 3 * m ≤ a ∧ a < β + 4 * m) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [g2 a (by omega), m₁]
  refine ⟨c₈, (t₁ + t₂) + ((t₃ + t₄) + ((t₅ + t₆) + (t₇ + t₈))),
    .seq (.seq e₁ e₂) (.seq (.seq e₃ e₄) (.seq (.seq e₅ e₆) (.seq e₇ e₈))), by omega,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun a h1 h2 h3 => ?_,
    fun r hr => ?_, ?_, by rw [rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁], by rw [o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [M8 _ (by omega), M6 _ (by omega), M4 _ (by omega), g1 i hi, m₁]
  · rw [M8 _ (by omega), M6 _ (by omega), k1 i hi, m₃, M2 _ (by omega)]
  · rw [M8 _ (by omega)]; exact y1 i hi
  · exact v1 i hi
  · rw [M8 _ h1, M6 _ h3, M4 _ (by omega), M2 _ (by omega)]
  · obtain ⟨q1, q2', -, q4', -⟩ := smScr_of hr
    rw [n₈ r (by omega), n₇ r (by omega), n₆ r (by omega), n₅ r (by omega), n₄ r (by omega),
      n₃ r (by omega), n₂ r (by omega), n₁ r (by omega)]
  · exact hL.of fun r h1 h2 => by rw [n₈ r (by omega), n₇ r (by omega), q6 r h1 h2]

end StEnc

end BKMNW

end PlanarFlow
