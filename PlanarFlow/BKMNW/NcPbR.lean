module

public import PlanarFlow.BKMNW.NcPb

/-!
# The runs of the set-up and of the copy-out of `pbP`

* **`pbS1_exec`**: `pbS1` saves the frame's flow array `FL` to `SV = Sb + 32 m + 1`, copies `G`
  into `FL`, writes `BT' = Kd + BT` (`Kd = (Z + Z) m + (Z + Z)`) at `Sb + 30 m + 1`, `FR = 0` at
  `Sb + 31 m + 1`, the header cell `d + 3 := 2Z`, and `pchP`'s registers, within `41 m + 66` steps;
* **`pbS3_exec`**: `pbS3` copies `FL` to `PB`, `SV` back to `FL` and the header cell back to `Z`,
  within `24 m + 21` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- The first part of the set-up: `SV := FL`, `FL := G`. -/
theorem pbS1v_exec (c : Config) (hc : WordsBounded W c) {m Gb FL SV : ℕ}
    (r01 : c.nreg 9901 = m) (r09 : c.nreg 9909 = Gb) (r06 : c.nreg 9906 = FL)
    (b61 : c.nreg 9261 = m) (b62 : c.nreg 9262 = FL) (b63 : c.nreg 9263 = FL)
    (b64 : c.nreg 9264 = SV) (b65 : c.nreg 9265 = 0) (b66 : c.nreg 9266 = 0)
    (dFS : FL + m ≤ SV) (dFG : FL + m ≤ Gb) (dGS : Gb + m ≤ SV) (w : SV + m + 1 ≤ W) :
    ∃ c' k, Exec P W pbS1v c c' k ∧ k ≤ 24 * m + 14 ∧
      (∀ i < m, c'.nmem (SV + i) = c.nmem (FL + i)) ∧
      (∀ i < m, c'.nmem (FL + i) = c.nmem (Gb + i)) ∧
      (∀ x, (x < FL ∨ FL + m ≤ x) → (x < SV ∨ SV + m ≤ x) → c'.nmem x = c.nmem x) ∧
      (∀ r, 9900 ≤ r → r ≤ 9915 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, o₁, f₁, rr₁, rm₁, oo₁⟩ := cpyL_exec (P := P) c hc
    b61 b62 b63 b64 b65 b66 (Or.inl dFS) (by omega) (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, d61, d62, d63, d64, d65, d66, mm₂, rr₂, rm₂, oo₂⟩ :=
    pbG1_exec (P := P) (m := m) (Gb := Gb) (FL := FL) c₁ e₁.wb_right
      (by rw [f₁ _ (by omega)]; exact r01) (by rw [f₁ _ (by omega)]; exact r09)
      (by rw [f₁ _ (by omega)]; exact r06)
  have q₂ := keepW_of_all e₂ pbG1_dests
  obtain ⟨c₃, k₃, e₃, hk₃, v₃, o₃, f₃, rr₃, rm₃, oo₃⟩ := cpyL_exec (P := P) c₂ e₂.wb_right
    d61 d62 d63 d64 d65 d66 (Or.inr dFG) (by omega) (by omega) (by omega)
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, fun i hi => ?_, fun i hi => ?_,
    fun x h1 h2 => ?_, fun r h1 h2 => ?_, by rw [rr₃, rr₂, rr₁], by rw [rm₃, rm₂, rm₁],
    by rw [oo₃, oo₂, oo₁]⟩
  · rw [o₃ _ (Or.inr (by omega)), mm₂, v₁ i hi]
  · rw [v₃ i hi, mm₂, o₁ _ (Or.inl (by omega))]
  · rw [o₃ _ h1, mm₂, o₁ _ h2]
  · rw [f₃ r (by omega), q₂ r (by omega), f₁ r (by omega)]

set_option maxHeartbeats 1000000 in
/-- The second part of the set-up: `BT' := Kd + BT`, `FR := 0`, `a := v`, `pchP`'s registers. -/
theorem pbS1u_exec (c : Config) (hc : WordsBounded W c) {m BTb BT' FR Kd a v A : ℕ}
    (r01 : c.nreg 9901 = m) (r10 : c.nreg 9910 = BTb) (r05 : c.nreg 9905 = BT')
    (r07 : c.nreg 9907 = Kd) (r13 : c.nreg 9913 = FR) (r12 : c.nreg 9912 = a)
    (r03 : c.nreg 9903 = v) (r04 : c.nreg 9904 = A)
    (dB : BTb + m ≤ BT') (hFR : FR = BT' + m) (ha : a < BT') (w : FR + m + 1 ≤ W)
    (wB : ∀ i < m, Kd + c.nmem (BTb + i) ≤ W) :
    ∃ c' k, Exec P W pbS1u c c' k ∧ k ≤ 17 * m + 22 ∧
      c'.nreg 9200 = A ∧ c'.nreg 9201 = BT' ∧ c'.nreg 9202 = FR ∧ c'.nreg 9203 = Kd ∧
      (∀ i < m, c'.nmem (BT' + i) = Kd + c.nmem (BTb + i)) ∧
      (∀ i < m, c'.nmem (FR + i) = 0) ∧ c'.nmem a = v ∧
      (∀ x, x ≠ a → (x < BT' ∨ FR + m ≤ x) → c'.nmem x = c.nmem x) ∧
      (∀ r, 9900 ≤ r → r ≤ 9915 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  subst hFR
  obtain ⟨c₄, k₄, e₄, hk₄, g61, g62, g63, g64, g65, g66, mm₄, rr₄, rm₄, oo₄⟩ :=
    pbG2_exec (P := P) (m := m) (BTb := BTb) (BT' := BT') (Kd := Kd) c hc r01 r10 r05 r07
  have q₄ := keepW_of_all e₄ pbG2_dests
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, o₅, f₅, rr₅, rm₅, oo₅⟩ := dvL_exec (P := P) c₄ e₄.wb_right
    g61 g62 g63 g64 g65 g66 (Or.inl dB) (Or.inl dB) (by omega) (by omega)
    (by omega) (by omega) (fun i hi => by rw [mm₄]; exact wB i hi) (fun i hi => by simp)
  have t₅ : ∀ r, 9900 ≤ r → r ≤ 9915 → c₅.nreg r = c.nreg r := fun r h1 h2 => by
    rw [f₅ r (by omega), q₄ r (by omega)]
  obtain ⟨c₆, k₆, e₆, hk₆, h51, h52, h53, mm₆, rr₆, rm₆, oo₆⟩ :=
    pbG3_exec (P := P) (m := m) (FR := BT' + m) c₅ e₅.wb_right
      (by rw [t₅ _ (by omega) (by omega)]; exact r01) (by rw [t₅ _ (by omega) (by omega)]; exact r13)
  have q₆ := keepW_of_all e₆ pbG3_dests
  obtain ⟨c₇, k₇, e₇, hk₇, v₇, o₇, f₇, rr₇, rm₇, oo₇⟩ := cstL_exec (P := P) c₆ e₆.wb_right
    h51 h52 h53 (by omega) (by omega)
  have t₇ : ∀ r, 9900 ≤ r → r ≤ 9915 → c₇.nreg r = c.nreg r := fun r h1 h2 => by
    rw [f₇ r (by omega), q₆ r (by omega), t₅ r h1 h2]
  obtain ⟨c₈, k₈, e₈, hk₈, p00, p01, p02, p03, mm₈, rr₈, rm₈, oo₈⟩ :=
    pbG4_exec (P := P) (a := a) (v := v) (A := A) (BT' := BT') (FR := BT' + m) (Kd := Kd) c₇
      e₇.wb_right (by rw [t₇ _ (by omega) (by omega)]; exact r12)
      (by rw [t₇ _ (by omega) (by omega)]; exact r03) (by rw [t₇ _ (by omega) (by omega)]; exact r04)
      (by rw [t₇ _ (by omega) (by omega)]; exact r05) (by rw [t₇ _ (by omega) (by omega)]; exact r13)
      (by rw [t₇ _ (by omega) (by omega)]; exact r07)
  have q₈ := keepW_of_all e₈ pbG4_dests
  refine ⟨c₈, _, .seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈))), by omega, p00, p01, p02, p03,
    fun i hi => ?_, fun i hi => ?_, by rw [mm₈, upd_same], fun x h1 h2 => ?_,
    fun r h1 h2 => ?_, by rw [rr₈, rr₇, rr₆, rr₅, rr₄], by rw [rm₈, rm₇, rm₆, rm₅, rm₄],
    by rw [oo₈, oo₇, oo₆, oo₅, oo₄]⟩
  · rw [mm₈, upd_other _ _ _ (by omega), o₇ _ (Or.inl (by omega)), mm₆, v₅ i hi, mm₄]; simp
  · rw [mm₈, upd_other _ _ _ (by omega), v₇ i hi]
  · rw [mm₈, upd_other _ _ _ h1]
    rcases h2 with h2 | h2
    · rw [o₇ _ (Or.inl (by omega)), mm₆, o₅ _ (Or.inl h2), mm₄]
    · rw [o₇ _ (Or.inr (by omega)), mm₆, o₅ _ (Or.inr (by omega)), mm₄]
  · rw [q₈ r (by omega), t₇ r h1 h2]

set_option maxHeartbeats 1000000 in
/-- **The set-up of `pbP`.** -/
theorem pbS1_exec (c : Config) (hc : WordsBounded W c) {d m Z Sb PBb Gb BTb : ℕ}
    (r04 : c.nreg 3004 = d) (hm : c.nmem d = m) (hZ : c.nmem (d + 3) = Z)
    (r05 : c.nreg 9805 = BTb) (r06 : c.nreg 9806 = Gb) (r07 : c.nreg 9807 = PBb)
    (r08 : c.nreg 9808 = Sb)
    (lG : d + 4 + 7 * m ≤ Gb) (lB : d + 4 + 7 * m ≤ BTb) (sG : Gb + m ≤ Sb) (sB : BTb + m ≤ Sb)
    (w1 : Sb + 33 * m + 2 ≤ W) (w3 : (Z + Z) * m + (Z + Z) ≤ W) (w4 : 30 ≤ W)
    (wB : ∀ i < m, (Z + Z) * m + (Z + Z) + c.nmem (BTb + i) ≤ W) :
    ∃ c' k, Exec P W pbS1 c c' k ∧ k ≤ 41 * m + 66 ∧
      c'.nreg 9200 = Sb ∧ c'.nreg 9201 = 30 * m + Sb + 1 ∧
      c'.nreg 9202 = 30 * m + Sb + 1 + m ∧ c'.nreg 9203 = (Z + Z) * m + (Z + Z) ∧
      c'.nreg 9901 = m ∧ c'.nreg 9902 = Z ∧ c'.nreg 9906 = 6 * m + d + 4 ∧
      c'.nreg 9908 = PBb ∧ c'.nreg 9912 = d + 3 ∧ c'.nreg 9914 = 30 * m + Sb + 1 + m + m ∧
      (∀ i < m, c'.nmem (30 * m + Sb + 1 + m + m + i) = c.nmem (6 * m + d + 4 + i)) ∧
      (∀ i < m, c'.nmem (6 * m + d + 4 + i) = c.nmem (Gb + i)) ∧
      (∀ i < m, c'.nmem (30 * m + Sb + 1 + i) = (Z + Z) * m + (Z + Z) + c.nmem (BTb + i)) ∧
      (∀ i < m, c'.nmem (30 * m + Sb + 1 + m + i) = 0) ∧
      c'.nmem (d + 3) = Z + Z ∧
      (∀ a, a ≠ d + 3 → (a < 6 * m + d + 4 ∨ 6 * m + d + 4 + m ≤ a) →
        (a < 30 * m + Sb + 1 ∨ 30 * m + Sb + 1 + m + m + m ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₀, k₀, e₀, hk₀, a00, a01, a02, a03, a04, a05, a13, a14, a06, a07, a08, a09, a10, a12,
    b61, b62, b63, b64, b65, b66, mm₀, rr₀, rm₀, o₀⟩ :=
    pbG0_exec (P := P) c hc r04 hm hZ r05 r06 r07 r08 w1 (by omega) w3 w4
  obtain ⟨c₁, k₁, e₁, hk₁, sv₁, fl₁, o₁, t₁, rr₁, rm₁, oo₁⟩ :=
    pbS1v_exec (P := P) (m := m) (Gb := Gb) (FL := 6 * m + d + 4)
      (SV := 30 * m + Sb + 1 + m + m) c₀ e₀.wb_right a01 a09 a06 b61 b62 b63 b64 b65 b66
      (by omega) (by omega) (by omega) (by omega)
  have mB : ∀ i < m, c₁.nmem (BTb + i) = c.nmem (BTb + i) := fun i hi => by
    rw [o₁ _ (Or.inr (by omega)) (Or.inl (by omega)), mm₀]
  obtain ⟨c₂, k₂, e₂, hk₂, p00, p01, p02, p03, bt₂, fr₂, z₂, o₂, t₂, rr₂, rm₂, oo₂⟩ :=
    pbS1u_exec (P := P) (m := m) (BTb := BTb) (BT' := 30 * m + Sb + 1)
      (FR := 30 * m + Sb + 1 + m) (Kd := (Z + Z) * m + (Z + Z)) (a := d + 3) (v := Z + Z)
      (A := Sb) c₁ e₁.wb_right
      (by rw [t₁ _ (by omega) (by omega)]; exact a01) (by rw [t₁ _ (by omega) (by omega)]; exact a10)
      (by rw [t₁ _ (by omega) (by omega)]; exact a05) (by rw [t₁ _ (by omega) (by omega)]; exact a07)
      (by rw [t₁ _ (by omega) (by omega)]; exact a13) (by rw [t₁ _ (by omega) (by omega)]; exact a12)
      (by rw [t₁ _ (by omega) (by omega)]; exact a03) (by rw [t₁ _ (by omega) (by omega)]; exact a04)
      (by omega) rfl (by omega) (by omega) (fun i hi => by rw [mB i hi]; exact wB i hi)
  have tt : ∀ r, 9900 ≤ r → r ≤ 9915 → c₂.nreg r = c₀.nreg r := fun r h1 h2 => by
    rw [t₂ r h1 h2, t₁ r h1 h2]
  refine ⟨c₂, _, .seq e₀ (.seq e₁ e₂), by omega, p00, p01, p02, p03,
    by rw [tt _ (by omega) (by omega)]; exact a01, by rw [tt _ (by omega) (by omega)]; exact a02,
    by rw [tt _ (by omega) (by omega)]; exact a06, by rw [tt _ (by omega) (by omega)]; exact a08,
    by rw [tt _ (by omega) (by omega)]; exact a12, by rw [tt _ (by omega) (by omega)]; exact a14,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fr₂, z₂, fun a h1 h2 h3 => ?_,
    by rw [rr₂, rr₁, rr₀], by rw [rm₂, rm₁, rm₀], by rw [oo₂, oo₁, o₀]⟩
  · rw [o₂ _ (by omega) (Or.inr (by omega)), sv₁ i hi, mm₀]
  · rw [o₂ _ (by omega) (Or.inl (by omega)), fl₁ i hi, mm₀]
  · rw [bt₂ i hi, mB i hi]
  · rcases h3 with h3 | h3
    · rw [o₂ _ h1 (Or.inl h3), o₁ _ h2 (Or.inl (by omega)), mm₀]
    · rw [o₂ _ h1 (Or.inr (by omega)), o₁ _ h2 (Or.inr (by omega)), mm₀]

set_option maxHeartbeats 1000000 in
/-- **The copy-out of `pbP`.** -/
theorem pbS3_exec (c : Config) (hc : WordsBounded W c) {m Z a FL PBb SV : ℕ}
    (r01 : c.nreg 9901 = m) (r02 : c.nreg 9902 = Z) (r06 : c.nreg 9906 = FL)
    (r08 : c.nreg 9908 = PBb) (r12 : c.nreg 9912 = a) (r14 : c.nreg 9914 = SV)
    (haF : a < FL) (hFP : FL + m ≤ PBb) (hPS : PBb + m ≤ SV) (w : SV + m + 1 ≤ W) :
    ∃ c' k, Exec P W pbS3 c c' k ∧ k ≤ 24 * m + 21 ∧
      (∀ i < m, c'.nmem (PBb + i) = c.nmem (FL + i)) ∧
      (∀ i < m, c'.nmem (FL + i) = c.nmem (SV + i)) ∧ c'.nmem a = Z ∧
      (∀ x, x ≠ a → (x < PBb ∨ PBb + m ≤ x) → (x < FL ∨ FL + m ≤ x) → c'.nmem x = c.nmem x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, d61, d62, d63, d64, d65, d66, mm₁, rr₁, rm₁, oo₁⟩ :=
    pbG5_exec (P := P) c hc r01 r06 r08
  have q₁ := keepW_of_all e₁ pbG5_dests
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, o₂, f₂, rr₂, rm₂, oo₂⟩ := cpyL_exec (P := P) c₁ e₁.wb_right
    d61 d62 d63 d64 d65 d66 (Or.inl hFP) (by omega) (by omega) (by omega)
  have t₂ : ∀ r, 9900 ≤ r → r ≤ 9915 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [f₂ r (by omega), q₁ r (by omega)]
  obtain ⟨c₃, k₃, e₃, hk₃, g61, g62, g63, g64, g65, g66, mm₃, rr₃, rm₃, oo₃⟩ :=
    pbG6_exec (P := P) (m := m) (SV := SV) (FL := FL) c₂ e₂.wb_right (by rw [t₂ _ (by omega) (by omega)]; exact r01)
      (by rw [t₂ _ (by omega) (by omega)]; exact r14) (by rw [t₂ _ (by omega) (by omega)]; exact r06)
  have q₃ := keepW_of_all e₃ pbG6_dests
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, o₄, f₄, rr₄, rm₄, oo₄⟩ := cpyL_exec (P := P) c₃ e₃.wb_right
    g61 g62 g63 g64 g65 g66 (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have t₄ : ∀ r, 9900 ≤ r → r ≤ 9915 → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    rw [f₄ r (by omega), q₃ r (by omega), t₂ r h1 h2]
  obtain ⟨c₅, k₅, e₅, hk₅, mm₅, rr₅, rm₅, oo₅⟩ :=
    pbG7_exec (P := P) (a := a) (v := Z) c₄ e₄.wb_right (by rw [t₄ _ (by omega) (by omega)]; exact r12)
      (by rw [t₄ _ (by omega) (by omega)]; exact r02)
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega, fun i hi => ?_,
    fun i hi => ?_, by rw [mm₅, upd_same], fun x h1 h2 h3 => ?_,
    by rw [rr₅, rr₄, rr₃, rr₂, rr₁], by rw [rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [oo₅, oo₄, oo₃, oo₂, oo₁]⟩
  · rw [mm₅, upd_other _ _ _ (by omega), o₄ _ (Or.inr (by omega)), mm₃, v₂ i hi, mm₁]
  · rw [mm₅, upd_other _ _ _ (by omega), v₄ i hi, mm₃, o₂ _ (Or.inr (by omega)), mm₁]
  · rw [mm₅, upd_other _ _ _ h1, o₄ _ h3, mm₃, o₂ _ h2, mm₁]

end NcStep

end BKMNW

end PlanarFlow
