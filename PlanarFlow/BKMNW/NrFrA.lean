module

public import PlanarFlow.BKMNW.NrFrG

/-!
# The core of `retP`/`frmP`, phase A: the net outflow per dart and the free flags

**`fcA = fA ; dvP ; fB ; decL ; fC ; dvL ; fD ; lgProg ; fE1 ; fE2 ; frL`** (scratch from `b`,
`r3006 = b + 5`): the vertex labels `VL = olab SG` (`b + 3m`), the words `Kd + div g` per label
(`b + 4m`) and per dart (`DVA` at `b + 5m`, `Kd = m Z + Z`), the free flags
`FRa[i] = [KR[i] = kfr]` (`b + 6m`, `kfr = r9185`).

* **`FcR`** (the registers `9180 … 9189` of the core), `FcR.congr`;
* **`fcA_exec`**: within `90 m + 90` steps; memory changed only in `[b, b + 7m)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

/-- **The registers of the core of `retP`/`frmP`.** -/
structure FcR (c : Config) (d b m Z kfr : ℕ) : Prop where
  r80 : c.nreg 9180 = d
  r81 : c.nreg 9181 = m
  r82 : c.nreg 9182 = Z
  r83 : c.nreg 9183 = b
  r84 : c.nreg 9184 = m * Z + Z
  r85 : c.nreg 9185 = kfr
  r86 : c.nreg 9186 = b + 3 * m
  r87 : c.nreg 9187 = b + 4 * m
  r88 : c.nreg 9188 = b + 5 * m
  r89 : c.nreg 9189 = b + 6 * m

lemma FcR.congr {c c' : Config} {d b m Z kfr : ℕ} (h : FcR c d b m Z kfr)
    (hk : ∀ x, 9180 ≤ x → x ≤ 9189 → c'.nreg x = c.nreg x) : FcR c' d b m Z kfr where
  r80 := by rw [hk _ (by omega) (by omega), h.r80]
  r81 := by rw [hk _ (by omega) (by omega), h.r81]
  r82 := by rw [hk _ (by omega) (by omega), h.r82]
  r83 := by rw [hk _ (by omega) (by omega), h.r83]
  r84 := by rw [hk _ (by omega) (by omega), h.r84]
  r85 := by rw [hk _ (by omega) (by omega), h.r85]
  r86 := by rw [hk _ (by omega) (by omega), h.r86]
  r87 := by rw [hk _ (by omega) (by omega), h.r87]
  r88 := by rw [hk _ (by omega) (by omega), h.r88]
  r89 := by rw [hk _ (by omega) (by omega), h.r89]

/-- **Phase A of the core**: the net outflow per dart, the free flags. -/
def fcA : Stmt :=
  .seq fA (.seq dvP (.seq fB (.seq decL (.seq fC (.seq dvL (.seq fD (.seq lgProg (.seq fE1
    (.seq fE2 frL)))))))))

section Exec

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **Phase A of the core** (see the module docstring). -/
theorem fcA_exec (c : Config) (hc : WordsBounded W c) {d b m Z kfr : ℕ}
    (r3004 : c.nreg 3004 = d) (r3006 : c.nreg 3006 = b + 5) (r85 : c.nreg 9185 = kfr)
    (hm : c.nmem d = m) (hz : c.nmem (d + 3) = Z) (hp : PermOn (sgF d m c.nmem) m)
    (hA : d + 4 + 7 * m ≤ b) (w : b + 40 * m + 10 ≤ W)
    (hFL : ∑ j ∈ range m, c.nmem (d + 6 * m + 4 + j) ≤ 2 * (m * Z))
    (wK : m * Z + Z + 2 * (m * Z) ≤ W) :
    ∃ c' t, Exec P W fcA c c' t ∧ t ≤ 90 * m + 90 ∧ FcR c' d b m Z kfr ∧ c'.nreg 3004 = d ∧
      (∀ i < m, c'.nmem (b + 3 * m + i) = olab (sgF d m c.nmem) i) ∧
      (∀ i < m, c'.nmem (b + 5 * m + i) =
        m * Z + Z + dvS (olab (sgF d m c.nmem)) (fun j => c.nmem (d + 6 * m + 4 + j)) m
          (olab (sgF d m c.nmem) i) - Z * dvC (olab (sgF d m c.nmem)) m (olab (sgF d m c.nmem) i)) ∧
      (∀ i < m, c'.nmem (b + 6 * m + i) = if c.nmem (d + 4 + 4 * m + i) = kfr then 1 else 0) ∧
      (∀ a, (a < b ∨ b + 7 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- `fA`
  obtain ⟨c₁, t₁, e₁, ht₁, a8430, a80, a81, a82, a83, a84, a98, a99, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    fA_exec (P := P) c hc (by rw [r3004]; clear * - w hA; omega) (by clear * - w hA; omega)
      (by rw [r3004]; clear * - w hA; omega) (by rw [r3004]; clear * - w hA; omega)
      (by clear * - w hA; omega) (by rw [r3004, hm, hz]; clear * - wK; omega)
      (by rw [r3004, hm, hz]; clear * - wK; omega)
  simp only [r3004, hm, hz, r3006] at a8430 a80 a81 a82 a83 a84
  have hb5 : b + 5 - 5 = b := by omega
  rw [hb5] at a8430 a83
  have q₁ : ∀ x, x ≠ 8430 → (x < 9180 ∨ 9184 < x) → x ≠ 9198 → x ≠ 9199 →
      c₁.nreg x = c.nreg x := fun x h1 h2 h3 h4 =>
    f₁ x h1 (by clear * - h2; omega) (by clear * - h2; omega) (by clear * - h2; omega)
      (by clear * - h2; omega) (by clear * - h2; omega) h3 h4
  -- `dvP`
  obtain ⟨c₂, t₂, e₂, ht₂, l₂, s₂, k₂, f₂, rr₂, rm₂, o₂⟩ := dvP_exec (P := P) c₁ e₁.wb_right
    (d := d) (A := b) (m := m) (by rw [q₁ _ (by decide) (by decide) (by decide) (by decide),
      r3004]) a8430 (by rw [m₁, hm]) (by rw [m₁]; exact hp) hA
    (by clear * - w hA; omega) (by clear * - w hA; omega) (by rw [m₁]; clear * - hFL wK; omega)
  simp only [m₁] at l₂ s₂
  have q₂ : ∀ x, 9180 ≤ x → x ≤ 9199 → c₂.nreg x = c₁.nreg x := fun x h1 h2 =>
    f₂ x (by clear * - h1; omega) (by clear * - h1; omega) (by clear * - h1; omega)
  have mem₂ : ∀ a, (a < b ∨ b + 3 * m ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [k₂ a ha, m₁]
  -- `fB ; decL`: `VL`
  obtain ⟨c₃, t₃, e₃, ht₃, b86, b41, b42, b43, f₃, m₃, rr₃, rm₃, o₃⟩ := fB_exec (P := P) c₂
    e₂.wb_right (by rw [q₂ _ (by decide) (by decide), q₂ _ (by decide) (by decide), a83, a81]; clear * - w hA; omega)
    (by rw [q₂ _ (by decide) (by decide), q₂ _ (by decide) (by decide), a83, a81]; clear * - w hA; omega)
    (by rw [q₂ _ (by decide) (by decide), q₂ _ (by decide) (by decide), a83, a81]; clear * - w hA; omega)
  simp only [q₂ 9183 (by decide) (by decide), q₂ 9181 (by decide) (by decide), a83, a81] at b86 b41 b42 b43
  obtain ⟨c₄, t₄, e₄, ht₄, v₄, k₄, f₄, rr₄, rm₄, o₄⟩ := decL_exec (P := P) c₃ e₃.wb_right
    b41 b42 b43 (Or.inl (by clear * -; omega)) (by clear * - w hA; omega) (by clear * - w hA; omega)
    (by clear * - w hA; omega)
  have vl₄ : ∀ i < m, c₄.nmem (b + m + m + m + i) = (olab (sgF d m c.nmem)) i := fun i hi => by
    rw [v₄ i hi, m₃, l₂ i hi]; clear * -; omega
  -- registers 9180 … 9199 since `c₁`
  have K4 : ∀ x, 9180 ≤ x → x ≤ 9199 → x ≠ 9186 → c₄.nreg x = c₁.nreg x := fun x h1 h2 h3 => by
    rw [f₄ x (by clear * - h1 h2; omega), f₃ x h3 (by clear * - h1 h2; omega)
      (by clear * - h1 h2; omega) (by clear * - h1 h2; omega), q₂ x h1 h2]
  have r86₄ : c₄.nreg 9186 = b + m + m + m := by
    rw [f₄ _ (by decide)]; exact b86
  -- `fC ; dvL`: `DV` per label
  obtain ⟨c₅, t₅, e₅, ht₅, g87, g61, g62, g63, g64, g65, g66, f₅, m₅, rr₅, rm₅, o₅⟩ :=
    fC_exec (P := P) c₄ e₄.wb_right
      (by rw [K4 _ (by decide) (by decide) (by decide), K4 _ (by decide) (by decide) (by decide),
        a83, a81]; clear * - w hA; omega)
      (by rw [K4 _ (by decide) (by decide) (by decide), K4 _ (by decide) (by decide) (by decide),
        a83, a81]; clear * - w hA; omega)
      (by rw [r86₄, K4 _ (by decide) (by decide) (by decide), a81]; clear * - w hA; omega)
  simp only [K4 9183 (by decide) (by decide) (by decide), K4 9181 (by decide) (by decide) (by decide), K4 9184 (by decide) (by decide) (by decide), K4 9182 (by decide) (by decide) (by decide), r86₄, a83, a81, a84, a82] at g87 g61 g62 g63 g64 g65 g66
  have hS : ∀ v < m, c₄.nmem (b + m + v) =
      dvS (olab (sgF d m c.nmem)) (fun j => c.nmem (d + 6 * m + 4 + j)) m v := fun v hv => by
    rw [k₄ _ (by clear * - hv; omega), m₃]; exact (s₂ v hv).1
  have hG : ∀ v < m, c₄.nmem (b + m + m + v) = dvC (olab (sgF d m c.nmem)) m v := fun v hv => by
    rw [k₄ _ (by clear * - hv; omega), m₃]; exact (s₂ v hv).2
  have hSle : ∀ v < m, dvS (olab (sgF d m c.nmem)) (fun j => c.nmem (d + 6 * m + 4 + j)) m v ≤ 2 * (m * Z) :=
    fun v _ => (dvS_le _ _ _ _).trans hFL
  obtain ⟨c₆, t₆, e₆, ht₆, v₆, k₆, f₆, rr₆, rm₆, o₆⟩ := dvL_exec (P := P) c₅ e₅.wb_right
    g61 g62 g63 g64 g65 g66 (Or.inl (by clear * -; omega)) (Or.inl (by clear * -; omega))
    (by clear * - w hA; omega) (by clear * - w hA; omega) (by clear * - w hA; omega) (by clear * - w hA; omega)
    (fun i hi => by rw [m₅, hS i hi]; have := hSle i hi; clear * - this wK; omega)
    (fun i hi => by
      rw [m₅, hG i hi]
      calc Z * dvC (olab (sgF d m c.nmem)) m i ≤ Z * m := Nat.mul_le_mul_left _ (dvC_le _ _ _)
        _ = m * Z := Nat.mul_comm _ _
        _ ≤ W := by clear * - wK; omega)
  have K6 : ∀ x, 9180 ≤ x → x ≤ 9199 → x ≠ 9186 → x ≠ 9187 → c₆.nreg x = c₁.nreg x :=
    fun x h1 h2 h3 h4 => by
      rw [f₆ x (by clear * - h1 h2; omega), f₅ x h4 (by clear * - h1 h2; omega)
        (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
        (by clear * - h1 h2; omega) (by clear * - h1 h2; omega), K4 x h1 h2 h3]
  have r86₆ : c₆.nreg 9186 = b + m + m + m := by
    rw [f₆ _ (by decide), f₅ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)]; exact r86₄
  have r87₆ : c₆.nreg 9187 = b + m + m + m + m := by
    rw [f₆ _ (by decide)]; exact g87
  -- `fD ; lgProg`: `DVA[i] = DV[VL[i]]`
  obtain ⟨c₇, t₇, e₇, ht₇, h10, h11, h12, h13, h88, f₇, m₇, rr₇, rm₇, o₇⟩ :=
    fD_exec (P := P) c₆ e₆.wb_right
      (by rw [r87₆, K6 9181 (by decide) (by decide) (by decide) (by decide), a81]; clear * - w hA; omega)
  simp only [K6 9181 (by decide) (by decide) (by decide) (by decide), r86₆, r87₆, a81] at h10 h11 h12 h13 h88
  have vl₇ : ∀ i < m, c₇.nmem (b + m + m + m + i) = (olab (sgF d m c.nmem)) i := fun i hi => by
    rw [m₇, k₆ _ (by clear * - hi; omega), m₅]; exact vl₄ i hi
  have dv₇ : ∀ v < m, c₇.nmem (b + m + m + m + m + v) =
      m * Z + Z + dvS (olab (sgF d m c.nmem)) (fun j => c.nmem (d + 6 * m + 4 + j)) m v - Z * dvC (olab (sgF d m c.nmem)) m v :=
    fun v hv => by
      rw [m₇, v₆ v hv, m₅, hS v hv, show b + m + m + v = b + m + m + v from rfl, hG v hv]
  obtain ⟨c₈, t₈, e₈, ht₈, v₈, k₈, f₈, rr₈, rm₈, o₈⟩ := lgProg_exec (P := P) c₇ e₇.wb_right
    h10 h11 h12 h13 (by clear * - w hA; omega) (by clear * - w hA; omega) (by clear * - w hA; omega)
    (fun j hj => by rw [vl₇ j hj]; have := olab_lt hp hj; clear * - this w hA; omega)
    (fun j hj => by clear * - hj; omega)
    (fun j hj => by rw [vl₇ j hj]; have := olab_lt hp hj; clear * - this; omega)
  have K8 : ∀ x, 9180 ≤ x → x ≤ 9199 → x ≠ 9186 → x ≠ 9187 → x ≠ 9188 →
      c₈.nreg x = c₁.nreg x := fun x h1 h2 h3 h4 h5 => by
    rw [f₈ x (by clear * - h1 h2; omega), f₇ x (by clear * - h1 h2; omega)
      (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) h5,
      K6 x h1 h2 h3 h4]
  have r86₈ : c₈.nreg 9186 = b + m + m + m := by
    rw [f₈ _ (by decide), f₇ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact r86₆
  have r87₈ : c₈.nreg 9187 = b + m + m + m + m := by
    rw [f₈ _ (by decide), f₇ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact r87₆
  have r88₈ : c₈.nreg 9188 = b + m + m + m + m + m := by
    rw [f₈ _ (by decide)]; exact h88
  have dva₈ : ∀ i < m, c₈.nmem (b + m + m + m + m + m + i) =
      m * Z + Z + dvS (olab (sgF d m c.nmem)) (fun j => c.nmem (d + 6 * m + 4 + j)) m ((olab (sgF d m c.nmem)) i) - Z * dvC (olab (sgF d m c.nmem)) m ((olab (sgF d m c.nmem)) i) :=
    fun i hi => by rw [v₈ i hi, vl₇ i hi]; exact dv₇ _ (olab_lt hp hi)
  -- `fE1 ; fE2 ; frL`: the free flags
  obtain ⟨c₉, t₉, e₉, ht₉, i89, i98, i99, i88, f₉, m₉, rr₉, rm₉, o₉⟩ :=
    fE1_exec (P := P) c₈ e₈.wb_right
      (by rw [r88₈, K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), a81]; clear * - w hA; omega) (by clear * - w hA; omega)
      (by rw [K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), a80]; clear * - w hA; omega)
      (by rw [K8 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), a80, a81]; clear * - w hA; omega)
      (by rw [K8 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), a80, a81]; clear * - w hA; omega)
      (by rw [K8 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), a80, a81]; clear * - w hA; omega)
      (by rw [K8 _ (by decide) (by decide) (by decide) (by decide) (by decide),
        K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), a80, a81]; clear * - w hA; omega)
  simp only [r88₈, K8 9180 (by decide) (by decide) (by decide) (by decide) (by decide), K8 9181 (by decide) (by decide) (by decide) (by decide) (by decide), a80, a81] at i89 i98 i88
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, j89, j90, j91, f₁₀, m₁₀, rr₁₀, rm₁₀, o₁₀⟩ :=
    fE2_exec (P := P) c₉ e₉.wb_right
  have r85₉ : c₉.nreg 9185 = kfr := by
    rw [f₉ _ (by decide) (by decide) (by decide) (by decide), K8 _ (by decide) (by decide)
      (by decide) (by decide) (by decide), q₁ _ (by decide) (by decide) (by decide) (by decide),
      r85]
  rw [i98] at j89; rw [i89] at j90; rw [r85₉] at j91
  have kr₁₀ : ∀ i < m, c₁₀.nmem (d + 4 + m + m + m + m + i) = c.nmem (d + 4 + 4 * m + i) :=
    fun i hi => by
      rw [m₁₀, m₉, k₈ _ (by clear * - hi hA; omega), m₇, k₆ _ (by clear * - hi hA; omega), m₅,
        k₄ _ (by clear * - hi hA; omega), m₃, mem₂ _ (by clear * - hi hA; omega)]
      try (congr 1; clear * -; omega)
  obtain ⟨c₁₁, t₁₁, e₁₁, ht₁₁, v₁₁, k₁₁, f₁₁, rr₁₁, rm₁₁, o₁₁⟩ := frL_exec (P := P) c₁₀
    e₁₀.wb_right (n := m) (by rw [f₁₀ _ (by decide) (by decide) (by decide)]; exact i88) j89 j90 j91
    (Or.inl (by clear * - hA; omega)) (by clear * - w hA; omega) (by clear * - w hA; omega)
    (by clear * - w hA; omega)
  -- the end
  have K11 : ∀ x, 9180 ≤ x → x ≤ 9189 → c₁₁.nreg x = c₉.nreg x := fun x h1 h2 => by
    rw [f₁₁ x (by clear * - h1 h2; omega), f₁₀ x (by clear * - h1 h2; omega)
      (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)]
  have K9 : ∀ x, 9180 ≤ x → x ≤ 9188 → c₉.nreg x = c₈.nreg x := fun x h1 h2 =>
    f₉ x (by clear * - h2; omega) (by clear * - h2; omega) (by clear * - h2; omega)
      (by clear * - h2; omega)
  have hR : FcR c₁₁ d b m Z kfr :=
    ⟨by rw [K11 _ (by decide) (by decide), K9 _ (by decide) (by decide),
        K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), a80],
      by rw [K11 _ (by decide) (by decide), K9 _ (by decide) (by decide),
        K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), a81],
      by rw [K11 _ (by decide) (by decide), K9 _ (by decide) (by decide),
        K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), a82],
      by rw [K11 _ (by decide) (by decide), K9 _ (by decide) (by decide),
        K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), a83],
      by rw [K11 _ (by decide) (by decide), K9 _ (by decide) (by decide),
        K8 _ (by decide) (by decide) (by decide) (by decide) (by decide), a84],
      by rw [K11 _ (by decide) (by decide)]; exact r85₉,
      by rw [K11 _ (by decide) (by decide), K9 _ (by decide) (by decide), r86₈]; clear * -; omega,
      by rw [K11 _ (by decide) (by decide), K9 _ (by decide) (by decide), r87₈]; clear * -; omega,
      by rw [K11 _ (by decide) (by decide), K9 _ (by decide) (by decide), r88₈]; clear * -; omega,
      by rw [K11 _ (by decide) (by decide), i89]; clear * -; omega⟩
  have mem₁₁ : ∀ a, (a < b ∨ b + 7 * m ≤ a) → c₁₁.nmem a = c.nmem a := fun a ha => by
    rw [k₁₁ a (by clear * - ha; omega), m₁₀, m₉, k₈ a (by clear * - ha; omega), m₇,
      k₆ a (by clear * - ha; omega), m₅, k₄ a (by clear * - ha; omega), m₃,
      mem₂ a (by clear * - ha; omega)]
  refine ⟨c₁₁, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + (t₈ + (t₉ + (t₁₀ + t₁₁))))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ (.seq e₉
      (.seq e₁₀ e₁₁))))))))),
    by clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇ ht₈ ht₉ ht₁₀ ht₁₁; omega, hR, ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, mem₁₁,
    by rw [rr₁₁, rr₁₀, rr₉, rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₁₁, rm₁₀, rm₉, rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₁₁, o₁₀, o₉, o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [f₁₁ _ (by decide), f₁₀ _ (by decide) (by decide) (by decide),
      f₉ _ (by decide) (by decide) (by decide) (by decide), f₈ _ (by decide),
      f₇ _ (by decide) (by decide) (by decide) (by decide) (by decide), f₆ _ (by decide),
      f₅ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      f₄ _ (by decide), f₃ _ (by decide) (by decide) (by decide) (by decide),
      f₂ _ (by decide) (by decide) (by decide), q₁ _ (by decide) (by decide) (by decide)
        (by decide), r3004]
  · rw [k₁₁ _ (by clear * - hi; omega), m₁₀, m₉, k₈ _ (by clear * - hi; omega), m₇,
      k₆ _ (by clear * - hi; omega), m₅, show b + 3 * m + i = b + m + m + m + i by clear * -; omega]
    exact vl₄ i hi
  · rw [k₁₁ _ (by clear * - hi; omega), m₁₀, m₉,
      show b + 5 * m + i = b + m + m + m + m + m + i by clear * -; omega]
    exact dva₈ i hi
  · rw [show b + 6 * m + i = b + m + m + m + m + m + m + i by clear * -; omega, v₁₁ i hi,
      kr₁₀ i hi]

end Exec

end BKMNW

end PlanarFlow
