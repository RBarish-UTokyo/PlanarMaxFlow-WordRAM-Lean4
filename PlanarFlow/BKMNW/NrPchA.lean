module

public import PlanarFlow.BKMNW.NrPchA0

/-!
# `pchP`, phase A: the bases, the vertex labels and the net outflows

* **`PchR`**: the registers of `pchP` after its set-up (`r3004 = d`, `9200 = A`, `9201 = BT`,
  `9202 = FR`, `9203 = Kd`, `9204 = m`, `9205 = Z`, the frame's `RV`, `SG`, `FL` bases and the
  scratch bases `A + k m`); `PchR.congr`;
* `pG0 = (pG0a ; pG0b) ; (pG0c ; pG0d)`, **`pG0_exec`** (in `NrPchA0.lean`);
* **`pchA = pG0 ; dvP ; pG1 ; decL ; pG2 ; dvL`**, **`pchA_exec`**: within `68 m + 100` steps,
  `VL[i] = olab SG i` at `A + 3m`, `DV[v] = Kd + dvS … v - Z · dvC … v` at `A + 4m`, memory
  changed only in `[A, A + 5m)`.

Scratch layout of `pchP` (from `A`, `m` cells each unless stated): `LAB`, `DVs`, `DG` (`dvP`),
`VL` (`3m`), `DV` (`4m`), `NX` (`5m`), `FLB` (`6m`), `F0` (`7m`), `CR` (`8m`), `KY` (`9m`),
`NH` (`10m`), `ONE` (`11m`), `OB`, `OE`, `OL` (`12m … 15m`), `osProg`'s scratch (`15m`, `2m+1`
cells), `CRV` (`18m`), the scratch `R` of `nrPass`/`kahnP` (`19m`, `11m + 1` cells).
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

/-- **Phase A of `pchP`**: the bases, the vertex labels, the net outflows. -/
def pchA : Stmt := .seq pG0 (.seq dvP (.seq pG1 (.seq decL (.seq pG2 dvL))))

section Exec

variable {P : Input} {W : ℕ}

/-- **Phase A of `pchP`** (see the module docstring). -/
theorem pchA_exec (c : Config) (hc : WordsBounded W c) {d A m Kd Z : ℕ}
    (r3004 : c.nreg 3004 = d) (r00 : c.nreg 9200 = A) (r03 : c.nreg 9203 = Kd)
    (hm : c.nmem d = m) (hz : c.nmem (d + 3) = Z) (hp : PermOn (sgF d m c.nmem) m)
    (hA : d + 4 + 7 * m ≤ A) (w : A + 30 * m + 10 ≤ W)
    (hFL : ∑ j ∈ range m, c.nmem (d + 6 * m + 4 + j) ≤ 2 * m * Z)
    (wK : Kd + 2 * m * Z ≤ W) (wZ : Z * m ≤ W) :
    ∃ c' t, Exec P W pchA c c' t ∧ t ≤ 68 * m + 100 ∧
      PchR c' d A (c.nreg 9201) (c.nreg 9202) Kd m Z ∧
      (∀ i < m, c'.nmem (A + 3 * m + i) = olab (sgF d m c.nmem) i) ∧
      (∀ v < m, c'.nmem (A + 4 * m + v) =
        Kd + dvS (olab (sgF d m c.nmem)) (fun j => c.nmem (d + 6 * m + 4 + j)) m v -
          Z * dvC (olab (sgF d m c.nmem)) m v) ∧
      (∀ a, (a < A ∨ A + 5 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, R₁, a8430, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    pG0_exec (P := P) c hc r3004 r00 hm (by omega) hA
  simp only [hz, r03] at R₁
  -- `dvP`
  obtain ⟨c₂, t₂, e₂, ht₂, l₂, s₂, k₂, f₂, rr₂, rm₂, o₂⟩ := dvP_exec (P := P) c₁ e₁.wb_right
    (d := d) (A := A) (m := m) R₁.r3004 a8430 (by rw [m₁, hm]) (by rw [m₁]; exact hp) hA
    (by omega) (by omega) (by rw [m₁]; omega)
  have R₂ : PchR c₂ d A (c.nreg 9201) (c.nreg 9202) Kd m Z :=
    R₁.congr (fun x h1 h2 => f₂ x (by omega) (by omega) (by omega)) (f₂ _ (by omega) (by omega)
      (by omega))
  simp only [m₁] at l₂ s₂
  -- `pG1 ; decL`: `VL[i] = LAB[i] - 1`
  obtain ⟨c₃, t₃, e₃, ht₃, g41, g42, g43, f₃, m₃, rr₃, rm₃, o₃⟩ := pG1_exec (P := P) c₂ e₂.wb_right
  have R₃ := R₂.congr (fun x h1 h2 => f₃ x (by omega) (by omega) (by omega)) (f₃ _ (by omega)
    (by omega) (by omega))
  simp only [R₂.r04] at g41
  simp only [R₂.r00] at g42
  simp only [R₂.r10] at g43
  obtain ⟨c₄, t₄, e₄, ht₄, v₄, k₄, f₄, rr₄, rm₄, o₄⟩ := decL_exec (P := P) c₃ e₃.wb_right
    g41 g42 g43 (by omega) (by omega) (by omega) (by omega)
  have R₄ := R₃.congr (fun x h1 h2 => f₄ x (by omega)) (f₄ _ (by omega))
  -- `pG2 ; dvL`: `DV[v] = Kd + DVs[v] - Z · DG[v]`
  obtain ⟨c₅, t₅, e₅, ht₅, g61, g62, g63, g64, g65, g66, f₅, m₅, rr₅, rm₅, o₅⟩ :=
    pG2_exec (P := P) c₄ e₄.wb_right (by rw [R₄.r00, R₄.r04]; omega)
      (by rw [R₄.r00, R₄.r04]; omega)
  have R₅ := R₄.congr (fun x h1 h2 => f₅ x (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)) (f₅ _ (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega))
  simp only [R₄.r04] at g61
  simp only [R₄.r00, R₄.r04] at g62 g63
  simp only [R₄.r11] at g64
  simp only [R₄.r03] at g65
  simp only [R₄.r05] at g66
  have mem₄ : ∀ a, (a < A + 3 * m ∨ A + 4 * m ≤ a) → c₄.nmem a = c₂.nmem a := fun a ha => by
    rw [k₄ a (by omega), m₃]
  have hS : ∀ v < m, c₅.nmem (A + m + v) =
      dvS (olab (sgF d m c.nmem)) (fun j => c.nmem (d + 6 * m + 4 + j)) m v := fun v hv => by
    rw [m₅, mem₄ _ (by omega)]; exact (s₂ v hv).1
  have hG : ∀ v < m, c₅.nmem (A + m + m + v) = dvC (olab (sgF d m c.nmem)) m v := fun v hv => by
    rw [m₅, mem₄ _ (by omega)]; exact (s₂ v hv).2
  have hSle : ∀ v < m, dvS (olab (sgF d m c.nmem)) (fun j => c.nmem (d + 6 * m + 4 + j)) m v ≤
      2 * m * Z := fun v _ => (dvS_le _ _ _ _).trans hFL
  have hCle : ∀ v < m, dvC (olab (sgF d m c.nmem)) m v ≤ m := fun v _ => dvC_le _ _ _
  obtain ⟨c₆, t₆, e₆, ht₆, v₆, k₆, f₆, rr₆, rm₆, o₆⟩ := dvL_exec (P := P) c₅ e₅.wb_right
    g61 g62 g63 g64 g65 g66 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi => by rw [hS i hi]; have := hSle i hi; omega)
    (fun i hi => by
      rw [show A + m + m + i = A + m + m + i from rfl, hG i hi]
      calc Z * dvC (olab (sgF d m c.nmem)) m i ≤ Z * m := Nat.mul_le_mul_left _ (hCle i hi)
        _ ≤ W := wZ)
  have R₆ := R₅.congr (fun x h1 h2 => f₆ x (by omega)) (f₆ _ (by omega))
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), by omega, R₆, fun i hi => ?_,
    fun v hv => ?_, fun a ha => ?_, by rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁], by rw [o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [k₆ _ (by omega), m₅, v₄ i hi, m₃, l₂ i hi]; omega
  · rw [v₆ v hv, hS v hv, show A + m + m + v = A + m + m + v from rfl, hG v hv]
  · rw [k₆ _ (by omega), m₅, mem₄ _ (by omega), k₂ _ (by omega), m₁]

end Exec

end BKMNW

end PlanarFlow
