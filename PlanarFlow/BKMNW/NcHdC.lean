module

public import PlanarFlow.BKMNW.NcHd
public import PlanarFlow.BKMNW.NcScanM

/-!
# The head of `c2sP`, stage D: the capacities, the excesses, the deleted vertices

* **`hdSc_exec`**: `scGl ; scP ; dfGl ; dfL` writes `CAP = (c2sCap U g C).toNat`,
  `BT = (c2sBeta U g C ∘ tail).toNat`, `DF = [tail ∈ delSet U g C]` at `b + 16m + 9`,
  `b + 17m + 9`, `b + 18m + 9`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall OrbLab Relation NegSSSP WordRAM
  WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

universe w

variable {P : Input} {W : ℕ} {Z : ℕ}

set_option maxHeartbeats 2000000 in
/-- **Stage D: the capacities `c2sCap`, the excesses `c2sBeta` and the flags of `delSet`.** -/
theorem hdSc_exec {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
    [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'} {en' : ℕ → D'} {m b d CPb : ℕ}
    (c : Config) (hc : WordsBounded W c) {U g : D' → ℤ} {C : Finset V'}
    (hIn : ScIn M' en' m c.nmem (b + 5 * m + 1) (b + 14 * m + 5) (d + 4 + m) CPb (d + 4 + 6 * m)
      (b + m) (b + 2 * m) (b + 3 * m) Z U g C)
    (hCPZ : ∀ i < m, c.nmem (CPb + i) ≤ Z) (hDG : ∀ v < m, c.nmem (b + 3 * m + v) ≤ m)
    (hLAB : ∀ i < m, c.nmem (b + m + i) ≤ m)
    (r32 : c.nreg 9832 = m) (r33 : c.nreg 9833 = Z) (r30 : c.nreg 9830 = CPb)
    (r39 : c.nreg 9839 = b + 5 * m + 1) (r41 : c.nreg 9841 = b + 14 * m + 5)
    (r74 : c.nreg 9874 = d + 4 + m) (r76 : c.nreg 9876 = d + 4 + 6 * m)
    (r35 : c.nreg 9835 = b + m) (r36 : c.nreg 9836 = b + 2 * m) (r37 : c.nreg 9837 = b + 3 * m)
    (r42 : c.nreg 9842 = b + 16 * m + 9) (r43 : c.nreg 9843 = b + 17 * m + 9)
    (r44 : c.nreg 9844 = b + 18 * m + 9)
    (hb : d + 4 + 7 * m ≤ b) (hCPl : CPb + m ≤ b + 16 * m + 9)
    (w : b + 19 * m + 9 + 1 ≤ W) (wZ : 2 * Z ≤ W) (wmZ : m * Z ≤ W) :
    ∃ c' k, Exec P W (.seq (.seq scGl scP) (.seq dfGl dfL)) c c' k ∧
      k ≤ 12 + (40 * m + 4) + (5 + (11 * m + 4)) ∧
      (∀ i < m, c'.nmem (b + 16 * m + 9 + i) = (c2sCap M' U g C (en' i)).toNat) ∧
      (∀ i < m, c'.nmem (b + 17 * m + 9 + i) = (c2sBeta M' U g C (M'.tail (en' i))).toNat) ∧
      (∀ i < m, c'.nmem (b + 18 * m + 9 + i) =
        if M'.tail (en' i) ∈ delSet M' U g C then 1 else 0) ∧
      (∀ a, (a < b + 16 * m + 9 ∨ b + 19 * m + 9 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ (9732 ≤ r ∧ r ≤ 9743) → ¬ ScScr r → ¬ (9792 ≤ r ∧ r ≤ 9796) → ¬ ArScr r →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hcf1 : ∀ i < m, c.nmem (b + 5 * m + 1 + i) ≤ 1 := fun i hi => by
    rw [hIn.cf i hi]; split_ifs <;> omega
  have hmk1 : ∀ i < m, c.nmem (b + 14 * m + 5 + i) ≤ 1 := fun i hi => (hIn.rb i hi).1
  obtain ⟨c₁, k₁, e₁, hk₁, a32, a33, a34, a35, a36, a37, a38, a39, a40, a41, a42, a43, f₁, m₁, rr₁,
    rm₁, o₁⟩ := scGl_exec (P := P) c hc
  rw [r39] at a32; rw [r41] at a33; rw [r74] at a34; rw [r30] at a35; rw [r76] at a36
  rw [r35] at a37; rw [r36] at a38; rw [r37] at a39; rw [r42] at a40; rw [r43] at a41
  rw [r33] at a42; rw [r32] at a43
  obtain ⟨c₂, k₂, e₂, hk₂, v₂, b₂, f₂, g₂, rr₂, rm₂, o₂⟩ := scP_exec (P := P) c₁ e₁.wb_right
    a32 a33 a34 a35 a36 a37 a38 a39 a40 a41 a42 a43
    (fun i hi => by rw [m₁]; exact hcf1 i hi) (fun i hi => by rw [m₁]; exact hmk1 i hi)
    (fun i hi => by rw [m₁]; exact (hIn.rv i hi).1)
    (fun i hi => by rw [m₁]; exact ⟨(hIn.dv i hi).1, hLAB i hi⟩)
    (fun i hi => by rw [m₁]; have := hCPZ i hi; omega)
    (fun v hv => by rw [m₁]; have := Nat.mul_le_mul_right Z (hDG v hv); omega)
    (by omega) (by omega) (by omega) hCPl (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  rw [m₁] at v₂ b₂
  have mem₂ : ∀ a, (a < b + 16 * m + 9 ∨ b + 18 * m + 9 ≤ a) → c₂.nmem a = c.nmem a :=
    fun a ha => by rw [f₂ a (by omega), m₁]
  obtain ⟨c₃, k₃, e₃, hk₃, a92, a93, a94, a95, a96, f₃, m₃, rr₃, rm₃, o₃⟩ :=
    dfGl_exec (P := P) c₂ e₂.wb_right
  have q : ∀ r, 9830 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [g₂ r (by unfold ScScr; omega), f₁ r (by omega)]
  rw [q _ (by omega), r39] at a92; rw [q _ (by omega), r41] at a93
  rw [q _ (by omega), r44] at a94; rw [q _ (by omega), r32] at a96
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, f₄, g₄, rr₄, rm₄, o₄⟩ := dfL_exec (P := P) c₃ e₃.wb_right
    (m := m) (Xb := b + 5 * m + 1) (Yb := b + 14 * m + 5) (Ob := b + 18 * m + 9) (K := 0)
    ⟨a92, a93, a94, a95, a96, by omega, by omega, by omega, by omega,
      fun t ht j hj => by omega, fun t ht j hj => by omega⟩
    (fun t ht => by
      rw [m₃, mem₂ _ (by omega), mem₂ _ (by omega)]
      have := Nat.mul_le_mul (hcf1 t ht) (hmk1 t ht); omega)
  refine ⟨c₄, k₁ + k₂ + (k₃ + k₄), (e₁.seq e₂).seq (e₃.seq e₄), by omega, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_, ?_, ?_, ?_⟩
  · rw [f₄ _ (by omega), m₃, v₂ i hi, scCap_eq hIn hi]
  · rw [f₄ _ (by omega), m₃, b₂ i hi, scBt_eq hIn hi]
  · rw [v₄ i hi, m₃, mem₂ _ (by omega), mem₂ _ (by omega)]
    exact scDF_eq hIn hi
  · rw [f₄ _ (by omega), m₃, f₂ a (by omega), m₁]
  · rw [g₄ r h4, f₃ r h3, g₂ r h2, f₁ r h1]
  · rw [rr₄, rr₃, rr₂, rr₁]
  · rw [rm₄, rm₃, rm₂, rm₁]
  · rw [o₄, o₃, o₂, o₁]

end NcStep

end BKMNW

end PlanarFlow
