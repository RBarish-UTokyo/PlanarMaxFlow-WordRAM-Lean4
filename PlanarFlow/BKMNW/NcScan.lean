module

public import PlanarFlow.BKMNW.NcTfRun

/-!
# The capacity and excess scan of `c2sP`

After `rbP` (`MK[i]`, the reach bit of the dart `i`) and the source flags `CF[i] = [tail ∈ C]`, one
scan over the darts writes, for `i < m` (`r = RV[i]`, `l = LAB[i] - 1`):

* `CAP[i] := (1 ∸ DF i ∸ DF r) · (CP[i] + Z ∸ FL[i])`, `DF j = CF[j] ∸ CF[j] · MK[j]`
  (the residual capacity `U - g` off the darts touching `C ∖ C⁺`: `c2sCap`);
* `BT[i] := CF[i] · MK[i] · (DG[l] · Z ∸ DV[l])` (minus the net outflow at the tail when it is in
  `C⁺`: `c2sBeta`).

**`scP_exec`** (natural words; registers `9730 … 9743` inputs, `9744 … 9756` scratch): within
`41 m + 2` steps the two arrays hold `scCap`/`scBt` of the input memory; memory changed only in
`[CAPb, CAPb + m) ∪ [BTb, BTb + m)`. The values are identified with `c2sCap`/`c2sBeta` in
`NcScanM.lean`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

variable {P : Input} {W : ℕ}

/-- The flag `[tail ∈ C ∖ C⁺]` of the dart `j`. -/
def scDF (mem : ℕ → ℕ) (CFb MKb j : ℕ) : ℕ := mem (CFb + j) - mem (CFb + j) * mem (MKb + j)

/-- The capacity word of the dart `i`. -/
def scCap (mem : ℕ → ℕ) (CFb MKb RVb CPb FLb Z i : ℕ) : ℕ :=
  (1 - scDF mem CFb MKb i - scDF mem CFb MKb (mem (RVb + i))) * (mem (CPb + i) + Z - mem (FLb + i))

/-- The excess word of the dart `i`. -/
def scBt (mem : ℕ → ℕ) (CFb MKb LABb DVb DGb Z i : ℕ) : ℕ :=
  mem (CFb + i) * mem (MKb + i) *
    (mem (DGb + (mem (LABb + i) - 1)) * Z - mem (DVb + (mem (LABb + i) - 1)))

/-- One dart of the scan. -/
def scB : Stmt :=
  block [.addN 9744 9732 9730, .loadN 9744 9744, .addN 9745 9733 9730, .loadN 9745 9745,
    .mulN 9746 9744 9745, .subN 9747 9744 9746,
    .addN 9748 9734 9730, .loadN 9748 9748, .addN 9749 9732 9748, .loadN 9749 9749,
    .addN 9750 9733 9748, .loadN 9750 9750, .mulN 9750 9749 9750, .subN 9749 9749 9750,
    .subN 9751 9731 9747, .subN 9751 9751 9749,
    .addN 9752 9735 9730, .loadN 9752 9752, .addN 9752 9752 9742,
    .addN 9753 9736 9730, .loadN 9753 9753, .subN 9752 9752 9753, .mulN 9752 9751 9752,
    .addN 9753 9740 9730, .storeN 9753 9752,
    .addN 9754 9737 9730, .loadN 9754 9754, .subN 9754 9754 9731,
    .addN 9755 9739 9754, .loadN 9755 9755, .mulN 9755 9755 9742,
    .addN 9756 9738 9754, .loadN 9756 9756, .subN 9755 9755 9756, .mulN 9755 9746 9755,
    .addN 9756 9741 9730, .storeN 9756 9755, .addN 9730 9730 9731]

/-- **The scan**: `r9730 := 0; r9731 := 1; while r9730 < r9743 do scB`. -/
def scP : Stmt := .seq (block [.constN 9730 0, .constN 9731 1]) (.whileLtN 9730 9743 scB)

/-- The registers written by `scP`. -/
def ScScr (r : ℕ) : Prop := (r = 9730 ∨ r = 9731) ∨ (9744 ≤ r ∧ r ≤ 9756)

lemma mul_le_of_le_one {a b : ℕ} (h : a ≤ 1) : a * b ≤ b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with rfl | rfl <;> simp

set_option maxHeartbeats 1600000 in
theorem scB_exec (c : Config) (hc : WordsBounded W c) {CFb MKb RVb CPb FLb LABb DVb DGb CAPb BTb
    Z i : ℕ}
    (r30 : c.nreg 9730 = i) (r31 : c.nreg 9731 = 1) (r32 : c.nreg 9732 = CFb)
    (r33 : c.nreg 9733 = MKb) (r34 : c.nreg 9734 = RVb) (r35 : c.nreg 9735 = CPb)
    (r36 : c.nreg 9736 = FLb) (r37 : c.nreg 9737 = LABb) (r38 : c.nreg 9738 = DVb)
    (r39 : c.nreg 9739 = DGb) (r40 : c.nreg 9740 = CAPb) (r41 : c.nreg 9741 = BTb)
    (r42 : c.nreg 9742 = Z)
    (hcf : c.nmem (CFb + i) ≤ 1) (hmk : c.nmem (MKb + i) ≤ 1)
    (hcf' : c.nmem (CFb + c.nmem (RVb + i)) ≤ 1) (hmk' : c.nmem (MKb + c.nmem (RVb + i)) ≤ 1)
    (a1 : CFb + i ≤ W) (a2 : MKb + i ≤ W) (a3 : RVb + i ≤ W)
    (a4 : CFb + c.nmem (RVb + i) ≤ W) (a5 : MKb + c.nmem (RVb + i) ≤ W)
    (a6 : CPb + i ≤ W) (a7 : FLb + i ≤ W) (a8 : CAPb + i ≤ W) (a9 : LABb + i ≤ W)
    (a10 : DGb + (c.nmem (LABb + i) - 1) ≤ W) (a11 : DVb + (c.nmem (LABb + i) - 1) ≤ W)
    (a12 : BTb + i ≤ W) (a13 : i + 1 ≤ W)
    (v1 : c.nmem (CPb + i) + Z ≤ W)
    (v2 : c.nmem (DGb + (c.nmem (LABb + i) - 1)) * Z ≤ W)
    (d1 : CAPb + i ≠ LABb + i) (d2 : CAPb + i ≠ DGb + (c.nmem (LABb + i) - 1))
    (d3 : CAPb + i ≠ DVb + (c.nmem (LABb + i) - 1)) :
    ∃ c' k, Exec P W scB c c' k ∧ k = 38 ∧
      c'.nmem = upd (upd c.nmem (CAPb + i) (scCap c.nmem CFb MKb RVb CPb FLb Z i)) (BTb + i)
        (scBt c.nmem CFb MKb LABb DVb DGb Z i) ∧ c'.nreg 9730 = i + 1 ∧
      (∀ r, r ≠ 9730 → ¬ (9744 ≤ r ∧ r ≤ 9756) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have p1 : c.nmem (CFb + i) * c.nmem (MKb + i) ≤ 1 := by
    have := mul_le_of_le_one (b := c.nmem (MKb + i)) hcf; omega
  have p2 : c.nmem (CFb + c.nmem (RVb + i)) * c.nmem (MKb + c.nmem (RVb + i)) ≤ 1 := by
    have := mul_le_of_le_one (b := c.nmem (MKb + c.nmem (RVb + i))) hcf'; omega
  have p3 : ∀ x y : ℕ, (1 - x - y) * (c.nmem (CPb + i) + Z - c.nmem (FLb + i)) ≤ W := by
    intro x y
    have := mul_le_of_le_one (a := 1 - x - y)
      (b := c.nmem (CPb + i) + Z - c.nmem (FLb + i)) (by omega)
    omega
  have p4 : c.nmem (CFb + i) * c.nmem (MKb + i) *
      (c.nmem (DGb + (c.nmem (LABb + i) - 1)) * Z - c.nmem (DVb + (c.nmem (LABb + i) - 1))) ≤ W := by
    have := mul_le_of_le_one (b := c.nmem (DGb + (c.nmem (LABb + i) - 1)) * Z -
      c.nmem (DVb + (c.nmem (LABb + i) - 1))) p1
    omega
  unfold scB
  exec_block
  all_goals try ((try config_simp); (try simp only [r30, r31, r32, r33, r34, r35, r36, r37, r38,
    r39, r40, r41, r42, upd_apply]); (try split_ifs) <;> omega)
  all_goals try (simp only [Nat.le_eq] at *; config_simp; simp only [upd_apply, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41,
    r42, ↓reduceIte, Nat.reduceEqDiff]; omega)
  all_goals try (config_simp; simp only [r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40,
    r41, r42, upd_apply]; first | exact p3 _ _ | exact p4)
  refine ⟨rfl, ?_, ?_, fun r hr hr' => ?_, rfl, rfl, rfl⟩
  · have q1 : ∀ X, upd c.nmem (CAPb + i) X (LABb + i) = c.nmem (LABb + i) := fun X => by
      rw [upd_apply, iteF (Ne.symm d1)]
    have q2 : ∀ X, upd c.nmem (CAPb + i) X (DGb + (c.nmem (LABb + i) - 1)) =
        c.nmem (DGb + (c.nmem (LABb + i) - 1)) := fun X => by
      rw [upd_apply, iteF (Ne.symm d2)]
    have q3 : ∀ X, upd c.nmem (CAPb + i) X (DVb + (c.nmem (LABb + i) - 1)) =
        c.nmem (DVb + (c.nmem (LABb + i) - 1)) := fun X => by
      rw [upd_apply, iteF (Ne.symm d3)]
    config_simp
    simp only [r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42]
    simp only [q1]
    simp only [q2, q3]
    rfl
  · config_simp; simp only [r30, r31]
  · have h30 : ¬ r = 9730 := hr
    have h44 : ¬ r = 9744 := by omega
    have h45 : ¬ r = 9745 := by omega
    have h46 : ¬ r = 9746 := by omega
    have h47 : ¬ r = 9747 := by omega
    have h48 : ¬ r = 9748 := by omega
    have h49 : ¬ r = 9749 := by omega
    have h50 : ¬ r = 9750 := by omega
    have h51 : ¬ r = 9751 := by omega
    have h52 : ¬ r = 9752 := by omega
    have h53 : ¬ r = 9753 := by omega
    have h54 : ¬ r = 9754 := by omega
    have h55 : ¬ r = 9755 := by omega
    have h56 : ¬ r = 9756 := by omega
    config_simp
    simp only [upd_apply, h30, h44, h45, h46, h47, h48, h49, h50, h51, h52, h53, h54, h55,
      h56, ite_false]

end NcStep

end BKMNW

end PlanarFlow
