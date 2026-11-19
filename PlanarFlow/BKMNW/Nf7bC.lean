module

public import PlanarFlow.BKMNW.Nf7bB
public import PlanarFlow.BKMNW.NfEl
public import PlanarFlow.BKMNW.NfSwP

/-!
# The stage loop of `fixP`, part C: bounds of the words of a stage

* **`SW.wbnd`**: with the flows `≤ B` in absolute value, the prices in `[0, B]`, the capacities
  in `[0, B]`, `|f₀| ≤ B`, `|div f₀| ≤ B`: `|cob| ≤ B`, `|f1| ≤ 2B`, `|bv| ≤ 6B`,
  `0 ≤ val0 ≤ 2B`, `|f2| ≤ 4B`, `0 ≤ |bv| − val0 ≤ 6B`;
* **`SW.elD_bnd`**, **`SW.elR_bnd`**: the lengths of the explicit arcs are `≤ 7B` in absolute
  value (`0 ≤ Mb ≤ B`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace SW

variable (w : SW)

theorem wbnd {B : ℤ} (hF : ∀ l, |w.Fw l| ≤ B) (hP : ∀ x, 0 ≤ w.Pw x ∧ w.Pw x ≤ B)
    (hcw : 0 ≤ w.cw w.i ∧ w.cw w.i ≤ B) (hcr : 0 ≤ w.cr w.i ∧ w.cr w.i ≤ B)
    (hf0 : ∀ l, |w.f0w l| ≤ B) (hdv : |w.dv| ≤ B) :
    |w.cob| ≤ B ∧ |w.f1| ≤ 2 * B ∧ |w.bv| ≤ 6 * B ∧ 0 ≤ w.val0 ∧ w.val0 ≤ 2 * B ∧
      |w.f2| ≤ 4 * B ∧ 0 ≤ |w.bv| - w.val0 ∧ |w.bv| - w.val0 ≤ 6 * B := by
  have p1 := hP (w.ia w.i); have p2 := hP (w.ib w.i)
  have hc : |w.cob| ≤ B := by unfold cob; rw [abs_le]; constructor <;> linarith
  have hF0 := hF w.i
  rw [abs_le] at hc hF0
  have hf1 : |w.f1| ≤ 2 * B := by
    unfold f1; rw [abs_le]
    constructor
    · have := le_max_right (min (w.Fw w.i + w.cob) (w.cw w.i)) (-w.cr w.i); linarith
    · have : max (min (w.Fw w.i + w.cob) (w.cw w.i)) (-w.cr w.i) ≤ B :=
        max_le ((min_le_right _ _).trans hcw.2) (by linarith)
      linarith
  have hb : |w.bv| ≤ 6 * B := by
    have h1 := hf0 w.i; have h2 := hf0 (w.i - 1); have h3 := hF (w.i - 1)
    rw [abs_le] at hf1 h1 h2 h3 hdv ⊢
    unfold bv
    split_ifs <;> constructor <;> linarith
  have hclamp : -w.cr w.i ≤ max (min (w.Fw w.i + w.cob) (w.cw w.i)) (-w.cr w.i) ∧
      max (min (w.Fw w.i + w.cob) (w.cw w.i)) (-w.cr w.i) ≤ w.cw w.i :=
    ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩
  have hres : 0 ≤ w.res ∧ w.res ≤ 2 * B := by
    have e : w.f1 + w.cob = max (min (w.Fw w.i + w.cob) (w.cw w.i)) (-w.cr w.i) := by
      unfold f1; ring
    unfold res
    split_ifs <;> constructor <;> linarith
  have habs := abs_nonneg w.bv
  have hv : 0 ≤ w.val0 ∧ w.val0 ≤ 2 * B ∧ w.val0 ≤ |w.bv| := by
    unfold val0
    exact ⟨le_min hres.1 habs, (min_le_left _ _).trans hres.2, min_le_right _ _⟩
  have hf2 : |w.f2| ≤ 4 * B := by
    rw [abs_le] at hf1 ⊢
    unfold f2; split_ifs <;> constructor <;> linarith
  refine ⟨by rw [abs_le]; exact hc, hf1, hb, hv.1, hv.2.1, hf2, by linarith, by linarith⟩

theorem elD_bnd {B Mb : ℤ} {cw : ℕ → ℤ} (hF : ∀ l, |w.Fw l| ≤ B)
    (hP : ∀ x, 0 ≤ w.Pw x ∧ w.Pw x ≤ B) (hcw : 0 ≤ w.cw w.i ∧ w.cw w.i ≤ B)
    (hcr : 0 ≤ w.cr w.i ∧ w.cr w.i ≤ B) (hf0 : ∀ l, |w.f0w l| ≤ B) (hdv : |w.dv| ≤ B)
    (hMb : 0 ≤ Mb ∧ Mb ≤ B) (l : ℕ) (hc : 0 ≤ cw l ∧ cw l ≤ B) : |w.elD Mb cw l| ≤ 7 * B := by
  obtain ⟨h1, -, -, -, -, h6, h7, h8⟩ := w.wbnd hF hP hcw hcr hf0 hdv
  have h9 := hF l
  rw [abs_le] at h1 h6 h9 ⊢
  unfold elD
  split_ifs <;> constructor <;> linarith

theorem elR_bnd {B Mb : ℤ} {cr : ℕ → ℤ} (hF : ∀ l, |w.Fw l| ≤ B)
    (hP : ∀ x, 0 ≤ w.Pw x ∧ w.Pw x ≤ B) (hcw : 0 ≤ w.cw w.i ∧ w.cw w.i ≤ B)
    (hcr : 0 ≤ w.cr w.i ∧ w.cr w.i ≤ B) (hf0 : ∀ l, |w.f0w l| ≤ B) (hdv : |w.dv| ≤ B)
    (hMb : 0 ≤ Mb ∧ Mb ≤ B) (l : ℕ) (hc : 0 ≤ cr l ∧ cr l ≤ B) : |w.elR Mb cr l| ≤ 7 * B := by
  obtain ⟨h1, -, -, -, -, h6, h7, h8⟩ := w.wbnd hF hP hcw hcr hf0 hdv
  have h9 := hF l
  rw [abs_le] at h1 h6 h9 ⊢
  unfold elR
  split_ifs <;> constructor <;> linarith

end SW

end BKMNW

end PlanarFlow
