module

public import PlanarFlow.BKMNW.NcScanRun
public import PlanarFlow.BKMNW.NcMath

/-!
# The words of the scan are the capacities and excesses of `c2sG`

On any map `M` with darts numbered by `en` (`i < m`), from the source flags
`CF[j] = [tail ∈ C]`, reach bits `MK[j] ≤ 1` with `MK[j] = 1 ∧ tail ∈ C ↔ tail ∈ C⁺`
(`rb_fwdReach`), the reversals `en (RV[i]) = rev (en i)`, the flow `FL[i] = Z + g (en i)`, the
capacities `CP[i] = U (en i)` with `g ≤ U`, and the labelled net outflows
`DV[l] - Z · DG[l] = div g (tail (en i))` (`LAB[i] = l + 1`, `dvP_div`):

* `scDF_eq` (`[tail ∈ delSet]`);
* **`scCap_eq`**: `scCap … i = (c2sCap M U g C (en i)).toNat` (`c2sCap ≥ 0`);
* **`scBt_eq`**: `scBt … i = (c2sBeta M U g C (tail (en i))).toNat`, and `c2sBeta ≥ 0` on a
  pseudoflow under the precondition `hpre` of `c2sG_spec` (`c2sBeta_nonneg`), so the words are
  the exact values.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

/-- The hypotheses of the scan at a dart (see the module docstring). -/
structure ScIn (M : CombMap D V F) (en : ℕ → D) (m : ℕ) (mem : ℕ → ℕ)
    (CFb MKb RVb CPb FLb LABb DVb DGb Z : ℕ) (U g : D → ℤ) (C : Finset V) : Prop where
  cf : ∀ j < m, mem (CFb + j) = if M.tail (en j) ∈ C then 1 else 0
  rb : ∀ j < m, mem (MKb + j) ≤ 1 ∧
    (mem (MKb + j) = 1 ∧ M.tail (en j) ∈ C ↔ M.tail (en j) ∈ fwdReach M U g (posSet M g C) C)
  rv : ∀ j < m, mem (RVb + j) < m ∧ en (mem (RVb + j)) = M.rev (en j)
  fl : ∀ j < m, (mem (FLb + j) : ℤ) = Z + g (en j)
  cp : ∀ j < m, (mem (CPb + j) : ℤ) = U (en j)
  le : ∀ j < m, g (en j) ≤ U (en j)
  dv : ∀ j < m, 1 ≤ mem (LABb + j) ∧
    (mem (DVb + (mem (LABb + j) - 1)) : ℤ) - Z * mem (DGb + (mem (LABb + j) - 1)) =
      M.div g (M.tail (en j))

lemma ScIn.cpl {mem : ℕ → ℕ} {CFb MKb RVb CPb FLb LABb DVb DGb Z : ℕ} {U g : D → ℤ}
    {C : Finset V} (h : ScIn M en m mem CFb MKb RVb CPb FLb LABb DVb DGb Z U g C) {j : ℕ}
    (hj : j < m) :
    mem (CFb + j) * mem (MKb + j) =
      if M.tail (en j) ∈ fwdReach M U g (posSet M g C) C then 1 else 0 := by
  classical
  rw [h.cf j hj]
  obtain ⟨hle, hiff⟩ := h.rb j hj
  by_cases hC : M.tail (en j) ∈ C
  · rw [iteT hC, one_mul]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h0 | h1
    · rw [h0, iteF (fun hr => by have := (hiff.2 hr).1; omega)]
    · rw [h1, iteT (hiff.1 ⟨h1, hC⟩)]
  · rw [iteF hC, zero_mul, iteF (fun hr => hC (fwdReach_subset hr))]

/-- The flag `[tail ∈ delSet]`. -/
lemma scDF_eq {mem : ℕ → ℕ} {CFb MKb RVb CPb FLb LABb DVb DGb Z : ℕ} {U g : D → ℤ}
    {C : Finset V} (h : ScIn M en m mem CFb MKb RVb CPb FLb LABb DVb DGb Z U g C) {j : ℕ}
    (hj : j < m) :
    scDF mem CFb MKb j = if M.tail (en j) ∈ delSet M U g C then 1 else 0 := by
  classical
  unfold scDF
  rw [h.cpl hj, h.cf j hj]
  have e : M.tail (en j) ∈ delSet M U g C ↔
      M.tail (en j) ∈ C ∧ M.tail (en j) ∉ fwdReach M U g (posSet M g C) C := by
    simp [delSet, mem_sdiff]
  by_cases hC : M.tail (en j) ∈ C
  · by_cases hR : M.tail (en j) ∈ fwdReach M U g (posSet M g C) C
    · rw [iteT hC, iteT hR, iteF (fun hd => (e.1 hd).2 hR)]
    · rw [iteT hC, iteF hR, iteT (e.2 ⟨hC, hR⟩)]
  · rw [iteF hC, iteF (fun hd => hC (e.1 hd).1)]
    by_cases hR : M.tail (en j) ∈ fwdReach M U g (posSet M g C) C
    · exact absurd (fwdReach_subset hR) hC
    · rw [iteF hR]

/-- **The capacity words are the capacities `c2sCap`.** -/
theorem scCap_eq {mem : ℕ → ℕ} {CFb MKb RVb CPb FLb LABb DVb DGb Z : ℕ} {U g : D → ℤ}
    {C : Finset V} (h : ScIn M en m mem CFb MKb RVb CPb FLb LABb DVb DGb Z U g C) {i : ℕ}
    (hi : i < m) :
    scCap mem CFb MKb RVb CPb FLb Z i = (c2sCap M U g C (en i)).toNat := by
  classical
  obtain ⟨hr, hre⟩ := h.rv i hi
  unfold scCap
  rw [scDF_eq h hi, scDF_eq h hr, hre, M.tail_rev]
  have hfl := h.fl i hi
  have hcp := h.cp i hi
  have hle := h.le i hi
  have e2 : mem (CPb + i) + Z - mem (FLb + i) = (U (en i) - g (en i)).toNat := by omega
  rw [e2]
  unfold c2sCap
  have hinc : en i ∈ incSet M (delSet M U g C) ↔
      M.tail (en i) ∈ delSet M U g C ∨ M.head (en i) ∈ delSet M U g C := by simp [incSet]
  by_cases h1 : M.tail (en i) ∈ delSet M U g C
  · rw [iteT h1, iteT (hinc.2 (Or.inl h1))]; simp
  · by_cases h2 : M.head (en i) ∈ delSet M U g C
    · rw [iteF h1, iteT h2, iteT (hinc.2 (Or.inr h2))]; simp
    · rw [iteF h1, iteF h2, iteF (fun hh => (hinc.1 hh).elim h1 h2)]; simp

/-- **The excess words are the excesses `c2sBeta`.** -/
theorem scBt_eq {mem : ℕ → ℕ} {CFb MKb RVb CPb FLb LABb DVb DGb Z : ℕ} {U g : D → ℤ}
    {C : Finset V} (h : ScIn M en m mem CFb MKb RVb CPb FLb LABb DVb DGb Z U g C) {i : ℕ}
    (hi : i < m) :
    scBt mem CFb MKb LABb DVb DGb Z i = (c2sBeta M U g C (M.tail (en i))).toNat := by
  classical
  unfold scBt
  rw [h.cpl hi]
  obtain ⟨-, hdv⟩ := h.dv i hi
  unfold c2sBeta
  by_cases hR : M.tail (en i) ∈ fwdReach M U g (posSet M g C) C
  · rw [iteT hR, iteT hR, one_mul]
    have e : ((mem (DGb + (mem (LABb + i) - 1)) * Z : ℕ) : ℤ) =
        (Z : ℤ) * mem (DGb + (mem (LABb + i) - 1)) := by push_cast; ring
    omega
  · rw [iteF hR, iteF hR, zero_mul]; rfl

/-- The excess `c2sBeta` is nonnegative under the precondition of `c2sG_spec`. -/
lemma c2sBeta_nonneg {U g : D → ℤ} {C : Finset V}
    (hpre : ∀ v ∈ fwdReach M U g (posSet M g C) C, M.div g v ≤ 0) (v : V) :
    0 ≤ c2sBeta M U g C v := by
  classical
  unfold c2sBeta
  split_ifs with h
  · have := hpre v h; omega
  · exact le_rfl

end NcStep

end BKMNW

end PlanarFlow
