module

public import PlanarFlow.BKMNW.MsEncF

/-!
# The composed MSSP encoder, part G: the low memory of the start and the size bounds

* **`kmem_of`**: a memory holding the flags at `n + j`, the residues of the real words of `mkC0`
  at `β = B + 16 (n + 1) + 1`, the input words at `β' = kleinWN + 1` and zero elsewhere below
  `Wz` is the low memory `kMem` of the start, cell by cell;
* the size bounds of the call: `N1M`, `wM`, `HM`, `KM` (the maxima of `N₁`, `w`, `Hc`, `kleinWN`
  over the calls on `m` darts with lengths `≤ L`), monotonicity (`isoN1_mono`, `msHI_mono`,
  `dB_mono`, `kleinWN_mono`), **`wzm`** (the bound of the low memory), **`Rm`** (the scratch).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

/-- **The low memory of the start from its words.** -/
lemma kmem_of {D' : Type*} {nD n k B Hc Wz : ℕ} {fl : ℕ → Bool} {σ : D' ≃ Fin nD}
    {wt φ : D' → ℤ} {L Th H0 : ℤ} {Pin : Input} {mem : ℕ → ℕ}
    (hn : n + k ≤ B + 16 * (n + 1)) (h3n : 3 * nD + 3 ≤ B + 16 * (n + 1))
    (hfl : ∀ j < k, mem (n + j) = if fl j then 1 else 0)
    (hwt : ∀ d, 0 ≤ wt d ∧ wt d < 2 * Hc + 1 ∧
      mem (B + 16 * (n + 1) + 1 + σ d) = (wt d).toNat)
    (hph : ∀ d, 0 ≤ φ d ∧ φ d < 2 * Hc + 1 ∧
      mem (B + 16 * (n + 1) + 1 + nD + σ d) = (φ d).toNat)
    (hL : 0 ≤ L ∧ L < 2 * Hc + 1 ∧ mem (B + 16 * (n + 1) + 1 + 3 * nD) = L.toNat)
    (hTh : 0 ≤ Th ∧ Th < 2 * Hc + 1 ∧ mem (B + 16 * (n + 1) + 1 + 3 * nD + 1) = Th.toNat)
    (hH0 : 0 ≤ H0 ∧ H0 < 2 * Hc + 1 ∧ mem (B + 16 * (n + 1) + 1 + 3 * nD + 2) = H0.toNat)
    (hPin : ∀ i < Pin.data.length, mem (Klein.kleinWN B n Hc + 1 + i) = Pin.data.getD i 0)
    (hz : ∀ a ≤ Wz, (a < n ∨ (n + k ≤ a ∧ a ≤ B + 16 * (n + 1)) ∨
      (B + 16 * (n + 1) + 1 + 2 * nD ≤ a ∧ a < B + 16 * (n + 1) + 1 + 3 * nD) ∨
      (B + 16 * (n + 1) + 1 + 3 * nD + 3 ≤ a ∧ a ≤ Klein.kleinWN B n Hc) ∨
      Klein.kleinWN B n Hc + 1 + Pin.data.length ≤ a) → mem a = 0) :
    ∀ a ≤ Wz, mem a = MsCall.kMem B n Hc (mkC0 nD n k fl σ wt φ L Th H0) Pin a := by
  intro a ha
  have hKW : Klein.kleinWN B n Hc = 2 * (B + 16 * (n + 1)) + 1 + (2 * Hc + 1) * (2 * Hc + 1) +
      (2 * Hc + 1) := rfl
  rw [kMem_mkC0]
  by_cases h1 : a ≤ Klein.kleinWN B n Hc
  · simp only [h1, ↓reduceIte]
    by_cases h2 : a ≤ B + 16 * (n + 1)
    · simp only [h2, ↓reduceIte]
      by_cases h3 : n ≤ a ∧ a < n + k
      · simp only [h3, and_self, ↓reduceIte]
        have := hfl (a - n) (by omega)
        rwa [show n + (a - n) = a by omega] at this
      · simp only [h3, ↓reduceIte]
        exact hz a ha (by omega)
    · simp only [h2, ↓reduceIte]
      by_cases h3 : B + 16 * (n + 1) + 1 ≤ a ∧ a ≤ B + 16 * (n + 1) + 1 + (B + 16 * (n + 1))
      · simp only [h3, and_self, ↓reduceIte]
        set j := a - (B + 16 * (n + 1) + 1) with hj
        have ha' : a = B + 16 * (n + 1) + 1 + j := by omega
        simp only [mkC0]
        by_cases j1 : j < nD
        · simp only [j1, ↓reduceDIte]
          obtain ⟨g0, g1, g2⟩ := hwt (σ.symm ⟨j, j1⟩)
          rw [resW_nat g0 (by exact_mod_cast g1), ha']
          simpa using g2
        · simp only [j1, ↓reduceDIte]
          by_cases j2 : j < 2 * nD
          · simp only [j2, ↓reduceDIte]
            obtain ⟨g0, g1, g2⟩ := hph (σ.symm ⟨j - nD, by omega⟩)
            rw [resW_nat g0 (by exact_mod_cast g1)]
            simp only [Equiv.apply_symm_apply] at g2
            rw [show B + 16 * (n + 1) + 1 + nD + (j - nD) = a by omega] at g2
            exact g2
          · simp only [j2, ↓reduceDIte]
            by_cases j3 : j = 3 * nD
            · simp only [j3, ↓reduceIte]
              rw [resW_nat hL.1 (by exact_mod_cast hL.2.1), ha', j3]; exact hL.2.2
            · simp only [j3, ↓reduceIte]
              by_cases j4 : j = 3 * nD + 1
              · rw [if_pos j4, resW_nat hTh.1 (by exact_mod_cast hTh.2.1), ha', j4]; exact hTh.2.2
              · rw [if_neg j4]
                by_cases j5 : j = 3 * nD + 2
                · rw [if_pos j5, resW_nat hH0.1 (by exact_mod_cast hH0.2.1), ha', j5]; exact hH0.2.2
                · rw [if_neg j5]
                  have : Klein.resW (2 * Hc + 1) (0 : ℝ) = 0 := by
                    have := resW_nat (Mo := 2 * Hc + 1) (z := 0) le_rfl (by omega)
                    simpa using this
                  rw [this]
                  exact hz a ha (by omega)
      · simp only [h3, ↓reduceIte]
        exact hz a ha (by omega)
  · simp only [h1, ↓reduceIte]
    by_cases h2 : a - (Klein.kleinWN B n Hc + 1) < Pin.data.length
    · have := hPin _ h2
      rwa [show Klein.kleinWN B n Hc + 1 + (a - (Klein.kleinWN B n Hc + 1)) = a by omega] at this
    · rw [List.getD_eq_default _ _ (by omega)]
      exact hz a ha (by omega)

/-! ### Size bounds -/

lemma isoN1_mono {a a' b b' c c' : ℕ} (h1 : a ≤ a') (h2 : b ≤ b') (h3 : c ≤ c') :
    MSSP.isoN1 a b c ≤ MSSP.isoN1 a' b' c' := by
  unfold MSSP.isoN1 MSSP.isoN2 MSSP.isoN3; gcongr

lemma msHI_mono {w w' a a' b b' k k' : ℕ} (h1 : w ≤ w') (h2 : a ≤ a') (h3 : b ≤ b')
    (h4 : k ≤ k') : msHI w a b k ≤ msHI w' a' b' k' := by
  unfold msHI msZ msH0 msL msK msTh; gcongr

lemma dB_mono {w w' a a' b b' c c' : ℕ} (h1 : w ≤ w') (h2 : a ≤ a') (h3 : b ≤ b')
    (h4 : c ≤ c') : dB w a b c ≤ dB w' a' b' c' := by
  unfold dB; gcongr

lemma kleinWN_mono {B B' n n' H H' : ℕ} (h1 : B ≤ B') (h2 : n ≤ n') (h3 : H ≤ H') :
    Klein.kleinWN B n H ≤ Klein.kleinWN B' n' H' := by
  unfold Klein.kleinWN; gcongr

/-- The maximum of `N₁` over the calls on `m` darts. -/
def N1M (m : ℕ) : ℕ := MSSP.isoN1 (2 * m) (5 * m) (2 * m + 1)

/-- The maximum of the sum `w` of the isolating lengths (lengths `≤ L`). -/
def wM (m L : ℕ) : ℕ := 5 * m * (N1M m * (L + 1))

/-- The maximum of Klein's `Hc`. -/
def HM (m L : ℕ) : ℕ := msHI (wM m L) (2 * m) (2 * m + 1) m

/-- The maximum of Klein's natural word bound `kleinWN`. -/
def KM (m L : ℕ) : ℕ := Klein.kleinWN (dB (wM m L) (5 * m) m m) (20 * m + 1) (HM m L)

/-- **The bound of the low memory of the call** (a polynomial in `m` and `L`). -/
def wzm (m L : ℕ) : ℕ :=
  100 * (KM m L + 1) + 4 * (5 * m + 2) * (N1M m * (L + 1)) + 100 * (m + 1) * (m + 1)

/-- **The scratch of the call** (a polynomial in `m`, `k`, `q`). -/
def Rm (m k q : ℕ) : ℕ := 860 * m + 100 + 2 * q + 3 * KCf m k + 1

lemma HM_ge (m L : ℕ) : 30 * (2 * (2 * m) * wM m L) ≤ HM m L := by
  unfold HM msHI msZ
  generalize msH0 (wM m L) (2 * m) m = a
  generalize msL (wM m L) (2 * m) = b
  generalize msK (wM m L) (2 * m) = c
  generalize 2 * (2 * m) * wM m L = d
  omega

lemma le_KM (m L : ℕ) : HM m L ≤ KM m L ∧ dB (wM m L) (5 * m) m m ≤ KM m L := by
  unfold KM Klein.kleinWN
  have := Nat.le_mul_self (2 * HM m L + 1)
  constructor <;> omega

end MsEnc

end BKMNW

end PlanarFlow
