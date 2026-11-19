module

public import PlanarFlow.BKMNW.NcFzN

/-!
# Polynomial bounds of the envelopes of `fzP`

Transfer lemmas for the zero area and room of `fzP fixC`: with `X = m + Z + 1`
(resp. `N + Z + 1`),

* **`Pp.fzWz_le`**: `wzf m Z ≤ a X^p` (all `m Z`) ⟹ `fzWz wzf m Z ≤ 3a X^(2p+1)`;
* **`Pp.fzRN_le`**: `fxR m Z ≤ r X^q` ⟹ `fzRN fxR N Z ≤ (3r + 44) X^(2q+3)`;
* **`Pp.c2sRC_fzRN_le`**: then `c2sRC (fzRN fxR) N Z ≤ (3r + 4000000144) X^(2q+5)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

/-! ### Transfer lemmas for the envelopes of `fzP` -/

namespace Pp

open Finset

/-- `i + m Z + 1 ≤ (m + Z + 1)²` for `i ≤ 3m`. -/
lemma fz_arg_le {i m Z : ℕ} (hi : i ≤ 3 * m) : i + m * Z + 1 ≤ (m + Z + 1) ^ 2 := by
  have h1 : m ≤ m * m := Nat.le_mul_self m
  have e : (m + Z + 1) ^ 2 = m * m + Z * Z + 2 * (m * Z) + 2 * m + 2 * Z + 1 := by ring
  omega

/-- A sum over `i ≤ 3m` of `f i (m Z)` with `f i Y ≤ a (i + Y + 1)^p`. -/
lemma fz_sum_le {f : ℕ → ℕ → ℕ} {a p : ℕ} (h : ∀ m Z, f m Z ≤ a * (m + Z + 1) ^ p) (m Z : ℕ) :
    ∑ i ∈ range (3 * m + 1), f i (m * Z) ≤ 3 * a * (m + Z + 1) ^ (2 * p + 1) := by
  have hX : 1 ≤ m + Z + 1 := by omega
  calc ∑ i ∈ range (3 * m + 1), f i (m * Z)
      ≤ ∑ _i ∈ range (3 * m + 1), a * ((m + Z + 1) ^ 2) ^ p :=
        sum_le_sum fun i hi => (h i (m * Z)).trans (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (fz_arg_le (by have := mem_range.1 hi; omega)) _))
    _ = (3 * m + 1) * (a * (m + Z + 1) ^ (2 * p)) := by
        simp only [sum_const, card_range, smul_eq_mul, ← pow_mul]
    _ ≤ (3 * (m + Z + 1)) * (a * (m + Z + 1) ^ (2 * p)) := Nat.mul_le_mul_right _ (by omega)
    _ = 3 * a * (m + Z + 1) ^ (2 * p + 1) := by ring

/-- **The zero area of `fzP`**: `wzf m Z ≤ a (m + Z + 1)^p` ⟹
`fzWz wzf m Z ≤ 3a (m + Z + 1)^(2p + 1)`. -/
theorem fzWz_le {wzf : ℕ → ℕ → ℕ} {a p : ℕ} (h : ∀ m Z, wzf m Z ≤ a * (m + Z + 1) ^ p)
    (m Z : ℕ) : NcFz.fzWz wzf m Z ≤ 3 * a * (m + Z + 1) ^ (2 * p + 1) :=
  fz_sum_le h m Z

/-- The room of `fzP` at a frame of `m` darts. -/
lemma fzRc_le {fxR : ℕ → ℕ → ℕ} {r q : ℕ} (h : ∀ m Z, fxR m Z ≤ r * (m + Z + 1) ^ q)
    (m Z : ℕ) : NcFz.fzRc fxR Z m ≤ (3 * r + 44) * (m + Z + 1) ^ (2 * q + 2) := by
  have h1 := fz_sum_le h m Z
  set X := m + Z + 1 with hXd
  have hX : 1 ≤ X := by omega
  have hmZ : m * Z ≤ X ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have hXX : X ≤ X ^ 2 := by rw [sq]; exact Nat.le_mul_self X
  have hp1 : X ^ 2 ≤ X ^ (2 * q + 2) := Nat.pow_le_pow_right hX (by omega)
  have hp2 : X ^ (2 * q + 1) ≤ X ^ (2 * q + 2) := Nat.pow_le_pow_right hX (by omega)
  have hp3 : 3 * r * X ^ (2 * q + 1) ≤ 3 * r * X ^ (2 * q + 2) := Nat.mul_le_mul_left _ hp2
  have e : (3 * r + 44) * X ^ (2 * q + 2) = 3 * r * X ^ (2 * q + 2) + 44 * X ^ (2 * q + 2) := by
    ring
  unfold NcFz.fzRc
  clear_value X
  omega

/-- **The room of `fzP`**: `fxR m Z ≤ r (m + Z + 1)^q` ⟹
`fzRN fxR N Z ≤ (3r + 44) (N + Z + 1)^(2q + 3)`. -/
theorem fzRN_le {fxR : ℕ → ℕ → ℕ} {r q : ℕ} (h : ∀ m Z, fxR m Z ≤ r * (m + Z + 1) ^ q)
    (N Z : ℕ) : NcFz.fzRN fxR N Z ≤ (3 * r + 44) * (N + Z + 1) ^ (2 * q + 3) := by
  unfold NcFz.fzRN
  calc ∑ m ∈ range (N + 1), NcFz.fzRc fxR Z m
      ≤ ∑ _m ∈ range (N + 1), (3 * r + 44) * (N + Z + 1) ^ (2 * q + 2) :=
        sum_le_sum fun m hm => (fzRc_le h m Z).trans (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (by have := mem_range.1 hm; omega) _))
    _ = (N + 1) * ((3 * r + 44) * (N + Z + 1) ^ (2 * q + 2)) := by
        simp only [sum_const, card_range, smul_eq_mul]
    _ ≤ (N + Z + 1) * ((3 * r + 44) * (N + Z + 1) ^ (2 * q + 2)) :=
        Nat.mul_le_mul_right _ (by omega)
    _ = (3 * r + 44) * (N + Z + 1) ^ (2 * q + 3) := by ring

/-- **The room of `c2sP (fzP fixC) pbP`**: `fxR m Z ≤ r (m + Z + 1)^q` ⟹
`c2sRC (fzRN fxR) N Z ≤ (3r + 4000000144) (N + Z + 1)^(2q + 5)`. -/
theorem c2sRC_fzRN_le {fxR : ℕ → ℕ → ℕ} {r q : ℕ} (h : ∀ m Z, fxR m Z ≤ r * (m + Z + 1) ^ q)
    (N Z : ℕ) : c2sRC (NcFz.fzRN fxR) N Z ≤ (3 * r + 4000000144) * (N + Z + 1) ^ (2 * q + 5) := by
  have := c2sRC_le (fzRN_le h) N Z
  have e : 3 * r + 44 + 4000000100 = 3 * r + 4000000144 := by ring
  rw [e] at this
  exact this

end Pp

end BKMNW

end PlanarFlow
