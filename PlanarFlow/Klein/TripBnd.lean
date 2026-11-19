module

public import PlanarFlow.Klein.ProgTripMaskC

/-!
# The explicit bound of the values of Klein's forest, and of the compared differences

The compare-bounded loop over the moves (`Klein.tLoopM_orunC`) holds for any `A`, `Wt`, `H` with
`|tripWt| ≤ Wt`, `|tripL| ≤ Wt`, `Wt + tripW + 2 #V tripW + |tripTh| ≤ A - tripH0` and
`30 (A - tripTh) + 12 tripK + 8 (Wt + tripW) ≤ H`; the values of the forest stay at most
`A - Lo ≤ A - tripTh`. This file fixes them:

* `abs_tripWt_le`: `|tripWt j d| ≤ tripL` (`Wt = tripL`);
* `kleinA`: `A = tripH0 + tripL + tripW + 2 #V tripW + |tripTh|`, **the bound of the values of the
  forest** is `kleinV = kleinA - tripTh` (`val d = wt d + label (tail d) - label (head d)`, the
  values at the nodes of the faces, and those of the isolated nodes, are all at most `kleinV`);
* `kleinH`: `H = 30 (A - tripTh) + 12 tripK + 8 (tripL + tripW)`, **the bound of the compared
  differences**; `klein_bnd_hyps`: the hypotheses of `tLoopM_orunC` hold for them;
* `tripW_le`, `kleinV_le`, `kleinH_le`: with lengths at most `Λ` on the piece (`|ℓ| ≤ Λ`),
  `tripW ≤ #S Λ` and **`kleinV`, `kleinH` are at most `c (k + 1) (#V + 1)² (#S Λ + 1)`**
  (`c = 60`, `c = 3000`): polynomial in the size of the map and the largest length. For the
  isolating lengths of `PlanarFlow/MSSP/Isolate.lean`, `Λ < N₁ (max ℓ + 1)`, `N₁ = (n m + 1)
  (2 B n + 1)(n + 1)` (`MSSP.isoLen_lt`).
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

lemma tripL_nonneg : 0 ≤ tripL V S ℓ := by
  have := tripW_nonneg (S := S) (ℓ := ℓ)
  unfold tripL tripB; positivity

lemma abs_tripWt_le (j : ℕ) (d : D) : |tripWt M k g S ℓ j d| ≤ tripL V S ℓ := by
  classical
  unfold tripWt
  split_ifs with h
  · have h1 := abs_le_tripW (ℓ := ℓ) h.1
    have := tripW_nonneg (S := S) (ℓ := ℓ)
    have : tripW S ℓ ≤ tripL V S ℓ := by
      unfold tripL tripB
      have : 0 ≤ (Fintype.card V : ℤ) * tripW S ℓ := by positivity
      linarith
    linarith
  · rw [abs_of_nonneg tripL_nonneg]

variable (V S ℓ) in
/-- The constant `A` of the bound `A - Lo` of the values of the forest. -/
def kleinA (k : ℕ) : ℝ :=
  tripH0 V S ℓ k + tripL V S ℓ + tripW S ℓ + 2 * (Fintype.card V * tripW S ℓ) +
    |(tripTh V S ℓ : ℝ)|

variable (V S ℓ) in
/-- **The bound of the values of Klein's forest** along the trip: `kleinA - tripTh`. -/
def kleinV (k : ℕ) : ℝ := kleinA V S ℓ k - tripTh V S ℓ

variable (V S ℓ) in
/-- **The bound of the compared differences** along the trip. -/
def kleinH (k : ℕ) : ℝ :=
  30 * (kleinA V S ℓ k - tripTh V S ℓ) + 12 * tripK V S ℓ + 8 * (tripL V S ℓ + tripW S ℓ)

/-- The hypotheses of `tLoopM_orunC` for `Wt = tripL`, `A = kleinA`, `H ≥ kleinH`. -/
theorem klein_bnd_hyps {H : ℝ} (hH : kleinH V S ℓ k ≤ H) :
    (∀ j' d, |(tripWt M k g S ℓ j' d : ℝ)| ≤ tripL V S ℓ) ∧
      |(tripL V S ℓ : ℝ)| ≤ tripL V S ℓ ∧
      (tripL V S ℓ : ℝ) + tripW S ℓ + 2 * (Fintype.card V * tripW S ℓ) +
        |(tripTh V S ℓ : ℝ)| ≤ kleinA V S ℓ k - tripH0 V S ℓ k ∧
      30 * (kleinA V S ℓ k - tripTh V S ℓ) + 12 * tripK V S ℓ +
        8 * ((tripL V S ℓ : ℝ) + tripW S ℓ) ≤ H := by
  refine ⟨fun j' d => by exact_mod_cast abs_tripWt_le j' d, ?_, ?_, hH⟩
  · rw [abs_of_nonneg (by exact_mod_cast tripL_nonneg)]
  · unfold kleinA; linarith

/-- With lengths at most `Λ` on the piece, `tripW ≤ #S Λ`. -/
lemma tripW_le {Λ : ℤ} (h : ∀ d ∈ S, |ℓ d| ≤ Λ) : tripW S ℓ ≤ S.card * Λ := by
  unfold tripW
  have := sum_le_sum h
  simpa [mul_comm] using this

/-- **The bounds `kleinV`, `kleinH` are polynomial**: at most `60 (k + 1) (#V + 1)² (tripW + 1)`
and `3000 (k + 1) (#V + 1)² (tripW + 1)`. -/
theorem kleinV_kleinH_le :
    kleinV V S ℓ k ≤ 60 * (k + 1) * ((Fintype.card V : ℝ) + 1) ^ 2 * (tripW S ℓ + 1) ∧
      kleinH V S ℓ k ≤ 3000 * (k + 1) * ((Fintype.card V : ℝ) + 1) ^ 2 * (tripW S ℓ + 1) := by
  have hW : (0 : ℝ) ≤ tripW S ℓ := by exact_mod_cast tripW_nonneg
  have hv : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  set w : ℝ := ((tripW S ℓ : ℤ) : ℝ) with hw
  set v : ℝ := ((Fintype.card V : ℕ) : ℝ) with hvd
  have eL : (tripL V S ℓ : ℝ) = 4 * (v * w) + w + 1 := by simp [tripL, tripB, hw, hvd]
  have eTh : (tripTh V S ℓ : ℝ) = (tripL V S ℓ : ℝ) - 2 * (v * w) := by simp [tripTh, hw, hvd]
  have eK : (tripK V S ℓ : ℝ) = |(tripL V S ℓ : ℝ)| + |w| + 2 * |v * w| := by
    simp [tripK, driftK, hw, hvd]
  have eH0 : (tripH0 V S ℓ k : ℝ) = tripTh V S ℓ + (k + 1) * ((v + 1) * tripK V S ℓ) := by
    simp [tripH0, hvd]
  have hvw : 0 ≤ v * w := mul_nonneg hv hW
  have hL0 : (0 : ℝ) ≤ tripL V S ℓ := by rw [eL]; positivity
  have hTh0 : (0 : ℝ) ≤ tripTh V S ℓ := by rw [eTh, eL]; linarith
  rw [abs_of_nonneg hL0, abs_of_nonneg hW, abs_of_nonneg hvw] at eK
  have hK : (tripK V S ℓ : ℝ) = 6 * (v * w) + 2 * w + 1 := by rw [eK, eL]; ring
  have hA : kleinA V S ℓ k - tripTh V S ℓ = (k + 1) * ((v + 1) * (6 * (v * w) + 2 * w + 1)) +
      (4 * (v * w) + w + 1) + w + 2 * (v * w) + (2 * (v * w) + w + 1) := by
    unfold kleinA
    rw [abs_of_nonneg hTh0, eH0, hK, eTh, eL]; ring
  have hV : kleinV V S ℓ k ≤ 60 * (k + 1) * (v + 1) ^ 2 * (w + 1) := by
    unfold kleinV; rw [hA]
    nlinarith [mul_nonneg hk hv, mul_nonneg (mul_nonneg hk hv) hv, mul_nonneg hk hW,
      mul_nonneg (mul_nonneg hk hv) hW, mul_nonneg (mul_nonneg (mul_nonneg hk hv) hv) hW,
      mul_nonneg hv hv, mul_nonneg (mul_nonneg hv hv) hW]
  refine ⟨hV, ?_⟩
  unfold kleinH
  rw [hA, hK, eL]
  nlinarith [mul_nonneg hk hv, mul_nonneg (mul_nonneg hk hv) hv, mul_nonneg hk hW,
    mul_nonneg (mul_nonneg hk hv) hW, mul_nonneg (mul_nonneg (mul_nonneg hk hv) hv) hW,
    mul_nonneg hv hv, mul_nonneg (mul_nonneg hv hv) hW]

end Klein

end PlanarFlow
