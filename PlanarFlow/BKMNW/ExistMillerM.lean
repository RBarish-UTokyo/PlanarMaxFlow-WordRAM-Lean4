module

public import PlanarFlow.BKMNW.ExistMillerD
public import PlanarSeparator.Machine.MillerFullAll

/-!
# The separator of the machine program meets the hypotheses of `exists_core_cycle'`

* `PlanarFlow.BKMNW.miller_len_bound`: the length bound `2 (l₂ - l₀) + #K₀ + #(T.lvl l₂)` of
  `PlanarSeparator.MillerProg.millerFull_spec` is at most `6 √n + 4`, from the facts exported by
  `millerFull_spec`.
* **`PlanarFlow.BKMNW.coreSep_of_sepOK`**: a separator `(C, Z)` of the stellar subdivision of the
  piece map with `SepOK (wR (coreWt …)) N (C, Z)` (the form of the output of `millerFull`, run on
  the coded stellar subdivision with the natural weights `coreWt`) and `N ≤ 6 √(#SVert + #Face) + 4`
  meets the four hypotheses of `exists_core_cycle'` (hence of `scert_core'` and of
  `ScChoice.OK.sep`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- **The length bound of Miller's program**: with the facts exported by `millerFull_spec`
(`a = #(T.lvl l₂)`, `b = #K₀`, `c = #(T.lvl l₀)`), the cycle has at most `6 √n + 4` darts. -/
lemma miller_len_bound {n l₀ l₂ a b c : ℕ} (h3 : (Nat.sqrt n + 1) * a ≤ n)
    (hl : l₂ ≤ l₀ + 2 * Nat.sqrt n + 1)
    (hK : (l₀ = 0 ∧ b = 1) ∨ (b ≤ c ∧ (Nat.sqrt n + 1) * c ≤ n)) :
    2 * (l₂ - l₀) + b + a ≤ 6 * Nat.sqrt n + 4 := by
  have ha := Map.le_sqrt_of_mul_le' h3
  rcases hK with ⟨-, rfl⟩ | ⟨hb, hc⟩
  · omega
  · have := Map.le_sqrt_of_mul_le' hc
    omega

open Classical PlanarSeparator.Map in
/-- **The output form of the machine's Miller program gives the hypotheses of
`exists_core_cycle'`**: `SepOK (wR (coreWt …)) N (C, Z)` with `N ≤ 6 √(#SVert + #Face) + 4`. -/
theorem coreSep_of_sepOK {σ : Perm D} {B : Finset D} (hσ : Stable σ B)
    (hB : Stable (revPerm M) B) (wd : D → ℕ) (wq : SVert σ B → ℕ) {N : ℕ}
    (hN : N ≤ 6 * Nat.sqrt (Fintype.card (SVert σ B) + Fintype.card (psep M hσ hB).Face) + 4)
    {C : (psep M hσ hB).stellar.SCycle} {Z : Finset (psep M hσ hB).stellar.Face}
    (h : SepOK (MillerProg.wR (coreWt hσ hB wd wq)) N (C, Z)) :
    C.k ≤ 6 * Nat.sqrt (Fintype.card (SVert σ B) + Fintype.card (psep M hσ hB).Face) + 4 ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      3 * ∑ y ∈ sideIn C Z, coreWt hσ hB wd wq y ≤
        2 * (∑ x : SDart B, wd x.1 + ∑ q, wq q) + 2 ∧
      3 * ∑ y ∈ sideOut C Z, coreWt hσ hB wd wq y ≤
        2 * (∑ x : SDart B, wd x.1 + ∑ q, wq q) + 2 := by
  obtain ⟨hk, hsep, hin, hout⟩ := h
  rw [← sum_coreWt hσ hB wd wq]
  exact ⟨hk.trans hN, hsep, three_sum_le_of_norm _ _ hin, three_sum_le_of_norm _ _ hout⟩

end BKMNW

end PlanarFlow
