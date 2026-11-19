module

public import PlanarFlow.STFlow.ProgStore
public import PlanarFlow.STFlow.LexCost

/-!
# The perturbed run as a loop

The program on the machine runs the steps of the perturbed run until one stops. This file
relates such a loop to `lrun` and `pcoreFlow`.

* `lrun_of_piv`: if the first `k` steps from `st` are pivots, `lrun k st` is the state after `k`
  steps and has not stopped;
* `lrun_of_stop`: if the first `i` steps are pivots and the step `i` stops, `lrun k st` is the
  state after `i + 1` steps, for every `k > i`;
* `PertOK`: the properties of the perturbation used by the program (`pertOK_lex` for `lexEps`);
* `piv_le_card`: **if the first `i` steps are pivots, `i ≤ m`** (`PertOK.steps`, `m` darts);
* `piv_lt_fuel`: and `i < fuel F` (`lrun_done`): the loop stops, and `lrun (fuel F)` is its
  result;
* `ltraj_mu`: the value of the second flow stays at most `lexR F ε` in absolute value.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {c ε : D → ℤ} {s t : V}

/-- **A run of pivots**: if the first `k` steps are pivots, `lrun k` has not stopped, has made
`k` steps, and ends at the state after `k` steps. -/
lemma lrun_of_piv : ∀ (k : ℕ) (st : LSt M),
    (∀ j < k, (lstep M c ε s t (ltraj M c ε s t st j)).2 = false) →
    lrun M c ε s t k st = (ltraj M c ε s t st k, k, false)
  | 0, st, _ => rfl
  | k + 1, st, h => by
    have h0 : (lstep M c ε s t st).2 = false := h 0 (by omega)
    have ih := lrun_of_piv k (lstep M c ε s t st).1 fun j hj => by
      rw [← ltraj_succ']; exact h (j + 1) (by omega)
    unfold lrun
    rw [ite_eq_right (by simp [h0]), ih, ltraj_succ']

/-- **A run stopping at the step `i`**: `lrun k` for `k > i` ends at the state after `i + 1`
steps. -/
lemma lrun_of_stop : ∀ (i : ℕ) (st : LSt M),
    (∀ j < i, (lstep M c ε s t (ltraj M c ε s t st j)).2 = false) →
    (lstep M c ε s t (ltraj M c ε s t st i)).2 = true → ∀ k, i < k →
    lrun M c ε s t k st = (ltraj M c ε s t st (i + 1), i + 1, true)
  | 0, st, _, hs, k, hk => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hs' : (lstep M c ε s t st).2 = true := hs
    unfold lrun
    rw [ite_eq_left hs']; rfl
  | i + 1, st, h, hs, k, hk => by
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h0 : (lstep M c ε s t st).2 = false := h 0 (by omega)
    have ih := lrun_of_stop i (lstep M c ε s t st).1 (fun j hj => by
      rw [← ltraj_succ']; exact h (j + 1) (by omega)) (by rw [← ltraj_succ']; exact hs) k
      (by omega)
    unfold lrun
    rw [ite_eq_right (by simp [h0]), ih, ← ltraj_succ']

/-- If the first `i` steps are pivots, `lrun (i + 1)` counts `i + 1` steps. -/
lemma lrun_count {i : ℕ} {st : LSt M}
    (h : ∀ j < i, (lstep M c ε s t (ltraj M c ε s t st j)).2 = false) :
    (lrun M c ε s t (i + 1) st).2.1 = i + 1 := by
  cases hs : (lstep M c ε s t (ltraj M c ε s t st i)).2
  · rw [lrun_of_piv (i + 1) st fun j hj => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact h j hj
      · exact hs]
  · rw [lrun_of_stop i st h hs (i + 1) (by omega)]

variable (M) in
/-- **The properties of a perturbation used by the program** (`pstProg`): it is nonnegative, it
separates the darts of the path of the cotree (two darts of the path with the same `lred` are
equal, so the least key on the path is the bottleneck, `lbott_eq_of_key'`), and every run from a
state rooted at the face of `d₀` takes at most `m + 1` steps. Both `lexEps` (`pertOK_lex`) and
the word-size perturbation `isoEps` (`PlanarFlow.STFlow.pertOK_iso`) have them. -/
structure PertOK (c ε : D → ℤ) (s t : V) (d₀ : D) : Prop where
  nonneg : ∀ d, 0 ≤ ε d
  sep : ∀ (T : DTree M) (d₁ d₂ : D), T.chi s t d₁ = 1 → T.chi s t d₂ = 1 →
    lred ε T d₁ = lred ε T d₂ → d₁ = d₂
  steps : ∀ st : LSt M, LInv c ε s t st → st.T.root = M.face d₀ → ∀ n,
    (lrun M c ε s t n st).2.1 ≤ Fintype.card D + 1

/-- **`lexEps` has the properties used by the program.** -/
theorem pertOK_lex (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hc : ∀ d, 0 ≤ c d) (hst : s ≠ t) {d₀ : D} (hd₀ : M.tail d₀ = t) :
    PertOK M c (lexEps D F) s t d₀ where
  nonneg d := lexEps_nonneg d
  sep T d₁ d₂ h₁ _ h := by
    obtain ⟨-, -, hoff, -⟩ := T.chi_spec hM s t
    exact lred_inj T (fun hT => by rw [hoff d₁ hT] at h₁; exact absurd h₁ (by norm_num)) h
  steps _ hI hroot n := lsteps_le hM hrot hface hc hst hd₀ hI hroot n

/-- **If the first `i` steps of a perturbed run are pivots, `i ≤ m`.** -/
theorem piv_le_card {d₀ : D} (hP : PertOK M c ε s t d₀) {st : LSt M}
    (hI : LInv c ε s t st) (hroot : st.T.root = M.face d₀) {i : ℕ}
    (h : ∀ j < i, (lstep M c ε s t (ltraj M c ε s t st j)).2 = false) :
    i ≤ Fintype.card D := by
  have := hP.steps st hI hroot (i + 1)
  rw [lrun_count h] at this
  omega

/-- **If the first `i` steps are pivots, `i < fuel F`.** -/
theorem piv_lt_fuel (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} {i : ℕ}
    (h : ∀ j < i, (lstep M c ε s t (ltraj M c ε s t st j)).2 = false) : i < fuel F := by
  by_contra hle
  obtain ⟨h1, h2, -, h4⟩ := st.T.chi_spec hM s t
  have hdone := lrun_done (c := c) (ε := ε) hM hst (P := st.T.chi s t) ⟨h1, h2, h4⟩ st
    (n := fuel F) (by unfold fuel; omega)
  rw [lrun_of_piv (fuel F) st fun j hj => h j (by omega)] at hdone
  exact absurd hdone (by simp)

/-- **The value of the second flow stays bounded** along the run. -/
theorem ltraj_mu (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} (hI : LInv c ε s t st)
    (hε : ∀ d, 0 ≤ ε d) (h0 : |M.div st.h s| ≤ lexR F ε) :
    ∀ i, |M.div (ltraj M c ε s t st i).h s| ≤ lexR F ε
  | 0 => h0
  | i + 1 => lstep_mu hM hst (ltraj_inv hM hI i) hε

end STFlow

end PlanarFlow
