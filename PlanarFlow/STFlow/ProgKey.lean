module

public import PlanarFlow.STFlow.TreePath

/-!
# The keys of the perturbed run: one number per dart

The perturbed run (`PlanarFlow/STFlow/Lex.lean`) compares the residual capacities of the darts of
the path of the cotree as pairs `(c - g, ε - h)`, lexicographically, with
`ε d = (4 F + 5) ^ (index of d)` (`lexEps`). The program on the machine stores **one integer per
dart**, the key

  `lkey N c ε g h d = N (c d - g d) + (ε d - h d)`,

an exact value in the real registers and memory of the machine (`WordRAM`, whose real arithmetic
is exact at unit cost); the keys are integers of `O(m log m)` bits. This file proves that the
keys select the same dart as the lexicographic rule and stay bounded.

* `linv_h`, `linv_g`: under the invariant `LInv`, the two flows are determined by the tree and
  their values: `h = μ χ + cob (psum ε)` and `g = λ χ + cob (psum c)`, with `χ` the path of the
  cotree, `μ`, `λ` the values. So on the darts of the path the second coordinates are
  `ε - h = lred ε T - μ`, where `lred ε T = ε - cob (psum ε)` is bounded by `lexR F ε =
  (F + 1) Σ ε` (`abs_lred_le`): on the path the second coordinates differ by less than `2 lexR`.
* `lkey_le_iff`: hence for `N > 2 lexR F ε` **the order of the keys on the darts of the path is
  the lexicographic order of the residual capacities**.
* `lred_inj`: **the perturbation separates the darts off the tree**: two darts off `T` with the
  same value of `lred (lexEps D F) T` are equal (base-`B` digits, `count_eq_of_dsum_eq`).
  So the lexicographic minimum on the path is unique.
* `lbott_eq_of_key`: **a dart of the path of least key is the perturbed bottleneck `lbott`**;
  `lbott_eq_of_key'`: the same for any nonnegative perturbation separating the darts of the path.
* `lstep_mu`: the value `μ` of the second flow after a step is `lred` of the bottleneck, so
  `|μ| ≤ lexR F ε` along the run (it is `0` at the start); `lkey_path_bound`: under this bound the
  keys of the darts of the path are between `0` and `N Σ c + 2 lexR F ε`.
* `lstep_key`: a step subtracts the key of the bottleneck times `χ` from the keys.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {c ε : D → ℤ} {s t : V}

variable (F) in
/-- The bound `(F + 1) Σ ε` of the perturbation part of a reduced length. -/
def lexR (ε : D → ℤ) : ℤ := (Fintype.card F + 1) * ∑ d, ε d

/-- **The key of a dart**: `N (c - g) + (ε - h)`. -/
def lkey (N : ℤ) (c ε g h : D → ℤ) (d : D) : ℤ := N * (c d - g d) + (ε d - h d)

/-- The perturbation part of the reduced length of a dart for a tree: `ε - cob (psum ε)`. -/
def lred (ε : D → ℤ) (T : DTree M) (d : D) : ℤ := ε d - M.cob (T.psum ε) d

/-! ### The flows of a state -/

/-- **The second flow of a state** is `μ χ + cob (psum ε)`. -/
theorem linv_h (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} (hI : LInv c ε s t st) (d : D) :
    st.h d = M.div st.h s * st.T.chi s t d + M.cob (st.T.psum ε) d := by
  obtain ⟨χa, χdiv, χoff, χle⟩ := st.T.chi_spec hM s t
  obtain ⟨ψ, hψ⟩ := exists_cob_of_cons hM hI.antisymm hI.cons
    (P := st.T.chi s t) ⟨χa, χdiv, χle⟩ hst
  have hpar : ∀ x, x ≠ st.T.root → M.cob ψ (st.T.par x) = ε (st.T.par x) := by
    intro x hx
    have h1 := hψ (st.T.par x)
    rw [χoff _ (st.T.inT_par hx), mul_zero, zero_add] at h1
    rw [← h1]; exact hI.sat x hx
  have hps : ∀ x, ψ x = st.T.psum ε x + ψ st.T.root := fun x => by
    have := st.T.psum_congr hpar x
    rw [DTree.psum_cob] at this; linarith
  rw [hψ d]; simp only [cob]; rw [hps (M.face (M.rev d)), hps (M.face d)]; ring

/-- **The flow of a state** is `λ χ + cob (psum c)`. -/
theorem linv_g (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} (hI : LInv c ε s t st) (d : D) :
    st.g d = M.div st.g s * st.T.chi s t d + M.cob (st.T.psum c) d := by
  obtain ⟨χa, χdiv, χoff, χle⟩ := st.T.chi_spec hM s t
  obtain ⟨ψ, hψ⟩ := exists_cob_of_cons hM hI.base.pseudo.antisymm hI.base.cons
    (P := st.T.chi s t) ⟨χa, χdiv, χle⟩ hst
  have hpar : ∀ x, x ≠ st.T.root → M.cob ψ (st.T.par x) = c (st.T.par x) := by
    intro x hx
    have h1 := hψ (st.T.par x)
    rw [χoff _ (st.T.inT_par hx), mul_zero, zero_add] at h1
    rw [← h1]; exact hI.base.sat x hx
  have hps : ∀ x, ψ x = st.T.psum c x + ψ st.T.root := fun x => by
    have := st.T.psum_congr hpar x
    rw [DTree.psum_cob] at this; linarith
  simp only [LSt.base_g] at hψ
  rw [hψ d]; simp only [cob]; rw [hps (M.face (M.rev d)), hps (M.face d)]; ring

/-- On a dart of the path, the second coordinate is `lred - μ`. -/
lemma linv_slack2 (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} (hI : LInv c ε s t st) {d : D}
    (hd : st.T.chi s t d = 1) : ε d - st.h d = lred ε st.T d - M.div st.h s := by
  rw [linv_h hM hst hI d, hd, lred]; ring

/-- **The perturbation part of a reduced length is at most `(F + 1) Σ ε`.** -/
lemma abs_lred_le (hε : ∀ d, 0 ≤ ε d) (T : DTree M) (d : D) : |lred ε T d| ≤ lexR F ε := by
  have h1 := T.psum_nonneg hε (M.face d)
  have h2 := T.psum_nonneg hε (M.face (M.rev d))
  have h3 := T.psum_le hε (M.face d)
  have h4 := T.psum_le hε (M.face (M.rev d))
  have h5 : ε d ≤ ∑ d, ε d := single_le_sum (fun d _ => hε d) (mem_univ d)
  have h6 := hε d
  unfold lred lexR
  simp only [cob]
  rw [abs_le]
  constructor <;> nlinarith

/-! ### The order of the keys -/

/-- **On the darts of the path, the keys are ordered as the lexicographic residual capacities**,
for `N > 2 lexR F ε`. -/
theorem lkey_le_iff (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} (hI : LInv c ε s t st)
    (hε : ∀ d, 0 ≤ ε d) {N : ℤ} (hN : 2 * lexR F ε < N) {d₁ d₂ : D}
    (h₁ : st.T.chi s t d₁ = 1) (h₂ : st.T.chi s t d₂ = 1) :
    lkey N c ε st.g st.h d₁ ≤ lkey N c ε st.g st.h d₂ ↔
      lslack c ε st.g st.h d₁ ≤ lslack c ε st.g st.h d₂ := by
  have e₁ := linv_slack2 hM hst hI h₁
  have e₂ := linv_slack2 hM hst hI h₂
  have b₁ := abs_le.1 (abs_lred_le hε st.T d₁)
  have b₂ := abs_le.1 (abs_lred_le hε st.T d₂)
  rw [lslack, lslack, Prod.Lex.toLex_le_toLex']
  simp only [lkey]
  set x₁ := c d₁ - st.g d₁
  set x₂ := c d₂ - st.g d₂
  have hy : |(ε d₁ - st.h d₁) - (ε d₂ - st.h d₂)| < N := by
    rw [e₁, e₂, abs_lt]; constructor <;> linarith
  rw [abs_lt] at hy
  constructor
  · intro h
    refine ⟨?_, fun hx => ?_⟩
    · by_contra hlt
      have : x₂ + 1 ≤ x₁ := by omega
      nlinarith
    · rw [hx] at h; linarith
  · rintro ⟨hx, hy'⟩
    rcases hx.lt_or_eq with hlt | heq
    · have : x₁ + 1 ≤ x₂ := by omega
      nlinarith
    · rw [heq]; linarith [hy' heq]

/-- **The perturbation separates the darts off the tree.** -/
theorem lred_inj (T : DTree M) {d₁ d₂ : D} (h₁ : ¬ T.InT d₁)
    (h : lred (lexEps D F) T d₁ = lred (lexEps D F) T d₂) : d₁ = d₂ := by
  by_contra hne
  set l₁ := d₁ :: (T.tpath (M.face d₁) ++ T.tpath (M.face (M.rev d₂))) with hl₁
  set l₂ := d₂ :: (T.tpath (M.face d₂) ++ T.tpath (M.face (M.rev d₁))) with hl₂
  have hB : 3 < lexBase F := by unfold lexBase; omega
  have hcnt : ∀ (a : D) (x y : F) (d : D),
      (a :: (T.tpath x ++ T.tpath y)).count d < lexBase F := by
    intro a x y d
    have c1 := List.nodup_iff_count_le_one.1 (T.nodup_tpath x) d
    have c2 := List.nodup_iff_count_le_one.1 (T.nodup_tpath y) d
    rw [List.count_cons, List.count_append]
    split_ifs <;> omega
  have hsum : ∀ (a : D) (x y : F), dsum (lexEps D F) (a :: (T.tpath x ++ T.tpath y)) =
      lexEps D F a + T.psum (lexEps D F) x + T.psum (lexEps D F) y := fun a x y => by
    rw [dsum_cons, dsum_append, T.dsum_tpath, T.dsum_tpath]; ring
  have heq : dsum (fun d => (lexBase F : ℤ) ^ (Fintype.equivFin D d : ℕ)) l₁ =
      dsum (fun d => (lexBase F : ℤ) ^ (Fintype.equivFin D d : ℕ)) l₂ := by
    change dsum (lexEps D F) l₁ = dsum (lexEps D F) l₂
    rw [hl₁, hl₂, hsum, hsum]
    unfold lred at h
    simp only [cob] at h
    linarith
  have := count_eq_of_dsum_eq (hcnt _ _ _) (hcnt _ _ _) heq d₁
  have hc1 : 1 ≤ l₁.count d₁ := by rw [hl₁, List.count_cons_self]; omega
  have hnot : ∀ x, d₁ ∉ T.tpath x := fun x hm => by
    obtain ⟨y, hy, -, rfl⟩ := T.mem_tpath.1 hm
    exact h₁ (T.inT_par hy)
  have hc2 : l₂.count d₁ = 0 := by
    rw [List.count_eq_zero, hl₂, List.mem_cons, List.mem_append, not_or, not_or]
    exact ⟨hne, hnot _, hnot _⟩
  have hc2' : (d₂ :: (T.tpath (M.face d₂) ++ T.tpath (M.face (M.rev d₁)))).count d₁ = 0 := hc2
  have hc1' : (d₁ :: (T.tpath (M.face d₁) ++ T.tpath (M.face (M.rev d₂)))).count d₁ ≥ 1 := hc1
  omega

/-- **A dart of the path of least key is the perturbed bottleneck.** -/
theorem lbott_eq_of_key (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M}
    (hI : LInv c (lexEps D F) s t st) {N : ℤ} (hN : 2 * lexR F (lexEps D F) < N) {e : D}
    (he : st.T.chi s t e = 1)
    (hmin : ∀ d, st.T.chi s t d = 1 →
      lkey N c (lexEps D F) st.g st.h e ≤ lkey N c (lexEps D F) st.g st.h d)
    (hne : (pathSet s t st.T).Nonempty) :
    lbott c (lexEps D F) s t st.g st.h st.T hne = e := by
  have hε : ∀ d, 0 ≤ lexEps D F d := fun d => lexEps_nonneg d
  set b := lbott c (lexEps D F) s t st.g st.h st.T hne with hb
  have hbm := lbott_mem c (lexEps D F) s t st.g st.h st.T hne
  have h1 := (lkey_le_iff hM hst hI hε hN he hbm).1 (hmin b hbm)
  have h2 := lbott_min c (lexEps D F) s t st.g st.h st.T hne he
  have heq := le_antisymm h1 h2
  rw [lslack, lslack] at heq
  have h2' := congrArg (fun p => (ofLex p).2) heq
  simp only [ofLex_toLex] at h2'
  rw [linv_slack2 hM hst hI he, linv_slack2 hM hst hI hbm] at h2'
  obtain ⟨-, -, hoff, -⟩ := st.T.chi_spec hM s t
  have hnT : ¬ st.T.InT e := fun h => by rw [hoff e h] at he; exact absurd he (by norm_num)
  exact (lred_inj st.T hnT (by linarith)).symm

/-- **A dart of the path of least key is the perturbed bottleneck**, for a nonnegative
perturbation separating the darts of the path (`lred_inj` for `lexEps`;
`PlanarFlow.STFlow.lred_isoEps_inj` for the word-size perturbation). -/
theorem lbott_eq_of_key' (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M}
    (hI : LInv c ε s t st) (hε : ∀ d, 0 ≤ ε d)
    (hsep : ∀ d₁ d₂, st.T.chi s t d₁ = 1 → st.T.chi s t d₂ = 1 →
      lred ε st.T d₁ = lred ε st.T d₂ → d₁ = d₂)
    {N : ℤ} (hN : 2 * lexR F ε < N) {e : D} (he : st.T.chi s t e = 1)
    (hmin : ∀ d, st.T.chi s t d = 1 → lkey N c ε st.g st.h e ≤ lkey N c ε st.g st.h d)
    (hne : (pathSet s t st.T).Nonempty) :
    lbott c ε s t st.g st.h st.T hne = e := by
  set b := lbott c ε s t st.g st.h st.T hne with hb
  have hbm := lbott_mem c ε s t st.g st.h st.T hne
  have h1 := (lkey_le_iff hM hst hI hε hN he hbm).1 (hmin b hbm)
  have h2 := lbott_min c ε s t st.g st.h st.T hne he
  have heq := le_antisymm h1 h2
  rw [lslack, lslack] at heq
  have h2' := congrArg (fun p => (ofLex p).2) heq
  simp only [ofLex_toLex] at h2'
  rw [linv_slack2 hM hst hI he, linv_slack2 hM hst hI hbm] at h2'
  exact (hsep e b he hbm (by linarith)).symm

/-! ### Bounds along the run -/

/-- **The value of the second flow after a step** is `lred` of the bottleneck: at most
`lexR F ε` in absolute value. -/
theorem lstep_mu (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} (hI : LInv c ε s t st)
    (hε : ∀ d, 0 ≤ ε d) : |M.div (lstep M c ε s t st).1.h s| ≤ lexR F ε := by
  obtain ⟨e, he, -, h2⟩ := lstep_value (c := c) (ε := ε) hM hst st
  rw [h2, linv_slack2 hM hst hI he]
  have := abs_lred_le hε st.T e
  simpa using this

/-- **The keys of the darts of the path are between `0` and `N Σ c + 2 lexR F ε`**, when
`|μ| ≤ lexR F ε`. -/
theorem lkey_path_bound (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} (hI : LInv c ε s t st)
    (hε : ∀ d, 0 ≤ ε d) (hc : ∀ d, 0 ≤ c d) (hμ : |M.div st.h s| ≤ lexR F ε) {N : ℤ}
    (hN : 2 * lexR F ε < N) {d : D} (hd : st.T.chi s t d = 1) :
    0 ≤ lkey N c ε st.g st.h d ∧ lkey N c ε st.g st.h d ≤ N * ∑ d, c d + 2 * lexR F ε := by
  have e₁ := linv_slack2 hM hst hI hd
  have b₁ := abs_le.1 (abs_lred_le hε st.T d)
  have bμ := abs_le.1 hμ
  have hle := hI.base.pseudo.le_cap d
  have hle' := hI.base.pseudo.le_cap (M.rev d)
  have hanti := hI.base.pseudo.antisymm d
  simp only [LSt.base_g] at hle hle' hanti
  have hpair : c d + c (M.rev d) ≤ ∑ d, c d := by
    have hdd : d ≠ M.rev d := (M.rev_ne d).symm
    rw [← sum_pair hdd]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => hc i
  have hR0 : 0 ≤ lexR F ε := (abs_nonneg _).trans hμ
  unfold lkey
  refine ⟨?_, ?_⟩
  · by_cases h0 : c d - st.g d = 0
    · have := hI.lex d (by omega)
      rw [h0]; linarith
    · have : 1 ≤ c d - st.g d := by omega
      nlinarith
  · have hx : c d - st.g d ≤ ∑ d, c d := by linarith
    nlinarith

/-- **A step subtracts the key of the bottleneck times `χ` from the keys.** -/
theorem lstep_key {st : LSt M} (hne : (pathSet s t st.T).Nonempty) (N : ℤ) (d : D) :
    lkey N c ε (lstep M c ε s t st).1.g (lstep M c ε s t st).1.h d =
      lkey N c ε st.g st.h d - lkey N c ε st.g st.h (lbott c ε s t st.g st.h st.T hne) *
        st.T.chi s t d := by
  rw [lstep_of_ne hne]
  simp only [stepE_g, aug, LSt.base_g, LSt.base_T, lkey]
  ring

end STFlow

end PlanarFlow
