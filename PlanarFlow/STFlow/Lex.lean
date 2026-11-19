module

public import PlanarFlow.STFlow.Spec

/-!
# The algorithm with perturbed capacities

The analysis of the number of pivots (Erickson, SODA 2010, through the multiple-source shortest
paths of Cabello, Chambers and Erickson, SIAM J. Comput. 42, 2013) assumes **generic lengths**:
unique shortest paths and exactly one dart becoming tight at each critical value of the parameter.
Cabello, Chambers and Erickson (Section 6, *Enforcing genericity*) remove the assumption by a
perturbation of the weights: the weight of a dart becomes a pair `(w, ω)`, and lengths, slacks and
flows are compared lexicographically. This file runs the algorithm of
`PlanarFlow/STFlow/Pivot.lean` with that perturbation of the capacities: the capacity of `d` is the
pair `(c d, ε d)` (`ε d = B ^ (index of d)` in the implementation, `lexEps`).

## The perturbed run

The state (`LSt`) carries, besides the flow `g` and the dual tree `T`, the flow `h` of the second
coordinates. One step (`lstep`) is the step of `PlanarFlow/STFlow/Pivot.lean` at the dart `e`
(`stepE`) chosen as a dart of the path of the cotree of **lexicographically** least residual
capacity `(c - g, ε - h)` (`lbott`); `h` is augmented along the same path by `ε e - h e`. The first
coordinate is the algorithm itself with a particular choice of the bottleneck (`lbott_isBott`): the
flow `g` and the tree evolve as in the unperturbed algorithm, so the correctness proof applies
unchanged.

* `LInv`: the invariant: `Inv` for `(g, T)`, `h` antisymmetric and conserved off `s` and `t`,
  `h ≤ ε` on the darts saturated by `g`, and `h = ε` on the darts of the tree.
* `lstep_inv`: **the step keeps the invariant.**
* `lrun_spec`: **correctness of the perturbed run**: from a state satisfying the invariant, with
  enough steps, the run stops with a pseudoflow conserved off `s` and `t` and no residual path.
* `exists_linit`: **the initial state**: the shortest-path tree of the dual for the lengths
  `N c + ε` (`N` large) is a shortest-path tree for the lexicographic lengths `(c, ε)`; the flows
  are the coboundaries of its path sums.
* `pstflow`, `pstflow_spec`: **the perturbed implementation meets `STFlowSpec`** on every plane
  map (the contraction by capacities of `PlanarFlow/STFlow/Spec.lean`, unchanged).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- The state of the perturbed run: the flow, the flow of the perturbation, the dual tree. -/
structure LSt where
  /-- The flow. -/
  g : D → ℤ
  /-- The flow of the second coordinates (the perturbation). -/
  h : D → ℤ
  /-- The spanning tree of the dual. -/
  T : DTree M

/-- The unperturbed part of a state. -/
def LSt.base (st : LSt M) : St M := ⟨st.g, st.T⟩

@[simp] lemma LSt.base_g (st : LSt M) : st.base.g = st.g := rfl

@[simp] lemma LSt.base_T (st : LSt M) : st.base.T = st.T := rfl

variable (c ε : D → ℤ) (s t : V)

/-- The residual capacity of a dart, as a pair compared lexicographically. -/
def lslack (g h : D → ℤ) (d : D) : ℤ ×ₗ ℤ := toLex (c d - g d, ε d - h d)

/-- **The perturbed bottleneck**: a dart of the path of the cotree of lexicographically least
residual capacity. -/
noncomputable def lbott (g h : D → ℤ) (T : DTree M) (hne : (pathSet s t T).Nonempty) : D :=
  ((pathSet s t T).exists_min_image (lslack c ε g h) hne).choose

lemma lbott_mem (g h : D → ℤ) (T : DTree M) (hne : (pathSet s t T).Nonempty) :
    T.chi s t (lbott c ε s t g h T hne) = 1 := by
  have := ((pathSet s t T).exists_min_image (lslack c ε g h) hne).choose_spec.1
  unfold lbott
  simpa [pathSet] using this

lemma lbott_min (g h : D → ℤ) (T : DTree M) (hne : (pathSet s t T).Nonempty) {d : D}
    (hd : T.chi s t d = 1) :
    lslack c ε g h (lbott c ε s t g h T hne) ≤ lslack c ε g h d :=
  ((pathSet s t T).exists_min_image (lslack c ε g h) hne).choose_spec.2 d
    (by simp [pathSet, hd])

/-- **The perturbed bottleneck is a bottleneck** of the unperturbed algorithm. -/
lemma lbott_isBott (g h : D → ℤ) (T : DTree M) (hne : (pathSet s t T).Nonempty) :
    IsBott c s t g T (lbott c ε s t g h T hne) := by
  refine ⟨lbott_mem c ε s t g h T hne, fun d hd => ?_⟩
  have := lbott_min c ε s t g h T hne hd
  rw [lslack, lslack, Prod.Lex.toLex_le_toLex'] at this
  exact this.1

variable (M) in
open Classical in
/-- **One step of the perturbed run**: the step at the perturbed bottleneck `e` (`stepE`), and the
flow of the perturbation augmented along the same path by `ε e - h e`. -/
noncomputable def lstep (st : LSt M) : LSt M × Bool :=
  if hne : (pathSet s t st.T).Nonempty then
    (⟨(stepE M c s t st.base (lbott c ε s t st.g st.h st.T hne)).1.g,
      aug st.h (st.T.chi s t)
        (ε (lbott c ε s t st.g st.h st.T hne) - st.h (lbott c ε s t st.g st.h st.T hne)),
      (stepE M c s t st.base (lbott c ε s t st.g st.h st.T hne)).1.T⟩,
      (stepE M c s t st.base (lbott c ε s t st.g st.h st.T hne)).2)
  else (st, true)

/-- **The invariant of the perturbed run.** -/
structure LInv (st : LSt M) : Prop where
  base : Inv c s t st.base
  antisymm : M.IsAntisymm st.h
  cons : ∀ v, v ≠ s → v ≠ t → M.div st.h v = 0
  lex : ∀ d, st.g d = c d → st.h d ≤ ε d
  sat : ∀ x, x ≠ st.T.root → st.h (st.T.par x) = ε (st.T.par x)

section Step

variable {c ε s t}

/-- The values of the path of the cotree are `-1`, `0` or `1`. -/
lemma chi_cases (hM : M.IsPlane) (T : DTree M) (d : D) :
    T.chi s t d = 1 ∨ T.chi s t d = 0 ∨ T.chi s t d = -1 := by
  obtain ⟨hχa, -, -, hχle⟩ := T.chi_spec hM s t
  have h1 := hχle d
  have h2 := hχle (M.rev d)
  rw [hχa d] at h2
  omega

lemma lstep_of_ne {st : LSt M} (hne : (pathSet s t st.T).Nonempty) :
    lstep M c ε s t st =
      (⟨(stepE M c s t st.base (lbott c ε s t st.g st.h st.T hne)).1.g,
        aug st.h (st.T.chi s t)
          (ε (lbott c ε s t st.g st.h st.T hne) - st.h (lbott c ε s t st.g st.h st.T hne)),
        (stepE M c s t st.base (lbott c ε s t st.g st.h st.T hne)).1.T⟩,
        (stepE M c s t st.base (lbott c ε s t st.g st.h st.T hne)).2) := by
  simp [lstep, hne]

lemma lstep_base_of_ne {st : LSt M} (hne : (pathSet s t st.T).Nonempty) :
    (lstep M c ε s t st).1.base = (stepE M c s t st.base (lbott c ε s t st.g st.h st.T hne)).1 ∧
      (lstep M c ε s t st).2 = (stepE M c s t st.base (lbott c ε s t st.g st.h st.T hne)).2 := by
  rw [lstep_of_ne hne]; exact ⟨rfl, rfl⟩

/-- **The perturbed step keeps the invariant.** -/
theorem lstep_inv (hM : M.IsPlane) {st : LSt M} (hI : LInv c ε s t st) :
    LInv c ε s t (lstep M c ε s t st).1 := by
  by_cases hne : (pathSet s t st.T).Nonempty
  swap
  · simpa [lstep, hne] using hI
  rw [lstep_of_ne hne]
  generalize he : lbott c ε s t st.g st.h st.T hne = e
  have hb : IsBott c s t st.g st.T e := he ▸ lbott_isBott c ε s t st.g st.h st.T hne
  have hmin : ∀ d, st.T.chi s t d = 1 → lslack c ε st.g st.h e ≤ lslack c ε st.g st.h d :=
    fun d hd => he ▸ lbott_min c ε s t st.g st.h st.T hne hd
  have hinv := stepE_inv hM hI.base hb
  obtain ⟨hχa, hχdiv, hχoff, -⟩ := st.T.chi_spec hM s t
  have hg : (stepE M c s t st.base e).1.g = aug st.g (st.T.chi s t) (c e - st.g e) :=
    stepE_g st.base e
  have hδ : 0 ≤ c e - st.g e := by have := hI.base.pseudo.le_cap e; simp [LSt.base] at this; omega
  refine ⟨hinv, fun d => ?_, fun v hs ht => ?_, fun d hd => ?_, fun x hx => ?_⟩
  · simp only [aug, hI.antisymm d, hχa d]; ring
  · rw [div_aug, hI.cons v hs ht, hχdiv]; simp [Ne.symm hs, Ne.symm ht]
  · simp only at hd ⊢
    rw [hg] at hd
    simp only [aug] at hd ⊢
    rcases chi_cases hM st.T d (s := s) (t := t) with h1 | h1 | h1 <;> rw [h1] at hd ⊢
    · -- a dart of the path: a tie with the bottleneck
      have := hmin d h1
      rw [lslack, lslack, Prod.Lex.toLex_le_toLex'] at this
      have := this.2 (by simp only; omega)
      simp only at this
      linarith
    · simp only [mul_zero, add_zero] at hd ⊢; exact hI.lex d hd
    · -- a reversed dart of the path: the bottleneck was saturated
      have hle := hI.base.pseudo.le_cap d
      simp only [LSt.base] at hle
      have hδ0 : c e - st.g e = 0 := by omega
      have hge : st.g e = c e := by omega
      have h2 := hI.lex e hge
      have h3 := hI.lex d (by omega)
      linarith
  · simp only at hx ⊢
    cases hb2 : (stepE M c s t st.base e).2
    · obtain ⟨-, -, hroot', hpar', -⟩ := stepE_facts hb2
      rw [hroot'] at hx
      rw [hpar']
      split_ifs with hxb
      · simp only [aug, hb.1]; ring
      · simp only [LSt.base_T] at hx
        simp only [aug, LSt.base_T, hχoff _ (st.T.inT_par hx), mul_zero, add_zero]
        exact hI.sat x hx
    · have hT : (stepE M c s t st.base e).1.T = st.T := by
        unfold stepE at hb2 ⊢; split_ifs at hb2 ⊢; simp_all
      rw [hT] at hx ⊢
      simp only [aug, hχoff _ (st.T.inT_par hx), mul_zero, add_zero]
      exact hI.sat x hx

end Step

/-! ### The run -/

variable (M) in
/-- **The perturbed run** with at most `n` steps: the final state, the number of steps, and
whether the algorithm stopped. -/
noncomputable def lrun : ℕ → LSt M → LSt M × ℕ × Bool
  | 0, st => (st, 0, false)
  | n + 1, st =>
    if (lstep M c ε s t st).2 then ((lstep M c ε s t st).1, 1, true)
    else ((lrun n (lstep M c ε s t st).1).1, (lrun n (lstep M c ε s t st).1).2.1 + 1,
      (lrun n (lstep M c ε s t st).1).2.2)

section Run

variable {c ε s t}

theorem lrun_inv (hM : M.IsPlane) :
    ∀ n (st : LSt M), LInv c ε s t st → LInv c ε s t (lrun M c ε s t n st).1
  | 0, _, hI => hI
  | n + 1, st, hI => by
    unfold lrun
    split_ifs
    · exact lstep_inv hM hI
    · exact lrun_inv hM n _ (lstep_inv hM hI)

/-- **When the perturbed step stops, no residual path leads from `s` to `t`.** -/
theorem lstep_noPath (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} (hI : LInv c ε s t st)
    (hdone : (lstep M c ε s t st).2 = true) :
    ¬ Relation.ReflTransGen (ResAdj M c (lstep M c ε s t st).1.g) s t := by
  have hne := pathSet_nonempty hM hst st.T (s := s) (t := t)
  obtain ⟨h1, h2⟩ := lstep_base_of_ne (c := c) (ε := ε) hne
  have key := stepE_noPath hM hI.base (lbott_isBott c ε s t st.g st.h st.T hne) (h2 ▸ hdone)
  have hg : (lstep M c ε s t st).1.g =
      (stepE M c s t st.base (lbott c ε s t st.g st.h st.T hne)).1.g := congrArg St.g h1
  rw [hg]
  exact key

/-- **A perturbed step that does not stop raises the levels.** -/
theorem lstep_pot (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} {P : D → ℤ}
    (hP : IsUnit (M := M) (s := s) (t := t) P) (hdone : (lstep M c ε s t st).2 = false) :
    pot P st.T + 1 ≤ pot P (lstep M c ε s t st).1.T ∧
      (lstep M c ε s t st).1.T.root = st.T.root := by
  have hne := pathSet_nonempty hM hst st.T (s := s) (t := t)
  obtain ⟨h1, h2⟩ := lstep_base_of_ne (c := c) (ε := ε) hne
  have key := stepE_pot hM (lbott_mem c ε s t st.g st.h st.T hne) hP (h2 ▸ hdone)
  have hT : (lstep M c ε s t st).1.T =
      (stepE M c s t st.base (lbott c ε s t st.g st.h st.T hne)).1.T := congrArg St.T h1
  rw [hT]
  exact key

theorem lrun_noPath (hM : M.IsPlane) (hst : s ≠ t) : ∀ n (st : LSt M), LInv c ε s t st →
    (lrun M c ε s t n st).2.2 = true →
    ¬ Relation.ReflTransGen (ResAdj M c (lrun M c ε s t n st).1.g) s t
  | 0, _, _, h => by simp [lrun] at h
  | n + 1, st, hI, h => by
    unfold lrun at h ⊢
    split_ifs at h ⊢ with hd
    · exact lstep_noPath hM hst hI hd
    · exact lrun_noPath hM hst n _ (lstep_inv hM hI) h

theorem lrun_pot (hM : M.IsPlane) (hst : s ≠ t) {P : D → ℤ}
    (hP : IsUnit (M := M) (s := s) (t := t) P) :
    ∀ n (st : LSt M), (lrun M c ε s t n st).2.2 = false →
      pot P st.T + n ≤ pot P (lrun M c ε s t n st).1.T
  | 0, _, _ => by simp [lrun]
  | n + 1, st, h => by
    unfold lrun at h ⊢
    split_ifs at h ⊢ with hd
    · have h1 := (lstep_pot hM hst hP (by simpa using hd)).1
      have h2 := lrun_pot hM hst hP n _ h
      simp only; push_cast; linarith

theorem lrun_steps_le : ∀ n (st : LSt M), (lrun M c ε s t n st).2.1 ≤ n
  | 0, _ => by simp [lrun]
  | n + 1, st => by
    unfold lrun
    split_ifs
    · simp
    · have := lrun_steps_le n (lstep M c ε s t st).1; simp only; omega

/-- **The perturbed run stops** within `2 F² + 1` steps. -/
theorem lrun_done (hM : M.IsPlane) (hst : s ≠ t) {P : D → ℤ}
    (hP : IsUnit (M := M) (s := s) (t := t) P) (st : LSt M) {n : ℕ}
    (hn : 2 * Fintype.card F * Fintype.card F < n) :
    (lrun M c ε s t n st).2.2 = true := by
  by_contra h
  have h1 := lrun_pot hM hst hP n st (by simpa using h)
  have h2 := abs_pot_le hP st.T
  have h3 := abs_pot_le hP (lrun M c ε s t n st).1.T
  rw [abs_le] at h2 h3
  have : (n : ℤ) > 2 * Fintype.card F * Fintype.card F := by exact_mod_cast hn
  linarith

/-- **Correctness of the perturbed run**: from a state satisfying the invariant, with enough
steps, the run stops with a pseudoflow conserved off `s` and `t` and no residual path from `s` to
`t`. -/
theorem lrun_spec (hM : M.IsPlane) (hst : s ≠ t) {P : D → ℤ}
    (hP : IsUnit (M := M) (s := s) (t := t) P) {st : LSt M} (hI : LInv c ε s t st) {n : ℕ}
    (hn : 2 * Fintype.card F * Fintype.card F < n) :
    IsPseudo M c (lrun M c ε s t n st).1.g ∧
      (∀ v, v ≠ s → v ≠ t → M.div (lrun M c ε s t n st).1.g v = 0) ∧
      NoPath M c (lrun M c ε s t n st).1.g {s} {t} := by
  have hI' := lrun_inv hM n st hI
  refine ⟨hI'.base.pseudo, hI'.base.cons, (noPath_iff hI'.base.pseudo).2 fun a ha b hb => ?_⟩
  rw [mem_singleton] at ha hb
  subst ha hb
  exact lrun_noPath hM hst n st hI (lrun_done hM hst hP st hn)

end Run

/-! ### The initial state -/

section Init

variable {c ε}

lemma DTree.psum_smul (T : DTree M) (N : ℤ) (φ : D → ℤ) (x : F) :
    T.psum (fun d => N * φ d) x = N * T.psum φ x := by
  simp [DTree.psum, mul_sum]

lemma DTree.psum_nonneg (T : DTree M) {φ : D → ℤ} (h : ∀ d, 0 ≤ φ d) (x : F) :
    0 ≤ T.psum φ x :=
  sum_nonneg fun _ _ => h _

lemma DTree.psum_le (T : DTree M) {φ : D → ℤ} (h : ∀ d, 0 ≤ φ d) (x : F) :
    T.psum φ x ≤ Fintype.card F * ∑ d, φ d := by
  unfold DTree.psum
  calc ∑ i ∈ range (T.depth x), φ (T.par (T.up^[i] x))
      ≤ ∑ _i ∈ range (T.depth x), ∑ d, φ d :=
        sum_le_sum fun i _ => single_le_sum (fun d _ => h d) (mem_univ _)
    _ = T.depth x * ∑ d, φ d := by simp
    _ ≤ Fintype.card F * ∑ d, φ d := by
        have h1 := T.depth_lt_card x
        have h2 : 0 ≤ ∑ d, φ d := sum_nonneg fun d _ => h d
        have h3 : (T.depth x : ℤ) ≤ Fintype.card F := by exact_mod_cast h1.le
        nlinarith

/-- **The initial state of the perturbed run**: a shortest-path tree of the dual for the lengths
`N c + ε` with `N = (F + 1) Σ ε + 1`, which is a shortest-path tree for the lexicographic lengths
`(c, ε)`, and the coboundaries of its path sums as the flows. -/
theorem exists_linit (hM : M.IsPlane) [Nonempty D] (hc : ∀ d, 0 ≤ c d) (hε : ∀ d, 0 ≤ ε d)
    (s t : V) (o : F) :
    ∃ st : LSt M, st.T.root = o ∧ LInv c ε s t st ∧ st.g = M.cob (st.T.psum c) ∧
      st.h = M.cob (st.T.psum ε) := by
  set E := ∑ d, ε d with hE
  set N : ℤ := (Fintype.card F + 1) * E + 1 with hN
  have hE0 : 0 ≤ E := sum_nonneg fun d _ => hε d
  have hc' : ∀ d, 0 ≤ N * c d + ε d := fun d => by
    have : 0 ≤ N := by nlinarith
    have := hc d; have := hε d; nlinarith
  obtain ⟨φ, par, hpot, htight, hreach⟩ := exists_spt hM hc' o
  let T : DTree M := ⟨o, par, fun x hx => (htight x hx).1, hreach⟩
  -- the distances are the path sums
  have hφ : ∀ x, φ x - φ o = T.psum (fun d => N * c d + ε d) x := fun x =>
    T.psum_unique _ (k := fun x => φ x - φ o) (by simp [T]) (fun y hy => by
      have h1 := (htight y hy).2
      simp only [cob, (htight y hy).1] at h1
      have : T.up y = M.face (par y) := T.up_of_ne hy
      simp only [this]
      show φ y - φ o = φ (M.face (par y)) - φ o + (N * c (par y) + ε (par y))
      linarith) x
  have hsplit : ∀ x, T.psum (fun d => N * c d + ε d) x = N * T.psum c x + T.psum ε x := by
    intro x
    have : (fun d => N * c d + ε d) = (fun d => N * c d) + ε := rfl
    rw [this, DTree.psum_add, DTree.psum_smul]
  refine ⟨⟨M.cob (T.psum c), M.cob (T.psum ε), T⟩, rfl, ?_, rfl, rfl⟩
  -- the perturbation part of the slack is small
  have hsmall : ∀ d, |ε d - M.cob (T.psum ε) d| < N := by
    intro d
    have h1 := T.psum_nonneg hε (M.face d)
    have h2 := T.psum_nonneg hε (M.face (M.rev d))
    have h3 := T.psum_le hε (M.face d)
    have h4 := T.psum_le hε (M.face (M.rev d))
    have h5 : ε d ≤ E := single_le_sum (fun d _ => hε d) (mem_univ d)
    have h6 := hε d
    simp only [cob]
    rw [abs_lt]
    constructor <;> nlinarith
  -- the slack for `N c + ε` is nonnegative
  have hfeas : ∀ d, 0 ≤ N * (c d - M.cob (T.psum c) d) + (ε d - M.cob (T.psum ε) d) := by
    intro d
    have h1 := hpot d
    have h2 := hφ (M.face d)
    have h3 := hφ (M.face (M.rev d))
    rw [hsplit] at h2 h3
    simp only [cob] at h1 ⊢
    nlinarith
  have hle : ∀ d, M.cob (T.psum c) d ≤ c d := by
    intro d
    by_contra h
    have h1 := hfeas d
    have h2 := (abs_lt.1 (hsmall d)).2
    have hN0 : 0 < N := by rw [hN]; positivity
    have : N * (c d - M.cob (T.psum c) d) ≤ -N := by
      have : c d - M.cob (T.psum c) d ≤ -1 := by omega
      nlinarith
    linarith
  have hsatc : ∀ x, x ≠ o → M.cob (T.psum c) (par x) = c (par x) := fun x hx => by
    have h := T.psum_of_ne c (x := x) hx
    simp only [cob, (htight x hx).1]
    rw [T.up_of_ne hx] at h
    show T.psum c x - T.psum c (M.face (par x)) = c (par x)
    linarith
  have hsate : ∀ x, x ≠ o → M.cob (T.psum ε) (par x) = ε (par x) := fun x hx => by
    have h := T.psum_of_ne ε (x := x) hx
    simp only [cob, (htight x hx).1]
    rw [T.up_of_ne hx] at h
    show T.psum ε x - T.psum ε (M.face (par x)) = ε (par x)
    linarith
  refine ⟨⟨⟨M.cob_antisymm _, hle⟩, fun v _ _ => M.div_cob _ v, hsatc⟩, M.cob_antisymm _,
    fun v _ _ => M.div_cob _ v, fun d hd => ?_, hsate⟩
  have h1 := hfeas d
  simp only at hd
  rw [hd, sub_self, mul_zero, zero_add] at h1
  linarith

variable (M) in
open Classical in
/-- The initial state of the perturbed run (a choice; `none` when the hypotheses fail). -/
noncomputable def linit (c ε : D → ℤ) (s t : V) (o : F) : Option (LSt M) :=
  if h : ∃ st : LSt M, st.T.root = o ∧ LInv c ε s t st ∧ st.g = M.cob (st.T.psum c) ∧
      st.h = M.cob (st.T.psum ε) then some h.choose else none

lemma linit_spec (hM : M.IsPlane) [Nonempty D] (hc : ∀ d, 0 ≤ c d) (hε : ∀ d, 0 ≤ ε d)
    (s t : V) (o : F) :
    ∃ st, linit M c ε s t o = some st ∧ st.T.root = o ∧ LInv c ε s t st ∧
      st.g = M.cob (st.T.psum c) ∧ st.h = M.cob (st.T.psum ε) := by
  have h := exists_linit hM hc hε s t o
  exact ⟨h.choose, by simp [linit, h], h.choose_spec⟩

lemma linit_inv {o : F} {st : LSt M} (h : linit M c ε s t o = some st) :
    st.T.root = o ∧ LInv c ε s t st := by
  unfold linit at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  exact ⟨hex.choose_spec.1, hex.choose_spec.2.1⟩

end Init

/-! ### The perturbed implementation -/

/-- The base of the perturbation: `4 F + 5`. -/
def lexBase (F' : Type*) [Fintype F'] : ℕ := 4 * Fintype.card F' + 5

/-- **The perturbation of the capacities**: the dart of index `i` gets `(4 F + 5) ^ i`. -/
noncomputable def lexEps (D' F' : Type*) [Fintype D'] [Fintype F'] (d : D') : ℤ :=
  (lexBase F' : ℤ) ^ (Fintype.equivFin D' d : ℕ)

lemma lexEps_nonneg (d : D) : 0 ≤ lexEps D F d := by
  unfold lexEps lexBase; positivity

variable (M) in
/-- **The perturbed single-source single-sink algorithm**: the perturbed run from the initial
shortest-path tree of the dual rooted at `o`. -/
noncomputable def pcoreRun (c : D → ℤ) (s t : V) (o : F) : Option (LSt M × ℕ × Bool) :=
  (linit M c (lexEps D F) s t o).map (lrun M c (lexEps D F) s t (fuel F))

variable (M) in
/-- The flow computed by `pcoreRun`. -/
noncomputable def pcoreFlow (c : D → ℤ) (s t : V) (o : F) : D → ℤ :=
  match pcoreRun M c s t o with
  | some r => r.1.g
  | none => 0

/-- **Correctness of the perturbed single-source single-sink algorithm.** -/
theorem pcoreFlow_spec (hM : M.IsPlane) [Nonempty D] {c : D → ℤ} (hc : ∀ d, 0 ≤ c d)
    {s t : V} (hst : s ≠ t) (o : F) :
    IsPseudo M c (pcoreFlow M c s t o) ∧
      (∀ v, v ≠ s → v ≠ t → M.div (pcoreFlow M c s t o) v = 0) ∧
      NoPath M c (pcoreFlow M c s t o) {s} {t} := by
  obtain ⟨st, hst0, -, hI, -⟩ := linit_spec hM hc (fun d => lexEps_nonneg (F := F) d) s t o
  obtain ⟨h1, h2, -, h4⟩ := st.T.chi_spec hM s t
  have hP : IsUnit (M := M) (s := s) (t := t) (st.T.chi s t) := ⟨h1, h2, h4⟩
  have := lrun_spec hM hst hP hI (n := fuel F) (by unfold fuel; omega)
  simpa [pcoreFlow, pcoreRun, hst0] using this

variable (M) in
open Classical in
/-- **SingleSourceSingleSinkMaxFlow with perturbed capacities**, from the vertex set `X` to the
vertex set `Y`: as `stflow`, with the perturbed algorithm on the contracted capacities. -/
noncomputable def pstflow (c : D → ℤ) (X Y : Finset V) : D → ℤ :=
  if h : X.Nonempty ∧ ∃ d, M.tail d ∈ Y then
    restrictR M X Y
      (pcoreFlow M (capR M c X Y) h.1.choose (M.tail h.2.choose) (M.face h.2.choose))
  else 0

/-- **The perturbed implementation meets `STFlowSpec`** on every plane map. -/
theorem pstflow_spec (hM : M.IsPlane) : STFlowSpec M (pstflow M) := by
  classical
  intro c πs πt hc hXY
  have hXne : πs.verts.Nonempty := ⟨_, πs.p_mem_init (Nat.zero_le _)⟩
  have hY : (πt.p 0) ∈ πt.verts := πt.p_mem_init (Nat.zero_le _)
  have hne : πs.p 0 ≠ πt.p 0 := fun h => disjoint_left.1 hXY (πs.p_mem_init (Nat.zero_le _))
    (h ▸ hY)
  obtain ⟨d₀, hd₀⟩ := exists_dart_tail hM hne
  have hex : πs.verts.Nonempty ∧ ∃ d, M.tail d ∈ πt.verts := ⟨hXne, d₀, hd₀ ▸ hY⟩
  have : Nonempty D := ⟨d₀⟩
  unfold pstflow
  simp only [hex, and_self, ↓reduceDIte]
  have hs := hex.1.choose_spec
  have ht := hex.2.choose_spec
  have hst : hex.1.choose ≠ M.tail hex.2.choose := fun h => disjoint_left.1 hXY hs (h ▸ ht)
  obtain ⟨h1, h2, h3⟩ := pcoreFlow_spec hM (capR_nonneg (M := M) hc πs.verts πt.verts) hst
    (M.face hex.2.choose)
  exact stOut_restrictR hc πs πt hXY hs ht h1 h2 h3

end STFlow

end PlanarFlow
