module

public import PlanarFlow.BKMNW.Hassin

/-!
# Simple paths and the boosted capacities of the fixing procedure

The fixing procedure of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput.
46(4), 2017, Section 3, Algorithm 2) works along a simple path `p 0, …, p k` with darts
`d j : p j → p (j + 1)` (`SPath`). It first raises the capacities of the darts of the path and
of their reverses by a large constant `Mb`, then lowers them back one dart at a time
(`SPath.cap c Mb i`: the darts `d j`, `rev (d j)` with `j ≥ i` are raised).

The correctness of the procedure needs that a raised dart is never saturated (a residual path can
always follow the unprocessed part of the path). The article takes `Mb` to be the sum of the
capacities and leaves this point implicit. We take `Mb = 4 N + 1`, with `N` the sum of the
absolute values of the capacities, and prove it (`SPath.abs_lt_boost`): the darts leaving
`{p 0, …, p j}` are `d j` and darts off the path, whose flow is at most `2 N` in total, and the
net outflow of this set is that of the initial flow (`≤ 2 N`), because the procedure has only
moved flow between `p t` and `p (t + 1)` for `t < j`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable {M : CombMap D V F}

variable (M) in
/-- A simple path of `k` darts `d 0, …, d (k - 1)` through the distinct vertices
`p 0, …, p k`. -/
structure SPath where
  /-- The number of darts. -/
  k : ℕ
  /-- The darts. -/
  d : ℕ → D
  /-- The vertices. -/
  p : ℕ → V
  tail_d : ∀ j < k, M.tail (d j) = p j
  head_d : ∀ j < k, M.head (d j) = p (j + 1)
  inj : ∀ i ≤ k, ∀ j ≤ k, p i = p j → i = j

namespace SPath

variable (P : SPath M)

/-- The darts of the path and their reverses. -/
def darts : List D := (List.range P.k).flatMap fun j => [P.d j, M.rev (P.d j)]

lemma mem_darts {e : D} : e ∈ P.darts ↔ ∃ j < P.k, e = P.d j ∨ e = M.rev (P.d j) := by
  simp only [darts, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false]

lemma d_mem (j : ℕ) (hj : j < P.k) : P.d j ∈ P.darts := P.mem_darts.2 ⟨j, hj, Or.inl rfl⟩

lemma rev_d_mem (j : ℕ) (hj : j < P.k) : M.rev (P.d j) ∈ P.darts :=
  P.mem_darts.2 ⟨j, hj, Or.inr rfl⟩

lemma rev_mem_darts {e : D} (he : e ∈ P.darts) : M.rev e ∈ P.darts := by
  obtain ⟨j, hj, rfl | rfl⟩ := P.mem_darts.1 he
  · exact P.rev_d_mem j hj
  · rw [M.rev_rev]; exact P.d_mem j hj

/-- The faces along the path: the faces of its darts and of their reverses. -/
def faces [DecidableEq F] : Finset F := (P.darts.map M.face).toFinset

lemma face_mem [DecidableEq F] {e : D} (he : e ∈ P.darts) : M.face e ∈ P.faces := by
  simp only [faces, List.mem_toFinset, List.mem_map]; exact ⟨e, he, rfl⟩

/-- The path has `2 k` darts, with their reverses. -/
lemma length_darts : P.darts.length = 2 * P.k := by
  simp only [darts, List.length_flatMap, List.length_cons, List.length_nil, zero_add,
    Nat.reduceAdd, List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  ring

/-- At most `2 k` faces lie along the path. -/
lemma card_faces_le [DecidableEq F] : P.faces.card ≤ 2 * P.k :=
  (List.toFinset_card_le _).trans (by rw [List.length_map, P.length_darts])

lemma d_inj {i j : ℕ} (hi : i < P.k) (hj : j < P.k) (h : P.d i = P.d j) : i = j :=
  P.inj i hi.le j hj.le (by rw [← P.tail_d i hi, ← P.tail_d j hj, h])

lemma d_ne_rev {i j : ℕ} (hi : i < P.k) (hj : j < P.k) : P.d i ≠ M.rev (P.d j) := by
  intro h
  have h1 : P.p i = P.p (j + 1) := by
    rw [← P.tail_d i hi, ← P.head_d j hj, h, M.tail_rev]
  have h2 : P.p (i + 1) = P.p j := by
    rw [← P.head_d i hi, ← P.tail_d j hj, h, M.head_rev]
  have e1 := P.inj i hi.le (j + 1) hj h1
  have e2 := P.inj (i + 1) hi j hj.le h2
  omega

/-- The vertices `p 0, …, p j`. -/
def init (j : ℕ) : Finset V := (range (j + 1)).image P.p

/-- The vertices of the path. -/
def verts : Finset V := P.init P.k

lemma mem_init {j : ℕ} {v : V} : v ∈ P.init j ↔ ∃ t ≤ j, P.p t = v := by
  simp [init]

lemma p_mem_init {t j : ℕ} (h : t ≤ j) : P.p t ∈ P.init j := P.mem_init.2 ⟨t, h, rfl⟩

lemma p_mem_init_iff {t j : ℕ} (ht : t ≤ P.k) (hj : j ≤ P.k) : P.p t ∈ P.init j ↔ t ≤ j := by
  constructor
  · intro h
    obtain ⟨s, hs, e⟩ := P.mem_init.1 h
    have := P.inj s (hs.trans hj) t ht e; omega
  · exact P.p_mem_init

/-- **The only dart of the path leaving `{p 0, …, p j}`** is `d j`. -/
lemma out_init {j : ℕ} (hj : j < P.k) {e : D} (he : e ∈ P.darts) (h1 : M.tail e ∈ P.init j)
    (h2 : M.head e ∉ P.init j) : e = P.d j := by
  obtain ⟨t, ht, rfl | rfl⟩ := P.mem_darts.1 he
  · rw [P.tail_d t ht, P.p_mem_init_iff ht.le hj.le] at h1
    rw [P.head_d t ht, P.p_mem_init_iff ht hj.le] at h2
    rw [show t = j by omega]
  · rw [M.tail_rev, P.head_d t ht, P.p_mem_init_iff ht hj.le] at h1
    rw [M.head_rev, P.tail_d t ht, P.p_mem_init_iff ht.le hj.le] at h2
    omega

/-! ### Boosted capacities -/

/-- The darts raised at stage `i`: `d j` and `rev (d j)` for `i ≤ j < k`. -/
def Boost (i : ℕ) (e : D) : Prop := ∃ j, i ≤ j ∧ j < P.k ∧ (e = P.d j ∨ e = M.rev (P.d j))

/-- The capacities at stage `i`: raised by `Mb` on the darts `d j`, `rev (d j)`, `j ≥ i`. -/
noncomputable def cap (c : D → ℤ) (Mb : ℤ) (i : ℕ) (e : D) : ℤ := by
  classical exact if P.Boost i e then c e + Mb else c e

lemma boost_mem {i : ℕ} {e : D} (h : P.Boost i e) : e ∈ P.darts := by
  obtain ⟨j, -, hj, h⟩ := h; exact P.mem_darts.2 ⟨j, hj, h⟩

lemma cap_of_not_mem (c : D → ℤ) (Mb : ℤ) (i : ℕ) {e : D} (he : e ∉ P.darts) :
    P.cap c Mb i e = c e := by
  unfold cap
  split_ifs with h
  · exact absurd (P.boost_mem h) he
  · rfl

lemma boost_d {i j : ℕ} (hij : i ≤ j) (hj : j < P.k) : P.Boost i (P.d j) := ⟨j, hij, hj, Or.inl rfl⟩

lemma boost_rev_d {i j : ℕ} (hij : i ≤ j) (hj : j < P.k) : P.Boost i (M.rev (P.d j)) :=
  ⟨j, hij, hj, Or.inr rfl⟩

lemma not_boost_d {i j : ℕ} (hij : j < i) (hj : j < P.k) : ¬ P.Boost i (P.d j) := by
  rintro ⟨t, ht, htk, h | h⟩
  · have := P.d_inj hj htk h; omega
  · exact P.d_ne_rev hj htk h

lemma not_boost_rev_d {i j : ℕ} (hij : j < i) (hj : j < P.k) : ¬ P.Boost i (M.rev (P.d j)) := by
  rintro ⟨t, ht, htk, h | h⟩
  · exact P.d_ne_rev htk hj h.symm
  · have := P.d_inj hj htk (M.rev_injective h); omega

lemma cap_d (c : D → ℤ) (Mb : ℤ) {i j : ℕ} (hj : j < P.k) :
    P.cap c Mb i (P.d j) = if i ≤ j then c (P.d j) + Mb else c (P.d j) := by
  unfold cap
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (P.not_boost_d (by omega) hj)
  · exact absurd (P.boost_d h2 hj) h1
  · rfl

lemma cap_rev_d (c : D → ℤ) (Mb : ℤ) {i j : ℕ} (hj : j < P.k) :
    P.cap c Mb i (M.rev (P.d j)) =
      if i ≤ j then c (M.rev (P.d j)) + Mb else c (M.rev (P.d j)) := by
  unfold cap
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 (P.not_boost_rev_d (by omega) hj)
  · exact absurd (P.boost_rev_d h2 hj) h1
  · rfl

/-- Lowering the capacities of `d i` and `rev (d i)`: from stage `i` to stage `i + 1`, only these
two capacities change. -/
lemma cap_succ (c : D → ℤ) (Mb : ℤ) {i : ℕ} (hi : i < P.k) {e : D} (he : e ≠ P.d i)
    (he' : e ≠ M.rev (P.d i)) : P.cap c Mb (i + 1) e = P.cap c Mb i e := by
  unfold cap
  have : P.Boost (i + 1) e ↔ P.Boost i e := by
    constructor
    · rintro ⟨j, hj, hjk, h⟩; exact ⟨j, by omega, hjk, h⟩
    · rintro ⟨j, hj, hjk, h⟩
      refine ⟨j, ?_, hjk, h⟩
      by_contra hne
      have : j = i := by omega
      subst this
      rcases h with h | h
      · exact he h
      · exact he' h
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (this.1 h1) h2
  · exact absurd (this.2 h2) h1
  · rfl

lemma cap_k (c : D → ℤ) (Mb : ℤ) : P.cap c Mb P.k = c := by
  funext e; unfold cap
  split_ifs with h
  · obtain ⟨j, h1, h2, -⟩ := h; omega
  · rfl

lemma le_cap_zero (c : D → ℤ) {Mb : ℤ} (hMb : 0 ≤ Mb) (i : ℕ) (e : D) : c e ≤ P.cap c Mb i e := by
  unfold cap; split_ifs <;> omega

lemma cap_succ_le (c : D → ℤ) {Mb : ℤ} (hMb : 0 ≤ Mb) (i : ℕ) (e : D) :
    P.cap c Mb (i + 1) e ≤ P.cap c Mb i e := by
  unfold cap
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; obtain ⟨j, hj, hjk, h⟩ := h1; exact h2 ⟨j, by omega, hjk, h⟩
  · omega
  · rfl

/-! ### The raised darts are never saturated -/

/-- The sum of the absolute values of the capacities. -/
def absSum (c : D → ℤ) : ℤ := ∑ e, |c e|

lemma absSum_nonneg (c : D → ℤ) : 0 ≤ absSum c := sum_nonneg fun e _ => abs_nonneg _

lemma sum_abs_rev (c : D → ℤ) : ∑ e, |c (M.rev e)| = absSum c := by
  have hbij : Function.Bijective M.rev := M.rev_injective.bijective_of_finite
  exact sum_equiv (Equiv.ofBijective _ hbij) (by simp) (fun _ _ => rfl)

/-- A pseudoflow is bounded by the capacities of a dart and of its reverse. -/
lemma abs_le_of_pseudo {u g : D → ℤ} (hg : IsPseudo M u g) (e : D) :
    |g e| ≤ |u e| + |u (M.rev e)| := by
  have h1 := hg.le_cap e
  have h2 := hg.le_cap (M.rev e)
  rw [hg.antisymm e] at h2
  rw [abs_le]; constructor
  · have := le_abs_self (u (M.rev e)); have := abs_nonneg (u e); linarith
  · have := le_abs_self (u e); have := abs_nonneg (u (M.rev e)); linarith

lemma sum_filter_abs_le {S : Finset D} (h : D → ℤ) : |∑ e ∈ S, h e| ≤ ∑ e, |h e| :=
  (abs_sum_le_sum_abs _ _).trans (sum_le_sum_of_subset_of_nonneg (subset_univ _)
    fun _ _ _ => abs_nonneg _)

/-- **A raised dart is never saturated**, as long as the net outflow of `{p 0, …, p j}` is that
of the initial pseudoflow `f₀`: its flow is at most `4 N` in absolute value. -/
theorem abs_le_boost {c f₀ g : D → ℤ} {Mb : ℤ} {i : ℕ} (hf₀ : IsPseudo M c f₀)
    (hg : IsPseudo M (P.cap c Mb i) g) {j : ℕ} (hj : j < P.k)
    (hsum : ∑ v ∈ P.init j, M.div g v = ∑ v ∈ P.init j, M.div f₀ v) :
    |g (P.d j)| ≤ 4 * absSum c := by
  classical
  -- the darts leaving the set
  have hout : ∑ v ∈ P.init j, M.div g v =
      g (P.d j) + ∑ e with (M.tail e ∈ P.init j ∧ M.head e ∉ P.init j) ∧ e ∉ P.darts, g e := by
    rw [sum_div_eq_out hg.antisymm, ← sum_filter_add_sum_filter_not _ (fun e => e ∈ P.darts)]
    congr 1
    rw [sum_eq_single (P.d j)]
    · intro e he hne
      simp only [mem_filter, mem_univ, true_and] at he
      exact absurd (P.out_init hj he.2 he.1.1 he.1.2) hne
    · intro h; exfalso; apply h
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, P.d_mem j hj⟩
      · rw [P.tail_d j hj]; exact P.p_mem_init le_rfl
      · rw [P.head_d j hj, P.p_mem_init_iff hj hj.le]; omega
    · simp only [filter_filter]
  have h1 : |∑ v ∈ P.init j, M.div f₀ v| ≤ 2 * absSum c := by
    rw [sum_div_eq_out hf₀.antisymm]
    refine (sum_filter_abs_le f₀).trans ?_
    calc ∑ e, |f₀ e| ≤ ∑ e, (|c e| + |c (M.rev e)|) := sum_le_sum fun e _ => abs_le_of_pseudo hf₀ e
      _ = 2 * absSum c := by rw [sum_add_distrib, sum_abs_rev]; unfold absSum; ring
  have h2 : |∑ e with (M.tail e ∈ P.init j ∧ M.head e ∉ P.init j) ∧ e ∉ P.darts, g e| ≤
      2 * absSum c := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ e with (M.tail e ∈ P.init j ∧ M.head e ∉ P.init j) ∧ e ∉ P.darts, |g e|
        ≤ ∑ e with (M.tail e ∈ P.init j ∧ M.head e ∉ P.init j) ∧ e ∉ P.darts,
            (|c e| + |c (M.rev e)|) := sum_le_sum fun e he => by
          simp only [mem_filter, mem_univ, true_and] at he
          have := abs_le_of_pseudo hg e
          rwa [P.cap_of_not_mem c Mb i he.2,
            P.cap_of_not_mem c Mb i fun h => he.2 (by simpa [M.rev_rev] using P.rev_mem_darts h)]
            at this
      _ ≤ ∑ e, (|c e| + |c (M.rev e)|) := sum_le_sum_of_subset_of_nonneg (subset_univ _)
          fun _ _ _ => by positivity
      _ = 2 * absSum c := by rw [sum_add_distrib, sum_abs_rev]; unfold absSum; ring
  rw [hsum] at hout
  have : g (P.d j) = ∑ v ∈ P.init j, M.div f₀ v -
      ∑ e with (M.tail e ∈ P.init j ∧ M.head e ∉ P.init j) ∧ e ∉ P.darts, g e := by linarith
  rw [this]
  calc _ ≤ |∑ v ∈ P.init j, M.div f₀ v| +
        |∑ e with (M.tail e ∈ P.init j ∧ M.head e ∉ P.init j) ∧ e ∉ P.darts, g e| := abs_sub _ _
    _ ≤ 4 * absSum c := by linarith

end SPath

end BKMNW

end PlanarFlow
