module

public import PlanarFlow.BKMNW.Path

/-!
# The fixing procedure: the invariant of Lemma B.1

This file proves the correctness of the abstract fixing procedure of Borradaile, Klein, Mozes,
Nussbaum and Wulff-Nilsen (SIAM J. Comput. 46(4), 2017, Section 3, Algorithm 2, Appendix B) at
the level of flows, whatever the subroutine computing the limited maximum flows.

Along a simple path `p 0, …, p k`, with the capacities raised by `Mb = 4 N + 1` on the darts of
the path that are not yet processed (`SPath.cap`), the stage `i` (for `i < k`):

1. lowers the capacities of `d i` and `rev (d i)` and clips the flow on them (`clip`);
2. pushes, from `p i` to `p (i + 1)` if `p i` has positive inflow (negative net outflow), and from
   `p (i + 1)` to `p i` otherwise, a maximum flow with limit the excess of `p i` (`LimPush`).

`FPInv i g` is the invariant of Lemma B.1 of the article after the stages `0, …, i - 1`, stated
with closed sets (`NoPath`); `FPInv.step` proves that a stage preserves it, and `FPInv.final`
gives the output property at the end: no residual path from the vertices of the path with
positive inflow to those with negative inflow.

Signs: the article's inflow is minus the net outflow `M.div`; *positive inflow* is
`M.div g v < 0`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Setting the flow on an edge -/

variable (M) in
/-- The flow `g` with the value `a` on `e` and `-a` on `rev e`. -/
def setPair (g : D → ℤ) (e : D) (a : ℤ) (e' : D) : ℤ :=
  if e' = e then a else if e' = M.rev e then -a else g e'

/-- `setPair` adds a multiple of the unit flow of `e`. -/
lemma setPair_eq {g : D → ℤ} (hg : M.IsAntisymm g) (e : D) (a : ℤ) :
    setPair M g e a =
      g + fun e' => (a - g e) * ((Pi.single e 1 - Pi.single (M.rev e) 1 : D → ℤ) e') := by
  funext e'
  have hne : M.rev e ≠ e := M.rev_ne e
  simp only [setPair, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases h1 : e' = e
  · subst h1; simp [hne.symm]
  · by_cases h2 : e' = M.rev e
    · subst h2; simp [hne, hg e]; ring
    · simp [h1, h2]

lemma setPair_antisymm {g : D → ℤ} (hg : M.IsAntisymm g) (e : D) (a : ℤ) :
    M.IsAntisymm (setPair M g e a) := by
  rw [setPair_eq hg]
  intro e'
  have := isAntisymm_dart (M := M) e e'
  simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
  rw [hg e', this]; ring

lemma div_setPair {g : D → ℤ} (hg : M.IsAntisymm g) (e : D) (a : ℤ) (v : V) :
    M.div (setPair M g e a) v = M.div g v +
      (a - g e) * ((if M.tail e = v then 1 else 0) - (if M.head e = v then 1 else 0)) := by
  rw [setPair_eq hg, div_add', div_smul, div_dart]

lemma setPair_self (g : D → ℤ) (e : D) (a : ℤ) : setPair M g e a e = a := by simp [setPair]

lemma setPair_rev (g : D → ℤ) (e : D) (a : ℤ) : setPair M g e a (M.rev e) = -a := by
  simp [setPair, M.rev_ne e]

lemma setPair_of_ne (g : D → ℤ) {e e' : D} (a : ℤ) (h1 : e' ≠ e) (h2 : e' ≠ M.rev e) :
    setPair M g e a e' = g e' := by
  simp [setPair, h1, h2]

/-! ### Closed sets under pushes -/

/-- The sum over a set of the net outflow of a push of `val` from `a` to `b`. -/
lemma sum_push (Y : Finset V) (a b : V) (val : ℤ) :
    ∑ v ∈ Y, val * ((if a = v then 1 else 0) - (if b = v then 1 else 0)) =
      val * ((if a ∈ Y then 1 else 0) - (if b ∈ Y then 1 else 0)) := by
  rw [← mul_sum, sum_sub_distrib, sum_ite_eq, sum_ite_eq]

/-- A closed set stays closed under a push from `a` to `b` if it contains `a` whenever it
contains `b`. -/
lemma Closed.of_push {u g g' : D → ℤ} {Y : Finset V} (hg : IsPseudo M u g)
    (hg' : IsPseudo M u g') (hY : Closed M u g Y) {a b : V} {val : ℤ} (hval : 0 ≤ val)
    (hdiv : ∀ v, M.div g' v =
      M.div g v + val * ((if a = v then 1 else 0) - (if b = v then 1 else 0)))
    (hab : b ∈ Y → a ∈ Y) : Closed M u g' Y := by
  refine hY.of_sum_le hg hg' ?_
  simp only [hdiv, sum_add_distrib, sum_push]
  have : 0 ≤ val * ((if a ∈ Y then 1 else 0) - (if b ∈ Y then 1 else 0)) := by
    apply mul_nonneg hval
    by_cases hb : b ∈ Y
    · simp [hb, hab hb]
    · simp only [hb, ite_false, sub_zero]; split_ifs <;> simp
  linarith

lemma NoPath.of_push {u g g' : D → ℤ} {A B : Finset V} (hg : IsPseudo M u g)
    (hg' : IsPseudo M u g') {a b : V} {val : ℤ} (hval : 0 ≤ val)
    (hdiv : ∀ v, M.div g' v =
      M.div g v + val * ((if a = v then 1 else 0) - (if b = v then 1 else 0)))
    (h : ∃ Y, A ⊆ Y ∧ Disjoint Y B ∧ Closed M u g Y ∧ (b ∈ Y → a ∈ Y)) : NoPath M u g' A B := by
  obtain ⟨Y, h1, h2, h3, h4⟩ := h
  exact ⟨Y, h1, h2, h3.of_push hg hg' hval hdiv h4⟩

lemma NoPath.of_res_le {u g u' g' : D → ℤ} {A B : Finset V} (h : NoPath M u g A B)
    (hg' : IsPseudo M u' g') (hle : ∀ d, u' d - g' d ≤ u d - g d) : NoPath M u' g' A B := by
  obtain ⟨Y, h1, h2, h3⟩ := h
  exact ⟨Y, h1, h2, h3.of_res_le hg' hle⟩

/-! ### The specification of a limited push -/

variable (M) in
/-- **A maximum flow with limit `x` from `a` to `b`** added to `g`: the result `g'` is a
pseudoflow, `val ∈ [0, x]` units go from `a` to `b`, and either the limit is reached or no
residual path leads from `a` to `b`. -/
def LimPush (u g g' : D → ℤ) (a b : V) (x : ℤ) : Prop :=
  IsPseudo M u g' ∧ ∃ val, 0 ≤ val ∧ val ≤ x ∧
    (∀ v, M.div g' v = M.div g v + val * ((if a = v then 1 else 0) - (if b = v then 1 else 0))) ∧
    (val = x ∨ ∃ Y, a ∈ Y ∧ b ∉ Y ∧ Closed M u g' Y)

namespace SPath

variable (P : SPath M)

/-! ### Clipping -/

/-- The clipped flow on `e`: `g e` brought into `[-c (rev e), c e]`. -/
def clipVal (c g : D → ℤ) (e : D) : ℤ := max (min (g e) (c e)) (-c (M.rev e))

variable (M) in
/-- Clipping the flow on `e` (lines 5–8 of Algorithm 2). -/
def clip (c g : D → ℤ) (e : D) : D → ℤ := setPair M g e (clipVal (M := M) c g e)

/-- The vertices `p t` with `j < t ≤ k`. -/
def after (j : ℕ) : Finset V := (Ioc j P.k).image P.p

lemma mem_after {j : ℕ} {v : V} : v ∈ P.after j ↔ ∃ t, j < t ∧ t ≤ P.k ∧ P.p t = v := by
  simp [after, and_assoc]

lemma p_mem_after {j t : ℕ} (h1 : j < t) (h2 : t ≤ P.k) : P.p t ∈ P.after j :=
  P.mem_after.2 ⟨t, h1, h2, rfl⟩

lemma p_not_mem_after {j t : ℕ} (h1 : t ≤ j) (hj : j ≤ P.k) : P.p t ∉ P.after j := by
  intro h
  obtain ⟨s, hs, hsk, e⟩ := P.mem_after.1 h
  have := P.inj s hsk t (h1.trans hj) e; omega

lemma p_ne {i j : ℕ} (hi : i ≤ P.k) (hj : j ≤ P.k) (h : i ≠ j) : P.p i ≠ P.p j :=
  fun e => h (P.inj i hi j hj e)

/-- The invariant of the fixing procedure after the stages `0, …, i - 1` (Lemma B.1). -/
structure FPInv (c f₀ : D → ℤ) (Mb : ℤ) (i : ℕ) (g : D → ℤ) : Prop where
  pseudo : IsPseudo M (P.cap c Mb i) g
  supp : ∀ v, v ∉ P.init i → M.div g v = M.div f₀ v
  pos : ∀ j < i, M.div g (P.p j) < 0 →
    NoPath M (P.cap c Mb i) g {P.p j} (P.after j)
  neg : ∀ j < i, 0 < M.div g (P.p j) →
    NoPath M (P.cap c Mb i) g (P.after j) {P.p j}
  pair : ∀ j < i, ∀ j' < i, M.div g (P.p j) < 0 → 0 < M.div g (P.p j') →
    NoPath M (P.cap c Mb i) g {P.p j} {P.p j'}

/-- The invariant holds at the start. -/
lemma fpInv_zero {c f₀ : D → ℤ} (hf₀ : IsPseudo M c f₀) {Mb : ℤ} (hMb : 0 ≤ Mb) :
    P.FPInv c f₀ Mb 0 f₀ :=
  ⟨⟨hf₀.antisymm, fun e => (hf₀.le_cap e).trans (P.le_cap_zero c hMb 0 e)⟩, fun _ _ => rfl,
    fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
    fun j hj => absurd hj (by omega)⟩

/-- The net outflow of `{p 0, …, p j}` is that of `f₀` when the change is supported in a smaller
initial segment. -/
lemma sum_init_eq {f₀ g : D → ℤ} (hf₀ : M.IsAntisymm f₀) (hg : M.IsAntisymm g) {i j : ℕ}
    (hij : i ≤ j) (hsupp : ∀ v, v ∉ P.init i → M.div g v = M.div f₀ v) :
    ∑ v ∈ P.init j, M.div g v = ∑ v ∈ P.init j, M.div f₀ v := by
  have hsub : P.init i ⊆ P.init j := fun v hv => by
    obtain ⟨t, ht, rfl⟩ := P.mem_init.1 hv; exact P.p_mem_init (ht.trans hij)
  have htot : ∑ v, (M.div g v - M.div f₀ v) = 0 := by
    rw [sum_sub_distrib, M.sum_div hg, M.sum_div hf₀, sub_self]
  have h1 : ∑ v, (M.div g v - M.div f₀ v) = ∑ v ∈ P.init i, (M.div g v - M.div f₀ v) :=
    (sum_subset (subset_univ _) fun v _ hv => by rw [hsupp v hv, sub_self]).symm
  have h2 : ∑ v ∈ P.init j, (M.div g v - M.div f₀ v) = ∑ v ∈ P.init i, (M.div g v - M.div f₀ v) :=
    (sum_subset hsub fun v _ hv => by rw [hsupp v hv, sub_self]).symm
  have := h2.trans (h1.symm.trans htot)
  rw [sum_sub_distrib] at this; linarith

/-- **The raised darts are not saturated** at stage `i`. -/
lemma lt_cap_boost {c f₀ g : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀) {i : ℕ}
    (hg : IsPseudo M (P.cap c (4 * absSum c + 1) i) g)
    (hsupp : ∀ v, v ∉ P.init i → M.div g v = M.div f₀ v) {t : ℕ} (hit : i ≤ t) (ht : t < P.k) :
    g (P.d t) < P.cap c (4 * absSum c + 1) i (P.d t) ∧
      g (M.rev (P.d t)) < P.cap c (4 * absSum c + 1) i (M.rev (P.d t)) := by
  have hb := P.abs_le_boost hf₀ hg ht (P.sum_init_eq hf₀.antisymm hg.antisymm hit hsupp)
  simp only [P.cap_d c _ ht, P.cap_rev_d c _ ht, hit, ↓reduceIte]
  rw [hg.antisymm (P.d t)]
  have := hc (P.d t); have := hc (M.rev (P.d t))
  rw [abs_le] at hb
  constructor <;> omega

/-- A closed set containing `p (i + 1)` but not `p i`: following the raised darts, it contains
every `p t`, `t > i`. -/
lemma after_sub_of_closed {c f₀ g : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀) {i : ℕ}
    (hi : i < P.k) (hg : IsPseudo M (P.cap c (4 * absSum c + 1) (i + 1)) g)
    (hsupp : ∀ v, v ∉ P.init (i + 1) → M.div g v = M.div f₀ v) {Y : Finset V}
    (hY : Closed M (P.cap c (4 * absSum c + 1) (i + 1)) g Y) (h : P.p (i + 1) ∈ Y) :
    P.after i ⊆ Y := by
  intro v hv
  obtain ⟨t, ht1, ht2, rfl⟩ := P.mem_after.1 hv
  clear hv
  induction t, ht1 using Nat.le_induction with
  | base => exact h
  | succ t ht ih =>
    have htk : t < P.k := by omega
    by_contra hn
    have := hY (P.d t) (by rw [P.tail_d t htk]; exact ih (by omega)) (by rwa [P.head_d t htk])
    have := (P.lt_cap_boost hc hf₀ hg hsupp ht htk).1
    omega

/-- A closed set containing `p i` but not `p (i + 1)` contains no `p t`, `t > i`. -/
lemma disj_after_of_closed {c f₀ g : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀)
    {i : ℕ} (hi : i < P.k) (hg : IsPseudo M (P.cap c (4 * absSum c + 1) (i + 1)) g)
    (hsupp : ∀ v, v ∉ P.init (i + 1) → M.div g v = M.div f₀ v) {Y : Finset V}
    (hY : Closed M (P.cap c (4 * absSum c + 1) (i + 1)) g Y) (h : P.p (i + 1) ∉ Y) :
    Disjoint Y (P.after i) := by
  rw [disjoint_right]
  intro v hv
  obtain ⟨t, ht1, ht2, rfl⟩ := P.mem_after.1 hv
  clear hv
  induction t, ht1 using Nat.le_induction with
  | base => exact h
  | succ t ht ih =>
    have htk : t < P.k := by omega
    intro hn
    have := hY (M.rev (P.d t)) (by rw [M.tail_rev, P.head_d t htk]; exact hn)
      (by rw [M.head_rev, P.tail_d t htk]; exact ih (by omega))
    have := (P.lt_cap_boost hc hf₀ hg hsupp ht htk).2
    omega

/-! ### One stage -/

/-- **One stage of the fixing procedure preserves the invariant** (Lemma B.1): clip the flow on
`d i`, then push a maximum flow with limit the excess of `p i`, forward if `p i` has positive
inflow and backward otherwise. -/
theorem FPInv.step {c f₀ g g' : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀) {i : ℕ}
    (hi : i < P.k) (h : P.FPInv c f₀ (4 * absSum c + 1) i g)
    (hpush : LimPush M (P.cap c (4 * absSum c + 1) (i + 1)) (clip M c g (P.d i)) g'
      (if M.div (clip M c g (P.d i)) (P.p i) < 0 then P.p i else P.p (i + 1))
      (if M.div (clip M c g (P.d i)) (P.p i) < 0 then P.p (i + 1) else P.p i)
      |M.div (clip M c g (P.d i)) (P.p i)|) :
    P.FPInv c f₀ (4 * absSum c + 1) (i + 1) g' := by
  classical
  have hMb0 : 0 ≤ 4 * absSum c + 1 := by have := absSum_nonneg c; omega
  generalize hg₁ : clip M c g (P.d i) = g₁ at hpush
  have hpi : P.p i ≠ P.p (i + 1) := P.p_ne hi.le hi (by omega)
  have hdi_ne : M.rev (P.d i) ≠ P.d i := M.rev_ne _
  -- the clipped flow
  have hgu : IsPseudo M (P.cap c (4 * absSum c + 1) i) g := h.pseudo
  have hcl_eq : g₁ = setPair M g (P.d i) (clipVal (M := M) c g (P.d i)) := by rw [← hg₁]; rfl
  have hii : ¬ (i + 1 ≤ i) := by omega
  have hcapd : (P.cap c (4 * absSum c + 1) i) (P.d i) = c (P.d i) + (4 * absSum c + 1) := by
    simp only [P.cap_d c (4 * absSum c + 1) hi, le_rfl, ↓reduceIte]
  have hcaprd : (P.cap c (4 * absSum c + 1) i) (M.rev (P.d i)) =
      c (M.rev (P.d i)) + (4 * absSum c + 1) := by
    simp only [P.cap_rev_d c (4 * absSum c + 1) hi, le_rfl, ↓reduceIte]
  have hcapd' : (P.cap c (4 * absSum c + 1) (i + 1)) (P.d i) = c (P.d i) := by
    simp only [P.cap_d c (4 * absSum c + 1) hi, hii, ↓reduceIte]
  have hcaprd' : (P.cap c (4 * absSum c + 1) (i + 1)) (M.rev (P.d i)) = c (M.rev (P.d i)) := by
    simp only [P.cap_rev_d c (4 * absSum c + 1) hi, hii, ↓reduceIte]
  have hcapo : ∀ e, e ≠ P.d i → e ≠ M.rev (P.d i) →
      (P.cap c (4 * absSum c + 1) (i + 1)) e = (P.cap c (4 * absSum c + 1) i) e := fun e h1 h2 => by
    simp only [P.cap_succ c (4 * absSum c + 1) hi h1 h2]
  have hg₁ps : IsPseudo M (P.cap c (4 * absSum c + 1) (i + 1)) g₁ := by
    rw [hcl_eq]
    refine ⟨setPair_antisymm hgu.antisymm _ _, fun e => ?_⟩
    by_cases h1 : e = P.d i
    · subst h1; rw [setPair_self, hcapd']; unfold clipVal
      have := hc (P.d i); have := hc (M.rev (P.d i)); omega
    · by_cases h2 : e = M.rev (P.d i)
      · subst h2; rw [setPair_rev, hcaprd']; unfold clipVal
        have := hc (P.d i); have := hc (M.rev (P.d i)); omega
      · rw [setPair_of_ne _ _ h1 h2, hcapo e h1 h2]; exact hgu.le_cap e
  have hres : ∀ e, (P.cap c (4 * absSum c + 1) (i + 1)) e - g₁ e ≤
      (P.cap c (4 * absSum c + 1) i) e - g e := fun e => by
    rw [hcl_eq]
    by_cases h1 : e = P.d i
    · subst h1; rw [setPair_self, hcapd', hcapd]; unfold clipVal
      have := hgu.le_cap (P.d i); rw [hcapd] at this; omega
    · by_cases h2 : e = M.rev (P.d i)
      · subst h2; rw [setPair_rev, hcaprd', hcaprd]; unfold clipVal
        have := hgu.le_cap (M.rev (P.d i)); rw [hcaprd, hgu.antisymm] at this
        rw [hgu.antisymm]; omega
      · rw [setPair_of_ne _ _ h1 h2, hcapo e h1 h2]
  have hdiv₁ : ∀ v, v ≠ P.p i → v ≠ P.p (i + 1) → M.div g₁ v = M.div g v := fun v h1 h2 => by
    rw [hcl_eq, div_setPair hgu.antisymm, P.tail_d i hi, P.head_d i hi]
    simp [Ne.symm h1, Ne.symm h2]
  -- the push
  obtain ⟨hg'ps, val, hv0, hvx, hdiv', hmax⟩ := hpush
  have hdiv'' : ∀ v, v ≠ P.p i → v ≠ P.p (i + 1) → M.div g' v = M.div g v := fun v h1 h2 => by
    rw [hdiv' v, hdiv₁ v h1 h2]
    split_ifs <;> simp_all
  have hsupp' : ∀ v, v ∉ P.init (i + 1) → M.div g' v = M.div f₀ v := fun v hv => by
    have h1 : v ≠ P.p i := fun e => hv (e ▸ P.p_mem_init (by omega))
    have h2 : v ≠ P.p (i + 1) := fun e => hv (e ▸ P.p_mem_init le_rfl)
    rw [hdiv'' v h1 h2]
    exact h.supp v fun h' => hv (by
      obtain ⟨t, ht, rfl⟩ := P.mem_init.1 h'; exact P.p_mem_init (by omega))
  have hsign : ∀ j < i, M.div g' (P.p j) = M.div g (P.p j) := fun j hj =>
    hdiv'' _ (P.p_ne (by omega) hi.le (by omega)) (P.p_ne (by omega) hi (by omega))
  -- the invariants of `g`, for `g₁`
  have pos₁ : ∀ j < i, M.div g (P.p j) < 0 →
      NoPath M (P.cap c (4 * absSum c + 1) (i + 1)) g₁ {P.p j} (P.after j) :=
    fun j hj hneg => (h.pos j hj hneg).of_res_le hg₁ps hres
  have neg₁ : ∀ j < i, 0 < M.div g (P.p j) →
      NoPath M (P.cap c (4 * absSum c + 1) (i + 1)) g₁ (P.after j) {P.p j} :=
    fun j hj hpos => (h.neg j hj hpos).of_res_le hg₁ps hres
  have pair₁ : ∀ j < i, ∀ j' < i, M.div g (P.p j) < 0 → 0 < M.div g (P.p j') →
      NoPath M (P.cap c (4 * absSum c + 1) (i + 1)) g₁ {P.p j} {P.p j'} :=
    fun j hj j' hj' h1 h2 => (h.pair j hj j' hj' h1 h2).of_res_le hg₁ps hres
  have hpi_after : ∀ j < i, P.p i ∈ P.after j := fun j hj => P.p_mem_after hj hi.le
  have hpi1_after : ∀ j < i, P.p (i + 1) ∈ P.after j := fun j hj => P.p_mem_after (by omega) hi
  -- the cases
  by_cases hs : M.div g₁ (P.p i) < 0
  · -- forward: from `p i` to `p (i + 1)`
    simp only [hs, ite_true] at hdiv' hmax hvx
    have hdpi : M.div g' (P.p i) = M.div g₁ (P.p i) + val := by
      rw [hdiv']; simp [hpi, hpi.symm]
    rw [abs_of_neg hs] at hvx hmax
    refine ⟨hg'ps, hsupp', fun j hj hneg => ?_, fun j hj hpos => ?_, fun j hj j' hj' h1 h2 => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · -- an earlier vertex: its set does not contain `p (i + 1)`
        obtain ⟨Y, h1, h2, h3⟩ := pos₁ j hj (by rwa [← hsign j hj])
        exact NoPath.of_push hg₁ps hg'ps hv0 hdiv' ⟨Y, h1, h2, h3,
          fun hy => absurd hy (disjoint_left.1 h2.symm (hpi1_after j hj))⟩
      · -- `p i` keeps positive inflow: the limit is not reached
        rcases hmax with hvx' | ⟨Y, hY1, hY2, hY3⟩
        · exfalso; rw [hdpi, hvx'] at hneg; omega
        · exact ⟨Y, singleton_subset_iff.2 hY1,
            P.disj_after_of_closed hc hf₀ hi hg'ps hsupp' hY3 hY2, hY3⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨Y, h1, h2, h3⟩ := neg₁ j hj (by rwa [← hsign j hj])
        exact NoPath.of_push hg₁ps hg'ps hv0 hdiv' ⟨Y, h1, h2, h3,
          fun _ => h1 (hpi_after j hj)⟩
      · exfalso; rw [hdpi] at hpos; omega
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
        · rw [hsign j hj] at h1; rw [hsign j' hj'] at h2
          obtain ⟨Y, hY1, hY2, hY3⟩ := pair₁ j hj j' hj' h1 h2
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := pos₁ j hj h1
          refine NoPath.of_push hg₁ps hg'ps hv0 hdiv' ⟨Y ∩ Z, subset_inter hY1 hZ1,
            disjoint_of_subset_left inter_subset_left hY2, hY3.inter hZ3, fun hy => ?_⟩
          exact absurd (mem_inter.1 hy).2 (disjoint_left.1 hZ2.symm (hpi1_after j hj))
        · exfalso; rw [hdpi] at h2; omega
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
        · rw [hsign j' hj'] at h2
          obtain ⟨Y, hY1, hY2, hY3⟩ := neg₁ j' hj' h2
          exact NoPath.of_push hg₁ps hg'ps hv0 hdiv' ⟨Y, singleton_subset_iff.2
            (hY1 (hpi_after j' hj')), hY2, hY3, fun _ => hY1 (hpi_after j' hj')⟩
        · omega
  · -- backward: from `p (i + 1)` to `p i`
    simp only [hs, ite_false] at hdiv' hmax hvx
    have hdpi : M.div g' (P.p i) = M.div g₁ (P.p i) - val := by
      rw [hdiv']; simp [hpi, hpi.symm]; ring
    rw [abs_of_nonneg (by omega)] at hvx hmax
    refine ⟨hg'ps, hsupp', fun j hj hneg => ?_, fun j hj hpos => ?_, fun j hj j' hj' h1 h2 => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨Y, h1, h2, h3⟩ := pos₁ j hj (by rwa [← hsign j hj])
        exact NoPath.of_push hg₁ps hg'ps hv0 hdiv' ⟨Y, h1, h2, h3,
          fun hy => absurd hy (disjoint_left.1 h2.symm (hpi_after j hj))⟩
      · exfalso; rw [hdpi] at hneg; omega
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · obtain ⟨Y, h1, h2, h3⟩ := neg₁ j hj (by rwa [← hsign j hj])
        exact NoPath.of_push hg₁ps hg'ps hv0 hdiv' ⟨Y, h1, h2, h3,
          fun _ => h1 (hpi1_after j hj)⟩
      · rcases hmax with hvx' | ⟨Y, hY1, hY2, hY3⟩
        · exfalso; rw [hdpi, hvx'] at hpos; omega
        · exact ⟨Y, P.after_sub_of_closed hc hf₀ hi hg'ps hsupp' hY3 hY1,
            disjoint_singleton_right.2 hY2, hY3⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
        · rw [hsign j hj] at h1; rw [hsign j' hj'] at h2
          obtain ⟨Y, hY1, hY2, hY3⟩ := pair₁ j hj j' hj' h1 h2
          obtain ⟨Z, hZ1, hZ2, hZ3⟩ := neg₁ j' hj' h2
          refine NoPath.of_push hg₁ps hg'ps hv0 hdiv' ⟨Y ∪ Z, hY1.trans subset_union_left,
            disjoint_union_left.2 ⟨hY2, hZ2⟩, hY3.union hZ3, fun _ => ?_⟩
          exact mem_union_right _ (hZ1 (hpi1_after j' hj'))
        · rw [hsign j hj] at h1
          obtain ⟨Y, hY1, hY2, hY3⟩ := pos₁ j hj h1
          exact NoPath.of_push hg₁ps hg'ps hv0 hdiv' ⟨Y, hY1,
            disjoint_singleton_right.2 (disjoint_left.1 hY2.symm (hpi_after j hj)), hY3,
            fun hy => absurd hy (disjoint_left.1 hY2.symm (hpi_after j hj))⟩
      · exfalso; rw [hdpi] at h1; omega

/-- **The output property** (Corollary B.2): after the last stage, with the capacities back to
`c`, no residual path leads from a vertex of the path with positive inflow to a vertex of the path
with negative inflow, and the net outflow has changed only on the path. -/
theorem FPInv.final {c f₀ g : D → ℤ} {Mb : ℤ} (h : P.FPInv c f₀ Mb P.k g) :
    IsPseudo M c g ∧ (∀ v, v ∉ P.verts → M.div g v = M.div f₀ v) ∧
      NoPath M c g (P.verts.filter fun v => M.div g v < 0)
        (P.verts.filter fun v => 0 < M.div g v) := by
  classical
  have hps := h.pseudo
  rw [P.cap_k] at hps
  refine ⟨hps, h.supp, ?_⟩
  rw [noPath_iff hps]
  intro a ha b hb hab
  simp only [mem_filter] at ha hb
  obtain ⟨s, hs, rfl⟩ := P.mem_init.1 ha.1
  obtain ⟨t, ht, rfl⟩ := P.mem_init.1 hb.1
  have key : NoPath M c g {P.p s} {P.p t} := by
    have hcap := P.cap_k c Mb
    rcases Nat.lt_or_ge s P.k with hsk | hsk
    · rcases Nat.lt_or_ge t P.k with htk | htk
      · have := h.pair s hsk t htk ha.2 hb.2; rwa [hcap] at this
      · obtain ⟨Y, h1, h2, h3⟩ := h.pos s hsk ha.2
        rw [hcap] at h3
        exact ⟨Y, h1, disjoint_singleton_right.2 (disjoint_left.1 h2.symm
          (P.p_mem_after (by omega) ht)), h3⟩
    · rcases Nat.lt_or_ge t P.k with htk | htk
      · obtain ⟨Y, h1, h2, h3⟩ := h.neg t htk hb.2
        rw [hcap] at h3
        exact ⟨Y, singleton_subset_iff.2 (h1 (P.p_mem_after (by omega) hs)),
          disjoint_singleton_right.2 (disjoint_left.1 h2.symm (mem_singleton_self _)), h3⟩
      · have : s = t := by omega
        subst this; omega
  exact (noPath_iff hps).1 key _ (mem_singleton_self _) _ (mem_singleton_self _) hab

end SPath

end BKMNW

end PlanarFlow
