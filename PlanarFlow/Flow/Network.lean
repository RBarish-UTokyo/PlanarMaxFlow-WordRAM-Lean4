module

public import PlanarFlow.Spec
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic.Linarith

/-!
# Flows in networks and the max-flow min-cut theorem

A *network* has a finite set of vertices `V`, a finite set of arcs `E` with a tail and a head
each (parallel arcs, antiparallel arcs and loops are allowed), and an integer capacity on every
arc. Given disjoint sets `S` of sources and `T` of sinks, a *flow* assigns to every arc an integer
between `0` and its capacity, such that at every vertex which is neither a source nor a sink the
flow is conserved. Its *value* is the net flow leaving the sources. A *cut* is a set of vertices
containing all sources and no sink; its capacity is the total capacity of the arcs leaving it.

## Main results

* `PlanarFlow.Network.value_eq_flowAcross`: the value of a flow is the net flow across any cut.
* `PlanarFlow.Network.value_le_cutCap`: **weak duality**, the value of a flow is at most the
  capacity of a cut.
* `PlanarFlow.Network.exists_augment`: if a sink is reachable from a source in the *residual
  graph* of a flow, there is a flow of value one more (augmentation along a shortest augmenting
  path).
* `PlanarFlow.Network.value_eq_cutCap_reach`: otherwise the set of vertices reachable from the
  sources in the residual graph is a cut whose capacity is the value of the flow.
* `PlanarFlow.Network.max_flow_min_cut`: **the max-flow min-cut theorem** for multiple sources
  and multiple sinks: there are a flow and a cut with the value of the flow equal to the capacity
  of the cut; by weak duality the flow is maximum and the cut is minimum. Since flows are
  integral by definition, this includes the integrality theorem.

The case of several sources and sinks is usually reduced to a single source and sink by adding a
super-source joined to every source and a super-sink joined from every sink by arcs of unbounded
capacity. The argument below works directly with sets of sources and sinks (an augmenting path
starts at any source and ends at any sink), which is the classical argument run in the network
with the super-source and super-sink.

## References

* L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*, Canad. J. Math. 8 (1956),
  399–404.
* P. Elias, A. Feinstein, C. E. Shannon, *A note on the maximum flow through a network*, IRE
  Trans. Inform. Theory 2 (1956), 117–119.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

open Finset

namespace Network

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (N : Network V E)

/-- The net flow across a set of vertices: out of it minus into it. -/
def flowAcross (f : E → ℤ) (X : Finset V) : ℤ :=
  ∑ e with N.tail e ∈ X ∧ N.head e ∉ X, f e - ∑ e with N.tail e ∉ X ∧ N.head e ∈ X, f e

/-! ### Linearity of the net outflow -/

lemma netOut_add (f g : E → ℤ) (v : V) :
    N.netOut (f + g) v = N.netOut f v + N.netOut g v := by
  simp only [netOut, Pi.add_apply, sum_add_distrib]; ring

lemma netOut_zero (v : V) : N.netOut 0 v = 0 := by simp [netOut]

lemma netOut_single (a : E) (c : ℤ) (v : V) :
    N.netOut (fun e => if e = a then c else 0) v =
      (if N.tail a = v then c else 0) - (if N.head a = v then c else 0) := by
  simp only [netOut, sum_ite_eq', mem_filter, mem_univ, true_and]

lemma netOut_sum {ι : Type*} (s : Finset ι) (g : ι → E → ℤ) (v : V) :
    N.netOut (∑ i ∈ s, g i) v = ∑ i ∈ s, N.netOut (g i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [netOut_zero]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, netOut_add, ih]

/-- The net flow leaving a set of vertices, summed vertex by vertex, is the net flow across the
set: arcs inside the set cancel. -/
theorem sum_netOut (f : E → ℤ) (X : Finset V) :
    ∑ v ∈ X, N.netOut f v = N.flowAcross f X := by
  have h1 : ∑ v ∈ X, ∑ e with N.tail e = v, f e = ∑ e with N.tail e ∈ X, f e := by
    rw [← sum_fiberwise_of_maps_to (s := univ.filter (fun e => N.tail e ∈ X)) (t := X)
      (g := N.tail) (by simp)]
    refine sum_congr rfl fun v hv => ?_
    congr 1; ext e; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro rfl; exact ⟨hv, rfl⟩
    · exact fun h => h.2
  have h2 : ∑ v ∈ X, ∑ e with N.head e = v, f e = ∑ e with N.head e ∈ X, f e := by
    rw [← sum_fiberwise_of_maps_to (s := univ.filter (fun e => N.head e ∈ X)) (t := X)
      (g := N.head) (by simp)]
    refine sum_congr rfl fun v hv => ?_
    congr 1; ext e; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro rfl; exact ⟨hv, rfl⟩
    · exact fun h => h.2
  simp only [netOut, sum_sub_distrib, h1, h2, flowAcross]
  have h3 : ∑ e with N.tail e ∈ X, f e =
      ∑ e with N.tail e ∈ X ∧ N.head e ∈ X, f e + ∑ e with N.tail e ∈ X ∧ N.head e ∉ X, f e := by
    rw [← sum_union]
    · congr 1; ext e; simp; tauto
    · rw [disjoint_filter]; intro e _ h; tauto
  have h4 : ∑ e with N.head e ∈ X, f e =
      ∑ e with N.tail e ∈ X ∧ N.head e ∈ X, f e + ∑ e with N.tail e ∉ X ∧ N.head e ∈ X, f e := by
    rw [← sum_union]
    · congr 1; ext e; simp; tauto
    · rw [disjoint_filter]; intro e _ h; tauto
  rw [h3, h4]; ring

/-! ### Weak duality -/

variable {N}

/-- The value of a flow is the net flow across any cut. -/
theorem value_eq_flowAcross {S T X : Finset V} {f : E → ℤ} (hf : N.IsFlow S T f)
    (hX : IsCut S T X) : N.value S f = N.flowAcross f X := by
  rw [← N.sum_netOut, value]
  refine sum_subset hX.1 fun v hvX hvS => hf.conserve v hvS ?_
  exact fun hvT => disjoint_left.1 hX.2 hvX hvT

/-- **Weak duality**: the value of a flow is at most the capacity of any cut. -/
theorem value_le_cutCap {S T X : Finset V} {f : E → ℤ} (hf : N.IsFlow S T f)
    (hX : IsCut S T X) : N.value S f ≤ N.cutCap X := by
  rw [value_eq_flowAcross hf hX, flowAcross, cutCap]
  have h1 : ∑ e with N.tail e ∈ X ∧ N.head e ∉ X, f e ≤
      ∑ e with N.tail e ∈ X ∧ N.head e ∉ X, N.cap e := sum_le_sum fun e _ => hf.le_cap e
  have h2 : 0 ≤ ∑ e with N.tail e ∉ X ∧ N.head e ∈ X, f e := sum_nonneg fun e _ => hf.nonneg e
  linarith

/-! ### The residual graph -/

variable (N)

/-- An arc of the residual graph of `f` from `a` to `b`: an arc from `a` to `b` which is not
saturated, or an arc from `b` to `a` carrying positive flow. -/
def Res (f : E → ℤ) (a b : V) : Prop :=
  ∃ e, (N.tail e = a ∧ N.head e = b ∧ f e < N.cap e) ∨ (N.tail e = b ∧ N.head e = a ∧ 0 < f e)

/-- The vertices reachable from a source in the residual graph. -/
noncomputable def reach (S : Finset V) (f : E → ℤ) : Finset V := by
  classical exact univ.filter fun v => ∃ s ∈ S, Relation.ReflTransGen (N.Res f) s v

variable {N}

lemma mem_reach {S : Finset V} {f : E → ℤ} {v : V} :
    v ∈ N.reach S f ↔ ∃ s ∈ S, Relation.ReflTransGen (N.Res f) s v := by
  classical
  unfold reach
  simp

/-- If no sink is reachable in the residual graph, the reachable set is a cut whose capacity is
the value of the flow. -/
theorem value_eq_cutCap_reach {S T : Finset V} {f : E → ℤ} (hf : N.IsFlow S T f)
    (hR : Disjoint (N.reach S f) T) : IsCut S T (N.reach S f) ∧
      N.value S f = N.cutCap (N.reach S f) := by
  have hcut : IsCut S T (N.reach S f) :=
    ⟨fun s hs => mem_reach.2 ⟨s, hs, .refl⟩, hR⟩
  refine ⟨hcut, ?_⟩
  rw [value_eq_flowAcross hf hcut, flowAcross, cutCap]
  have hout : ∀ e ∈ ({e | N.tail e ∈ N.reach S f ∧ N.head e ∉ N.reach S f} : Finset E),
      f e = N.cap e := by
    intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    by_contra hne
    obtain ⟨s, hs, hr⟩ := mem_reach.1 he.1
    exact he.2 (mem_reach.2 ⟨s, hs, hr.tail ⟨e, Or.inl ⟨rfl, rfl,
      lt_of_le_of_ne (hf.le_cap e) hne⟩⟩⟩)
  have hin : ∀ e ∈ ({e | N.tail e ∉ N.reach S f ∧ N.head e ∈ N.reach S f} : Finset E),
      f e = 0 := by
    intro e he
    simp only [mem_filter, mem_univ, true_and] at he
    by_contra hne
    obtain ⟨s, hs, hr⟩ := mem_reach.1 he.2
    exact he.1 (mem_reach.2 ⟨s, hs, hr.tail ⟨e, Or.inr ⟨rfl, rfl,
      lt_of_le_of_ne (hf.nonneg e) (Ne.symm hne)⟩⟩⟩)
  rw [sum_congr rfl hout, sum_congr rfl hin, sum_const_zero, sub_zero]

/-! ### Augmenting paths -/

/-- A relation-chain of length `n` from `a` to `b`, as a sequence of vertices. -/
lemma exists_seq_of_reflTransGen {r : V → V → Prop} {a b : V}
    (h : Relation.ReflTransGen r a b) :
    ∃ n, ∃ p : ℕ → V, p 0 = a ∧ p n = b ∧ ∀ i < n, r (p i) (p (i + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, p, h0, hn, hp⟩ := ih
    refine ⟨n + 1, fun i => if i ≤ n then p i else c, by simp [h0], by simp, fun i hi => ?_⟩
    by_cases hin : i < n
    · simp only [show i ≤ n by omega, show i + 1 ≤ n by omega, ite_true]; exact hp i hin
    · have : i = n := by omega
      subst this
      simp only [le_refl, ite_true, show ¬ i + 1 ≤ i by omega, ite_false, hn]; exact hbc

/-- An augmenting path of length `n`: a residual walk from a source to a sink. -/
def AugPath (S T : Finset V) (f : E → ℤ) (n : ℕ) : Prop :=
  ∃ p : ℕ → V, p 0 ∈ S ∧ p n ∈ T ∧ ∀ i < n, N.Res f (p i) (p (i + 1))

/-- A shortest augmenting path visits no vertex twice. -/
lemma injective_of_min {S T : Finset V} {f : E → ℤ} {n : ℕ} {p : ℕ → V} (h0 : p 0 ∈ S)
    (hn : p n ∈ T) (hp : ∀ i < n, N.Res f (p i) (p (i + 1)))
    (hmin : ∀ m < n, ¬ N.AugPath S T f m) {i j : ℕ} (hij : i < j) (hj : j ≤ n)
    (heq : p i = p j) : False := by
  refine hmin (n - (j - i)) (by omega) ⟨fun k => if k ≤ i then p k else p (k + (j - i)),
    by simp [h0], ?_, fun k hk => ?_⟩
  · by_cases hni : n - (j - i) ≤ i
    · have : n - (j - i) = i := by omega
      simp only [hni, ite_true]
      rw [this, heq, show j = n by omega]; exact hn
    · simp only [hni, ite_false]; rw [show n - (j - i) + (j - i) = n by omega]; exact hn
  · by_cases hki : k < i
    · simp only [show k ≤ i by omega, show k + 1 ≤ i by omega, ite_true]; exact hp k (by omega)
    · by_cases hk' : k = i
      · subst hk'
        simp only [le_refl, ite_true, show ¬ k + 1 ≤ k by omega, ite_false]
        rw [heq, show k + 1 + (j - k) = j + 1 by omega]; exact hp j (by omega)
      · simp only [show ¬ k ≤ i by omega, show ¬ k + 1 ≤ i by omega, ite_false]
        rw [show k + 1 + (j - i) = k + (j - i) + 1 by omega]; exact hp _ (by omega)

/-- **Augmentation.** If a sink is reachable from a source in the residual graph, then pushing
one unit along a shortest augmenting path gives a flow of value one more. -/
theorem exists_augment {S T : Finset V} {f : E → ℤ} (hST : Disjoint S T) (hf : N.IsFlow S T f)
    (hR : ¬ Disjoint (N.reach S f) T) :
    ∃ f', N.IsFlow S T f' ∧ N.value S f' = N.value S f + 1 := by
  classical
  have hex : ∃ n, N.AugPath S T f n := by
    obtain ⟨t, htR, htT⟩ := not_disjoint_iff.1 hR
    obtain ⟨s, hs, hr⟩ := mem_reach.1 htR
    obtain ⟨n, p, h0, hn, hp⟩ := exists_seq_of_reflTransGen hr
    exact ⟨n, p, h0 ▸ hs, hn ▸ htT, hp⟩
  obtain ⟨p, h0, hn, hp⟩ := Nat.find_spec hex
  generalize hN : Nat.find hex = n at h0 hn hp
  have hmin : ∀ m < n, ¬ N.AugPath S T f m := fun m hm => Nat.find_min hex (by omega)
  have hinj : ∀ i j, i ≤ n → j ≤ n → p i = p j → i = j := by
    intro i j hi hj he
    rcases lt_trichotomy i j with h | h | h
    · exact (injective_of_min h0 hn hp hmin h hj he).elim
    · exact h
    · exact (injective_of_min h0 hn hp hmin h hi he.symm).elim
  have hnS : p n ∉ S := fun h => disjoint_left.1 hST h hn
  have hn0 : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    subst this
    exact hnS h0
  -- choose the arcs of the path
  have hp' : ∀ i, ∃ e, i < n → (N.tail e = p i ∧ N.head e = p (i + 1) ∧ f e < N.cap e) ∨
      (N.tail e = p (i + 1) ∧ N.head e = p i ∧ 0 < f e) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨e, he⟩ := hp i hi; exact ⟨e, fun _ => he⟩
    · obtain ⟨e, -⟩ := hp 0 hn0
      exact ⟨e, fun h => absurd h hi⟩
  choose a ha using hp'
  let fwd : ℕ → Prop := fun i => N.tail (a i) = p i ∧ N.head (a i) = p (i + 1) ∧
    f (a i) < N.cap (a i)
  let δ : ℕ → E → ℤ := fun i e => if e = a i then (if fwd i then 1 else -1) else 0
  have hδ : ∀ i < n, ∀ v, N.netOut (δ i) v =
      (if p i = v then 1 else 0) - (if p (i + 1) = v then 1 else 0) := by
    intro i hi v
    have hne : p i ≠ p (i + 1) := fun h => by have := hinj _ _ (by omega) (by omega) h; omega
    simp only [δ]
    rw [netOut_single]
    by_cases hfw : fwd i
    · simp only [hfw, ite_true, hfw.1, hfw.2.1]
    · rcases ha i hi with h | ⟨h1, h2, -⟩
      · exact absurd h hfw
      · simp only [hfw, ite_false, h1, h2]
        split_ifs <;> simp
  let f' : E → ℤ := f + ∑ i ∈ range n, δ i
  have hnet : ∀ v, N.netOut f' v =
      N.netOut f v + ((if p 0 = v then 1 else 0) - (if p n = v then 1 else 0)) := by
    intro v
    simp only [f', netOut_add, netOut_sum]
    rw [sum_congr rfl fun i hi => hδ i (mem_range.1 hi) v]
    rw [sum_range_sub' (fun i => if p i = v then (1 : ℤ) else 0)]
  -- each arc is used at most once
  have huniq : ∀ i j, i < n → j < n → a i = a j → i = j := by
    intro i j hi hj he
    have key : ∀ k < n, (N.tail (a k) = p k ∧ N.head (a k) = p (k + 1)) ∨
        (N.tail (a k) = p (k + 1) ∧ N.head (a k) = p k) := by
      intro k hk
      rcases ha k hk with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
    rcases key i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases key j hj with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      rw [he] at h1 h2
    · exact hinj i j (by omega) (by omega) (h1.symm.trans h3)
    · have := hinj i (j + 1) (by omega) (by omega) (h1.symm.trans h3)
      have := hinj (i + 1) j (by omega) (by omega) (h2.symm.trans h4); omega
    · have := hinj (i + 1) j (by omega) (by omega) (h1.symm.trans h3)
      have := hinj i (j + 1) (by omega) (by omega) (h2.symm.trans h4); omega
    · exact hinj i j (by omega) (by omega) (h2.symm.trans h4)
  have hval : ∀ e, f' e = f e ∨ ∃ i < n, a i = e ∧ f' e = f e + (if fwd i then 1 else -1) := by
    intro e
    simp only [f', Pi.add_apply, Finset.sum_apply]
    by_cases hex' : ∃ i < n, a i = e
    · obtain ⟨i, hi, rfl⟩ := hex'
      right
      refine ⟨i, hi, rfl, ?_⟩
      rw [sum_eq_single i]
      · simp [δ]
      · intro j hj hji
        simp only [δ]
        exact ite_eq_right_iff.2 fun h => absurd (huniq _ _ (mem_range.1 hj) hi h.symm) hji
      · intro h; exact absurd (mem_range.2 hi) h
    · left
      push Not at hex'
      rw [sum_eq_zero, add_zero]
      intro j hj
      simp only [δ]
      exact ite_eq_right_iff.2 fun h => absurd h.symm (hex' j (mem_range.1 hj))
  refine ⟨f', ⟨fun e => ?_, fun e => ?_, fun v hvS hvT => ?_⟩, ?_⟩
  · rcases hval e with h | ⟨i, hi, rfl, h⟩
    · rw [h]; exact hf.nonneg e
    · rw [h]
      by_cases hfw : fwd i
      · simp only [hfw, ite_true]; linarith [hf.nonneg (a i)]
      · simp only [hfw, ite_false]
        rcases ha i hi with h' | ⟨-, -, h'⟩
        · exact absurd h' hfw
        · linarith
  · rcases hval e with h | ⟨i, hi, rfl, h⟩
    · rw [h]; exact hf.le_cap e
    · rw [h]
      by_cases hfw : fwd i
      · simp only [hfw, ite_true]; have := hfw.2.2; linarith
      · simp only [hfw, ite_false]; linarith [hf.le_cap (a i)]
  · rw [hnet, hf.conserve v hvS hvT]
    have h1 : p 0 ≠ v := fun h => hvS (h ▸ h0)
    have h2 : p n ≠ v := fun h => hvT (h ▸ hn)
    simp [h1, h2]
  · simp only [value]
    rw [sum_congr rfl fun v _ => hnet v, sum_add_distrib, sum_sub_distrib, sum_ite_eq,
      sum_ite_eq]
    simp [h0, hnS]

/-! ### The max-flow min-cut theorem -/

/-- The flows, as a finite set (flows take values between `0` and the capacity). -/
noncomputable def flows (S T : Finset V) : Finset (E → ℤ) := by
  classical exact (Fintype.piFinset fun e => Icc 0 (N.cap e)).filter fun f => N.IsFlow S T f

lemma mem_flows {S T : Finset V} {f : E → ℤ} : f ∈ N.flows S T ↔ N.IsFlow S T f := by
  classical
  unfold flows
  simp only [mem_filter, Fintype.mem_piFinset, mem_Icc, and_iff_right_iff_imp]
  exact fun hf e => ⟨hf.nonneg e, hf.le_cap e⟩

/-- **The max-flow min-cut theorem** for multiple sources and sinks: if the capacities are
nonnegative and no vertex is both a source and a sink, there are a flow `f` and a cut `X` with
`value f = cutCap X`. By weak duality (`value_le_cutCap`) `f` is a maximum flow and `X` a minimum
cut. -/
theorem max_flow_min_cut {S T : Finset V} (hST : Disjoint S T) (hcap : ∀ e, 0 ≤ N.cap e) :
    ∃ f X, N.IsFlow S T f ∧ IsCut S T X ∧ N.value S f = N.cutCap X := by
  have h0 : N.IsFlow S T 0 :=
    ⟨fun _ => le_rfl, hcap, fun v _ _ => N.netOut_zero v⟩
  obtain ⟨f, hf, hmax⟩ := (N.flows S T).exists_max_image (N.value S) ⟨0, mem_flows.2 h0⟩
  rw [mem_flows] at hf
  by_cases hR : Disjoint (N.reach S f) T
  · obtain ⟨hX, hv⟩ := value_eq_cutCap_reach hf hR
    exact ⟨f, _, hf, hX, hv⟩
  · obtain ⟨f', hf', hv'⟩ := exists_augment hST hf hR
    have := hmax f' (mem_flows.2 hf')
    omega

/-- The maximum value of a flow equals the minimum capacity of a cut: the flow and cut of
`max_flow_min_cut` are optimal. -/
theorem max_flow_min_cut' {S T : Finset V} (hST : Disjoint S T) (hcap : ∀ e, 0 ≤ N.cap e) :
    ∃ f X, N.IsFlow S T f ∧ IsCut S T X ∧
      (∀ g, N.IsFlow S T g → N.value S g ≤ N.value S f) ∧
      (∀ Y, IsCut S T Y → N.cutCap X ≤ N.cutCap Y) := by
  obtain ⟨f, X, hf, hX, hv⟩ := N.max_flow_min_cut hST hcap
  exact ⟨f, X, hf, hX, fun g hg => hv ▸ value_le_cutCap hg hX,
    fun Y hY => hv ▸ value_le_cutCap hf hY⟩

end Network

end PlanarFlow
