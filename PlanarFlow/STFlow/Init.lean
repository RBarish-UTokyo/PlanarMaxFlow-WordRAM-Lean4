module

public import PlanarFlow.STFlow.Pivot

/-!
# The initial state: a shortest-path tree of the dual

The algorithm starts at the parameter `λ = 0` of Erickson's formulation (SODA 2010): the
distances `φ` in the dual graph from the root face `o`, with the capacities as lengths
(nonnegative; one run of Dijkstra's algorithm), and a shortest-path tree `T*` of the dual. The
initial flow is the circulation `cob φ`: it is within the capacities (the triangle inequality)
and saturates the darts of `T*` (they are tight). This is the leftmost circulation of Khuller,
Naor and Klein, which saturates the clockwise cycles, as in Borradaile and Klein.

With zero lengths a tree of tight darts may close a cycle; the parent of a face `x ≠ o` is the
last dart of a shortest walk from `o` to `x` with the fewest darts (`hop x`), so that the number
of darts decreases towards the root.

* `exists_init`: the initial state exists and satisfies the invariant `Inv`, with the flow a
  circulation.
* `init`: a choice of it.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-- **A shortest-path tree of the dual** with nonnegative lengths `c`, rooted at `o`: a feasible
potential `φ` and parent darts that are tight and lead to the root. -/
theorem exists_spt (hM : M.IsPlane) [Nonempty D] {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (o : F) :
    ∃ (φ : F → ℤ) (par : F → D), (∀ d, M.cob φ d ≤ c d) ∧
      (∀ x, x ≠ o → M.face (M.rev (par x)) = x ∧ M.cob φ (par x) = c (par x)) ∧
      ∀ x, ∃ n, (upF M o par)^[n] x = o := by
  classical
  let G := M.dualGraph c
  have hpot0 : G.IsPot fun _ => 0 := fun d => by simp [G, dualGraph, hc d]
  obtain ⟨δ, hδ⟩ := exists_isDist hpot0 o
  have hreach : ∀ y, δ y ≠ none := fun y => by
    obtain ⟨l, hl⟩ := dual_reach hM c o y
    obtain ⟨ℓ, h1, -⟩ := hδ.exists_le hl
    simp [h1]
  let φ : F → ℤ := fun y => (δ y).getD 0
  have hφpot : G.IsPot φ := hδ.isPot hreach
  have hφo : φ o = 0 := by simp [φ, hδ.self hpot0]
  -- shortest walks
  have hsw : ∀ y, ∃ n l, IsWalk G o l y ∧ wlen G l = φ y ∧ l.length = n := fun y => by
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.1 (hreach y)
    obtain ⟨l, hl, hlen⟩ := hδ.some_walk y ℓ hℓ
    exact ⟨_, l, hl, by simp [φ, hℓ, hlen], rfl⟩
  let hop : F → ℕ := fun y => Nat.find (hsw y)
  -- the last dart of a shortest walk with the fewest darts
  have hlast : ∀ y, y ≠ o → ∃ e, M.face (M.rev e) = y ∧ φ y = φ (M.face e) + c e ∧
      hop (M.face e) < hop y := by
    intro y hy
    obtain ⟨l, hl, hlen, hn⟩ := Nat.find_spec (hsw y)
    rcases List.eq_nil_or_concat' l with rfl | ⟨l', e, rfl⟩
    · exact absurd hl.symm hy
    obtain ⟨z, hl', he⟩ := isWalk_append_iff.1 hl
    obtain ⟨hz, hy'⟩ := isWalk_singleton.1 he
    have hz' : M.face e = z := hz
    have hy'' : M.face (M.rev e) = y := hy'
    have h1 : φ z ≤ wlen G l' := hδ.getD_le hl'
    have h2 := hφpot e
    simp only [G, dualGraph] at h2
    rw [hz', hy''] at h2
    rw [wlen_append] at hlen
    have h3 : wlen G [e] = c e := by simp [G, dualGraph, wlen]
    rw [h3] at hlen
    have hwz : wlen G l' = φ z := by omega
    refine ⟨e, hy'', by rw [hz']; omega, ?_⟩
    rw [hz']
    have : hop z ≤ l'.length := Nat.find_min' (hsw z) ⟨l', hl', hwz, rfl⟩
    simp only [List.length_append, List.length_singleton] at hn
    show hop z < Nat.find (hsw y)
    omega
  choose! par hpar using hlast
  refine ⟨φ, par, fun d => ?_, fun x hx => ⟨(hpar x hx).1, ?_⟩, fun x => ?_⟩
  · have := hφpot d
    simp only [G, dualGraph] at this
    simp only [cob]; omega
  · simp only [cob, (hpar x hx).1]; have := (hpar x hx).2.1; omega
  · induction hn : hop x using Nat.strong_induction_on generalizing x with
    | _ n ih =>
      by_cases hx : x = o
      · exact ⟨0, hx⟩
      · obtain ⟨k, hk⟩ := ih _ (hn ▸ (hpar x hx).2.2) (M.face (par x)) rfl
        exact ⟨k + 1, by rw [Function.iterate_succ_apply]; simpa [upF, hx] using hk⟩

/-- **The initial state** exists: a shortest-path tree of the dual rooted at `o` and the
circulation `cob φ` of its distances, which saturates the tree. -/
theorem exists_init (hM : M.IsPlane) [Nonempty D] {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (s t : V) (o : F) :
    ∃ st : St M, st.T.root = o ∧ Inv c s t st ∧ M.IsCirc st.g := by
  obtain ⟨φ, par, hpot, htight, hreach⟩ := exists_spt hM hc o
  refine ⟨⟨M.cob φ, ⟨o, par, fun x hx => (htight x hx).1, hreach⟩⟩, rfl,
    ⟨⟨M.cob_antisymm φ, hpot⟩, fun v _ _ => M.div_cob φ v, fun x hx => (htight x hx).2⟩,
    M.isCirc_cob φ⟩

variable (M) in
open Classical in
/-- The initial state (a choice; the zero flow and an arbitrary tree when the hypotheses fail). -/
noncomputable def init (c : D → ℤ) (s t : V) (o : F) : Option (St M) :=
  if h : ∃ st : St M, st.T.root = o ∧ Inv c s t st ∧ M.IsCirc st.g then some h.choose else none

lemma init_spec (hM : M.IsPlane) [Nonempty D] {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (s t : V) (o : F) :
    ∃ st, init M c s t o = some st ∧ st.T.root = o ∧ Inv c s t st ∧ M.IsCirc st.g := by
  have h := exists_init hM hc s t o
  exact ⟨h.choose, by simp [init, h], h.choose_spec⟩

end STFlow

end PlanarFlow
