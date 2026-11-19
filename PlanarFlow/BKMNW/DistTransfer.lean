module

public import PlanarFlow.BKMNW.Dist

/-!
# Distances along an embedding of digraphs

Let `ι : X → Y` be injective, `G` a digraph on `X` and `G'` one on `Y`, such that every arc of `G`
has a copy in `G'` along `ι`, and every arc of `G'` leaving the image of `ι` is a copy of an arc
of `G` or a loop of nonnegative length. Then the distances from `ι r` in `G'` are those from `r`
in `G`, read along `ι`, and the vertices outside the image are unreachable (`isDist_transfer`).

This is how the input of a subroutine run on the machine, numbered `0, …, N - 1`, is related to the
call of the subroutine in the algorithm (`PlanarFlow/BKMNW/FRFixPath.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {X Y A B : Type*} {G : Digraph X A} {G' : Digraph Y B} {ι : X → Y}

/-- The hypotheses of the transfer. -/
structure Transfer (G : Digraph X A) (G' : Digraph Y B) (ι : X → Y) : Prop where
  inj : Function.Injective ι
  fwd : ∀ a, ∃ a', G'.src a' = ι (G.src a) ∧ G'.dst a' = ι (G.dst a) ∧ G'.len a' = G.len a
  bwd : ∀ a', ∀ x, G'.src a' = ι x →
    (∃ a, G.src a = x ∧ ι (G.dst a) = G'.dst a' ∧ G.len a = G'.len a') ∨
      (G'.dst a' = G'.src a' ∧ 0 ≤ G'.len a')

variable (h : Transfer G G' ι)
include h

/-- Walks of `G` go to walks of `G'` of the same length. -/
theorem Transfer.walk_fwd {x z : X} {l : List A} (hl : IsWalk G x l z) :
    ∃ l', IsWalk G' (ι x) l' (ι z) ∧ wlen G' l' = wlen G l := by
  induction l generalizing x with
  | nil => exact ⟨[], by simp only [isWalk_nil] at hl ⊢; rw [hl], rfl⟩
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := hl
    obtain ⟨l', hl', he⟩ := ih h2
    obtain ⟨a', hs, hd, hlen⟩ := h.fwd a
    refine ⟨a' :: l', ⟨by rw [hs, h1], by rw [hd]; exact hl'⟩, ?_⟩
    rw [wlen_cons, wlen_cons, hlen, he]

/-- Walks of `G'` from the image stay in the image and come from walks of `G` that are no
longer. -/
theorem Transfer.walk_bwd {x : X} {y : Y} {l : List B} (hl : IsWalk G' (ι x) l y) :
    ∃ z, ι z = y ∧ ∃ m, IsWalk G x m z ∧ wlen G m ≤ wlen G' l := by
  induction l generalizing x with
  | nil => exact ⟨x, by simpa using hl, [], rfl, le_rfl⟩
  | cons a' l ih =>
    obtain ⟨h1, h2⟩ := hl
    rcases h.bwd a' x h1 with ⟨a, hs, hd, hlen⟩ | ⟨hloop, hnn⟩
    · rw [← hd] at h2
      obtain ⟨z, hz, m, hm, hle⟩ := ih h2
      refine ⟨z, hz, a :: m, ⟨hs, hm⟩, ?_⟩
      rw [wlen_cons, wlen_cons, hlen]; omega
    · rw [hloop, h1] at h2
      obtain ⟨z, hz, m, hm, hle⟩ := ih h2
      refine ⟨z, hz, m, hm, ?_⟩
      rw [wlen_cons]; omega

open Classical in
/-- The distances of `G` read along `ι`, `none` off the image. -/
noncomputable def Transfer.pull (_h : Transfer G G' ι) (δ : X → Option ℤ) (y : Y) : Option ℤ :=
  if hy : ∃ z, ι z = y then δ hy.choose else none

theorem Transfer.pull_iota (δ : X → Option ℤ) (z : X) : h.pull δ (ι z) = δ z := by
  classical
  have hy : ∃ z', ι z' = ι z := ⟨z, rfl⟩
  unfold pull
  rw [dite_eq_left_of_eq_true (eq_true hy), h.inj hy.choose_spec]

/-- **The transfer of distances.** -/
theorem isDist_transfer {r : X} {δ : X → Option ℤ} (hd : IsDist G r δ) :
    IsDist G' (ι r) (h.pull δ) where
  some_walk y ℓ hy := by
    classical
    by_cases hex : ∃ z, ι z = y
    · obtain ⟨z, rfl⟩ := hex
      rw [h.pull_iota] at hy
      obtain ⟨l, hl, he⟩ := hd.some_walk z ℓ hy
      obtain ⟨l', hl', he'⟩ := h.walk_fwd hl
      exact ⟨l', hl', he'.trans he⟩
    · simp [Transfer.pull, hex] at hy
  some_le y ℓ hy l hl := by
    obtain ⟨z, rfl, m, hm, hle⟩ := h.walk_bwd hl
    rw [h.pull_iota] at hy
    exact (hd.some_le z ℓ hy m hm).trans hle
  none y hy l hl := by
    obtain ⟨z, rfl, m, hm, -⟩ := h.walk_bwd hl
    rw [h.pull_iota] at hy
    exact hd.none z hy m hm

end BKMNW

end PlanarFlow
