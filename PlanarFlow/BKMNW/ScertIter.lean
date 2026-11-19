module

public import PlanarFlow.BKMNW.ScertLoop

/-!
# `scertD` from the prune levels actually taken

A loop program running the levels of `scertD` (`lvProg`) stops at the first level that is not a
prune; its invariant is "the levels so far were `ℓ` prunes". This file states `scertD` in that
form, with no bound on the number of iterations in the statement:

* `scIter ch Hs ℓ s` (`ℓ` prune levels, all taken: the state and the records, last one first),
  **`scIter_snoc`** (one more prune at the end prepends its record — the loop step),
  **`scRun_stable`** (after the last prune, `scRun k = scIter ℓ` for every `k ≥ ℓ`);
* **`scertD_iter`**: if `ℓ` prunes lead to a state `s'` with `scStep … s' = none`, then
  `scertD = (scBase s').map fun x => (x.1, applyPr Hs x.1 rs x.2)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation CombMap PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- **`ℓ` prune levels, all taken**: the state and the records (the last one first), or `none`
if a level before the `ℓ`-th is not a prune. -/
noncomputable def scIter (ch : ScChoice M) (Hs : List (Finset V)) :
    ℕ → ScSt D → Option (ScSt D × List (ScRec D))
  | 0, s => some (s, [])
  | ℓ + 1, s =>
    match scStep ch Hs s with
    | none => none
    | some (s', r) => (scIter ch Hs ℓ s').map fun p => (p.1, p.2 ++ [r])

/-- **One more prune at the end** prepends its record. -/
theorem scIter_snoc (ch : ScChoice M) (Hs : List (Finset V)) :
    ∀ (ℓ : ℕ) (s s' s'' : ScSt D) (rs : List (ScRec D)) (r : ScRec D),
      scIter ch Hs ℓ s = some (s', rs) → scStep ch Hs s' = some (s'', r) →
      scIter ch Hs (ℓ + 1) s = some (s'', r :: rs) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro s s' s'' rs r h h'
    simp only [scIter, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [scIter, h', Option.map_some, List.nil_append]
  | succ ℓ ih =>
    intro s s' s'' rs r h h'
    rw [scIter] at h ⊢
    cases hs : scStep ch Hs s with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨s₁, r₁⟩ := p
      rw [hs] at h
      simp only at h ⊢
      cases h1 : scIter ch Hs ℓ s₁ with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some q =>
        obtain ⟨s₂, rs₂⟩ := q
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih s₁ s₂ s'' rs₂ r h1 h']
        simp

/-- **After the last prune the bounded loop is stable.** -/
theorem scRun_stable (ch : ScChoice M) (Hs : List (Finset V)) :
    ∀ (ℓ : ℕ) (s s' : ScSt D) (rs : List (ScRec D)), scIter ch Hs ℓ s = some (s', rs) →
      scStep ch Hs s' = none → ∀ k, ℓ ≤ k → scRun ch Hs k s = (s', rs) := by
  intro ℓ
  induction ℓ with
  | zero =>
    intro s s' rs h hn k _
    simp only [scIter, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases k with
    | zero => rfl
    | succ k => simp only [scRun, hn]
  | succ ℓ ih =>
    intro s s' rs h hn k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [scIter] at h
    cases hs : scStep ch Hs s with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some p =>
      obtain ⟨s₁, r₁⟩ := p
      rw [hs] at h
      simp only at h
      cases h1 : scIter ch Hs ℓ s₁ with
      | none => rw [h1] at h; exact absurd h (by simp)
      | some q =>
        obtain ⟨s₂, rs₂⟩ := q
        rw [h1] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [scRun, hs]
        rw [ih s₁ s₂ rs₂ h1 hn k (by omega)]

/-- **`scertD` from the prune levels actually taken**: if `ℓ` prunes lead to `s'` and the level
at `s'` is not a prune, `scertD` is the base case at `s'` with the records applied backwards. -/
theorem scertD_iter (ch : ScChoice M) (Hs : List (Finset V)) {ℓ : ℕ} {s s' : ScSt D}
    {rs : List (ScRec D)} (h : scIter ch Hs ℓ s = some (s', rs)) (hn : scStep ch Hs s' = none) :
    scertD ch Hs s.1 s.2.1 s.2.2 =
      (scBase ch Hs s').map fun x => (x.1, applyPr Hs x.1 rs x.2) := by
  have hk := scertD_loop ch Hs (ℓ + scDepth ch Hs s.1 s.2.1 s.2.2) s (by omega)
  rw [scRun_stable ch Hs ℓ s s' rs h hn _ (by omega)] at hk
  exact hk

end BKMNW

end PlanarFlow
