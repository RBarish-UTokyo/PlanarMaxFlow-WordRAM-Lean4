module

public import PlanarFlow.BKMNW.ScertDepth

/-!
# `scertD` as a loop: a bounded number of prunes, a base case, the prunes applied backwards

The recursion of `scertD` is tail-shaped up to the item update: every prune level replaces
`(N, τ, ex)` by `(K, ret τ K, ex')` and records `(N, K, a₀)`; the base case (Miller's separator,
or the cut at a hole, or failure) returns a path `ρ` and items; then the records are applied by
`pruneI` from the last one back (they need the final `ρ`, through `newHole Hs ρ.mverts`). With
`scDepth_le_nTouch` the number of prune levels is at most `nTouch`, so a program may run this
loop with a fixed bound of iterations (`≤ 6` on the pieces of the decomposition).

* `ScSt` (the state `(N, τ, ex)`), `scStep` (the prune level, if it applies), `scBase` (the
  non-recursive branches), **`scertD_step`** (the one-level equation),
  `scDepth_step` (the depth drops by one along a prune);
* `scRun ch Hs k s` (iterate `scStep` at most `k` times: final state and the records, last first),
  `applyPr` (the records applied by `pruneI`), **`scertD_loop`**: for `k ≥ scDepth`,
  `scertD = (scBase (final state)).map fun r => (r.1, applyPr Hs r.1 records r.2)`;
  **`scertD_loop_scChoiceE`** (`k = nTouch M N Hs` iterations for the choices `scChoiceE`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation CombMap PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- The state of the certificate recursion: the darts, the rotation, the extra weights. -/
abbrev ScSt (D : Type*) := Finset D × Perm D × (D → ℕ)

/-- A record of a prune: the darts `N` before, the kept component `K`, the anchor `a₀`. -/
abbrev ScRec (D : Type*) := Finset D × Finset D × D

open Classical in
/-- **The prune level of `scertD`**, if it applies: the next state and the record. -/
noncomputable def scStep (ch : ScChoice M) (Hs : List (Finset V)) (s : ScSt D) :
    Option (ScSt D × ScRec D) :=
  if NoCut M s.1 Hs then none
  else
    match ch.hole s.1 with
    | none => none
    | some g =>
      match ch.heavy s.1 g s.2.2 with
      | some z =>
        match ch.anchor (comp M s.1 Hs g z) g with
        | none => none
        | some a₀ =>
          if (comp M s.1 Hs g z).card < s.1.card then
            some ((comp M s.1 Hs g z, ret s.2.1 (comp M s.1 Hs g z),
              fun d => s.2.2 d + if d = a₀ then ∑ d ∈ s.1 \ comp M s.1 Hs g z, (1 + s.2.2 d)
                else 0), (s.1, comp M s.1 Hs g z, a₀))
          else none
      | none => none

open Classical in
/-- **The non-recursive branches of `scertD`**: Miller's separator when no hole is a cut vertex;
the cut at the hole when no component is heavy; failure otherwise. -/
noncomputable def scBase (ch : ScChoice M) (Hs : List (Finset V)) (s : ScSt D) :
    Option (HPath M × Finset (Finset D)) :=
  if NoCut M s.1 Hs then
    (if h : Stable s.2.1 s.1 ∧ Stable (revPerm M) s.1 then
      (ch.sep s.1 s.2.1 h.1 h.2 s.2.2).map fun r => (corePath h.1 h.2 r.1,
        {sideItem h.1 h.2 (coreI h.1 h.2 r.1 r.2), sideItem h.1 h.2 (coreO h.1 h.2 r.1 r.2)})
    else none)
  else
    match ch.hole s.1 with
    | none => none
    | some g =>
      match ch.heavy s.1 g s.2.2 with
      | some _ => none
      | none =>
        match ch.anchor s.1 g with
        | none => none
        | some a₁ => some (cutCert M Hs s.1 g a₁)

/-- **The one-level equation of `scertD`**: a prune level recurses and prunes the items; else the
base case. -/
theorem scertD_step (ch : ScChoice M) (Hs : List (Finset V)) (s : ScSt D) :
    scertD ch Hs s.1 s.2.1 s.2.2 =
      match scStep ch Hs s with
      | none => scBase ch Hs s
      | some (s', r) => (scertD ch Hs s'.1 s'.2.1 s'.2.2).map
          fun x => (x.1, pruneI Hs r.1 r.2.1 r.2.2 x.1 x.2) := by
  obtain ⟨N, τ, ex⟩ := s
  rw [scertD]
  by_cases hnc : NoCut M N Hs
  · simp only [scStep, scBase, hnc, ↓reduceIte]
  · simp only [scStep, scBase, hnc, ↓reduceIte]
    rcases hh : ch.hole N with _ | g
    · rfl
    · simp only
      rcases hz : ch.heavy N g ex with _ | z
      · (try simp only); rfl
      · simp only
        rcases ha : ch.anchor (comp M N Hs g z) g with _ | a₀
        · simp only
        · simp only
          by_cases hK : (comp M N Hs g z).card < N.card
          · simp only [hK, ↓reduceIte, ↓reduceDIte]
          · simp only [hK, ↓reduceIte, ↓reduceDIte]

/-- The depth along a prune level. -/
theorem scDepth_step {ch : ScChoice M} {Hs : List (Finset V)} {s s' : ScSt D} {r : ScRec D}
    (h : scStep ch Hs s = some (s', r)) :
    scDepth ch Hs s.1 s.2.1 s.2.2 = scDepth ch Hs s'.1 s'.2.1 s'.2.2 + 1 := by
  obtain ⟨N, τ, ex⟩ := s
  rw [scDepth]
  by_cases hnc : NoCut M N Hs
  · simp [scStep, hnc] at h
  · simp only [scStep, hnc, ↓reduceIte] at h
    simp only [hnc, ↓reduceIte]
    rcases hh : ch.hole N with _ | g
    · rw [hh] at h; exact absurd h (by simp)
    · rw [hh] at h
      simp only at h ⊢
      rcases hz : ch.heavy N g ex with _ | z
      · rw [hz] at h; exact absurd h (by simp)
      · rw [hz] at h
        simp only at h ⊢
        rcases ha : ch.anchor (comp M N Hs g z) g with _ | a₀
        · rw [ha] at h; exact absurd h (by simp)
        · rw [ha] at h
          simp only at h ⊢
          by_cases hK : (comp M N Hs g z).card < N.card
          · simp only [hK, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            simp only [hK, ↓reduceDIte]
          · simp [hK] at h

/-- **Iterate the prune level at most `k` times**: the final state and the records (the last
one first). -/
noncomputable def scRun (ch : ScChoice M) (Hs : List (Finset V)) : ℕ → ScSt D → ScSt D × List (ScRec D)
  | 0, s => (s, [])
  | k + 1, s =>
    match scStep ch Hs s with
    | none => (s, [])
    | some (s', r) => ((scRun ch Hs k s').1, (scRun ch Hs k s').2 ++ [r])

/-- The records applied to the items by `pruneI`, the last one first. -/
def applyPr (Hs : List (Finset V)) (ρ : HPath M) : List (ScRec D) → Finset (Finset D) →
    Finset (Finset D)
  | [], I => I
  | r :: rs, I => applyPr Hs ρ rs (pruneI Hs r.1 r.2.1 r.2.2 ρ I)

lemma applyPr_append (Hs : List (Finset V)) (ρ : HPath M) (rs : List (ScRec D)) (r : ScRec D)
    (I : Finset (Finset D)) :
    applyPr Hs ρ (rs ++ [r]) I = pruneI Hs r.1 r.2.1 r.2.2 ρ (applyPr Hs ρ rs I) := by
  induction rs generalizing I with
  | nil => rfl
  | cons r' rs ih => exact ih _

/-- **`scertD` as a loop**: with at least `scDepth` iterations, `scertD` is the base case of the
final state with the records applied backwards. -/
theorem scertD_loop (ch : ScChoice M) (Hs : List (Finset V)) :
    ∀ (k : ℕ) (s : ScSt D), scDepth ch Hs s.1 s.2.1 s.2.2 ≤ k →
      scertD ch Hs s.1 s.2.1 s.2.2 = (scBase ch Hs (scRun ch Hs k s).1).map
        fun x => (x.1, applyPr Hs x.1 (scRun ch Hs k s).2 x.2) := by
  intro k
  induction k with
  | zero =>
    intro s hs
    rw [scertD_step]
    cases h : scStep ch Hs s with
    | none =>
      simp only [scRun]
      cases scBase ch Hs s <;> rfl
    | some p =>
      obtain ⟨s', r⟩ := p
      have := scDepth_step h
      omega
  | succ k ih =>
    intro s hs
    rw [scertD_step]
    cases h : scStep ch Hs s with
    | none =>
      simp only [scRun, h]
      cases scBase ch Hs s <;> rfl
    | some p =>
      obtain ⟨s', r⟩ := p
      have hd := scDepth_step h
      simp only [scRun, h]
      rw [ih s' (by omega), Option.map_map]
      congr 1
      funext x
      simp only [Function.comp, applyPr_append]

open Classical in
/-- **`scertD` with the choices `scChoiceE` is a loop of `nTouch` iterations** (for a connected,
rev-closed `N`, holes pairwise disjoint): `≤ 6` iterations on the pieces of the decomposition. -/
theorem scertD_loop_scChoiceE (sepF : SepFn M) (e : ℕ → D) (n : ℕ) {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) (A W : ℕ) {N : Finset D} (τ : Perm D) (ex : D → ℕ)
    (hB : Stable (revPerm M) N) (hconn : ∀ x ∈ N, ∀ y ∈ N, ReflTransGen (HStep M N Hs) x y) :
    scertD (scChoiceE M sepF e n Hs A W) Hs N τ ex =
      (scBase (scChoiceE M sepF e n Hs A W) Hs
          (scRun (scChoiceE M sepF e n Hs A W) Hs (nTouch M N Hs) (N, τ, ex)).1).map
        fun x => (x.1, applyPr Hs x.1
          (scRun (scChoiceE M sepF e n Hs A W) Hs (nTouch M N Hs) (N, τ, ex)).2 x.2) := by
  obtain ⟨h1, h2⟩ := scDepth_scChoiceE sepF e n Hs A W
  exact scertD_loop _ Hs _ (N, τ, ex) (scDepth_le_nTouch hd _ h1 h2 ex hB hconn)

end BKMNW

end PlanarFlow
