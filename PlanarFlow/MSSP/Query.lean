module

public import PlanarFlow.MSSP.NonCrossing

/-!
# The divide-and-conquer and its queries

The data structure of Das, Kipouridis, Probst Gutenberg and Wulff-Nilsen (SOSA 2022,
Algorithms 1 and 2), in the setting `PlanarFlow.MSSP.Hyp` (roots `r i = tail (g i)`, `i < k`, on
a face).

The recursion works on intervals `[i₁, i₂]` of roots: it stores the distances from the two
endpoints and, if `i₁ + 1 < i₂`, recurses on `[i₁, i]` and `[i, i₂]` for `i = (i₁ + i₂) / 2`. For
each subinterval `J = [j₁, j₂]` it contracts the trees hanging from the vertices `x` where the
shortest paths from `r j₁` and `r j₂` meet, on the side of the roots of `J` in the rotation at
`x` (`HangsIn`), and records for every vertex `u` the root `contr j₁ j₂ u` of its tree (`u` itself
when it hangs from no vertex) and the offset `offs j₁ j₂ u = dist (contr j₁ j₂ u) u`
(the article's `s_J(u)` and `δ_J(u)`).

A query for the distance from `r j` to `u` (`query`) returns the stored distance when `j` is an
endpoint, and otherwise asks the subinterval containing `j` for the distance to the root of the
tree of `u`, adding the offset.

* `odist_contr`: the contraction preserves the distances from the roots of the subinterval (the
  article's Corollary 5.5, distance form), from `dist_hangs`.
* `query_eq`: **every query returns the distance** (the article's Lemma 5.6).
* `query_steps_le`: a query makes at most `⌈log₂ (i₂ - i₁)⌉` recursive steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace MSSP

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

variable (M : CombMap D V F) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ)

/-- `u` hangs from `x` for the interval `[j₁, j₂]`, on the side of the roots of the interval. -/
def HangsIn (j₁ j₂ : ℕ) (x u : V) : Prop :=
  ∃ p₁ p₂ e, Hangs M S ℓ (M.tail (g j₁)) (M.tail (g j₂)) x u p₁ p₂ e ∧
    M.RotBetween (M.rev p₂.1) (M.rev p₁.1) e.1

open Classical in
/-- The root of the contracted tree of `u` for the interval `[j₁, j₂]` (the article's
`s_J(u)`): the vertex from which `u` hangs, or `u` itself. -/
noncomputable def contr (j₁ j₂ : ℕ) (u : V) : V :=
  if h : ∃ x, HangsIn M g S ℓ j₁ j₂ x u then h.choose else u

/-- The offset of `u` in its contracted tree (the article's `δ_J(u)`). -/
noncomputable def offs (j₁ j₂ : ℕ) (u : V) : ℤ :=
  dist (pieceGraph M S ℓ) (contr M g S ℓ j₁ j₂ u) u

/-- **The query** (the article's Algorithm 2) for the distance from the root `r j` to `u`, in the
recursion on the interval `[i₁, i₂]`. -/
noncomputable def query (j : ℕ) (i₁ i₂ : ℕ) (u : V) : Option ℤ :=
  if j = i₁ ∨ j = i₂ then odist (pieceGraph M S ℓ) (M.tail (g j)) u
  else if i₁ + 1 < i₂ then
    if j ≤ (i₁ + i₂) / 2 then
      (query j i₁ ((i₁ + i₂) / 2) (contr M g S ℓ i₁ ((i₁ + i₂) / 2) u)).map
        (· + offs M g S ℓ i₁ ((i₁ + i₂) / 2) u)
    else
      (query j ((i₁ + i₂) / 2) i₂ (contr M g S ℓ ((i₁ + i₂) / 2) i₂ u)).map
        (· + offs M g S ℓ ((i₁ + i₂) / 2) i₂ u)
  else none
termination_by i₂ - i₁
decreasing_by all_goals omega

/-- The number of recursive steps of a query. -/
def querySteps (j : ℕ) (i₁ i₂ : ℕ) : ℕ :=
  if j = i₁ ∨ j = i₂ then 0
  else if i₁ + 1 < i₂ then
    if j ≤ (i₁ + i₂) / 2 then querySteps j i₁ ((i₁ + i₂) / 2) + 1
    else querySteps j ((i₁ + i₂) / 2) i₂ + 1
  else 0
termination_by i₂ - i₁
decreasing_by all_goals omega

variable {M g S ℓ}

/-- A query makes at most `⌈log₂ (i₂ - i₁)⌉` recursive steps. -/
theorem query_steps_le (j : ℕ) : ∀ i₁ i₂, querySteps j i₁ i₂ ≤ Nat.clog 2 (i₂ - i₁) := by
  intro i₁ i₂
  induction h : i₂ - i₁ using Nat.strong_induction_on generalizing i₁ i₂ with
  | _ n ih =>
    rw [querySteps]
    have hc : 2 ≤ n → Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := fun hn =>
      Nat.clog_of_two_le (by norm_num) hn
    split_ifs with h1 h2 h3
    · omega
    · have := ih _ (by omega) i₁ ((i₁ + i₂) / 2) rfl
      have := Nat.clog_mono_right 2 (show (i₁ + i₂) / 2 - i₁ ≤ (n + 1) / 2 by omega)
      rw [hc (by omega)]; omega
    · have := ih _ (by omega) ((i₁ + i₂) / 2) i₂ rfl
      have := Nat.clog_mono_right 2 (show i₂ - (i₁ + i₂) / 2 ≤ (n + 1) / 2 by omega)
      rw [hc (by omega)]; omega
    · omega

variable {k : ℕ} (H : Hyp M k g S ℓ)
include H

/-- **The contraction preserves the distances from the roots of the interval** (the article's
Corollary 5.5, distance form): the distance from `r j` to `u` is the distance to the root of the
contracted tree of `u`, plus the offset. -/
theorem odist_contr {j₁ j j₂ : ℕ} (h1 : j₁ ≤ j) (h2 : j ≤ j₂) (h12 : j₁ < j₂) (hk : j₂ < k)
    (u : V) :
    (odist (pieceGraph M S ℓ) (M.tail (g j)) (contr M g S ℓ j₁ j₂ u)).map
      (· + offs M g S ℓ j₁ j₂ u) = odist (pieceGraph M S ℓ) (M.tail (g j)) u := by
  unfold offs contr
  split_ifs with h
  · obtain ⟨p₁, p₂, e, hh, hrb⟩ := h.choose_spec
    obtain ⟨d1, d2⟩ := dist_hangs H h1 h2 h12 hk hh hrb
    unfold odist
    by_cases hx : Reach (pieceGraph M S ℓ) (M.tail (g j)) h.choose
    · simp only [hx, d1.2 hx, ↓reduceIte, Option.map_some, d2 hx]
    · have hu : ¬ Reach (pieceGraph M S ℓ) (M.tail (g j)) u := fun h' => hx (d1.1 h')
      simp only [hx, hu, ↓reduceIte, Option.map_none]
  · rw [dist_self H.nn, Option.map_congr (fun _ _ => add_zero _), Option.map_id']

/-- **Every query returns the distance** (the article's Lemma 5.6): for `i₁ ≤ j ≤ i₂ < k`, the
query on `[i₁, i₂]` returns the distance from the root `r j` to `u` (`none` when `u` is not
reachable). -/
theorem query_eq {j : ℕ} : ∀ {i₁ i₂ : ℕ}, i₁ ≤ j → j ≤ i₂ → i₂ < k → ∀ u,
    query M g S ℓ j i₁ i₂ u = odist (pieceGraph M S ℓ) (M.tail (g j)) u := by
  intro i₁ i₂ h1 h2 hk
  induction h : i₂ - i₁ using Nat.strong_induction_on generalizing i₁ i₂ with
  | _ n ih =>
    intro u
    rw [query]
    split_ifs with he hlt hle
    · rfl
    · rw [ih _ (by omega) h1 hle (by omega) rfl, odist_contr H h1 hle (by omega) (by omega)]
    · rw [ih _ (by omega) (by omega) h2 hk rfl,
        odist_contr H (by omega) h2 (by omega) hk]
    · omega

end MSSP

end PlanarFlow
