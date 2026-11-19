module

public import PlanarFlow.NegSSSP.BFExec
public import PlanarFlow.Monge.DDGBF2O

/-!
# The Bellman–Ford calls of the recursion, realized by `bfDDG2O` (missing arcs allowed)

`PlanarFlow/NegSSSP/BFExec.lean` realizes the calls of `bf` of the recursion for negative
lengths (`PlanarFlow.NegSSSP.step`) when both child dense distance graphs are complete. This
file removes the completeness hypotheses.

## Where the missing arcs come from

The length `(childDDG N mssp P ℓ δ B).len u v` is `mssp P (redLen N ℓ δ) B u v` shifted by
`δ v - δ u`; under `PieceMSSPSpec` it is the distance from `u` to `v` in the piece graph of `P`
(the darts of `P`, directed from tail to head, with the reduced lengths), so it is `none` exactly
when **no walk of darts of `P` leads from `u` to `v`**. Neither `OneFace` nor `PieceMSSPSpec`
makes `P` closed under reversal, and the decomposition does not either: a part is the set of
darts of the piece whose triangle of the stellar subdivision lies on one side of the separating
cycle (`PlanarFlow.NegSSSP.side`), so the two darts of an edge lying along the cycle go to
different parts. Reachability inside a part can be **one-directional** (for example a part whose
only dart from `a` to `b` is `a → b`, with `a`, `b` shared vertices). So the dense distance
graph of a part is not block-diagonal with complete blocks; its lengths satisfy only the crossing
inequality with missing arcs, `PlanarFlow.Monge.CrossingO` (`crossing_step_parts`).

## The fix (no change to the graphs of the algorithm)

The machine program `PlanarFlow.Monge.bfDDG2O` (`PlanarFlow/Monge/DDGBF2O.lean`) is Bellman–Ford
over the union of two dense distance graphs **with missing arcs**: a half block of the level
loop is then Monge in the extended sense (`+∞` for a missing arc), and SMAWK runs on the totally
monotone matrix of `PlanarFlow/Monge/ExtMonge.lean` (missing entries replaced by large values
ordered around the first finite entry of the row, rows without an arc replaced by copies of a
genuine row), read from static tables (`tVal`, `tMul`, `finB`). Only existing arcs are relaxed;
the union digraph `ddg2O` has exactly the arcs of `H₁.join H₂` between distinct vertices.

* `isPot_join_of_feas2O`, `feas2O_of_isPot_join`, `potOut_join_of_outcomeO`: the bridge between
  `H₁.join H₂` and `ddg2O` (arcs `i → j` with `X i j = (H.len (β i) (β j)).isSome`, lengths
  `matOf H β`), with nonnegative loops (`DDG.join` keeps an arc `v → v` when `H.len v v` is
  defined; for the child graphs `childDDG_loop_nonneg`). No completeness is assumed.
* `bf2StartO`: the input laid out from address `0` with the tables of both matrices, the bound
  `Hb b D = Σ |D s t| + b + 1`; `bf2StartO_spec`.
* `bfDDG2O_join_exec`: the run from `bf2StartO` halts within `bf2CostO b` steps with a `PotOut`
  output of `H₁.join H₂`.
* `step_bf_execO`: **every call of `bf` at a node of the recursion** (the hypotheses of
  `crossing_step_parts`, no completeness) is realized this way, with `b = |B|` and
  `bf2CostO b ≤ 7600 (b + 1)² lg b` (`bf2CostO_le_lg`); it fits a cost field
  `bf b := 7600 (b + 1)² lg b`.

## The tables

The tables `tVal`, `tMul`, `finB` (for each pair `(s, t)`: whether the arc exists, and the entry
of the copied matrix of its half block without the shift) are part of the starting layout
`bf2StartO`, defined mathematically from the lengths. The machine pass computing them from the
plain encoding (arc flags and lengths) is `PlanarFlow.Monge.prepO`
(`PlanarFlow/Monge/PrepO.lean`); the run from the plain encoding, `prepO` for both matrices then
`bfDDG2O`, is `PlanarFlow.NegSSSP.bfFull` (`PlanarFlow/NegSSSP/BFExecP.lean`, within
`7900 (b + 1)² lg b` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

/-- `CrossingO` (lengths in `Option ℤ`) is `CrossingX` for `isSome` and `getD 0`. -/
theorem CrossingO.crossingX {b : ℕ} {D : ℕ → ℕ → Option ℤ} (h : CrossingO b D) :
    CrossingX b (fun i j => (D i j).isSome) (fun i j => (D i j).getD 0) := by
  intro i i' j j' hi hj hi' hj' hsep h1 h2
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.1 h2
  obtain ⟨x, y, hx, hy, hle⟩ := h i i' j j' hi hj hi' hj' hsep a a' ha ha'
  refine ⟨by show (D i j').isSome; rw [hx]; rfl, by show (D i' j).isSome; rw [hy]; rfl, ?_⟩
  show (D i j').getD 0 + (D i' j).getD 0 ≤ (D i j).getD 0 + (D i' j').getD 0
  rw [hx, hy, ha, ha']
  exact hle

end Monge

namespace NegSSSP

open Finset BKMNW Monge WordRAM WordRAM.Machine WordRAM.Programs

/-! ### The bridge between `DDG.join` and `ddg2O` -/

section Bridge

variable {V : Type*} [DecidableEq V]

/-- The arc pattern of `H` in the order `β`. -/
def arcOf (H : DDG V) (β : ℕ → V) (i j : ℕ) : Prop := (H.len (β i) (β j)).isSome

variable {b : ℕ} {β₁ β₂ : ℕ → V} {B : Finset V} {H₁ H₂ : DDG V}

/-- A feasible potential of both matrices is, through `β₁⁻¹`, a feasible potential of the
union `H₁.join H₂` (the loops being nonnegative). -/
theorem isPot_join_of_feas2O (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) (hl₁ : ∀ v ∈ B, 0 ≤ (H₁.len v v).getD 0)
    (hl₂ : ∀ v ∈ B, 0 ≤ (H₂.len v v).getD 0) {E : ℕ → ℤ}
    (hE : Feas2O b (arcOf H₁ β₁) (matOf H₁ β₁) (arcOf H₂ β₂) (matOf H₂ β₂) (permOf b β₁ β₂) E) :
    (H₁.join H₂).IsPot (fun v => E (enumInv b β₁ v)) := by
  rintro (⟨⟨u, v⟩, hu, hv, hs⟩ | ⟨⟨u, v⟩, hu, hv, hs⟩)
  · change u ∈ H₁.bdry at hu
    change v ∈ H₁.bdry at hv
    change (H₁.len u v).isSome at hs
    show E (enumInv b β₁ v) ≤ E (enumInv b β₁ u) + (H₁.len u v).getD 0
    rw [hB₁] at hu hv
    by_cases huv : u = v
    · subst huv; have := hl₁ u hu; omega
    · obtain ⟨hi, ei⟩ := enumInv_spec e₁ hu
      obtain ⟨hj, ej⟩ := enumInv_spec e₁ hv
      have hij : enumInv b β₁ u ≠ enumInv b β₁ v := fun h => huv (by rw [← ei, ← ej, h])
      have := (hE _ _ hi hj hij).1 (by show (H₁.len _ _).isSome; rw [ei, ej]; exact hs)
      simp only [matOf, ei, ej] at this
      exact this
  · change u ∈ H₂.bdry at hu
    change v ∈ H₂.bdry at hv
    change (H₂.len u v).isSome at hs
    show E (enumInv b β₁ v) ≤ E (enumInv b β₁ u) + (H₂.len u v).getD 0
    rw [hB₂] at hu hv
    by_cases huv : u = v
    · subst huv; have := hl₂ u hu; omega
    · obtain ⟨hi, ei⟩ := enumInv_spec e₂ hu
      obtain ⟨hj, ej⟩ := enumInv_spec e₂ hv
      have hij : enumInv b β₂ u ≠ enumInv b β₂ v := fun h => huv (by rw [← ei, ← ej, h])
      have := (hE _ _ hi hj hij).2 (by show (H₂.len _ _).isSome; rw [ei, ej]; exact hs)
      simp only [matOf, permOf, ei, ej] at this
      exact this

/-- A feasible potential of the union is, through `β₁`, a feasible potential of both matrices
on their arcs. -/
theorem feas2O_of_isPot_join (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) {p : V → ℤ} (hp : (H₁.join H₂).IsPot p) :
    Feas2O b (arcOf H₁ β₁) (matOf H₁ β₁) (arcOf H₂ β₂) (matOf H₂ β₂) (permOf b β₁ β₂)
      (fun i => p (β₁ i)) := by
  intro i j hi hj _
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have := hp (.inl ⟨(β₁ i, β₁ j), hB₁ ▸ e₁.mem i hi, hB₁ ▸ e₁.mem j hj, hx⟩)
    simp only [DDG.join] at this
    exact this
  · have := hp (.inr ⟨(β₂ i, β₂ j), hB₂ ▸ e₂.mem i hi, hB₂ ▸ e₂.mem j hj, hx⟩)
    simp only [DDG.join] at this
    simp only [(permOf_spec e₁ e₂ hi).2, (permOf_spec e₁ e₂ hj).2]
    exact this

/-- **The union `H₁.join H₂` has a feasible potential iff `ddg2O` has one** (no completeness). -/
theorem hasPot_join_iffO (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) (hl₁ : ∀ v ∈ B, 0 ≤ (H₁.len v v).getD 0)
    (hl₂ : ∀ v ∈ B, 0 ≤ (H₂.len v v).getD 0) :
    (∃ p, (H₁.join H₂).IsPot p) ↔ HasPot2O b (arcOf H₁ β₁) (matOf H₁ β₁) (arcOf H₂ β₂)
      (matOf H₂ β₂) (permOf b β₁ β₂) := by
  rw [hasPot2O_iff (isPermB_permOf e₁ e₂)]
  exact ⟨fun ⟨p, hp⟩ => ⟨_, feas2O_of_isPot_join hB₁ hB₂ e₁ e₂ hp⟩,
    fun ⟨E, hE⟩ => ⟨_, isPot_join_of_feas2O hB₁ hB₂ e₁ e₂ hl₁ hl₂ hE⟩⟩

/-- **The outcome of `bfDDG2O` is a `PotOut` output of the union `H₁.join H₂`**, the values read
through `β₁⁻¹`. -/
theorem potOut_join_of_outcomeO (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) (hl₁ : ∀ v ∈ B, 0 ≤ (H₁.len v v).getD 0)
    (hl₂ : ∀ v ∈ B, 0 ≤ (H₂.len v v).getD 0) {E : ℕ → ℤ} {flag : ℕ}
    (h : (flag = 0 ∧ Feas2O b (arcOf H₁ β₁) (matOf H₁ β₁) (arcOf H₂ β₂) (matOf H₂ β₂)
        (permOf b β₁ β₂) E) ∨
      (flag = 1 ∧ ¬ ∃ E', Feas2O b (arcOf H₁ β₁) (matOf H₁ β₁) (arcOf H₂ β₂) (matOf H₂ β₂)
        (permOf b β₁ β₂) E')) :
    PotOut (H₁.join H₂) (if flag = 0 then some (fun v => E (enumInv b β₁ v)) else none) := by
  rcases h with ⟨h0, hp⟩ | ⟨h1, hn⟩
  · simp only [h0, ↓reduceIte]; exact isPot_join_of_feas2O hB₁ hB₂ e₁ e₂ hl₁ hl₂ hp
  · simp only [h1, one_ne_zero, ↓reduceIte]
    exact fun ⟨p, hp⟩ => hn ⟨_, feas2O_of_isPot_join hB₁ hB₂ e₁ e₂ hp⟩

end Bridge

/-! ### A starting configuration -/

/-- A bound above the lengths: `Σ |D s t| + b + 1`. -/
noncomputable def Hb (b : ℕ) (D : ℕ → ℕ → ℤ) : ℝ :=
  ∑ s ∈ range b, ∑ t ∈ range b, |(D s t : ℝ)| + b + 1

/-- `Hb` bounds the lengths plus `b`. -/
lemma lt_Hb {b : ℕ} {D : ℕ → ℕ → ℤ} {s t : ℕ} (hs : s < b) (ht : t < b) :
    (D s t : ℝ) + b < Hb b D := by
  unfold Hb
  have h1 : |(D s t : ℝ)| ≤ ∑ t ∈ range b, |(D s t : ℝ)| :=
    single_le_sum (f := fun t => |(D s t : ℝ)|) (fun _ _ => abs_nonneg _) (mem_range.2 ht)
  have h2 : ∑ t ∈ range b, |(D s t : ℝ)| ≤ ∑ s ∈ range b, ∑ t ∈ range b, |(D s t : ℝ)| :=
    single_le_sum (f := fun s => ∑ t ∈ range b, |(D s t : ℝ)|)
      (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _) (mem_range.2 hs)
  have := le_abs_self (D s t : ℝ)
  linarith

/-- The real table word at `a`, `Vb ≤ a < Vb + 2 b²`. -/
noncomputable def tabR (b : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (Vb a : ℕ) : ℝ :=
  if (a - Vb) % 2 = 0 then tVal b X D (Hb b D) ((a - Vb) / 2 / b) ((a - Vb) / 2 % b)
  else tMul b X ((a - Vb) / 2 / b) ((a - Vb) / 2 % b)

/-- The input of `bfDDG2O` laid out from address `0`: the scratch cells at `pb = 0`, the values
at `5b + 2`, the second values at `6b + 2`, the tables of matrix 1 at `7b + 2` and of matrix 2
at `7b + 2 + 2b²` (real and natural memory), `π` at `5b + 2` (natural memory). -/
noncomputable def bf2StartO (b : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (X₂ : ℕ → ℕ → Prop)
    (D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) : Config where
  pc := 0
  nreg := fun r => if r = 1 then b else if r = 2 then 7 * b + 2 else if r = 3 then 5 * b + 2
    else if r = 7 then 7 * b + 2 + 2 * (b * b) else if r = 8 then 6 * b + 2
    else if r = 9 then 5 * b + 2 else 0
  rreg := fun _ => 0
  nmem := fun a => if 5 * b + 2 ≤ a ∧ a < 6 * b + 2 then π (a - (5 * b + 2))
    else if 7 * b + 2 ≤ a ∧ a < 7 * b + 2 + 2 * (b * b) then
      finB X₁ ((a - (7 * b + 2)) / 2 / b) ((a - (7 * b + 2)) / 2 % b)
    else if 7 * b + 2 + 2 * (b * b) ≤ a ∧ a < 7 * b + 2 + 2 * (b * b) + 2 * (b * b) then
      finB X₂ ((a - (7 * b + 2 + 2 * (b * b))) / 2 / b)
        ((a - (7 * b + 2 + 2 * (b * b))) / 2 % b)
    else 0
  rmem := fun a =>
    if 7 * b + 2 ≤ a ∧ a < 7 * b + 2 + 2 * (b * b) then tabR b X₁ D₁ (7 * b + 2) a
    else if 7 * b + 2 + 2 * (b * b) ≤ a ∧ a < 7 * b + 2 + 2 * (b * b) + 2 * (b * b) then
      tabR b X₂ D₂ (7 * b + 2 + 2 * (b * b)) a
    else 0
  output := []

/-- The word bound of `bf2StartO`. -/
def bf2WO (b : ℕ) : ℕ := 4 * (b * b) + 11 * b + 12

/-- The decoding of a table address. -/
lemma tab_dec {b s t : ℕ} (hs : s < b) (ht : t < b) :
    (2 * (s * b + t)) / 2 / b = s ∧ (2 * (s * b + t)) / 2 % b = t ∧
      (2 * (s * b + t) + 1) / 2 / b = s ∧ (2 * (s * b + t) + 1) / 2 % b = t ∧
      2 * (s * b + t) + 1 < 2 * (b * b) := by
  obtain ⟨h1, h2, h3⟩ := rowcol hs ht
  have e1 : 2 * (s * b + t) / 2 = s * b + t := by omega
  have e2 : (2 * (s * b + t) + 1) / 2 = s * b + t := by omega
  rw [e1, e2]
  exact ⟨h1, h2, h1, h2, by omega⟩

/-- **`bf2StartO` meets the hypotheses of `bfDDG2O_exec`.** -/
theorem bf2StartO_spec {b : ℕ} {X₁ X₂ : ℕ → ℕ → Prop} {D₁ D₂ : ℕ → ℕ → ℤ} {π : ℕ → ℕ}
    (hπ : IsPermB b π) :
    Lay2O b (7 * b + 2) (5 * b + 2) (7 * b + 2 + 2 * (b * b)) (6 * b + 2) (5 * b + 2) 0
        (bf2WO b) ∧
      WordsBounded (bf2WO b) (bf2StartO b X₁ D₁ X₂ D₂ π) ∧
      (bf2StartO b X₁ D₁ X₂ D₂ π).nreg 1 = b ∧ (bf2StartO b X₁ D₁ X₂ D₂ π).nreg 2 = 7 * b + 2 ∧
      (bf2StartO b X₁ D₁ X₂ D₂ π).nreg 3 = 5 * b + 2 ∧ (bf2StartO b X₁ D₁ X₂ D₂ π).nreg 4 = 0 ∧
      (bf2StartO b X₁ D₁ X₂ D₂ π).nreg 7 = 7 * b + 2 + 2 * (b * b) ∧
      (bf2StartO b X₁ D₁ X₂ D₂ π).nreg 8 = 6 * b + 2 ∧
      (bf2StartO b X₁ D₁ X₂ D₂ π).nreg 9 = 5 * b + 2 ∧
      (∀ s t, s < b → t < b → (bf2StartO b X₁ D₁ X₂ D₂ π).rmem (7 * b + 2 + 2 * (s * b + t)) =
        tVal b X₁ D₁ (Hb b D₁) s t) ∧
      (∀ s t, s < b → t < b →
        (bf2StartO b X₁ D₁ X₂ D₂ π).rmem (7 * b + 2 + 2 * (s * b + t) + 1) = tMul b X₁ s t) ∧
      (∀ s t, s < b → t < b →
        (bf2StartO b X₁ D₁ X₂ D₂ π).nmem (7 * b + 2 + 2 * (s * b + t)) = finB X₁ s t) ∧
      (∀ s t, s < b → t < b → (bf2StartO b X₁ D₁ X₂ D₂ π).rmem
        (7 * b + 2 + 2 * (b * b) + 2 * (s * b + t)) = tVal b X₂ D₂ (Hb b D₂) s t) ∧
      (∀ s t, s < b → t < b → (bf2StartO b X₁ D₁ X₂ D₂ π).rmem
        (7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) + 1) = tMul b X₂ s t) ∧
      (∀ s t, s < b → t < b → (bf2StartO b X₁ D₁ X₂ D₂ π).nmem
        (7 * b + 2 + 2 * (b * b) + 2 * (s * b + t)) = finB X₂ s t) ∧
      (∀ i < b, (bf2StartO b X₁ D₁ X₂ D₂ π).nmem (5 * b + 2 + i) = π i) := by
  refine ⟨⟨by omega, by omega, by omega, by omega, by unfold bf2WO; omega, by omega,
    by unfold bf2WO; omega⟩, ⟨fun r => ?_, fun a => ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun s t hs ht => ?_, fun s t hs ht => ?_, fun s t hs ht => ?_, fun s t hs ht => ?_,
    fun s t hs ht => ?_, fun s t hs ht => ?_, fun i hi => ?_⟩
  · simp only [bf2StartO, bf2WO]; split_ifs <;> omega
  · simp only [bf2StartO, bf2WO]; split_ifs with h1 h2 h3
    · have := hπ.lt (a - (5 * b + 2)) (by omega); omega
    · have := finB_le (X := X₁) ((a - (7 * b + 2)) / 2 / b) ((a - (7 * b + 2)) / 2 % b); omega
    · have := finB_le (X := X₂) ((a - (7 * b + 2 + 2 * (b * b))) / 2 / b)
        ((a - (7 * b + 2 + 2 * (b * b))) / 2 % b); omega
    · omega
  all_goals first
    | (have hi' : 5 * b + 2 ≤ 5 * b + 2 + i ∧ 5 * b + 2 + i < 6 * b + 2 := ⟨by omega, by omega⟩
       simp only [bf2StartO, hi', and_self, ↓reduceIte]
       congr 1; omega)
    | skip
  all_goals obtain ⟨d1, d2, d3, d4, d5⟩ := tab_dec hs ht
  · have c1 : 7 * b + 2 ≤ 7 * b + 2 + 2 * (s * b + t) ∧
        7 * b + 2 + 2 * (s * b + t) < 7 * b + 2 + 2 * (b * b) := ⟨by omega, by omega⟩
    simp only [bf2StartO, c1, and_self, ↓reduceIte, tabR]
    rw [show 7 * b + 2 + 2 * (s * b + t) - (7 * b + 2) = 2 * (s * b + t) by omega,
      Nat.mul_mod_right, d1, d2]; rfl
  · have c1 : 7 * b + 2 ≤ 7 * b + 2 + 2 * (s * b + t) + 1 ∧
        7 * b + 2 + 2 * (s * b + t) + 1 < 7 * b + 2 + 2 * (b * b) := ⟨by omega, by omega⟩
    simp only [bf2StartO, c1, and_self, ↓reduceIte, tabR]
    rw [show 7 * b + 2 + 2 * (s * b + t) + 1 - (7 * b + 2) = 2 * (s * b + t) + 1 by omega,
      show (2 * (s * b + t) + 1) % 2 = 1 by omega, d3, d4]; rfl
  · have c0 : ¬ (5 * b + 2 ≤ 7 * b + 2 + 2 * (s * b + t) ∧
        7 * b + 2 + 2 * (s * b + t) < 6 * b + 2) := by omega
    have c1 : 7 * b + 2 ≤ 7 * b + 2 + 2 * (s * b + t) ∧
        7 * b + 2 + 2 * (s * b + t) < 7 * b + 2 + 2 * (b * b) := ⟨by omega, by omega⟩
    simp only [bf2StartO, c0, c1, and_self, ↓reduceIte]
    rw [show 7 * b + 2 + 2 * (s * b + t) - (7 * b + 2) = 2 * (s * b + t) by omega, d1, d2]
  · have c0 : ¬ (7 * b + 2 ≤ 7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) ∧
        7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) < 7 * b + 2 + 2 * (b * b)) := by omega
    have c1 : 7 * b + 2 + 2 * (b * b) ≤ 7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) ∧
        7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) < 7 * b + 2 + 2 * (b * b) + 2 * (b * b) :=
      ⟨by omega, by omega⟩
    simp only [bf2StartO, c0, c1, and_self, ↓reduceIte, tabR]
    rw [show 7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) - (7 * b + 2 + 2 * (b * b)) =
      2 * (s * b + t) by omega, Nat.mul_mod_right, d1, d2]; rfl
  · have c0 : ¬ (7 * b + 2 ≤ 7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) + 1 ∧
        7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) + 1 < 7 * b + 2 + 2 * (b * b)) := by omega
    have c1 : 7 * b + 2 + 2 * (b * b) ≤ 7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) + 1 ∧
        7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) + 1 < 7 * b + 2 + 2 * (b * b) + 2 * (b * b) :=
      ⟨by omega, by omega⟩
    simp only [bf2StartO, c0, c1, and_self, ↓reduceIte, tabR]
    rw [show 7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) + 1 - (7 * b + 2 + 2 * (b * b)) =
      2 * (s * b + t) + 1 by omega, show (2 * (s * b + t) + 1) % 2 = 1 by omega, d3, d4]; rfl
  · have c0 : ¬ (5 * b + 2 ≤ 7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) ∧
        7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) < 6 * b + 2) := by omega
    have c0' : ¬ (7 * b + 2 ≤ 7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) ∧
        7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) < 7 * b + 2 + 2 * (b * b)) := by omega
    have c1 : 7 * b + 2 + 2 * (b * b) ≤ 7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) ∧
        7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) < 7 * b + 2 + 2 * (b * b) + 2 * (b * b) :=
      ⟨by omega, by omega⟩
    simp only [bf2StartO, c0, c0', c1, and_self, ↓reduceIte]
    rw [show 7 * b + 2 + 2 * (b * b) + 2 * (s * b + t) - (7 * b + 2 + 2 * (b * b)) =
      2 * (s * b + t) by omega, d1, d2]

/-- The cost of `bfDDG2O` against `lg b = ⌊log₂ b⌋ + 1`: it fits a cost field
`bf b := 7600 (b + 1)² lg b`. -/
theorem bf2CostO_le_lg (b : ℕ) : bf2CostO b ≤ 7600 * (b + 1) ^ 2 * lg b := bf2CostO_le b

/-! ### The run on two dense distance graphs with missing arcs -/

section Run

variable {V : Type*} [DecidableEq V] {b : ℕ} {β₁ β₂ : ℕ → V} {B : Finset V} {H₁ H₂ : DDG V}

/-- **Bellman–Ford over the union of two crossing dense distance graphs with missing arcs, on
the machine.** For two dense distance graphs on `B` with nonnegative loops, whose lengths satisfy
the crossing inequality with missing arcs in the enumerations `β₁`, `β₂` of `B`, the run of
`bfDDG2O` from `bf2StartO` halts within `bf2CostO b` steps; with `E i` the value left at
`5b + 2 + i`, the outcome (`some (E ∘ β₁⁻¹)` when `r30 = 0`, `none` otherwise) is a `PotOut`
output of `H₁.join H₂`. -/
theorem bfDDG2O_join_exec (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) (hl₁ : ∀ v ∈ B, 0 ≤ (H₁.len v v).getD 0)
    (hl₂ : ∀ v ∈ B, 0 ≤ (H₂.len v v).getD 0)
    (hD₁ : CrossingO b (fun i j => H₁.len (β₁ i) (β₁ j)))
    (hD₂ : CrossingO b (fun i j => H₂.len (β₂ i) (β₂ j))) (I : Input) :
    ∃ (c' : Config) (steps : ℕ) (E : ℕ → ℤ),
      Exec I (bf2WO b) bfDDG2O (bf2StartO b (arcOf H₁ β₁) (matOf H₁ β₁) (arcOf H₂ β₂)
        (matOf H₂ β₂) (permOf b β₁ β₂)) c' steps ∧ steps ≤ bf2CostO b ∧
      (∀ i < b, c'.rmem (5 * b + 2 + i) = E i) ∧
      PotOut (H₁.join H₂)
        (if c'.nreg 30 = 0 then some (fun v => E (enumInv b β₁ v)) else none) := by
  have hπ := isPermB_permOf e₁ e₂
  obtain ⟨hL, hw, h1, h2, h3, h4, h7, h8, h9, hT₁, hM₁, hF₁, hT₂, hM₂, hF₂, hmπ⟩ :=
    bf2StartO_spec (X₁ := arcOf H₁ β₁) (D₁ := matOf H₁ β₁) (X₂ := arcOf H₂ β₂)
      (D₂ := matOf H₂ β₂) hπ
  obtain ⟨c', k, he, hk, E, hv, hout, -⟩ :=
    bfDDG2O_exec (P := I) hπ hD₁.crossingX hD₂.crossingX
      (fun s t hs ht _ => lt_Hb (D := matOf H₁ β₁) hs ht)
      (fun s t hs ht _ => lt_Hb (D := matOf H₂ β₂) hs ht) hL _ hw h1 h2 h3 h4 h7 h8 h9
      (fun s t hs ht _ => hT₁ s t hs ht) (fun s t hs ht _ => hM₁ s t hs ht)
      (fun s t hs ht _ => hF₁ s t hs ht) (fun s t hs ht _ => hT₂ s t hs ht)
      (fun s t hs ht _ => hM₂ s t hs ht) (fun s t hs ht _ => hF₂ s t hs ht) hmπ
  exact ⟨c', k, E, he, hk, hv, potOut_join_of_outcomeO hB₁ hB₂ e₁ e₂ hl₁ hl₂ hout⟩

end Run

/-! ### The calls of the recursion -/

section Step

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **Every call of `bf` at a node of the recursion is realized by a run of `bfDDG2O`**, missing
arcs allowed. Under the hypotheses of `crossing_step_parts` (each part on one face holding the
shared vertices `B = bdry N P₀ P₁`, `mssp` meeting `PieceMSSPSpec`, nonnegative reduced lengths),
for `b = |B|` and an enumeration `β` of `B`, a run of `bfDDG2O` halts within
`bf2CostO b ≤ 7600 (b + 1)² lg b` steps, and its outcome (`some`, the value of `v ∈ B` read at
`5b + 2 + β⁻¹ v`, when `r30 = 0`; `none` otherwise) is a `PotOut` output of the union
`H₁.join H₂`, as `BFDDGSpec` requires of the call. -/
theorem step_bf_execO {P₀ P₁ : Finset D} {q₀ q₁ k₀ k₁ : ℕ}
    (h₀ : OneFace N P₀ (bdry N P₀ P₁) q₀ k₀) (h₁ : OneFace N P₁ (bdry N P₀ P₁) q₁ k₁)
    (hB : (bdry N P₀ P₁).Nonempty)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {ℓ : D → ℤ} {δ₀ δ₁ : V → ℤ} (hnn₀ : ∀ d ∈ P₀, 0 ≤ redLen N ℓ δ₀ d)
    (hnn₁ : ∀ d ∈ P₁, 0 ≤ redLen N ℓ δ₁ d) (I : Input) :
    ∃ (b : ℕ) (β : ℕ → V) (W : ℕ) (c₀ c' : Config) (steps : ℕ) (E : ℕ → ℤ),
      b = (bdry N P₀ P₁).card ∧ IsEnum b β (bdry N P₀ P₁) ∧
      Exec I W bfDDG2O c₀ c' steps ∧ steps ≤ bf2CostO b ∧
      bf2CostO b ≤ 7600 * (b + 1) ^ 2 * lg b ∧ (∀ i < b, c'.rmem (5 * b + 2 + i) = E i) ∧
      PotOut ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).join
          (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)))
        (if c'.nreg 30 = 0 then some (fun v => E (enumInv b β v)) else none) := by
  obtain ⟨⟨b₀, β₀, m₀, s₀, i₀, cr₀, -⟩, ⟨b₁, β₁, m₁, s₁, i₁, cr₁, -⟩⟩ :=
    crossing_step_parts h₀ h₁ hB hmssp hnn₀ hnn₁
  have e₀ : IsEnum b₀ β₀ (bdry N P₀ P₁) := ⟨m₀, s₀, i₀⟩
  have e₁ : IsEnum b₁ β₁ (bdry N P₀ P₁) := ⟨m₁, s₁, i₁⟩
  have hb : b₁ = b₀ := e₁.card.trans e₀.card.symm
  subst hb
  obtain ⟨c', k, E, he, hk, hv, hout⟩ := bfDDG2O_join_exec (H₁ := childDDG N mssp P₀ ℓ δ₀ _)
    (H₂ := childDDG N mssp P₁ ℓ δ₁ _) rfl rfl e₀ e₁
    (fun v hv => childDDG_loop_nonneg hmssp hnn₀ hv)
    (fun v hv => childDDG_loop_nonneg hmssp hnn₁ hv) cr₀ cr₁ I
  exact ⟨b₁, β₀, _, _, c', k, E, e₀.card, e₀, he, hk, bf2CostO_le_lg _, hv, hout⟩

end Step

end NegSSSP

end PlanarFlow
