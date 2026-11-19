module

public import PlanarFlow.Monge.DDGBF2Pot
public import PlanarFlow.NegSSSP.FaceMonge

/-!
# The Bellman–Ford calls of the recursion, realized by `bfDDG2` for complete child graphs

At a node of the recursion for negative lengths (`PlanarFlow.NegSSSP.step`) the subroutine `bf`
is called on the dense distance graphs `H₁ = childDDG N mssp P₀ ℓ δ₀ B` and
`H₂ = childDDG N mssp P₁ ℓ δ₁ B` of the two parts on their shared vertices `B = bdry N P₀ P₁`,
and must return a `PotOut` output of the union `H₁.join H₂` (`BFDDGSpec`). This file realizes
these calls by the machine program `PlanarFlow.Monge.bfDDG2` when both child graphs are complete.

## The bridge (any two dense distance graphs on `B`)

* `IsEnum b β B`: `β 0, …, β (b - 1)` enumerate `B` without repetition (the form of the orders
  of `crossing_step_parts`); then `b = B.card` (`IsEnum.card`), `enumInv b β` is the inverse
  (`enumInv_apply`, `enumInv_spec`), and for two enumerations `β₁, β₂` of `B` the map
  `permOf b β₁ β₂ = β₁⁻¹ ∘ β₂` permutes `0, …, b - 1` (`isPermB_permOf`).
* `matOf H β i j = (H.len (β i) (β j)).getD 0`: the length matrix of `H` in the order `β`.
* With `D₁ = matOf H₁ β₁`, `D₂ = matOf H₂ β₂`, `π = permOf b β₁ β₂`, the arcs of
  `ddg2 b D₁ D₂ π` are, through `β₁`, the arcs of `H₁.join H₂` between distinct vertices.
  `isPot_join_of_feas2` and `feas2_of_isPot_join` transport feasible potentials both ways
  (`E ↦ E ∘ β₁⁻¹` and `p ↦ p ∘ β₁`), hence `hasPot_join_iff`, `isPot_join_of_ddg2`, and
  `potOut_join_of_outcome`: the outcome of `bfDDG2` (flag `0` with a feasible potential of both
  matrices, or flag `1` with none) gives `PotOut (H₁.join H₂)`, the values read through `β₁`.
* **Loops.** `DDG.join` has an arc `v → v` of length `(H.len v v).getD 0` whenever `H.len v v` is
  defined, while `ddg2` has no loops. A loop constrains a potential only if its length is
  negative (then there is no potential at all). The bridge therefore assumes the loops
  nonnegative (`hl₁`, `hl₂`). For the child graphs of the recursion this is proved
  (`childDDG_loop_nonneg`): `H.len v v` is the distance from `v` to itself in the part with
  nonnegative reduced lengths (`PieceMSSPSpec`), shifted by `δ v - δ v = 0`.

## The run

* `bf2Start b D₁ D₂ π`: the input laid out from address `0` (scratch cells at `pb = 0`, values at
  `5b + 2`, second values at `6b + 2`, `D₁` at `7b + 2`, `D₂` at `7b + 2 + b²` in the real
  memory, `π` at `5b + 2` in the natural memory, word bound `2b² + 11b + 12`); `bf2Start_spec`:
  it meets the hypotheses of `bfDDG2_exec`.
* `bfDDG2_join_exec`: for any two dense distance graphs on `B`, complete between distinct
  vertices, with nonnegative loops and crossing in orders `β₁`, `β₂`, the run of `bfDDG2` from
  `bf2Start` halts within `bf2Cost b` steps with an outcome that is a `PotOut` output of
  `H₁.join H₂` (flag `r30 ≠ 0` ↔ `none`; the value of `v ∈ B` at `5b + 2 + β₁⁻¹ v`).
* `step_bf_exec`: **at a node of the recursion** (the hypotheses of `crossing_step_parts`), when
  both child dense distance graphs are complete on `B`, the call of `bf` is realized this way,
  with `b = |B|` and the cost `bf2Cost b ≤ 6500 (b + 1)² lg b` (`bf2Cost_le_lg`): it fits a cost
  field `bf b := 6500 (b + 1)² lg b` (the field `cNegMach.bf` itself is not changed here).

## What is not covered: missing arcs

When some length `H.len u v` between distinct sources is `none` (the part is not strongly
connected between its sources), the child graph is not complete and none of this applies.
`bfDDG2` relaxes complete Monge matrices: the row minima of every block are taken by SMAWK on
the stored real lengths (`PlanarFlow.Monge.Crossing` on the lengths with `none` read as `0`).
What holds with missing arcs is only `PlanarFlow.Monge.CrossingO` (`none` read as an infinite
length), and replacing `none` by a finite length breaks the crossing inequality in general:
when an interleaved left-hand pair has a missing arc, so has the right-hand side, and the
inequality `M + x ≤ M + y` that remains for a large stand-in `M` need not hold. Handling this
case needs a program for Monge matrices with infinite entries (or a decomposition of the
matrices into complete Monge blocks), which is not done here.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW Monge WordRAM WordRAM.Machine WordRAM.Programs

/-! ### Enumerations of the shared vertices -/

section Enum

variable {V : Type*} [DecidableEq V]

/-- `β 0, …, β (b - 1)` enumerate `B` without repetition. -/
structure IsEnum (b : ℕ) (β : ℕ → V) (B : Finset V) : Prop where
  mem : ∀ i < b, β i ∈ B
  surj : ∀ v ∈ B, ∃ i < b, β i = v
  inj : ∀ i < b, ∀ i' < b, β i = β i' → i = i'

variable {b : ℕ} {β β₁ β₂ : ℕ → V} {B : Finset V}

/-- An enumeration has `|B|` terms. -/
theorem IsEnum.card (h : IsEnum b β B) : b = B.card := by
  have hB : (range b).image β = B := by
    ext v
    simp only [mem_image, mem_range]
    exact ⟨fun ⟨i, hi, e⟩ => e ▸ h.mem i hi, fun hv => h.surj v hv⟩
  rw [← hB, card_image_of_injOn (fun i hi i' hi' e =>
    h.inj i (by simpa using hi) i' (by simpa using hi') e), card_range]

/-- The inverse of an enumeration (`0` outside `B`). -/
noncomputable def enumInv (b : ℕ) (β : ℕ → V) (v : V) : ℕ := by
  classical
  exact if h : ∃ i, i < b ∧ β i = v then Classical.choose h else 0

/-- The inverse of an enumeration on `B`. -/
theorem enumInv_spec (h : IsEnum b β B) {v : V} (hv : v ∈ B) :
    enumInv b β v < b ∧ β (enumInv b β v) = v := by
  classical
  have hv' : ∃ i, i < b ∧ β i = v := h.surj v hv
  unfold enumInv
  rw [dite_eq_left_of_eq_true (eq_true hv')]
  exact Classical.choose_spec (of_eq_true (eq_true hv'))

/-- The inverse of an enumeration on its terms. -/
theorem enumInv_apply (h : IsEnum b β B) {i : ℕ} (hi : i < b) : enumInv b β (β i) = i := by
  have hs := enumInv_spec h (h.mem i hi)
  exact h.inj _ hs.1 i hi hs.2

/-- `β₁⁻¹ ∘ β₂`. -/
noncomputable def permOf (b : ℕ) (β₁ β₂ : ℕ → V) (i : ℕ) : ℕ := enumInv b β₁ (β₂ i)

/-- `β₁ ∘ (β₁⁻¹ ∘ β₂) = β₂`. -/
theorem permOf_spec (e₁ : IsEnum b β₁ B) (e₂ : IsEnum b β₂ B) {i : ℕ} (hi : i < b) :
    permOf b β₁ β₂ i < b ∧ β₁ (permOf b β₁ β₂ i) = β₂ i :=
  enumInv_spec e₁ (e₂.mem i hi)

/-- **`β₁⁻¹ ∘ β₂` permutes `0, …, b - 1`.** -/
theorem isPermB_permOf (e₁ : IsEnum b β₁ B) (e₂ : IsEnum b β₂ B) :
    IsPermB b (permOf b β₁ β₂) :=
  ⟨fun i hi => (permOf_spec e₁ e₂ hi).1, fun i j hi hj h => e₂.inj i hi j hj (by
    rw [← (permOf_spec e₁ e₂ hi).2, ← (permOf_spec e₁ e₂ hj).2, h])⟩

end Enum

/-! ### The bridge between `DDG.join` and `ddg2` -/

section Bridge

variable {V : Type*} [DecidableEq V]

/-- The length matrix of `H` in the order `β` (`none` read as `0`). -/
def matOf (H : DDG V) (β : ℕ → V) (i j : ℕ) : ℤ := (H.len (β i) (β j)).getD 0

variable {b : ℕ} {β₁ β₂ : ℕ → V} {B : Finset V} {H₁ H₂ : DDG V}

/-- A feasible potential of both matrices is, through `β₁⁻¹`, a feasible potential of the
union `H₁.join H₂` (the loops being nonnegative). -/
theorem isPot_join_of_feas2 (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) (hl₁ : ∀ v ∈ B, 0 ≤ (H₁.len v v).getD 0)
    (hl₂ : ∀ v ∈ B, 0 ≤ (H₂.len v v).getD 0) {E : ℕ → ℤ}
    (hE : Feas2 b (matOf H₁ β₁) (matOf H₂ β₂) (permOf b β₁ β₂) E) :
    (H₁.join H₂).IsPot (fun v => E (enumInv b β₁ v)) := by
  rintro (⟨⟨u, v⟩, hu, hv, -⟩ | ⟨⟨u, v⟩, hu, hv, -⟩)
  · change u ∈ H₁.bdry at hu
    change v ∈ H₁.bdry at hv
    show E (enumInv b β₁ v) ≤ E (enumInv b β₁ u) + (H₁.len u v).getD 0
    rw [hB₁] at hu hv
    by_cases huv : u = v
    · subst huv; have := hl₁ u hu; omega
    · obtain ⟨hi, ei⟩ := enumInv_spec e₁ hu
      obtain ⟨hj, ej⟩ := enumInv_spec e₁ hv
      have hij : enumInv b β₁ u ≠ enumInv b β₁ v := fun h => huv (by rw [← ei, ← ej, h])
      have := (hE _ _ hi hj hij).1
      simp only [matOf, ei, ej] at this
      exact this
  · change u ∈ H₂.bdry at hu
    change v ∈ H₂.bdry at hv
    show E (enumInv b β₁ v) ≤ E (enumInv b β₁ u) + (H₂.len u v).getD 0
    rw [hB₂] at hu hv
    by_cases huv : u = v
    · subst huv; have := hl₂ u hu; omega
    · obtain ⟨hi, ei⟩ := enumInv_spec e₂ hu
      obtain ⟨hj, ej⟩ := enumInv_spec e₂ hv
      have hij : enumInv b β₂ u ≠ enumInv b β₂ v := fun h => huv (by rw [← ei, ← ej, h])
      have := (hE _ _ hi hj hij).2
      simp only [matOf, permOf, ei, ej] at this
      exact this

/-- A feasible potential of the union is, through `β₁`, a feasible potential of both matrices
(the graphs being complete between distinct vertices). -/
theorem feas2_of_isPot_join (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) (hc₁ : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → (H₁.len u v).isSome)
    (hc₂ : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → (H₂.len u v).isSome) {p : V → ℤ}
    (hp : (H₁.join H₂).IsPot p) :
    Feas2 b (matOf H₁ β₁) (matOf H₂ β₂) (permOf b β₁ β₂) (fun i => p (β₁ i)) := by
  intro i j hi hj hij
  have hne₁ : β₁ i ≠ β₁ j := fun h => hij (e₁.inj i hi j hj h)
  have hne₂ : β₂ i ≠ β₂ j := fun h => hij (e₂.inj i hi j hj h)
  refine ⟨?_, ?_⟩
  · have := hp (.inl ⟨(β₁ i, β₁ j), hB₁ ▸ e₁.mem i hi, hB₁ ▸ e₁.mem j hj,
      hc₁ _ (e₁.mem i hi) _ (e₁.mem j hj) hne₁⟩)
    simp only [DDG.join] at this
    exact this
  · have := hp (.inr ⟨(β₂ i, β₂ j), hB₂ ▸ e₂.mem i hi, hB₂ ▸ e₂.mem j hj,
      hc₂ _ (e₂.mem i hi) _ (e₂.mem j hj) hne₂⟩)
    simp only [DDG.join] at this
    simp only [(permOf_spec e₁ e₂ hi).2, (permOf_spec e₁ e₂ hj).2]
    exact this

/-- **The union `H₁.join H₂` has a feasible potential iff `ddg2 b D₁ D₂ π` has one.** -/
theorem hasPot_join_iff (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) (hc₁ : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → (H₁.len u v).isSome)
    (hc₂ : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → (H₂.len u v).isSome)
    (hl₁ : ∀ v ∈ B, 0 ≤ (H₁.len v v).getD 0) (hl₂ : ∀ v ∈ B, 0 ≤ (H₂.len v v).getD 0) :
    (∃ p, (H₁.join H₂).IsPot p) ↔
      HasPot2 b (matOf H₁ β₁) (matOf H₂ β₂) (permOf b β₁ β₂) := by
  rw [hasPot2_iff (isPermB_permOf e₁ e₂)]
  exact ⟨fun ⟨p, hp⟩ => ⟨_, feas2_of_isPot_join hB₁ hB₂ e₁ e₂ hc₁ hc₂ hp⟩,
    fun ⟨E, hE⟩ => ⟨_, isPot_join_of_feas2 hB₁ hB₂ e₁ e₂ hl₁ hl₂ hE⟩⟩

/-- A feasible potential `q` of `ddg2 b D₁ D₂ π` is, through `β₁⁻¹`, one of the union. -/
theorem isPot_join_of_ddg2 (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) (hl₁ : ∀ v ∈ B, 0 ≤ (H₁.len v v).getD 0)
    (hl₂ : ∀ v ∈ B, 0 ≤ (H₂.len v v).getD 0) {q : Fin b → ℤ}
    (hq : (ddg2 b (matOf H₁ β₁) (matOf H₂ β₂) (permOf b β₁ β₂)).IsPot q) :
    (H₁.join H₂).IsPot (fun v => liftF b q (enumInv b β₁ v)) :=
  isPot_join_of_feas2 hB₁ hB₂ e₁ e₂ hl₁ hl₂ (feas2_of_isPot (isPermB_permOf e₁ e₂) hq)

/-- **The outcome of `bfDDG2` is a `PotOut` output of the union `H₁.join H₂`**, the values read
through `β₁⁻¹`. -/
theorem potOut_join_of_outcome (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) (hc₁ : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → (H₁.len u v).isSome)
    (hc₂ : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → (H₂.len u v).isSome)
    (hl₁ : ∀ v ∈ B, 0 ≤ (H₁.len v v).getD 0) (hl₂ : ∀ v ∈ B, 0 ≤ (H₂.len v v).getD 0)
    {E : ℕ → ℤ} {flag : ℕ}
    (h : (flag = 0 ∧ Feas2 b (matOf H₁ β₁) (matOf H₂ β₂) (permOf b β₁ β₂) E) ∨
      (flag = 1 ∧ ¬ ∃ E', Feas2 b (matOf H₁ β₁) (matOf H₂ β₂) (permOf b β₁ β₂) E')) :
    PotOut (H₁.join H₂) (if flag = 0 then some (fun v => E (enumInv b β₁ v)) else none) := by
  rcases h with ⟨h0, hp⟩ | ⟨h1, hn⟩
  · simp only [h0, ↓reduceIte]; exact isPot_join_of_feas2 hB₁ hB₂ e₁ e₂ hl₁ hl₂ hp
  · simp only [h1, one_ne_zero, ↓reduceIte]
    exact fun ⟨p, hp⟩ => hn ⟨_, feas2_of_isPot_join hB₁ hB₂ e₁ e₂ hc₁ hc₂ hp⟩

end Bridge

/-! ### A starting configuration -/

/-- The input of `bfDDG2` laid out from address `0`: the row-minima scratch cells at `pb = 0`,
the values at `5b + 2`, the second values at `6b + 2`, `D₁` at `7b + 2` and `D₂` at
`7b + 2 + b²` in the real memory, `π` at `5b + 2` in the natural memory. -/
noncomputable def bf2Start (b : ℕ) (D₁ D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) : Config where
  pc := 0
  nreg := fun r => if r = 1 then b else if r = 2 then 7 * b + 2 else if r = 3 then 5 * b + 2
    else if r = 7 then 7 * b + 2 + b * b else if r = 8 then 6 * b + 2
    else if r = 9 then 5 * b + 2 else 0
  rreg := fun _ => 0
  nmem := fun a => if 5 * b + 2 ≤ a ∧ a < 6 * b + 2 then π (a - (5 * b + 2)) else 0
  rmem := fun a =>
    if 7 * b + 2 ≤ a ∧ a < 7 * b + 2 + b * b then
      (D₁ ((a - (7 * b + 2)) / b) ((a - (7 * b + 2)) % b) : ℝ)
    else if 7 * b + 2 + b * b ≤ a ∧ a < 7 * b + 2 + b * b + b * b then
      (D₂ ((a - (7 * b + 2 + b * b)) / b) ((a - (7 * b + 2 + b * b)) % b) : ℝ)
    else 0
  output := []

/-- The word bound of `bf2Start`. -/
def bf2W (b : ℕ) : ℕ := 2 * (b * b) + 11 * b + 12

/-- The row and the column of the entry `i b + j` of a `b × b` matrix. -/
lemma rowcol {b i j : ℕ} (hi : i < b) (hj : j < b) :
    (i * b + j) / b = i ∧ (i * b + j) % b = j ∧ i * b + j < b * b := by
  have hb : 0 < b := by omega
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  · have := Nat.mul_le_mul_right b (show i + 1 ≤ b by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

/-- **`bf2Start` meets the hypotheses of `bfDDG2_exec`.** -/
theorem bf2Start_spec {b : ℕ} {D₁ D₂ : ℕ → ℕ → ℤ} {π : ℕ → ℕ} (hπ : IsPermB b π) :
    Lay2 b (7 * b + 2) (5 * b + 2) (7 * b + 2 + b * b) (6 * b + 2) (5 * b + 2) 0 (bf2W b) ∧
      WordsBounded (bf2W b) (bf2Start b D₁ D₂ π) ∧
      (bf2Start b D₁ D₂ π).nreg 1 = b ∧ (bf2Start b D₁ D₂ π).nreg 2 = 7 * b + 2 ∧
      (bf2Start b D₁ D₂ π).nreg 3 = 5 * b + 2 ∧ (bf2Start b D₁ D₂ π).nreg 4 = 0 ∧
      (bf2Start b D₁ D₂ π).nreg 7 = 7 * b + 2 + b * b ∧
      (bf2Start b D₁ D₂ π).nreg 8 = 6 * b + 2 ∧ (bf2Start b D₁ D₂ π).nreg 9 = 5 * b + 2 ∧
      (∀ i j, i < b → j < b → (bf2Start b D₁ D₂ π).rmem (7 * b + 2 + i * b + j) = D₁ i j) ∧
      (∀ i j, i < b → j < b →
        (bf2Start b D₁ D₂ π).rmem (7 * b + 2 + b * b + i * b + j) = D₂ i j) ∧
      (∀ i < b, (bf2Start b D₁ D₂ π).nmem (5 * b + 2 + i) = π i) := by
  refine ⟨⟨by omega, by omega, by omega, by omega, by unfold bf2W; omega, by omega,
    by unfold bf2W; omega⟩, ⟨fun r => ?_, fun a => ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun i j hi hj => ?_, fun i j hi hj => ?_, fun i hi => ?_⟩
  · simp only [bf2Start, bf2W]; split_ifs <;> omega
  · simp only [bf2Start, bf2W]; split_ifs with h
    · have := hπ.lt (a - (5 * b + 2)) (by omega); omega
    · omega
  · obtain ⟨h1, h2, h3⟩ := rowcol hi hj
    have c1 : 7 * b + 2 ≤ 7 * b + 2 + i * b + j ∧ 7 * b + 2 + i * b + j < 7 * b + 2 + b * b :=
      ⟨by omega, by omega⟩
    simp only [bf2Start, c1, and_self, ↓reduceIte]
    rw [show 7 * b + 2 + i * b + j - (7 * b + 2) = i * b + j by omega, h1, h2]
  · obtain ⟨h1, h2, h3⟩ := rowcol hi hj
    have c1 : ¬ (7 * b + 2 ≤ 7 * b + 2 + b * b + i * b + j ∧
        7 * b + 2 + b * b + i * b + j < 7 * b + 2 + b * b) := by omega
    have c2 : 7 * b + 2 + b * b ≤ 7 * b + 2 + b * b + i * b + j ∧
        7 * b + 2 + b * b + i * b + j < 7 * b + 2 + b * b + b * b := ⟨by omega, by omega⟩
    simp only [bf2Start, c1, c2, and_self, ↓reduceIte]
    rw [show 7 * b + 2 + b * b + i * b + j - (7 * b + 2 + b * b) = i * b + j by omega, h1, h2]
  · have c1 : 5 * b + 2 ≤ 5 * b + 2 + i ∧ 5 * b + 2 + i < 6 * b + 2 := ⟨by omega, by omega⟩
    simp only [bf2Start, c1, and_self, ↓reduceIte]
    congr 1; omega

/-- The cost of `bfDDG2` against `lg b = ⌊log₂ b⌋ + 1`: it fits a cost field
`bf b := 6500 (b + 1)² lg b`. -/
theorem bf2Cost_le_lg (b : ℕ) : bf2Cost b ≤ 6500 * (b + 1) ^ 2 * lg b := bf2Cost_le b

/-! ### The run on two dense distance graphs -/

section Run

variable {V : Type*} [DecidableEq V] {b : ℕ} {β₁ β₂ : ℕ → V} {B : Finset V} {H₁ H₂ : DDG V}

/-- **Bellman–Ford over the union of two complete crossing dense distance graphs, on the
machine.** For two dense distance graphs on `B`, complete between distinct vertices, with
nonnegative loops, whose length matrices are crossing in the enumerations `β₁`, `β₂` of `B`, the
run of `bfDDG2` from `bf2Start` halts within `bf2Cost b` steps; with `E i` the value left at
`5b + 2 + i`, the outcome (`some (E ∘ β₁⁻¹)` when `r30 = 0`, `none` otherwise) is a `PotOut`
output of `H₁.join H₂`. -/
theorem bfDDG2_join_exec (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) (hc₁ : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → (H₁.len u v).isSome)
    (hc₂ : ∀ u ∈ B, ∀ v ∈ B, u ≠ v → (H₂.len u v).isSome)
    (hl₁ : ∀ v ∈ B, 0 ≤ (H₁.len v v).getD 0) (hl₂ : ∀ v ∈ B, 0 ≤ (H₂.len v v).getD 0)
    (hD₁ : Crossing b (matOf H₁ β₁)) (hD₂ : Crossing b (matOf H₂ β₂)) (I : Input) :
    ∃ (c' : Config) (steps : ℕ) (E : ℕ → ℤ),
      Exec I (bf2W b) bfDDG2 (bf2Start b (matOf H₁ β₁) (matOf H₂ β₂) (permOf b β₁ β₂)) c'
        steps ∧ steps ≤ bf2Cost b ∧ (∀ i < b, c'.rmem (5 * b + 2 + i) = E i) ∧
      PotOut (H₁.join H₂)
        (if c'.nreg 30 = 0 then some (fun v => E (enumInv b β₁ v)) else none) := by
  have hπ := isPermB_permOf e₁ e₂
  obtain ⟨hL, hw, h1, h2, h3, h4, h7, h8, h9, hm₁, hm₂, hmπ⟩ :=
    bf2Start_spec (D₁ := matOf H₁ β₁) (D₂ := matOf H₂ β₂) hπ
  obtain ⟨c', k, he, hk, E, hv, hout, -⟩ :=
    bfDDG2_exec (P := I) hπ hD₁ hD₂ hL _ hw h1 h2 h3 h4 h7 h8 h9 hm₁ hm₂ hmπ
  exact ⟨c', k, E, he, hk, hv, potOut_join_of_outcome hB₁ hB₂ e₁ e₂ hc₁ hc₂ hl₁ hl₂ hout⟩

end Run

/-! ### The calls of the recursion -/

section Step

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **The loops of a child dense distance graph are nonnegative**: `H.len v v` is the distance
from `v` to itself in the part with nonnegative reduced lengths, shifted by `δ v - δ v = 0`. -/
theorem childDDG_loop_nonneg {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    (hmssp : PieceMSSPSpec N mssp) {P : Finset D} {ℓ : D → ℤ} {δ : V → ℤ}
    (hnn : ∀ d ∈ P, 0 ≤ redLen N ℓ δ d) {B : Finset V} {v : V} (hv : v ∈ B) :
    0 ≤ ((childDDG N mssp P ℓ δ B).len v v).getD 0 := by
  have hd := hmssp P (redLen N ℓ δ) B hnn v hv
  show 0 ≤ ((mssp P (redLen N ℓ δ) B v v).map (· + (δ v - δ v))).getD 0
  cases h : mssp P (redLen N ℓ δ) B v v with
  | none => simp
  | some x =>
    obtain ⟨l, hl, hlen⟩ := hd.some_walk v x h
    have h0 : (MSSP.pieceGraph N P (redLen N ℓ δ)).IsPot (fun _ => 0) := fun a => by
      show (0 : ℤ) ≤ 0 + redLen N ℓ δ a.1
      have := hnn a.1 a.2; omega
    have := hl.le_wlen h0
    simp only [Option.map_some, Option.getD_some]
    omega

/-- **Every call of `bf` at a node of the recursion whose two child dense distance graphs are
complete is realized by a run of `bfDDG2`.** Under the hypotheses of `crossing_step_parts` (each
part on one face holding the shared vertices `B = bdry N P₀ P₁`, `mssp` meeting
`PieceMSSPSpec`, nonnegative reduced lengths), if every length between vertices of `B` in both
child graphs is defined, then for `b = |B|` and an enumeration `β` of `B` a run of `bfDDG2`
halts within `bf2Cost b ≤ 6500 (b + 1)² lg b` steps, and its outcome (`some`, the value of
`v ∈ B` read at `5b + 2 + β⁻¹ v`, when `r30 = 0`; `none` otherwise) is a `PotOut` output of the
union `H₁.join H₂`, as `BFDDGSpec` requires of the call. -/
theorem step_bf_exec {P₀ P₁ : Finset D} {q₀ q₁ k₀ k₁ : ℕ}
    (h₀ : OneFace N P₀ (bdry N P₀ P₁) q₀ k₀) (h₁ : OneFace N P₁ (bdry N P₀ P₁) q₁ k₁)
    (hB : (bdry N P₀ P₁).Nonempty)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {ℓ : D → ℤ} {δ₀ δ₁ : V → ℤ} (hnn₀ : ∀ d ∈ P₀, 0 ≤ redLen N ℓ δ₀ d)
    (hnn₁ : ∀ d ∈ P₁, 0 ≤ redLen N ℓ δ₁ d)
    (hc₀ : ∀ x ∈ bdry N P₀ P₁, ∀ y ∈ bdry N P₀ P₁,
      ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).len x y).isSome)
    (hc₁ : ∀ x ∈ bdry N P₀ P₁, ∀ y ∈ bdry N P₀ P₁,
      ((childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)).len x y).isSome) (I : Input) :
    ∃ (b : ℕ) (β : ℕ → V) (W : ℕ) (c₀ c' : Config) (steps : ℕ) (E : ℕ → ℤ),
      b = (bdry N P₀ P₁).card ∧ IsEnum b β (bdry N P₀ P₁) ∧
      Exec I W bfDDG2 c₀ c' steps ∧ steps ≤ bf2Cost b ∧
      bf2Cost b ≤ 6500 * (b + 1) ^ 2 * lg b ∧ (∀ i < b, c'.rmem (5 * b + 2 + i) = E i) ∧
      PotOut ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).join
          (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)))
        (if c'.nreg 30 = 0 then some (fun v => E (enumInv b β v)) else none) := by
  obtain ⟨⟨b₀, β₀, m₀, s₀, i₀, -, cr₀⟩, ⟨b₁, β₁, m₁, s₁, i₁, -, cr₁⟩⟩ :=
    crossing_step_parts h₀ h₁ hB hmssp hnn₀ hnn₁
  have e₀ : IsEnum b₀ β₀ (bdry N P₀ P₁) := ⟨m₀, s₀, i₀⟩
  have e₁ : IsEnum b₁ β₁ (bdry N P₀ P₁) := ⟨m₁, s₁, i₁⟩
  have hb : b₁ = b₀ := e₁.card.trans e₀.card.symm
  subst hb
  have hD₀ := cr₀ fun i hi i' hi' => hc₀ _ (m₀ i hi) _ (m₀ i' hi')
  have hD₁ := cr₁ fun i hi i' hi' => hc₁ _ (m₁ i hi) _ (m₁ i' hi')
  obtain ⟨c', k, E, he, hk, hv, hout⟩ := bfDDG2_join_exec (H₁ := childDDG N mssp P₀ ℓ δ₀ _)
    (H₂ := childDDG N mssp P₁ ℓ δ₁ _) rfl rfl e₀ e₁ (fun x hx y hy _ => hc₀ x hx y hy)
    (fun x hx y hy _ => hc₁ x hx y hy) (fun v hv => childDDG_loop_nonneg hmssp hnn₀ hv)
    (fun v hv => childDDG_loop_nonneg hmssp hnn₁ hv) hD₀ hD₁ I
  exact ⟨b₁, β₀, _, _, c', k, E, e₀.card, e₀, he, hk, bf2Cost_le_lg _, hv, hout⟩

end Step

end NegSSSP

end PlanarFlow
