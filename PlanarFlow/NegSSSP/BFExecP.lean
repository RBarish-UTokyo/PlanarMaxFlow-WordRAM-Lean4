module

public import PlanarFlow.Monge.PrepO

/-!
# The Bellman–Ford calls of the recursion from the plain encoding

`PlanarFlow/NegSSSP/BFExecO.lean` realizes the calls of `bf` of the recursion for negative
lengths by a run of `PlanarFlow.Monge.bfDDG2O` started from `bf2StartO`, a configuration holding
the static tables (`tVal`, `tMul`, `finB`) already computed. This file starts the run from the
**plain encoding** of the two matrices with missing arcs: for each matrix the arc flags
`finB X s t` (natural memory) and the lengths `D s t` (real memory) in row-major order, the order
`π`, and the base registers (`bfStartP`). The program `bfFull` first computes both sets of
tables with `PlanarFlow.Monge.prepO` (`PlanarFlow/Monge/PrepO.lean`), then runs `bfDDG2O`.

* `bfFull_exec`: the run of `bfFull` from `bfStartP` halts within `bfCostP b` steps with the
  outcome of `bfDDG2O_exec`.
* `bfCostP_le`: `bfCostP b ≤ 7900 (b + 1)² lg b`.
* `bfFull_join_exec`, `step_bf_execP`: the calls of the recursion, as in `BFExecO.lean`, now
  from the plain encoding of the two `Option`-matrices (`arcOf`, `matOf`).

The memory layout (with `n = b²`): scratch cells of `bfDDG2O` from `0`, the values at `5b + 2`
and `6b + 2` (real memory), `π` at `5b + 2` (natural memory), the flags of the two matrices at
`7b + 2` and `7b + 2 + n`, the scratch rows of `prepO` at `7b + 2 + 2n`, the lengths at
`10b + 2 + 2n` and `10b + 2 + 3n`, the tables at `10b + 2 + 4n` and `10b + 2 + 6n`; the word
bound is `bfWP b = 8n + 14b + 12`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Finset BKMNW

/-- The plain encoding of two matrices with missing arcs and the order `π` (see the module
docstring for the layout). The registers: `r1 = b`, the bases of `bfDDG2O` (`r2`, `r3`, `r4`,
`r7`, `r8`, `r9`), `r10 = 1`, the bases of `prepO` for the first matrix (`r40 … r43`), those of
the second (`r80`, `r81`). -/
noncomputable def bfStartP (b : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (X₂ : ℕ → ℕ → Prop)
    (D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) : Config where
  pc := 0
  nreg := fun r => if r = 1 then b else if r = 2 then 10 * b + 2 + 4 * (b * b)
    else if r = 3 then 5 * b + 2 else if r = 7 then 10 * b + 2 + 6 * (b * b)
    else if r = 8 then 6 * b + 2 else if r = 9 then 5 * b + 2 else if r = 10 then 1
    else if r = 40 then 10 * b + 2 + 4 * (b * b) else if r = 41 then 10 * b + 2 + 2 * (b * b)
    else if r = 42 then 7 * b + 2 else if r = 43 then 7 * b + 2 + 2 * (b * b)
    else if r = 80 then 10 * b + 2 + 3 * (b * b) else if r = 81 then 7 * b + 2 + b * b else 0
  rreg := fun _ => 0
  nmem := fun a => if 5 * b + 2 ≤ a ∧ a < 6 * b + 2 then π (a - (5 * b + 2))
    else if 7 * b + 2 ≤ a ∧ a < 7 * b + 2 + b * b then
      finB X₁ ((a - (7 * b + 2)) / b) ((a - (7 * b + 2)) % b)
    else if 7 * b + 2 + b * b ≤ a ∧ a < 7 * b + 2 + 2 * (b * b) then
      finB X₂ ((a - (7 * b + 2 + b * b)) / b) ((a - (7 * b + 2 + b * b)) % b)
    else 0
  rmem := fun a =>
    if 10 * b + 2 + 2 * (b * b) ≤ a ∧ a < 10 * b + 2 + 3 * (b * b) then
      D₁ ((a - (10 * b + 2 + 2 * (b * b))) / b) ((a - (10 * b + 2 + 2 * (b * b))) % b)
    else if 10 * b + 2 + 3 * (b * b) ≤ a ∧ a < 10 * b + 2 + 4 * (b * b) then
      D₂ ((a - (10 * b + 2 + 3 * (b * b))) / b) ((a - (10 * b + 2 + 3 * (b * b))) % b)
    else 0
  output := []

/-- The word bound of `bfStartP`. -/
def bfWP (b : ℕ) : ℕ := 8 * (b * b) + 14 * b + 12

/-- Between the two passes: the bases of the second matrix into `r40 … r42`. -/
def glueP : Stmt := block [.copyN 40 7, .copyN 41 80, .copyN 42 81]

/-- **Bellman–Ford over two matrices with missing arcs from the plain encoding**: the tables of
the first matrix, of the second, then `bfDDG2O`. -/
def bfFull : Stmt := .seq prepO (.seq glueP (.seq prepO bfDDG2O))

/-- The cost bound of `bfFull`. -/
def bfCostP (b : ℕ) : ℕ := prepCost b + (3 + (prepCost b + bf2CostO b))

variable {b W : ℕ} {P : Input}

/-- The glue block. -/
theorem glueP_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W glueP c c' k ∧ k ≤ 3 ∧
      (c'.nreg 40 = c.nreg 7 ∧ c'.nreg 41 = c.nreg 80 ∧ c'.nreg 42 = c.nreg 81 ∧
        (∀ r, r ≠ 40 → r ≠ 41 → r ≠ 42 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold glueP
  exec_block
  refine ⟨le_refl _, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals simp only [upd_apply]
  all_goals split_ifs <;> omega

/-- A conditional below a bound. -/
lemma ite_le_of {p : Prop} [Decidable p] {x y z : ℕ} (hx : x ≤ z) (hy : y ≤ z) :
    (if p then x else y) ≤ z := by
  split <;> assumption

/-- The decoding of a row-major address. -/
lemma rm_dec {b s t A : ℕ} (hs : s < b) (ht : t < b) :
    (A + s * b + t - A) / b = s ∧ (A + s * b + t - A) % b = t ∧ s * b + t < b * b := by
  rw [show A + s * b + t - A = s * b + t by omega]
  exact rowcol hs ht

section Start

variable {X₁ X₂ : ℕ → ℕ → Prop} {D₁ D₂ : ℕ → ℕ → ℤ} {π : ℕ → ℕ}

/-- **`bfStartP` holds the plain encoding.** -/
theorem bfStartP_spec (hπ : IsPermB b π) :
    WordsBounded (bfWP b) (bfStartP b X₁ D₁ X₂ D₂ π) ∧
      LayP b (10 * b + 2 + 4 * (b * b)) (10 * b + 2 + 2 * (b * b)) (7 * b + 2)
        (7 * b + 2 + 2 * (b * b)) (bfWP b) ∧
      LayP b (10 * b + 2 + 6 * (b * b)) (10 * b + 2 + 3 * (b * b)) (7 * b + 2 + b * b)
        (7 * b + 2 + 2 * (b * b)) (bfWP b) ∧
      Lay2O b (10 * b + 2 + 4 * (b * b)) (5 * b + 2) (10 * b + 2 + 6 * (b * b)) (6 * b + 2)
        (5 * b + 2) 0 (bfWP b) ∧
      InP b (10 * b + 2 + 4 * (b * b)) (10 * b + 2 + 2 * (b * b)) (7 * b + 2)
        (7 * b + 2 + 2 * (b * b)) X₁ D₁ (bfStartP b X₁ D₁ X₂ D₂ π) ∧
      (∀ s t, s < b → t < b →
        (bfStartP b X₁ D₁ X₂ D₂ π).nmem (7 * b + 2 + b * b + s * b + t) = finB X₂ s t) ∧
      (∀ s t, s < b → t < b →
        (bfStartP b X₁ D₁ X₂ D₂ π).rmem (10 * b + 2 + 3 * (b * b) + s * b + t) = D₂ s t) ∧
      (∀ i < b, (bfStartP b X₁ D₁ X₂ D₂ π).nmem (5 * b + 2 + i) = π i) := by
  refine ⟨⟨fun r => ?_, fun a => ?_⟩, ⟨by omega, by omega, by omega, by unfold bfWP; omega⟩,
    ⟨by omega, by omega, by omega, by unfold bfWP; omega⟩,
    ⟨by omega, by omega, by omega, by omega, by unfold bfWP; omega, by omega,
      by unfold bfWP; omega⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun s t hs ht => ?_, fun s t hs ht => ?_⟩,
    fun s t hs ht => ?_, fun s t hs ht => ?_, fun i hi => ?_⟩
  · unfold bfWP; dsimp only [bfStartP]
    repeat' apply ite_le_of
    all_goals omega
  · unfold bfWP; dsimp only [bfStartP]; split_ifs with h1 h2 h3
    · have := hπ.lt (a - (5 * b + 2)) (by omega); omega
    · have := finB_le (X := X₁) ((a - (7 * b + 2)) / b) ((a - (7 * b + 2)) % b); omega
    · have := finB_le (X := X₂) ((a - (7 * b + 2 + b * b)) / b)
        ((a - (7 * b + 2 + b * b)) % b); omega
    · omega
  · obtain ⟨d1, d2, d3⟩ := rm_dec (A := 7 * b + 2) hs ht
    have c0 : ¬ (5 * b + 2 ≤ 7 * b + 2 + s * b + t ∧ 7 * b + 2 + s * b + t < 6 * b + 2) := by
      omega
    have c1 : 7 * b + 2 ≤ 7 * b + 2 + s * b + t ∧ 7 * b + 2 + s * b + t < 7 * b + 2 + b * b :=
      ⟨by omega, by omega⟩
    simp only [bfStartP, c0, c1, and_self, ↓reduceIte]
    rw [d1, d2]
  · obtain ⟨d1, d2, d3⟩ := rm_dec (A := 10 * b + 2 + 2 * (b * b)) hs ht
    have c1 : 10 * b + 2 + 2 * (b * b) ≤ 10 * b + 2 + 2 * (b * b) + s * b + t ∧
        10 * b + 2 + 2 * (b * b) + s * b + t < 10 * b + 2 + 3 * (b * b) := ⟨by omega, by omega⟩
    simp only [bfStartP, c1, and_self, ↓reduceIte]
    rw [d1, d2]
  · obtain ⟨d1, d2, d3⟩ := rm_dec (A := 7 * b + 2 + b * b) hs ht
    have c0 : ¬ (5 * b + 2 ≤ 7 * b + 2 + b * b + s * b + t ∧
        7 * b + 2 + b * b + s * b + t < 6 * b + 2) := by omega
    have c0' : ¬ (7 * b + 2 ≤ 7 * b + 2 + b * b + s * b + t ∧
        7 * b + 2 + b * b + s * b + t < 7 * b + 2 + b * b) := by omega
    have c1 : 7 * b + 2 + b * b ≤ 7 * b + 2 + b * b + s * b + t ∧
        7 * b + 2 + b * b + s * b + t < 7 * b + 2 + 2 * (b * b) := ⟨by omega, by omega⟩
    simp only [bfStartP, c0, c0', c1, and_self, ↓reduceIte]
    rw [d1, d2]
  · obtain ⟨d1, d2, d3⟩ := rm_dec (A := 10 * b + 2 + 3 * (b * b)) hs ht
    have c0 : ¬ (10 * b + 2 + 2 * (b * b) ≤ 10 * b + 2 + 3 * (b * b) + s * b + t ∧
        10 * b + 2 + 3 * (b * b) + s * b + t < 10 * b + 2 + 3 * (b * b)) := by omega
    have c1 : 10 * b + 2 + 3 * (b * b) ≤ 10 * b + 2 + 3 * (b * b) + s * b + t ∧
        10 * b + 2 + 3 * (b * b) + s * b + t < 10 * b + 2 + 4 * (b * b) := ⟨by omega, by omega⟩
    simp only [bfStartP, c0, c1, and_self, ↓reduceIte]
    rw [d1, d2]
  · have hi' : 5 * b + 2 ≤ 5 * b + 2 + i ∧ 5 * b + 2 + i < 6 * b + 2 := ⟨by omega, by omega⟩
    simp only [bfStartP, hi', and_self, ↓reduceIte]
    congr 1; omega

/-- **Bellman–Ford over two crossing matrices with missing arcs, from the plain encoding.** For
two matrices crossing in the extended sense (the second in the order `π`), stored as flags and
lengths (`bfStartP`), the run of `bfFull` halts within `bfCostP b` steps with the outcome of
`bfDDG2O_exec`: the values `E v` at `5b + 2 + v`, and either `r30 = 0` and `E` is a feasible
potential of both matrices (on their arcs), or `r30 = 1` and there is none; if there is one, `E`
is `bfuO b`. -/
theorem bfFull_exec (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁) (hD₂ : CrossingX b X₂ D₂) :
    ∃ c' k, Exec P (bfWP b) bfFull (bfStartP b X₁ D₁ X₂ D₂ π) c' k ∧ k ≤ bfCostP b ∧
      ∃ E : ℕ → ℤ, (∀ v < b, c'.rmem (5 * b + 2 + v) = E v) ∧
        ((c'.nreg 30 = 0 ∧ Feas2O b X₁ D₁ X₂ D₂ π E) ∨
          (c'.nreg 30 = 1 ∧ ¬ ∃ E', Feas2O b X₁ D₁ X₂ D₂ π E')) ∧
        ((∃ E', Feas2O b X₁ D₁ X₂ D₂ π E') → ∀ v < b, E v = bfuO b X₁ D₁ X₂ D₂ π b v) := by
  obtain ⟨hw, hL₁, hL₂, hL, hI, hfl₂, hdv₂, hπm⟩ :=
    bfStartP_spec (X₁ := X₁) (D₁ := D₁) (X₂ := X₂) (D₂ := D₂) hπ
  set c := bfStartP b X₁ D₁ X₂ D₂ π
  unfold bfFull
  refine spec_seq ?_
  refine spec_use (prepO_exec (P := P) hL₁ c hw hI) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hF₁, htab₁⟩
  refine spec_seq ?_
  refine spec_use (glueP_exec (P := P) c₁ hw₁) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨g40, g41, g42, gn, gr, gnm, grm, go⟩
  have e : ∀ r, (r < 40 ∨ (42 < r ∧ r < 44) ∨ 80 ≤ r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [gn r (by omega) (by omega) (by omega), hF₁.nreg r (by omega)]
  have hI₂ : InP b (10 * b + 2 + 6 * (b * b)) (10 * b + 2 + 3 * (b * b)) (7 * b + 2 + b * b)
      (7 * b + 2 + 2 * (b * b)) X₂ D₂ c₂ := by
    refine ⟨by rw [e 1 (by omega)]; rfl, by rw [e 10 (by omega)]; rfl,
      by rw [g40, hF₁.nreg 7 (by omega)]; rfl, by rw [g41, hF₁.nreg 80 (by omega)]; rfl,
      by rw [g42, hF₁.nreg 81 (by omega)]; rfl, by rw [e 43 (by omega)]; rfl,
      fun s t hs ht => ?_, fun s t hs ht => ?_⟩
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [gnm, hF₁.nmem _ (Or.inl (by omega))]; exact hfl₂ s t hs ht
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [grm, hF₁.rmem _ (Or.inl (by omega))]; exact hdv₂ s t hs ht
  have htab₂ := htab₁.of (c' := c₂) (fun a _ _ => by rw [gnm]) (fun a _ _ => by rw [grm])
  refine spec_seq ?_
  refine spec_use (prepO_exec (P := P) hL₂ c₂ hw₂ hI₂) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hF₃, htab₃⟩
  have htab₁' := htab₂.of (c' := c₃) (fun a _ h2 => hF₃.nmem a (Or.inr (Or.inl ⟨by omega,
    by omega⟩))) (fun a _ h2 => hF₃.rmem a (Or.inl (by omega)))
  have f : ∀ r, r < 40 → c₃.nreg r = c.nreg r := fun r hr => by
    rw [hF₃.nreg r (by omega), e r (by omega)]
  refine spec_use (bfDDG2O_exec (P := P) hπ hD₁ hD₂
    (fun s t hs ht _ => lt_Hb (D := D₁) hs ht) (fun s t hs ht _ => lt_Hb (D := D₂) hs ht) hL c₃
    hw₃ (by rw [f 1 (by omega)]; rfl) (by rw [f 2 (by omega)]; rfl)
    (by rw [f 3 (by omega)]; rfl) (by rw [f 4 (by omega)]; rfl) (by rw [f 7 (by omega)]; rfl)
    (by rw [f 8 (by omega)]; rfl) (by rw [f 9 (by omega)]; rfl)
    (fun s t hs ht hst => (htab₁' s t hs ht hst trivial).1)
    (fun s t hs ht hst => (htab₁' s t hs ht hst trivial).2.1)
    (fun s t hs ht hst => (htab₁' s t hs ht hst trivial).2.2)
    (fun s t hs ht hst => (htab₃ s t hs ht hst trivial).1)
    (fun s t hs ht hst => (htab₃ s t hs ht hst trivial).2.1)
    (fun s t hs ht hst => (htab₃ s t hs ht hst trivial).2.2) (fun i hi => ?_)) ?_
  · rw [hF₃.nmem _ (Or.inl (by omega)), gnm, hF₁.nmem _ (Or.inl (by omega))]
    exact hπm i hi
  intro c₄ k₄ hk₄ _ ⟨E, hv, hout, hbfu, _⟩
  refine ⟨?_, E, hv, hout, hbfu⟩
  unfold bfCostP; omega

end Start

/-- The cost of `prepO` against `lg b`: at most `139 (b + 1)² lg b`. -/
theorem prepCost_le (b : ℕ) : prepCost b ≤ 139 * (b + 1) ^ 2 * lg b := by
  unfold prepCost levelCostP
  have hn : (b + 1) ^ 2 = b * b + 2 * b + 1 := by ring
  have hL : 1 ≤ lg b := by unfold lg; omega
  have e1 : (10 * b + 8) * b + 10 + 1 + 2 ≤ 13 * (b + 1) ^ 2 := by
    rw [hn]; ring_nf; omega
  have e2 : (53 * b + 126) * b + 10 + 2 ≤ 126 * (b + 1) ^ 2 := by
    rw [hn]; ring_nf; omega
  have e3 : 13 * (b + 1) ^ 2 ≤ 13 * (b + 1) ^ 2 * lg b := Nat.le_mul_of_pos_right _ hL
  have e4 : ((53 * b + 126) * b + 10 + 2) * (Nat.log 2 b + 1) ≤ 126 * (b + 1) ^ 2 * lg b :=
    Nat.mul_le_mul_right _ e2
  have e5 : 139 * (b + 1) ^ 2 * lg b = 13 * (b + 1) ^ 2 * lg b + 126 * (b + 1) ^ 2 * lg b := by
    ring
  omega

/-- **The cost of `bfFull`**: `bfCostP b ≤ 7900 (b + 1)² lg b`. -/
theorem bfCostP_le (b : ℕ) : bfCostP b ≤ 7900 * (b + 1) ^ 2 * lg b := by
  unfold bfCostP
  have h1 := prepCost_le b
  have h2 := bf2CostO_le_lg b
  have hL : 1 ≤ lg b := by unfold lg; omega
  have h3 : 3 ≤ 3 * ((b + 1) ^ 2 * lg b) := by
    have : 1 ≤ (b + 1) ^ 2 * lg b := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have e : ∀ C, C * (b + 1) ^ 2 * lg b = C * ((b + 1) ^ 2 * lg b) := fun C => by ring
  rw [e] at h1 h2 ⊢
  omega

/-! ### The run on two dense distance graphs with missing arcs -/

section Run

variable {V : Type*} [DecidableEq V] {β₁ β₂ : ℕ → V} {B : Finset V} {H₁ H₂ : DDG V}

/-- **Bellman–Ford over the union of two crossing dense distance graphs with missing arcs, on
the machine, from the plain encoding.** As `bfDDG2O_join_exec`, with the run of `bfFull` from
`bfStartP` (flags `arcOf`, lengths `matOf`) within `bfCostP b` steps. -/
theorem bfFull_join_exec (hB₁ : H₁.bdry = B) (hB₂ : H₂.bdry = B) (e₁ : IsEnum b β₁ B)
    (e₂ : IsEnum b β₂ B) (hl₁ : ∀ v ∈ B, 0 ≤ (H₁.len v v).getD 0)
    (hl₂ : ∀ v ∈ B, 0 ≤ (H₂.len v v).getD 0)
    (hD₁ : CrossingO b (fun i j => H₁.len (β₁ i) (β₁ j)))
    (hD₂ : CrossingO b (fun i j => H₂.len (β₂ i) (β₂ j))) (I : Input) :
    ∃ (c' : Config) (steps : ℕ) (E : ℕ → ℤ),
      Exec I (bfWP b) bfFull (bfStartP b (arcOf H₁ β₁) (matOf H₁ β₁) (arcOf H₂ β₂)
        (matOf H₂ β₂) (permOf b β₁ β₂)) c' steps ∧ steps ≤ bfCostP b ∧
      (∀ i < b, c'.rmem (5 * b + 2 + i) = E i) ∧
      PotOut (H₁.join H₂)
        (if c'.nreg 30 = 0 then some (fun v => E (enumInv b β₁ v)) else none) := by
  have hπ := isPermB_permOf e₁ e₂
  obtain ⟨c', k, he, hk, E, hv, hout, -⟩ :=
    bfFull_exec (P := I) (X₁ := arcOf H₁ β₁) (D₁ := matOf H₁ β₁) (X₂ := arcOf H₂ β₂)
      (D₂ := matOf H₂ β₂) hπ hD₁.crossingX hD₂.crossingX
  exact ⟨c', k, E, he, hk, hv, potOut_join_of_outcomeO hB₁ hB₂ e₁ e₂ hl₁ hl₂ hout⟩

end Run

/-! ### The calls of the recursion -/

section Step

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **Every call of `bf` at a node of the recursion is realized by a run of `bfFull` from the
plain encoding** of the two child dense distance graphs (missing arcs allowed). Under the
hypotheses of `crossing_step_parts`, for `b = |B|` and an enumeration `β` of `B`, the run of
`bfFull` from `bfStartP` (the arc flags and the lengths of the two `Option`-matrices
`(childDDG …).len (β i) (β j)`, in row-major order, and the order of the second enumeration)
halts within `bfCostP b ≤ 7900 (b + 1)² lg b` steps, and its outcome (`some`, the value of
`v ∈ B` read at `5b + 2 + β⁻¹ v`, when `r30 = 0`; `none` otherwise) is a `PotOut` output of the
union `H₁.join H₂`, as `BFDDGSpec` requires of the call. -/
theorem step_bf_execP {P₀ P₁ : Finset D} {q₀ q₁ k₀ k₁ : ℕ}
    (h₀ : OneFace N P₀ (bdry N P₀ P₁) q₀ k₀) (h₁ : OneFace N P₁ (bdry N P₀ P₁) q₁ k₁)
    (hB : (bdry N P₀ P₁).Nonempty)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {ℓ : D → ℤ} {δ₀ δ₁ : V → ℤ} (hnn₀ : ∀ d ∈ P₀, 0 ≤ redLen N ℓ δ₀ d)
    (hnn₁ : ∀ d ∈ P₁, 0 ≤ redLen N ℓ δ₁ d) (I : Input) :
    ∃ (b : ℕ) (β₀ β₁ : ℕ → V) (c' : Config) (steps : ℕ) (E : ℕ → ℤ),
      b = (bdry N P₀ P₁).card ∧ IsEnum b β₀ (bdry N P₀ P₁) ∧ IsEnum b β₁ (bdry N P₀ P₁) ∧
      Exec I (bfWP b) bfFull
        (bfStartP b (arcOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) β₀)
          (matOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) β₀)
          (arcOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) β₁)
          (matOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) β₁) (permOf b β₀ β₁)) c' steps ∧
      steps ≤ bfCostP b ∧ bfCostP b ≤ 7900 * (b + 1) ^ 2 * lg b ∧
      (∀ i < b, c'.rmem (5 * b + 2 + i) = E i) ∧
      PotOut ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).join
          (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)))
        (if c'.nreg 30 = 0 then some (fun v => E (enumInv b β₀ v)) else none) := by
  obtain ⟨⟨b₀, β₀, m₀, s₀, i₀, cr₀, -⟩, ⟨b₁, β₁, m₁, s₁, i₁, cr₁, -⟩⟩ :=
    crossing_step_parts h₀ h₁ hB hmssp hnn₀ hnn₁
  have e₀ : IsEnum b₀ β₀ (bdry N P₀ P₁) := ⟨m₀, s₀, i₀⟩
  have e₁ : IsEnum b₁ β₁ (bdry N P₀ P₁) := ⟨m₁, s₁, i₁⟩
  have hb : b₁ = b₀ := e₁.card.trans e₀.card.symm
  subst hb
  obtain ⟨c', k, E, he, hk, hv, hout⟩ := bfFull_join_exec (H₁ := childDDG N mssp P₀ ℓ δ₀ _)
    (H₂ := childDDG N mssp P₁ ℓ δ₁ _) rfl rfl e₀ e₁
    (fun v hv => childDDG_loop_nonneg hmssp hnn₀ hv)
    (fun v hv => childDDG_loop_nonneg hmssp hnn₁ hv) cr₀ cr₁ I
  exact ⟨b₁, β₀, β₁, c', k, E, e₀.card, e₀, e₁, he, hk, bfCostP_le _, hv, hout⟩

end Step

end NegSSSP

end PlanarFlow
