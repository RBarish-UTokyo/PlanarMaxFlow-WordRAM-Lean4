module

public import PlanarFlow.Monge.DDGBF2Round

/-!
# Bellman–Ford over the union of two dense distance graphs on the machine

The input is two dense distance graphs on the same `b` vertices `0, …, b - 1`, each complete and
satisfying the crossing inequality (`PlanarFlow.Monge.Crossing`) **in its own order** of the
vertices:

* matrix 1: the lengths `D₁ i j` of the arcs `i → j`, stored in the real memory at
  `Db₁ + i b + j`, crossing in the natural order;
* matrix 2: a permutation `π` of `0, …, b - 1` (`IsPermB`), stored in the natural memory at
  `πb + i`, and the lengths `D₂ i j` of the arcs `π i → π j`, stored at `Db₂ + i b + j`;
  `D₂` is crossing (in the order `π 0, π 1, …` of the vertices).

The union is the digraph `ddg2 b D₁ D₂ π` on `Fin b` (both kinds of arcs, `i ≠ j`); `bfu k` are
its Bellman–Ford values after `k` rounds from `0` (a virtual source joined to every vertex).
`Feas2 b D₁ D₂ π E` says that `E` is a feasible potential of both matrices, i.e. of the union
(`hasPot2_iff`).

## The program

`bfDDG2` keeps the values `e v` at `eb + v` (real memory), sets them to `0` and runs `b + 1`
rounds `round2`. A round of the union is:

1. the levels of a round of `bfDDG` for matrix 1 on the values at `eb` (the program
   `whileLtN 20 1 levelBF` of `PlanarFlow/Monge/DDGBF.lean`, unchanged, with `r2 = Db₁`,
   `r3 = eb`);
2. the copy `e₂[i] := e[π i]` to the second value array at `eb₂` (`cpToBody`);
3. the levels of a round for matrix 2 on `e₂` (the same program with `r2 = Db₂`, `r3 = eb₂`);
4. the copy back `e[π i] := e₂[i]` (`cpBackBody`);
5. the flag `r30 := max (flag of 1) (flag of 3)`.

This design reuses the verified one-matrix level loop verbatim: matrix 2 is Monge in the order
of the copied array, so its blocks are exactly those of `bfDDG`. Each phase resets the flag, so
that each phase's invariant (`PlanarFlow.Monge.RoundG`) is relative to the values at its own
start, and the flags are merged at the end (`round2_math`). The invariants of the phases are
stated against the reference values of the union (`lo = bfu b`, `hi = bfu k`, composed with `π`
for matrix 2); this is the generalized round invariant of `PlanarFlow/Monge/DDGBF2Round.lean`.

**`PlanarFlow.Monge.bfDDG2_exec`.** The program halts within `bf2Cost b` steps
(`bf2Cost_le`: at most `6500 (b + 1)² (log₂ b + 1)`), and ends either with the flag `r30 = 0`
and values forming a feasible potential of both matrices, or with `r30 = 1` and no feasible
potential of both matrices exists; if one exists, the values are the Bellman–Ford values
`bfu b` of the union.

Memory: the row-minima scratch cells at `pb + 1 … pb + 5b + 1` (natural and real), the values
at `eb … eb + b - 1`, the second values at `eb₂ … eb₂ + b - 1`, the lengths at `Db₁` and `Db₂`
(real), the permutation at `πb … πb + b - 1` (natural), with the layout `Lay2`.
Registers: inputs `r1 = b`, `r2 = Db₁`, `r3 = eb`, `r4 = pb`, `r7 = Db₂`, `r8 = eb₂`,
`r9 = πb`; `r5 = Db₁` and `r6 = eb` are saved copies (`r2, r3` alternate between the two
matrices); `r10 = 1` and the real `r10 = 0`; `r12, r13` (initialization), `r14` the round,
`r15 = b + 1`, `r16 … r18` and the real `r16` (copies), `r20 … r30` (levels, as in `bfDDG`),
`r31` the flag of the first phase; `r60 …` belong to `smawk` and `r80 …` to the oracle.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### Permutations of `0, …, b - 1` -/

/-- `π` permutes `0, …, b - 1`. -/
structure IsPermB (b : ℕ) (π : ℕ → ℕ) : Prop where
  lt : ∀ i < b, π i < b
  inj : ∀ i j, i < b → j < b → π i = π j → i = j

variable {b : ℕ} {π : ℕ → ℕ}

/-- A permutation of `0, …, b - 1` is onto. -/
theorem IsPermB.surj (h : IsPermB b π) {v : ℕ} (hv : v < b) : ∃ i < b, π i = v := by
  have hsub : (Finset.range b).image π ⊆ Finset.range b := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    exact h.lt i hi
  have hcard : (Finset.range b).card ≤ ((Finset.range b).image π).card := by
    rw [Finset.card_image_of_injOn (fun i hi j hj e =>
      h.inj i j (by simpa using hi) (by simpa using hj) e)]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hmem : v ∈ (Finset.range b).image π := by rw [heq]; simpa using hv
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  exact hmem

/-- Values given on the positions `0, …, b - 1` are the values of some function at
`π 0, …, π (b - 1)`. -/
theorem IsPermB.exists_inv (h : IsPermB b π) (F : ℕ → ℤ) : ∃ G : ℕ → ℤ, ∀ i < b, G (π i) = F i := by
  classical
  refine ⟨fun v => if hv : ∃ i, i < b ∧ π i = v then F (Classical.choose hv) else 0,
    fun i hi => ?_⟩
  have hv : ∃ j, j < b ∧ π j = π i := ⟨i, hi, rfl⟩
  simp only
  rw [dite_eq_left_of_eq_true (eq_true hv)]
  have hs := Classical.choose_spec (of_eq_true (eq_true hv))
  rw [h.inj _ _ hs.1 hi hs.2]

/-! ### The union digraph -/

/-- `π` on `Fin b` (reduced modulo `b`; it is `π` itself for a permutation, `pfin_val`). -/
def pfin (b : ℕ) (π : ℕ → ℕ) (i : Fin b) : Fin b :=
  ⟨π i % b, Nat.mod_lt _ ((Nat.zero_le _).trans_lt i.2)⟩

/-- For a permutation, `pfin` is `π`. -/
lemma pfin_val (hπ : IsPermB b π) (i : Fin b) : (pfin b π i : ℕ) = π i :=
  Nat.mod_eq_of_lt (hπ.lt i i.2)

/-- **The union of the two dense distance graphs**: the arcs `i → j` of length `D₁ i j` and the
arcs `π i → π j` of length `D₂ i j`, for `i ≠ j`. -/
def ddg2 (b : ℕ) (D₁ D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) : Digraph (Fin b) (Arc b ⊕ Arc b) where
  src := Sum.elim (fun a => a.1.1) fun a => pfin b π a.1.1
  dst := Sum.elim (fun a => a.1.2) fun a => pfin b π a.1.2
  len := Sum.elim (fun a => D₁ a.1.1 a.1.2) fun a => D₂ a.1.1 a.1.2

/-- A function on `Fin b`, extended by `0` to `ℕ`. -/
def liftF (b : ℕ) (p : Fin b → ℤ) (v : ℕ) : ℤ := if h : v < b then p ⟨v, h⟩ else 0

/-- The extension below `b`. -/
lemma liftF_of_lt {p : Fin b → ℤ} {v : ℕ} (h : v < b) : liftF b p v = p ⟨v, h⟩ := by
  simp [liftF, h]

/-- The Bellman–Ford values of the union, indexed by `ℕ` (`0` outside). -/
def bfu (b : ℕ) (D₁ D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) (k : ℕ) : ℕ → ℤ :=
  liftF b ((ddg2 b D₁ D₂ π).bf k)

/-- The union has a feasible potential. -/
def HasPot2 (b : ℕ) (D₁ D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) : Prop := ∃ p, (ddg2 b D₁ D₂ π).IsPot p

/-- `E` is a feasible potential of both matrices: `E j ≤ E i + D₁ i j` and
`E (π j) ≤ E (π i) + D₂ i j` for all `i ≠ j` below `b`. -/
def Feas2 (b : ℕ) (D₁ D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) (E : ℕ → ℤ) : Prop :=
  ∀ i j, i < b → j < b → i ≠ j → E j ≤ E i + D₁ i j ∧ E (π j) ≤ E (π i) + D₂ i j

variable {D₁ D₂ : ℕ → ℕ → ℤ}

/-- A feasible potential of both matrices is a feasible potential of the union. -/
theorem isPot_of_feas2 (hπ : IsPermB b π) {E : ℕ → ℤ} (h : Feas2 b D₁ D₂ π E) :
    (ddg2 b D₁ D₂ π).IsPot (fun v => E v) := by
  intro a
  rcases a with a | a
  · exact (h a.1.1 a.1.2 a.1.1.2 a.1.2.2 (fun e => a.2 (Fin.ext e))).1
  · show E (pfin b π a.1.2) ≤ E (pfin b π a.1.1) + D₂ a.1.1 a.1.2
    rw [pfin_val hπ, pfin_val hπ]
    exact (h a.1.1 a.1.2 a.1.1.2 a.1.2.2 (fun e => a.2 (Fin.ext e))).2

/-- A feasible potential of the union is a feasible potential of both matrices. -/
theorem feas2_of_isPot (hπ : IsPermB b π) {p : Fin b → ℤ} (hp : (ddg2 b D₁ D₂ π).IsPot p) :
    Feas2 b D₁ D₂ π (liftF b p) := by
  intro i j hi hj hij
  have hne : (⟨i, hi⟩ : Fin b) ≠ ⟨j, hj⟩ := fun e => hij (congrArg Fin.val e)
  refine ⟨?_, ?_⟩
  · have := hp (.inl ⟨(⟨i, hi⟩, ⟨j, hj⟩), hne⟩)
    rw [liftF_of_lt hi, liftF_of_lt hj]
    exact this
  · have := hp (.inr ⟨(⟨i, hi⟩, ⟨j, hj⟩), hne⟩)
    change p (pfin b π ⟨j, hj⟩) ≤ p (pfin b π ⟨i, hi⟩) + D₂ i j at this
    rw [liftF_of_lt (hπ.lt i hi), liftF_of_lt (hπ.lt j hj)]
    rwa [show pfin b π ⟨j, hj⟩ = ⟨π j, hπ.lt j hj⟩ from Fin.ext (pfin_val hπ _),
      show pfin b π ⟨i, hi⟩ = ⟨π i, hπ.lt i hi⟩ from Fin.ext (pfin_val hπ _)] at this

/-- **The union has a feasible potential iff both matrices have a common feasible potential.** -/
theorem hasPot2_iff (hπ : IsPermB b π) : HasPot2 b D₁ D₂ π ↔ ∃ E, Feas2 b D₁ D₂ π E :=
  ⟨fun ⟨_, hp⟩ => ⟨_, feas2_of_isPot hπ hp⟩, fun ⟨_, hE⟩ => ⟨_, isPot_of_feas2 hπ hE⟩⟩

/-- With a feasible potential, `bfu b` is one (`PlanarFlow.Digraph.isPot_bf_card`). -/
theorem bfu_feas (hπ : IsPermB b π) (hP : HasPot2 b D₁ D₂ π) :
    Feas2 b D₁ D₂ π (bfu b D₁ D₂ π b) := by
  obtain ⟨p, hp⟩ := hP
  have := (ddg2 b D₁ D₂ π).isPot_bf_card hp
  rw [Fintype.card_fin] at this
  exact feas2_of_isPot hπ this

/-- No round: the values `0`. -/
lemma bfu_zero (v : ℕ) : bfu b D₁ D₂ π 0 v = 0 := by
  unfold bfu liftF; split_ifs <;> rfl

/-- With a feasible potential, `bfu b` is below every `bfu k`. -/
theorem bfu_card_le (hP : HasPot2 b D₁ D₂ π) (k : ℕ) {v : ℕ} (hv : v < b) :
    bfu b D₁ D₂ π b v ≤ bfu b D₁ D₂ π k v := by
  obtain ⟨p, hp⟩ := hP
  have := (ddg2 b D₁ D₂ π).bf_card_le k hp ⟨v, hv⟩
  rw [Fintype.card_fin] at this
  unfold bfu
  rw [liftF_of_lt hv, liftF_of_lt hv]
  exact this

/-- With a feasible potential, the values do not change after `b` rounds. -/
theorem bfu_succ_card (hP : HasPot2 b D₁ D₂ π) {v : ℕ} (hv : v < b) :
    bfu b D₁ D₂ π (b + 1) v = bfu b D₁ D₂ π b v := by
  obtain ⟨p, hp⟩ := hP
  have := (ddg2 b D₁ D₂ π).bf_succ_card hp ⟨v, hv⟩
  rw [Fintype.card_fin] at this
  unfold bfu
  rw [liftF_of_lt hv, liftF_of_lt hv]
  exact this

/-- **The end of a round of the union**: values below `bfu k` satisfying every arc inequality of
both matrices against `bfu k` are below `bfu (k + 1)`
(`PlanarFlow.Digraph.le_bf_succ_of_round`). -/
theorem bfu_le_succ (hπ : IsPermB b π) {k : ℕ} {E : ℕ → ℤ}
    (h1 : ∀ v < b, E v ≤ bfu b D₁ D₂ π k v)
    (h2 : ∀ i j, i < b → j < b → i ≠ j → E j ≤ bfu b D₁ D₂ π k i + D₁ i j)
    (h3 : ∀ i j, i < b → j < b → i ≠ j → E (π j) ≤ bfu b D₁ D₂ π k (π i) + D₂ i j)
    {v : ℕ} (hv : v < b) : E v ≤ bfu b D₁ D₂ π (k + 1) v := by
  rw [bfu, liftF_of_lt hv]
  refine (ddg2 b D₁ D₂ π).le_bf_succ_of_round (E := fun w => E w) (fun w => ?_) (fun a => ?_)
    ⟨v, hv⟩
  · have := h1 w w.2; rwa [bfu, liftF_of_lt w.2] at this
  · rcases a with a | a
    · have := h2 a.1.1 a.1.2 a.1.1.2 a.1.2.2 (fun e => a.2 (Fin.ext e))
      rw [bfu, liftF_of_lt a.1.1.2] at this
      exact this
    · have := h3 a.1.1 a.1.2 a.1.1.2 a.1.2.2 (fun e => a.2 (Fin.ext e))
      show E (pfin b π a.1.2) ≤ (ddg2 b D₁ D₂ π).bf k (pfin b π a.1.1) + D₂ a.1.1 a.1.2
      rw [pfin_val hπ, show pfin b π a.1.1 = ⟨π a.1.1, hπ.lt _ a.1.1.2⟩ from
        Fin.ext (pfin_val hπ _)]
      rw [bfu, liftF_of_lt (hπ.lt _ a.1.1.2)] at this
      exact this

/-! ### One round of the union -/

/-- **One round of the union, mathematically.** Phase 1 relaxes every arc of `D₁` from the
values `E₀` to `E₁` (`RoundG` against `bfu b`, `bfu k`), phase 2 every arc of `D₂` from the
copied values `E₁ ∘ π` to `E₂` (against `bfu b ∘ π`, `bfu k ∘ π`), the values `E'` are copied
back (`E' (π i) = E₂ i`) and `F` is the larger flag. Then the new values lie between `bfu b`
and `bfu (k + 1)` (under a feasible potential); if `F = 0` they are a feasible potential of
both matrices; if `F = 1`, `bfu b < bfu k` somewhere (under a feasible potential). -/
theorem round2_math (hπ : IsPermB b π) {k : ℕ} {E₀ E₁ E₂ E' : ℕ → ℤ} {f₁ f₂ F : ℕ}
    (hR₁ : RoundG b D₁ (HasPot2 b D₁ D₂ π) (bfu b D₁ D₂ π b) (bfu b D₁ D₂ π k)
      (fun _ _ => True) E₀ E₁ f₁)
    (hR₂ : RoundG b D₂ (HasPot2 b D₁ D₂ π) (fun v => bfu b D₁ D₂ π b (π v))
      (fun v => bfu b D₁ D₂ π k (π v)) (fun _ _ => True) (fun v => E₁ (π v)) E₂ f₂)
    (hE' : ∀ i < b, E' (π i) = E₂ i) (hF : (F = f₁ ∧ f₂ < f₁) ∨ (F = f₂ ∧ ¬ f₂ < f₁)) :
    F ≤ 1 ∧
      (HasPot2 b D₁ D₂ π → ∀ v < b, bfu b D₁ D₂ π b v ≤ E' v ∧ E' v ≤ bfu b D₁ D₂ π (k + 1) v) ∧
      (F = 0 → Feas2 b D₁ D₂ π E') ∧
      (F = 1 → HasPot2 b D₁ D₂ π → ∃ v < b, bfu b D₁ D₂ π b v < bfu b D₁ D₂ π k v) := by
  have f1 := hR₁.flag_le
  have f2 := hR₂.flag_le
  have hle' : ∀ v < b, E' v ≤ E₁ v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := hπ.surj hv
    rw [hE' i hi]; exact hR₂.le i hi
  refine ⟨by omega, fun hP v hv => ?_, fun h0 => ?_, fun h1 hP => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := hπ.surj hv
    refine ⟨by rw [hE' i hi]; exact ((hR₂.bf hP).1 i hi).1, bfu_le_succ hπ (fun w hw => ?_)
      (fun i j hi hj hij => ?_) (fun i j hi hj hij => ?_) (hπ.lt i hi)⟩
    · exact (hle' w hw).trans ((hR₁.le w hw).trans ((hR₁.bf hP).1 w hw).2)
    · exact (hle' j hj).trans ((hR₁.bf hP).2 i j hi hj hij trivial)
    · rw [hE' j hj]; exact (hR₂.bf hP).2 i j hi hj hij trivial
  · have h10 : f₁ = 0 := by omega
    have h20 : f₂ = 0 := by omega
    have hEq : ∀ v < b, E' v = E₁ v := by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := hπ.surj hv
      rw [hE' i hi]
      rcases hR₂.chg with ⟨-, h⟩ | ⟨h, -⟩
      · exact h i hi
      · omega
    intro i j hi hj hij
    refine ⟨?_, ?_⟩
    · rw [hEq i hi, hEq j hj]; exact hR₁.feas h10 i j hi hj hij trivial
    · rw [hE' i hi, hE' j hj]; exact hR₂.feas h20 i j hi hj hij trivial
  · by_cases h11 : f₁ = 1
    · rcases hR₁.chg with ⟨h, -⟩ | ⟨-, v, hv, hlt⟩
      · omega
      · refine ⟨v, hv, ?_⟩
        have := ((hR₁.bf hP).1 v hv).1
        have := ((hR₁.bf hP).1 v hv).2
        omega
    · have h21 : f₂ = 1 := by omega
      rcases hR₂.chg with ⟨h, -⟩ | ⟨-, i, hi, hlt⟩
      · omega
      · refine ⟨π i, hπ.lt i hi, ?_⟩
        have := ((hR₂.bf hP).1 i hi).1
        have := hR₁.le (π i) (hπ.lt i hi)
        have := ((hR₁.bf hP).1 (π i) (hπ.lt i hi)).2
        omega

/-! ### The program -/

/-- One step of the copy `e₂[i] := e[π i]` (`i = r16`). -/
def cpToBody : Stmt := block [.addN 17 9 16, .loadN 17 17, .addN 17 6 17, .loadR 16 17,
  .addN 18 8 16, .storeR 18 16, .addN 16 16 10]

/-- One step of the copy back `e[π i] := e₂[i]` (`i = r16`). -/
def cpBackBody : Stmt := block [.addN 17 9 16, .loadN 17 17, .addN 17 6 17, .addN 18 8 16,
  .loadR 16 18, .storeR 17 16, .addN 16 16 10]

/-- **A round of the union**: the levels of matrix 1 on `e`, the copy to `e₂`, the levels of
matrix 2 on `e₂`, the copy back, the larger flag of the two phases. -/
def round2 : Stmt :=
  .seq (block [.constN 30 0, .copyN 2 5, .copyN 3 6, .constN 20 1]) <|
  .seq (.whileLtN 20 1 levelBF) <|
  .seq (block [.copyN 31 30, .constN 30 0, .constN 16 0]) <|
  .seq (.whileLtN 16 1 cpToBody) <|
  .seq (block [.copyN 2 7, .copyN 3 8, .constN 20 1]) <|
  .seq (.whileLtN 20 1 levelBF) <|
  .seq (.instr (.constN 16 0)) <|
  .seq (.whileLtN 16 1 cpBackBody) <|
  .seq (.ifLtN 30 31 (.instr (.copyN 30 31)) .skip) <|
  .instr (.addN 14 14 10)

/-- **Bellman–Ford over the union of two dense distance graphs.** -/
def bfDDG2 : Stmt :=
  .seq (block [.constN 10 1, .constR 10 0, .constN 12 0, .addN 15 1 10, .constN 14 0,
    .constN 30 0, .copyN 5 2, .copyN 6 3]) <|
  .seq (.whileLtN 12 1 initBody) (.whileLtN 14 15 round2)

/-! ### The fixed data -/

/-- The layout of the memory and the word bound. -/
structure Lay2 (b Db₁ eb Db₂ eb₂ πb pb W : ℕ) : Prop where
  pe : pb + 5 * b + 1 < eb
  ee : eb + b ≤ eb₂
  ed : eb₂ + b ≤ Db₁
  dd : Db₁ + b * b ≤ Db₂
  w : Db₂ + b * b + 4 * b + 10 ≤ W
  pp : pb + 5 * b + 1 < πb
  pw : πb + b ≤ W

/-- The layout of matrix 1 for the one-matrix level loop. -/
theorem Lay2.lay₁ {Db₁ eb Db₂ eb₂ πb pb W : ℕ} (h : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) :
    Lay b Db₁ eb pb W :=
  ⟨h.pe, by have := h.ee; have := h.ed; omega, by have := h.dd; have := h.w; omega⟩

/-- The layout of matrix 2 for the one-matrix level loop. -/
theorem Lay2.lay₂ {Db₁ eb Db₂ eb₂ πb pb W : ℕ} (h : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) :
    Lay b Db₂ eb₂ pb W :=
  ⟨by have := h.pe; have := h.ee; omega, by have := h.ed; have := h.dd; omega, h.w⟩

/-- The fixed registers and the stored input. -/
structure Env2 (b Db₁ eb Db₂ eb₂ πb pb : ℕ) (D₁ D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) (c : Config) :
    Prop where
  r1 : c.nreg 1 = b
  r4 : c.nreg 4 = pb
  r5 : c.nreg 5 = Db₁
  r6 : c.nreg 6 = eb
  r7 : c.nreg 7 = Db₂
  r8 : c.nreg 8 = eb₂
  r9 : c.nreg 9 = πb
  r10 : c.nreg 10 = 1
  r15 : c.nreg 15 = b + 1
  z10 : c.rreg 10 = 0
  d₁ : ∀ i j, i < b → j < b → c.rmem (Db₁ + i * b + j) = D₁ i j
  d₂ : ∀ i j, i < b → j < b → c.rmem (Db₂ + i * b + j) = D₂ i j
  perm : ∀ i < b, c.nmem (πb + i) = π i

variable {P : Input} {W Db₁ eb Db₂ eb₂ πb pb : ℕ}

/-- The fixed data survive a step with the given frame. -/
theorem Env2.of (hL : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) {c c' : Config}
    (h : Env2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π c)
    (hn : ∀ r, r < 16 → r ≠ 2 → r ≠ 3 → r ≠ 12 → r ≠ 13 → r ≠ 14 → c'.nreg r = c.nreg r)
    (hr : c'.rreg 10 = c.rreg 10) (hm : ∀ a, Db₁ ≤ a → c'.rmem a = c.rmem a)
    (hnm : ∀ a, πb ≤ a → c'.nmem a = c.nmem a) : Env2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π c' := by
  have hdd := hL.dd
  exact ⟨(hn 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r1,
    (hn 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r4,
    (hn 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r5,
    (hn 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r6,
    (hn 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r7,
    (hn 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r8,
    (hn 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r9,
    (hn 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r10,
    (hn 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r15,
    hr.trans h.z10, fun i j hi hj => (hm _ (by omega)).trans (h.d₁ i j hi hj),
    fun i j hi hj => (hm _ (by omega)).trans (h.d₂ i j hi hj),
    fun i hi => (hnm _ (by omega)).trans (h.perm i hi)⟩

/-- The data of matrix 1, when `r2 = Db₁` and `r3 = eb`. -/
theorem Env2.env₁ {c : Config} (h : Env2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π c) (h2 : c.nreg 2 = Db₁)
    (h3 : c.nreg 3 = eb) : Env b Db₁ eb pb D₁ c :=
  ⟨h.r1, h2, h3, h.r4, h.r10, h.z10, h.d₁⟩

/-- The data of matrix 2, when `r2 = Db₂` and `r3 = eb₂`. -/
theorem Env2.env₂ {c : Config} (h : Env2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π c) (h2 : c.nreg 2 = Db₂)
    (h3 : c.nreg 3 = eb₂) : Env b Db₂ eb₂ pb D₂ c :=
  ⟨h.r1, h2, h3, h.r4, h.r10, h.z10, h.d₂⟩

/-- The data kept during a round: the fixed data, the round counter `k`, the output. -/
structure Keep (b Db₁ eb Db₂ eb₂ πb pb : ℕ) (D₁ D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) (k : ℕ)
    (c₀ c : Config) : Prop where
  env : Env2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π c
  r14 : c.nreg 14 = k
  out : c.output = c₀.output

/-- The kept data survive a step with the given frame. -/
theorem Keep.of (hL : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) {k : ℕ} {c₀ c c' : Config}
    (h : Keep b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π k c₀ c)
    (hn : ∀ r, r < 16 → r ≠ 2 → r ≠ 3 → c'.nreg r = c.nreg r)
    (hr : c'.rreg 10 = c.rreg 10) (hm : ∀ a, Db₁ ≤ a → c'.rmem a = c.rmem a)
    (hnm : ∀ a, πb ≤ a → c'.nmem a = c.nmem a) (ho : c'.output = c.output) :
    Keep b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π k c₀ c' :=
  ⟨h.env.of hL (fun r hr h2 h3 _ _ _ => hn r hr h2 h3) hr hm hnm,
    (hn 14 (by omega) (by omega) (by omega)).trans h.r14, ho.trans h.out⟩

/-- The levels of a phase keep the data. -/
theorem Keep.ofFrm (hL : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) {k e : ℕ} {c₀ c c' : Config}
    (he : e + b ≤ Db₁) (h : Keep b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π k c₀ c) (hF : Frm b e pb c c') :
    Keep b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π k c₀ c' := by
  have := hL.pp
  exact h.of hL (fun r hr _ _ => hF.nreg r (by omega) (by omega))
    (hF.rreg 10 (by omega) (by omega) (by omega)) (fun a ha => hF.rmem a (Or.inr (by omega)))
    (fun a ha => hF.nmem a (by omega)) hF.out

/-! ### The copies -/

/-- The state of the copy `e₂[i] := e[π i]` of the values `E`, started from `c₀`. -/
structure ICpTo (b eb₂ : ℕ) (π : ℕ → ℕ) (W : ℕ) (E : ℕ → ℤ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  nreg : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → c.nreg r = c₀.nreg r
  rreg : ∀ r, r ≠ 16 → c.rreg r = c₀.rreg r
  nmem : c.nmem = c₀.nmem
  rmem : ∀ a, (a < eb₂ ∨ eb₂ + b ≤ a) → c.rmem a = c₀.rmem a
  out : c.output = c₀.output
  le : c.nreg 16 ≤ b
  cp : ∀ i < c.nreg 16, c.rmem (eb₂ + i) = E (π i)

/-- One step of the copy to `e₂`. -/
theorem cpToBody_exec (hπ : IsPermB b π) (hL : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) {E : ℕ → ℤ}
    {c₀ : Config} (hE : Env2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π c₀) (hV : Vals b eb E c₀)
    (c : Config) (hI : ICpTo b eb₂ π W E c₀ c) (hlt : c.nreg 16 < c.nreg 1) :
    ∃ c' k', Exec P W cpToBody c c' k' ∧ ICpTo b eb₂ π W E c₀ c' ∧
      9 * (b - c'.nreg 16) + k' + 2 ≤ 9 * (b - c.nreg 16) := by
  have hc := hI.wb
  have hpe := hL.pe
  have hee := hL.ee
  have hed := hL.ed
  have hdd := hL.dd
  have hw := hL.w
  have hpw := hL.pw
  have g : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → c.nreg r = c₀.nreg r := hI.nreg
  have g1 : c.nreg 1 = b := (g 1 (by omega) (by omega) (by omega)).trans hE.r1
  have g6 : c.nreg 6 = eb := (g 6 (by omega) (by omega) (by omega)).trans hE.r6
  have g8 : c.nreg 8 = eb₂ := (g 8 (by omega) (by omega) (by omega)).trans hE.r8
  have g9 : c.nreg 9 = πb := (g 9 (by omega) (by omega) (by omega)).trans hE.r9
  have g10 : c.nreg 10 = 1 := (g 10 (by omega) (by omega) (by omega)).trans hE.r10
  rw [g1] at hlt
  have hle := hI.le
  generalize hm : c.nreg 16 = m at hlt hle
  have hpm : c.nmem (πb + m) = π m := by rw [hI.nmem]; exact hE.perm m hlt
  have hpl := hπ.lt m hlt
  have hrd : c.rmem (eb + π m) = E (π m) := by
    rw [hI.rmem _ (Or.inl (by omega))]; exact hV _ hpl
  unfold cpToBody
  exec_block
  · rw [g9, hm]; omega
  · config_simp; rw [g6, g9, hm, hpm]; omega
  · config_simp; rw [g8, hm]; omega
  · config_simp; rw [hm, g10]; omega
  refine ⟨⟨‹_›, fun r h1 h2 h3 => ?_, fun r h1 => ?_, rfl.trans hI.nmem, fun a ha => ?_,
    hI.out, ?_, fun i hi => ?_⟩, ?_⟩
  · config_simp; rw [← g r h1 h2 h3]; upd_tac
  · config_simp; rw [← hI.rreg r h1]; upd_tac
  · config_simp; rw [upd_apply, g8, hm]
    split_ifs with h
    · omega
    · exact hI.rmem a ha
  · config_simp; rw [hm, g10]; omega
  · config_simp at hi; rw [hm, g10] at hi
    config_simp; rw [upd_apply, g8, hm, g6, g9, hpm, hrd]
    split_ifs with h
    · rw [show i = m by omega]
    · exact hI.cp i (by omega)
  · config_simp; rw [hm, g10]; omega

/-- **The copy `e₂[i] := e[π i]`** of the values `E` at `eb` to `eb₂`, within `9 b + 2` steps. -/
theorem cpTo_exec (hπ : IsPermB b π) (hL : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) {E : ℕ → ℤ}
    (c : Config) (hc : WordsBounded W c) (hE : Env2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π c)
    (hV : Vals b eb E c) (h16 : c.nreg 16 = 0) :
    ∃ c' k, Exec P W (.whileLtN 16 1 cpToBody) c c' k ∧ k ≤ 9 * b + 2 ∧
      ((∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 16 → c'.rreg r = c.rreg r) ∧ c'.nmem = c.nmem ∧
        (∀ a, (a < eb₂ ∨ eb₂ + b ≤ a) → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
        Vals b eb₂ (fun i => E (π i)) c') := by
  refine spec_while (ICpTo b eb₂ π W E c) (fun c => 9 * (b - c.nreg 16)) (fun c h => h.wb)
    (fun c' hc' hlt' => cpToBody_exec hπ hL hE hV c' hc' hlt')
    ⟨hc, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, by omega,
      fun i hi => absurd hi (by omega)⟩ ?_
  intro c' k hI hn hk
  rw [hI.nreg 1 (by omega) (by omega) (by omega), hE.r1] at hn
  refine ⟨by rw [h16] at hk; omega, hI.nreg, hI.rreg, hI.nmem, hI.rmem, hI.out,
    fun v hv => hI.cp v (by omega)⟩

/-- The state of the copy back `e[π i] := e₂[i]` of the values `E₂`, started from `c₀`. -/
structure ICpBack (b eb : ℕ) (π : ℕ → ℕ) (W : ℕ) (E₂ : ℕ → ℤ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  nreg : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → c.nreg r = c₀.nreg r
  rreg : ∀ r, r ≠ 16 → c.rreg r = c₀.rreg r
  nmem : c.nmem = c₀.nmem
  rmem : ∀ a, (a < eb ∨ eb + b ≤ a) → c.rmem a = c₀.rmem a
  out : c.output = c₀.output
  le : c.nreg 16 ≤ b
  cp : ∀ i < c.nreg 16, c.rmem (eb + π i) = E₂ i

/-- One step of the copy back. -/
theorem cpBackBody_exec (hπ : IsPermB b π) (hL : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) {E₂ : ℕ → ℤ}
    {c₀ : Config} (hE : Env2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π c₀) (hV : Vals b eb₂ E₂ c₀)
    (c : Config) (hI : ICpBack b eb π W E₂ c₀ c) (hlt : c.nreg 16 < c.nreg 1) :
    ∃ c' k', Exec P W cpBackBody c c' k' ∧ ICpBack b eb π W E₂ c₀ c' ∧
      9 * (b - c'.nreg 16) + k' + 2 ≤ 9 * (b - c.nreg 16) := by
  have hc := hI.wb
  have hpe := hL.pe
  have hee := hL.ee
  have hed := hL.ed
  have hdd := hL.dd
  have hw := hL.w
  have hpw := hL.pw
  have g : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → c.nreg r = c₀.nreg r := hI.nreg
  have g1 : c.nreg 1 = b := (g 1 (by omega) (by omega) (by omega)).trans hE.r1
  have g6 : c.nreg 6 = eb := (g 6 (by omega) (by omega) (by omega)).trans hE.r6
  have g8 : c.nreg 8 = eb₂ := (g 8 (by omega) (by omega) (by omega)).trans hE.r8
  have g9 : c.nreg 9 = πb := (g 9 (by omega) (by omega) (by omega)).trans hE.r9
  have g10 : c.nreg 10 = 1 := (g 10 (by omega) (by omega) (by omega)).trans hE.r10
  rw [g1] at hlt
  have hle := hI.le
  generalize hm : c.nreg 16 = m at hlt hle
  have hpm : c.nmem (πb + m) = π m := by rw [hI.nmem]; exact hE.perm m hlt
  have hpl := hπ.lt m hlt
  have hrd : c.rmem (eb₂ + m) = E₂ m := by
    rw [hI.rmem _ (Or.inr (by omega))]; exact hV _ hlt
  unfold cpBackBody
  exec_block
  · rw [g9, hm]; omega
  · config_simp; rw [g6, g9, hm, hpm]; omega
  · config_simp; rw [g8, hm]; omega
  · config_simp; rw [hm, g10]; omega
  refine ⟨⟨‹_›, fun r h1 h2 h3 => ?_, fun r h1 => ?_, rfl.trans hI.nmem, fun a ha => ?_,
    hI.out, ?_, fun i hi => ?_⟩, ?_⟩
  · config_simp; rw [← g r h1 h2 h3]; upd_tac
  · config_simp; rw [← hI.rreg r h1]; upd_tac
  · config_simp; rw [upd_apply, g6, g9, hm, hpm]
    split_ifs with h
    · omega
    · exact hI.rmem a ha
  · config_simp; rw [hm, g10]; omega
  · config_simp at hi; rw [hm, g10] at hi
    config_simp; rw [upd_apply, g8, hm, g6, g9, hpm, hrd]
    split_ifs with h
    · rw [hπ.inj i m (by omega) hlt (by omega)]
    · have him : i ≠ m := fun e => h (by rw [e])
      exact hI.cp i (by omega)
  · config_simp; rw [hm, g10]; omega

/-- **The copy back `e[π i] := e₂[i]`** of the values `E₂` at `eb₂`, within `9 b + 2` steps. -/
theorem cpBack_exec (hπ : IsPermB b π) (hL : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) {E₂ : ℕ → ℤ}
    (c : Config) (hc : WordsBounded W c) (hE : Env2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π c)
    (hV : Vals b eb₂ E₂ c) (h16 : c.nreg 16 = 0) :
    ∃ c' k, Exec P W (.whileLtN 16 1 cpBackBody) c c' k ∧ k ≤ 9 * b + 2 ∧
      ((∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 16 → c'.rreg r = c.rreg r) ∧ c'.nmem = c.nmem ∧
        (∀ a, (a < eb ∨ eb + b ≤ a) → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
        ∀ i < b, c'.rmem (eb + π i) = E₂ i) := by
  refine spec_while (ICpBack b eb π W E₂ c) (fun c => 9 * (b - c.nreg 16)) (fun c h => h.wb)
    (fun c' hc' hlt' => cpBackBody_exec hπ hL hE hV c' hc' hlt')
    ⟨hc, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, by omega,
      fun i hi => absurd hi (by omega)⟩ ?_
  intro c' k hI hn hk
  rw [hI.nreg 1 (by omega) (by omega) (by omega), hE.r1] at hn
  refine ⟨by rw [h16] at hk; omega, hI.nreg, hI.rreg, hI.nmem, hI.rmem, hI.out,
    fun v hv => hI.cp v (by omega)⟩

/-! ### The straight-line pieces of a round -/

/-- The start of phase 1: the flag `0`, `r2 = Db₁`, `r3 = eb`, `r20 = 1`. -/
theorem start1_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (block [.constN 30 0, .copyN 2 5, .copyN 3 6, .constN 20 1]) c c' k ∧
      k ≤ 4 ∧ (c'.nreg 30 = 0 ∧ c'.nreg 2 = c.nreg 5 ∧ c'.nreg 3 = c.nreg 6 ∧ c'.nreg 20 = 1 ∧
        (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 20 → r ≠ 30 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  exec_block
  · omega
  · omega
  exact ⟨by omega, by config_simp, by config_simp, by config_simp, by config_simp,
    fun r h1 h2 h3 h4 => by config_simp; upd_tac, rfl, rfl, rfl, rfl⟩

/-- Between the phases: save the flag in `r31`, reset it, `r16 = 0`. -/
theorem mid_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (block [.copyN 31 30, .constN 30 0, .constN 16 0]) c c' k ∧
      k ≤ 3 ∧ (c'.nreg 31 = c.nreg 30 ∧ c'.nreg 30 = 0 ∧ c'.nreg 16 = 0 ∧
        (∀ r, r ≠ 16 → r ≠ 30 → r ≠ 31 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  exec_block
  · omega
  · omega
  exact ⟨by omega, by config_simp, by config_simp, by config_simp,
    fun r h1 h2 h3 => by config_simp; upd_tac, rfl, rfl, rfl, rfl⟩

/-- The start of phase 2: `r2 = Db₂`, `r3 = eb₂`, `r20 = 1`. -/
theorem start2_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (block [.copyN 2 7, .copyN 3 8, .constN 20 1]) c c' k ∧
      k ≤ 3 ∧ (c'.nreg 2 = c.nreg 7 ∧ c'.nreg 3 = c.nreg 8 ∧ c'.nreg 20 = 1 ∧
        (∀ r, r ≠ 2 → r ≠ 3 → r ≠ 20 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  exec_block
  · omega
  exact ⟨by omega, by config_simp, by config_simp, by config_simp,
    fun r h1 h2 h3 => by config_simp; upd_tac, rfl, rfl, rfl, rfl⟩

/-- `r30 := max r30 r31`. -/
theorem flag_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' k, Exec P W (.ifLtN 30 31 (.instr (.copyN 30 31)) .skip) c c' k ∧ k ≤ 2 ∧
      (((c'.nreg 30 = c.nreg 31 ∧ c.nreg 30 < c.nreg 31) ∨
          (c'.nreg 30 = c.nreg 30 ∧ ¬ c.nreg 30 < c.nreg 31)) ∧
        (∀ r, r ≠ 30 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  by_cases h : c.nreg 30 < c.nreg 31
  · refine spec_ifLtN_true h ?_
    refine spec_instr (Exec.copyN hc 30 31) fun _ => ?_
    refine ⟨le_refl _, Or.inl ⟨by config_simp, h⟩, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    config_simp; rw [upd_other _ _ _ hr]
  · refine spec_ifLtN_false h ?_
    refine spec_skip hc ?_
    exact ⟨by omega, Or.inr ⟨rfl, h⟩, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

/-! ### A round -/

/-- The state between the rounds. -/
structure IK2 (b Db₁ eb Db₂ eb₂ πb pb : ℕ) (D₁ D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) (W : ℕ)
    (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  env : Env2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π c
  r14 : c.nreg 14 ≤ b + 1
  flag : c.nreg 30 ≤ 1
  vals : ∃ E, Vals b eb E c ∧
    (HasPot2 b D₁ D₂ π → ∀ v < b,
      bfu b D₁ D₂ π b v ≤ E v ∧ E v ≤ bfu b D₁ D₂ π (c.nreg 14) v) ∧
    (1 ≤ c.nreg 14 → c.nreg 30 = 0 → Feas2 b D₁ D₂ π E) ∧
    (1 ≤ c.nreg 14 → c.nreg 30 = 1 → HasPot2 b D₁ D₂ π →
      ∃ v < b, bfu b D₁ D₂ π b v < bfu b D₁ D₂ π (c.nreg 14 - 1) v)
  out : c.output = c₀.output

/-- The cost bound of a round of the union. -/
def round2Cost (b : ℕ) : ℕ :=
  2 * ((levelCost b + 2) * (Nat.log 2 b + 1) + 2) + 2 * (9 * b + 2) + 14

/-- **A round of the union** (one iteration of the main loop): the invariant `IK2`
advances from `k` to `k + 1` rounds within `round2Cost b` steps. -/
theorem round2_exec (hπ : IsPermB b π) (hD₁ : Crossing b D₁) (hD₂ : Crossing b D₂)
    (hL : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) {c₀ : Config} (c : Config)
    (hI : IK2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π W c₀ c) (hlt : c.nreg 14 < c.nreg 15) :
    ∃ c' k', Exec P W round2 c c' k' ∧ IK2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π W c₀ c' ∧
      (round2Cost b + 2) * (b + 1 - c'.nreg 14) + k' + 2 ≤
        (round2Cost b + 2) * (b + 1 - c.nreg 14) := by
  have hc := hI.wb
  have hE := hI.env
  have hl₁ := hL.lay₁
  have hl₂ := hL.lay₂
  have hpe := hL.pe
  have hee := hL.ee
  have hed := hL.ed
  have hdd := hL.dd
  have hw := hL.w
  have hpp := hL.pp
  have hpw := hL.pw
  rw [hE.r15] at hlt
  generalize hk : c.nreg 14 = k at hlt
  obtain ⟨E, hV, hB, -, -⟩ := hI.vals
  rw [hk] at hB
  have hK : Keep b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π k c₀ c := ⟨hE, hk, hI.out⟩
  unfold round2
  -- phase 1: the levels of matrix 1 on `e`
  refine spec_seq ?_
  refine spec_use (start1_exec c hc (by omega)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a30, a2, a3, a20, an, ar, anm, arm, ao⟩
  have hK₁ := hK.of hL (fun r hr h2 h3 => an r h2 h3 (by omega) (by omega)) (by rw [ar])
    (fun a _ => by rw [arm]) (fun a _ => by rw [anm]) ao
  refine spec_seq ?_
  refine spec_use (levels2_exec (P := P) hD₁ hl₁ (Q := HasPot2 b D₁ D₂ π)
    (lo := bfu b D₁ D₂ π b) (hi := bfu b D₁ D₂ π k) c₁ hw₁
    (hK₁.env.env₁ (by rw [a2, hE.r5]) (by rw [a3, hE.r6]))
    (fun v hv => by rw [arm]; exact hV v hv)
    a20 a30 (fun hP i j hi hj hij => (bfu_feas hπ hP i j hi hj hij).1) hB) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hF₂, _, E₁, hV₁, hR₁⟩
  have hK₂ := hK₁.ofFrm hL (by omega) hF₂
  -- the copy to `e₂`
  refine spec_seq ?_
  refine spec_use (mid_exec c₂ hw₂) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨b31, b30, b16, bn, br, bnm, brm, bo⟩
  have hK₃ := hK₂.of hL (fun r hr _ _ => bn r (by omega) (by omega) (by omega)) (by rw [br])
    (fun a _ => by rw [brm]) (fun a _ => by rw [bnm]) bo
  refine spec_seq ?_
  refine spec_use (cpTo_exec (P := P) hπ hL (E := E₁) c₃ hw₃ hK₃.env
    (fun v hv => by rw [brm]; exact hV₁ v hv) b16) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨cn, cr, cnm, crm, co, cV⟩
  have hK₄ := hK₃.of hL (fun r hr _ _ => cn r (by omega) (by omega) (by omega))
    (cr 10 (by omega)) (fun a ha => crm a (Or.inr (by omega))) (fun a _ => by rw [cnm]) co
  -- phase 2: the levels of matrix 2 on `e₂`
  refine spec_seq ?_
  refine spec_use (start2_exec c₄ hw₄ (by omega)) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨d2, d3, d20, dn, dr, dnm, drm, d_o⟩
  have hK₅ := hK₄.of hL (fun r hr h2 h3 => dn r h2 h3 (by omega)) (by rw [dr])
    (fun a _ => by rw [drm]) (fun a _ => by rw [dnm]) d_o
  have hS₂ : HasPot2 b D₁ D₂ π → ∀ v < b,
      bfu b D₁ D₂ π b (π v) ≤ E₁ (π v) ∧ E₁ (π v) ≤ bfu b D₁ D₂ π k (π v) := fun hP v hv =>
    ⟨((hR₁.bf hP).1 (π v) (hπ.lt v hv)).1,
      (hR₁.le _ (hπ.lt v hv)).trans ((hR₁.bf hP).1 (π v) (hπ.lt v hv)).2⟩
  refine spec_seq ?_
  refine spec_use (levels2_exec (P := P) hD₂ hl₂ (Q := HasPot2 b D₁ D₂ π)
    (lo := fun v => bfu b D₁ D₂ π b (π v)) (hi := fun v => bfu b D₁ D₂ π k (π v)) c₅ hw₅
    (hK₅.env.env₂ (by rw [d2, hK₄.env.r7]) (by rw [d3, hK₄.env.r8]))
    (fun v hv => by rw [drm]; exact cV v hv) d20
    (by rw [dn 30 (by omega) (by omega) (by omega), cn 30 (by omega) (by omega) (by omega), b30])
    (fun hP i j hi hj hij => (bfu_feas hπ hP i j hi hj hij).2) hS₂) ?_
  intro c₆ k₆ hk₆ hw₆ ⟨hF₆, _, E₂, hV₂, hR₂⟩
  have hK₆ := hK₅.ofFrm hL (by omega) hF₆
  -- the copy back
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₆ 16 0 (by omega)) fun hw₇ => ?_
  refine spec_seq ?_
  have hK₇ : Keep b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π k c₀ { c₆ with nreg := upd c₆.nreg 16 0 } :=
    hK₆.of hL (fun r hr _ _ => by config_simp; upd_tac) rfl (fun _ _ => rfl) (fun _ _ => rfl) rfl
  refine spec_use (cpBack_exec (P := P) hπ hL (E₂ := E₂) _ hw₇ hK₇.env
    (fun v hv => by config_simp; exact hV₂ v hv) (by config_simp)) ?_
  intro c₈ k₈ hk₈ hw₈ ⟨en, er, enm, erm, eo, eV⟩
  have hK₈ := hK₇.of hL (fun r hr _ _ => en r (by omega) (by omega) (by omega))
    (er 10 (by omega)) (fun a ha => erm a (Or.inr (by omega))) (fun a _ => by rw [enm]) eo
  have g31 : c₈.nreg 31 = c₂.nreg 30 := by
    rw [en 31 (by omega) (by omega) (by omega)]; config_simp
    rw [hF₆.nreg 31 (by omega) (by omega), dn 31 (by omega) (by omega) (by omega),
      cn 31 (by omega) (by omega) (by omega), b31]
  have g30 : c₈.nreg 30 = c₆.nreg 30 := by
    rw [en 30 (by omega) (by omega) (by omega)]; config_simp
  obtain ⟨E', hE'⟩ := hπ.exists_inv E₂
  have hV' : Vals b eb E' c₈ := fun v hv => by
    obtain ⟨i, hi, rfl⟩ := hπ.surj hv
    rw [eV i hi, hE' i hi]
  -- the flag
  refine spec_seq ?_
  refine spec_use (flag_exec c₈ hw₈) ?_
  intro c₉ k₉ hk₉ hw₉ ⟨hfl, fn, fr, fnm, frm, fo⟩
  rw [g31, g30] at hfl
  obtain ⟨hM1, hM2, hM3, hM4⟩ := round2_math hπ hR₁ hR₂ hE' hfl
  have g14 : c₉.nreg 14 = k := by rw [fn 14 (by omega)]; exact hK₈.r14
  have g10 : c₉.nreg 10 = 1 := by rw [fn 10 (by omega)]; exact hK₈.env.r10
  have hE₉ := hK₈.env.of hL (c' := c₉) (fun r hr _ _ _ _ _ => fn r (by omega)) (by rw [fr])
    (fun a _ => by rw [frm]) (fun a _ => by rw [fnm])
  refine spec_instr (Exec.addN hw₉ 14 14 10 (by rw [g14, g10]; omega)) fun hw₁₀ => ?_
  refine ⟨⟨hw₁₀, hE₉.of hL (fun r hr _ _ _ _ h14 => by config_simp; rw [upd_other _ _ _ h14]) rfl
      (fun _ _ => rfl) (fun _ _ => rfl), by config_simp; rw [g14, g10]; omega,
    by config_simp; exact hM1,
    ⟨E', fun v hv => by config_simp; rw [frm]; exact hV' v hv,
      fun hP v hv => by config_simp; rw [g14, g10]; exact hM2 hP v hv,
      fun _ h0 => by config_simp at h0; exact hM3 h0,
      fun _ h1 hP => by
        config_simp at h1; config_simp; rw [g14, g10, Nat.add_sub_cancel]; exact hM4 h1 hP⟩,
    by config_simp; rw [fo]; exact hK₈.out⟩, ?_⟩
  -- the cost
  config_simp; rw [g14, g10]
  have := mul_pred_add (a := round2Cost b + 2) (x := b + 1 - k) (by omega)
  rw [show b + 1 - k - 1 = b + 1 - (k + 1) by omega] at this
  have hR : round2Cost b =
      2 * ((levelCost b + 2) * (Nat.log 2 b + 1) + 2) + 2 * (9 * b + 2) + 14 := rfl
  generalize (levelCost b + 2) * (Nat.log 2 b + 1) = LC at hk₂ hk₆ hR
  generalize round2Cost b = R at hR this ⊢
  omega

/-! ### The whole run -/

/-- The state of the initialization of the values. -/
structure II2 (b Db₁ eb Db₂ eb₂ πb pb : ℕ) (D₁ D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) (W : ℕ)
    (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  env : Env2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π c
  r3 : c.nreg 3 = eb
  r12 : c.nreg 12 ≤ b
  r14 : c.nreg 14 = 0
  r30 : c.nreg 30 = 0
  zero : ∀ v < c.nreg 12, c.rmem (eb + v) = 0
  out : c.output = c₀.output

/-- One value set to `0`. -/
theorem initBody2_exec (hL : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) {c₀ : Config} (c : Config)
    (hI : II2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π W c₀ c) (hlt : c.nreg 12 < c.nreg 1) :
    ∃ c' k', Exec P W initBody c c' k' ∧ II2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π W c₀ c' ∧
      5 * (b - c'.nreg 12) + k' + 2 ≤ 5 * (b - c.nreg 12) := by
  have hc := hI.wb
  have hE := hI.env
  have hw := hL.w
  have hee := hL.ee
  have hed := hL.ed
  have hdd := hL.dd
  rw [hE.r1] at hlt
  unfold initBody
  exec_block
  · rw [hI.r3]; omega
  · config_simp; rw [hE.r10]; omega
  refine ⟨⟨‹_›, hE.of hL (fun r hr _ _ _ _ _ => by config_simp; upd_tac) rfl (fun a ha => ?_)
    (fun _ _ => rfl), ?_, ?_, ?_, ?_, fun v hv => ?_, hI.out⟩, ?_⟩
  · config_simp; rw [upd_other _ _ _ (by rw [hI.r3]; omega)]
  · config_simp; exact hI.r3
  · config_simp; rw [hE.r10]; omega
  · config_simp; exact hI.r14
  · config_simp; exact hI.r30
  · config_simp at hv; config_simp
    rw [hE.r10] at hv
    rw [upd_apply, hI.r3, hE.z10]
    split_ifs with h
    · rfl
    · exact hI.zero v (by omega)
  · config_simp; rw [hE.r10]; omega

/-- The cost bound of the whole run. -/
def bf2Cost (b : ℕ) : ℕ := 5 * b + 12 + (round2Cost b + 2) * (b + 1)

/-- **Bellman–Ford over the union of two dense distance graphs on the machine.** On two dense
distance graphs on the vertices `0, …, b - 1`, the first with the lengths `D₁ i j` at
`Db₁ + i b + j` (crossing), the second with the lengths `D₂ i j` of the arcs `π i → π j` at
`Db₂ + i b + j` (crossing) for the permutation `π` stored at `πb`, `bfDDG2` runs `b + 1` rounds
of Bellman–Ford over their union from the values `0` within `bf2Cost b = O(b² log b)` steps
(`bf2Cost_le`). At the end the values `E v` are stored at `eb + v`, and either `r30 = 0` and `E`
is a feasible potential of both matrices, or `r30 = 1` and the two matrices have no common
feasible potential. If one exists, `E` is `bfu b`, the Bellman–Ford values of the union: the
distances from a virtual source joined to every vertex by an arc of length `0`. The input is
kept. -/
theorem bfDDG2_exec (hπ : IsPermB b π) (hD₁ : Crossing b D₁) (hD₂ : Crossing b D₂)
    (hL : Lay2 b Db₁ eb Db₂ eb₂ πb pb W) (c : Config) (hc : WordsBounded W c)
    (h1 : c.nreg 1 = b) (h2 : c.nreg 2 = Db₁) (h3 : c.nreg 3 = eb) (h4 : c.nreg 4 = pb)
    (h7 : c.nreg 7 = Db₂) (h8 : c.nreg 8 = eb₂) (h9 : c.nreg 9 = πb)
    (hD₁m : ∀ i j, i < b → j < b → c.rmem (Db₁ + i * b + j) = D₁ i j)
    (hD₂m : ∀ i j, i < b → j < b → c.rmem (Db₂ + i * b + j) = D₂ i j)
    (hπm : ∀ i < b, c.nmem (πb + i) = π i) :
    ∃ c' k, Exec P W bfDDG2 c c' k ∧ k ≤ bf2Cost b ∧
      ∃ E : ℕ → ℤ, (∀ v < b, c'.rmem (eb + v) = E v) ∧
        ((c'.nreg 30 = 0 ∧ Feas2 b D₁ D₂ π E) ∨
          (c'.nreg 30 = 1 ∧ ¬ ∃ E', Feas2 b D₁ D₂ π E')) ∧
        ((∃ E', Feas2 b D₁ D₂ π E') → ∀ v < b, E v = bfu b D₁ D₂ π b v) ∧
        c'.output = c.output ∧
        (∀ i j, i < b → j < b → c'.rmem (Db₁ + i * b + j) = D₁ i j) ∧
        (∀ i j, i < b → j < b → c'.rmem (Db₂ + i * b + j) = D₂ i j) ∧
        (∀ i < b, c'.nmem (πb + i) = π i) := by
  have hw := hL.w
  unfold bfDDG2
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  · config_simp; rw [h1]; omega
  · omega
  · omega
  refine spec_seq ?_
  refine spec_while (II2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π W c) (fun c => 5 * (b - c.nreg 12))
    (fun c h => h.wb) (fun c' hc' hlt' => initBody2_exec hL c' hc' hlt')
    ⟨‹_›, ⟨by config_simp; exact h1, by config_simp; exact h4, by config_simp; exact h2,
      by config_simp; exact h3, by config_simp; exact h7, by config_simp; exact h8,
      by config_simp; exact h9, by config_simp, by config_simp; rw [h1], by config_simp; simp,
      fun i j hi hj => by config_simp; exact hD₁m i j hi hj,
      fun i j hi hj => by config_simp; exact hD₂m i j hi hj,
      fun i hi => by config_simp; exact hπm i hi⟩,
      by config_simp; exact h3, by config_simp; omega, by config_simp, by config_simp,
      fun v hv => by config_simp at hv; omega, rfl⟩ ?_
  intro c₁ k₁ hI₁ hn₁ hk₁
  have h12 : c₁.nreg 12 = b := by have := hI₁.r12; rw [hI₁.env.r1] at hn₁; omega
  refine spec_while (IK2 b Db₁ eb Db₂ eb₂ πb pb D₁ D₂ π W c)
    (fun c => (round2Cost b + 2) * (b + 1 - c.nreg 14))
    (fun c h => h.wb) (fun c' hc' hlt' => round2_exec hπ hD₁ hD₂ hL c' hc' hlt')
    ⟨hI₁.wb, hI₁.env, by rw [hI₁.r14]; omega, by rw [hI₁.r30]; omega,
      ⟨fun _ => 0, fun v hv => by rw [hI₁.zero v (by omega)]; simp, fun hP v hv => ?_,
        fun h => by rw [hI₁.r14] at h; omega, fun h => by rw [hI₁.r14] at h; omega⟩,
      hI₁.out⟩ ?_
  · rw [hI₁.r14, bfu_zero]
    exact ⟨by have := bfu_card_le hP 0 hv; rwa [bfu_zero] at this, le_rfl⟩
  intro c₂ k₂ hI₂ hn₂ hk₂
  have h14 : c₂.nreg 14 = b + 1 := by have := hI₂.r14; rw [hI₂.env.r15] at hn₂; omega
  obtain ⟨E, hV, hB, hF, hN⟩ := hI₂.vals
  rw [h14] at hB hF hN
  refine ⟨?_, E, hV, ?_, fun hP v hv => ?_, by rw [hI₂.out], hI₂.env.d₁, hI₂.env.d₂,
    hI₂.env.perm⟩
  · beta_reduce at hk₁ hk₂
    config_simp at hk₁
    rw [hI₁.r14, Nat.sub_zero] at hk₂
    unfold bf2Cost
    omega
  · have hfl := hI₂.flag
    rcases Nat.lt_or_ge (c₂.nreg 30) 1 with h | h
    · exact Or.inl ⟨by omega, hF (by omega) (by omega)⟩
    · refine Or.inr ⟨by omega, fun hP => ?_⟩
      obtain ⟨v, hv, hlt⟩ := hN (by omega) (by omega) ((hasPot2_iff hπ).2 hP)
      rw [Nat.add_sub_cancel] at hlt
      exact lt_irrefl _ hlt
  · have hP' := (hasPot2_iff hπ).2 hP
    have := hB hP' v hv
    rw [bfu_succ_card hP' hv] at this
    omega

/-- The cost of the whole run is `O(b² log b)`. -/
theorem bf2Cost_le (b : ℕ) : bf2Cost b ≤ 6500 * (b + 1) ^ 2 * (Nat.log 2 b + 1) := by
  unfold bf2Cost round2Cost levelCost
  have hL : 1 ≤ Nat.log 2 b + 1 := by omega
  generalize Nat.log 2 b + 1 = L at hL ⊢
  nlinarith [Nat.mul_le_mul (le_refl (b + 1)) hL, Nat.mul_le_mul (le_refl ((b + 1) * (b + 1))) hL]

end Monge

end PlanarFlow
