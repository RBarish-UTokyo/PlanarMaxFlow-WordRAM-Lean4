module

public import PlanarFlow.Monge.DDGBF2
public import PlanarFlow.Monge.DDGBFO

/-!
# Bellman–Ford over the union of two dense distance graphs with missing arcs, on the machine

The program and the proof of `PlanarFlow/Monge/DDGBF2.lean` (two dense distance graphs on the
same `b` vertices, each crossing in its own order, the second through a permutation `π`), for
dense distance graphs **with missing arcs**: the arc `i → j` of matrix 1 exists when `X₁ i j`,
with the length `D₁ i j`, the arc `π i → π j` of matrix 2 when `X₂ i j`, with the length
`D₂ i j`, and each satisfies the crossing inequality in the extended sense
(`PlanarFlow.Monge.CrossingX`, the form of `PlanarFlow.Monge.CrossingO`). Each matrix is stored
as the static tables of `PlanarFlow/Monge/DDGBFOHead.lean` (`tVal`, `tMul`, `finB`, with a bound
`H` above the lengths plus `b`), and the level loops are `whileLtN 20 1 levelBFO`
(`PlanarFlow.Monge.levelsO_exec`).

* `ddg2O b X₁ D₁ X₂ D₂ π`: the union digraph (only the existing arcs); `bfuO`, `HasPot2O`,
  `Feas2O` (`hasPot2O_iff`); `round2O_math`: one round of the union.
* `bfDDG2O_exec`: **the run** halts within `bf2CostO b ≤ 7600 (b + 1)² (log₂ b + 1)` steps
  (`bf2CostO_le`), with flag `0` and a feasible potential of both matrices, or flag `1` and none;
  with a feasible potential, the values are `bfuO b`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The union digraph with missing arcs -/

/-- The arcs `i → j`, `i ≠ j`, with `X i j`. -/
def ArcX (b : ℕ) (X : ℕ → ℕ → Prop) : Type := {p : Fin b × Fin b // p.1 ≠ p.2 ∧ X p.1 p.2}

noncomputable instance (b : ℕ) (X : ℕ → ℕ → Prop) : Fintype (ArcX b X) := by
  classical unfold ArcX; infer_instance

variable {b : ℕ} {π : ℕ → ℕ} {X₁ X₂ : ℕ → ℕ → Prop} {D₁ D₂ : ℕ → ℕ → ℤ} {H₁ H₂ : ℝ}

/-- **The union of the two dense distance graphs with missing arcs.** -/
def ddg2O (b : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (X₂ : ℕ → ℕ → Prop)
    (D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) : Digraph (Fin b) (ArcX b X₁ ⊕ ArcX b X₂) where
  src := Sum.elim (fun a => a.1.1) fun a => pfin b π a.1.1
  dst := Sum.elim (fun a => a.1.2) fun a => pfin b π a.1.2
  len := Sum.elim (fun a => D₁ a.1.1 a.1.2) fun a => D₂ a.1.1 a.1.2

/-- The Bellman–Ford values of the union, indexed by `ℕ` (`0` outside). -/
noncomputable def bfuO (b : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (X₂ : ℕ → ℕ → Prop)
    (D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) (k : ℕ) : ℕ → ℤ :=
  liftF b ((ddg2O b X₁ D₁ X₂ D₂ π).bf k)

/-- The union has a feasible potential. -/
def HasPot2O (b : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (X₂ : ℕ → ℕ → Prop)
    (D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) : Prop := ∃ p, (ddg2O b X₁ D₁ X₂ D₂ π).IsPot p

/-- `E` is a feasible potential of both matrices (on their existing arcs). -/
def Feas2O (b : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (X₂ : ℕ → ℕ → Prop)
    (D₂ : ℕ → ℕ → ℤ) (π : ℕ → ℕ) (E : ℕ → ℤ) : Prop :=
  ∀ i j, i < b → j < b → i ≠ j →
    (X₁ i j → E j ≤ E i + D₁ i j) ∧ (X₂ i j → E (π j) ≤ E (π i) + D₂ i j)

/-- A feasible potential of both matrices is a feasible potential of the union. -/
theorem isPot_of_feas2O (hπ : IsPermB b π) {E : ℕ → ℤ} (h : Feas2O b X₁ D₁ X₂ D₂ π E) :
    (ddg2O b X₁ D₁ X₂ D₂ π).IsPot (fun v => E v) := by
  intro a
  rcases a with a | a
  · exact (h a.1.1 a.1.2 a.1.1.2 a.1.2.2 (fun e => a.2.1 (Fin.ext e))).1 a.2.2
  · show E (pfin b π a.1.2) ≤ E (pfin b π a.1.1) + D₂ a.1.1 a.1.2
    rw [pfin_val hπ, pfin_val hπ]
    exact (h a.1.1 a.1.2 a.1.1.2 a.1.2.2 (fun e => a.2.1 (Fin.ext e))).2 a.2.2

/-- A feasible potential of the union is a feasible potential of both matrices. -/
theorem feas2O_of_isPot (hπ : IsPermB b π) {p : Fin b → ℤ}
    (hp : (ddg2O b X₁ D₁ X₂ D₂ π).IsPot p) : Feas2O b X₁ D₁ X₂ D₂ π (liftF b p) := by
  intro i j hi hj hij
  have hne : (⟨i, hi⟩ : Fin b) ≠ ⟨j, hj⟩ := fun e => hij (congrArg Fin.val e)
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have := hp (.inl ⟨(⟨i, hi⟩, ⟨j, hj⟩), hne, hx⟩)
    rw [liftF_of_lt hi, liftF_of_lt hj]
    exact this
  · have := hp (.inr ⟨(⟨i, hi⟩, ⟨j, hj⟩), hne, hx⟩)
    change p (pfin b π ⟨j, hj⟩) ≤ p (pfin b π ⟨i, hi⟩) + D₂ i j at this
    rw [liftF_of_lt (hπ.lt i hi), liftF_of_lt (hπ.lt j hj)]
    rwa [show pfin b π ⟨j, hj⟩ = ⟨π j, hπ.lt j hj⟩ from Fin.ext (pfin_val hπ _),
      show pfin b π ⟨i, hi⟩ = ⟨π i, hπ.lt i hi⟩ from Fin.ext (pfin_val hπ _)] at this

/-- **The union has a feasible potential iff both matrices have a common feasible potential.** -/
theorem hasPot2O_iff (hπ : IsPermB b π) :
    HasPot2O b X₁ D₁ X₂ D₂ π ↔ ∃ E, Feas2O b X₁ D₁ X₂ D₂ π E :=
  ⟨fun ⟨_, hp⟩ => ⟨_, feas2O_of_isPot hπ hp⟩, fun ⟨_, hE⟩ => ⟨_, isPot_of_feas2O hπ hE⟩⟩

/-- With a feasible potential, `bfuO b` is one. -/
theorem bfuO_feas (hπ : IsPermB b π) (hP : HasPot2O b X₁ D₁ X₂ D₂ π) :
    Feas2O b X₁ D₁ X₂ D₂ π (bfuO b X₁ D₁ X₂ D₂ π b) := by
  obtain ⟨p, hp⟩ := hP
  have := (ddg2O b X₁ D₁ X₂ D₂ π).isPot_bf_card hp
  rw [Fintype.card_fin] at this
  exact feas2O_of_isPot hπ this

/-- No round: the values `0`. -/
lemma bfuO_zero (v : ℕ) : bfuO b X₁ D₁ X₂ D₂ π 0 v = 0 := by
  unfold bfuO liftF; split_ifs <;> rfl

/-- With a feasible potential, `bfuO b` is below every `bfuO k`. -/
theorem bfuO_card_le (hP : HasPot2O b X₁ D₁ X₂ D₂ π) (k : ℕ) {v : ℕ} (hv : v < b) :
    bfuO b X₁ D₁ X₂ D₂ π b v ≤ bfuO b X₁ D₁ X₂ D₂ π k v := by
  obtain ⟨p, hp⟩ := hP
  have := (ddg2O b X₁ D₁ X₂ D₂ π).bf_card_le k hp ⟨v, hv⟩
  rw [Fintype.card_fin] at this
  unfold bfuO
  rw [liftF_of_lt hv, liftF_of_lt hv]
  exact this

/-- With a feasible potential, the values do not change after `b` rounds. -/
theorem bfuO_succ_card (hP : HasPot2O b X₁ D₁ X₂ D₂ π) {v : ℕ} (hv : v < b) :
    bfuO b X₁ D₁ X₂ D₂ π (b + 1) v = bfuO b X₁ D₁ X₂ D₂ π b v := by
  obtain ⟨p, hp⟩ := hP
  have := (ddg2O b X₁ D₁ X₂ D₂ π).bf_succ_card hp ⟨v, hv⟩
  rw [Fintype.card_fin] at this
  unfold bfuO
  rw [liftF_of_lt hv, liftF_of_lt hv]
  exact this

/-- The end of a round of the union. -/
theorem bfuO_le_succ (hπ : IsPermB b π) {k : ℕ} {E : ℕ → ℤ}
    (h1 : ∀ v < b, E v ≤ bfuO b X₁ D₁ X₂ D₂ π k v)
    (h2 : ∀ i j, i < b → j < b → i ≠ j → X₁ i j → E j ≤ bfuO b X₁ D₁ X₂ D₂ π k i + D₁ i j)
    (h3 : ∀ i j, i < b → j < b → i ≠ j → X₂ i j →
      E (π j) ≤ bfuO b X₁ D₁ X₂ D₂ π k (π i) + D₂ i j)
    {v : ℕ} (hv : v < b) : E v ≤ bfuO b X₁ D₁ X₂ D₂ π (k + 1) v := by
  unfold bfuO
  rw [liftF_of_lt hv]
  refine (ddg2O b X₁ D₁ X₂ D₂ π).le_bf_succ_of_round (E := fun w => E w) (fun w => ?_)
    (fun a => ?_) ⟨v, hv⟩
  · have := h1 w w.2; unfold bfuO at this; rwa [liftF_of_lt w.2] at this
  · rcases a with a | a
    · have := h2 a.1.1 a.1.2 a.1.1.2 a.1.2.2 (fun e => a.2.1 (Fin.ext e)) a.2.2
      unfold bfuO at this
      rw [liftF_of_lt a.1.1.2] at this
      exact this
    · have := h3 a.1.1 a.1.2 a.1.1.2 a.1.2.2 (fun e => a.2.1 (Fin.ext e)) a.2.2
      show E (pfin b π a.1.2) ≤ (ddg2O b X₁ D₁ X₂ D₂ π).bf k (pfin b π a.1.1) + D₂ a.1.1 a.1.2
      rw [pfin_val hπ, show pfin b π a.1.1 = ⟨π a.1.1, hπ.lt _ a.1.1.2⟩ from
        Fin.ext (pfin_val hπ _)]
      unfold bfuO at this
      rw [liftF_of_lt (hπ.lt _ a.1.1.2)] at this
      exact this

/-- **One round of the union with missing arcs, mathematically** (as `round2_math`). -/
theorem round2O_math (hπ : IsPermB b π) {k : ℕ} {E₀ E₁ E₂ E' : ℕ → ℤ} {f₁ f₂ F : ℕ}
    (hR₁ : RoundGX b X₁ D₁ (HasPot2O b X₁ D₁ X₂ D₂ π) (bfuO b X₁ D₁ X₂ D₂ π b)
      (bfuO b X₁ D₁ X₂ D₂ π k) (fun _ _ => True) E₀ E₁ f₁)
    (hR₂ : RoundGX b X₂ D₂ (HasPot2O b X₁ D₁ X₂ D₂ π) (fun v => bfuO b X₁ D₁ X₂ D₂ π b (π v))
      (fun v => bfuO b X₁ D₁ X₂ D₂ π k (π v)) (fun _ _ => True) (fun v => E₁ (π v)) E₂ f₂)
    (hE' : ∀ i < b, E' (π i) = E₂ i) (hF : (F = f₁ ∧ f₂ < f₁) ∨ (F = f₂ ∧ ¬ f₂ < f₁)) :
    F ≤ 1 ∧
      (HasPot2O b X₁ D₁ X₂ D₂ π → ∀ v < b,
        bfuO b X₁ D₁ X₂ D₂ π b v ≤ E' v ∧ E' v ≤ bfuO b X₁ D₁ X₂ D₂ π (k + 1) v) ∧
      (F = 0 → Feas2O b X₁ D₁ X₂ D₂ π E') ∧
      (F = 1 → HasPot2O b X₁ D₁ X₂ D₂ π →
        ∃ v < b, bfuO b X₁ D₁ X₂ D₂ π b v < bfuO b X₁ D₁ X₂ D₂ π k v) := by
  have f1 := hR₁.flag_le
  have f2 := hR₂.flag_le
  have hle' : ∀ v < b, E' v ≤ E₁ v := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := hπ.surj hv
    rw [hE' i hi]; exact hR₂.le i hi
  refine ⟨by omega, fun hP v hv => ?_, fun h0 => ?_, fun h1 hP => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := hπ.surj hv
    refine ⟨by rw [hE' i hi]; exact ((hR₂.bf hP).1 i hi).1, bfuO_le_succ hπ (fun w hw => ?_)
      (fun i j hi hj hij hx => ?_) (fun i j hi hj hij hx => ?_) (hπ.lt i hi)⟩
    · exact (hle' w hw).trans ((hR₁.le w hw).trans ((hR₁.bf hP).1 w hw).2)
    · exact (hle' j hj).trans ((hR₁.bf hP).2 i j hi hj hij hx trivial)
    · rw [hE' j hj]; exact (hR₂.bf hP).2 i j hi hj hij hx trivial
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
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [hEq i hi, hEq j hj]; exact hR₁.feas h10 i j hi hj hij hx trivial
    · rw [hE' i hi, hE' j hj]; exact hR₂.feas h20 i j hi hj hij hx trivial
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

/-- **A round of the union with missing arcs** (`round2` with the level loop `levelBFO`). -/
def round2O : Stmt :=
  .seq (block [.constN 30 0, .copyN 2 5, .copyN 3 6, .constN 20 1]) <|
  .seq (.whileLtN 20 1 levelBFO) <|
  .seq (block [.copyN 31 30, .constN 30 0, .constN 16 0]) <|
  .seq (.whileLtN 16 1 cpToBody) <|
  .seq (block [.copyN 2 7, .copyN 3 8, .constN 20 1]) <|
  .seq (.whileLtN 20 1 levelBFO) <|
  .seq (.instr (.constN 16 0)) <|
  .seq (.whileLtN 16 1 cpBackBody) <|
  .seq (.ifLtN 30 31 (.instr (.copyN 30 31)) .skip) <|
  .instr (.addN 14 14 10)

/-- **Bellman–Ford over the union of two dense distance graphs with missing arcs.** -/
def bfDDG2O : Stmt :=
  .seq (block [.constN 10 1, .constR 10 0, .constN 12 0, .addN 15 1 10, .constN 14 0,
    .constN 30 0, .copyN 5 2, .copyN 6 3]) <|
  .seq (.whileLtN 12 1 initBody) (.whileLtN 14 15 round2O)

/-! ### The fixed data -/

/-- The layout of the memory and the word bound. -/
structure Lay2O (b Vb₁ eb Vb₂ eb₂ πb pb W : ℕ) : Prop where
  pe : pb + 5 * b + 1 < eb
  ee : eb + b ≤ eb₂
  ed : eb₂ + b ≤ Vb₁
  dd : Vb₁ + 2 * (b * b) ≤ Vb₂
  w : Vb₂ + 2 * (b * b) + 4 * b + 10 ≤ W
  pp : pb + 5 * b + 1 < πb
  pw : πb + b ≤ W

/-- The layout of matrix 1 for the level loop. -/
theorem Lay2O.lay₁ {Vb₁ eb Vb₂ eb₂ πb pb W : ℕ} (h : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) :
    LayO b Vb₁ eb pb W :=
  ⟨h.pe, by have := h.ee; have := h.ed; omega, by have := h.dd; have := h.w; omega⟩

/-- The layout of matrix 2 for the level loop. -/
theorem Lay2O.lay₂ {Vb₁ eb Vb₂ eb₂ πb pb W : ℕ} (h : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) :
    LayO b Vb₂ eb₂ pb W :=
  ⟨by have := h.pe; have := h.ee; omega, by have := h.ed; have := h.dd; omega, h.w⟩

/-- The fixed registers and the stored tables. -/
structure Env2O (b Vb₁ eb Vb₂ eb₂ πb pb : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (H₁ : ℝ)
    (X₂ : ℕ → ℕ → Prop) (D₂ : ℕ → ℕ → ℤ) (H₂ : ℝ) (π : ℕ → ℕ) (c : Config) : Prop where
  r1 : c.nreg 1 = b
  r4 : c.nreg 4 = pb
  r5 : c.nreg 5 = Vb₁
  r6 : c.nreg 6 = eb
  r7 : c.nreg 7 = Vb₂
  r8 : c.nreg 8 = eb₂
  r9 : c.nreg 9 = πb
  r10 : c.nreg 10 = 1
  r15 : c.nreg 15 = b + 1
  z10 : c.rreg 10 = 0
  t₁ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₁ + 2 * (s * b + t)) = tVal b X₁ D₁ H₁ s t
  m₁ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₁ + 2 * (s * b + t) + 1) = tMul b X₁ s t
  f₁ : ∀ s t, s < b → t < b → s ≠ t → c.nmem (Vb₁ + 2 * (s * b + t)) = finB X₁ s t
  t₂ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₂ + 2 * (s * b + t)) = tVal b X₂ D₂ H₂ s t
  m₂ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₂ + 2 * (s * b + t) + 1) = tMul b X₂ s t
  f₂ : ∀ s t, s < b → t < b → s ≠ t → c.nmem (Vb₂ + 2 * (s * b + t)) = finB X₂ s t
  perm : ∀ i < b, c.nmem (πb + i) = π i

variable {P : Input} {W Vb₁ eb Vb₂ eb₂ πb pb : ℕ}

/-- The fixed data survive a step with the given frame. -/
theorem Env2O.of (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) {c c' : Config}
    (h : Env2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π c)
    (hn : ∀ r, r < 16 → r ≠ 2 → r ≠ 3 → r ≠ 12 → r ≠ 13 → r ≠ 14 → c'.nreg r = c.nreg r)
    (hr : c'.rreg 10 = c.rreg 10) (hm : ∀ a, Vb₁ ≤ a → c'.rmem a = c.rmem a)
    (hnm : ∀ a, pb + 5 * b + 1 < a → c'.nmem a = c.nmem a) :
    Env2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π c' := by
  have hdd := hL.dd
  have hpe := hL.pe
  have hee := hL.ee
  have hed := hL.ed
  have hpp := hL.pp
  exact ⟨(hn 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r1,
    (hn 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r4,
    (hn 5 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r5,
    (hn 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r6,
    (hn 7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r7,
    (hn 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r8,
    (hn 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r9,
    (hn 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r10,
    (hn 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans h.r15,
    hr.trans h.z10, fun s t hs ht hst => (hm _ (by omega)).trans (h.t₁ s t hs ht hst),
    fun s t hs ht hst => (hm _ (by omega)).trans (h.m₁ s t hs ht hst),
    fun s t hs ht hst => (hnm _ (by omega)).trans (h.f₁ s t hs ht hst),
    fun s t hs ht hst => (hm _ (by omega)).trans (h.t₂ s t hs ht hst),
    fun s t hs ht hst => (hm _ (by omega)).trans (h.m₂ s t hs ht hst),
    fun s t hs ht hst => (hnm _ (by omega)).trans (h.f₂ s t hs ht hst),
    fun i hi => (hnm _ (by omega)).trans (h.perm i hi)⟩

/-- The data of matrix 1, when `r2 = Vb₁` and `r3 = eb`. -/
theorem Env2O.env₁ {c : Config} (h : Env2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π c)
    (h2 : c.nreg 2 = Vb₁) (h3 : c.nreg 3 = eb) : EnvO b Vb₁ eb pb X₁ D₁ H₁ c :=
  ⟨h.r1, h2, h3, h.r4, h.r10, h.z10, h.t₁, h.m₁, h.f₁⟩

/-- The data of matrix 2, when `r2 = Vb₂` and `r3 = eb₂`. -/
theorem Env2O.env₂ {c : Config} (h : Env2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π c)
    (h2 : c.nreg 2 = Vb₂) (h3 : c.nreg 3 = eb₂) : EnvO b Vb₂ eb₂ pb X₂ D₂ H₂ c :=
  ⟨h.r1, h2, h3, h.r4, h.r10, h.z10, h.t₂, h.m₂, h.f₂⟩

/-- The data kept during a round: the fixed data, the round counter `k`, the output. -/
structure KeepO (b Vb₁ eb Vb₂ eb₂ πb pb : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (H₁ : ℝ)
    (X₂ : ℕ → ℕ → Prop) (D₂ : ℕ → ℕ → ℤ) (H₂ : ℝ) (π : ℕ → ℕ) (k : ℕ)
    (c₀ c : Config) : Prop where
  env : Env2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π c
  r14 : c.nreg 14 = k
  out : c.output = c₀.output

/-- The kept data survive a step with the given frame. -/
theorem KeepO.of (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) {k : ℕ} {c₀ c c' : Config}
    (h : KeepO b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π k c₀ c)
    (hn : ∀ r, r < 16 → r ≠ 2 → r ≠ 3 → c'.nreg r = c.nreg r)
    (hr : c'.rreg 10 = c.rreg 10) (hm : ∀ a, Vb₁ ≤ a → c'.rmem a = c.rmem a)
    (hnm : ∀ a, pb + 5 * b + 1 < a → c'.nmem a = c.nmem a) (ho : c'.output = c.output) :
    KeepO b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π k c₀ c' :=
  ⟨h.env.of hL (fun r hr h2 h3 _ _ _ => hn r hr h2 h3) hr hm hnm,
    (hn 14 (by omega) (by omega) (by omega)).trans h.r14, ho.trans h.out⟩

/-- The levels of a phase keep the data. -/
theorem KeepO.ofFrm (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) {k e : ℕ} {c₀ c c' : Config}
    (he : e + b ≤ Vb₁) (h : KeepO b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π k c₀ c)
    (hF : Frm b e pb c c') :
    KeepO b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π k c₀ c' := by
  have := hL.pp
  exact h.of hL (fun r hr _ _ => hF.nreg r (by omega) (by omega))
    (hF.rreg 10 (by omega) (by omega) (by omega)) (fun a ha => hF.rmem a (Or.inr (by omega)))
    (fun a ha => hF.nmem a (by omega)) hF.out

/-! ### The copies -/

/-- The state of the copy `e₂[i] := e[π i]` of the values `E`, started from `c₀`. -/
structure ICpToO (b eb₂ : ℕ) (π : ℕ → ℕ) (W : ℕ) (E : ℕ → ℤ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  nreg : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → c.nreg r = c₀.nreg r
  rreg : ∀ r, r ≠ 16 → c.rreg r = c₀.rreg r
  nmem : c.nmem = c₀.nmem
  rmem : ∀ a, (a < eb₂ ∨ eb₂ + b ≤ a) → c.rmem a = c₀.rmem a
  out : c.output = c₀.output
  le : c.nreg 16 ≤ b
  cp : ∀ i < c.nreg 16, c.rmem (eb₂ + i) = E (π i)

/-- One step of the copy to `e₂`. -/
theorem cpToBodyO_exec (hπ : IsPermB b π) (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) {E : ℕ → ℤ}
    {c₀ : Config} (hE : Env2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π c₀) (hV : Vals b eb E c₀)
    (c : Config) (hI : ICpToO b eb₂ π W E c₀ c) (hlt : c.nreg 16 < c.nreg 1) :
    ∃ c' k', Exec P W cpToBody c c' k' ∧ ICpToO b eb₂ π W E c₀ c' ∧
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
theorem cpToO_exec (hπ : IsPermB b π) (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) {E : ℕ → ℤ}
    (c : Config) (hc : WordsBounded W c) (hE : Env2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π c)
    (hV : Vals b eb E c) (h16 : c.nreg 16 = 0) :
    ∃ c' k, Exec P W (.whileLtN 16 1 cpToBody) c c' k ∧ k ≤ 9 * b + 2 ∧
      ((∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 16 → c'.rreg r = c.rreg r) ∧ c'.nmem = c.nmem ∧
        (∀ a, (a < eb₂ ∨ eb₂ + b ≤ a) → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
        Vals b eb₂ (fun i => E (π i)) c') := by
  refine spec_while (ICpToO b eb₂ π W E c) (fun c => 9 * (b - c.nreg 16)) (fun c h => h.wb)
    (fun c' hc' hlt' => cpToBodyO_exec hπ hL hE hV c' hc' hlt')
    ⟨hc, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, by omega,
      fun i hi => absurd hi (by omega)⟩ ?_
  intro c' k hI hn hk
  rw [hI.nreg 1 (by omega) (by omega) (by omega), hE.r1] at hn
  refine ⟨by rw [h16] at hk; omega, hI.nreg, hI.rreg, hI.nmem, hI.rmem, hI.out,
    fun v hv => hI.cp v (by omega)⟩

/-- The state of the copy back `e[π i] := e₂[i]` of the values `E₂`, started from `c₀`. -/
structure ICpBackO (b eb : ℕ) (π : ℕ → ℕ) (W : ℕ) (E₂ : ℕ → ℤ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  nreg : ∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → c.nreg r = c₀.nreg r
  rreg : ∀ r, r ≠ 16 → c.rreg r = c₀.rreg r
  nmem : c.nmem = c₀.nmem
  rmem : ∀ a, (a < eb ∨ eb + b ≤ a) → c.rmem a = c₀.rmem a
  out : c.output = c₀.output
  le : c.nreg 16 ≤ b
  cp : ∀ i < c.nreg 16, c.rmem (eb + π i) = E₂ i

/-- One step of the copy back. -/
theorem cpBackBodyO_exec (hπ : IsPermB b π) (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) {E₂ : ℕ → ℤ}
    {c₀ : Config} (hE : Env2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π c₀) (hV : Vals b eb₂ E₂ c₀)
    (c : Config) (hI : ICpBackO b eb π W E₂ c₀ c) (hlt : c.nreg 16 < c.nreg 1) :
    ∃ c' k', Exec P W cpBackBody c c' k' ∧ ICpBackO b eb π W E₂ c₀ c' ∧
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
theorem cpBackO_exec (hπ : IsPermB b π) (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) {E₂ : ℕ → ℤ}
    (c : Config) (hc : WordsBounded W c) (hE : Env2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π c)
    (hV : Vals b eb₂ E₂ c) (h16 : c.nreg 16 = 0) :
    ∃ c' k, Exec P W (.whileLtN 16 1 cpBackBody) c c' k ∧ k ≤ 9 * b + 2 ∧
      ((∀ r, r ≠ 16 → r ≠ 17 → r ≠ 18 → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 16 → c'.rreg r = c.rreg r) ∧ c'.nmem = c.nmem ∧
        (∀ a, (a < eb ∨ eb + b ≤ a) → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
        ∀ i < b, c'.rmem (eb + π i) = E₂ i) := by
  refine spec_while (ICpBackO b eb π W E₂ c) (fun c => 9 * (b - c.nreg 16)) (fun c h => h.wb)
    (fun c' hc' hlt' => cpBackBodyO_exec hπ hL hE hV c' hc' hlt')
    ⟨hc, fun _ _ _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl, by omega,
      fun i hi => absurd hi (by omega)⟩ ?_
  intro c' k hI hn hk
  rw [hI.nreg 1 (by omega) (by omega) (by omega), hE.r1] at hn
  refine ⟨by rw [h16] at hk; omega, hI.nreg, hI.rreg, hI.nmem, hI.rmem, hI.out,
    fun v hv => hI.cp v (by omega)⟩

/-! ### A round -/

/-- The state between the rounds. -/
structure IK2O (b Vb₁ eb Vb₂ eb₂ πb pb : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (H₁ : ℝ)
    (X₂ : ℕ → ℕ → Prop) (D₂ : ℕ → ℕ → ℤ) (H₂ : ℝ) (π : ℕ → ℕ) (W : ℕ)
    (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  env : Env2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π c
  r14 : c.nreg 14 ≤ b + 1
  flag : c.nreg 30 ≤ 1
  vals : ∃ E, Vals b eb E c ∧ (∀ v < b, E v ≤ 0) ∧
    (HasPot2O b X₁ D₁ X₂ D₂ π → ∀ v < b,
      bfuO b X₁ D₁ X₂ D₂ π b v ≤ E v ∧ E v ≤ bfuO b X₁ D₁ X₂ D₂ π (c.nreg 14) v) ∧
    (1 ≤ c.nreg 14 → c.nreg 30 = 0 → Feas2O b X₁ D₁ X₂ D₂ π E) ∧
    (1 ≤ c.nreg 14 → c.nreg 30 = 1 → HasPot2O b X₁ D₁ X₂ D₂ π →
      ∃ v < b, bfuO b X₁ D₁ X₂ D₂ π b v < bfuO b X₁ D₁ X₂ D₂ π (c.nreg 14 - 1) v)
  out : c.output = c₀.output

/-- The cost bound of a round of the union. -/
def round2CostO (b : ℕ) : ℕ :=
  2 * ((levelCostO b + 2) * (Nat.log 2 b + 1) + 2) + 2 * (9 * b + 2) + 14

/-- **A round of the union** (one iteration of the main loop): the invariant `IK2`
advances from `k` to `k + 1` rounds within `round2CostO b` steps. -/
theorem round2O_exec (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁) (hD₂ : CrossingX b X₂ D₂)
    (hH₁ : ∀ s t, s < b → t < b → X₁ s t → (D₁ s t : ℝ) + b < H₁)
    (hH₂ : ∀ s t, s < b → t < b → X₂ s t → (D₂ s t : ℝ) + b < H₂)
    (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) {c₀ : Config} (c : Config)
    (hI : IK2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π W c₀ c) (hlt : c.nreg 14 < c.nreg 15) :
    ∃ c' k', Exec P W round2O c c' k' ∧ IK2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π W c₀ c' ∧
      (round2CostO b + 2) * (b + 1 - c'.nreg 14) + k' + 2 ≤
        (round2CostO b + 2) * (b + 1 - c.nreg 14) := by
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
  obtain ⟨E, hV, hE0, hB, -, -⟩ := hI.vals
  rw [hk] at hB
  have hK : KeepO b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π k c₀ c := ⟨hE, hk, hI.out⟩
  unfold round2O
  -- phase 1: the levels of matrix 1 on `e`
  refine spec_seq ?_
  refine spec_use (start1_exec c hc (by omega)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a30, a2, a3, a20, an, ar, anm, arm, ao⟩
  have hK₁ := hK.of hL (fun r hr h2 h3 => an r h2 h3 (by omega) (by omega)) (by rw [ar])
    (fun a _ => by rw [arm]) (fun a _ => by rw [anm]) ao
  refine spec_seq ?_
  refine spec_use (levelsO_exec (P := P) hD₁ hH₁ hl₁ (Q := HasPot2O b X₁ D₁ X₂ D₂ π)
    (lo := bfuO b X₁ D₁ X₂ D₂ π b) (hi := bfuO b X₁ D₁ X₂ D₂ π k) c₁ hw₁
    (hK₁.env.env₁ (by rw [a2, hE.r5]) (by rw [a3, hE.r6]))
    (fun v hv => by rw [arm]; exact hV v hv)
    a20 a30 hE0 (fun hP i j hi hj hij hx => (bfuO_feas hπ hP i j hi hj hij).1 hx) hB) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hF₂, _, E₁, hV₁, hR₁⟩
  have hK₂ := hK₁.ofFrm hL (by omega) hF₂
  -- the copy to `e₂`
  refine spec_seq ?_
  refine spec_use (mid_exec c₂ hw₂) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨b31, b30, b16, bn, br, bnm, brm, bo⟩
  have hK₃ := hK₂.of hL (fun r hr _ _ => bn r (by omega) (by omega) (by omega)) (by rw [br])
    (fun a _ => by rw [brm]) (fun a _ => by rw [bnm]) bo
  refine spec_seq ?_
  refine spec_use (cpToO_exec (P := P) hπ hL (E := E₁) c₃ hw₃ hK₃.env
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
  have hS₂ : HasPot2O b X₁ D₁ X₂ D₂ π → ∀ v < b,
      bfuO b X₁ D₁ X₂ D₂ π b (π v) ≤ E₁ (π v) ∧ E₁ (π v) ≤ bfuO b X₁ D₁ X₂ D₂ π k (π v) :=
    fun hP v hv =>
    ⟨((hR₁.bf hP).1 (π v) (hπ.lt v hv)).1,
      (hR₁.le _ (hπ.lt v hv)).trans ((hR₁.bf hP).1 (π v) (hπ.lt v hv)).2⟩
  refine spec_seq ?_
  refine spec_use (levelsO_exec (P := P) hD₂ hH₂ hl₂ (Q := HasPot2O b X₁ D₁ X₂ D₂ π)
    (lo := fun v => bfuO b X₁ D₁ X₂ D₂ π b (π v)) (hi := fun v => bfuO b X₁ D₁ X₂ D₂ π k (π v))
    c₅ hw₅
    (hK₅.env.env₂ (by rw [d2, hK₄.env.r7]) (by rw [d3, hK₄.env.r8]))
    (fun v hv => by rw [drm]; exact cV v hv) d20
    (by rw [dn 30 (by omega) (by omega) (by omega), cn 30 (by omega) (by omega) (by omega), b30])
    (fun v hv => hR₁.nonpos _ (hπ.lt v hv))
    (fun hP i j hi hj hij hx => (bfuO_feas hπ hP i j hi hj hij).2 hx) hS₂) ?_
  intro c₆ k₆ hk₆ hw₆ ⟨hF₆, _, E₂, hV₂, hR₂⟩
  have hK₆ := hK₅.ofFrm hL (by omega) hF₆
  -- the copy back
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₆ 16 0 (by omega)) fun hw₇ => ?_
  refine spec_seq ?_
  have hK₇ : KeepO b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π k c₀
      { c₆ with nreg := upd c₆.nreg 16 0 } :=
    hK₆.of hL (fun r hr _ _ => by config_simp; upd_tac) rfl (fun _ _ => rfl) (fun _ _ => rfl) rfl
  refine spec_use (cpBackO_exec (P := P) hπ hL (E₂ := E₂) _ hw₇ hK₇.env
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
  obtain ⟨hM1, hM2, hM3, hM4⟩ := round2O_math hπ hR₁ hR₂ hE' hfl
  have g14 : c₉.nreg 14 = k := by rw [fn 14 (by omega)]; exact hK₈.r14
  have g10 : c₉.nreg 10 = 1 := by rw [fn 10 (by omega)]; exact hK₈.env.r10
  have hE₉ := hK₈.env.of hL (c' := c₉) (fun r hr _ _ _ _ _ => fn r (by omega)) (by rw [fr])
    (fun a _ => by rw [frm]) (fun a _ => by rw [fnm])
  refine spec_instr (Exec.addN hw₉ 14 14 10 (by rw [g14, g10]; omega)) fun hw₁₀ => ?_
  refine ⟨⟨hw₁₀, hE₉.of hL (fun r hr _ _ _ _ h14 => by config_simp; rw [upd_other _ _ _ h14]) rfl
      (fun _ _ => rfl) (fun _ _ => rfl), by config_simp; rw [g14, g10]; omega,
    by config_simp; exact hM1,
    ⟨E', fun v hv => by config_simp; rw [frm]; exact hV' v hv, fun v hv => by
        obtain ⟨i, hi, rfl⟩ := hπ.surj hv; rw [hE' i hi]; exact hR₂.nonpos i hi,
      fun hP v hv => by config_simp; rw [g14, g10]; exact hM2 hP v hv,
      fun _ h0 => by config_simp at h0; exact hM3 h0,
      fun _ h1 hP => by
        config_simp at h1; config_simp; rw [g14, g10, Nat.add_sub_cancel]; exact hM4 h1 hP⟩,
    by config_simp; rw [fo]; exact hK₈.out⟩, ?_⟩
  -- the cost
  config_simp; rw [g14, g10]
  have := mul_pred_add (a := round2CostO b + 2) (x := b + 1 - k) (by omega)
  rw [show b + 1 - k - 1 = b + 1 - (k + 1) by omega] at this
  have hR : round2CostO b =
      2 * ((levelCostO b + 2) * (Nat.log 2 b + 1) + 2) + 2 * (9 * b + 2) + 14 := rfl
  generalize (levelCostO b + 2) * (Nat.log 2 b + 1) = LC at hk₂ hk₆ hR
  generalize round2CostO b = R at hR this ⊢
  omega

/-! ### The whole run -/

/-- The state of the initialization of the values. -/
structure II2O (b Vb₁ eb Vb₂ eb₂ πb pb : ℕ) (X₁ : ℕ → ℕ → Prop) (D₁ : ℕ → ℕ → ℤ) (H₁ : ℝ)
    (X₂ : ℕ → ℕ → Prop) (D₂ : ℕ → ℕ → ℤ) (H₂ : ℝ) (π : ℕ → ℕ) (W : ℕ)
    (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  env : Env2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π c
  r3 : c.nreg 3 = eb
  r12 : c.nreg 12 ≤ b
  r14 : c.nreg 14 = 0
  r30 : c.nreg 30 = 0
  zero : ∀ v < c.nreg 12, c.rmem (eb + v) = 0
  out : c.output = c₀.output

/-- One value set to `0`. -/
theorem initBody2O_exec (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) {c₀ : Config} (c : Config)
    (hI : II2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π W c₀ c) (hlt : c.nreg 12 < c.nreg 1) :
    ∃ c' k', Exec P W initBody c c' k' ∧ II2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π W c₀ c' ∧
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
def bf2CostO (b : ℕ) : ℕ := 5 * b + 12 + (round2CostO b + 2) * (b + 1)

/-- **Bellman–Ford over the union of two dense distance graphs with missing arcs, on the
machine.** For two dense distance graphs on `0, …, b - 1` with missing arcs, crossing in the
extended sense (the second in the order `π`), stored as the tables of `DDGBFOHead` at `Vb₁` and
`Vb₂` (with bounds `H₁`, `H₂` above the lengths plus `b`), `bfDDG2O` runs `b + 1` rounds of
Bellman–Ford over their union within `bf2CostO b = O(b² log b)` steps (`bf2CostO_le`). At the end
the values `E v` are at `eb + v`, and either `r30 = 0` and `E` is a feasible potential of both
matrices (on their arcs), or `r30 = 1` and there is none; if there is one, `E` is `bfuO b`. -/
theorem bfDDG2O_exec (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁) (hD₂ : CrossingX b X₂ D₂)
    (hH₁ : ∀ s t, s < b → t < b → X₁ s t → (D₁ s t : ℝ) + b < H₁)
    (hH₂ : ∀ s t, s < b → t < b → X₂ s t → (D₂ s t : ℝ) + b < H₂)
    (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) (c : Config) (hc : WordsBounded W c)
    (h1 : c.nreg 1 = b) (h2 : c.nreg 2 = Vb₁) (h3 : c.nreg 3 = eb) (h4 : c.nreg 4 = pb)
    (h7 : c.nreg 7 = Vb₂) (h8 : c.nreg 8 = eb₂) (h9 : c.nreg 9 = πb)
    (hT₁ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₁ + 2 * (s * b + t)) = tVal b X₁ D₁ H₁ s t)
    (hM₁ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₁ + 2 * (s * b + t) + 1) = tMul b X₁ s t)
    (hF₁ : ∀ s t, s < b → t < b → s ≠ t → c.nmem (Vb₁ + 2 * (s * b + t)) = finB X₁ s t)
    (hT₂ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₂ + 2 * (s * b + t)) = tVal b X₂ D₂ H₂ s t)
    (hM₂ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₂ + 2 * (s * b + t) + 1) = tMul b X₂ s t)
    (hF₂ : ∀ s t, s < b → t < b → s ≠ t → c.nmem (Vb₂ + 2 * (s * b + t)) = finB X₂ s t)
    (hπm : ∀ i < b, c.nmem (πb + i) = π i) :
    ∃ c' k, Exec P W bfDDG2O c c' k ∧ k ≤ bf2CostO b ∧
      ∃ E : ℕ → ℤ, (∀ v < b, c'.rmem (eb + v) = E v) ∧
        ((c'.nreg 30 = 0 ∧ Feas2O b X₁ D₁ X₂ D₂ π E) ∨
          (c'.nreg 30 = 1 ∧ ¬ ∃ E', Feas2O b X₁ D₁ X₂ D₂ π E')) ∧
        ((∃ E', Feas2O b X₁ D₁ X₂ D₂ π E') → ∀ v < b, E v = bfuO b X₁ D₁ X₂ D₂ π b v) ∧
        c'.output = c.output := by
  have hw := hL.w
  unfold bfDDG2O
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  · config_simp; rw [h1]; omega
  · omega
  · omega
  refine spec_seq ?_
  refine spec_while (II2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π W c)
    (fun c => 5 * (b - c.nreg 12))
    (fun c h => h.wb) (fun c' hc' hlt' => initBody2O_exec hL c' hc' hlt')
    ⟨‹_›, ⟨by config_simp; exact h1, by config_simp; exact h4, by config_simp; exact h2,
      by config_simp; exact h3, by config_simp; exact h7, by config_simp; exact h8,
      by config_simp; exact h9, by config_simp, by config_simp; rw [h1], by config_simp; simp,
      fun s t hs ht hst => by config_simp; exact hT₁ s t hs ht hst,
      fun s t hs ht hst => by config_simp; exact hM₁ s t hs ht hst,
      fun s t hs ht hst => by config_simp; exact hF₁ s t hs ht hst,
      fun s t hs ht hst => by config_simp; exact hT₂ s t hs ht hst,
      fun s t hs ht hst => by config_simp; exact hM₂ s t hs ht hst,
      fun s t hs ht hst => by config_simp; exact hF₂ s t hs ht hst,
      fun i hi => by config_simp; exact hπm i hi⟩,
      by config_simp; exact h3, by config_simp; omega, by config_simp, by config_simp,
      fun v hv => by config_simp at hv; omega, rfl⟩ ?_
  intro c₁ k₁ hI₁ hn₁ hk₁
  have h12 : c₁.nreg 12 = b := by have := hI₁.r12; rw [hI₁.env.r1] at hn₁; omega
  refine spec_while (IK2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π W c)
    (fun c => (round2CostO b + 2) * (b + 1 - c.nreg 14))
    (fun c h => h.wb) (fun c' hc' hlt' => round2O_exec hπ hD₁ hD₂ hH₁ hH₂ hL c' hc' hlt')
    ⟨hI₁.wb, hI₁.env, by rw [hI₁.r14]; omega, by rw [hI₁.r30]; omega,
      ⟨fun _ => 0, fun v hv => by rw [hI₁.zero v (by omega)]; simp, fun _ _ => le_rfl,
        fun hP v hv => ?_,
        fun h => by rw [hI₁.r14] at h; omega, fun h => by rw [hI₁.r14] at h; omega⟩,
      hI₁.out⟩ ?_
  · rw [hI₁.r14, bfuO_zero]
    exact ⟨by have := bfuO_card_le hP 0 hv; rwa [bfuO_zero] at this, le_rfl⟩
  intro c₂ k₂ hI₂ hn₂ hk₂
  have h14 : c₂.nreg 14 = b + 1 := by have := hI₂.r14; rw [hI₂.env.r15] at hn₂; omega
  obtain ⟨E, hV, -, hB, hF, hN⟩ := hI₂.vals
  rw [h14] at hB hF hN
  refine ⟨?_, E, hV, ?_, fun hP v hv => ?_, by rw [hI₂.out]⟩
  · beta_reduce at hk₁ hk₂
    config_simp at hk₁
    rw [hI₁.r14, Nat.sub_zero] at hk₂
    unfold bf2CostO
    omega
  · have hfl := hI₂.flag
    rcases Nat.lt_or_ge (c₂.nreg 30) 1 with h | h
    · exact Or.inl ⟨by omega, hF (by omega) (by omega)⟩
    · refine Or.inr ⟨by omega, fun hP => ?_⟩
      obtain ⟨v, hv, hlt⟩ := hN (by omega) (by omega) ((hasPot2O_iff hπ).2 hP)
      rw [Nat.add_sub_cancel] at hlt
      exact lt_irrefl _ hlt
  · have hP' := (hasPot2O_iff hπ).2 hP
    have := hB hP' v hv
    rw [bfuO_succ_card hP' hv] at this
    omega

/-- The cost of the whole run is `O(b² log b)`. -/
theorem bf2CostO_le (b : ℕ) : bf2CostO b ≤ 7600 * (b + 1) ^ 2 * (Nat.log 2 b + 1) := by
  unfold bf2CostO round2CostO levelCostO
  have hL : 1 ≤ Nat.log 2 b + 1 := by omega
  generalize Nat.log 2 b + 1 = L at hL ⊢
  nlinarith [Nat.mul_le_mul (le_refl (b + 1)) hL, Nat.mul_le_mul (le_refl ((b + 1) * (b + 1))) hL]

end Monge

end PlanarFlow
