module

public import PlanarFlow.Monge.Basic
public import PlanarFlow.ShortestPath.BellmanFord

/-!
# Dense distance graphs of a face: the crossing inequality and the Monge blocks

Let `0, …, b - 1` be the vertices of a face of a planar graph (a *hole* of a piece), numbered in
their cyclic order, and `D i j` the distance from `i` to `j` in the piece. Two paths whose ends
interleave on the face, from `i` to `j` and from `i'` to `j'`, meet at some vertex `x` (Jordan
curve theorem); exchanging their tails at `x` gives `D i j' + D i' j ≤ D i j + D i' j'`. With
`i < i'` and `j < j'` the ends interleave exactly when all the sources come before all the
targets or after them, which is `Crossing b D`. (`crossing_of_meet` derives it from the meeting
property and the triangle inequality; the meeting property itself is planar topology and is not
proved here.)

The dense distance graph `ddg b D` is the complete digraph on `0, …, b - 1` with lengths `D`.
Its arcs are covered by `O(log b)` levels of Monge blocks, in the dyadic form of
Fakcharoenphol and Rao:

* at level `s = 2 ^ t`, for every `q`, the *block* `[2sq, 2sq + s) × [2sq + s, 2sq + 2s)` and its
  mirror image (`InBlock`), and every arc `i → j` with `i ≠ j` lies in a block of some level
  (`dyadic_cover`);
* the matrix of a block, with the sources in decreasing order and an arbitrary function `e` of the
  source added (`blk D e r0 c1`, entry `(ρ, κ)` is `e i + D i (r0 + ρ)` for the source
  `i = c1 - 1 - κ`), is **Monge** (`isMonge_blk`). Its row minima are the minima of
  `e i + D i t` over the sources `i`, for each target `t`: one Bellman–Ford relaxation of all the
  arcs of the block.

`Cov s base` records which arcs are covered after the blocks of the levels below `s`, and those
of level `s` below `base`, have been processed (`not_cov_one_zero`, `cov_step`, `cov_level`,
`cov_all`).

The Bellman–Ford values of `ddg b D` are `bfv b D k` (indexed by `ℕ`); `pot_of_feas`,
`bfv_isPot`, `bfv_le_succ` restate `PlanarFlow.Digraph.isPot_bf_card` and
`PlanarFlow.Digraph.le_bf_succ_of_round` in this form.

## References

* J. Fakcharoenphol, S. Rao, *Planar graphs, negative weight edges, shortest paths, and near
  linear time*, J. Comput. Syst. Sci. 72 (2006), 868–889.
* P. N. Klein, S. Mozes, O. Weimann, *Shortest paths in directed planar graphs with negative
  lengths: a linear-space `O(n log² n)`-time algorithm*, ACM Trans. Algorithms 6 (2010), 30.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

section crossing

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- The crossing inequality of the distances between the vertices `0, …, b - 1` of a face, in
their cyclic order: for `i < i'` and `j < j'` with the sources and the targets separated,
`D i j' + D i' j ≤ D i j + D i' j'`. -/
def Crossing (b : ℕ) (D : ℕ → ℕ → α) : Prop :=
  ∀ i i' j j', i < i' → j < j' → i' < b → j' < b → (i' < j ∨ j' < i) →
    D i j' + D i' j ≤ D i j + D i' j'

/-- **The crossing inequality from the meeting of interleaved shortest paths.** If `δ` satisfies
the triangle inequality and, for interleaved ends, some vertex `x` lies on a shortest path from
`i` to `j` and on one from `i'` to `j'`, the distances between the vertices `v 0, …, v (b - 1)`
satisfy the crossing inequality. -/
theorem crossing_of_meet {V : Type*} (δ : V → V → α) (hδ : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (v : ℕ → V) (b : ℕ)
    (hmeet : ∀ i i' j j', i < i' → j < j' → i' < b → j' < b → (i' < j ∨ j' < i) →
      ∃ x, δ (v i) (v j) = δ (v i) x + δ x (v j) ∧ δ (v i') (v j') = δ (v i') x + δ x (v j')) :
    Crossing b (fun i j => δ (v i) (v j)) := by
  intro i i' j j' hi hj hi' hj' hsep
  obtain ⟨x, h1, h2⟩ := hmeet i i' j j' hi hj hi' hj' hsep
  show δ (v i) (v j') + δ (v i') (v j) ≤ δ (v i) (v j) + δ (v i') (v j')
  rw [h1, h2]
  calc δ (v i) (v j') + δ (v i') (v j) ≤ (δ (v i) x + δ x (v j')) + (δ (v i') x + δ x (v j)) :=
        add_le_add (hδ _ _ _) (hδ _ _ _)
    _ = δ (v i) x + δ x (v j) + (δ (v i') x + δ x (v j')) := by abel

/-- The matrix of the relaxations from the sources `c1 - 1, c1 - 2, …` (column `κ` is the source
`c1 - 1 - κ`) to the targets `r0, r0 + 1, …` (row `ρ` is the target `r0 + ρ`), for the values
`e` of the sources. -/
def blk (D : ℕ → ℕ → α) (e : ℕ → α) (r0 c1 ρ κ : ℕ) : α := e (c1 - 1 - κ) + D (c1 - 1 - κ) (r0 + ρ)

/-- **A block of separated sources and targets is Monge.** -/
theorem isMonge_blk {b : ℕ} {D : ℕ → ℕ → α} (hD : Crossing b D) (e : ℕ → α) {r0 nr c1 nc : ℕ}
    (hnc : nc ≤ c1) (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b) (hsep : r0 + nr ≤ c1 - nc ∨ c1 ≤ r0) :
    IsMonge nr nc (blk D e r0 c1) := by
  intro ρ ρ' κ κ' hρ hρ' hκ hκ'
  simp only [blk]
  have key := hD (c1 - 1 - κ') (c1 - 1 - κ) (r0 + ρ) (r0 + ρ') (by omega) (by omega) (by omega)
    (by omega) (by omega)
  calc e (c1 - 1 - κ) + D (c1 - 1 - κ) (r0 + ρ) + (e (c1 - 1 - κ') + D (c1 - 1 - κ') (r0 + ρ'))
      = (e (c1 - 1 - κ) + e (c1 - 1 - κ')) +
          (D (c1 - 1 - κ') (r0 + ρ') + D (c1 - 1 - κ) (r0 + ρ)) := by abel
    _ ≤ (e (c1 - 1 - κ) + e (c1 - 1 - κ')) +
          (D (c1 - 1 - κ') (r0 + ρ) + D (c1 - 1 - κ) (r0 + ρ')) := add_le_add le_rfl key
    _ = _ := by abel

end crossing

/-! ### The dyadic blocks -/

/-- `i` and `j` lie in the two halves of the block `[base, base + 2s)`. -/
def InBlock (s base i j : ℕ) : Prop :=
  (base ≤ i ∧ i < base + s ∧ base + s ≤ j ∧ j < base + 2 * s) ∨
    (base ≤ j ∧ j < base + s ∧ base + s ≤ i ∧ i < base + 2 * s)

lemma div_pow_succ_eq {i j t : ℕ} (h : i / 2 ^ t = j / 2 ^ t) : i / 2 ^ (t + 1) = j / 2 ^ (t + 1) := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

/-- **Every arc lies in a dyadic block.** -/
theorem dyadic_cover {i j : ℕ} (h : i ≠ j) : ∃ t q, InBlock (2 ^ t) (2 * 2 ^ t * q) i j := by
  have hex : ∃ T, i / 2 ^ T = j / 2 ^ T := by
    refine ⟨i + j, ?_⟩
    have h1 : i < 2 ^ (i + j) := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by omega) (by omega))
    have h2 : j < 2 ^ (i + j) := lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2]
  classical
  generalize hT : Nat.find hex = T
  have hP : i / 2 ^ T = j / 2 ^ T := hT ▸ Nat.find_spec hex
  have hT0 : T ≠ 0 := by
    rintro rfl; simp at hP; exact h hP
  obtain ⟨t, rfl⟩ : ∃ t, T = t + 1 := ⟨T - 1, by omega⟩
  have hnP : i / 2 ^ t ≠ j / 2 ^ t := Nat.find_min hex (by omega)
  have hs : 0 < 2 ^ t := Nat.two_pow_pos t
  generalize hsd : 2 ^ t = s at hs hnP
  have hP' : i / s / 2 = j / s / 2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← hsd, ← pow_succ]; exact hP
  generalize hu : i / s = u at hP' hnP
  generalize hw : j / s = w at hP' hnP
  have hi1 := Nat.div_add_mod i s
  have hi2 := Nat.mod_lt i hs
  have hj1 := Nat.div_add_mod j s
  have hj2 := Nat.mod_lt j hs
  rw [hu] at hi1
  rw [hw] at hj1
  refine ⟨t, u / 2, ?_⟩
  rw [hsd]
  rcases Nat.even_or_odd u with ⟨a, ha⟩ | ⟨a, ha⟩
  · have hwa : w = 2 * a + 1 := by omega
    have e1 : u / 2 = a := by omega
    rw [e1]
    have e2 : s * u = 2 * s * a := by rw [ha]; ring
    have e3 : s * w = 2 * s * a + s := by rw [hwa]; ring
    left; omega
  · have hwa : w = 2 * a := by omega
    have e1 : u / 2 = a := by omega
    rw [e1]
    have e2 : s * u = 2 * s * a + s := by rw [ha]; ring
    have e3 : s * w = 2 * s * a := by rw [hwa]; ring
    right; omega

/-- The arcs covered after the levels below `s`, and the blocks of level `s` that start below
`base`, have been processed. -/
def Cov (s base i j : ℕ) : Prop :=
  (∃ t q, 2 ^ t < s ∧ InBlock (2 ^ t) (2 * 2 ^ t * q) i j) ∨
    (∃ q, 2 * s * q < base ∧ InBlock s (2 * s * q) i j)

theorem not_cov_one_zero {i j : ℕ} : ¬ Cov 1 0 i j := by
  rintro (⟨t, q, ht, -⟩ | ⟨q, hq, -⟩)
  · have := Nat.one_le_two_pow (n := t); omega
  · omega

/-- Processing the block at `base` (a multiple of `2s`) covers its arcs. -/
theorem cov_step {s q0 i j : ℕ} (hs : 0 < s) (h : Cov s (2 * s * q0 + 2 * s) i j) :
    Cov s (2 * s * q0) i j ∨ InBlock s (2 * s * q0) i j := by
  rcases h with h | ⟨q, hq, hb⟩
  · exact Or.inl (Or.inl h)
  · have hq' : q < q0 + 1 := by
      have : 2 * s * q < 2 * s * (q0 + 1) := by rw [Nat.mul_add, Nat.mul_one]; exact hq
      exact Nat.lt_of_mul_lt_mul_left this
    rcases Nat.lt_or_ge q q0 with hlt | hge
    · exact Or.inl (Or.inr ⟨q, Nat.mul_lt_mul_of_pos_left hlt (by omega), hb⟩)
    · rw [show q = q0 by omega] at hb; exact Or.inr hb

/-- At the end of level `s` (no block of level `s` starts at `base` or later below `b`), the arcs
covered from level `2s` on are covered. -/
theorem cov_level {s t base b i j : ℕ} (hst : s = 2 ^ t) (hend : b ≤ base + s) (hi : i < b)
    (hj : j < b) (h : Cov (2 * s) 0 i j) : Cov s base i j := by
  rcases h with ⟨t', q, ht', hb⟩ | ⟨q, hq, -⟩
  · rw [hst, ← pow_succ'] at ht'
    have : t' < t + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 ht'
    rcases Nat.lt_or_ge t' t with hlt | hge
    · exact Or.inl ⟨t', q, by rw [hst]; exact Nat.pow_lt_pow_right (by norm_num) hlt, hb⟩
    · rw [show t' = t by omega, ← hst] at hb
      refine Or.inr ⟨q, ?_, hb⟩
      rcases hb with hb | hb <;> omega
  · omega

/-- At the end of the levels (`b ≤ s`), every arc is covered. -/
theorem cov_all {s base b i j : ℕ} (hb : b ≤ s) (hij : i ≠ j) (hi : i < b) (hj : j < b) :
    Cov s base i j := by
  obtain ⟨t, q, hblk⟩ := dyadic_cover hij
  refine Or.inl ⟨t, q, ?_, hblk⟩
  rcases hblk with h | h <;> omega

/-! ### The dense distance graph -/

/-- The arcs of the complete digraph on `0, …, b - 1`. -/
abbrev Arc (b : ℕ) := {p : Fin b × Fin b // p.1 ≠ p.2}

/-- The dense distance graph: the complete digraph on `0, …, b - 1` with the lengths `D`. -/
def ddg (b : ℕ) (D : ℕ → ℕ → ℤ) : Digraph (Fin b) (Arc b) where
  src a := a.1.1
  dst a := a.1.2
  len a := D a.1.1 a.1.2

/-- The Bellman–Ford values of the dense distance graph, indexed by `ℕ` (`0` outside). -/
def bfv (b : ℕ) (D : ℕ → ℕ → ℤ) (k v : ℕ) : ℤ :=
  if h : v < b then (ddg b D).bf k ⟨v, h⟩ else 0

/-- The dense distance graph has a feasible potential. -/
def HasPot (b : ℕ) (D : ℕ → ℕ → ℤ) : Prop := ∃ p, (ddg b D).IsPot p

lemma bfv_of_lt {b : ℕ} {D : ℕ → ℕ → ℤ} {k v : ℕ} (h : v < b) :
    bfv b D k v = (ddg b D).bf k ⟨v, h⟩ := by
  simp [bfv, h]

lemma bfv_zero (b : ℕ) (D : ℕ → ℕ → ℤ) (v : ℕ) : bfv b D 0 v = 0 := by
  unfold bfv; split_ifs <;> rfl

/-- A function satisfying every arc inequality is a feasible potential. -/
theorem pot_of_feas {b : ℕ} {D : ℕ → ℕ → ℤ} {E : ℕ → ℤ}
    (h : ∀ i j, i < b → j < b → i ≠ j → E j ≤ E i + D i j) :
    (ddg b D).IsPot (fun v => E v) := by
  intro a
  exact h a.1.1 a.1.2 a.1.1.2 a.1.2.2 (fun e => a.2 (Fin.ext e))

/-- With a feasible potential, `bf b` satisfies every arc inequality. -/
theorem bfv_isPot {b : ℕ} {D : ℕ → ℕ → ℤ} (hP : HasPot b D) {i j : ℕ} (hi : i < b) (hj : j < b)
    (hij : i ≠ j) : bfv b D b j ≤ bfv b D b i + D i j := by
  obtain ⟨p, hp⟩ := hP
  have := (ddg b D).isPot_bf_card hp ⟨(⟨i, hi⟩, ⟨j, hj⟩), fun e => hij (congrArg Fin.val e)⟩
  rw [Fintype.card_fin] at this
  rw [bfv_of_lt hi, bfv_of_lt hj]
  exact this

/-- With a feasible potential, `bf b` is below every `bf k`. -/
theorem bfv_card_le {b : ℕ} {D : ℕ → ℕ → ℤ} (hP : HasPot b D) (k : ℕ) {v : ℕ} (hv : v < b) :
    bfv b D b v ≤ bfv b D k v := by
  obtain ⟨p, hp⟩ := hP
  have := (ddg b D).bf_card_le k hp ⟨v, hv⟩
  rw [Fintype.card_fin] at this
  rw [bfv_of_lt hv, bfv_of_lt hv]
  exact this

/-- The end of a round: values below `bf k` satisfying every arc inequality against `bf k` are
below `bf (k + 1)`. -/
theorem bfv_le_succ {b : ℕ} {D : ℕ → ℕ → ℤ} {k : ℕ} {E : ℕ → ℤ} (h1 : ∀ v < b, E v ≤ bfv b D k v)
    (h2 : ∀ i j, i < b → j < b → i ≠ j → E j ≤ bfv b D k i + D i j) {v : ℕ} (hv : v < b) :
    E v ≤ bfv b D (k + 1) v := by
  rw [bfv_of_lt hv]
  refine (ddg b D).le_bf_succ_of_round (E := fun w => E w) (fun w => ?_) (fun a => ?_) ⟨v, hv⟩
  · have := h1 w w.2; rw [bfv_of_lt w.2] at this; exact this
  · have := h2 a.1.1 a.1.2 a.1.1.2 a.1.2.2 (fun e => a.2 (Fin.ext e))
    rw [bfv_of_lt a.1.1.2] at this
    exact this

end Monge

end PlanarFlow
