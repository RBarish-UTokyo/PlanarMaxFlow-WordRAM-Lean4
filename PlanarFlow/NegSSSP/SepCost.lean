module

public import PlanarFlow.NegSSSP.SimpleRot
public import PlanarFlow.NegSSSP.Cost

/-!
# The cost of the recursion on the decomposition of a separator tree: `O(n log² n)`

Let `N` be a plane map with transitive rotations and faces and `n` darts, and `t` a separator
tree of its simple graph meeting `GoodTree` (separators and boundaries of at most `T √m` vertices
at every subtree with `m` vertices, `T = 50000`, parts of at most two thirds of the vertices;
such trees exist, `PlanarFlow.NegSSSP.exists_goodTree`). The decomposition `conv N t`
(`PlanarFlow/NegSSSP/Simple.lean`) has at every node of `t`, with vertices `U` (`u = |U|`),
separator `s` and parts `a` and `b`, two nodes of the recursion:

* the darts of `a` with the darts `extra` (an end in `s`, none in the parts), and then these with
  the darts of `b`. Both share only vertices of `s` or of the boundary of `U` (`bdry_left_subset`,
  `bdry_right_subset`): at most `2 T √u` vertices, since no edge joins `a` and `b`; so each of
  the two nodes costs `O((m + T² u) lg n)` (`node_le_lg`), with `u ≤ m` for the `m` darts with
  an end in `U`;
* the leaf `extra`, of at most `12 · 2 T √u` darts (`card_wset_le`: the simple graph of a plane
  map is sparse), and the leaves of `t`, of at most `24 T √u` darts, cost
  `K (24 T)² u` each by Bellman–Ford.

Siblings in `t` have disjoint darts, and a branch of `t` through nonempty parts has at most
`2 log₂ n + 1` nodes (`ndepth_le`, the parts having at most two thirds of the vertices). Hence
`negCost_negDec`: **the cost of the recursion is at most `C₁ K n lg² n + C₂ K n`**, with
`C₁ = 160 (1 + 9 T²) + 1152 T²` and `C₂ = 576 T²`, for every family of subroutine costs meeting
`NegCosts.Bounds K`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW CombMap NestedDissection NestedDissection.SepTree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {N : CombMap D V F}

/-! ### Arithmetic -/

lemma sq_le_of_le_sqrt {x u : ℕ} (h : (x : ℝ) ≤ 50000 * √(u : ℝ)) :
    x ^ 2 ≤ 50000 ^ 2 * u := by
  have h0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have := pow_le_pow_left₀ h0 h 2
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] at this
  exact_mod_cast this

lemma sum_sq_le {x y z : ℕ} (hx : x ^ 2 ≤ 50000 ^ 2 * z) (hy : y ^ 2 ≤ 50000 ^ 2 * z) :
    (12 * (x + y)) ^ 2 ≤ 576 * 50000 ^ 2 * z := by
  nlinarith [sq_nonneg ((x : ℤ) - y)]

lemma succ_sq_le {x y z : ℕ} (hz : 1 ≤ z) (hx : x ^ 2 ≤ 50000 ^ 2 * z)
    (hy : y ^ 2 ≤ 50000 ^ 2 * z) : (x + y + 1) ^ 2 ≤ 9 * 50000 ^ 2 * z := by
  nlinarith [sq_nonneg ((x : ℤ) - y), sq_nonneg ((x : ℤ) - 1), sq_nonneg ((y : ℤ) - 1)]

/-! ### The cost of a node -/

namespace NegCosts

variable {c : NegCosts} {K : ℕ}

/-- **A node costs `O((m + b²) lg n)`.** -/
theorem node_le_lg (hc : c.Bounds K) {n m b m₀ w₀ m₁ w₁ : ℕ} (hn : 1 ≤ n) (h₀ : m₀ ≤ m)
    (h₁ : m₁ ≤ m) (hm : m ≤ n) (hw₀ : w₀ ≤ 2 * m₀) (hw₁ : w₁ ≤ 2 * m₁) (hb : b ≤ 2 * n) :
    c.node m b m₀ w₀ m₁ w₁ ≤ 40 * K * lg n * (m + (b + 1) ^ 2) := by
  have hl1 := one_le_lg n
  have hl3 : lg (3 * n) ≤ 3 * lg n := lg_three_mul n
  have hlm₀ : lg m₀ ≤ lg n := lg_mono (h₀.trans hm)
  have hlm₁ : lg m₁ ≤ lg n := lg_mono (h₁.trans hm)
  have hlb : lg b ≤ 3 * lg n := (lg_mono (by omega : b ≤ 3 * n)).trans hl3
  have hlw₀ : lg (w₀ + 1) ≤ 3 * lg n := (lg_mono (by omega : w₀ + 1 ≤ 3 * n)).trans hl3
  have hlw₁ : lg (w₁ + 1) ≤ 3 * lg n := (lg_mono (by omega : w₁ + 1 ≤ 3 * n)).trans hl3
  have e1 : c.sep m ≤ K * lg n * m :=
    (hc.sep m).trans (by
      rw [mul_right_comm]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (lg_mono hm)))
  have e2 := hc.lin m
  have e3 : c.mssp m₀ b ≤ K * lg n * (m + b ^ 2) :=
    calc c.mssp m₀ b ≤ K * (m₀ * lg m₀ + b ^ 2 * lg m₀) := hc.mssp m₀ b
      _ ≤ K * (m * lg n + b ^ 2 * lg n) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul h₀ hlm₀)
            (Nat.mul_le_mul_left _ hlm₀))
      _ = K * lg n * (m + b ^ 2) := by ring
  have e4 : c.mssp m₁ b ≤ K * lg n * (m + b ^ 2) :=
    calc c.mssp m₁ b ≤ K * (m₁ * lg m₁ + b ^ 2 * lg m₁) := hc.mssp m₁ b
      _ ≤ K * (m * lg n + b ^ 2 * lg n) :=
          Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul h₁ hlm₁)
            (Nat.mul_le_mul_left _ hlm₁))
      _ = K * lg n * (m + b ^ 2) := by ring
  have e5 : c.bf b ≤ K * lg n * (3 * (b + 1) ^ 2) :=
    calc c.bf b ≤ K * (b + 1) ^ 2 * lg b := hc.bf b
      _ ≤ K * (b + 1) ^ 2 * (3 * lg n) := Nat.mul_le_mul_left _ hlb
      _ = K * lg n * (3 * (b + 1) ^ 2) := by ring
  have e6 : c.dij (w₀ + 1) (m₀ + w₀) ≤ K * lg n * (3 * (5 * m + 1)) :=
    calc c.dij (w₀ + 1) (m₀ + w₀) ≤ K * (w₀ + 1 + (m₀ + w₀)) * lg (w₀ + 1) := hc.dij _ _
      _ ≤ K * (5 * m + 1) * (3 * lg n) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hlw₀
      _ = K * lg n * (3 * (5 * m + 1)) := by ring
  have e7 : c.dij (w₁ + 1) (m₁ + w₁) ≤ K * lg n * (3 * (5 * m + 1)) :=
    calc c.dij (w₁ + 1) (m₁ + w₁) ≤ K * (w₁ + 1 + (m₁ + w₁)) * lg (w₁ + 1) := hc.dij _ _
      _ ≤ K * (5 * m + 1) * (3 * lg n) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hlw₁
      _ = K * lg n * (3 * (5 * m + 1)) := by ring
  have e0 : K * m ≤ K * lg n * m := by
    rw [mul_comm K (lg n), mul_assoc]; exact Nat.le_mul_of_pos_left _ hl1
  unfold node
  have hb2 : b ^ 2 ≤ (b + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h1 : 1 ≤ (b + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have key : K * lg n * m + K * lg n * m + K * lg n * (m + b ^ 2) + K * lg n * (m + b ^ 2) +
      K * lg n * (3 * (b + 1) ^ 2) + K * lg n * (3 * (5 * m + 1)) +
      K * lg n * (3 * (5 * m + 1)) ≤ 40 * K * lg n * (m + (b + 1) ^ 2) := by
    have : m + m + (m + b ^ 2) + (m + b ^ 2) + 3 * (b + 1) ^ 2 + 3 * (5 * m + 1) +
        3 * (5 * m + 1) ≤ 40 * (m + (b + 1) ^ 2) := by omega
    calc _ = K * lg n * (m + m + (m + b ^ 2) + (m + b ^ 2) + 3 * (b + 1) ^ 2 +
          3 * (5 * m + 1) + 3 * (5 * m + 1)) := by ring
      _ ≤ K * lg n * (40 * (m + (b + 1) ^ 2)) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  omega

end NegCosts

/-! ### The cost of a node with the empty pieces left out -/

lemma negCost_mk (c : NegCosts) (l r : NTree D) {X : ℕ}
    (h : l.piece.Nonempty → r.piece.Nonempty →
      c.node (l.piece ∪ r.piece).card (bdry N l.piece r.piece).card l.piece.card
        (verts N l.piece).card r.piece.card (verts N r.piece).card ≤ X) :
    negCost N c (NTree.mk l r) ≤ negCost N c l + negCost N c r + X := by
  unfold NTree.mk
  split_ifs with h1 h2
  · omega
  · omega
  · simp only [negCost]
    have := h (nonempty_iff_ne_empty.2 h1) (nonempty_iff_ne_empty.2 h2)
    omega

lemma negCost_leaf_empty {c : NegCosts} {K : ℕ} (hc : c.Bounds K) :
    negCost N c (.leaf ∅) = 0 := by
  have := hc.leaf 0
  simp only [negCost, card_empty] at this ⊢
  omega

lemma eset_empty : eset N (∅ : Finset V) = ∅ :=
  subset_empty.1 fun d hd => by
    obtain ⟨-, h | h⟩ := mem_eset.1 hd
    · exact absurd h (notMem_empty _)
    · exact absurd h (notMem_empty _)

/-- A subtree with no kept darts is the empty leaf. -/
lemma conv_empty : ∀ t : SepTree V, eset N t.verts = ∅ → conv N t = .leaf ∅
  | .leaf s, h => by simp only [conv, SepTree.verts] at h ⊢; rw [h]
  | .node s a b, h => by
    simp only [SepTree.verts] at h
    have ha : eset N a.verts = ∅ := subset_empty.1 (h ▸ eset_mono fun x hx =>
      mem_union_left _ (mem_union_right _ hx))
    have hb : eset N b.verts = ∅ := subset_empty.1 (h ▸ eset_mono subset_union_right)
    have he : extra N (s ∪ a.verts ∪ b.verts) a.verts b.verts = ∅ := by
      rw [extra, h, empty_sdiff]
    simp only [conv, conv_empty a ha, conv_empty b hb, he, NTree.mk, NTree.piece, ite_true]

/-! ### The vertices shared by the pieces -/

section Shared

variable {s A B U : Finset V}

lemma verts_subset_of_wset {P : Finset D} {W : Finset V} (h : P ⊆ wset N W) :
    verts N P ⊆ W := by
  intro v hv
  rcases mem_union.1 hv with hv | hv <;> obtain ⟨d, hd, rfl⟩ := mem_image.1 hv
  · exact (mem_wset.1 (h hd)).2.1
  · exact (mem_wset.1 (h hd)).2.2

lemma mem_verts_iff {P : Finset D} {v : V} :
    v ∈ verts N P ↔ ∃ d ∈ P, N.tail d = v ∨ N.head d = v := by
  unfold verts
  simp only [mem_union, mem_image]
  constructor
  · rintro (⟨d, hd, e⟩ | ⟨d, hd, e⟩)
    · exact ⟨d, hd, Or.inl e⟩
    · exact ⟨d, hd, Or.inr e⟩
  · rintro ⟨d, hd, e | e⟩
    · exact Or.inl ⟨d, hd, e⟩
    · exact Or.inr ⟨d, hd, e⟩

lemma mem_bdry_sg {W : Finset V} {y : V} :
    y ∈ NestedDissection.bdry (sgraph N) W ↔ y ∉ W ∧ ∃ x ∈ W, (sgraph N).Adj x y := by
  simp [NestedDissection.bdry]

/-- The darts `extra` have their ends in the separator and the boundary. -/
lemma extra_subset (hU : U = s ∪ A ∪ B) :
    extra N U A B ⊆ wset N (s ∪ NestedDissection.bdry (sgraph N) U) := by
  intro d hd
  obtain ⟨hdU, hdAB⟩ := mem_sdiff.1 hd
  have hw := mem_wset.1 (eset_subset_wset U hdU)
  have hnA : N.tail d ∉ A ∧ N.head d ∉ A := by
    refine ⟨fun h => hdAB (mem_union_left _ (mem_eset.2 ⟨hw.1, Or.inl h⟩)),
      fun h => hdAB (mem_union_left _ (mem_eset.2 ⟨hw.1, Or.inr h⟩))⟩
  have hnB : N.tail d ∉ B ∧ N.head d ∉ B := by
    refine ⟨fun h => hdAB (mem_union_right _ (mem_eset.2 ⟨hw.1, Or.inl h⟩)),
      fun h => hdAB (mem_union_right _ (mem_eset.2 ⟨hw.1, Or.inr h⟩))⟩
  have key : ∀ v, v ∈ U ∪ NestedDissection.bdry (sgraph N) U → v ∉ A → v ∉ B →
      v ∈ s ∪ NestedDissection.bdry (sgraph N) U := by
    intro v hv hvA hvB
    rcases mem_union.1 hv with hv | hv
    · rw [hU] at hv
      simp only [mem_union] at hv
      rcases hv with (hv | hv) | hv
      · exact mem_union_left _ hv
      · exact absurd hv hvA
      · exact absurd hv hvB
    · exact mem_union_right _ hv
  exact mem_wset.2 ⟨hw.1, key _ hw.2.1 hnA.1 hnB.1, key _ hw.2.2 hnA.2 hnB.2⟩

/-- The pieces `a` and `extra` share vertices of the separator and the boundary only. -/
lemma bdry_left_subset (hU : U = s ∪ A ∪ B) :
    bdry N (eset N A) (extra N U A B) ⊆ s ∪ NestedDissection.bdry (sgraph N) U :=
  inter_subset_right.trans (verts_subset_of_wset (extra_subset hU))

/-- The pieces `a ∪ extra` and `b` share vertices of the separator and the boundary only. -/
lemma bdry_right_subset (hU : U = s ∪ A ∪ B) (hAB : Disjoint A B)
    (hadj : ∀ x ∈ A, ∀ y ∈ B, ¬ (sgraph N).Adj x y) :
    bdry N (eset N A ∪ extra N U A B) (eset N B) ⊆ s ∪ NestedDissection.bdry (sgraph N) U := by
  intro v hv
  obtain ⟨hv1, hv2⟩ := mem_inter.1 hv
  have hvB := verts_subset_of_wset (eset_subset_wset B) hv2
  have hadj' : ∀ x ∈ A, ∀ y ∈ B, ¬ (sgraph N).Adj y x := fun x hx y hy h =>
    hadj x hx y hy h.symm
  rcases mem_union.1 hvB with hb | hb
  · exfalso
    obtain ⟨d, hd, e⟩ := mem_verts_iff.1 hv1
    rcases mem_union.1 hd with hd | hd
    · obtain ⟨hr, ht | hh⟩ := mem_eset.1 hd
      · rcases e with e | e
        · exact disjoint_left.1 hAB ht (e ▸ hb)
        · exact hadj _ ht _ (e ▸ hb) ⟨d, hr, rfl, rfl⟩
      · rcases e with e | e
        · exact hadj' _ hh _ (e ▸ hb) ⟨d, hr, rfl, rfl⟩
        · exact disjoint_left.1 hAB hh (e ▸ hb)
    · have hn := (mem_sdiff.1 hd).2
      have hr := (mem_eset.1 (mem_sdiff.1 hd).1).1
      rcases e with e | e
      · exact hn (mem_union_right _ (mem_eset.2 ⟨hr, Or.inl (e ▸ hb)⟩))
      · exact hn (mem_union_right _ (mem_eset.2 ⟨hr, Or.inr (e ▸ hb)⟩))
  · obtain ⟨hvB', x, hx, hxv⟩ := mem_bdry_sg.1 hb
    have hvA : v ∉ A := fun h => hadj' _ h _ hx hxv
    by_cases hvU : v ∈ U
    · rw [hU] at hvU
      simp only [mem_union] at hvU
      rcases hvU with (h | h) | h
      · exact mem_union_left _ h
      · exact absurd h hvA
      · exact absurd h hvB'
    · exact mem_union_right _ (mem_bdry_sg.2 ⟨hvU, x, by rw [hU]; exact mem_union_right _ hx,
        hxv⟩)

end Shared

/-! ### Depth -/

/-- **The depth of a separator tree through nonempty parts.** -/
def ndepth : SepTree V → ℕ
  | .leaf _ => 0
  | .node _ a b => if a.verts = ∅ ∧ b.verts = ∅ then 0 else
      max (if a.verts = ∅ then 0 else ndepth a) (if b.verts = ∅ then 0 else ndepth b) + 1

lemma pow_ndepth : ∀ {t : SepTree V}, AllNodes Shrinks t → t.verts.Nonempty →
    3 ^ ndepth t ≤ 2 ^ ndepth t * t.verts.card
  | .leaf _, _, h => by simp only [ndepth, pow_zero, one_mul]; exact card_pos.2 h
  | .node s a b, hs, hne => by
    obtain ⟨⟨sa, sb⟩, ha, hb⟩ := hs
    have hU : (node s a b).verts = s ∪ a.verts ∪ b.verts := rfl
    have ia : a.verts ≠ ∅ → 3 ^ ndepth a ≤ 2 ^ ndepth a * a.verts.card :=
      fun h => pow_ndepth ha (nonempty_iff_ne_empty.2 h)
    have ib : b.verts ≠ ∅ → 3 ^ ndepth b ≤ 2 ^ ndepth b * b.verts.card :=
      fun h => pow_ndepth hb (nonempty_iff_ne_empty.2 h)
    rw [hU] at sa sb hne
    simp only [ndepth]
    by_cases h0 : a.verts = ∅ ∧ b.verts = ∅
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]; simp only [pow_zero, one_mul]; rw [hU]
      exact card_pos.2 hne
    rw [ite_eq_right_of_eq_false _ _ (eq_false h0), hU]
    -- each child gives the bound
    have step : ∀ (c : SepTree V), (c.verts ≠ ∅ → 3 ^ ndepth c ≤ 2 ^ ndepth c * c.verts.card) →
        3 * c.verts.card ≤
        2 * (s ∪ a.verts ∪ b.verts).card →
        3 ^ ((if c.verts = ∅ then 0 else ndepth c) + 1) ≤
          2 ^ ((if c.verts = ∅ then 0 else ndepth c) + 1) * (s ∪ a.verts ∪ b.verts).card := by
      intro c hc h3
      split_ifs with hce
      · simp only [zero_add, pow_one]
        -- the other child is nonempty
        have : 1 ≤ a.verts.card ∨ 1 ≤ b.verts.card := by
          by_contra hcon
          push Not at hcon
          exact h0 ⟨card_eq_zero.1 (by omega), card_eq_zero.1 (by omega)⟩
        omega
      · have ih := hc hce
        rw [pow_succ, pow_succ]
        nlinarith [Nat.zero_le (2 ^ ndepth c)]
    rcases le_total (if a.verts = ∅ then 0 else ndepth a)
      (if b.verts = ∅ then 0 else ndepth b) with hle | hle
    · rw [max_eq_right hle]; exact step b ib sb
    · rw [max_eq_left hle]; exact step a ia sa

/-- A branch through nonempty parts has at most `2 log₂ m + 1` nodes. -/
lemma ndepth_le {t : SepTree V} (hs : AllNodes Shrinks t) (hne : t.verts.Nonempty) :
    ndepth t ≤ 2 * Nat.log 2 t.verts.card + 1 := by
  have h1 := pow_ndepth hs hne
  have h2 := ADec.two_pow_mul_two_pow_half_le (ndepth t)
  have h3 : 2 ^ (ndepth t / 2) ≤ t.verts.card :=
    Nat.le_of_mul_le_mul_left (h2.trans h1) (by positivity)
  have := Nat.le_log_of_pow_le (by norm_num) h3
  omega

/-! ### The cost of the decomposition of a separator tree -/

lemma card_le_eset (htouch : ∀ v, ∃ d ∈ reps N, N.tail d = v) (U : Finset V) :
    U.card ≤ (eset N U).card := by
  choose f hf1 hf2 using htouch
  refine card_le_card_of_injOn f (fun v hv => ?_) (fun v _ w _ e => ?_)
  · exact mem_eset.2 ⟨hf1 v, Or.inl (by rw [hf2]; exact hv)⟩
  · rw [← hf2 v, ← hf2 w, e]

lemma card_eset_le_reps (U : Finset V) : (eset N U).card ≤ (reps N).card :=
  card_le_card (filter_subset _ _)

variable {c : NegCosts} {K : ℕ}

/-- **The cost per level**: at most `A m d + L m` for the `m` darts with an end in the vertices of
`t` and `d = ndepth t`, with `A = 80 K lg n (1 + 9 T²) + 576 T² K` and `L = 576 T² K`. -/
theorem negCost_conv (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (htouch : ∀ v, ∃ d ∈ reps N, N.tail d = v) (hc : c.Bounds K) :
    ∀ {t : SepTree V}, IsDissection (sgraph N) t → AllNodes (SqrtBound (sgraph N) 50000 50000) t →
      AllNodes Shrinks t →
      negCost N c (conv N t) ≤
        (80 * K * lg (Fintype.card D) * (1 + 9 * 50000 ^ 2) + 576 * 50000 ^ 2 * K) *
            (eset N t.verts).card * ndepth t +
          576 * 50000 ^ 2 * K * (eset N t.verts).card
  | .leaf s, _, hq, _ => by
    obtain ⟨h1, h2⟩ := hq
    have e1 := sq_le_of_le_sqrt h1
    have e2 := sq_le_of_le_sqrt h2
    simp only [own, SepTree.verts] at e1 e2
    simp only [conv, negCost, SepTree.verts, ndepth, mul_zero, zero_add]
    have hw := (card_le_card (eset_subset_wset (N := N) s)).trans
      (card_wset_le hM hrot hface _)
    have hw' : (eset N s).card ≤ 12 * (s.card + (NestedDissection.bdry (sgraph N) s).card) :=
      hw.trans (Nat.mul_le_mul_left _ (card_union_le _ _))
    have hsq : (eset N s).card ^ 2 ≤ 576 * 50000 ^ 2 * s.card :=
      (Nat.pow_le_pow_left hw' 2).trans (sum_sq_le e1 e2)
    have hle := card_le_eset htouch s
    calc c.leaf (eset N s).card ≤ K * (eset N s).card ^ 2 := hc.leaf _
      _ ≤ K * (576 * 50000 ^ 2 * s.card) := Nat.mul_le_mul_left _ hsq
      _ ≤ K * (576 * 50000 ^ 2 * (eset N s).card) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)
      _ = _ := by ring
  | .node s a b, hd, hq, hs => by
    obtain ⟨hsa, hsb, hab, hadj, hda, hdb⟩ := hd
    obtain ⟨⟨h1, h2⟩, hqa, hqb⟩ := hq
    obtain ⟨-, hsa', hsb'⟩ := hs
    set U := s ∪ a.verts ∪ b.verts with hU
    have hUv : (node s a b).verts = U := rfl
    simp only [own, hUv] at h1 h2
    have e1 := sq_le_of_le_sqrt h1
    have e2 := sq_le_of_le_sqrt h2
    rw [hUv]
    set n := Fintype.card D
    set A := 80 * K * lg n * (1 + 9 * 50000 ^ 2) + 576 * 50000 ^ 2 * K
    set L := 576 * 50000 ^ 2 * K
    -- the empty case
    by_cases hE : eset N U = ∅
    · have := conv_empty (N := N) (node s a b) (by rw [hUv]; exact hE)
      rw [this, negCost_leaf_empty hc]; exact Nat.zero_le _
    have hu : 1 ≤ U.card := by
      obtain ⟨d, hd⟩ := nonempty_iff_ne_empty.2 hE
      obtain ⟨-, h | h⟩ := mem_eset.1 hd
      · exact card_pos.2 ⟨_, h⟩
      · exact card_pos.2 ⟨_, h⟩
    have huE := card_le_eset htouch U
    -- the darts and the bounds
    set Ea := eset N a.verts
    set Eb := eset N b.verts
    set X := extra N U a.verts b.verts
    have hEaU : Ea ⊆ eset N U := eset_mono fun x hx => mem_union_left _ (mem_union_right _ hx)
    have hEbU : Eb ⊆ eset N U := eset_mono subset_union_right
    have hXU : X ⊆ eset N U := sdiff_subset
    have hdisj : Disjoint Ea Eb := by
      refine disjoint_left.2 fun d hda' hdb' => ?_
      obtain ⟨hr, ha1 | ha1⟩ := mem_eset.1 hda' <;> obtain ⟨-, hb1 | hb1⟩ := mem_eset.1 hdb'
      · exact disjoint_left.1 hab ha1 hb1
      · exact hadj _ ha1 _ hb1 ⟨d, hr, rfl, rfl⟩
      · exact hadj _ ha1 _ hb1 ⟨N.rev d, reps_rev hr, by simp, by simp⟩
      · exact disjoint_left.1 hab ha1 hb1
    have hdX : Disjoint (Ea ∪ X) Eb := by
      refine disjoint_union_left.2 ⟨hdisj, disjoint_left.2 fun d hx hb' => ?_⟩
      exact (mem_sdiff.1 hx).2 (mem_union_right _ hb')
    have hcardU : (Ea ∪ X ∪ Eb).card = (eset N U).card := by
      congr 1
      ext d
      simp only [mem_union]
      constructor
      · rintro ((h | h) | h)
        · exact hEaU h
        · exact hXU h
        · exact hEbU h
      · intro h
        by_cases h1 : d ∈ Ea
        · exact Or.inl (Or.inl h1)
        by_cases h2 : d ∈ Eb
        · exact Or.inr h2
        · exact Or.inl (Or.inr (mem_sdiff.2 ⟨h, by rw [mem_union]; exact fun h' => h'.elim h1 h2⟩))
    have hcard3 : Ea.card + X.card + Eb.card = (eset N U).card := by
      have hdEX : Disjoint Ea X :=
        disjoint_left.2 fun d h1 h2 => (mem_sdiff.1 h2).2 (mem_union_left _ h1)
      rw [← hcardU, card_union_of_disjoint hdX, card_union_of_disjoint hdEX]
    have hEn : (eset N U).card ≤ n := (card_eset_le_reps U).trans (card_le_univ _)
    have hn : 1 ≤ n := hu.trans (huE.trans hEn)
    -- the bound on a node
    have hnode : ∀ P Q : Finset D, P ∪ Q ⊆ eset N U →
        bdry N P Q ⊆ s ∪ NestedDissection.bdry (sgraph N) U →
        c.node (P ∪ Q).card (bdry N P Q).card P.card (verts N P).card Q.card
          (verts N Q).card ≤ 40 * K * lg n * (1 + 9 * 50000 ^ 2) * (eset N U).card := by
      intro P Q hPQ hb
      have hm := card_le_card hPQ
      have hbc : (bdry N P Q).card ≤ s.card + (NestedDissection.bdry (sgraph N) U).card :=
        (card_le_card hb).trans (card_union_le _ _)
      have hb2 : ((bdry N P Q).card + 1) ^ 2 ≤ 9 * 50000 ^ 2 * U.card :=
        (Nat.pow_le_pow_left (by omega) 2).trans (succ_sq_le hu e1 e2)
      have hbn : (bdry N P Q).card ≤ 2 * n := by
        have := card_le_card (inter_subset_left (s₁ := verts N P) (s₂ := verts N Q))
        have := NTree.card_verts_le (N := N) P
        have := card_le_card (subset_union_left (s₁ := P) (s₂ := Q))
        unfold bdry; omega
      refine (NegCosts.node_le_lg hc hn (card_le_card subset_union_left)
        (card_le_card subset_union_right) (hm.trans hEn) (NTree.card_verts_le P)
        (NTree.card_verts_le Q) hbn).trans ?_
      calc 40 * K * lg n * ((P ∪ Q).card + ((bdry N P Q).card + 1) ^ 2)
          ≤ 40 * K * lg n * ((eset N U).card + 9 * 50000 ^ 2 * (eset N U).card) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add hm (hb2.trans (Nat.mul_le_mul_left _ huE)))
        _ = _ := by ring
    -- the leaf `extra`
    have hX : c.leaf X.card ≤ L * (eset N U).card := by
      have hw := (card_le_card (extra_subset (N := N) hU)).trans (card_wset_le hM hrot hface _)
      have hw' : X.card ≤ 12 * (s.card + (NestedDissection.bdry (sgraph N) U).card) :=
        hw.trans (Nat.mul_le_mul_left _ (card_union_le _ _))
      have hsq : X.card ^ 2 ≤ 576 * 50000 ^ 2 * U.card :=
        (Nat.pow_le_pow_left hw' 2).trans (sum_sq_le e1 e2)
      calc c.leaf X.card ≤ K * X.card ^ 2 := hc.leaf _
        _ ≤ K * (576 * 50000 ^ 2 * U.card) := Nat.mul_le_mul_left _ hsq
        _ ≤ K * (576 * 50000 ^ 2 * (eset N U).card) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ huE)
        _ = _ := by ring
    -- the cost of the node of `t`
    have hcost : negCost N c (conv N (node s a b)) ≤ negCost N c (conv N a) +
        negCost N c (conv N b) + L * (eset N U).card +
          2 * (40 * K * lg n * (1 + 9 * 50000 ^ 2) * (eset N U).card) := by
      show negCost N c (NTree.mk (NTree.mk (conv N a) (.leaf X)) (conv N b)) ≤ _
      have k1 := negCost_mk (N := N) c (conv N a) (.leaf X)
        (X := 40 * K * lg n * (1 + 9 * 50000 ^ 2) * (eset N U).card) fun _ _ => by
          rw [piece_conv]
          exact hnode _ _ (union_subset hEaU hXU) (bdry_left_subset hU)
      have k2 := negCost_mk (N := N) c (NTree.mk (conv N a) (.leaf X)) (conv N b)
        (X := 40 * K * lg n * (1 + 9 * 50000 ^ 2) * (eset N U).card) fun _ _ => by
          rw [NTree.piece_mk, piece_conv, piece_conv]
          exact hnode _ _ (union_subset (union_subset hEaU hXU) hEbU)
            (bdry_right_subset hU hab hadj)
      simp only [negCost] at k1
      have := hX
      omega
    -- the children
    have ia : negCost N c (conv N a) ≤ A * Ea.card * (if a.verts = ∅ then 0 else ndepth a) +
        L * Ea.card := by
      by_cases hx : a.verts = ∅
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hx), conv_empty a (by rw [hx]; exact eset_empty),
          negCost_leaf_empty hc]
        exact Nat.zero_le _
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
        exact negCost_conv hM hrot hface htouch hc hda hqa hsa'
    have ib : negCost N c (conv N b) ≤ A * Eb.card * (if b.verts = ∅ then 0 else ndepth b) +
        L * Eb.card := by
      by_cases hx : b.verts = ∅
      · rw [ite_eq_left_of_eq_true _ _ (eq_true hx), conv_empty b (by rw [hx]; exact eset_empty),
          negCost_leaf_empty hc]
        exact Nat.zero_le _
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hx)]
        exact negCost_conv hM hrot hface htouch hc hdb hqb hsb'
    show _ ≤ A * (eset N U).card * ndepth (node s a b) + L * (eset N U).card
    by_cases h0 : a.verts = ∅ ∧ b.verts = ∅
    · -- both parts empty: the node is the leaf `extra`
      obtain ⟨ha0, hb0⟩ := h0
      have hEa0 : Ea = ∅ := by show eset N a.verts = ∅; rw [ha0]; exact eset_empty
      have hEb0 : Eb = ∅ := by show eset N b.verts = ∅; rw [hb0]; exact eset_empty
      have hXE : X.card = (eset N U).card := by rw [← hcard3, hEa0, hEb0]; simp
      have hca : conv N a = .leaf ∅ := conv_empty a hEa0
      have hcb : conv N b = .leaf ∅ := conv_empty b hEb0
      have hnd : ndepth (node s a b) = 0 := by
        simp only [ndepth]; exact ite_eq_left_of_eq_true _ _ (eq_true ⟨ha0, hb0⟩)
      rw [hnd, mul_zero, zero_add]
      show negCost N c (NTree.mk (NTree.mk (conv N a) (.leaf X)) (conv N b)) ≤ _
      rw [hca, hcb]
      have k1 := negCost_mk (N := N) c (.leaf ∅) (.leaf X) (X := 0) fun h _ => by
        simp [NTree.piece] at h
      have k2 := negCost_mk (N := N) c (NTree.mk (.leaf ∅) (.leaf X)) (.leaf ∅) (X := 0)
        fun _ h => by simp [NTree.piece] at h
      rw [negCost_leaf_empty hc] at k1 k2
      simp only [negCost] at k1
      have := hX
      omega
    · have hnd : ndepth (node s a b) = max (if a.verts = ∅ then 0 else ndepth a)
          (if b.verts = ∅ then 0 else ndepth b) + 1 := by
        simp only [ndepth]; exact ite_eq_right_of_eq_false _ _ (eq_false h0)
      rw [hnd]
      set da := if a.verts = ∅ then 0 else ndepth a
      set db := if b.verts = ∅ then 0 else ndepth b
      set d := max da db + 1
      have hda : da ≤ d - 1 := by omega
      have hdb : db ≤ d - 1 := by omega
      have ia' : negCost N c (conv N a) ≤ A * Ea.card * (d - 1) + L * Ea.card :=
        ia.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hda) _)
      have ib' : negCost N c (conv N b) ≤ A * Eb.card * (d - 1) + L * Eb.card :=
        ib.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hdb) _)
      have hd1 : 1 ≤ d := by omega
      have hsum : A * Ea.card * (d - 1) + A * Eb.card * (d - 1) + A * (eset N U).card ≤
          A * (eset N U).card * d := by
        have : Ea.card + Eb.card ≤ (eset N U).card := by omega
        have h' : (Ea.card + Eb.card) * (d - 1) + (eset N U).card ≤ (eset N U).card * d := by
          have := Nat.mul_le_mul_right (d - 1) this
          have e : (eset N U).card * d = (eset N U).card * (d - 1) + (eset N U).card := by
            rw [← Nat.mul_succ]; congr 1
          omega
        calc _ = A * ((Ea.card + Eb.card) * (d - 1) + (eset N U).card) := by ring
          _ ≤ A * ((eset N U).card * d) := Nat.mul_le_mul_left _ h'
          _ = _ := by ring
      have hA : L * (eset N U).card + 2 * (40 * K * lg n * (1 + 9 * 50000 ^ 2) *
          (eset N U).card) = A * (eset N U).card := by
        simp only [A, L]; ring
      have hL : L * Ea.card + L * Eb.card ≤ L * (eset N U).card := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
      omega

/-- With a kept dart, every vertex of a plane map is the tail of a kept dart. -/
lemma touch_of_reps (hM : N.IsPlane) (hne : (reps N).Nonempty) :
    ∀ v, ∃ d ∈ reps N, N.tail d = v := by
  obtain ⟨d₀, hd₀⟩ := hne
  exact exists_reps_tail hM hd₀

/-- **The cost of the recursion on `negDec N` is `O(n log² n)`**: on a plane map with transitive
rotations and faces and `n` darts, at most `C₁ K n lg² n + C₂ K n` with
`C₁ = 160 (1 + 9 · 50000²) + 1152 · 50000²` and `C₂ = 576 · 50000²`, for every family of
subroutine costs meeting `NegCosts.Bounds K`. -/
theorem negCost_negDec (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (hc : c.Bounds K) :
    negCost N c (negDec N) ≤
      (160 * (1 + 9 * 50000 ^ 2) + 1152 * 50000 ^ 2) * K * Fintype.card D *
          lg (Fintype.card D) ^ 2 +
        576 * 50000 ^ 2 * K * Fintype.card D := by
  classical
  rcases (reps N).eq_empty_or_nonempty with h0 | hne
  · have hd : negDec N = .leaf ∅ := by
      unfold negDec
      split_ifs with h
      · exact conv_empty _ (by rw [h.choose_spec.1, eset_univ, h0])
      · rw [h0]
    rw [hd, negCost_leaf_empty hc]; exact Nat.zero_le _
  obtain ⟨d₀, hd₀⟩ := hne
  have hex := exists_goodTree hM hrot hface hd₀
  have hd : negDec N = conv N hex.choose := by unfold negDec; simp only [hex, ↓reduceDIte]
  obtain ⟨hv, h1, h2, h3⟩ := hex.choose_spec
  have htouch := touch_of_reps hM ⟨d₀, hd₀⟩
  have hcost := negCost_conv hM hrot hface htouch hc h1 h2 h3
  rw [hv, eset_univ] at hcost
  rw [hd]
  set n := Fintype.card D
  have hrn : (reps N).card ≤ n := card_le_univ _
  have hVn : Fintype.card V ≤ n := by
    have := card_le_eset htouch univ
    rw [eset_univ, card_univ] at this
    omega
  have hdep : ndepth hex.choose ≤ 2 * lg n := by
    have := ndepth_le h3 (by rw [hv]; exact univ_nonempty_iff.2 ⟨N.tail d₀⟩)
    rw [hv, card_univ] at this
    have := Nat.log_mono_right (b := 2) hVn
    unfold lg; omega
  have hl := one_le_lg n
  calc negCost N c (conv N hex.choose)
      ≤ (80 * K * lg n * (1 + 9 * 50000 ^ 2) + 576 * 50000 ^ 2 * K) * (reps N).card *
          ndepth hex.choose + 576 * 50000 ^ 2 * K * (reps N).card := hcost
    _ ≤ (80 * K * lg n * (1 + 9 * 50000 ^ 2) + 576 * 50000 ^ 2 * K * lg n) * n * (2 * lg n) +
          576 * 50000 ^ 2 * K * n := by
        have h1 : 80 * K * lg n * (1 + 9 * 50000 ^ 2) + 576 * 50000 ^ 2 * K ≤
            80 * K * lg n * (1 + 9 * 50000 ^ 2) + 576 * 50000 ^ 2 * K * lg n :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_right _ hl) _
        exact Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul h1 hrn) hdep)
          (Nat.mul_le_mul_left _ hrn)
    _ = (160 * (1 + 9 * 50000 ^ 2) + 1152 * 50000 ^ 2) * K * n * lg n ^ 2 +
          576 * 50000 ^ 2 * K * n := by ring

variable (N) in
/-- **The counted cost of `negSSSPDec`**: the simple graph (the kept darts, their least lengths
and the check of the loops, linear bookkeeping on the `n` darts) and the recursion on
`negDec N`. The separator tree is given by an existence proof; its computation (Lipton and
Tarjan: linear time per separator) is charged at the nodes, as the separator calls `c.sep`. -/
noncomputable def negDecCost (c : NegCosts) : ℕ := c.lin (Fintype.card D) + negCost N c (negDec N)

/-- **The cost of `negSSSPDec` is `O(n log² n)`**: on a plane map with transitive rotations and
faces and `n` darts, at most `C₁ K n lg² n + (C₂ + 1) K n` with
`C₁ = 160 (1 + 9 · 50000²) + 1152 · 50000²` and `C₂ = 576 · 50000²`. -/
theorem negDecCost_le (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (hc : c.Bounds K) :
    negDecCost N c ≤
      (160 * (1 + 9 * 50000 ^ 2) + 1152 * 50000 ^ 2) * K * Fintype.card D *
          lg (Fintype.card D) ^ 2 +
        (576 * 50000 ^ 2 + 1) * K * Fintype.card D := by
  have h1 := hc.lin (Fintype.card D)
  have h2 := negCost_negDec hM hrot hface hc
  unfold negDecCost
  nlinarith

end NegSSSP

end PlanarFlow
