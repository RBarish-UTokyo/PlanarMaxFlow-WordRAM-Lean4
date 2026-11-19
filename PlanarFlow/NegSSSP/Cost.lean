module

public import PlanarFlow.NegSSSP.Rec

/-!
# The cost of the recursion: `O(n log² n)`

The cost of the algorithm of Klein, Mozes and Weimann (ACM Trans. Algorithms 6 (2010), 30), as
described by Mozes and Wulff-Nilsen (ESA 2010, the article, Section 3), is counted as an explicit
recurrence following the calls of `PlanarFlow.NegSSSP.run` (`negCost`), with the costs of the
subroutines as hypotheses (`NegCosts.Bounds`). Every call is charged its own input: a node of the
decomposition with a piece of `m` darts, split into pieces of `m₀` and `m₁` darts with `w₀` and
`w₁` vertices and `b` boundary vertices, costs (`NegCosts.node`)

* the separator and the check of the split: `sep m ≤ K m lg m` (the article quotes `O(m)`; the
  extra factor `lg m` leaves room for a machine implementation of Miller's cycle separator,
  within the budget `O(m lg m)` of a node);
* the boundary, the reduced lengths, the lowering of `E` and the minima: `lin m ≤ K m`;
* multiple-source shortest paths in each piece from the boundary (Klein; the boundary lies on one
  face of the piece), `mssp mᵢ b ≤ K (mᵢ lg mᵢ + b² lg mᵢ)` (the build, and `b²` queries);
* Bellman–Ford over the union of the two dense distance graphs, `bf b ≤ K (b + 1)² lg b`
  (`b + 1` rounds of `O(b log b)` by the Monge property; this is the bound
  `PlanarFlow.Monge.bfCost_le` of the program `PlanarFlow.Monge.bfDDG`);
* Dijkstra with a price function in each piece, on the `wᵢ` vertices and the root with the
  `mᵢ + wᵢ` explicit arcs (FR-Dijkstra on an empty dense distance graph, which is Dijkstra with a
  binary heap), `dij x p ≤ K (x + p) lg x`.

A leaf of `m` darts costs Bellman–Ford on its at most `2 m` vertices, `leaf m ≤ K m²`.

With the separators of `PlanarFlow.BKMNW.SepSpec` (simple paths of `k ≤ κ √m` darts, two thirds
balance, the boundary on the path), the boundary has `b ≤ k + 1` vertices, so a node costs
`O(m lg m)` (`NegCosts.node_le`), a depth of the decomposition `O(n lg n)`, and the depth is at
most `2 log₂ n + 1`. Hence **`negCost_le`: the cost is `O(n log² n)`**: at most
`2 (58 + 3 κ²) K n lg² n + K s n` for `n` darts, leaves of at most `s` darts.

`negSSSP_cost_dual`: the same on the dual map, with `n` the number of darts of `M`.

The hypothesis `SepSpec` of these two theorems cannot be met in general.
The bound without it, on the decomposition of a separator
tree of Lipton, Rose and Tarjan which exists on every plane map with transitive rotations and
faces, is `PlanarFlow.NegSSSP.negCost_negDec` (`PlanarFlow/NegSSSP/SepCost.lean`); on the
decomposition by simple cycles used by the maximum-flow algorithm, with the shared vertices of
every node on one face, it is `PlanarFlow.NegSSSP.negCost_le_fsq`
(`PlanarFlow/NegSSSP/FaceDec.lean`, `PlanarFlow.NegSSSP.negSSSPDecF`). On that decomposition the
charge `mssp` of a node is met in order by Klein's program on the map with the sources copied
(`PlanarFlow.NegSSSP.splitF_exec`: `O(m lg m)` steps per part, the reading of the `b²` answers off
its trees not included); the costs remain hypotheses of the counted model.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW CombMap

/-! ### The costs of the subroutines -/

/-- The costs of the subroutines. -/
structure NegCosts where
  /-- The separator (with the check of the split), on `m` darts. -/
  sep : ℕ → ℕ
  /-- Multiple-source shortest paths in a piece of `m` darts from `b` boundary vertices. -/
  mssp : ℕ → ℕ → ℕ
  /-- Bellman–Ford over the union of two dense distance graphs on `b` vertices. -/
  bf : ℕ → ℕ
  /-- Dijkstra with a price function on `x` vertices and `p` arcs. -/
  dij : ℕ → ℕ → ℕ
  /-- Linear bookkeeping on `m` darts. -/
  lin : ℕ → ℕ
  /-- The leaf solver on `m` darts. -/
  leaf : ℕ → ℕ

namespace NegCosts

variable (c : NegCosts)

/-- **The work of a node**: a piece of `m` darts with `b` boundary vertices, split into pieces of
`m₀` and `m₁` darts with `w₀` and `w₁` vertices. -/
def node (m b m₀ w₀ m₁ w₁ : ℕ) : ℕ :=
  c.sep m + c.lin m + c.mssp m₀ b + c.mssp m₁ b + c.bf b + c.dij (w₀ + 1) (m₀ + w₀) +
    c.dij (w₁ + 1) (m₁ + w₁)

/-- **The hypotheses on the costs of the subroutines.** -/
structure Bounds (K : ℕ) : Prop where
  sep : ∀ m, c.sep m ≤ K * m * lg m
  mssp : ∀ m b, c.mssp m b ≤ K * (m * lg m + b ^ 2 * lg m)
  bf : ∀ b, c.bf b ≤ K * (b + 1) ^ 2 * lg b
  dij : ∀ x p, c.dij x p ≤ K * (x + p) * lg x
  lin : ∀ m, c.lin m ≤ K * m
  leaf : ∀ m, c.leaf m ≤ K * m ^ 2

variable {c} {K : ℕ}

lemma dij_le (hc : c.Bounds K) {m mi wi : ℕ} (h1 : 1 ≤ mi) (h2 : mi ≤ m) (hw : wi ≤ 2 * mi) :
    c.dij (wi + 1) (mi + wi) ≤ 18 * K * m * lg m := by
  have h := hc.dij (wi + 1) (mi + wi)
  have hl : lg (wi + 1) ≤ 3 * lg m :=
    (lg_mono (by omega : wi + 1 ≤ 3 * m)).trans (lg_three_mul m)
  have hx : wi + 1 + (mi + wi) ≤ 6 * m := by omega
  calc c.dij (wi + 1) (mi + wi) ≤ K * (wi + 1 + (mi + wi)) * lg (wi + 1) := h
    _ ≤ K * (6 * m) * (3 * lg m) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hx) hl
    _ = 18 * K * m * lg m := by ring

lemma mssp_le (hc : c.Bounds K) {m mi b β : ℕ} (h2 : mi ≤ m) (hb : (b + 1) ^ 2 ≤ β * m) :
    c.mssp mi b ≤ (1 + β) * K * m * lg m := by
  have h := hc.mssp mi b
  have hl : lg mi ≤ lg m := lg_mono h2
  have hb2 : b ^ 2 ≤ β * m := le_trans (Nat.pow_le_pow_left (by omega) 2) hb
  calc c.mssp mi b ≤ K * (mi * lg mi + b ^ 2 * lg mi) := h
    _ ≤ K * (m * lg m + β * m * lg m) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul h2 hl) (Nat.mul_le_mul hb2 hl))
    _ = (1 + β) * K * m * lg m := by ring

/-- **A node costs `O(m lg m)`.** -/
theorem node_le (hc : c.Bounds K) {m b m₀ w₀ m₁ w₁ β : ℕ} (h₀ : 1 ≤ m₀) (h₁ : 1 ≤ m₁)
    (h₀m : m₀ ≤ m) (h₁m : m₁ ≤ m) (hw₀ : w₀ ≤ 2 * m₀) (hw₁ : w₁ ≤ 2 * m₁) (hbm : b ≤ m)
    (hb : (b + 1) ^ 2 ≤ β * m) :
    c.node m b m₀ w₀ m₁ w₁ ≤ (40 + 3 * β) * K * m * lg m := by
  have hl1 := one_le_lg m
  have hlin : K * m ≤ K * m * lg m := Nat.le_mul_of_pos_right _ hl1
  have hs : c.sep m ≤ K * m * lg m := hc.sep m
  have hli := hc.lin m
  have hm₀ := mssp_le hc h₀m hb
  have hm₁ := mssp_le hc h₁m hb
  have hd₀ := dij_le hc h₀ h₀m hw₀
  have hd₁ := dij_le hc h₁ h₁m hw₁
  have hbf : c.bf b ≤ β * K * m * lg m :=
    calc c.bf b ≤ K * (b + 1) ^ 2 * lg b := hc.bf b
      _ ≤ K * (β * m) * lg m := Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) (lg_mono hbm)
      _ = β * K * m * lg m := by ring
  unfold node
  rw [show (1 + β) * K * m * lg m = (1 + β) * (K * m * lg m) by ring] at hm₀ hm₁
  rw [show 18 * K * m * lg m = 18 * (K * m * lg m) by ring] at hd₀ hd₁
  rw [show β * K * m * lg m = β * (K * m * lg m) by ring] at hbf
  rw [show (40 + 3 * β) * K * m * lg m = (40 + 3 * β) * (K * m * lg m) by ring]
  generalize K * m * lg m = X at *
  nlinarith

end NegCosts

/-! ### The recurrence -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable {N : CombMap D V F}

variable (N) in
/-- **The cost of the recursion**, following the calls of `PlanarFlow.NegSSSP.run`: each node is
charged the work on its own piece. -/
def negCost (c : NegCosts) : NTree D → ℕ
  | .leaf P => c.leaf P.card
  | .node l r => negCost c l + negCost c r +
      c.node (l.piece ∪ r.piece).card (bdry N l.piece r.piece).card l.piece.card
        (verts N l.piece).card r.piece.card (verts N r.piece).card

namespace NTree

/-- The depth of a decomposition. -/
def depth : NTree D → ℕ
  | leaf _ => 0
  | node l r => max l.depth r.depth + 1

/-- The leaves have at most `s` darts. -/
def LeafLe (s : ℕ) : NTree D → Prop
  | leaf P => P.card ≤ s
  | node l r => l.LeafLe s ∧ r.LeafLe s

variable (N) in
/-- **A balanced decomposition**: siblings are disjoint and nonempty, each with at most two
thirds of the darts of their parent, and the boundary has `b ≤ m` vertices with
`(b + 1)² ≤ β m`. -/
def Bal (β : ℕ) : NTree D → Prop
  | leaf _ => True
  | node l r => l.Bal β ∧ r.Bal β ∧ Disjoint l.piece r.piece ∧ 0 < l.piece.card ∧
      0 < r.piece.card ∧ 3 * l.piece.card ≤ 2 * (l.piece ∪ r.piece).card ∧
      3 * r.piece.card ≤ 2 * (l.piece ∪ r.piece).card ∧
      ((bdry N l.piece r.piece).card + 1) ^ 2 ≤ β * (l.piece ∪ r.piece).card ∧
      (bdry N l.piece r.piece).card ≤ (l.piece ∪ r.piece).card

/-- **The depth of a balanced decomposition**: `(3/2)^depth ≤ n`. -/
theorem Bal.pow_depth {β : ℕ} :
    ∀ {τ : NTree D}, τ.Bal N β → 0 < τ.piece.card → 3 ^ τ.depth ≤ 2 ^ τ.depth * τ.piece.card
  | leaf _, _, hpos => by simp only [depth, pow_zero, one_mul]; exact hpos
  | node l r, h, _ => by
    obtain ⟨hl, hr, -, hl0, hr0, b0, b1, -⟩ := h
    have il := Bal.pow_depth hl hl0
    have ir := Bal.pow_depth hr hr0
    simp only [depth, piece] at il ir ⊢
    rcases le_total l.depth r.depth with hle | hle
    · rw [max_eq_right hle, pow_succ, pow_succ]
      nlinarith [Nat.zero_le (2 ^ r.depth)]
    · rw [max_eq_left hle, pow_succ, pow_succ]
      nlinarith [Nat.zero_le (2 ^ l.depth)]

/-- The depth of a balanced decomposition of `n` darts is at most `2 log₂ n + 1`. -/
theorem Bal.depth_le {β : ℕ} {τ : NTree D} (h : τ.Bal N β) (hpos : 0 < τ.piece.card) :
    τ.depth ≤ 2 * Nat.log 2 τ.piece.card + 1 := by
  have h1 := h.pow_depth hpos
  have h2 := ADec.two_pow_mul_two_pow_half_le τ.depth
  have h3 : 2 ^ (τ.depth / 2) ≤ τ.piece.card :=
    Nat.le_of_mul_le_mul_left (h2.trans h1) (by positivity)
  have := Nat.le_log_of_pow_le (by norm_num) h3
  omega

lemma card_verts_le (P : Finset D) : (verts N P).card ≤ 2 * P.card := by
  unfold verts
  have := card_union_le (P.image N.tail) (P.image N.head)
  have := card_image_le (s := P) (f := N.tail)
  have := card_image_le (s := P) (f := N.head)
  omega

end NTree

/-- **The cost per depth**: every depth of the decomposition costs `O(n lg n)`. -/
theorem negCost_le_depth {c : NegCosts} {K β s Nn : ℕ} (hc : c.Bounds K) :
    ∀ {τ : NTree D}, τ.Bal N β → τ.LeafLe s → τ.piece.card ≤ Nn →
      negCost N c τ ≤ (40 + 3 * β) * K * lg Nn * (τ.piece.card * τ.depth) + K * s * τ.piece.card
  | .leaf P, _, hs, _ => by
    simp only [negCost, NTree.piece, NTree.depth, mul_zero, zero_add]
    calc c.leaf P.card ≤ K * P.card ^ 2 := hc.leaf _
      _ = K * P.card * P.card := by ring
      _ ≤ K * s * P.card := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hs)
  | .node l r, h, hs, hN => by
    obtain ⟨hl, hr, hlr, hl0, hr0, -, -, hb, hbm⟩ := h
    have hcard : (l.piece ∪ r.piece).card = l.piece.card + r.piece.card :=
      card_union_of_disjoint hlr
    simp only [NTree.piece] at hN
    have il := negCost_le_depth hc hl hs.1 (by omega : l.piece.card ≤ Nn)
    have ir := negCost_le_depth hc hr hs.2 (by omega : r.piece.card ≤ Nn)
    have hn := NegCosts.node_le hc hl0 hr0 (by omega) (by omega)
      (NTree.card_verts_le (N := N) l.piece) (NTree.card_verts_le (N := N) r.piece) hbm hb
    have hlg : lg (l.piece ∪ r.piece).card ≤ lg Nn := lg_mono hN
    generalize (40 + 3 * β) * K = B at il ir hn ⊢
    have hn' : c.node (l.piece ∪ r.piece).card (bdry N l.piece r.piece).card l.piece.card
        (verts N l.piece).card r.piece.card (verts N r.piece).card ≤
        B * lg Nn * (l.piece ∪ r.piece).card := by
      calc _ ≤ B * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card := hn
        _ ≤ B * (l.piece ∪ r.piece).card * lg Nn := Nat.mul_le_mul_left _ hlg
        _ = _ := by ring
    simp only [negCost, NTree.piece, NTree.depth]
    rw [hcard] at hn' ⊢
    generalize B * lg Nn = A at il ir hn' ⊢
    have hw : l.piece.card * l.depth + r.piece.card * r.depth + (l.piece.card + r.piece.card) ≤
        (l.piece.card + r.piece.card) * (max l.depth r.depth + 1) := by
      nlinarith [Nat.mul_le_mul_left l.piece.card (le_max_left l.depth r.depth),
        Nat.mul_le_mul_left r.piece.card (le_max_right l.depth r.depth)]
    have := Nat.mul_le_mul_left A hw
    nlinarith

/-- **The cost of the recursion is `O(n log² n)`**: on a balanced decomposition of a nonempty
piece of `n` darts with leaves of at most `s` darts, at most `2 (40 + 3 β) K n lg² n + K s n`. -/
theorem negCost_le_sq {c : NegCosts} {K β s : ℕ} (hc : c.Bounds K) {τ : NTree D}
    (h : τ.Bal N β) (hs : τ.LeafLe s) (hpos : 0 < τ.piece.card) :
    negCost N c τ ≤ 2 * (40 + 3 * β) * K * τ.piece.card * lg τ.piece.card ^ 2 +
      K * s * τ.piece.card := by
  have h1 := negCost_le_depth hc h hs le_rfl
  have h2 : τ.depth ≤ 2 * lg τ.piece.card := by
    have := h.depth_le hpos; unfold lg; omega
  generalize hB : (40 + 3 * β) * K = B at h1
  have h3 : B * lg τ.piece.card * (τ.piece.card * τ.depth) ≤
      B * lg τ.piece.card * (τ.piece.card * (2 * lg τ.piece.card)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
  calc _ ≤ _ := h1
    _ ≤ B * lg τ.piece.card * (τ.piece.card * (2 * lg τ.piece.card)) +
        K * s * τ.piece.card := Nat.add_le_add_right h3 _
    _ = _ := by rw [← hB]; ring

/-! ### The decomposition of the separator subroutine is balanced -/

lemma touch_of_mem_verts {P : Finset D} (hP : RevClosed N P) {v : V} (hv : v ∈ verts N P) :
    Touch N P v := by
  rcases mem_union.1 hv with h | h
  · obtain ⟨d, hd, rfl⟩ := mem_image.1 h
    exact ⟨d, hd, rfl⟩
  · obtain ⟨d, hd, rfl⟩ := mem_image.1 h
    exact ⟨N.rev d, hP d hd, rfl⟩

lemma card_verts_path (π : SPath N) : π.verts.card ≤ π.k + 1 := by
  unfold SPath.verts SPath.init
  exact card_image_le.trans (by simp)

/-- **The decomposition built from a separator subroutine meeting `SepSpec`** (on the pieces
alone: no terminals, no holes) is balanced with `β = κ² + 6`, and its leaves have at most `s`
darts. -/
theorem build_spec {κ η s : ℕ}
    {sep : Finset D → List (Finset V) → Finset D × Finset D × SPath N}
    (hsep : SepSpec N ∅ ∅ κ η s sep) :
    ∀ (n : ℕ) (P : Finset D), P.card ≤ n → RevClosed N P →
      (NTree.build sep s P).Bal N (κ ^ 2 + 6) ∧ (NTree.build sep s P).LeafLe s := by
  intro n
  induction n with
  | zero =>
    intro P hP _
    rw [NTree.build]
    split_ifs with h
    · omega
    · exact ⟨trivial, by simp only [NTree.LeafLe]; omega⟩
  | succ n ih =>
    intro P hP hrev
    by_cases hs : s < P.card
    · have hsp := hsep P [] hrev hs (by simp [nTouch])
      have h1 : (sep P []).1.card < P.card := by have := hsp.bal₀; omega
      have h2 : (sep P []).2.1.card < P.card := by have := hsp.bal₁; omega
      rw [NTree.build]
      split_ifs with h
      swap
      · exact absurd ⟨hs, h1, h2, hsp.union⟩ h
      obtain ⟨b1, l1⟩ := ih _ (by omega) hsp.rev₀
      obtain ⟨b2, l2⟩ := ih _ (by omega) hsp.rev₁
      have e1 := NTree.piece_build sep s _ (sep P []).1 le_rfl
      have e2 := NTree.piece_build sep s _ (sep P []).2.1 le_rfl
      have hbd : bdry N (sep P []).1 (sep P []).2.1 ⊆ (sep P []).2.2.verts := by
        intro v hv
        obtain ⟨hv₀, hv₁⟩ := mem_inter.1 hv
        have := hsp.bd (mem_bd.2 ⟨touch_of_mem_verts hsp.rev₀ hv₀,
          touch_of_mem_verts hsp.rev₁ hv₁⟩)
        simpa [hunion] using this
      have hb := (card_le_card hbd).trans (card_verts_path _)
      have hk := hsp.len
      have hk2 := hsp.len₂
      have hP0 : 0 < P.card := by omega
      refine ⟨⟨b1, b2, ?_⟩, l1, l2⟩
      rw [e1, e2, hsp.union]
      refine ⟨hsp.disj, hsp.pos₀, hsp.pos₁, hsp.bal₀, hsp.bal₁, ?_, by omega⟩
      generalize (bdry N (sep P []).1 (sep P []).2.1).card = b at hb ⊢
      generalize (sep P []).2.2.k = k at hb hk hk2
      have : (b + 1) ^ 2 ≤ (k + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      nlinarith
    · rw [NTree.build]
      split_ifs with h
      · exact absurd h.1 hs
      · exact ⟨trivial, by simp only [NTree.LeafLe]; omega⟩

/-- **The cost of shortest paths with negative lengths is `O(n log² n)`**: with a separator
subroutine meeting `SepSpec` (simple paths of `k ≤ κ √m` darts), on a map with `n ≥ 1` darts,
the counted cost of the recursion is at most `2 (58 + 3 κ²) K n lg² n + K s n`. -/
theorem negSSSP_cost {κ η s : ℕ} {sep : Finset D → List (Finset V) → Finset D × Finset D × SPath N}
    (hsep : SepSpec N ∅ ∅ κ η s sep) {c : NegCosts} {K : ℕ} (hc : c.Bounds K)
    (hD : 0 < Fintype.card D) :
    negCost N c (NTree.build sep s univ) ≤
      2 * (58 + 3 * κ ^ 2) * K * Fintype.card D * lg (Fintype.card D) ^ 2 +
        K * s * Fintype.card D := by
  obtain ⟨hbal, hleaf⟩ := build_spec hsep _ univ le_rfl (fun _ _ => mem_univ _)
  have hp := NTree.piece_build sep s _ univ le_rfl
  have := negCost_le_sq hc hbal hleaf (by rw [hp, card_univ]; exact hD)
  rw [hp, card_univ] at this
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **The cost on the dual map**: `O(n log² n)` for a map `M` with `n ≥ 1` darts, with a
separator subroutine for the dual map meeting `SepSpec`. -/
theorem negSSSP_cost_dual [Fintype F] [DecidableEq F] (M : CombMap D V F) {κ η s : ℕ}
    {sep : Finset D → List (Finset F) → Finset D × Finset D × SPath M.dual}
    (hsep : SepSpec M.dual ∅ ∅ κ η s sep) {c : NegCosts} {K : ℕ} (hc : c.Bounds K)
    (hD : 0 < Fintype.card D) :
    negCost M.dual c (NTree.build sep s univ) ≤
      2 * (58 + 3 * κ ^ 2) * K * Fintype.card D * lg (Fintype.card D) ^ 2 +
        K * s * Fintype.card D :=
  negSSSP_cost hsep hc hD

end NegSSSP

end PlanarFlow
