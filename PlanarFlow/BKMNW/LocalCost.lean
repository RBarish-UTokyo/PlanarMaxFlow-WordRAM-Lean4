module

public import PlanarFlow.BKMNW.Local

/-!
# The cost of Algorithm 1 on the piece maps

`arunLCost` counts the calls of `PlanarFlow.BKMNW.arunL`, **every call charged at the size of
the piece map it runs on**: at a recursive step on a piece `P` with holes `Hs`, the piece map has
`m ≤ |P|` darts (`pdarts M P Hs`), `nf` faces and `N = m + V + F ≤ 3 m` darts, vertices and
faces (`psize`), and

* the separator subroutine is charged on the piece (`c.sep |P|`);
* the recursive step `PlanarFlow.BKMNW.sepStep` on the piece map is charged as
  `PlanarFlow.BKMNW.SubCosts.nodeRuns` charges it on a map: for each part of the separator off the
  holes, of `k` darts along `x ≤ 2 k` faces, `PlanarFlow.BKMNW.SubCosts.nodeRun`
  (FixConservationOnPath, the two calls of Section 4 for each hole, the two push-backs, the linear
  passes), with the sizes of the piece map and as holes its `h` holes and the later parts;
* the linear bookkeeping is charged `8` linear passes on `|P| + |Hs|`: the darts of the piece map,
  the rotations of the two child piece maps (`PlanarFlow.BKMNW.childRot`, two first returns
  each, linear in the darts of the piece map), the images of the terminals and the holes, the
  separator of the piece map, the sum of the flows of the children, and the orbits of the piece
  map;
* a leaf: the leaf solver on its piece map and `4` linear passes on `|Q| + |Hs|`.

`runLCost` adds `2` linear passes on the map (its rotation, and the final flow).

## Main results

* `SubCosts.nodeRun_le'`: a recursive step on a piece map of size at most `N'` costs
  `O(N' lg² N')` when `k ≤ κ √N'`, with at most `η` holes; `SubCosts.nodeRuns_le'`: the same for
  each part of a separator.
* `arunLCost_le`: on a balanced decomposition, a piece of `m` darts at depth `d` costs at most
  `A m (d + 1)`.
* `runL_cost`: **the cost of the algorithm with every recursive step on its piece map is
  `O(n log³ n)`** on a balanced decomposition, the bound of Theorem 1.1 of the article, for the
  algorithm `runL` that is proved correct (`PlanarFlow.BKMNW.runL_isMax`). The two theorems have
  separate hypotheses on the decomposition: correctness needs `ADec.Good`, `ADec.PGood` and
  `ADec.LeafOK`; the cost needs `ADec.Bal`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv CombMap Orbit

namespace SubCosts

variable {c : SubCosts} {K K₀ : ℕ}

/-- The push-back on a map of size `N ≤ N'`. -/
theorem pushRun_le' (hc : c.Bounds K K₀) {n nf N N' : ℕ} (hn : n ≤ N') (hf : nf ≤ N')
    (hN : N ≤ N') : c.pushRun n nf N ≤ 8 * K * N' * lg N' ^ 2 := by
  have hl1 := one_le_lg N'
  have hlg := lg_le_sq N'
  have hlf : lg nf ≤ lg N' := lg_mono hf
  have h1 : c.fr nf n ≤ 2 * (K * N' * lg N' ^ 2) := by
    refine (hc.fr nf n).trans ?_
    have : nf * lg nf ^ 2 ≤ N' * lg N' ^ 2 := Nat.mul_le_mul hf (Nat.pow_le_pow_left hlf 2)
    have : n * lg nf ≤ N' * lg N' ^ 2 := Nat.mul_le_mul hn (hlf.trans hlg)
    have : K * (nf * lg nf ^ 2 + n * lg nf) ≤ K * (2 * (N' * lg N' ^ 2)) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have h2 := lin_le_of_le hc hN
  unfold pushRun
  nlinarith

/-- CycleToSingleSinkLimitedMaxFlow on a map of size `N ≤ N'`. -/
theorem c2sRun_le' (hc : c.Bounds K K₀) {n nf N N' x k κ : ℕ} (hn : n ≤ N') (hf : nf ≤ N')
    (hN : N ≤ N') (hx : x ≤ 2 * k) (hk : 2 * k ≤ N') (hκ : k ^ 2 ≤ κ ^ 2 * N') :
    c.c2sRun n nf N x k ≤ (16 + 7 * κ ^ 2) * K * N' * lg N' ^ 2 := by
  have hl1 := one_le_lg N'
  have hlg := lg_le_sq N'
  have h1 : c.stflow n ≤ K * N' * lg N' ^ 2 :=
    (hc.stflow n).trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hn)
      (Nat.pow_le_pow_left (lg_mono hn) 2))
  have h2 := fixRun_le hc hn hx hk hκ (by omega : 3 * N ≤ 3 * N')
  have h3 := pushRun_le' hc hn hf hN
  have h4 := lin_le_of_le hc hN
  unfold c2sRun
  nlinarith

/-- **A recursive step on a map of size `N ≤ N'`** costs `O(N' lg² N')`, with at most `η` holes,
all of them tested. -/
theorem nodeRun_le' (hc : c.Bounds K K₀) {n nf N N' x k h κ η : ℕ} (hn : n ≤ N') (hf : nf ≤ N')
    (hN : N ≤ N') (hx : x ≤ 2 * k) (hk : 2 * k ≤ N') (hκ : k ^ 2 ≤ κ ^ 2 * N') (hh : h ≤ η) :
    c.nodeRun n nf N x k h h ≤ (25 + 7 * κ ^ 2 + η * (34 + 14 * κ ^ 2)) * K * N' * lg N' ^ 2 := by
  have hl1 := one_le_lg N'
  have hlg := lg_le_sq N'
  have h1 : c.sep n ≤ K * N' * lg N' ^ 2 := sep_le_of_le hc hn
  have h2 := fixRun_le hc hn hx hk hκ (by omega : N ≤ 3 * N')
  have h3 := pushRun_le' hc hn hf hN
  have h4 := lin_le_of_le hc hN
  have h5 := c2sRun_le' hc hn hf hN hx hk hκ
  have h7 : h * (2 * c.c2sRun n nf N x k + c.lin N) ≤
      η * ((33 + 14 * κ ^ 2) * K * N' * lg N' ^ 2) :=
    Nat.mul_le_mul hh (by nlinarith)
  have h6 : h * c.lin N ≤ η * (K * N' * lg N' ^ 2) := Nat.mul_le_mul hh h4
  unfold nodeRun
  nlinarith

/-- **The steps on the parts of a separator on a map of size `N ≤ N'`** cost `O(N' lg² N')` each,
with at most `2 η` holes and later parts, all of them tested. -/
theorem nodeRuns_le' (hc : c.Bounds K K₀) {n nf N N' h κ η : ℕ} (hn : n ≤ N') (hf : nf ≤ N')
    (hN : N ≤ N') :
    ∀ l : List (ℕ × ℕ), (∀ xk ∈ l, xk.1 ≤ 2 * xk.2 ∧ 2 * xk.2 ≤ N' ∧ xk.2 ^ 2 ≤ κ ^ 2 * N') →
      h + l.length ≤ 2 * η + 1 →
      c.nodeRuns n nf N h h l ≤
        l.length * ((25 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2)) * K * N' * lg N' ^ 2)
  | [], _, _ => by simp [nodeRuns]
  | xk :: l, hl, hh => by
    simp only [List.length_cons] at hh
    obtain ⟨h1, h2, h3⟩ := hl xk (List.mem_cons_self ..)
    have i := nodeRuns_le' hc (h := h) (κ := κ) (η := η) hn hf hN l
      (fun y hy => hl y (List.mem_cons_of_mem _ hy)) (by omega)
    have e := nodeRun_le' hc (h := h + l.length) (η := 2 * η) hn hf hN h1 h2 h3 (by omega)
    simp only [nodeRuns, List.length_cons]
    nlinarith

end SubCosts

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- The size of a piece map: its darts, vertices and faces. -/
noncomputable def psize (σ : Perm D) (B : Finset D) : ℕ :=
  B.card + nOrb σ B + nOrb (σ * revPerm M) B

lemma psize_le (σ : Perm D) (B : Finset D) : psize M σ B ≤ 3 * B.card := by
  have := nOrb_le_card σ B; have := nOrb_le_card (σ * revPerm M) B; unfold psize; omega

lemma length_pholes_le {σ : Perm D} {B P : Finset D} (hBP : B ⊆ P) (Hs : List (Finset V)) :
    (pholes M σ B Hs).length ≤ nTouch M P Hs := by
  classical
  induction Hs with
  | nil => simp [pholes, nTouch]
  | cons H Hs ih =>
    simp only [pholes, nTouch, List.map_cons, List.filter_cons] at ih ⊢
    split_ifs with h1 h2 h2 <;> (try simp only [List.length_cons]) <;> try omega
    exfalso
    obtain ⟨w, hw⟩ := of_decide_eq_true h1
    obtain ⟨x, hx, -⟩ := mem_vimg.1 hw
    exact h2 (decide_eq_true ⟨_, hx, x.1, hBP x.2, rfl⟩)

variable (M) in
open Classical in
/-- **The cost of `PlanarFlow.BKMNW.arunL`**, every call charged at the size of the piece map it
runs on. -/
noncomputable def arunLCost (c : SubCosts) : ADec M → List (Finset V) → Perm D → ℕ
  | .leaf Q, Hs, _ => c.leaf (pdarts M Q Hs).card + 4 * c.lin (Q.card + Hs.length)
  | .node l r π, Hs, σ =>
    arunLCost c l (childHoles Hs π.path.mverts) (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs)
        π.path.darts (pdarts M l.piece (childHoles Hs π.path.mverts))) +
      arunLCost c r (childHoles Hs π.path.mverts) (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs)
        π.path.darts (pdarts M r.piece (childHoles Hs π.path.mverts))) +
      (if h : PieceInv M (l.piece ∪ r.piece) Hs σ ∧
          ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s then
        c.sep (l.piece ∪ r.piece).card +
          c.nodeRuns (pdarts M (l.piece ∪ r.piece) Hs).card
            (nOrb (σ * revPerm M) (pdarts M (l.piece ∪ r.piece) Hs))
            (psize M σ (pdarts M (l.piece ∪ r.piece) Hs))
            (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length
            (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length
            ((segsP h.1 π.segs h.2).map fun s => (s.faces.card, s.k))
      else 0) +
      8 * c.lin ((l.piece ∪ r.piece).card + Hs.length)

/-- The bound of one call per dart of its piece: `A = (3 Cₙ + 1) K lg² (3 n) + 8 K (L + 1) + K₀`,
with `Cₙ = (η + 1) (25 + 7 κ² + 2 η (34 + 14 κ²))`, `n` the darts of the map and `L` a bound on
the number of holes and the depth (the term `K lg² (3 n)` for the separator, `K m lg m` on a
piece of `m` darts). -/
def callBound (K K₀ κ η L n : ℕ) : ℕ :=
  (3 * ((η + 1) * (25 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2))) + 1) * K * lg (3 * n) ^ 2 +
    8 * K * (L + 1) + K₀

/-- **The recurrence**: on a decomposition meeting `ADec.Core` (in particular a balanced one,
`ADec.Bal.core`), a piece of `m ≥ 1` darts costs at most `A m (d + 1)` for its depth `d`. -/
theorem arunLCost_le {c : SubCosts} {K K₀ κ η L n : ℕ} (hc : c.Bounds K K₀) :
    ∀ {τ : ADec M} {Hs : List (Finset V)} (σ : Perm D), τ.Core M κ η Hs → 0 < τ.piece.card →
      τ.piece.card ≤ n → Hs.length + τ.depth ≤ L →
      arunLCost M c τ Hs σ ≤ callBound K K₀ κ η L n * (τ.piece.card * (τ.depth + 1))
  | .leaf Q, Hs, σ, _, hpos, hn, hL => by
    simp only [ADec.piece] at hpos hn
    simp only [ADec.depth, add_zero] at hL
    simp only [arunLCost, ADec.piece, ADec.depth, zero_add, mul_one]
    have h1 : c.leaf (pdarts M Q Hs).card ≤ K₀ * Q.card :=
      (hc.leaf _).trans (Nat.mul_le_mul_left _ (card_le_card (pdarts_subset Q Hs)))
    have h2 : 4 * c.lin (Q.card + Hs.length) ≤ 4 * K * (L + 1) * Q.card := by
      have := hc.lin (Q.card + Hs.length)
      have : Q.card + Hs.length ≤ (L + 1) * Q.card := by nlinarith
      nlinarith
    unfold callBound
    generalize (3 * ((η + 1) * (25 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2))) + 1) * K *
      lg (3 * n) ^ 2 = X
    have e : 4 * K * (L + 1) * Q.card ≤ 8 * K * (L + 1) * Q.card :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
    have : (X + 8 * K * (L + 1) + K₀) * Q.card =
        X * Q.card + 8 * K * (L + 1) * Q.card + K₀ * Q.card := by ring
    rw [this]
    have := Nat.zero_le (X * Q.card)
    omega
  | .node l r π, Hs, σ, h, hpos, hn, hL => by
    classical
    obtain ⟨hl, hr, hlr, hl0, hr0, ⟨hlen, hk⟩, hη⟩ := h
    have hcard : (l.piece ∪ r.piece).card = l.piece.card + r.piece.card :=
      card_union_of_disjoint hlr
    have hn' : l.piece.card + r.piece.card ≤ n := by rw [← hcard]; exact hn
    simp only [ADec.depth] at hL
    have hHl := length_childHoles Hs π.path.mverts
    have hLl : (childHoles Hs π.path.mverts).length + l.depth ≤ L := by
      have := le_max_left l.depth r.depth; omega
    have hLr : (childHoles Hs π.path.mverts).length + r.depth ≤ L := by
      have := le_max_right l.depth r.depth; omega
    have il := arunLCost_le (n := n) (L := L) (κ := κ) (η := η) hc
      (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts
        (pdarts M l.piece (childHoles Hs π.path.mverts))) hl hl0 (by omega) hLl
    have ir := arunLCost_le (n := n) (L := L) (κ := κ) (η := η) hc
      (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts
        (pdarts M r.piece (childHoles Hs π.path.mverts))) hr hr0 (by omega) hLr
    generalize hm : (l.piece ∪ r.piece).card = m at hcard hk hn
    have hmn : m ≤ n := by rw [← hm]; exact hn
    -- one call
    have hstep : (if h : PieceInv M (l.piece ∪ r.piece) Hs σ ∧
          ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s then
        c.sep (l.piece ∪ r.piece).card +
          c.nodeRuns (pdarts M (l.piece ∪ r.piece) Hs).card
            (nOrb (σ * revPerm M) (pdarts M (l.piece ∪ r.piece) Hs))
            (psize M σ (pdarts M (l.piece ∪ r.piece) Hs))
            (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length
            (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length
            ((segsP h.1 π.segs h.2).map fun s => (s.faces.card, s.k))
      else 0) ≤ K * m * lg (3 * n) ^ 2 +
        3 * ((η + 1) * (25 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2))) * K * m * lg (3 * n) ^ 2 := by
      split_ifs with hh
      · have hB : (pdarts M (l.piece ∪ r.piece) Hs).card ≤ m := by
          rw [← hm]; exact card_le_card (pdarts_subset _ _)
        have hsep : c.sep (l.piece ∪ r.piece).card ≤ K * m * lg (3 * n) ^ 2 :=
          (SubCosts.sep_le_sq hc _).trans (by
            rw [hm]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (lg_mono (by omega)) 2))
        have hph := (length_pholes_le (M := M) (σ := σ)
          (pdarts_subset (M := M) (l.piece ∪ r.piece) Hs)
          Hs).trans hη
        have hrun := SubCosts.nodeRuns_le' hc (N' := 3 * m) (κ := κ) (η := η)
          (n := (pdarts M (l.piece ∪ r.piece) Hs).card)
          (nf := nOrb (σ * revPerm M) (pdarts M (l.piece ∪ r.piece) Hs))
          (N := psize M σ (pdarts M (l.piece ∪ r.piece) Hs))
          (h := (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length) (by omega)
          ((nOrb_le_card _ _).trans (by omega)) ((psize_le _ _).trans (by omega))
          ((segsP hh.1 π.segs hh.2).map fun s => (s.faces.card, s.k)) (fun xk hxk => by
            obtain ⟨π', hπ', rfl⟩ := List.mem_map.1 hxk
            have : π'.k ∈ (segsP hh.1 π.segs hh.2).map SPath.k := List.mem_map_of_mem hπ'
            rw [segsP_k] at this
            obtain ⟨s, hs, e⟩ := List.mem_map.1 this
            obtain ⟨k1, k2⟩ := hk s hs
            refine ⟨π'.card_faces_le, by rw [← e]; omega, ?_⟩
            rw [← e]; nlinarith)
          (by rw [List.length_map]
              have : (segsP hh.1 π.segs hh.2).length = π.segs.length := by
                rw [← List.length_map (f := SPath.k), segsP_k, List.length_map]
              omega)
        rw [List.length_map] at hrun
        have hlen' : (segsP hh.1 π.segs hh.2).length ≤ η + 1 := by
          rw [← List.length_map (f := SPath.k), segsP_k, List.length_map]; exact hlen
        have hlg : lg (3 * m) ^ 2 ≤ lg (3 * n) ^ 2 := Nat.pow_le_pow_left (lg_mono (by omega)) 2
        generalize 25 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2) = Cn at hrun ⊢
        have h1 : (segsP hh.1 π.segs hh.2).length * (Cn * K * (3 * m) * lg (3 * m) ^ 2) ≤
            (η + 1) * (Cn * K * (3 * m) * lg (3 * m) ^ 2) := Nat.mul_le_mul_right _ hlen'
        have : (η + 1) * (Cn * K * (3 * m) * lg (3 * m) ^ 2) ≤
            3 * ((η + 1) * Cn) * K * m * lg (3 * n) ^ 2 := by
          calc (η + 1) * (Cn * K * (3 * m) * lg (3 * m) ^ 2) =
              3 * ((η + 1) * Cn) * K * m * lg (3 * m) ^ 2 := by ring
            _ ≤ _ := Nat.mul_le_mul_left _ hlg
        omega
      · exact Nat.zero_le _
    have hbook : 8 * c.lin (m + Hs.length) ≤ 8 * K * (L + 1) * m := by
      have h1 := hc.lin (m + Hs.length)
      have h2 : Hs.length ≤ L * m :=
        (by omega : Hs.length ≤ L).trans (Nat.le_mul_of_pos_right _ (by omega))
      have h3 : m + Hs.length ≤ (L + 1) * m := by rw [add_mul, one_mul]; omega
      have h4 : K * (m + Hs.length) ≤ K * ((L + 1) * m) := Nat.mul_le_mul_left _ h3
      calc 8 * c.lin (m + Hs.length) ≤ 8 * (K * (m + Hs.length)) := Nat.mul_le_mul_left _ h1
        _ ≤ 8 * (K * ((L + 1) * m)) := Nat.mul_le_mul_left _ h4
        _ = 8 * K * (L + 1) * m := by ring
    simp only [arunLCost, ADec.piece, ADec.depth]
    rw [hm] at hstep ⊢
    have hA : K * m * lg (3 * n) ^ 2 +
        3 * ((η + 1) * (25 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2))) * K * m *
        lg (3 * n) ^ 2 + 8 * K * (L + 1) * m ≤ callBound K K₀ κ η L n * m := by
      unfold callBound
      generalize (η + 1) * (25 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2)) = Cn
      generalize lg (3 * n) ^ 2 = G
      have h2 : ((3 * Cn + 1) * K * G + 8 * K * (L + 1) + K₀) * m =
          K * m * G + 3 * Cn * K * m * G + 8 * K * (L + 1) * m + K₀ * m := by ring
      rw [h2]
      omega
    have hw : l.piece.card * (l.depth + 1) + r.piece.card * (r.depth + 1) + m ≤
        m * (max l.depth r.depth + 1 + 1) := by
      have h1 := Nat.mul_le_mul_left l.piece.card (le_max_left l.depth r.depth)
      have h2 := Nat.mul_le_mul_left r.piece.card (le_max_right l.depth r.depth)
      rw [hcard]
      generalize max l.depth r.depth = d at h1 h2
      have e : (l.piece.card + r.piece.card) * (d + 1 + 1) =
          l.piece.card * d + r.piece.card * d + 2 * l.piece.card + 2 * r.piece.card := by ring
      have e1 : l.piece.card * (l.depth + 1) = l.piece.card * l.depth + l.piece.card := by ring
      have e2 : r.piece.card * (r.depth + 1) = r.piece.card * r.depth + r.piece.card := by ring
      rw [e, e1, e2]
      omega
    generalize callBound K K₀ κ η L n = A at il ir hA ⊢
    have := Nat.mul_le_mul_left A hw
    rw [mul_add, mul_add] at this
    omega


variable (M) in
/-- **The cost of `PlanarFlow.BKMNW.runL`** on the decomposition `τ`: the recursion on the piece
maps, and two linear passes on the map (its rotation, and the final flow). -/
noncomputable def runLCost (c : SubCosts) (τ : ADec M) : ℕ :=
  arunLCost M c τ [] (rotPerm M) + 2 * c.lin (mapSize M)

/-- **The cost of Algorithm 1 with every recursive step on its piece map is `O(n log³ n)`** (the
bound of Theorem 1.1 of the article): on a plane map with `n ≥ 1` darts and a balanced
decomposition of its darts, at most `(54 Cₙ + 58) K n lg³ n + 2 K₀ n lg n` with
`Cₙ = (η + 1) (25 + 7 κ² + 2 η (34 + 14 κ²))`. -/
theorem runL_cost (hM : M.IsPlane) {κ η : ℕ} {τ : ADec M} (hall : τ.piece = univ)
    (hbal : τ.Bal M κ η []) {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    (hD : 0 < Fintype.card D) :
    runLCost M c τ ≤ (54 * ((η + 1) * (25 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2))) + 58) * K *
        Fintype.card D * lg (Fintype.card D) ^ 3 +
      2 * K₀ * Fintype.card D * lg (Fintype.card D) := by
  have hpos : 0 < τ.piece.card := by rw [hall, card_univ]; exact hD
  have hdep := hbal.depth_le hpos
  rw [hall, card_univ] at hdep
  generalize hn : Fintype.card D = n at hD hdep
  have hcn : τ.piece.card = n := by rw [hall, card_univ, hn]
  have h1 := arunLCost_le (n := n) (L := τ.depth) (σ := rotPerm M) hc hbal.core hpos (by omega)
    (by simp)
  rw [hcn] at h1
  have hl1 := one_le_lg n
  have hdl : τ.depth + 1 ≤ 2 * lg n := by unfold lg; omega
  have hlg3 : lg (3 * n) ^ 2 ≤ 9 * lg n ^ 2 := by have := lg_three_mul n; nlinarith
  have hmap : c.lin (mapSize M) ≤ 4 * K * n := by
    have := mapSize_le_of_isPlane hM
    rw [hn] at this
    exact (hc.lin _).trans (by nlinarith)
  unfold runLCost
  unfold callBound at h1
  generalize (η + 1) * (25 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2)) = Cn at h1 ⊢
  generalize τ.depth + 1 = d1 at h1 hdl
  generalize lg n = G at hl1 hdl hlg3 ⊢
  have hX : (3 * Cn + 1) * K * lg (3 * n) ^ 2 + 8 * K * d1 + K₀ ≤
      (27 * Cn + 9) * K * G ^ 2 + 16 * K * G + K₀ := by
    have a1 : (3 * Cn + 1) * K * lg (3 * n) ^ 2 ≤ (3 * Cn + 1) * K * (9 * G ^ 2) :=
      Nat.mul_le_mul_left _ hlg3
    have a2 : 8 * K * d1 ≤ 8 * K * (2 * G) := Nat.mul_le_mul_left _ hdl
    have e1 : (3 * Cn + 1) * K * (9 * G ^ 2) = (27 * Cn + 9) * K * G ^ 2 := by ring
    have e2 : 8 * K * (2 * G) = 16 * K * G := by ring
    omega
  have hY := Nat.mul_le_mul hX (Nat.mul_le_mul_left n hdl)
  have e3 : ((27 * Cn + 9) * K * G ^ 2 + 16 * K * G + K₀) * (n * (2 * G)) =
      (54 * Cn + 18) * K * n * G ^ 3 + 32 * K * n * G ^ 2 + 2 * K₀ * n * G := by ring
  have hG : 32 * K * n * G ^ 2 ≤ 32 * K * n * G ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hl1 (by norm_num))
  have hG' : 8 * K * n ≤ 8 * K * n * G ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
  have e4 : (54 * Cn + 58) * K * n * G ^ 3 =
      (54 * Cn + 18) * K * n * G ^ 3 + 32 * K * n * G ^ 3 + 8 * K * n * G ^ 3 := by ring
  have hm2 : 2 * c.lin (mapSize M) ≤ 8 * K * n := by
    have : 2 * (4 * K * n) = 8 * K * n := by ring
    omega
  have hA := h1.trans (hY.trans e3.le)
  rw [e4]
  calc arunLCost M c τ [] (rotPerm M) + 2 * c.lin (mapSize M)
      ≤ ((54 * Cn + 18) * K * n * G ^ 3 + 32 * K * n * G ^ 2 + 2 * K₀ * n * G) + 8 * K * n :=
        Nat.add_le_add hA hm2
    _ ≤ _ := by linarith

end BKMNW

end PlanarFlow
