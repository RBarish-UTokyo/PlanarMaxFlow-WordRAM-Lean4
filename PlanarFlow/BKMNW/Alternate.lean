module

public import PlanarFlow.BKMNW.LocalCost

/-!
# The balance of the article: alternation, slack, small pieces

`PlanarFlow.BKMNW.ADec.Bal` asks every split to give each child at most two thirds of the darts
of its parent. The recursion of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J.
Comput. 46(4), 2017, Algorithm 1, line 2) does less: following Fakcharoenphol and Rao, it
alternates splits balanced in size and splits balanced in the number of holes, which need not
balance size; and a cycle separator of Miller balances the weight strictly on each side of the
cycle, so that once the darts along the cycle are distributed a child has at most
`2 m / 3 + O(√m)` darts, which is at most `3 m / 4` only for `m` above a constant.

`ADec.BalA κ η s` is that weaker balance: the conditions `ADec.Core` (siblings disjoint and
nonempty, separators with at most `η + 1` parts off the holes of `k ≤ κ √m` darts each with `2 k ≤
m`, at most `η` holes touching every piece), and on every branch no two consecutive splits
unbalanced in size, where a split of a piece of `m` darts is balanced in size when `m ≤ s` or each
child has at most `3 m / 4` darts (`ADec.SizeBal`). The flag `free` says whether the split at the
root may be unbalanced.

* `ADec.Bal.balA`: a balanced decomposition meets `BalA` for all `s`.
* `ADec.BalA.pow`, `ADec.BalA.depth_le`: the depth of a decomposition of `m ≥ 1` darts meeting
  `BalA` is at most `5 lg m + s + 5`.
* `runL_costA`: **the cost of the algorithm on the piece maps is `O(n log³ n)`** on a decomposition
  meeting `BalA`: at most `(s + 11)² ((27 Cₙ + 25) K n lg³ n + K₀ n lg n)` with `Cₙ = (η + 1) (25 +
  7 κ² + 2 η (34 + 14 κ²))`, under the cost bounds `SubCosts.Bounds` of the subroutines.

The existence of decompositions meeting `BalA` together with the hypotheses of correctness is
discussed at `PlanarFlow.BKMNW.BalDecA`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv CombMap Orbit

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

namespace ADec

/-- A split of a piece of `m` darts into children of `a` and `b` darts is **balanced in size**
when the piece is small (`m ≤ s`) or each child has at most three quarters of the darts. -/
def SizeBal (s m a b : ℕ) : Prop := m ≤ s ∨ (4 * a ≤ 3 * m ∧ 4 * b ≤ 3 * m)

variable (M) in
/-- **The balance of the article**: the conditions `Core`, and on every branch no two
consecutive splits unbalanced in size (`SizeBal`); a split may be unbalanced in size only if
`free` holds, and then the splits of its children must be balanced in size. -/
def BalA (κ η s : ℕ) : Bool → ADec M → List (Finset V) → Prop
  | _, leaf _, _ => True
  | free, node l r π, Hs =>
      Disjoint l.piece r.piece ∧ 0 < l.piece.card ∧ 0 < r.piece.card ∧
      π.Short κ η (l.piece ∪ r.piece).card ∧ nTouch M (l.piece ∪ r.piece) Hs ≤ η ∧
      ((SizeBal s (l.piece ∪ r.piece).card l.piece.card r.piece.card ∧
          l.BalA κ η s true (childHoles Hs π.path.mverts) ∧
          r.BalA κ η s true (childHoles Hs π.path.mverts)) ∨
        (free = true ∧ l.BalA κ η s false (childHoles Hs π.path.mverts) ∧
          r.BalA κ η s false (childHoles Hs π.path.mverts)))

/-- A decomposition meeting `BalA` meets `Core`. -/
lemma BalA.core {κ η s : ℕ} :
    ∀ {τ : ADec M} {Hs : List (Finset V)} {b : Bool}, τ.BalA M κ η s b Hs → τ.Core M κ η Hs
  | leaf _, _, _, _ => trivial
  | node _ _ _, _, _, ⟨h1, h2, h3, h4, h6, h⟩ => by
    rcases h with ⟨-, hl, hr⟩ | ⟨-, hl, hr⟩
    · exact ⟨hl.core, hr.core, h1, h2, h3, h4, h6⟩
    · exact ⟨hl.core, hr.core, h1, h2, h3, h4, h6⟩

/-- **A balanced decomposition meets the balance of the article**, for every `s` and `free`. -/
lemma Bal.balA {κ η : ℕ} (s : ℕ) :
    ∀ {τ : ADec M} {Hs : List (Finset V)} (b : Bool), τ.Bal M κ η Hs → τ.BalA M κ η s b Hs
  | leaf _, _, _, _ => trivial
  | node _ _ _, _, _, ⟨hl, hr, h1, h2, h3, b0, b1, h4, h6⟩ =>
    ⟨h1, h2, h3, h4, h6, Or.inl ⟨Or.inr ⟨by omega, by omega⟩, hl.balA s true,
      hr.balA s true⟩⟩

lemma pow_le_of_le {q qc mc : ℕ} (h : 4 ^ qc ≤ 3 ^ qc * mc) (hq : q ≤ qc) :
    4 ^ q ≤ 3 ^ q * mc := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hq
  have h1 : 4 ^ q * 3 ^ t ≤ 4 ^ q * 4 ^ t :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) t)
  have h2 : 4 ^ q * 3 ^ t ≤ 3 ^ q * mc * 3 ^ t := by
    calc 4 ^ q * 3 ^ t ≤ 4 ^ q * 4 ^ t := h1
      _ = 4 ^ (q + t) := by ring
      _ ≤ 3 ^ (q + t) * mc := h
      _ = 3 ^ q * mc * 3 ^ t := by ring
  exact Nat.le_of_mul_le_mul_right h2 (by positivity)

lemma pow_le_of_step {q qc mc m : ℕ} (h : 4 ^ qc ≤ 3 ^ qc * mc) (hq : q ≤ qc + 1)
    (hm : 4 * mc ≤ 3 * m) : 4 ^ q ≤ 3 ^ q * m := by
  rcases Nat.lt_or_ge qc q with hlt | hle
  · have e : q = qc + 1 := by omega
    subst e
    calc 4 ^ (qc + 1) = 4 * 4 ^ qc := by ring
      _ ≤ 4 * (3 ^ qc * mc) := Nat.mul_le_mul_left _ h
      _ = 3 ^ qc * (4 * mc) := by ring
      _ ≤ 3 ^ qc * (3 * m) := Nat.mul_le_mul_left _ hm
      _ = 3 ^ (qc + 1) * m := by ring
  · exact (pow_le_of_le h hle).trans (Nat.mul_le_mul_left _ (by omega))

/-- **The depth of a decomposition meeting `BalA`**: with `q = (d - s - [free]) / 2` for its depth
`d`, `(4/3)^q ≤ m` for its number `m ≥ 1` of darts. -/
theorem BalA.pow {κ η s : ℕ} :
    ∀ {τ : ADec M} {Hs : List (Finset V)} {b : Bool}, τ.BalA M κ η s b Hs →
      0 < τ.piece.card →
      4 ^ ((τ.depth - s - b.toNat) / 2) ≤ 3 ^ ((τ.depth - s - b.toNat) / 2) * τ.piece.card
  | leaf _, _, _, _, hpos => by
    simp only [depth, Nat.zero_sub, Nat.zero_div, pow_zero, one_mul]; omega
  | node l r π, Hs, b, h, hpos => by
    have hcore : (node l r π).Core M κ η Hs := BalA.core h
    obtain ⟨hlr, hl0, hr0, -, -, hcase⟩ := h
    have hcard : (l.piece ∪ r.piece).card = l.piece.card + r.piece.card :=
      card_union_of_disjoint hlr
    simp only [piece, depth] at hpos ⊢
    rcases hcase with ⟨hsb, hl, hr⟩ | ⟨hb, hl, hr⟩
    · rcases hsb with hsm | ⟨b0, b1⟩
      · have := Core.depth_lt hcore hpos
        simp only [depth, piece] at this
        have e : (max l.depth r.depth + 1 - s - b.toNat) / 2 = 0 := by omega
        rw [e]; simp only [pow_zero, one_mul]; omega
      · have il := BalA.pow hl hl0
        have ir := BalA.pow hr hr0
        simp only [Bool.toNat_true] at il ir
        rcases le_total l.depth r.depth with hle | hle
        · rw [max_eq_right hle]
          exact pow_le_of_step ir (by omega) b1
        · rw [max_eq_left hle]
          exact pow_le_of_step il (by omega) b0
    · subst hb
      have il := BalA.pow hl hl0
      have ir := BalA.pow hr hr0
      simp only [Bool.toNat_false, Nat.sub_zero, Bool.toNat_true] at il ir ⊢
      rcases le_total l.depth r.depth with hle | hle
      · rw [max_eq_right hle]
        exact (pow_le_of_le ir (by omega)).trans (Nat.mul_le_mul_left _ (by omega))
      · rw [max_eq_left hle]
        exact (pow_le_of_le il (by omega)).trans (Nat.mul_le_mul_left _ (by omega))

/-- **The depth of a decomposition of `m ≥ 1` darts meeting `BalA` is at most `5 lg m + s + 5`**
(with `lg m = ⌊log₂ m⌋ + 1`). -/
theorem BalA.depth_le {κ η s : ℕ} {τ : ADec M} {Hs : List (Finset V)} {b : Bool}
    (h : τ.BalA M κ η s b Hs) (hpos : 0 < τ.piece.card) :
    τ.depth + 1 ≤ 5 * lg τ.piece.card + s + 6 := by
  have h1 := h.pow hpos
  generalize hq : (τ.depth - s - b.toNat) / 2 = q at h1
  generalize τ.piece.card = m at h1 hpos ⊢
  have h5 : 4 ^ (5 * (q / 5)) ≤ 3 ^ (5 * (q / 5)) * m := pow_le_of_le h1 (Nat.mul_div_le q 5)
  have h6 : 4 ^ (q / 5) * 3 ^ (5 * (q / 5)) ≤ 4 ^ (5 * (q / 5)) := by
    rw [pow_mul, pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (by norm_num) _
  have h7 : 4 ^ (q / 5) ≤ m :=
    Nat.le_of_mul_le_mul_right (by rw [mul_comm m]; exact h6.trans h5) (by positivity)
  have h8 : 2 ^ (2 * (q / 5)) ≤ m := by rw [pow_mul]; exact h7
  have h9 := Nat.le_log_of_pow_le (by norm_num) h8
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  unfold lg
  omega

end ADec

/-- **The cost of Algorithm 1 on the piece maps is `O(n log³ n)` on a decomposition meeting the
balance of the article** (`ADec.BalA`): on a plane map with `n ≥ 1` darts, at most `(s + 11)² ((27
Cₙ + 25) K n lg³ n + K₀ n lg n)` with `Cₙ = (η + 1) (25 + 7 κ² + 2 η (34 + 14 κ²))`, under the cost
bounds `SubCosts.Bounds` of the subroutines. -/
theorem runL_costA (hM : M.IsPlane) {κ η s : ℕ} {b : Bool} {τ : ADec M} (hall : τ.piece = univ)
    (hbal : τ.BalA M κ η s b []) {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    (hD : 0 < Fintype.card D) :
    runLCost M c τ ≤ (s + 11) ^ 2 * ((27 * ((η + 1) * (25 + 7 * κ ^ 2 +
      2 * η * (34 + 14 * κ ^ 2))) + 25) * K * Fintype.card D * lg (Fintype.card D) ^ 3 +
        K₀ * Fintype.card D * lg (Fintype.card D)) := by
  have hpos : 0 < τ.piece.card := by rw [hall, card_univ]; exact hD
  have hdep := hbal.depth_le hpos
  rw [hall, card_univ] at hdep
  generalize hn : Fintype.card D = n at hD hdep
  have hcn : τ.piece.card = n := by rw [hall, card_univ, hn]
  have h1 := arunLCost_le (n := n) (L := τ.depth) (σ := rotPerm M) hc hbal.core hpos (by omega)
    (by simp)
  rw [hcn] at h1
  have hl1 := one_le_lg n
  have hlg3 : lg (3 * n) ^ 2 ≤ 9 * lg n ^ 2 := by have := lg_three_mul n; nlinarith
  have hmap : c.lin (mapSize M) ≤ 4 * K * n := by
    have := mapSize_le_of_isPlane hM
    rw [hn] at this
    exact (hc.lin _).trans (by nlinarith)
  unfold runLCost
  unfold callBound at h1
  generalize (η + 1) * (25 + 7 * κ ^ 2 + 2 * η * (34 + 14 * κ ^ 2)) = Cn at h1 ⊢
  generalize τ.depth + 1 = X at h1 hdep
  generalize lg n = G at hl1 hdep hlg3 ⊢
  -- `X ≤ Y G` with `Y = s + 11`
  have hX : X ≤ (s + 11) * G := by nlinarith
  have hY : 1 ≤ s + 11 := by omega
  generalize s + 11 = Y at hX hY ⊢
  have hA : (3 * Cn + 1) * K * lg (3 * n) ^ 2 + 8 * K * X + K₀ ≤
      (27 * Cn + 9) * K * G ^ 2 + 8 * K * X + K₀ := by
    have : (3 * Cn + 1) * K * lg (3 * n) ^ 2 ≤ (3 * Cn + 1) * K * (9 * G ^ 2) :=
      Nat.mul_le_mul_left _ hlg3
    nlinarith
  have hB := (h1.trans (Nat.mul_le_mul_right _ hA))
  have hG2 : G ^ 2 ≤ G ^ 3 := Nat.pow_le_pow_right hl1 (by norm_num)
  have hG1 : G ≤ G ^ 3 := by nlinarith
  have hYY : Y ≤ Y ^ 2 := by nlinarith
  -- the three terms
  have t1 : (27 * Cn + 9) * K * G ^ 2 * (n * X) ≤ Y ^ 2 * ((27 * Cn + 9) * K * n * G ^ 3) := by
    have : (27 * Cn + 9) * K * G ^ 2 * (n * X) ≤ (27 * Cn + 9) * K * G ^ 2 * (n * (Y * G)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
    have e : (27 * Cn + 9) * K * G ^ 2 * (n * (Y * G)) =
        Y * ((27 * Cn + 9) * K * n * G ^ 3) := by ring
    have := Nat.mul_le_mul_right ((27 * Cn + 9) * K * n * G ^ 3) hYY
    omega
  have t2 : 8 * K * X * (n * X) ≤ Y ^ 2 * (8 * K * n * G ^ 3) := by
    have hXX : X * X ≤ (Y * G) * (Y * G) := Nat.mul_le_mul hX hX
    have : 8 * K * X * (n * X) = 8 * K * n * (X * X) := by ring
    have e : 8 * K * n * ((Y * G) * (Y * G)) = Y ^ 2 * (8 * K * n * G ^ 2) := by ring
    have : 8 * K * n * (X * X) ≤ 8 * K * n * ((Y * G) * (Y * G)) :=
      Nat.mul_le_mul_left _ hXX
    have : Y ^ 2 * (8 * K * n * G ^ 2) ≤ Y ^ 2 * (8 * K * n * G ^ 3) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hG2)
    omega
  have t3 : K₀ * (n * X) ≤ Y ^ 2 * (K₀ * n * G) := by
    have : K₀ * (n * X) ≤ K₀ * (n * (Y * G)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hX)
    have e : K₀ * (n * (Y * G)) = Y * (K₀ * n * G) := by ring
    have := Nat.mul_le_mul_right (K₀ * n * G) hYY
    omega
  have t4 : 2 * c.lin (mapSize M) ≤ Y ^ 2 * (8 * K * n * G ^ 3) := by
    have : 8 * K * n ≤ 8 * K * n * G ^ 3 := Nat.le_mul_of_pos_right _ (by positivity)
    have : 8 * K * n * G ^ 3 ≤ Y ^ 2 * (8 * K * n * G ^ 3) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    have : 2 * (4 * K * n) = 8 * K * n := by ring
    omega
  have e : ((27 * Cn + 9) * K * G ^ 2 + 8 * K * X + K₀) * (n * X) =
      (27 * Cn + 9) * K * G ^ 2 * (n * X) + 8 * K * X * (n * X) + K₀ * (n * X) := by ring
  have e2 : Y ^ 2 * ((27 * Cn + 25) * K * n * G ^ 3 + K₀ * n * G) =
      Y ^ 2 * ((27 * Cn + 9) * K * n * G ^ 3) + Y ^ 2 * (8 * K * n * G ^ 3) +
        Y ^ 2 * (K₀ * n * G) + Y ^ 2 * (8 * K * n * G ^ 3) := by ring
  rw [e] at hB
  rw [e2]
  omega

end BKMNW

end PlanarFlow
