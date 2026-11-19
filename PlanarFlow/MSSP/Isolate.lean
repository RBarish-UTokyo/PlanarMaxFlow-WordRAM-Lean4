module

public import PlanarFlow.MSSP.Perturb

/-!
# Unique shortest paths with word-sized lengths: isolation in plane maps

`PlanarFlow/MSSP/Perturb.lean` obtains the unique shortest paths assumed by the multiple-source
shortest path algorithm (`PlanarFlow.MSSP.Hyp`) by the perturbation `2^c ℓ + 2^(index)`, whose
numbers have `Θ(m)` bits. This file gives a **deterministic perturbation with polynomially
bounded integers**, based on planarity (the "Green's theorem" isolation of Tewari and
Vinodchandran for planar graphs): a weight `w` on the darts, antisymmetric, whose *curl*
`Σ_{face d = f} w d` is positive at every face but one (`IsoW`), has a nonzero sum on every simple
cycle (`circ_ne_zero`): by the winding function of the cycle
(`PlanarFlow.CombMap.exists_winding`), the sum of `w` on the cycle is, up to sign, the sum of the
curls of the faces on one side, and one of the two sides avoids the exceptional face.

**The isolating lengths** (`isoLen`), for nonnegative lengths `ℓ`, a bound `n ≥ #V`, an injective
numbering `ι < m` of the darts and `|w| ≤ B`:

  `isoLen ℓ d = N₁ ℓ d + N₂ + N₃ (w d + B) + ι d`,
  `N₃ = n m + 1`, `N₂ = N₃ (2 B n + 1)`, `N₁ = N₂ (n + 1)`

(`isoN1`, `isoN2`, `isoN3`). On a walk without repeated vertices the four terms are separated
(`lex_of_wlen_eq`): equal lengths mean equal lengths `ℓ`, equal numbers of darts, equal sums of
`w` and equal sums of `ι`.

* `isoLen_uniqTight`: **unique tight arcs** for `isoLen ℓ`: two shortest paths to the same vertex
  with different last darts would contain two internally disjoint shortest paths between the same
  vertices; together they form a simple cycle of the map, on which the sum of `w` is not zero
  (`circ_ne_zero`), or two parallel darts, which have different numbers `ι`.
* `isoLen_dist_bounds`, `isoLen_dist_div`: **the distances are the isolated distances divided by
  `N₁`** (`N₁ dist ≤ dist' < N₁ (dist + 1)`).
* `HypNN.hypIso`: the isolating lengths meet the article's assumptions; `odist_isoLen`: the
  answers for `isoLen ℓ`, divided by `N₁`, are those for `ℓ`; `dkpw_iso`: so are the answers of
  the data structure; `HypNN.exists_iso`: all of it for `n = #V`, `m = #D`, `B = #F` and the
  numbering of the darts.
* `isoLen_lt`: the isolating lengths are below `N₁ (ℓ d + 1)`: integers of word size, for
  `n = #V`, `m = #D`, `B = #F` a polynomial in the size of the map times the largest length.
* `exists_isoW`: **an isolating weight exists with `|w| ≤ #F`** on every plane map (the sum, over
  the faces `y ≠ f₀`, of the unit flows of simple dual paths from `y` to `f₀`); a spanning tree of
  the dual gives one in linear time (the flow on the parent dart of a face is the size of its
  subtree).

No randomness and no number of more than `O(log n + log (max ℓ + 1))` bits is involved.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace MSSP

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### Isolating weights -/

/-- The *curl* of a weight on the darts at a face: its sum along the boundary of the face. -/
def curl (M : CombMap D V F) (w : D → ℤ) (f : F) : ℤ := ∑ d with M.face d = f, w d

/-- `w` is an **isolating weight** with the exceptional face `f₀`: antisymmetric, with a positive
curl at every other face. -/
structure IsoW (M : CombMap D V F) (f₀ : F) (w : D → ℤ) : Prop where
  antisymm : M.IsAntisymm w
  curl_pos : ∀ f, f ≠ f₀ → 1 ≤ curl M w f

variable {M : CombMap D V F}

lemma sum_rev {β : Type*} [AddCommMonoid β] (h : D → β) : ∑ d, h (M.rev d) = ∑ d, h d :=
  Equiv.sum_comp (Function.Involutive.toPerm M.rev M.rev_rev) h

lemma sum_antisymm_eq_zero {w : D → ℤ} (hw : M.IsAntisymm w) : ∑ d, w d = 0 := by
  have hw' : ∀ d, w (M.rev d) = - w d := hw
  have h := sum_rev (M := M) w
  simp only [hw', Finset.sum_neg_distrib] at h
  linarith

lemma sum_face_mul (ψ : F → ℤ) (w : D → ℤ) :
    ∑ d, ψ (M.face d) * w d = ∑ f, ψ f * curl M w f := by
  rw [← Finset.sum_fiberwise Finset.univ M.face]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [curl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun d hd => by rw [(Finset.mem_filter.1 hd).2]

lemma sum_cob_mul {w : D → ℤ} (hw : M.IsAntisymm w) (φ : F → ℤ) :
    ∑ d, M.cob φ d * w d = -2 * ∑ d, φ (M.face d) * w d := by
  have hw' : ∀ d, w (M.rev d) = - w d := hw
  have h := sum_rev (M := M) fun d => φ (M.face (M.rev d)) * w d
  simp only [M.rev_rev, hw'] at h
  simp only [CombMap.cob, sub_mul, Finset.sum_sub_distrib]
  have : ∑ d, φ (M.face (M.rev d)) * w d = - ∑ d, φ (M.face d) * w d := by
    rw [← h]; simp
  rw [this]; ring

lemma sum_cyc_mul {w : D → ℤ} (hw : M.IsAntisymm w) (n : ℕ) (c : ℕ → D) :
    ∑ d, M.cyc n c d * w d = 2 * ∑ t ∈ range n, w (c t) := by
  have e1 : ∀ e : D → D, ∑ d, (#{t ∈ range n | c t = e d} : ℤ) * w d =
      ∑ t ∈ range n, ∑ d, if c t = e d then w d else 0 := by
    intro e
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.natCast_card_filter, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp
  have e2 := e1 id
  have e3 := e1 M.rev
  simp only [id_eq, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at e2
  have e4 : ∀ t, (∑ d, if c t = M.rev d then w d else 0) = - w (c t) := by
    intro t
    have : ∀ d, (c t = M.rev d) ↔ (M.rev (c t) = d) := fun d =>
      ⟨fun h => by rw [h, M.rev_rev], fun h => by rw [← h, M.rev_rev]⟩
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact hw (c t)
  simp only [e4, Finset.sum_neg_distrib] at e3
  simp only [CombMap.cyc, sub_mul, Finset.sum_sub_distrib]
  rw [e2, e3]; ring

/-- **The winding function of a simple cycle takes two values**: `φ (face (c 0))` and one more. -/
lemma winding_two (hM : M.IsPlane) (hrot : M.RotTrans) {n : ℕ} {c : ℕ → D}
    (hC : M.IsSimpleCycle n c) {φ : F → ℤ}
    (hφ : ∀ d, φ (M.face (M.rev d)) = φ (M.face d) + M.cyc n c d) (f : F) :
    φ f = φ (M.face (c 0)) ∨ φ f = φ (M.face (c 0)) + 1 := by
  induction hM.dualConn (M.face (c 0)) f with
  | refl => exact Or.inl rfl
  | @tail a b _ hab ih =>
    obtain ⟨d, rfl, rfl⟩ := hab
    by_cases h1 : ∃ t < n, c t = d
    · obtain ⟨t, ht, rfl⟩ := h1
      right
      rw [hφ, hC.cyc_cycle ht, face_cycle hC hφ hrot ht]
    · by_cases h2 : ∃ t < n, c t = M.rev d
      · obtain ⟨t, ht, e⟩ := h2
        left
        rw [← e, face_cycle hC hφ hrot ht]
      · push Not at h1 h2
        rw [hφ, hC.cyc_eq_zero h1 h2, add_zero]
        exact ih

/-- A `0`/`1` function on the faces, `0` at the exceptional face and `1` somewhere, has a
positive sum against the curls. -/
lemma sum_curl_pos {f₀ : F} {w : D → ℤ} (hw : IsoW M f₀ w) {χ : F → ℤ}
    (h01 : ∀ f, χ f = 0 ∨ χ f = 1) (h0 : χ f₀ = 0) {f₁ : F} (h1 : χ f₁ = 1) :
    0 < ∑ f, χ f * curl M w f := by
  have hne : f₁ ≠ f₀ := fun e => by rw [e, h0] at h1; exact zero_ne_one h1
  have hnn : ∀ f ∈ (Finset.univ : Finset F), 0 ≤ χ f * curl M w f := by
    intro f _
    by_cases hf : f = f₀
    · rw [hf, h0, zero_mul]
    · have := hw.curl_pos f hf
      rcases h01 f with h | h <;> rw [h] <;> omega
  have := Finset.single_le_sum hnn (Finset.mem_univ f₁)
  have := hw.curl_pos f₁ hne
  rw [h1, one_mul] at *
  omega

/-- **Green's theorem for an isolating weight**: the sum of `w` along a simple cycle of a plane
map with transitive rotations is not zero. -/
theorem circ_ne_zero (hM : M.IsPlane) (hrot : M.RotTrans) {f₀ : F} {w : D → ℤ}
    (hw : IsoW M f₀ w) {n : ℕ} {c : ℕ → D} (hC : M.IsSimpleCycle n c) :
    ∑ t ∈ range n, w (c t) ≠ 0 := by
  intro h0
  obtain ⟨φ, hφ⟩ := exists_winding hM hC
  have hcob : ∀ d, M.cyc n c d = M.cob φ d := fun d => by
    rw [CombMap.cob, hφ]; ring
  have e1 := sum_cyc_mul hw.antisymm n c
  simp only [hcob, sum_cob_mul hw.antisymm, h0, mul_zero] at e1
  -- `Σ φ (face d) w d = 0`
  have e2 : ∑ d, φ (M.face d) * w d = 0 := by linarith
  set A := φ (M.face (c 0)) with hA
  have h2 := winding_two hM hrot hC hφ
  have hs0 := sum_antisymm_eq_zero hw.antisymm
  have hsc : ∑ f, curl M w f = 0 := by
    have := sum_face_mul (M := M) (fun _ => (1 : ℤ)) w
    simp only [one_mul] at this
    rw [← this, hs0]
  have hψ : ∑ f, (φ f - A) * curl M w f = 0 := by
    have h1 := sum_face_mul (M := M) φ w
    rw [e2] at h1
    have : ∑ f, (φ f - A) * curl M w f = ∑ f, φ f * curl M w f - A * ∑ f, curl M w f := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun f _ => by ring
    rw [this, ← h1, hsc]; ring
  have hface1 : φ (M.face (M.rev (c 0))) - A = 1 := by
    rw [hφ, hC.cyc_cycle hC.pos]; ring
  rcases h2 f₀ with h | h
  · have := sum_curl_pos hw (χ := fun f => φ f - A) (fun f => by rcases h2 f with e | e <;> omega)
      (show φ f₀ - A = 0 by omega) hface1
    rw [hψ] at this; exact lt_irrefl _ this
  · have hχ : ∑ f, (1 - (φ f - A)) * curl M w f = 0 := by
      have : ∑ f, (1 - (φ f - A)) * curl M w f =
          ∑ f, curl M w f - ∑ f, (φ f - A) * curl M w f := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun f _ => by ring
      rw [this, hsc, hψ, sub_zero]
    have := sum_curl_pos hw (χ := fun f => 1 - (φ f - A))
      (fun f => by rcases h2 f with e | e <;> omega) (show 1 - (φ f₀ - A) = 0 by omega)
      (f₁ := M.face (c 0)) (show 1 - (φ (M.face (c 0)) - A) = 1 by omega)
    rw [hχ] at this; exact lt_irrefl _ this

/-! ### The isolating lengths -/

/-- The factor of the hop count and the weights: `n m + 1`. -/
def isoN3 (n m : ℕ) : ℕ := n * m + 1

/-- The factor of the number of darts: `N₃ (2 B n + 1)`. -/
def isoN2 (n m B : ℕ) : ℕ := isoN3 n m * (2 * B * n + 1)

/-- The factor of the lengths: `N₂ (n + 1)`. -/
def isoN1 (n m B : ℕ) : ℕ := isoN2 n m B * (n + 1)

/-- **The isolating lengths**: `N₁ ℓ d + N₂ + N₃ (w d + B) + ι d`. -/
def isoLen (n m B : ℕ) (w : D → ℤ) (ι : D → ℕ) (ℓ : D → ℤ) (d : D) : ℤ :=
  (isoN1 n m B : ℤ) * ℓ d + isoN2 n m B + isoN3 n m * (w d + B) + ι d

lemma isoN3_pos (n m : ℕ) : 0 < isoN3 n m := Nat.succ_pos _

lemma isoN2_pos (n m B : ℕ) : 0 < isoN2 n m B := Nat.mul_pos (isoN3_pos n m) (Nat.succ_pos _)

lemma isoN1_pos (n m B : ℕ) : 0 < isoN1 n m B := Nat.mul_pos (isoN2_pos n m B) (Nat.succ_pos _)

/-- Two numbers written `N x + r` with `0 ≤ r < N` have the same digits. -/
lemma lex_eq {N x y r s : ℤ} (h : N * x + r = N * y + s) (hr : 0 ≤ r) (hr' : r < N)
    (hs : 0 ≤ s) (hs' : s < N) : x = y ∧ r = s := by
  have hxy : x = y := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : N * (x + 1) ≤ N * y := mul_le_mul_of_nonneg_left (by omega) (by omega)
      nlinarith
    · have : N * (y + 1) ≤ N * x := mul_le_mul_of_nonneg_left (by omega) (by omega)
      nlinarith
  subst hxy; exact ⟨rfl, by linarith⟩

section Iso

variable {S : Finset D}

/-- The sum of `f` over a list of darts of `S`. -/
def lsum (f : D → ℤ) (L : List {d // d ∈ S}) : ℤ := (L.map fun a => f a.1).sum

@[simp] lemma lsum_nil (f : D → ℤ) : lsum f ([] : List {d // d ∈ S}) = 0 := rfl

@[simp] lemma lsum_cons (f : D → ℤ) (a : {d // d ∈ S}) (L : List {d // d ∈ S}) :
    lsum f (a :: L) = f a.1 + lsum f L := by simp [lsum]

lemma lsum_bounds {f : D → ℤ} {lo hi : ℤ} (h : ∀ d, lo ≤ f d ∧ f d ≤ hi)
    (L : List {d // d ∈ S}) : L.length * lo ≤ lsum f L ∧ lsum f L ≤ L.length * hi := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [lsum_cons, List.length_cons]; push_cast
    have := h a.1; constructor <;> nlinarith [ih.1, ih.2, this.1, this.2]

lemma lsum_add_const (f : D → ℤ) (B : ℤ) (L : List {d // d ∈ S}) :
    lsum (fun d => f d + B) L = lsum f L + B * L.length := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [lsum_cons, ih, List.length_cons]; push_cast; ring

variable {M : CombMap D V F} {n m B : ℕ} {w : D → ℤ} {ι : D → ℕ} {ℓ : D → ℤ}

lemma wlen_iso (L : List {d // d ∈ S}) :
    wlen (pieceGraph M S (isoLen n m B w ι ℓ)) L =
      isoN1 n m B * wlen (pieceGraph M S ℓ) L + isoN2 n m B * L.length +
        isoN3 n m * lsum (fun d => w d + B) L + lsum (fun d => (ι d : ℤ)) L := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [wlen_cons, ih, lsum_cons, List.length_cons]
    simp only [pieceGraph, isoLen]; push_cast; ring

variable (hB : ∀ d, |w d| ≤ B) (hιm : ∀ d, ι d < m)
include hB hιm

/-- The part of the isolated length below `N₂`: `N₃ (Σ (w + B)) + Σ ι`. -/
lemma low_bounds {L : List {d // d ∈ S}} (hL : L.length ≤ n) :
    0 ≤ (isoN3 n m : ℤ) * lsum (fun d => w d + B) L + lsum (fun d => (ι d : ℤ)) L ∧
      (isoN3 n m : ℤ) * lsum (fun d => w d + B) L + lsum (fun d => (ι d : ℤ)) L <
        isoN2 n m B := by
  have h1 := lsum_bounds (lo := 0) (hi := 2 * B) (f := fun d => w d + B)
    (fun d => by have := abs_le.1 (hB d); constructor <;> linarith) L
  have h2 := lsum_bounds (lo := 0) (hi := m) (f := fun d => (ι d : ℤ))
    (fun d => by have := hιm d; constructor <;> omega) L
  have hL' : (L.length : ℤ) ≤ n := by exact_mod_cast hL
  have hN3 : (0 : ℤ) < isoN3 n m := by exact_mod_cast isoN3_pos n m
  have e3 : (isoN3 n m : ℤ) = n * m + 1 := by simp [isoN3]
  have e2 : (isoN2 n m B : ℤ) = isoN3 n m * (2 * B * n + 1) := by simp [isoN2]
  simp only [mul_zero] at h1 h2
  have hB0 : (0 : ℤ) ≤ B := by exact_mod_cast Nat.zero_le B
  have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast Nat.zero_le m
  have a1 : lsum (fun d => w d + B) L ≤ 2 * B * n := by nlinarith
  have a2 : lsum (fun d => (ι d : ℤ)) L ≤ m * n := by nlinarith
  have a3 : (isoN3 n m : ℤ) * lsum (fun d => w d + B) L ≤ isoN3 n m * (2 * B * n) :=
    mul_le_mul_of_nonneg_left a1 hN3.le
  constructor
  · have := mul_nonneg hN3.le h1.1; linarith
  · rw [e2]; nlinarith

/-- The part of the isolated length below `N₁`. -/
lemma mid_bounds {L : List {d // d ∈ S}} (hL : L.length ≤ n) :
    0 ≤ (isoN2 n m B : ℤ) * L.length + (isoN3 n m * lsum (fun d => w d + B) L +
        lsum (fun d => (ι d : ℤ)) L) ∧
      (isoN2 n m B : ℤ) * L.length + (isoN3 n m * lsum (fun d => w d + B) L +
        lsum (fun d => (ι d : ℤ)) L) < isoN1 n m B := by
  obtain ⟨h1, h2⟩ := low_bounds hB hιm hL
  have hL' : (L.length : ℤ) ≤ n := by exact_mod_cast hL
  have hN2 : (0 : ℤ) < isoN2 n m B := by exact_mod_cast isoN2_pos n m B
  have e1 : (isoN1 n m B : ℤ) = isoN2 n m B * (n + 1) := by simp [isoN1]
  have : (isoN2 n m B : ℤ) * L.length ≤ isoN2 n m B * n := mul_le_mul_of_nonneg_left hL' hN2.le
  have : (0 : ℤ) ≤ isoN2 n m B * L.length := mul_nonneg hN2.le (by positivity)
  constructor
  · linarith
  · rw [e1]; linarith

/-- **The four terms of the isolated length are separated** on walks of at most `n` darts. -/
lemma lex_of_wlen_eq {L₁ L₂ : List {d // d ∈ S}} (h₁ : L₁.length ≤ n) (h₂ : L₂.length ≤ n)
    (h : wlen (pieceGraph M S (isoLen n m B w ι ℓ)) L₁ =
      wlen (pieceGraph M S (isoLen n m B w ι ℓ)) L₂) :
    wlen (pieceGraph M S ℓ) L₁ = wlen (pieceGraph M S ℓ) L₂ ∧ L₁.length = L₂.length ∧
      lsum w L₁ = lsum w L₂ ∧ lsum (fun d => (ι d : ℤ)) L₁ = lsum (fun d => (ι d : ℤ)) L₂ := by
  rw [wlen_iso, wlen_iso] at h
  have m1 := mid_bounds hB hιm h₁
  have m2 := mid_bounds hB hιm h₂
  have l1 := low_bounds hB hιm h₁
  have l2 := low_bounds hB hιm h₂
  obtain ⟨e1, e2⟩ := lex_eq (N := isoN1 n m B) (x := wlen (pieceGraph M S ℓ) L₁)
    (y := wlen (pieceGraph M S ℓ) L₂) (by linarith) m1.1 m1.2 m2.1 m2.2
  obtain ⟨e3, e4⟩ := lex_eq (N := isoN2 n m B) (x := L₁.length) (y := L₂.length) e2
    l1.1 l1.2 l2.1 l2.2
  have h3 : (L₁.length : ℤ) = L₂.length := e3
  have hι1 := lsum_bounds (lo := 0) (hi := m) (f := fun d => (ι d : ℤ))
    (fun d => by have := hιm d; constructor <;> omega) L₁
  have hι2 := lsum_bounds (lo := 0) (hi := m) (f := fun d => (ι d : ℤ))
    (fun d => by have := hιm d; constructor <;> omega) L₂
  have hN3 : (n : ℤ) * m < isoN3 n m := by simp [isoN3]
  have hl1 : (L₁.length : ℤ) ≤ n := by exact_mod_cast h₁
  have hl2 : (L₂.length : ℤ) ≤ n := by exact_mod_cast h₂
  have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast Nat.zero_le m
  simp only [mul_zero] at hι1 hι2
  obtain ⟨e5, e6⟩ := lex_eq (N := isoN3 n m) (x := lsum (fun d => w d + B) L₁)
    (y := lsum (fun d => w d + B) L₂) e4 hι1.1 (by nlinarith) hι2.1 (by nlinarith)
  refine ⟨e1, by exact_mod_cast e3, ?_, e6⟩
  rw [lsum_add_const, lsum_add_const, h3] at e5
  linarith

end Iso

/-! ### Unique tight arcs -/

lemma map_src_concat {X A : Type*} {G : Digraph X A} {x y : X} {L : List A} {a : A}
    (h : LWalk G x y (L ++ [a])) : (L ++ [a]).map G.src = x :: L.map G.dst := by
  induction L generalizing x with
  | nil =>
    simp only [List.nil_append] at h
    simp [(LWalk.cons_iff.1 h).1]
  | cons e L ih =>
    rw [List.cons_append] at h
    obtain ⟨rfl, h'⟩ := LWalk.cons_iff.1 h
    rw [List.cons_append, List.map_cons, ih h', List.map_cons]

lemma sum_range_getD (f : D → ℤ) (l : List D) (d₀ : D) :
    ∑ t ∈ range l.length, f (l.getD t d₀) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih, List.map_cons, List.sum_cons]
    ring

lemma sum_rev_reverse {M : CombMap D V F} {w : D → ℤ} (hw : M.IsAntisymm w) (l : List D) :
    ((l.reverse.map M.rev).map w).sum = - (l.map w).sum := by
  have hw' : ∀ d, w (M.rev d) = - w d := hw
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.reverse_cons, List.map_append, List.sum_append, ih, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, hw']
    ring

section Unique

variable {M : CombMap D V F} {S : Finset D} {n m B : ℕ} {w : D → ℤ} {ι : D → ℕ} {ℓ : D → ℤ}

lemma isoLen_nonneg_low (hB : ∀ d, |w d| ≤ B) (d : D) :
    (0 : ℤ) < isoN2 n m B + isoN3 n m * (w d + B) + ι d := by
  have h2 := abs_le.1 (hB d)
  have : (0 : ℤ) < isoN2 n m B := by exact_mod_cast isoN2_pos n m B
  have : (0 : ℤ) ≤ isoN3 n m * (w d + B) := mul_nonneg (by positivity) (by linarith)
  have : (0 : ℤ) ≤ ι d := by positivity
  linarith

lemma isoLen_pos (hB : ∀ d, |w d| ≤ B) (hnn : ∀ d ∈ S, 0 ≤ ℓ d) (a : {d // d ∈ S}) :
    0 < (pieceGraph M S (isoLen n m B w ι ℓ)).len a := by
  show 0 < isoLen n m B w ι ℓ a.1
  have := isoLen_nonneg_low (n := n) (m := m) (ι := ι) hB a.1
  have : (0 : ℤ) ≤ isoN1 n m B * ℓ a.1 := mul_nonneg (by positivity) (hnn a.1 a.2)
  unfold isoLen; linarith

variable (hM : M.IsPlane) (hrot : M.RotTrans) {f₀ : F} (hw : IsoW M f₀ w)
  (hB : ∀ d, |w d| ≤ B) (hn : Fintype.card V ≤ n) (hι : Function.Injective ι)
  (hιm : ∀ d, ι d < m) (hnn : ∀ d ∈ S, 0 ≤ ℓ d)
include hM hrot hw hB hn hι hιm hnn

/-- **No two shortest paths for the isolating lengths fork before their end**: two shortest walks
between the same vertices end with the same dart. -/
theorem iso_no_fork : ∀ (s : ℕ) {x y : V} {P Q : List {d // d ∈ S}} {a b : {d // d ∈ S}},
    P.length + Q.length = s → IsSP (pieceGraph M S (isoLen n m B w ι ℓ)) x y (P ++ [a]) →
    IsSP (pieceGraph M S (isoLen n m B w ι ℓ)) x y (Q ++ [b]) → a ≠ b → False := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro x y P Q a b hs hP hQ hab
  set G' := pieceGraph M S (isoLen n m B w ι ℓ) with hG'
  have hpos : ∀ a, 0 < G'.len a := isoLen_pos hB hnn
  have hnn' : ∀ a, 0 ≤ G'.len a := fun a => (hpos a).le
  by_cases hint : ∃ z, z ∈ P.map G'.dst ∧ z ∈ Q.map G'.dst
  · -- the two walks meet before the end: induction on the rest
    obtain ⟨z, hzP, hzQ⟩ := hint
    obtain ⟨e, he, hez⟩ := List.mem_map.1 hzP
    obtain ⟨e', he', hez'⟩ := List.mem_map.1 hzQ
    obtain ⟨P₁, P₂, rfl⟩ := List.append_of_mem he
    obtain ⟨Q₁, Q₂, rfl⟩ := List.append_of_mem he'
    have suf : ∀ {R₁ R₂ : List {d // d ∈ S}} {c e : {d // d ∈ S}}, G'.dst e = z →
        IsSP G' x y (R₁ ++ e :: R₂ ++ [c]) → IsSP G' z y (R₂ ++ [c]) := by
      intro R₁ R₂ c e hez h
      rw [show R₁ ++ e :: R₂ ++ [c] = (R₁ ++ [e]) ++ (R₂ ++ [c]) by simp] at h
      obtain ⟨u, h1, h2, -, e2, -⟩ := dist_split hnn' h.1 h.2
      obtain ⟨-, rfl⟩ := LWalk.concat_iff.1 h1
      rw [hez] at h2 e2
      exact ⟨h2, e2⟩
    refine ih (P₂.length + Q₂.length) ?_ rfl (suf hez hP) (suf hez' hQ) hab
    simp only [List.length_append, List.length_cons] at hs; omega
  · push Not at hint
    have nsP := hP.nodup_src hpos
    have nsQ := hQ.nodup_src hpos
    have hlP : (P ++ [a]).length ≤ n := by
      have := nsP.length_le_card; rw [List.length_map] at this; omega
    have hlQ : (Q ++ [b]).length ≤ n := by
      have := nsQ.length_le_card; rw [List.length_map] at this; omega
    have hlex := lex_of_wlen_eq (M := M) (ℓ := ℓ) hB hιm hlP hlQ (by rw [hP.2, hQ.2])
    by_cases h0 : P = [] ∧ Q = []
    · -- two parallel darts: different numbers
      obtain ⟨rfl, rfl⟩ := h0
      have := hlex.2.2.2
      simp only [List.nil_append, lsum_cons, lsum_nil, add_zero, Nat.cast_inj] at this
      exact hab (Subtype.ext (hι this))
    · -- a simple cycle of the map
      have hx : (P ++ [a]).map G'.src = x :: P.map G'.dst := map_src_concat hP.1
      have hxQ : (Q ++ [b]).map G'.src = x :: Q.map G'.dst := map_src_concat hQ.1
      have hyP : G'.dst a = y := (LWalk.concat_iff.1 hP.1).2
      have hyQ : G'.dst b = y := (LWalk.concat_iff.1 hQ.1).2
      have ndP := hP.nodup_dst hpos
      have ndQ := hQ.nodup_dst hpos
      rw [List.map_append, List.map_singleton, hyP] at ndP
      rw [List.map_append, List.map_singleton, hyQ] at ndQ
      rw [hx] at nsP
      rw [hxQ] at nsQ
      have hxy : x ≠ y := by
        rintro rfl
        have e := hP.2
        rw [dist_self hnn', wlen_append] at e
        have := wlen_nonneg hnn' P
        have := hpos a
        simp only [wlen_cons, wlen_nil, add_zero] at e
        linarith
      set C : List D := (P ++ [a]).map Subtype.val ++
        ((Q ++ [b]).map Subtype.val).reverse.map M.rev with hCdef
      have hCw : LWalk (mapGraph M) x x C :=
        (lwalk_map hP.1).append (lwalk_reverse (lwalk_map hQ.1))
      have hCt : C.map M.tail = x :: (P.map G'.dst ++ y :: (Q.map G'.dst).reverse) := by
        have e1 : (P ++ [a]).map (fun d => M.tail d.1) = x :: P.map G'.dst := hx
        have e2 : (Q ++ [b]).map (fun d => M.head d.1) = Q.map G'.dst ++ [y] := by
          rw [← hyQ, List.map_append]; rfl
        rw [show C.map M.tail = (P ++ [a]).map (fun d => M.tail d.1) ++
            ((Q ++ [b]).map (fun d => M.head d.1)).reverse by
          simp [hCdef, List.map_reverse, Function.comp_def], e1, e2]
        simp
      have yP : y ∉ P.map G'.dst := fun h =>
        (List.nodup_append.1 ndP).2.2 y h y (List.mem_singleton_self y) rfl
      have yQ : y ∉ Q.map G'.dst := fun h =>
        (List.nodup_append.1 ndQ).2.2 y h y (List.mem_singleton_self y) rfl
      have nP := (List.nodup_append.1 ndP).1
      have nQ := (List.nodup_append.1 ndQ).1
      have xP := (List.nodup_cons.1 nsP).1
      have xQ := (List.nodup_cons.1 nsQ).1
      have hnd : (C.map M.tail).Nodup := by
        rw [hCt]
        refine List.nodup_cons.2 ⟨?_, List.nodup_append.2 ⟨nP, List.nodup_cons.2
          ⟨fun h => yQ (List.mem_reverse.1 h), List.nodup_reverse.2 nQ⟩, ?_⟩⟩
        · simp only [List.mem_append, List.mem_cons, List.mem_reverse]
          rintro (h | h | h)
          · exact xP h
          · exact hxy h
          · exact xQ h
        · intro z hz z' hz' e
          subst e
          rcases List.mem_cons.1 hz' with rfl | h
          · exact yP hz
          · exact hint z hz (List.mem_reverse.1 h)
      have h3 : 3 ≤ C.length := by
        simp only [hCdef, List.length_append, List.length_map, List.length_reverse,
          List.length_singleton]
        rcases not_and_or.1 h0 with h | h
        · have := List.length_pos_iff.2 h; omega
        · have := List.length_pos_iff.2 h; omega
      have hne := circ_ne_zero hM hrot hw (isSimpleCycle_of_list hCw hnd h3 a.1)
      rw [sum_range_getD] at hne
      have hsum : (C.map w).sum = lsum w (P ++ [a]) - lsum w (Q ++ [b]) := by
        rw [hCdef, List.map_append, List.sum_append, sum_rev_reverse hw.antisymm]
        simp only [lsum, List.map_map, Function.comp_def]
        ring
      rw [hsum, hlex.2.2.1, sub_self] at hne
      exact hne rfl

/-- **The isolating lengths have unique tight arcs.** -/
theorem isoLen_uniqTight : UniqTight (pieceGraph M S (isoLen n m B w ι ℓ)) := by
  set G' := pieceGraph M S (isoLen n m B w ι ℓ) with hG'
  have hpos : ∀ a, 0 < G'.len a := isoLen_pos hB hnn
  have hnn' : ∀ a, 0 ≤ G'.len a := fun a => (hpos a).le
  intro r a b ha hb hab _
  have walk : ∀ e, Tight G' r e → ∃ L, IsSP G' r (G'.dst e) (L ++ [e]) := by
    intro e he
    obtain ⟨L, hL⟩ := exists_isSP hnn' he.1
    refine ⟨L, hL.1.concat rfl, ?_⟩
    rw [wlen_append, hL.2]; simp only [wlen_cons, wlen_nil, add_zero]; exact he.2
  obtain ⟨La, hLa⟩ := walk a ha
  obtain ⟨Lb, hLb⟩ := walk b hb
  rw [hab] at hLa
  by_contra hne
  exact iso_no_fork hM hrot hw hB hn hι hιm hnn _ rfl hLa hLb hne

end Unique

/-! ### The distances -/

section Dist

variable {M : CombMap D V F} {S : Finset D} {n m B : ℕ} {w : D → ℤ} {ι : D → ℕ} {ℓ : D → ℤ}
variable (hB : ∀ d, |w d| ≤ B) (hn : Fintype.card V ≤ n) (hιm : ∀ d, ι d < m)
  (hnn : ∀ d ∈ S, 0 ≤ ℓ d)
include hB hn hιm hnn

lemma lwalk_iso_iff {x y : V} {L : List {d // d ∈ S}} :
    LWalk (pieceGraph M S (isoLen n m B w ι ℓ)) x y L ↔ LWalk (pieceGraph M S ℓ) x y L :=
  ⟨fun h => lwalk_of_eq (G := pieceGraph M S (isoLen n m B w ι ℓ)) (G' := pieceGraph M S ℓ)
      rfl rfl h,
    fun h => lwalk_of_eq (G := pieceGraph M S ℓ) (G' := pieceGraph M S (isoLen n m B w ι ℓ))
      rfl rfl h⟩

lemma reach_iso_iff {x y : V} :
    Reach (pieceGraph M S (isoLen n m B w ι ℓ)) x y ↔ Reach (pieceGraph M S ℓ) x y :=
  ⟨fun ⟨l, h⟩ => ⟨l, (lwalk_iso_iff hB hn hιm hnn).1 h⟩,
    fun ⟨l, h⟩ => ⟨l, (lwalk_iso_iff hB hn hιm hnn).2 h⟩⟩

/-- **Isolated distances**: `N₁ dist ≤ dist' < N₁ (dist + 1)`. -/
theorem isoLen_dist_bounds {x y : V} (h : Reach (pieceGraph M S ℓ) x y) :
    (isoN1 n m B : ℤ) * dist (pieceGraph M S ℓ) x y ≤
        dist (pieceGraph M S (isoLen n m B w ι ℓ)) x y ∧
      dist (pieceGraph M S (isoLen n m B w ι ℓ)) x y <
        (isoN1 n m B : ℤ) * (dist (pieceGraph M S ℓ) x y + 1) := by
  set G := pieceGraph M S ℓ
  set G' := pieceGraph M S (isoLen n m B w ι ℓ)
  have hpos : ∀ a, 0 < G'.len a := isoLen_pos hB hnn
  have hnn' : ∀ a, 0 ≤ G'.len a := fun a => (hpos a).le
  have hnnG : ∀ a, 0 ≤ G.len a := fun a => hnn a.1 a.2
  have hN1 : (0 : ℤ) ≤ isoN1 n m B := by positivity
  constructor
  · obtain ⟨L, hL⟩ := exists_isSP hnn' ((reach_iso_iff hB hn hιm hnn).2 h)
    have hlen : L.length ≤ n := by
      have := (hL.nodup_src hpos).length_le_card; rw [List.length_map] at this; omega
    have hd := dist_le hnnG ((lwalk_iso_iff hB hn hιm hnn).1 hL.1)
    rw [← hL.2, wlen_iso]
    have := (mid_bounds hB hιm hlen).1
    have := mul_le_mul_of_nonneg_left hd hN1
    linarith
  · obtain ⟨L, hL, hLe⟩ := exists_walk_dist hnnG h
    obtain ⟨L', hL', hsub, hnd⟩ := exists_nodup_walk hL
    have h1 : wlen G L' ≤ wlen G L := by
      unfold wlen
      exact (hsub.map G.len).sum_le_sum fun x hx => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact hnnG a
    have h2 := dist_le hnnG hL'
    have h3 := dist_le hnn' ((lwalk_iso_iff hB hn hιm hnn).2 hL')
    have hlen : L'.length ≤ n := by
      have := hnd.length_le_card; rw [List.length_map] at this; omega
    have h4 := (mid_bounds hB hιm hlen).2
    rw [wlen_iso] at h3
    have h5 : wlen G L' = dist G x y := by omega
    rw [h5] at h3
    linarith

/-- **The distances are the isolated distances divided by `N₁`.** -/
theorem isoLen_dist_div {x y : V} (h : Reach (pieceGraph M S ℓ) x y) :
    dist (pieceGraph M S ℓ) x y =
      dist (pieceGraph M S (isoLen n m B w ι ℓ)) x y / isoN1 n m B := by
  obtain ⟨h1, h2⟩ := isoLen_dist_bounds hB hn hιm hnn h
  have hc : (0 : ℤ) < isoN1 n m B := by exact_mod_cast isoN1_pos n m B
  obtain ⟨s, hs⟩ : ∃ s, dist (pieceGraph M S (isoLen n m B w ι ℓ)) x y =
      isoN1 n m B * dist (pieceGraph M S ℓ) x y + s := ⟨_, (add_sub_cancel _ _).symm⟩
  rw [hs] at h1 h2 ⊢
  rw [show (isoN1 n m B : ℤ) * dist (pieceGraph M S ℓ) x y + s =
      s + dist (pieceGraph M S ℓ) x y * isoN1 n m B by ring,
    Int.add_mul_ediv_right _ _ hc.ne', Int.ediv_eq_zero_of_lt (by linarith) (by linarith),
    zero_add]

/-- **The answers for the isolating lengths**, divided by `N₁`, are the answers for `ℓ`. -/
theorem odist_isoLen (x v : V) :
    (odist (pieceGraph M S (isoLen n m B w ι ℓ)) x v).map (· / (isoN1 n m B : ℤ)) =
      odist (pieceGraph M S ℓ) x v := by
  unfold odist
  split_ifs with h1 h2 h2
  · rw [Option.map_some, ← isoLen_dist_div hB hn hιm hnn h2]
  · exact absurd ((reach_iso_iff hB hn hιm hnn).1 h1) h2
  · exact absurd ((reach_iso_iff hB hn hιm hnn).2 h2) h1
  · rfl

end Dist

/-! ### The article's assumptions, and the size of the numbers -/

section Hyp

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {n m B : ℕ} {w : D → ℤ} {ι : D → ℕ} {f₀ : F}

/-- **The isolating lengths meet the article's assumptions.** -/
theorem HypNN.hypIso (H : HypNN M k g S ℓ) (hw : IsoW M f₀ w) (hB : ∀ d, |w d| ≤ B)
    (hn : Fintype.card V ≤ n) (hι : Function.Injective ι) (hιm : ∀ d, ι d < m) :
    Hyp M k g S (isoLen n m B w ι ℓ) where
  plane := H.plane
  rot := H.rot
  face := H.face
  pos d hd := isoLen_pos (M := M) (n := n) (m := m) (ι := ι) hB H.nonneg ⟨d, hd⟩
  noIn := H.noIn
  uniq := isoLen_uniqTight H.plane H.rot hw hB hn hι hιm H.nonneg

lemma isoN1_eq (n m B : ℕ) : isoN1 n m B = (n * m + 1) * (2 * B * n + 1) * (n + 1) := rfl

/-- **The isolating lengths are word-sized**: `0 < isoLen ℓ d < N₁ (ℓ d + 1)` for `ℓ d ≥ 0` and
`n ≥ 1`, with `N₁ = (n m + 1)(2 B n + 1)(n + 1)`. -/
theorem isoLen_lt (hB : ∀ d, |w d| ≤ B) (hιm : ∀ d, ι d < m) (hn1 : 1 ≤ n) {d : D}
    (hd : 0 ≤ ℓ d) :
    0 < isoLen n m B w ι ℓ d ∧ isoLen n m B w ι ℓ d < isoN1 n m B * (ℓ d + 1) := by
  have h0 := isoLen_nonneg_low (n := n) (m := m) (ι := ι) hB d
  have hN1 : (0 : ℤ) ≤ isoN1 n m B := by positivity
  have := mul_nonneg hN1 hd
  refine ⟨by unfold isoLen; linarith, ?_⟩
  have h2 := abs_le.1 (hB d)
  have hιd : (ι d : ℤ) < m := by exact_mod_cast hιm d
  have hn1' : (1 : ℤ) ≤ n := by exact_mod_cast hn1
  have hB0 : (0 : ℤ) ≤ B := by exact_mod_cast Nat.zero_le B
  have hm0 : (0 : ℤ) ≤ m := by exact_mod_cast Nat.zero_le m
  have e3 : (isoN3 n m : ℤ) = n * m + 1 := by simp [isoN3]
  have e2 : (isoN2 n m B : ℤ) = isoN3 n m * (2 * B * n + 1) := by simp [isoN2]
  have e1 : (isoN1 n m B : ℤ) = isoN2 n m B * (n + 1) := by simp [isoN1]
  have hN3 : (0 : ℤ) < isoN3 n m := by exact_mod_cast isoN3_pos n m
  have a1 : (isoN3 n m : ℤ) * (w d + B) ≤ isoN3 n m * (2 * B) :=
    mul_le_mul_of_nonneg_left (by linarith) hN3.le
  have a2 : (m : ℤ) < isoN3 n m := by rw [e3]; nlinarith
  have a3 : (isoN3 n m : ℤ) * (2 * B) + isoN3 n m ≤ isoN2 n m B := by
    have h := mul_le_mul_of_nonneg_left (show (2 : ℤ) * B ≤ 2 * B * n by nlinarith) hN3.le
    have : (isoN3 n m : ℤ) * (2 * B * n + 1) = isoN3 n m * (2 * B * n) + isoN3 n m := by ring
    rw [e2, this]; linarith
  have a4 : (isoN2 n m B : ℤ) * 2 ≤ isoN1 n m B := by
    rw [e1]; have : (0 : ℤ) ≤ isoN2 n m B := by positivity
    nlinarith
  unfold isoLen
  nlinarith

end Hyp

/-! ### Existence of an isolating weight -/

section Exist

variable {M : CombMap D V F}

variable (M) in
/-- The dual graph: the dart `d` goes from its face to the face of its reverse. -/
def dualGraph : Digraph F D := ⟨M.face, fun d => M.face (M.rev d), fun _ => 0⟩

variable (M) in
/-- The unit flow of a list of darts: `+1` on its darts, `-1` on their reverses. -/
def dflow : List D → D → ℤ
  | [] => fun _ => 0
  | e :: l => fun d => (if d = e then 1 else 0) - (if d = M.rev e then 1 else 0) + dflow l d

lemma dflow_antisymm (l : List D) : M.IsAntisymm (dflow M l) := by
  intro d
  induction l with
  | nil => simp [dflow]
  | cons e l ih =>
    simp only [dflow, ih]
    have h1 : (M.rev d = e) ↔ (d = M.rev e) :=
      ⟨fun h => by rw [← h, M.rev_rev], fun h => by rw [h, M.rev_rev]⟩
    have h2 : (M.rev d = M.rev e) ↔ (d = e) := M.rev_injective.eq_iff
    simp only [h1, h2]; ring

lemma dflow_eq_of_nodup {l : List D} (hl : (l.map M.face).Nodup) (d : D) :
    dflow M l d = (if d ∈ l then 1 else 0) - (if M.rev d ∈ l then 1 else 0) := by
  induction l with
  | nil => simp [dflow]
  | cons e l ih =>
    rw [List.map_cons, List.nodup_cons] at hl
    have hnot : ∀ x, x ∈ l → x ≠ e := fun x hx hxe =>
      hl.1 (List.mem_map.2 ⟨x, hx, by rw [hxe]⟩)
    simp only [dflow, ih hl.2, List.mem_cons]
    have h1 : (M.rev d = e) ↔ (d = M.rev e) :=
      ⟨fun h => by rw [← h, M.rev_rev], fun h => by rw [h, M.rev_rev]⟩
    by_cases hd : d = e <;> by_cases hr : d = M.rev e
    · exact absurd (hd.symm.trans hr) (M.rev_ne e).symm
    · subst hd; have := hnot d; simp_all; ring
    · subst hr; have := hnot (M.rev (M.rev e)); simp_all; ring
    · have : ¬ M.rev d = e := fun h => hr (h1.1 h)
      simp [hd, hr, this]

lemma abs_dflow_le {l : List D} (hl : (l.map M.face).Nodup) (d : D) : |dflow M l d| ≤ 1 := by
  rw [dflow_eq_of_nodup hl]
  split_ifs <;> simp

lemma curl_dflow {s t : F} {l : List D} (h : LWalk (dualGraph M) s t l) (f : F) :
    curl M (dflow M l) f = (if s = f then 1 else 0) - (if t = f then 1 else 0) := by
  induction h with
  | nil => simp [curl, dflow]
  | @cons e y l _ ih =>
    have : curl M (dflow M (e :: l)) f = (if M.face e = f then 1 else 0) -
        (if M.face (M.rev e) = f then 1 else 0) + curl M (dflow M l) f := by
      simp only [curl, dflow, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      congr 2
      · rw [Finset.sum_ite_eq']; simp
      · rw [Finset.sum_ite_eq']; simp
    rw [this, ih]
    simp only [dualGraph]
    split_ifs <;> simp_all <;> ring

/-- **An isolating weight exists, with values at most `#F`**: the sum, over all the faces `y`, of
the unit flows of dual paths from `y` to `f₀` without repeated faces. -/
theorem exists_isoW (hM : M.IsPlane) (f₀ : F) :
    ∃ w : D → ℤ, IsoW M f₀ w ∧ ∀ d, |w d| ≤ Fintype.card F := by
  have hreach : ∀ y, Reach (dualGraph M) y f₀ := by
    intro y
    induction hM.dualConn y f₀ with
    | refl => exact Reach.refl _
    | @tail a b _ hab ih =>
      obtain ⟨d, rfl, rfl⟩ := hab
      exact ih.arc (a := d)
  have hl : ∀ y, ∃ l, LWalk (dualGraph M) y f₀ l ∧ (l.map M.face).Nodup := by
    intro y
    obtain ⟨l, hl⟩ := hreach y
    obtain ⟨l', hl', -, hnd⟩ := exists_nodup_walk hl
    exact ⟨l', hl', hnd⟩
  choose L hL hLn using hl
  refine ⟨fun d => ∑ y, dflow M (L y) d, ⟨fun d => ?_, fun f hf => ?_⟩, fun d => ?_⟩
  · simp only [dflow_antisymm _ d, Finset.sum_neg_distrib]
  · have : curl M (fun d => ∑ y, dflow M (L y) d) f = ∑ y, curl M (dflow M (L y)) f := by
      simp only [curl]; rw [Finset.sum_comm]
    rw [this]
    simp only [curl_dflow (hL _), Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    have : ¬ f₀ = f := fun h => hf h.symm
    simp [this]
  · calc |∑ y, dflow M (L y) d| ≤ ∑ y, |dflow M (L y) d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y : F, (1 : ℤ) := Finset.sum_le_sum fun y _ => abs_dflow_le (hLn y) d
      _ = Fintype.card F := by simp

end Exist

/-! ### The data structure on the isolating lengths -/

section DKPW

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {n m B : ℕ} {w : D → ℤ} {ι : D → ℕ} {f₀ : F}

/-- **The data structure on the isolating lengths gives the distances**: from every root of the
face, the answers divided by `N₁` are the distances in the piece with the lengths `ℓ`. -/
theorem dkpw_iso (H : HypNN M k g S ℓ) (hw : IsoW M f₀ w) (hB : ∀ d, |w d| ≤ B)
    (hn : Fintype.card V ≤ n) (hι : Function.Injective ι) (hιm : ∀ d, ι d < m) {j : ℕ}
    (hj : j < k) (φ : F) (B' : Finset V) (v : V) :
    (dkpw M k g S (isoLen n m B w ι ℓ) (M.tail (g j)) v).map (· / (isoN1 n m B : ℤ)) =
      msspDist M S ℓ φ B' (M.tail (g j)) v := by
  rw [dkpw_eq (H.hypIso hw hB hn hι hιm) hj φ B']
  unfold msspDist
  split_ifs
  · exact odist_isoLen hB hn hιm H.nonneg _ _
  · rfl

/-- **Summary**: for the numbering `σ` of the darts, with `n = #V`, `m = #D`, `B = #F`, some
isolating weight gives lengths of size below `N₁ (ℓ + 1)`, `N₁ = (n m + 1)(2 B n + 1)(n + 1)`,
which meet the article's assumptions and whose distances divided by `N₁` are those of `ℓ`. -/
theorem HypNN.exists_iso (H : HypNN M k g S ℓ) (σ : D ≃ Fin (Fintype.card D)) (f₀ : F) :
    ∃ w : D → ℤ, IsoW M f₀ w ∧ (∀ d, |w d| ≤ Fintype.card F) ∧
      Hyp M k g S (isoLen (Fintype.card V) (Fintype.card D) (Fintype.card F) w
        (fun d => σ d) ℓ) ∧
      (∀ d ∈ S, 0 < isoLen (Fintype.card V) (Fintype.card D) (Fintype.card F) w (fun d => σ d) ℓ d
        ∧ isoLen (Fintype.card V) (Fintype.card D) (Fintype.card F) w (fun d => σ d) ℓ d <
          isoN1 (Fintype.card V) (Fintype.card D) (Fintype.card F) * (ℓ d + 1)) ∧
      ∀ x v, (odist (pieceGraph M S (isoLen (Fintype.card V) (Fintype.card D) (Fintype.card F) w
          (fun d => σ d) ℓ)) x v).map
          (· / (isoN1 (Fintype.card V) (Fintype.card D) (Fintype.card F) : ℤ)) =
        odist (pieceGraph M S ℓ) x v := by
  obtain ⟨w, hw, hB⟩ := exists_isoW H.plane f₀
  have hι : Function.Injective fun d => (σ d : ℕ) := fun a b h => σ.injective (Fin.ext h)
  have hιm : ∀ d, (σ d : ℕ) < Fintype.card D := fun d => (σ d).isLt
  have hn1 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 H.plane.nonempty
  exact ⟨w, hw, hB, H.hypIso hw hB le_rfl hι hιm,
    fun d hd => isoLen_lt hB hιm hn1 (H.nonneg d hd), odist_isoLen hB le_rfl hιm H.nonneg⟩

end DKPW

end MSSP

end PlanarFlow
