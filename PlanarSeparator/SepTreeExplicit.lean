module

public import PlanarSeparator.Square

/-!
# Explicit separator trees from a separator routine

`PlanarSeparator.exists_sepTree` and `PlanarSeparator.exists_sepTree_square` only show that
separator trees with boundary bounds exist. This file builds such a tree by an explicit
recursion from a **separator routine** given as a parameter: a function
`sep : Finset V → (V → ℕ) → Finset V × Finset V × Finset V` which, on a vertex set `U` and
natural weights `w`, returns `(S, A, B)` with `IsSeparation G U S A B`, `#S ≤ c √(#U)` and
`3 w(A) ≤ 2 w(U)`, `3 w(B) ≤ 2 w(U)` (`PlanarSeparator.SepRoutine`). Every step of the
construction is a definite function of the outputs of the routine (no choice), so a program that
calls a separator program in place of `sep` computes the same tree.

The construction follows the proof of `PlanarSeparator.exists_sepTree_of_separators`
(`PlanarSeparator/Nested.lean`) step by step:

* **Division** (`PlanarSeparator.SepRoutine.divide`, after
  `PlanarSeparator.exists_division_of_separators`): to cut a vertex set `U` with natural weights
  `μ` into pieces of weight at most `L`, a set of weight at most `L` is one piece; otherwise
  separate `U` with the weights `μ` and divide the two parts recursively. The pieces are given
  by a labelling `κ : V → Finset V` constant along edges off the separator.
* **Balanced split** (`PlanarSeparator.bsplit`, after `PlanarSeparator.exists_balanced_split`):
  the pieces, as a list, are split into a sublist `J` and the rest, both light for a second
  measure `y`, and `J` near half of a first measure `x`; first the longest prefix with at most
  half of `x` (`PlanarSeparator.gpre`), then, if one side is too heavy for `y`, the walk of
  `PlanarSeparator.exists_balanced_walk` with the pieces taken in list order
  (`PlanarSeparator.bwalk`).
* **Splitting a node** (`PlanarSeparator.SepRoutine.splitW`, after
  `PlanarSeparator.exists_split_of_separators`): for a vertex set `W` with `m` vertices and
  boundary `B` with `b` vertices, the weights are `20 max b 1` on `W` and `20 m` on `B`, the
  threshold is `L = m max b 1` (the weights `20/m` and `20/b` of the existence proof, scaled by
  `L`); the division of `W ∪ B` gives `S` and the pieces, listed in the order of their first
  vertex; the balanced split for the measures `#(piece ∩ W \ S)` and `#(piece ∩ B \ S)` with
  `c = 3 b / 5` gives the two parts; the separator is `W ∩ S`.
* **The tree** (`PlanarSeparator.SepRoutine.buildTree`): a set of at most `T²` vertices is a leaf;
  otherwise the node `W ∩ S` with the trees of the two parts.

The functions `divide`, `splitW`, `buildAux`, `buildTree` take the separator function `sep`
itself (not the routine with its proofs) as their argument, and the graph `G` and a list `ord` of
the vertices (fixing the order of the pieces) explicitly: `buildTree G R.sep ord T`. They are
recursions with explicit fuel (`#U`, `#W`, `Fintype.card V`), so they are computable from `sep`.

## Main results

* `PlanarSeparator.SepRoutine`: separator routines with their specification;
  `PlanarSeparator.SepRoutine.ofHasSqrtSeparators` (one exists for every graph with
  `c √m`-separators, by choice) and `PlanarSeparator.SepRoutine.square` (an explicit routine for
  the square of a graph of maximum degree `Δ` from one for the graph, as in
  `PlanarSeparator.HasSqrtSeparators.square`).
* `PlanarSeparator.SepRoutine.divide_spec`, `PlanarSeparator.bsplit_spec`,
  `PlanarSeparator.SepRoutine.splitW_spec`: the steps.
* `PlanarSeparator.SepRoutine.buildTree_spec`: for every natural `T ≥ 40 (177 c + 1)` and every
  list `ord` of all vertices, the tree `buildTree G R.sep ord T` covers all vertices, is a
  separator tree of `G`, has separators and boundaries
  of at most `T √m` vertices at every subtree with `m` vertices, and parts of at most `2m/3`
  vertices: `PlanarSeparator.GoodTree G T (buildTree G R.sep ord T)`.
* `PlanarSeparator.SepRoutine.buildTree_square_spec`: the same for the square of a graph of
  maximum degree `≤ Δ`, from a routine for the graph with constant `c`, for every natural
  `T ≥ 40 (177 c (Δ + 1)² + 1)`; for a plane graph (`c = 6`) this is `squareTreeConst Δ`.
* `PlanarSeparator.exists_goodTree_explicit`, `PlanarSeparator.exists_goodTree_square_explicit`:
  the statements of `exists_sepTree` and `exists_sepTree_square` recovered from the explicit
  construction (with a routine obtained by choice).
-/

@[expose] public section

namespace PlanarSeparator

open Finset NestedDissection NestedDissection.SepTree

/-! ### Sums over lists -/

section lists

variable {ι : Type*}

/-- The sum of a natural measure over a list. -/
def lsum (x : ι → ℕ) (l : List ι) : ℕ := (l.map x).sum

@[simp] lemma lsum_nil (x : ι → ℕ) : lsum x [] = 0 := rfl

@[simp] lemma lsum_cons (x : ι → ℕ) (i : ι) (l : List ι) : lsum x (i :: l) = x i + lsum x l := by
  simp [lsum]

@[simp] lemma lsum_append (x : ι → ℕ) (l l' : List ι) : lsum x (l ++ l') = lsum x l + lsum x l' := by
  simp [lsum]

lemma lsum_eq_sum [DecidableEq ι] (x : ι → ℕ) {l : List ι} (hl : l.Nodup) :
    lsum x l = ∑ i ∈ l.toFinset, x i := by
  rw [lsum, List.sum_toFinset _ hl]

@[simp] lemma lsum_reverse (x : ι → ℕ) (l : List ι) : lsum x l.reverse = lsum x l := by
  simp [lsum, List.sum_reverse]

lemma lsum_le_of_subperm (x : ι → ℕ) {l l' : List ι} (h : l.Subperm l') : lsum x l ≤ lsum x l' := by
  obtain ⟨l₀, hp, hs⟩ := h
  rw [lsum, ← hp.map x |>.sum_eq]
  exact (hs.map x).sum_le_sum (fun _ _ => Nat.zero_le _)

/-! ### The balanced split -/

/-- The longest prefix of `l` whose measure, added to `s`, is at most half of `X`. -/
def gpre (x : ι → ℕ) (X : ℕ) : ℕ → List ι → List ι
  | _, [] => []
  | s, i :: l => if 2 * (s + x i) ≤ X then i :: gpre x X (s + x i) l else []

lemma gpre_spec (x : ι → ℕ) (X : ℕ) :
    ∀ (l : List ι) (s : ℕ), 2 * s ≤ X →
      gpre x X s l ++ l.drop (gpre x X s l).length = l ∧ 2 * (s + lsum x (gpre x X s l)) ≤ X ∧
      ∀ i rest, l.drop (gpre x X s l).length = i :: rest →
        X < 2 * (s + lsum x (gpre x X s l) + x i)
  | [], s, hs => by simpa [gpre] using hs
  | i :: l, s, hs => by
    by_cases h : 2 * (s + x i) ≤ X
    · obtain ⟨h1, h2, h3⟩ := gpre_spec x X l (s + x i) h
      simp only [gpre, ite_eq_left h, List.cons_append, List.length_cons, List.drop_succ_cons, lsum_cons]
      refine ⟨by rw [h1], by omega, fun j rest hj => ?_⟩
      have := h3 j rest hj
      omega
    · simp only [gpre, ite_eq_right h, List.nil_append, List.length_nil, List.drop_zero, lsum_nil]
      refine ⟨trivial, by omega, fun j rest hj => ?_⟩
      simp only [List.cons.injEq] at hj
      rw [← hj.1]
      omega

/-- The walk of `PlanarSeparator.exists_balanced_walk` with the pieces taken in list order: the
current subfamily is `r ++ acc`, where `r` remains of the first family and `acc` (reversed) has
been taken from the second family, whose remaining pieces are `a`. While the `x`-measure is
below half of `X` and pieces remain, the next piece of the second family is added; otherwise the
first piece of `r` is removed, and the walk stops as soon as `p y ≤ q`. -/
def bwalk (x y : ι → ℕ) (X p q : ℕ) : ℕ → List ι → List ι → List ι → List ι
  | 0, r, _, acc => r ++ acc
  | k + 1, r, a, acc =>
    match a with
    | j :: a' =>
      if 2 * lsum x (r ++ acc) < X then bwalk x y X p q k r a' (j :: acc)
      else
        match r with
        | [] => acc
        | _ :: r' => if p * lsum y (r' ++ acc) ≤ q then r' ++ acc else bwalk x y X p q k r' (j :: a') acc
    | [] =>
      match r with
      | [] => acc
      | _ :: r' => if p * lsum y (r' ++ acc) ≤ q then r' ++ acc else bwalk x y X p q k r' [] acc

/-- **The balanced split.** The longest prefix `J₁` of `l` with at most half of the `x`-measure
`X`, and the rest `J₂`; if `J₁` is too heavy for `y` (`q < p y(J₁)`), the walk from `J₁` towards
`J₂`; if `J₂` is, the walk from `J₂` towards `J₁`; otherwise `J₁`. -/
def bsplit (x y : ι → ℕ) (p q : ℕ) (l : List ι) : List ι :=
  let X := lsum x l
  let J₁ := gpre x X 0 l
  let J₂ := l.drop J₁.length
  if q < p * lsum y J₁ then bwalk x y X p q (J₁.length + J₂.length) J₁ J₂ []
  else if q < p * lsum y J₂ then bwalk x y X p q (J₁.length + J₂.length) J₂ J₁ []
  else J₁

section walk

variable (x y : ι → ℕ) (X p q : ℕ)

lemma le_div_iff_nat {p q s : ℕ} (hp : 0 < p) : p * s ≤ q ↔ (s : ℝ) ≤ (q : ℝ) / p := by
  rw [le_div_iff₀ (by exact_mod_cast hp), mul_comm]
  exact_mod_cast Iff.rfl

lemma lt_mul_iff_nat {p q s : ℕ} (hp : 0 < p) : q < p * s ↔ (q : ℝ) / p < s := by
  rw [← not_le, ← not_le, le_div_iff_nat hp]

/-- The invariant of the walk gives a nodup subfamily of `S₁ ++ S₂`. -/
lemma walk_nodup {S₁ S₂ r acc a : List ι} (hnd : (S₁ ++ S₂).Nodup) (hr : r <:+ S₁)
    (hacc : acc.reverse ++ a = S₂) : (r ++ acc).Nodup ∧ ∀ i ∈ r ++ acc, i ∈ S₁ ++ S₂ := by
  have hsub : (r ++ acc.reverse).Sublist (S₁ ++ S₂) :=
    hr.sublist.append (hacc ▸ List.prefix_append _ _).sublist
  refine ⟨((hnd.sublist hsub).perm ((List.perm_append_left_iff r).2 (List.reverse_perm acc))),
    fun i hi => hsub.subset ?_⟩
  simpa using hi

/-- **The walk.** Under the hypotheses of `PlanarSeparator.exists_balanced_walk`, the walk ends
at a nodup subfamily of `S₁ ++ S₂` with `x`-measure within `ε` of `X/2` and `y`-measure between
`Y - c` and `c`, `c = q/p`. -/
theorem bwalk_spec (hp : 0 < p) {S₁ S₂ : List ι} (hnd : (S₁ ++ S₂).Nodup) {ε η Y : ℝ}
    (hxε : ∀ i ∈ S₁ ++ S₂, (x i : ℝ) ≤ ε) (hyη : ∀ i ∈ S₁, (y i : ℝ) ≤ η) (hη : 0 ≤ η)
    (hc : η + Y ≤ 2 * ((q : ℝ) / p)) (hS₂x : (X : ℝ) / 2 - ε ≤ lsum x S₂)
    (hS₂y : (lsum y S₂ : ℝ) < Y - (q : ℝ) / p) :
    ∀ k r a acc, r <:+ S₁ → acc.reverse ++ a = S₂ → r.length + a.length = k →
      (X : ℝ) / 2 - ε ≤ lsum x (r ++ acc) → (lsum x (r ++ acc) : ℝ) ≤ X / 2 + ε →
      (q : ℝ) / p < lsum y (r ++ acc) →
      let K := bwalk x y X p q k r a acc
      K.Nodup ∧ (∀ i ∈ K, i ∈ S₁ ++ S₂) ∧ (X : ℝ) / 2 - ε ≤ lsum x K ∧
        (lsum x K : ℝ) ≤ X / 2 + ε ∧ Y - (q : ℝ) / p ≤ lsum y K ∧ (lsum y K : ℝ) ≤ (q : ℝ) / p := by
  set c : ℝ := (q : ℝ) / p
  have hyacc : ∀ acc a : List ι, acc.reverse ++ a = S₂ → (lsum y acc : ℝ) ≤ lsum y S₂ := by
    intro acc a h
    rw [← h, lsum_append, lsum_reverse]
    exact_mod_cast Nat.le_add_right _ _
  -- the subfamily `[] ++ acc` is never too heavy
  have hnil : ∀ acc a : List ι, acc.reverse ++ a = S₂ → c < lsum y ([] ++ acc) → False := by
    intro acc a h h'
    have := hyacc acc a h
    simp only [List.nil_append] at h'
    linarith
  -- the removal step
  have hrem : ∀ (k : ℕ) (i : ι) (r' a acc : List ι), (i :: r') <:+ S₁ →
      acc.reverse ++ a = S₂ → (X : ℝ) / 2 - ε ≤ lsum x (r' ++ acc) →
      (lsum x (r' ++ acc) : ℝ) ≤ X / 2 + ε → c < lsum y (i :: r' ++ acc) →
      (r'.length + a.length = k → (X : ℝ) / 2 - ε ≤ lsum x (r' ++ acc) →
        (lsum x (r' ++ acc) : ℝ) ≤ X / 2 + ε → c < lsum y (r' ++ acc) →
        let K := bwalk x y X p q k r' a acc
        K.Nodup ∧ (∀ i ∈ K, i ∈ S₁ ++ S₂) ∧ (X : ℝ) / 2 - ε ≤ lsum x K ∧
          (lsum x K : ℝ) ≤ X / 2 + ε ∧ Y - c ≤ lsum y K ∧ (lsum y K : ℝ) ≤ c) →
      r'.length + a.length = k →
      let K := if p * lsum y (r' ++ acc) ≤ q then r' ++ acc else bwalk x y X p q k r' a acc
      K.Nodup ∧ (∀ i ∈ K, i ∈ S₁ ++ S₂) ∧ (X : ℝ) / 2 - ε ≤ lsum x K ∧
        (lsum x K : ℝ) ≤ X / 2 + ε ∧ Y - c ≤ lsum y K ∧ (lsum y K : ℝ) ≤ c := by
    intro k i r' a acc hr hacc hx1 hx2 hy ih hlen
    have hr' : r' <:+ S₁ := (List.suffix_cons i r').trans hr
    have hyi : (y i : ℝ) ≤ η := hyη i (hr.subset (List.mem_cons_self))
    simp only [List.cons_append, lsum_cons, Nat.cast_add] at hy
    by_cases hfin : p * lsum y (r' ++ acc) ≤ q
    · simp only [hfin, ↓reduceIte]
      obtain ⟨h1, h2⟩ := walk_nodup hnd hr' hacc
      exact ⟨h1, h2, hx1, hx2, by linarith, (le_div_iff_nat hp).1 hfin⟩
    · simp only [hfin, ↓reduceIte]
      exact ih hlen hx1 hx2 ((lt_mul_iff_nat hp).1 (not_le.1 hfin))
  intro k
  induction k with
  | zero =>
    intro r a acc hr hacc hlen _ _ hy
    have hr0 : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr0
    exact (hnil acc a hacc hy).elim
  | succ k ih =>
    intro r a acc hr hacc hlen hx1 hx2 hy
    cases a with
    | cons j a' =>
      have hjS : j ∈ S₂ := hacc ▸ List.mem_append_right _ List.mem_cons_self
      have hxj : (x j : ℝ) ≤ ε := hxε j (List.mem_append_right _ hjS)
      by_cases hadd : 2 * lsum x (r ++ acc) < X
      · simp only [bwalk, hadd, ↓reduceIte]
        have hadd' : (lsum x (r ++ acc) : ℝ) < X / 2 := by
          have : (2 * lsum x (r ++ acc) : ℝ) < X := by exact_mod_cast hadd
          linarith
        have e : ∀ f : ι → ℕ, (lsum f (r ++ j :: acc) : ℝ) = lsum f (r ++ acc) + f j := by
          intro f; simp only [lsum_append, lsum_cons]; push_cast; ring
        refine ih r a' (j :: acc) hr (by simpa using hacc) (by simp at hlen ⊢; omega)
          ?_ ?_ ?_
        · rw [e]; linarith [(Nat.cast_nonneg (x j) : (0 : ℝ) ≤ x j)]
        · rw [e]; linarith
        · rw [e]; linarith [(Nat.cast_nonneg (y j) : (0 : ℝ) ≤ y j)]
      · simp only [bwalk, hadd, ↓reduceIte]
        have hX : (X : ℝ) / 2 ≤ lsum x (r ++ acc) := by
          have : (X : ℝ) ≤ 2 * lsum x (r ++ acc) := by exact_mod_cast not_lt.1 hadd
          linarith
        cases r with
        | nil => exact (hnil acc _ hacc hy).elim
        | cons i r' =>
          have hxi : (x i : ℝ) ≤ ε := hxε i (List.mem_append_left _ (hr.subset List.mem_cons_self))
          have e : (lsum x (i :: r' ++ acc) : ℝ) = x i + lsum x (r' ++ acc) := by
            simp only [List.cons_append, lsum_cons]; push_cast; ring
          rw [e] at hx1 hx2 hX
          have h0 : (0 : ℝ) ≤ x i := Nat.cast_nonneg _
          exact hrem k i r' (j :: a') acc hr hacc (by linarith) (by linarith) hy
            (fun hl h1 h2 h3 => ih r' (j :: a') acc ((List.suffix_cons i r').trans hr) hacc hl
              h1 h2 h3) (by simp at hlen ⊢; omega)
    | nil =>
      simp only [bwalk]
      have hAS : acc.reverse = S₂ := by simpa using hacc
      cases r with
      | nil => exact (hnil acc _ hacc hy).elim
      | cons i r' =>
        have e : (lsum x (i :: r' ++ acc) : ℝ) = x i + lsum x (r' ++ acc) := by
          simp only [List.cons_append, lsum_cons]; push_cast; ring
        rw [e] at hx1 hx2
        have h0 : (0 : ℝ) ≤ x i := Nat.cast_nonneg _
        have hS : (lsum x S₂ : ℝ) ≤ lsum x (r' ++ acc) := by
          rw [← hAS, lsum_reverse, lsum_append]
          exact_mod_cast Nat.le_add_left _ _
        exact hrem k i r' [] acc hr hacc (by linarith) (by linarith) hy
          (fun hl h1 h2 h3 => ih r' [] acc ((List.suffix_cons i r').trans hr) hacc hl h1 h2 h3)
          (by simp at hlen ⊢; omega)

end walk

/-- **The balanced split** (explicit form of `PlanarSeparator.exists_balanced_split`): for a nodup
list `l` of pieces with `x`-measures at most `ε` and `y`-measures at most `η`, with
`η + y(l) ≤ 2c`, `c = q/p`, the sublist `J = bsplit x y p q l` is nodup, inside `l`, has
`x`-measure within `ε` of half of `x(l)`, and `J` and the rest have `y`-measure at most `c`. -/
theorem bsplit_spec (x y : ι → ℕ) (p q : ℕ) (hp : 0 < p) {l : List ι} (hl : l.Nodup) {ε η : ℝ}
    (hε : 0 ≤ ε) (hxε : ∀ i ∈ l, (x i : ℝ) ≤ ε) (hyη : ∀ i ∈ l, (y i : ℝ) ≤ η) (hη : 0 ≤ η)
    (hc : η + lsum y l ≤ 2 * ((q : ℝ) / p)) :
    let J := bsplit x y p q l
    J.Nodup ∧ (∀ i ∈ J, i ∈ l) ∧ (lsum x l : ℝ) / 2 - ε ≤ lsum x J ∧
      (lsum x J : ℝ) ≤ lsum x l / 2 + ε ∧ (lsum y J : ℝ) ≤ (q : ℝ) / p ∧
      (lsum y l : ℝ) - lsum y J ≤ (q : ℝ) / p := by
  intro J
  set X := lsum x l with hX
  set J₁ := gpre x X 0 l with hJ₁
  set J₂ := l.drop J₁.length with hJ₂
  obtain ⟨hl12, hx1, hnext⟩ := gpre_spec x X l 0 (Nat.zero_le _)
  rw [← hJ₁, ← hJ₂] at hl12 hnext
  rw [← hJ₁, zero_add] at hx1
  set c : ℝ := (q : ℝ) / p
  have hXs : (X : ℝ) = lsum x J₁ + lsum x J₂ := by
    rw [hX]; conv_lhs => rw [← hl12]
    push_cast [lsum_append]; ring
  have hYs : (lsum y l : ℝ) = lsum y J₁ + lsum y J₂ := by
    conv_lhs => rw [← hl12]
    push_cast [lsum_append]; ring
  have hx1' : (lsum x J₁ : ℝ) ≤ X / 2 := by
    have : (2 * lsum x J₁ : ℝ) ≤ X := by exact_mod_cast hx1
    linarith
  have hx0 : (X : ℝ) / 2 - ε ≤ lsum x J₁ := by
    rcases hrest : J₂ with _ | ⟨i, rest⟩
    · rw [hrest] at hXs; simp only [lsum_nil, Nat.cast_zero, add_zero] at hXs
      have : (0 : ℝ) ≤ X := Nat.cast_nonneg _
      linarith
    · have h := hnext i rest hrest
      have hxi : (x i : ℝ) ≤ ε := hxε i (hl12 ▸ List.mem_append_right _ (hrest ▸ List.mem_cons_self))
      have : (X : ℝ) < 2 * (lsum x J₁ + x i) := by exact_mod_cast (by omega : X < 2 * (lsum x J₁ + x i))
      linarith
  have hmem12 : ∀ i, i ∈ J₁ ++ J₂ → i ∈ l := fun i hi => hl12 ▸ hi
  have hmem21 : ∀ i, i ∈ J₂ ++ J₁ → i ∈ l := fun i hi => hmem12 i (List.mem_append.2
    ((List.mem_append.1 hi).symm))
  have hnd12 : (J₁ ++ J₂).Nodup := hl12 ▸ hl
  have hnd21 : (J₂ ++ J₁).Nodup := (List.perm_append_comm.nodup_iff).1 hnd12
  have hXr : (lsum x l : ℝ) = X := rfl
  by_cases h1 : q < p * lsum y J₁
  · have h1' := (lt_mul_iff_nat hp).1 h1
    have hJ : J = bwalk x y X p q (J₁.length + J₂.length) J₁ J₂ [] := by
      simp only [J, bsplit, ← hX, ← hJ₁, ← hJ₂, h1, ↓reduceIte]
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := bwalk_spec x y X p q hp hnd12 (ε := ε) (η := η)
      (Y := lsum y l) (fun i hi => hxε i (hmem12 i hi))
      (fun i hi => hyη i (hmem12 i (List.mem_append_left _ hi))) hη hc (by linarith)
      (by linarith) (J₁.length + J₂.length) J₁ J₂ [] List.suffix_rfl (by simp) rfl (by simpa using hx0)
      (by simp only [List.append_nil]; linarith) (by simpa using h1')
    rw [← hJ] at k1 k2 k3 k4 k5 k6
    exact ⟨k1, fun i hi => hmem12 i (k2 i hi), hXr ▸ k3, hXr ▸ k4, k6, by linarith⟩
  by_cases h2 : q < p * lsum y J₂
  · have h2' := (lt_mul_iff_nat hp).1 h2
    have hJ : J = bwalk x y X p q (J₁.length + J₂.length) J₂ J₁ [] := by
      simp only [J, bsplit, ← hX, ← hJ₁, ← hJ₂, h1, h2, ↓reduceIte]
    obtain ⟨k1, k2, k3, k4, k5, k6⟩ := bwalk_spec x y X p q hp hnd21 (ε := ε) (η := η)
      (Y := lsum y l) (fun i hi => hxε i (hmem21 i hi))
      (fun i hi => hyη i (hmem21 i (List.mem_append_left _ hi))) hη hc hx0
      (by linarith) (J₁.length + J₂.length) J₂ J₁ [] List.suffix_rfl (by simp) (by omega)
      (by simp only [List.append_nil]; linarith) (by simp only [List.append_nil]; linarith)
      (by simpa using h2')
    rw [← hJ] at k1 k2 k3 k4 k5 k6
    exact ⟨k1, fun i hi => hmem21 i (k2 i hi), hXr ▸ k3, hXr ▸ k4, k6, by linarith⟩
  · have hJ : J = J₁ := by
      simp only [J, bsplit, ← hX, ← hJ₁, ← hJ₂, h1, h2, ↓reduceIte]
    rw [hJ]
    have h1' := (le_div_iff_nat hp).1 (not_lt.1 h1)
    have h2' := (le_div_iff_nat hp).1 (not_lt.1 h2)
    exact ⟨hnd12.of_append_left, fun i hi => hmem12 i (List.mem_append_left _ hi), hXr ▸ hx0,
      by rw [hXr]; linarith, h1', by linarith⟩

/-- `PlanarSeparator.bsplit_spec` with finite sets, in the form of
`PlanarSeparator.exists_balanced_split`. -/
theorem bsplit_spec' [DecidableEq ι] (x y : ι → ℕ) (p q : ℕ) (hp : 0 < p) {l : List ι}
    (hl : l.Nodup) {ε η : ℝ} (hε : 0 ≤ ε) (hxε : ∀ i ∈ l.toFinset, (x i : ℝ) ≤ ε)
    (hyη : ∀ i ∈ l.toFinset, (y i : ℝ) ≤ η) (hη : 0 ≤ η)
    (hc : η + ∑ i ∈ l.toFinset, (y i : ℝ) ≤ 2 * ((q : ℝ) / p)) :
    let J := (bsplit x y p q l).toFinset
    J ⊆ l.toFinset ∧ (∑ i ∈ l.toFinset, (x i : ℝ)) / 2 - ε ≤ ∑ i ∈ J, (x i : ℝ) ∧
      ∑ i ∈ J, (x i : ℝ) ≤ (∑ i ∈ l.toFinset, (x i : ℝ)) / 2 + ε ∧
      ∑ i ∈ J, (y i : ℝ) ≤ (q : ℝ) / p ∧ ∑ i ∈ l.toFinset \ J, (y i : ℝ) ≤ (q : ℝ) / p := by
  intro J
  have hs : ∀ (f : ι → ℕ) {m : List ι}, m.Nodup → ∑ i ∈ m.toFinset, (f i : ℝ) = lsum f m :=
    fun f m hm => by rw [lsum_eq_sum f hm]; push_cast; rfl
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := bsplit_spec x y p q hp hl hε (fun i hi => hxε i
    (List.mem_toFinset.2 hi)) (fun i hi => hyη i (List.mem_toFinset.2 hi)) hη (by rwa [← hs y hl])
  have hJl : J ⊆ l.toFinset := fun i hi => List.mem_toFinset.2 (k2 i (List.mem_toFinset.1 hi))
  refine ⟨hJl, ?_, ?_, ?_, ?_⟩
  · rw [hs x hl, hs x k1]; exact k3
  · rw [hs x hl, hs x k1]; exact k4
  · rw [hs y k1]; exact k5
  · have := sum_sdiff hJl (f := fun i => (y i : ℝ))
    rw [hs y hl, hs y k1] at this
    linarith

end lists

/-! ### Separator routines -/

section routine

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **separator routine** for `G` with constant `c`: a function returning, for a vertex set `U`
and natural weights `w`, a separation `(S, A, B)` of `U` with `#S ≤ c √(#U)` and parts of weight
at most `2/3` of the weight of `U`. -/
structure SepRoutine (G : SimpleGraph V) (c : ℝ) where
  /-- The separator, the first part and the second part. -/
  sep : Finset V → (V → ℕ) → Finset V × Finset V × Finset V
  isSeparation : ∀ U w, IsSeparation G U (sep U w).1 (sep U w).2.1 (sep U w).2.2
  card_le : ∀ U w, ((sep U w).1.card : ℝ) ≤ c * √(#U : ℝ)
  weight_left : ∀ U w, 3 * ∑ v ∈ (sep U w).2.1, w v ≤ 2 * ∑ v ∈ U, w v
  weight_right : ∀ U w, 3 * ∑ v ∈ (sep U w).2.2, w v ≤ 2 * ∑ v ∈ U, w v

namespace SepRoutine

variable {G : SimpleGraph V} {c : ℝ} (R : SepRoutine G c)

/-- A routine for `c` is one for every larger constant. -/
def mono {c' : ℝ} (h : c ≤ c') : SepRoutine G c' where
  sep := R.sep
  isSeparation := R.isSeparation
  card_le U w := (R.card_le U w).trans (by gcongr)
  weight_left := R.weight_left
  weight_right := R.weight_right

/-- **Division into light pieces** (explicit form of
`PlanarSeparator.exists_division_of_separators`), with fuel `k`: a set of weight at most `L` is
one piece; otherwise the routine separates `U` with the weights `μ` and both parts are divided.
Returns the separator vertices and the labels of the pieces. -/
def divide (sep : Finset V → (V → ℕ) → Finset V × Finset V × Finset V) (μ : V → ℕ) (L : ℕ) :
    ℕ → Finset V → Finset V × (V → Finset V)
  | 0, U => (∅, fun _ => U)
  | k + 1, U =>
    if ∑ v ∈ U, μ v ≤ L then (∅, fun _ => U)
    else
      let r := sep U μ
      let d₁ := divide sep μ L k r.2.1
      let d₂ := divide sep μ L k r.2.2
      (r.1 ∪ d₁.1 ∪ d₂.1, fun v => if v ∈ r.2.1 then d₁.2 v else d₂.2 v)

omit [Fintype V] in
/-- **The division** (as `PlanarSeparator.exists_division_of_separators`, with natural weights
`μ` and pieces of weight at most `L > 0`): `S ⊆ U` has at most `c √(#U) max 0 (3 μ(U)/L - 2)`
vertices, and the labels of `U \ S` are constant along edges, contain their vertex, lie in `U`,
and have classes of weight at most `L`, when the fuel is at least `#U`. -/
theorem divide_spec (hc : 0 ≤ c) (μ : V → ℕ) {L : ℕ} (hL : 0 < L) :
    ∀ (k : ℕ) (U : Finset V), #U ≤ k →
      let S := (divide R.sep μ L k U).1
      let κ := (divide R.sep μ L k U).2
      S ⊆ U ∧ (∀ v ∈ U \ S, v ∈ κ v ∧ κ v ⊆ U) ∧
      (∀ u ∈ U \ S, ∀ v ∈ U \ S, G.Adj u v → κ u = κ v) ∧
      (∀ i, ∑ v ∈ U \ S with κ v = i, μ v ≤ L) ∧
      (#S : ℝ) ≤ c * √(#U : ℝ) * max 0 (3 * ((∑ v ∈ U, μ v : ℕ) : ℝ) / L - 2) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hsub : ∀ (s s' : Finset V), s ⊆ s' → ∑ v ∈ s, μ v ≤ ∑ v ∈ s', μ v :=
    fun s s' h => sum_le_sum_of_subset_of_nonneg h fun v _ _ => Nat.zero_le _
  have htriv : ∀ U : Finset V, ∑ v ∈ U, μ v ≤ L →
      ∅ ⊆ U ∧ (∀ v ∈ U \ ∅, v ∈ (fun _ => U) v ∧ (fun _ => U) v ⊆ U) ∧
      (∀ u ∈ U \ ∅, ∀ v ∈ U \ ∅, G.Adj u v → (fun _ => U) u = (fun _ : V => U) v) ∧
      (∀ i, ∑ v ∈ U \ ∅ with (fun _ => U) v = i, μ v ≤ L) ∧
      ((#(∅ : Finset V) : ℕ) : ℝ) ≤ c * √(#U : ℝ) *
        max 0 (3 * ((∑ v ∈ U, μ v : ℕ) : ℝ) / L - 2) := fun U hU =>
    ⟨empty_subset _, fun v hv => ⟨by simpa using hv, subset_rfl⟩, fun _ _ _ _ _ => rfl,
      fun i => (hsub _ _ (fun v hv => by simpa using (mem_filter.1 hv).1)).trans hU,
      by simp only [card_empty, Nat.cast_zero]; positivity⟩
  intro k
  induction k with
  | zero =>
    intro U hU
    have hU0 : U = ∅ := card_eq_zero.1 (by omega)
    subst hU0
    exact htriv ∅ (by simp)
  | succ k ih =>
  intro U hU
  set Φ := ∑ v ∈ U, μ v with hΦdef
  by_cases hΦ : Φ ≤ L
  · have hd : divide R.sep μ L (k + 1) U = (∅, fun _ => U) := by
      simp only [divide, ← hΦdef, hΦ, ↓reduceIte]
    rw [hd]
    exact htriv U hΦ
  simp only [divide, ← hΦdef, hΦ, ↓reduceIte]
  push Not at hΦ
  set S₁ := (R.sep U μ).1
  set A₁ := (R.sep U μ).2.1
  set A₂ := (R.sep U μ).2.2
  have hsep : IsSeparation G U S₁ A₁ A₂ := R.isSeparation U μ
  have hA₁ : 3 * ∑ v ∈ A₁, μ v ≤ 2 * Φ := R.weight_left U μ
  have hA₂ : 3 * ∑ v ∈ A₂, μ v ≤ 2 * Φ := R.weight_right U μ
  have hS₁ : (#S₁ : ℝ) ≤ c * √(#U : ℝ) := R.card_le U μ
  have hA₁U : A₁ ⊆ U := fun x hx => hsep.union_eq ▸ mem_union_left _ (mem_union_right _ hx)
  have hA₂U : A₂ ⊆ U := fun x hx => hsep.union_eq ▸ mem_union_right _ hx
  have hS₁U : S₁ ⊆ U := fun x hx => hsep.union_eq ▸ mem_union_left _ (mem_union_left _ hx)
  have hlt : ∀ A ⊆ U, 3 * ∑ v ∈ A, μ v ≤ 2 * Φ → #A ≤ k := by
    intro A hAU hAμ
    have : #A < #U := by
      refine card_lt_card ⟨hAU, fun hUA => ?_⟩
      have := hsub _ _ hUA
      omega
    omega
  obtain ⟨hS'A, hκ₁, hadj₁, hpiece₁, hsize₁⟩ := ih A₁ (hlt A₁ hA₁U hA₁)
  obtain ⟨hS''A, hκ₂, hadj₂, hpiece₂, hsize₂⟩ := ih A₂ (hlt A₂ hA₂U hA₂)
  set S' := (divide R.sep μ L k A₁).1
  set S'' := (divide R.sep μ L k A₂).1
  set κ₁ := (divide R.sep μ L k A₁).2
  set κ₂ := (divide R.sep μ L k A₂).2
  have hdisj := hsep.disjoint
  set S := S₁ ∪ S' ∪ S''
  set κ : V → Finset V := fun v => if v ∈ A₁ then κ₁ v else κ₂ v
  -- vertices off `S`
  have hside : ∀ v ∈ U \ S, (v ∈ A₁ ∧ v ∈ A₁ \ S') ∨ (v ∉ A₁ ∧ v ∈ A₂ \ S'') := by
    intro v hv
    obtain ⟨hvU, hvS⟩ := mem_sdiff.1 hv
    simp only [S, mem_union, not_or] at hvS
    rw [← hsep.union_eq] at hvU
    simp only [mem_union] at hvU
    rcases hvU with (h | h) | h
    · exact absurd h hvS.1.1
    · exact Or.inl ⟨h, mem_sdiff.2 ⟨h, hvS.1.2⟩⟩
    · exact Or.inr ⟨fun h' => disjoint_left.1 hdisj h' h, mem_sdiff.2 ⟨h, hvS.2⟩⟩
  refine ⟨union_subset (union_subset hS₁U (hS'A.trans hA₁U)) (hS''A.trans hA₂U), ?_, ?_,
    ?_, ?_⟩
  · intro v hv
    rcases hside v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [ite_eq_left h1]
      exact ⟨(hκ₁ v h2).1, (hκ₁ v h2).2.trans hA₁U⟩
    · simp only [ite_eq_right h1]
      exact ⟨(hκ₂ v h2).1, (hκ₂ v h2).2.trans hA₂U⟩
  · intro u hu v hv huv
    rcases hside u hu with ⟨hu1, hu2⟩ | ⟨hu1, hu2⟩ <;>
      rcases hside v hv with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩
    · simp only [ite_eq_left hu1, ite_eq_left hv1]
      exact hadj₁ u hu2 v hv2 huv
    · exact absurd huv (hsep.not_adj u hu1 v (mem_sdiff.1 hv2).1)
    · exact absurd huv.symm (hsep.not_adj v hv1 u (mem_sdiff.1 hu2).1)
    · simp only [ite_eq_right hu1, ite_eq_right hv1]
      exact hadj₂ u hu2 v hv2 huv
  · intro i
    by_cases hi : ∃ v ∈ A₁ \ S', κ₁ v = i
    · obtain ⟨v₀, hv₀, rfl⟩ := hi
      refine (hsub _ ((A₁ \ S').filter fun v => κ₁ v = κ₁ v₀) fun v hv => ?_).trans
        (hpiece₁ _)
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      rcases hside v hv1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [ite_eq_left h1] at hv2
        exact mem_filter.2 ⟨h2, hv2⟩
      · simp only [ite_eq_right h1] at hv2
        have : v ∈ κ₁ v₀ := hv2 ▸ (hκ₂ v h2).1
        exact absurd ((hκ₁ v₀ hv₀).2 this) h1
    · push Not at hi
      refine (hsub _ ((A₂ \ S'').filter fun v => κ₂ v = i) fun v hv => ?_).trans (hpiece₂ _)
      obtain ⟨hv1, hv2⟩ := mem_filter.1 hv
      rcases hside v hv1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [ite_eq_left h1] at hv2
        exact absurd hv2 (hi v h2)
      · simp only [ite_eq_right h1] at hv2
        exact mem_filter.2 ⟨h2, hv2⟩
  · have hcard : (#S : ℝ) ≤ #S₁ + #S' + #S'' := by
      have h' : #S ≤ #S₁ + #S' + #S'' := by
        calc #S ≤ #(S₁ ∪ S') + #S'' := card_union_le _ _
          _ ≤ #S₁ + #S' + #S'' := by
            have := card_union_le S₁ S'
            omega
      exact_mod_cast h'
    have hsq : ∀ A ⊆ U, √(#A : ℝ) ≤ √(#U : ℝ) := fun A hA =>
      Real.sqrt_le_sqrt (by exact_mod_cast card_le_card hA)
    set Φ₁ : ℝ := ((∑ v ∈ A₁, μ v : ℕ) : ℝ) / L
    set Φ₂ : ℝ := ((∑ v ∈ A₂, μ v : ℕ) : ℝ) / L
    set Φ' : ℝ := (Φ : ℝ) / L
    have e1 : 3 * ((∑ v ∈ A₁, μ v : ℕ) : ℝ) / L = 3 * Φ₁ := by ring
    have e2 : 3 * ((∑ v ∈ A₂, μ v : ℕ) : ℝ) / L = 3 * Φ₂ := by ring
    have e : 3 * (Φ : ℝ) / L = 3 * Φ' := by ring
    rw [e1] at hsize₁
    rw [e2] at hsize₂
    rw [e]
    have h1 : (#S' : ℝ) ≤ c * √(#U : ℝ) * max 0 (3 * Φ₁ - 2) :=
      hsize₁.trans (by gcongr)
    have h2 : (#S'' : ℝ) ≤ c * √(#U : ℝ) * max 0 (3 * Φ₂ - 2) :=
      hsize₂.trans (by gcongr)
    have hdiv : ∀ a b : ℕ, a ≤ b → (a : ℝ) / L ≤ (b : ℝ) / L := fun a b h =>
      div_le_div_of_nonneg_right (by exact_mod_cast h) hL'.le
    have hΦ' : 1 < Φ' := by
      rw [lt_div_iff₀ hL', one_mul]; exact_mod_cast hΦ
    have hΦ₁ : Φ₁ ≤ 2 / 3 * Φ' := by
      have h3 : (3 * (∑ v ∈ A₁, μ v : ℕ) : ℝ) ≤ 2 * Φ := by exact_mod_cast hA₁
      simp only [Φ₁, Φ']
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by linarith) hL'.le
    have hΦ₂ : Φ₂ ≤ 2 / 3 * Φ' := by
      have h3 : (3 * (∑ v ∈ A₂, μ v : ℕ) : ℝ) ≤ 2 * Φ := by exact_mod_cast hA₂
      simp only [Φ₂, Φ']
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (by linarith) hL'.le
    have h12 : Φ₁ + Φ₂ ≤ Φ' := by
      have : ∑ v ∈ A₁, μ v + ∑ v ∈ A₂, μ v ≤ Φ := by
        rw [← sum_union hdisj]
        exact hsub _ _ (union_subset hA₁U hA₂U)
      have := hdiv _ _ this
      simp only [Φ₁, Φ₂, Φ']
      rw [← add_div]
      exact_mod_cast this
    have key := division_step_bound hΦ' hΦ₁ hΦ₂ h12
    have hsqU := Real.sqrt_nonneg (#U : ℝ)
    have : c * √(#U : ℝ) * (1 + max 0 (3 * Φ₁ - 2) + max 0 (3 * Φ₂ - 2))
        ≤ c * √(#U : ℝ) * max 0 (3 * Φ' - 2) := by
      gcongr
      exact key.trans (le_max_right _ _)
    linarith

end SepRoutine

end routine

/-! ### Splitting a node and the tree -/

section tree

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {c : ℝ} (R : SepRoutine G c)

namespace SepRoutine

variable (G) in
/-- **Splitting a node** (explicit form of `PlanarSeparator.exists_split_of_separators`). For a
vertex set `W` with `m` vertices and boundary `B` with `b` vertices: the division of `W ∪ B` with
the weights `20 max b 1` on `W` and `20 m` on `B` into pieces of weight at most `m max b 1`; the
pieces listed in the order of their first vertex in `ord`; the balanced split of this list for
the measures `#(piece ∩ W \ S)` and `#(piece ∩ B \ S)` with `c = 3 b / 5`. Returns the separator
`W ∩ S` and the two parts. -/
def splitW (sep : Finset V → (V → ℕ) → Finset V × Finset V × Finset V) (ord : List V) (W : Finset V) : Finset V × Finset V × Finset V :=
  let B := bdry G W
  let μ : V → ℕ := fun v => if v ∈ W then 20 * max #B 1 else if v ∈ B then 20 * #W else 0
  let d := divide sep μ (#W * max #B 1) #(W ∪ B) (W ∪ B)
  let S := d.1
  let κ := d.2
  let l := ((ord.filter (· ∈ (W ∪ B) \ S)).map κ).dedup
  let J := (bsplit (fun i => #((W \ S).filter fun v => κ v = i))
    (fun i => #((B \ S).filter fun v => κ v = i)) 5 (3 * #B) l).toFinset
  (W ∩ S, (W \ S).filter fun v => κ v ∈ J, (W \ S).filter fun v => κ v ∉ J)

/-- **The split of a node** satisfies the conclusion of
`PlanarSeparator.exists_split_of_separators`: for `T ≥ 40 (177 c + 1)`, a vertex set `W` with
more than `T²` vertices and at most `T √(#W)` boundary vertices is split by at most `T √(#W)` of
its vertices into two parts of at most `2/3` of its vertices, each with a boundary of at most
`T √m` vertices, `m` the size of the part. -/
theorem splitW_spec (hc : 0 ≤ c) {T : ℝ} (hT : sepTreeConst c ≤ T) {ord : List V}
    (hord : ∀ v, v ∈ ord) {W : Finset V} (hm : T ^ 2 < (#W : ℝ))
    (hb : (#(bdry G W) : ℝ) ≤ T * √(#W : ℝ)) {s₀ A₀ A₀' : Finset V}
    (h : splitW G R.sep ord W = (s₀, A₀, A₀')) :
    s₀ ∪ A₀ ∪ A₀' = W ∧ Disjoint s₀ A₀ ∧ Disjoint s₀ A₀' ∧ Disjoint A₀ A₀' ∧
      (∀ x ∈ A₀, ∀ y ∈ A₀', ¬ G.Adj x y) ∧ (#s₀ : ℝ) ≤ T * √(#W : ℝ) ∧
      3 * #A₀ ≤ 2 * #W ∧ 3 * #A₀' ≤ 2 * #W ∧
      (#(bdry G A₀) : ℝ) ≤ T * √(#A₀ : ℝ) ∧ (#(bdry G A₀') : ℝ) ≤ T * √(#A₀' : ℝ) := by
  have hT' : 7080 * c + 40 ≤ T := by simp only [sepTreeConst] at hT; linarith
  set B := bdry G W
  set m : ℝ := (#W : ℝ) with hmdef
  set b : ℝ := (#B : ℝ) with hbdef
  set s := √m with hsdef
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hb0 : 0 ≤ b := Nat.cast_nonneg _
  have hss : s * s = m := Real.mul_self_sqrt hm0
  have hs : T ≤ s := by
    rw [hsdef, Real.le_sqrt (by linarith) hm0]
    exact hm.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hmpos : 0 < m := by rw [← hss]; exact mul_pos (by linarith) (by linarith)
  have hss' : T * s ≤ s * s := mul_le_mul_of_nonneg_right hs hs0
  have hbs : b ≤ T * s := hb
  set K : ℝ := 177 * c * s with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hK1 : 10 * K ≤ s * s := by
    have : 1770 * c * s ≤ s * s := mul_le_mul_of_nonneg_right (by linarith) hs0
    linarith
  have hK2 : K ≤ 3 / 100 * (T * s) := by
    have : 177 * c * s ≤ (3 / 100 * T) * s := mul_le_mul_of_nonneg_right (by linarith) hs0
    linarith
  have hWB : Disjoint W B := disjoint_right.2 fun y hy => (mem_bdry.1 hy).1
  -- the weights
  set μ : V → ℝ := fun v => if v ∈ W then 20 / m else if v ∈ B then 20 / b else 0
  have hμ : ∀ v, 0 ≤ μ v := fun v => by
    simp only [μ]
    split_ifs <;> positivity
  have hμW : ∀ v ∈ W, μ v = 20 / m := fun v hv => by simp [μ, hv]
  have hμB : ∀ v ∈ B, μ v = 20 / b := fun v hv => by
    simp [μ, hv, disjoint_right.1 hWB hv]
  have hsumμ : ∑ v ∈ W ∪ B, μ v ≤ 40 := by
    rw [sum_union hWB, sum_congr rfl hμW, sum_congr rfl hμB, sum_const, sum_const,
      nsmul_eq_mul, nsmul_eq_mul, ← hmdef, ← hbdef, mul_div_cancel₀ _ hmpos.ne']
    rcases eq_or_lt_of_le hb0 with h | h
    · rw [← h]
      norm_num
    · rw [mul_div_cancel₀ _ h.ne']
      norm_num
  -- the natural weights of the explicit construction: `μ` scaled by `L = m max b 1`
  have hb1' : (0 : ℝ) < max b 1 := lt_max_of_lt_right one_pos
  have hW0 : 0 < #W := by
    have := hmpos
    rw [hmdef] at this
    exact_mod_cast this
  have hL : 0 < #W * max #B 1 := Nat.mul_pos hW0 (by omega)
  have hL' : (0 : ℝ) < ((#W * max #B 1 : ℕ) : ℝ) := by exact_mod_cast hL
  have hμμ : ∀ v, ((if v ∈ W then 20 * max #B 1 else if v ∈ B then 20 * #W else 0 : ℕ) : ℝ) /
      ((#W * max #B 1 : ℕ) : ℝ) = μ v := by
    intro v
    by_cases hvW : v ∈ W
    · simp only [μ, hvW, ↓reduceIte]
      push_cast
      rw [div_eq_div_iff (mul_pos hmpos hb1').ne' hmpos.ne']
      ring
    · by_cases hvB : v ∈ B
      · have hb1 : 1 ≤ #B := card_pos.2 ⟨v, hvB⟩
        have hbpos : 0 < b := by rw [hbdef]; exact_mod_cast hb1
        simp only [μ, hvW, hvB, ↓reduceIte, max_eq_left hb1]
        push_cast
        rw [div_eq_div_iff (mul_pos hmpos hbpos).ne' hbpos.ne']
        ring
      · simp [μ, hvW, hvB]
  have hsumn : ∀ t : Finset V,
      ((∑ v ∈ t, (if v ∈ W then 20 * max #B 1 else if v ∈ B then 20 * #W else 0) : ℕ) : ℝ) /
        ((#W * max #B 1 : ℕ) : ℝ) = ∑ v ∈ t, μ v := by
    intro t
    rw [Nat.cast_sum, sum_div]
    exact sum_congr rfl fun v _ => hμμ v
  have hdv := R.divide_spec hc (fun v => if v ∈ W then 20 * max #B 1 else if v ∈ B then 20 * #W
    else 0) hL #(W ∪ B) (W ∪ B) le_rfl
  dsimp only at hdv
  obtain ⟨hSU, hκ, hadj, hpiece', hsize'⟩ := hdv
  set S := (divide R.sep (fun v => if v ∈ W then 20 * max #B 1 else if v ∈ B then 20 * #W else 0)
    (#W * max #B 1) #(W ∪ B) (W ∪ B)).1 with hSdef
  set κ := (divide R.sep (fun v => if v ∈ W then 20 * max #B 1 else if v ∈ B then 20 * #W else 0)
    (#W * max #B 1) #(W ∪ B) (W ∪ B)).2 with hκdef
  have hpiece : ∀ i, ∑ v ∈ (W ∪ B) \ S with κ v = i, μ v ≤ 1 := by
    intro i
    rw [← hsumn, div_le_one hL']
    exact_mod_cast hpiece' i
  have hsize : (#S : ℝ) ≤ c * √(#(W ∪ B) : ℝ) * max 0 (3 * ∑ v ∈ W ∪ B, μ v - 2) := by
    rw [← hsumn, ← mul_div_assoc]
    exact hsize'
  -- the size of the separator
  have hcardU : (#(W ∪ B) : ℝ) = m + b := by
    rw [card_union_of_disjoint hWB]
    push_cast
    rfl
  have hsqrt : √(#(W ∪ B) : ℝ) ≤ 3 / 2 * s := by
    rw [hcardU]
    calc √(m + b) ≤ √((3 / 2 * s) ^ 2) := Real.sqrt_le_sqrt (by
          rw [show (3 / 2 * s) ^ 2 = 9 / 4 * (s * s) by ring]
          linarith)
      _ = 3 / 2 * s := Real.sqrt_sq (by linarith)
  have hS : (#S : ℝ) ≤ K := by
    have h1 : max 0 (3 * ∑ v ∈ W ∪ B, μ v - 2) ≤ 118 := max_le (by norm_num) (by linarith)
    have h2 := Real.sqrt_nonneg (#(W ∪ B) : ℝ)
    calc (#S : ℝ) ≤ c * √(#(W ∪ B) : ℝ) * max 0 (3 * ∑ v ∈ W ∪ B, μ v - 2) := hsize
      _ ≤ c * (3 / 2 * s) * 118 := by gcongr
      _ = K := by rw [hKdef]; ring
  -- the pieces and their two measures
  set I := ((W ∪ B) \ S).image κ
  set x : Finset V → ℝ := fun i => #((W \ S).filter fun v => κ v = i)
  set y : Finset V → ℝ := fun i => #((B \ S).filter fun v => κ v = i)
  have hWS : W \ S ⊆ (W ∪ B) \ S := sdiff_subset_sdiff subset_union_left subset_rfl
  have hBS : B \ S ⊆ (W ∪ B) \ S := sdiff_subset_sdiff subset_union_right subset_rfl
  have hpw : ∀ i, x i * (20 / m) ≤ 1 := fun i => by
    refine le_trans ?_ (hpiece i)
    calc x i * (20 / m) = ∑ v ∈ (W \ S).filter fun v => κ v = i, μ v := by
          rw [sum_congr rfl fun v hv => hμW v (mem_sdiff.1 (mem_filter.1 hv).1).1, sum_const,
            nsmul_eq_mul]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun v hv => mem_filter.2
          ⟨hWS (mem_filter.1 hv).1, (mem_filter.1 hv).2⟩) fun v _ _ => hμ v
  have hpb : ∀ i, y i * (20 / b) ≤ 1 := fun i => by
    refine le_trans ?_ (hpiece i)
    calc y i * (20 / b) = ∑ v ∈ (B \ S).filter fun v => κ v = i, μ v := by
          rw [sum_congr rfl fun v hv => hμB v (mem_sdiff.1 (mem_filter.1 hv).1).1, sum_const,
            nsmul_eq_mul]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun v hv => mem_filter.2
          ⟨hBS (mem_filter.1 hv).1, (mem_filter.1 hv).2⟩) fun v _ _ => hμ v
  have hxε : ∀ i ∈ I, x i ≤ m / 20 := fun i _ => by
    have := hpw i
    rw [mul_div_assoc', div_le_one hmpos] at this
    linarith
  have hyη : ∀ i ∈ I, y i ≤ b / 20 := fun i _ => by
    rcases eq_or_lt_of_le hb0 with h | h
    · have h' : (#B : ℝ) = 0 := h.symm
      have hB : B = ∅ := card_eq_zero.1 (by exact_mod_cast h')
      simp [y, hB, ← h]
    · have := hpb i
      rw [mul_div_assoc', div_le_one h] at this
      linarith
  have hsumx : ∑ i ∈ I, x i = #(W \ S) := by
    simp only [x]
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise fun v hv => mem_image_of_mem κ (hWS hv)]
  have hsumy : ∑ i ∈ I, y i = #(B \ S) := by
    simp only [y]
    rw [← Nat.cast_sum, ← card_eq_sum_card_fiberwise fun v hv => mem_image_of_mem κ (hBS hv)]
  have hY : (#(B \ S) : ℝ) ≤ b := by
    rw [hbdef]
    exact_mod_cast card_le_card sdiff_subset
  -- the explicit balanced split
  have hlI : (((ord.filter (· ∈ (W ∪ B) \ S)).map κ).dedup).toFinset = I := by
    ext i
    simp [I, hord]
  have hc35 : ((3 * #B : ℕ) : ℝ) / ((5 : ℕ) : ℝ) = 3 / 5 * b := by
    rw [hbdef]; push_cast; ring
  have hJ' := bsplit_spec' (fun i => #((W \ S).filter fun v => κ v = i))
    (fun i => #((B \ S).filter fun v => κ v = i)) 5 (3 * #B) (by norm_num)
    (List.nodup_dedup _) (ε := m / 20) (η := b / 20) (by positivity)
    (fun i hi => hxε i (hlI ▸ hi)) (fun i hi => hyη i (hlI ▸ hi)) (by positivity)
    (by rw [hlI, hc35]; change b / 20 + ∑ i ∈ I, y i ≤ _; rw [hsumy]; linarith)
  dsimp only at hJ'
  rw [hlI, hc35] at hJ'
  set J := (bsplit (fun i => #((W \ S).filter fun v => κ v = i))
    (fun i => #((B \ S).filter fun v => κ v = i)) 5 (3 * #B)
    (((ord.filter (· ∈ (W ∪ B) \ S)).map κ).dedup)).toFinset with hJdef
  obtain ⟨hJI, hJ1, hJ2, hJ3, hJ4⟩ := hJ'
  replace hJ1 : (∑ i ∈ I, x i) / 2 - m / 20 ≤ ∑ i ∈ J, x i := hJ1
  replace hJ2 : ∑ i ∈ J, x i ≤ (∑ i ∈ I, x i) / 2 + m / 20 := hJ2
  replace hJ3 : ∑ i ∈ J, y i ≤ 3 / 5 * b := hJ3
  replace hJ4 : ∑ i ∈ I \ J, y i ≤ 3 / 5 * b := hJ4
  rw [hsumx] at hJ1 hJ2
  have hJ4' : (#(B \ S) : ℝ) - ∑ i ∈ J, y i ≤ 3 / 5 * b := by
    have := sum_sdiff hJI (f := y)
    rw [hsumy] at this
    linarith
  -- the two parts
  set A := (W \ S).filter fun v => κ v ∈ J
  set A' := (W \ S).filter fun v => κ v ∉ J
  have hA : (#A : ℝ) = ∑ i ∈ J, x i := by
    simp only [A, x]
    rw [card_filter_mem_eq_sum, Nat.cast_sum]
  have hAA' : (#A : ℝ) + #A' = #(W \ S) := by
    exact_mod_cast card_filter_add_card_filter_not (s := W \ S) (p := fun v => κ v ∈ J)
  have hX : m - K ≤ #(W \ S) := by
    have h1 : #(W \ S) + #(W ∩ S) = #W := card_sdiff_add_card_inter W S
    have h2 : #(W ∩ S) ≤ #S := card_le_card inter_subset_right
    have : (#W : ℝ) ≤ #(W \ S) + #S := by exact_mod_cast (by omega : #W ≤ #(W \ S) + #S)
    linarith
  have hXm : (#(W \ S) : ℝ) ≤ m := by
    rw [hmdef]
    exact_mod_cast card_le_card sdiff_subset
  have hs531 : K / 2 ≤ m / 20 := by linarith
  have hAlow : 2 / 5 * m ≤ #A := by linarith
  have hAhigh : (#A : ℝ) ≤ 11 / 20 * m := by linarith
  have hA'low : 2 / 5 * m ≤ #A' := by linarith
  have hA'high : (#A' : ℝ) ≤ 11 / 20 * m := by linarith
  -- the boundaries of the parts
  have hbdry : ∀ (p : Finset V → Prop) [DecidablePred p],
      bdry G ((W \ S).filter fun v => p (κ v)) ⊆ S ∪ (B \ S).filter fun v => p (κ v) := by
    intro p _ z hz
    obtain ⟨hzA, a, ha, haz⟩ := mem_bdry.1 hz
    obtain ⟨haWS, hpa⟩ := mem_filter.1 ha
    by_cases hzS : z ∈ S
    · exact mem_union_left _ hzS
    have hzU : z ∈ W ∪ B := by
      by_cases hzW : z ∈ W
      · exact mem_union_left _ hzW
      · exact mem_union_right _ (mem_bdry.2 ⟨hzW, a, (mem_sdiff.1 haWS).1, haz⟩)
    have hκz : κ a = κ z := hadj a (hWS haWS) z (mem_sdiff.2 ⟨hzU, hzS⟩) haz
    rcases mem_union.1 hzU with hzW | hzB
    · exact absurd (mem_filter.2 ⟨mem_sdiff.2 ⟨hzW, hzS⟩, hκz ▸ hpa⟩) hzA
    · exact mem_union_right _ (mem_filter.2 ⟨mem_sdiff.2 ⟨hzB, hzS⟩, hκz ▸ hpa⟩)
  have hyJ : (#((B \ S).filter fun v => κ v ∈ J) : ℝ) = ∑ i ∈ J, y i := by
    simp only [y]
    rw [card_filter_mem_eq_sum, Nat.cast_sum]
  have hyJ' : (#((B \ S).filter fun v => κ v ∉ J) : ℝ) = #(B \ S) - ∑ i ∈ J, y i := by
    rw [← hyJ]
    have := card_filter_add_card_filter_not (s := B \ S) (p := fun v => κ v ∈ J)
    have : (#((B \ S).filter fun v => κ v ∈ J) : ℝ) + #((B \ S).filter fun v => κ v ∉ J) =
        #(B \ S) := by exact_mod_cast this
    linarith
  have hbA : (#(bdry G A) : ℝ) ≤ K + 3 / 5 * b := by
    have := (card_le_card (hbdry (fun i => i ∈ J))).trans (card_union_le _ _)
    have : (#(bdry G A) : ℝ) ≤ #S + #((B \ S).filter fun v => κ v ∈ J) := by
      exact_mod_cast this
    linarith
  have hbA' : (#(bdry G A') : ℝ) ≤ K + 3 / 5 * b := by
    have := (card_le_card (hbdry (fun i => i ∉ J))).trans (card_union_le _ _)
    have : (#(bdry G A') : ℝ) ≤ #S + #((B \ S).filter fun v => κ v ∉ J) := by
      exact_mod_cast this
    linarith
  have hroot : ∀ a : ℝ, 2 / 5 * m ≤ a → 63 / 100 * s ≤ √a := fun a ha => by
    rw [Real.le_sqrt (by positivity) (by linarith),
      show (63 / 100 * s) ^ 2 = 3969 / 10000 * (s * s) by ring]
    linarith
  have hr : splitW G R.sep ord W = (W ∩ S, A, A') := rfl
  rw [hr] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [union_assoc, filter_union_filter_not_eq, union_comm, sdiff_union_inter]
  · exact disjoint_left.2 fun v hv hvA => (mem_sdiff.1 (mem_filter.1 hvA).1).2 (mem_inter.1 hv).2
  · exact disjoint_left.2 fun v hv hvA => (mem_sdiff.1 (mem_filter.1 hvA).1).2 (mem_inter.1 hv).2
  · exact disjoint_filter_filter_not _ _ _
  · intro u hu v hv huv
    exact (mem_filter.1 hv).2 (hadj u (hWS (mem_filter.1 hu).1) v (hWS (mem_filter.1 hv).1) huv ▸
      (mem_filter.1 hu).2)
  · have : (#(W ∩ S) : ℝ) ≤ #S := by exact_mod_cast card_le_card inter_subset_right
    have : 0 ≤ T * s := mul_nonneg (by linarith) hs0
    linarith
  · have : (3 * #A : ℝ) ≤ 2 * #W := by linarith
    exact_mod_cast this
  · have : (3 * #A' : ℝ) ≤ 2 * #W := by linarith
    exact_mod_cast this
  · have := mul_le_mul_of_nonneg_left (hroot _ hAlow) (show 0 ≤ T by linarith)
    linarith
  · have := mul_le_mul_of_nonneg_left (hroot _ hA'low) (show 0 ≤ T by linarith)
    linarith


variable (G) in
/-- The separator tree from the vertex set `W` down, with fuel `k`: a leaf if `#W ≤ T²`,
otherwise the node of `PlanarSeparator.SepRoutine.splitW`. -/
def buildAux (sep : Finset V → (V → ℕ) → Finset V × Finset V × Finset V) (ord : List V) (T : ℕ) :
    ℕ → Finset V → SepTree V
  | 0, W => leaf W
  | k + 1, W =>
    if #W ≤ T ^ 2 then leaf W
    else
      let r := splitW G sep ord W
      node r.1 (buildAux sep ord T k r.2.1) (buildAux sep ord T k r.2.2)

variable (G) in
/-- **The explicit separator tree** of `G` from the separator routine `R`, the vertex order `ord`
and the natural constant `T`. -/
def buildTree (sep : Finset V → (V → ℕ) → Finset V × Finset V × Finset V) (ord : List V) (T : ℕ) : SepTree V :=
  buildAux G sep ord T (Fintype.card V) univ

/-- **The tree from a vertex set** (explicit form of
`PlanarSeparator.exists_sepTree_of_bdry_of_separators`): for a natural `T ≥ 40 (177 c + 1)` and a
vertex set `W` with at most `T √(#W)` boundary vertices, the tree `buildAux G R.sep ord T k W` (fuel
`k ≥ #W`) has vertex set `W`, is a separator tree of `G`, has separators and boundaries of at
most `T √m` vertices at every subtree with `m` vertices, and parts of at most `2m/3` vertices. -/
theorem buildAux_spec (hc : 0 ≤ c) {T : ℕ} (hT : sepTreeConst c ≤ T) {ord : List V}
    (hord : ∀ v, v ∈ ord) :
    ∀ (k : ℕ) (W : Finset V), #W ≤ k → (#(bdry G W) : ℝ) ≤ T * √(#W : ℝ) →
      (buildAux G R.sep ord T k W).verts = W ∧ IsDissection G (buildAux G R.sep ord T k W) ∧
      AllNodes (SqrtBound G T T) (buildAux G R.sep ord T k W) ∧
      AllNodes Shrinks (buildAux G R.sep ord T k W) := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (by simp only [sepTreeConst]; positivity) hT
  have hleaf : ∀ W : Finset V, (#W : ℝ) ≤ (T : ℝ) ^ 2 → (#(bdry G W) : ℝ) ≤ T * √(#W : ℝ) →
      (leaf W : SepTree V).verts = W ∧ IsDissection G (leaf W) ∧
        AllNodes (SqrtBound G T T) (leaf W) ∧ AllNodes Shrinks (leaf W : SepTree V) := by
    intro W hsmall hW
    refine ⟨rfl, trivial, ⟨?_, hW⟩, trivial⟩
    change (#W : ℝ) ≤ T * √(#W : ℝ)
    have h0 : (0 : ℝ) ≤ #W := Nat.cast_nonneg _
    have h1 : √(#W : ℝ) ≤ T := by
      rw [Real.sqrt_le_left hT0.le]
      exact hsmall
    have h2 := Real.mul_self_sqrt h0
    have h3 := Real.sqrt_nonneg (#W : ℝ)
    nlinarith
  intro k
  induction k with
  | zero =>
    intro W hk hW
    have hW0 : W = ∅ := card_eq_zero.1 (by omega)
    subst hW0
    exact hleaf ∅ (by simp) hW
  | succ k ih =>
  intro W hk hW
  by_cases hsmall : #W ≤ T ^ 2
  · have hd : buildAux G R.sep ord T (k + 1) W = leaf W := by
      simp only [buildAux, hsmall, ↓reduceIte]
    rw [hd]
    exact hleaf W (by exact_mod_cast hsmall) hW
  have hd : buildAux G R.sep ord T (k + 1) W = node (splitW G R.sep ord W).1
      (buildAux G R.sep ord T k (splitW G R.sep ord W).2.1) (buildAux G R.sep ord T k (splitW G R.sep ord W).2.2) := by
    simp only [buildAux, hsmall, ↓reduceIte]
  rw [hd]
  have hsmall' : (T : ℝ) ^ 2 < (#W : ℝ) := by exact_mod_cast not_le.1 hsmall
  obtain ⟨hunion, hsA, hsA', hAA', hadj, hs, hA, hA', hbA, hbA'⟩ :=
    R.splitW_spec hc hT hord hsmall' hW (s₀ := (splitW G R.sep ord W).1) (A₀ := (splitW G R.sep ord W).2.1)
      (A₀' := (splitW G R.sep ord W).2.2) rfl
  set s := (splitW G R.sep ord W).1
  set A := (splitW G R.sep ord W).2.1
  set A' := (splitW G R.sep ord W).2.2
  have hW0 : 0 < #W := by
    have : (0 : ℝ) < #W := lt_of_le_of_lt (by positivity) hsmall'
    exact_mod_cast this
  obtain ⟨hta, hda, hsa, hsha⟩ := ih A (by omega) hbA
  obtain ⟨htb, hdb, hsb, hshb⟩ := ih A' (by omega) hbA'
  set ta := buildAux G R.sep ord T k A
  set tb := buildAux G R.sep ord T k A'
  have hverts : (node s ta tb).verts = W := by
    simp only [verts, hta, htb]
    exact hunion
  refine ⟨hverts, ?_, ⟨⟨?_, ?_⟩, hsa, hsb⟩, ⟨?_, hsha, hshb⟩⟩
  · exact ⟨hta ▸ hsA, htb ▸ hsA', hta ▸ htb ▸ hAA', hta ▸ htb ▸ hadj, hda, hdb⟩
  · rw [hverts]
    exact hs
  · rw [hverts]
    exact hW
  · change 3 * #ta.verts ≤ 2 * #(node s ta tb).verts ∧ 3 * #tb.verts ≤ 2 * #(node s ta tb).verts
    rw [hverts, hta, htb]
    exact ⟨hA, hA'⟩

end SepRoutine

/-- The properties of a separator tree used by nested dissection: it covers all
vertices, is a separator tree of `G`, has separators and boundaries of at most `T √m` vertices
at every subtree with `m` vertices, and parts of at most `2m/3` vertices. -/
def GoodTree (G : SimpleGraph V) [DecidableRel G.Adj] (T : ℝ) (t : SepTree V) : Prop :=
  t.verts = univ ∧ IsDissection G t ∧ AllNodes (SqrtBound G T T) t ∧ AllNodes Shrinks t

namespace SepRoutine

/-- **The explicit separator tree is good**: for a separator routine with constant `c ≥ 0`, a
list `ord` of all vertices and a natural `T ≥ 40 (177 c + 1)`, `buildTree G R.sep ord T` satisfies
`GoodTree G T`. -/
theorem buildTree_spec (hc : 0 ≤ c) {T : ℕ} (hT : sepTreeConst c ≤ T) {ord : List V}
    (hord : ∀ v, v ∈ ord) : GoodTree G T (buildTree G R.sep ord T) :=
  R.buildAux_spec hc hT hord _ univ (card_le_univ _) (by
    rw [bdry_univ, card_empty, Nat.cast_zero]
    positivity)

end SepRoutine

end tree

/-! ### Routines: by choice, and for the square -/

section routines

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
/-- `c √m`-separators with natural weights. -/
theorem HasSqrtSeparators.exists_nat {c : ℝ} (hG : HasSqrtSeparators G c) (U : Finset V)
    (w : V → ℕ) :
    ∃ S A B, IsSeparation G U S A B ∧ (#S : ℝ) ≤ c * √(#U : ℝ) ∧
      3 * ∑ v ∈ A, w v ≤ 2 * ∑ v ∈ U, w v ∧ 3 * ∑ v ∈ B, w v ≤ 2 * ∑ v ∈ U, w v := by
  set Φ := ∑ v ∈ U, w v with hΦ
  obtain ⟨S, A, B, hsep, hS, hA, hB⟩ := hG U (fun v => (w v : ℝ) / Φ)
    (fun v => by positivity) (by
      rw [← sum_div]
      rcases Nat.eq_zero_or_pos Φ with h | h
      · simp [h]
      · rw [div_le_one (by exact_mod_cast h)]
        push_cast [hΦ]; rfl)
  refine ⟨S, A, B, hsep, hS, ?_, ?_⟩ <;>
  · rename_i hX
    rcases Nat.eq_zero_or_pos Φ with h | h
    · have hAU : ∀ X ⊆ U, ∑ v ∈ X, w v ≤ Φ := fun X hX =>
        sum_le_sum_of_subset_of_nonneg hX fun _ _ _ => Nat.zero_le _
      first
      | (have := hAU A (fun x hx => hsep.union_eq ▸ mem_union_left _ (mem_union_right _ hx));
         omega)
      | (have := hAU B (fun x hx => hsep.union_eq ▸ mem_union_right _ hx); omega)
    · have hΦ0 : (0 : ℝ) < Φ := by exact_mod_cast h
      first
      | (rw [← sum_div, div_le_iff₀ hΦ0] at hA
         have : (3 * ∑ v ∈ A, w v : ℝ) ≤ 2 * Φ := by push_cast at hA ⊢; linarith
         exact_mod_cast this)
      | (rw [← sum_div, div_le_iff₀ hΦ0] at hB
         have : (3 * ∑ v ∈ B, w v : ℝ) ≤ 2 * Φ := by push_cast at hB ⊢; linarith
         exact_mod_cast this)

namespace SepRoutine

/-- A separator routine for a graph with `c √m`-separators, by choice (this shows that the
specification of separator routines can be met; the trees built from it are explicit in it). -/
noncomputable def ofHasSqrtSeparators {c : ℝ} (hG : HasSqrtSeparators G c) : SepRoutine G c where
  sep U w := ((hG.exists_nat U w).choose, (hG.exists_nat U w).choose_spec.choose,
    (hG.exists_nat U w).choose_spec.choose_spec.choose)
  isSeparation U w := (hG.exists_nat U w).choose_spec.choose_spec.choose_spec.1
  card_le U w := (hG.exists_nat U w).choose_spec.choose_spec.choose_spec.2.1
  weight_left U w := (hG.exists_nat U w).choose_spec.choose_spec.choose_spec.2.2.1
  weight_right U w := (hG.exists_nat U w).choose_spec.choose_spec.choose_spec.2.2.2

variable [DecidableRel G.Adj] {c : ℝ}

/-- **The separator routine of the square** (explicit form of
`PlanarSeparator.HasSqrtSeparators.square`): to separate `U` in the square of `G`, separate the
closed neighbourhood `U'` of `U` in `G` with the weights restricted to `U`, and put into the
separator the vertices of `U` in the closed neighbourhood of the separator. -/
def square (R : SepRoutine G c) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    SepRoutine (PlanarSeparator.square G) (c * (Δ + 1) * √((Δ : ℝ) + 1)) where
  sep U w :=
    let r := R.sep (closedNbhd G U) (fun v => if v ∈ U then w v else 0)
    let N := closedNbhd G r.1
    (U ∩ N, (r.2.1 ∩ U) \ N, (r.2.2 ∩ U) \ N)
  isSeparation U w := by
    dsimp only
    set U' := closedNbhd G U
    have hUU' : U ⊆ U' := subset_closedNbhd U
    have hsep := R.isSeparation U' (fun v => if v ∈ U then w v else 0)
    set S := (R.sep U' (fun v => if v ∈ U then w v else 0)).1
    set A := (R.sep U' (fun v => if v ∈ U then w v else 0)).2.1
    set B := (R.sep U' (fun v => if v ∈ U then w v else 0)).2.2
    set N := closedNbhd G S
    have hSN : S ⊆ N := subset_closedNbhd S
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext v
      simp only [mem_union, mem_inter, mem_sdiff]
      constructor
      · rintro ((h | h) | h)
        · exact h.1
        · exact h.1.2
        · exact h.1.2
      · intro hv
        by_cases hvN : v ∈ N
        · exact Or.inl (Or.inl ⟨hv, hvN⟩)
        have hvU' : v ∈ S ∪ A ∪ B := hsep.union_eq ▸ hUU' hv
        simp only [mem_union] at hvU'
        rcases hvU' with (h | h) | h
        · exact absurd (hSN h) hvN
        · exact Or.inl (Or.inr ⟨⟨h, hv⟩, hvN⟩)
        · exact Or.inr ⟨⟨h, hv⟩, hvN⟩
    · exact disjoint_left.2 fun v hv hv' => (mem_sdiff.1 hv').2 (mem_inter.1 hv).2
    · exact disjoint_left.2 fun v hv hv' => (mem_sdiff.1 hv').2 (mem_inter.1 hv).2
    · exact disjoint_of_subset_left (fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).1)
        (disjoint_of_subset_right (fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).1) hsep.disjoint)
    · intro a ha b hb hab
      obtain ⟨hai, haN⟩ := mem_sdiff.1 ha
      obtain ⟨haA, haU⟩ := mem_inter.1 hai
      have hbB := (mem_inter.1 (mem_sdiff.1 hb).1).1
      rcases hab.2 with h | ⟨k, hak, hkb⟩
      · exact hsep.not_adj a haA b hbB h
      · have hkU' : k ∈ S ∪ A ∪ B := hsep.union_eq ▸ mem_closedNbhd_of_adj haU hak
        simp only [mem_union] at hkU'
        rcases hkU' with (h | h) | h
        · exact haN (mem_closedNbhd_of_adj h hak.symm)
        · exact hsep.not_adj k h b hbB hkb
        · exact hsep.not_adj a haA k h hak
  card_le U w := by
    dsimp only
    rcases U.eq_empty_or_nonempty with hU | hU
    · subst hU
      simp
    set U' := closedNbhd G U
    set S := (R.sep U' (fun v => if v ∈ U then w v else 0)).1
    have hS := R.card_le U' (fun v => if v ∈ U then w v else 0)
    have hc : 0 ≤ c := by
      have hpos : 0 < √(#U' : ℝ) := Real.sqrt_pos.2
        (by exact_mod_cast card_pos.2 (hU.mono (subset_closedNbhd U)))
      by_contra hc
      push Not at hc
      have := mul_neg_of_neg_of_pos hc hpos
      have h0 : (0 : ℝ) ≤ #S := Nat.cast_nonneg _
      linarith
    have h1 : #(U ∩ closedNbhd G S) ≤ (Δ + 1) * #S :=
      (card_le_card inter_subset_right).trans (card_closedNbhd_le hΔ S)
    have h2 : (#U' : ℝ) ≤ (Δ + 1) * #U := by exact_mod_cast card_closedNbhd_le hΔ U
    have h3 : √(#U' : ℝ) ≤ √((Δ : ℝ) + 1) * √(#U : ℝ) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt h2
    have h1' : (#(U ∩ closedNbhd G S) : ℝ) ≤ (Δ + 1) * #S := by exact_mod_cast h1
    calc (#(U ∩ closedNbhd G S) : ℝ) ≤ (Δ + 1) * #S := h1'
      _ ≤ (Δ + 1) * (c * √(#U' : ℝ)) := by gcongr
      _ ≤ (Δ + 1) * (c * (√((Δ : ℝ) + 1) * √(#U : ℝ))) := by gcongr
      _ = c * (Δ + 1) * √((Δ : ℝ) + 1) * √(#U : ℝ) := by ring
  weight_left U w := by
    dsimp only
    set U' := closedNbhd G U
    have hUU' : U ⊆ U' := subset_closedNbhd U
    have hA := R.weight_left U' (fun v => if v ∈ U then w v else 0)
    set A := (R.sep U' (fun v => if v ∈ U then w v else 0)).2.1
    set N := closedNbhd G (R.sep U' (fun v => if v ∈ U then w v else 0)).1
    have e1 : ∑ v ∈ U', (if v ∈ U then w v else 0) = ∑ v ∈ U, w v := by
      rw [← sum_subset hUU' fun v _ hv => by simp [hv]]
      exact sum_congr rfl fun v hv => by simp [hv]
    have e2 : ∑ v ∈ (A ∩ U) \ N, w v ≤ ∑ v ∈ A, (if v ∈ U then w v else 0) := by
      calc ∑ v ∈ (A ∩ U) \ N, w v = ∑ v ∈ (A ∩ U) \ N, (if v ∈ U then w v else 0) :=
            sum_congr rfl fun v hv => by simp [(mem_inter.1 (mem_sdiff.1 hv).1).2]
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg
            (fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).1) fun _ _ _ => Nat.zero_le _
    omega
  weight_right U w := by
    dsimp only
    set U' := closedNbhd G U
    have hUU' : U ⊆ U' := subset_closedNbhd U
    have hA := R.weight_right U' (fun v => if v ∈ U then w v else 0)
    set A := (R.sep U' (fun v => if v ∈ U then w v else 0)).2.2
    set N := closedNbhd G (R.sep U' (fun v => if v ∈ U then w v else 0)).1
    have e1 : ∑ v ∈ U', (if v ∈ U then w v else 0) = ∑ v ∈ U, w v := by
      rw [← sum_subset hUU' fun v _ hv => by simp [hv]]
      exact sum_congr rfl fun v hv => by simp [hv]
    have e2 : ∑ v ∈ (A ∩ U) \ N, w v ≤ ∑ v ∈ A, (if v ∈ U then w v else 0) := by
      calc ∑ v ∈ (A ∩ U) \ N, w v = ∑ v ∈ (A ∩ U) \ N, (if v ∈ U then w v else 0) :=
            sum_congr rfl fun v hv => by simp [(mem_inter.1 (mem_sdiff.1 hv).1).2]
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg
            (fun v hv => (mem_inter.1 (mem_sdiff.1 hv).1).1) fun _ _ _ => Nat.zero_le _
    omega

/-- **The explicit separator tree of the square.** For a separator routine `R` of `G` with
constant `c ≥ 0`, maximum degree at most `Δ`, a list `ord` of all vertices and a natural
`T ≥ 40 (177 c (Δ + 1)² + 1)`, the tree `buildTree (square G) (R.square hΔ).sep ord T` is a good
tree of the
square of `G`. -/
theorem buildTree_square_spec (R : SepRoutine G c) (hc : 0 ≤ c) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {T : ℕ} (hT : sepTreeConst (c * ((Δ : ℝ) + 1) ^ 2) ≤ T)
    {ord : List V} (hord : ∀ v, v ∈ ord) :
    GoodTree (PlanarSeparator.square G) T (buildTree (PlanarSeparator.square G) (R.square hΔ).sep ord T) := by
  have h0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ
  have hsq : √((Δ : ℝ) + 1) ≤ (Δ : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hle : c * (Δ + 1) * √((Δ : ℝ) + 1) ≤ c * ((Δ : ℝ) + 1) ^ 2 := by
    calc c * (Δ + 1) * √((Δ : ℝ) + 1) ≤ c * ((Δ : ℝ) + 1) * ((Δ : ℝ) + 1) := by gcongr
      _ = c * ((Δ : ℝ) + 1) ^ 2 := by ring
  exact ((R.square hΔ).mono hle).buildTree_spec (by positivity) hT hord

end SepRoutine

/-! ### The existence statements recovered -/

variable [DecidableRel G.Adj] {R : Kasteleyn.RotationSystem G}

/-- `PlanarSeparator.exists_sepTree` from the explicit construction. -/
theorem exists_goodTree_explicit (hR : R.IsPlane) : ∃ t : SepTree V, GoodTree G treeConst t := by
  have h := (SepRoutine.ofHasSqrtSeparators (hasSqrtSeparators_of_isPlane hR)).buildTree_spec
    (by norm_num) (T := 50000) (by norm_num [sepTreeConst]) (ord := univ.toList)
    (fun v => mem_toList.2 (mem_univ v))
  exact ⟨_, by simpa [treeConst] using h⟩

/-- The natural constant `40 (1062 (Δ + 1)² + 1)` of the separator trees of squares of plane
graphs of maximum degree `Δ`. -/
def squareTreeNat (Δ : ℕ) : ℕ := 40 * (1062 * (Δ + 1) ^ 2 + 1)

lemma squareTreeNat_cast (Δ : ℕ) : (squareTreeNat Δ : ℝ) = squareTreeConst Δ := by
  simp [squareTreeNat, squareTreeConst]

lemma sepTreeConst_square_six (Δ : ℕ) :
    sepTreeConst (6 * ((Δ : ℝ) + 1) ^ 2) = squareTreeNat Δ := by
  rw [squareTreeNat_cast, sepTreeConst, squareTreeConst]; ring

/-- `PlanarSeparator.exists_sepTree_square` from the explicit construction. -/
theorem exists_goodTree_square_explicit (hR : R.IsPlane) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) :
    ∃ t : SepTree V, GoodTree (PlanarSeparator.square G) (squareTreeConst Δ) t := by
  have h := (SepRoutine.ofHasSqrtSeparators (hasSqrtSeparators_of_isPlane hR)).buildTree_square_spec
    (by norm_num) hΔ (T := squareTreeNat Δ) (sepTreeConst_square_six Δ).le
    (ord := univ.toList) (fun v => mem_toList.2 (mem_univ v))
  exact ⟨_, by rwa [squareTreeNat_cast] at h⟩

end routines

end PlanarSeparator
