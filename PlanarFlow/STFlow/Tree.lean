module

public import PlanarFlow.Plane.Map

/-!
# Rooted spanning trees of the dual graph

The maximum-flow algorithm of Borradaile and Klein (*An `O(n log n)` algorithm for maximum
`st`-flow in a directed planar graph*, J. ACM 56(2), 2009), in the parametric form of Erickson
(*Maximum flows and parametric shortest paths in planar graphs*, SODA 2010), maintains a spanning
tree `T*` of the dual graph rooted at a face `o`, and changes it by *pivots*: one face gets a new
parent. This file contains the combinatorics of such trees.

A tree (`DTree`) is given by a parent dart `par x` for every face `x ≠ root`, a dart of the dual
from the face `face (par x)` (the parent) to the face `face (rev (par x)) = x`; following parents
from any face reaches the root (`DTree.reach`).

* `DTree.depth`: the number of steps to the root, less than the number of faces
  (`depth_lt_card`).
* `DTree.Anc b x`: `b` is on the path from `x` to the root.
* `DTree.psum φ x`: the sum of `φ` over the parent darts on the path from the root to `x`; it is
  the unique function vanishing at the root with `psum φ x = psum φ (up x) + φ (par x)`
  (`psum_unique`). For a coboundary, `psum (cob ψ) x = ψ x - ψ root` (`psum_cob`).
* `DTree.reparent`: the pivot. If `b ≠ root` is not on the path from `face e` to the root and `e`
  enters `b`, giving `b` the parent dart `e` yields a tree, in which the path sums change by a
  constant on the subtree of `b` and nowhere else (`psum_reparent`).
* `DTree.eq_zero_of_dualCirc`: **a tree supports no nonzero circulation**: an antisymmetric
  function on the darts that vanishes off the edges of the tree and has zero net flow around every
  face vanishes.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- One step towards the root `r` along the parent darts `p`. -/
def upF (r : F) (p : F → D) (x : F) : F := if x = r then r else M.face (p x)

variable (M) in
/-- **A spanning tree of the dual graph**, rooted at `root`: the face `x ≠ root` has the parent
dart `par x`, which enters `x` in the dual, and following parents reaches the root. -/
structure DTree where
  /-- The root face. -/
  root : F
  /-- The parent dart of a face (unused at the root). -/
  par : F → D
  head_par : ∀ x, x ≠ root → M.face (M.rev (par x)) = x
  reach : ∀ x, ∃ n, (upF M root par)^[n] x = root

namespace DTree

variable (T : DTree M)

/-- The parent of a face (the root for the root). -/
def up : F → F := upF M T.root T.par

lemma up_root : T.up T.root = T.root := by simp [up, upF]

lemma up_of_ne {x : F} (h : x ≠ T.root) : T.up x = M.face (T.par x) := by simp [up, upF, h]

lemma iterate_root (n : ℕ) : T.up^[n] T.root = T.root := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, up_root, ih]

/-- The number of steps from `x` to the root. -/
def depth (x : F) : ℕ := Nat.find (T.reach x)

lemma iterate_depth (x : F) : T.up^[T.depth x] x = T.root := Nat.find_spec (T.reach x)

lemma iterate_ne_root {x : F} {i : ℕ} (h : i < T.depth x) : T.up^[i] x ≠ T.root :=
  Nat.find_min (T.reach x) h

lemma iterate_of_le {x : F} {n : ℕ} (h : T.depth x ≤ n) : T.up^[n] x = T.root := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm, Function.iterate_add_apply, iterate_depth, iterate_root]

lemma depth_root : T.depth T.root = 0 :=
  Nat.eq_zero_of_le_zero (Nat.find_min' (T.reach T.root) rfl)

lemma depth_up {x : F} (h : x ≠ T.root) : T.depth x = T.depth (T.up x) + 1 := by
  have h0 : 0 < T.depth x := by
    by_contra h'
    have : T.depth x = 0 := by omega
    have := T.iterate_depth x
    rw [‹T.depth x = 0›] at this
    exact h this
  apply le_antisymm
  · apply Nat.find_min'
    show T.up^[T.depth (T.up x) + 1] x = T.root
    rw [Function.iterate_succ_apply, iterate_depth]
  · have : T.depth (T.up x) ≤ T.depth x - 1 := by
      apply Nat.find_min'
      show T.up^[T.depth x - 1] (T.up x) = T.root
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel h0,
        iterate_depth]
    omega

lemma depth_lt_card (x : F) : T.depth x < Fintype.card F := by
  have hinj : Function.Injective fun i : Fin (T.depth x + 1) => T.up^[i] x := by
    intro i j hij
    simp only at hij
    by_contra hne
    wlog hlt : (i : ℕ) < j generalizing i j
    · exact this hij.symm (Ne.symm hne) (by have : (i : ℕ) ≠ j := fun h => hne (Fin.ext h); omega)
    -- the iterates from `i` on are periodic of period `j - i`
    have hper : ∀ m, T.up^[i + m * (j - i)] x = T.up^[i] x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have : (i : ℕ) + (m + 1) * (j - i) = (j - i) + (i + m * (j - i)) := by ring
        rw [this, Function.iterate_add_apply, ih, ← Function.iterate_add_apply,
          Nat.sub_add_cancel hlt.le, ← hij]
    have hbig := hper (T.depth x + 1)
    rw [iterate_of_le T (by nlinarith [Nat.sub_pos_of_lt hlt])] at hbig
    exact T.iterate_ne_root (show (i : ℕ) < T.depth x by omega) hbig.symm
  have := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at this
  omega

/-! ### Ancestors -/

/-- `b` is on the path from `x` to the root (`x` included). -/
def Anc (b x : F) : Prop := ∃ n, T.up^[n] x = b

lemma anc_self (x : F) : T.Anc x x := ⟨0, rfl⟩

lemma anc_root_iff {b : F} : T.Anc b T.root ↔ b = T.root := by
  constructor
  · rintro ⟨n, hn⟩; rw [iterate_root] at hn; exact hn.symm
  · rintro rfl; exact T.anc_self _

lemma anc_of_up {b x : F} (h : T.Anc b (T.up x)) : T.Anc b x := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply, hn]⟩

lemma anc_up_iff {b x : F} (hx : x ≠ b) : T.Anc b x ↔ T.Anc b (T.up x) := by
  refine ⟨fun ⟨n, hn⟩ => ?_, T.anc_of_up⟩
  rcases n with _ | n
  · exact absurd hn hx
  · exact ⟨n, by rw [← Function.iterate_succ_apply]; exact hn⟩

/-- The first time the path from `x` meets an ancestor `b`; the faces before it are not the
root. -/
lemma exists_first {b x : F} (h : T.Anc b x) :
    ∃ n, T.up^[n] x = b ∧ ∀ i < n, T.up^[i] x ≠ b ∧ T.up^[i] x ≠ T.root := by
  classical
  refine ⟨Nat.find h, Nat.find_spec h, fun i hi => ⟨Nat.find_min h hi, fun hr => ?_⟩⟩
  have h1 : T.up^[Nat.find h] x = T.root := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hi
    rw [hk, show i + k + 1 = (k + 1) + i by ring, Function.iterate_add_apply, hr, iterate_root]
  exact Nat.find_min h hi (hr.trans (h1.symm.trans (Nat.find_spec h)))

/-! ### Sums along the paths from the root -/

/-- The sum of `φ` over the parent darts on the path from the root to `x`. -/
def psum (φ : D → ℤ) (x : F) : ℤ := ∑ i ∈ range (T.depth x), φ (T.par (T.up^[i] x))

lemma psum_root (φ : D → ℤ) : T.psum φ T.root = 0 := by simp [psum, depth_root]

lemma psum_of_ne (φ : D → ℤ) {x : F} (h : x ≠ T.root) :
    T.psum φ x = T.psum φ (T.up x) + φ (T.par x) := by
  rw [psum, T.depth_up h, sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rfl

/-- **The path sums are the unique function vanishing at the root and adding `φ (par x)` at
every step.** -/
theorem psum_unique (φ : D → ℤ) {k : F → ℤ} (h0 : k T.root = 0)
    (h1 : ∀ x, x ≠ T.root → k x = k (T.up x) + φ (T.par x)) (x : F) : k x = T.psum φ x := by
  induction hn : T.depth x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hx : x = T.root
    · subst hx; rw [h0, psum_root]
    · rw [h1 x hx, T.psum_of_ne φ hx, ih (T.depth (T.up x)) (by rw [← hn, T.depth_up hx]; omega)
        (T.up x) rfl]

lemma psum_eq_zero {φ : D → ℤ} (h : ∀ x, x ≠ T.root → φ (T.par x) = 0) (x : F) :
    T.psum φ x = 0 :=
  (T.psum_unique φ (k := fun _ => 0) rfl (fun x hx => by simp [h x hx]) x).symm

lemma psum_add (φ φ' : D → ℤ) (x : F) : T.psum (φ + φ') x = T.psum φ x + T.psum φ' x := by
  simp [psum, sum_add_distrib]

lemma psum_sub (φ φ' : D → ℤ) (x : F) : T.psum (φ - φ') x = T.psum φ x - T.psum φ' x := by
  simp [psum, sum_sub_distrib]

/-- **Path sums of a coboundary telescope.** -/
lemma psum_cob (ψ : F → ℤ) (x : F) : T.psum (M.cob ψ) x = ψ x - ψ T.root :=
  (T.psum_unique (M.cob ψ) (k := fun x => ψ x - ψ T.root) (by simp) (fun x hx => by
    simp only [cob, T.head_par x hx, T.up_of_ne hx]; ring) x).symm

lemma abs_psum_le {φ : D → ℤ} (h : ∀ d, |φ d| ≤ 1) (x : F) : |T.psum φ x| ≤ T.depth x := by
  unfold psum
  calc |∑ i ∈ range (T.depth x), φ (T.par (T.up^[i] x))|
      ≤ ∑ i ∈ range (T.depth x), |φ (T.par (T.up^[i] x))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range (T.depth x), (1 : ℤ) := sum_le_sum fun i _ => h _
    _ = T.depth x := by simp

/-- The path sum from an ancestor `b` down to `x`, through the first `n` steps from `x`. -/
lemma psum_anc (φ : D → ℤ) {b x : F} {n : ℕ} (hn : T.up^[n] x = b)
    (hne : ∀ i < n, T.up^[i] x ≠ T.root) :
    T.psum φ x = T.psum φ b + ∑ i ∈ range n, φ (T.par (T.up^[i] x)) := by
  induction n generalizing x with
  | zero => simp only [Function.iterate_zero_apply] at hn; simp [hn]
  | succ n ih =>
    have hx : x ≠ T.root := hne 0 (by omega)
    rw [Function.iterate_succ_apply] at hn
    rw [T.psum_of_ne φ hx, ih hn (fun i hi => by
      rw [← Function.iterate_succ_apply]; exact hne (i + 1) (by omega)), sum_range_succ']
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    ring

/-! ### Pivots -/

/-- After giving `b` the parent `a`, one step towards the root. -/
lemma up_update {b a : F} (e : D) (hb : b ≠ T.root) (ha : M.face e = a) (x : F) :
    upF M T.root (Function.update T.par b e) x = if x = b then a else T.up x := by
  unfold upF
  by_cases hx : x = b
  · subst hx; simp [hb, ha]
  · by_cases hr : x = T.root
    · subst hr; simp [hx, up_root]
    · simp [hx, hr, T.up_of_ne hr]

lemma iterate_update_eq {b a : F} (e : D) (hb : b ≠ T.root) (ha : M.face e = a) {x : F} {n : ℕ}
    (h : ∀ i < n, T.up^[i] x ≠ b) :
    (upF M T.root (Function.update T.par b e))^[n] x = T.up^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have h0 : x ≠ b := h 0 (by omega)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, T.up_update e hb ha]
    simp only [h0, ↓reduceIte]
    exact ih fun i hi => by rw [← Function.iterate_succ_apply]; exact h (i + 1) (by omega)

/-- **The pivot**: `b ≠ root` gets the parent dart `e`, which enters `b` from a face not below
`b`. -/
def reparent (b : F) (e : D) (hb : b ≠ T.root) (he : M.face (M.rev e) = b)
    (hna : ¬ T.Anc b (M.face e)) : DTree M where
  root := T.root
  par := Function.update T.par b e
  head_par x hx := by
    by_cases h : x = b
    · subst h; simpa using he
    · rw [Function.update_of_ne h]; exact T.head_par x hx
  reach x := by
    have hA : ∀ i, T.up^[i] (M.face e) ≠ b := fun i h => hna ⟨i, h⟩
    have hra := T.iterate_update_eq e hb rfl (n := T.depth (M.face e)) fun i _ => hA i
    rw [iterate_depth] at hra
    by_cases hx : T.Anc b x
    · obtain ⟨n, hn, hne⟩ := T.exists_first hx
      refine ⟨T.depth (M.face e) + 1 + n, ?_⟩
      rw [Function.iterate_add_apply, T.iterate_update_eq e hb rfl (fun i hi => (hne i hi).1), hn,
        Function.iterate_succ_apply, T.up_update e hb rfl]
      simpa using hra
    · exact ⟨T.depth x, by
        rw [T.iterate_update_eq e hb rfl (fun i _ h => hx ⟨i, h⟩), iterate_depth]⟩

section Reparent

variable {b : F} {e : D} {hb : b ≠ T.root} {he : M.face (M.rev e) = b}
  {hna : ¬ T.Anc b (M.face e)}

lemma reparent_root : (T.reparent b e hb he hna).root = T.root := rfl

lemma reparent_par (x : F) :
    (T.reparent b e hb he hna).par x = if x = b then e else T.par x := by
  by_cases h : x = b
  · subst h; simp [reparent]
  · simp [reparent, h]

lemma reparent_up (x : F) :
    (T.reparent b e hb he hna).up x = if x = b then M.face e else T.up x :=
  T.up_update e hb rfl x

open Classical in
/-- **The path sums after a pivot** change by `psum (face e) + φ e - psum b` on the subtree of
`b`. -/
theorem psum_reparent (φ : D → ℤ) (x : F) :
    (T.reparent b e hb he hna).psum φ x = T.psum φ x +
      if T.Anc b x then T.psum φ (M.face e) + φ e - T.psum φ b else 0 := by
  refine ((T.reparent b e hb he hna).psum_unique φ (k := fun x => T.psum φ x +
      if T.Anc b x then T.psum φ (M.face e) + φ e - T.psum φ b else 0) ?_ ?_ x).symm
  · have h1 : ¬ T.Anc b T.root := by rw [anc_root_iff]; exact hb
    show T.psum φ T.root + (if T.Anc b T.root then _ else 0) = 0
    simp [psum_root, h1]
  · intro y hy
    rw [reparent_root] at hy
    simp only [reparent_up, reparent_par]
    by_cases hyb : y = b
    · subst hyb
      simp only [↓reduceIte, hna, T.anc_self]
      ring
    · simp only [hyb, ↓reduceIte]
      rw [T.psum_of_ne φ hy, T.anc_up_iff hyb]
      ring

lemma reparent_inT_par {x : F} (_hx : x ≠ T.root) :
    (T.reparent b e hb he hna).par x = e ∨ (x ≠ b ∧ (T.reparent b e hb he hna).par x = T.par x) := by
  rw [reparent_par]
  by_cases h : x = b
  · left; simp [h]
  · right; simp [h]

end Reparent

/-! ### Circulations on a tree -/

/-- The darts of the edges of the tree. -/
def InT (d : D) : Prop := ∃ x, x ≠ T.root ∧ (d = T.par x ∨ d = M.rev (T.par x))

lemma inT_par {x : F} (hx : x ≠ T.root) : T.InT (T.par x) := ⟨x, hx, Or.inl rfl⟩

lemma inT_rev {d : D} (h : T.InT d) : T.InT (M.rev d) := by
  obtain ⟨x, hx, rfl | rfl⟩ := h
  · exact ⟨x, hx, Or.inr rfl⟩
  · exact ⟨x, hx, Or.inl (M.rev_rev (T.par x))⟩

lemma inT_rev_iff {d : D} : T.InT (M.rev d) ↔ T.InT d :=
  ⟨fun h => by simpa [M.rev_rev] using T.inT_rev h, T.inT_rev⟩

/-- **A tree supports no nonzero circulation**: an antisymmetric function vanishing off the edges
of the tree, with zero net flow out of every face, vanishes. -/
theorem eq_zero_of_dualCirc {κ : D → ℤ} (hκ : M.IsAntisymm κ) (hsupp : ∀ d, κ d ≠ 0 → T.InT d)
    (hdiv : ∀ x, ∑ d with M.face d = x, κ d = 0) (d : D) : κ d = 0 := by
  have key : ∀ m x, x ≠ T.root → Fintype.card F - T.depth x = m → κ (T.par x) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro x hx hm
      have hsum : ∑ d with M.face d = x, κ d = κ (M.rev (T.par x)) := by
        refine sum_eq_single (M.rev (T.par x)) (fun d hd hne => ?_) (fun h => ?_)
        · by_contra h0
          obtain ⟨y, hy, rfl | rfl⟩ := hsupp d h0
          · simp only [mem_filter, mem_univ, true_and] at hd
            have hup : T.up y = x := by rw [T.up_of_ne hy, hd]
            have hdep := T.depth_up hy
            rw [hup] at hdep
            have := T.depth_lt_card y
            exact h0 (ih _ (by omega) y hy rfl)
          · simp only [mem_filter, mem_univ, true_and, T.head_par y hy] at hd
            subst hd; exact hne rfl
        · exact absurd (by simp [T.head_par x hx]) h
      have := hdiv x
      rw [hsum, hκ] at this
      omega
  by_contra h0
  obtain ⟨x, hx, rfl | rfl⟩ := hsupp d h0
  · exact h0 (key _ x hx rfl)
  · rw [hκ, key _ x hx rfl, neg_zero] at h0; exact h0 rfl

/-- A face potential whose coboundary vanishes on the parent darts is constant. -/
lemma pot_const {ψ : F → ℤ} (h : ∀ x, x ≠ T.root → M.cob ψ (T.par x) = 0) (x : F) :
    ψ x = ψ T.root := by
  have := T.psum_cob ψ x
  rw [T.psum_eq_zero h] at this
  omega

end DTree

end STFlow

end PlanarFlow
