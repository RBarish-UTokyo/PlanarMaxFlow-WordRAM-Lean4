module

public import PlanarFlow.MSSP.Defs

/-!
# Walks, distances and tight arcs

Basic facts on shortest paths in a digraph with integer lengths (`PlanarFlow.Digraph`), used by
the multiple-source shortest path algorithm of Das, Kipouridis, Probst Gutenberg and Wulff-Nilsen
(SOSA 2022).

* `LWalk G x y l`: the list of arcs `l` is a walk from `x` to `y`; `wlen G l` is its length.
  For a nonempty arc type these are the indexed walks `PlanarFlow.MSSP.IsWalk` of the
  specification (`exists_isWalk_iff`).
* `Reach G x y` and `dist G x y`: reachability and, for nonnegative lengths, the least length of
  a walk (`exists_walk_dist`, `dist_le`). `isDist`: these are the distances of the specification
  `PlanarFlow.MSSP.IsDist`.
* `Tight G r a`: the arc `a` is on a shortest walk from `r` (`dist r (src a) + len a = dist r (dst
  a)`), and `UniqTight G`: every vertex other than the source has at most one tight incoming arc
  (the article's assumption of unique shortest paths, in local form).
* `TReach G r y w`: `w` is reached from `y` along tight arcs from `r`; then `y` lies on a shortest
  walk from `r` to `w` (`TReach.dist_eq`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace MSSP

open Finset

variable {X A : Type*} (G : Digraph X A)

/-! ### Walks as lists of arcs -/

/-- `LWalk G x y l`: the arcs `l` form a walk from `x` to `y`. -/
inductive LWalk : X → X → List A → Prop
  | nil (x : X) : LWalk x x []
  | cons {a : A} {y : X} {l : List A} : LWalk (G.dst a) y l → LWalk (G.src a) y (a :: l)

/-- The length of a list of arcs. -/
def wlen (l : List A) : ℤ := (l.map G.len).sum

variable {G}

@[simp] lemma wlen_nil : wlen G [] = 0 := rfl

@[simp] lemma wlen_cons (a : A) (l : List A) : wlen G (a :: l) = G.len a + wlen G l := by
  simp [wlen]

@[simp] lemma wlen_append (l l' : List A) : wlen G (l ++ l') = wlen G l + wlen G l' := by
  simp [wlen]

lemma wlen_nonneg (hnn : ∀ a, 0 ≤ G.len a) (l : List A) : 0 ≤ wlen G l := by
  induction l with
  | nil => simp
  | cons a l ih => rw [wlen_cons]; have := hnn a; omega

lemma LWalk.nil_iff {x y : X} : LWalk G x y [] ↔ x = y := by
  constructor
  · rintro ⟨⟩; rfl
  · rintro rfl; exact .nil x

lemma LWalk.cons_iff {x y : X} {a : A} {l : List A} :
    LWalk G x y (a :: l) ↔ G.src a = x ∧ LWalk G (G.dst a) y l := by
  constructor
  · rintro ⟨⟩; exact ⟨rfl, ‹_›⟩
  · rintro ⟨rfl, h⟩; exact .cons h

lemma LWalk.append {x y z : X} {l l' : List A} (h : LWalk G x y l) (h' : LWalk G y z l') :
    LWalk G x z (l ++ l') := by
  induction h with
  | nil => exact h'
  | cons _ ih => exact .cons (ih h')

lemma LWalk.split {x z : X} {l l' : List A} (h : LWalk G x z (l ++ l')) :
    ∃ y, LWalk G x y l ∧ LWalk G y z l' := by
  induction l generalizing x with
  | nil => exact ⟨x, .nil x, h⟩
  | cons a l ih =>
    rw [List.cons_append] at h
    obtain ⟨hx, h'⟩ := LWalk.cons_iff.1 h
    subst hx
    obtain ⟨y, h1, h2⟩ := ih h'
    exact ⟨y, .cons h1, h2⟩

lemma LWalk.concat {x y : X} {l : List A} {a : A} (h : LWalk G x y l) (ha : G.src a = y) :
    LWalk G x (G.dst a) (l ++ [a]) := h.append (ha ▸ .cons (.nil _))

lemma LWalk.concat_iff {x z : X} {l : List A} {a : A} :
    LWalk G x z (l ++ [a]) ↔ LWalk G x (G.src a) l ∧ G.dst a = z := by
  constructor
  · intro h
    obtain ⟨y, h1, h2⟩ := h.split
    obtain ⟨hy, h3⟩ := LWalk.cons_iff.1 h2
    subst hy
    exact ⟨h1, LWalk.nil_iff.1 h3⟩
  · rintro ⟨h, rfl⟩; exact h.concat rfl

/-- The first arc of a nonempty walk starts at its start. -/
lemma LWalk.src_head {x y : X} {a : A} {l : List A} (h : LWalk G x y (a :: l)) : G.src a = x :=
  (LWalk.cons_iff.1 h).1

/-- Every arc of a walk is followed, in the walk, by the remaining walk. -/
lemma LWalk.mem_split {x y : X} {l : List A} {a : A} (h : LWalk G x y l) (ha : a ∈ l) :
    ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ LWalk G x (G.src a) l₁ ∧ LWalk G (G.dst a) y l₂ := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
  obtain ⟨z, h1, h2⟩ := h.split
  obtain ⟨hz, h3⟩ := LWalk.cons_iff.1 h2
  subst hz
  exact ⟨l₁, l₂, rfl, h1, h3⟩

/-! ### Reachability and distances -/

/-- `y` is reachable from `x`. -/
def Reach (G : Digraph X A) (x y : X) : Prop := ∃ l, LWalk G x y l

lemma Reach.refl (x : X) : Reach G x x := ⟨[], .nil x⟩

lemma Reach.trans {x y z : X} (h : Reach G x y) (h' : Reach G y z) : Reach G x z :=
  let ⟨l, hl⟩ := h; let ⟨l', hl'⟩ := h'; ⟨l ++ l', hl.append hl'⟩

lemma Reach.arc {x : X} {a : A} (h : Reach G x (G.src a)) : Reach G x (G.dst a) :=
  h.trans ⟨[a], .cons (.nil _)⟩

open Classical in
/-- The least length of a walk from `x` to `y` (meaningful for nonnegative lengths and
`Reach G x y`; `0` otherwise). -/
noncomputable def dist (G : Digraph X A) (x y : X) : ℤ :=
  if h : ∃ n : ℕ, ∃ l, LWalk G x y l ∧ wlen G l ≤ n then (Nat.find h : ℤ) else 0

section Dist

variable (hnn : ∀ a, 0 ≤ G.len a)
include hnn

lemma dist_spec {x y : X} (h : Reach G x y) :
    (∃ l, LWalk G x y l ∧ wlen G l = dist G x y) ∧ ∀ l, LWalk G x y l → dist G x y ≤ wlen G l := by
  classical
  obtain ⟨l₀, hl₀⟩ := h
  have hex : ∃ n : ℕ, ∃ l, LWalk G x y l ∧ wlen G l ≤ n :=
    ⟨(wlen G l₀).toNat, l₀, hl₀, Int.self_le_toNat _⟩
  have hd : dist G x y = (Nat.find hex : ℤ) := by simp only [dist, hex, dite_true]
  obtain ⟨l, hl, hle⟩ := Nat.find_spec hex
  have hmin : ∀ l', LWalk G x y l' → (Nat.find hex : ℤ) ≤ wlen G l' := by
    intro l' hl'
    have h0 := wlen_nonneg hnn l'
    have := Nat.find_min' hex (m := (wlen G l').toNat) ⟨l', hl', Int.self_le_toNat _⟩
    have : ((wlen G l').toNat : ℤ) = wlen G l' := Int.toNat_of_nonneg h0
    omega
  refine ⟨⟨l, hl, ?_⟩, fun l' hl' => hd ▸ hmin l' hl'⟩
  have := hmin l hl
  omega

lemma exists_walk_dist {x y : X} (h : Reach G x y) : ∃ l, LWalk G x y l ∧ wlen G l = dist G x y :=
  (dist_spec hnn h).1

lemma dist_le {x y : X} {l : List A} (hl : LWalk G x y l) : dist G x y ≤ wlen G l :=
  (dist_spec hnn ⟨l, hl⟩).2 l hl

lemma dist_nonneg {x y : X} (h : Reach G x y) : 0 ≤ dist G x y := by
  obtain ⟨l, hl, he⟩ := exists_walk_dist hnn h
  rw [← he]; exact wlen_nonneg hnn l

lemma dist_self (x : X) : dist G x x = 0 := by
  have := dist_le hnn (LWalk.nil (G := G) x)
  have := dist_nonneg hnn (Reach.refl (G := G) x)
  simp at *; omega

lemma dist_triangle {x y z : X} (h : Reach G x y) (h' : Reach G y z) :
    dist G x z ≤ dist G x y + dist G y z := by
  obtain ⟨l, hl, he⟩ := exists_walk_dist hnn h
  obtain ⟨l', hl', he'⟩ := exists_walk_dist hnn h'
  have := dist_le hnn (hl.append hl')
  rw [wlen_append] at this; omega

lemma dist_arc {x : X} {a : A} (h : Reach G x (G.src a)) :
    dist G x (G.dst a) ≤ dist G x (G.src a) + G.len a := by
  have := dist_triangle hnn h (Reach.refl _ |>.arc (a := a))
  have h2 := dist_le hnn (G := G) (LWalk.cons (a := a) (.nil (G.dst a)))
  simp at h2; omega

/-- A walk of least length splits into walks of least length. -/
lemma dist_split {x z : X} {l l' : List A} (h : LWalk G x z (l ++ l'))
    (hmin : wlen G (l ++ l') = dist G x z) :
    ∃ y, LWalk G x y l ∧ LWalk G y z l' ∧ wlen G l = dist G x y ∧ wlen G l' = dist G y z ∧
      dist G x z = dist G x y + dist G y z := by
  obtain ⟨y, h1, h2⟩ := h.split
  have e1 := dist_le hnn h1
  have e2 := dist_le hnn h2
  have e3 := dist_triangle hnn ⟨l, h1⟩ ⟨l', h2⟩
  rw [wlen_append] at hmin
  exact ⟨y, h1, h2, by omega, by omega, by omega⟩

end Dist

/-! ### The specification of distances -/

open Classical in
/-- The distances from `r` as in the specification: `none` for the unreachable vertices. -/
noncomputable def odist (G : Digraph X A) (r y : X) : Option ℤ :=
  if Reach G r y then some (dist G r y) else none

/-- The arcs of a walk in the indexed form of the specification. -/
lemma isWalk_of_lwalk {x y : X} {l : List A} (h : LWalk G x y l) (a₀ : A) :
    IsWalk G x y l.length (fun t => l.getD t a₀) ∧
      G.walkLen l.length (fun t => l.getD t a₀) = wlen G l := by
  induction h with
  | nil x => exact ⟨Or.inl ⟨rfl, rfl⟩, by simp [Digraph.walkLen]⟩
  | @cons a y l h ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨Or.inr ⟨by simp, by simp, ?_, ?_⟩, ?_⟩
    · rcases ih1 with ⟨h0, rfl⟩ | ⟨h0, -, h1, -⟩
      · rw [List.length_eq_zero_iff.1 h0]; simp
      · simp only [List.length_cons, Nat.add_sub_cancel]
        obtain ⟨k, hk⟩ : ∃ k, l.length = k + 1 := ⟨l.length - 1, by omega⟩
        rw [hk] at h1 ⊢
        simpa using h1
    · intro t ht
      rcases t with _ | t
      · simp only [List.getD_cons_zero, List.getD_cons_succ, zero_add]
        rcases ih1 with ⟨h0, -⟩ | ⟨-, h1, -, -⟩
        · simp at ht; omega
        · exact h1.symm
      · simp only [List.getD_cons_succ]
        rcases ih1 with ⟨h0, -⟩ | ⟨-, -, -, h2⟩
        · simp at ht; omega
        · exact h2 t (by simp at ht; omega)
    · simp only [Digraph.walkLen, List.length_cons, wlen_cons] at ih2 ⊢
      rw [Finset.sum_range_succ', ← ih2]
      simp [add_comm]

/-- The indexed walks of the specification are walks. -/
lemma lwalk_of_isWalk {x y : X} {m : ℕ} {c : ℕ → A} (h : IsWalk G x y m c) :
    LWalk G x y ((List.range m).map c) ∧ wlen G ((List.range m).map c) = G.walkLen m c := by
  refine ⟨?_, ?_⟩
  swap
  · simp only [wlen, Digraph.walkLen, List.map_map]
    clear h
    induction m with
    | zero => simp
    | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  rcases h with ⟨rfl, rfl⟩ | ⟨hm, h0, h1, h2⟩
  · exact .nil x
  · -- induction on the walk from the back
    have key : ∀ k, k ≤ m → 0 < k → LWalk G x (G.dst (c (k - 1))) ((List.range k).map c) := by
      intro k hk hk0
      induction k with
      | zero => omega
      | succ k ih =>
        rw [List.range_succ, List.map_append, List.map_singleton]
        rcases Nat.eq_zero_or_pos k with rfl | hk1
        · simp only [List.range_zero, List.map_nil, List.nil_append, zero_add, Nat.sub_self]
          rw [← h0]; exact .cons (.nil _)
        · have := ih (by omega) hk1
          rw [show k + 1 - 1 = k by omega]
          exact this.concat (h2 (k - 1) (by omega) ▸ by rw [show k - 1 + 1 = k by omega])
    have := key m le_rfl hm
    rwa [h1] at this

/-- Walks in the indexed form are walks as lists (for a nonempty type of arcs). -/
lemma exists_isWalk_iff [Nonempty A] {x y : X} {L : ℤ} :
    (∃ m c, IsWalk G x y m c ∧ G.walkLen m c = L) ↔ ∃ l, LWalk G x y l ∧ wlen G l = L := by
  constructor
  · rintro ⟨m, c, h, rfl⟩
    exact ⟨_, (lwalk_of_isWalk h).1, (lwalk_of_isWalk h).2⟩
  · rintro ⟨l, h, rfl⟩
    obtain ⟨a₀⟩ := ‹Nonempty A›
    exact ⟨_, _, (isWalk_of_lwalk h a₀).1, (isWalk_of_lwalk h a₀).2⟩

/-- **The distances meet the specification** (nonnegative lengths, nonempty type of arcs). -/
theorem isDist [Nonempty A] (hnn : ∀ a, 0 ≤ G.len a) (r : X) : IsDist G r (odist G r) where
  some_walk y ℓ h := by
    unfold odist at h
    split_ifs at h with hr
    cases h
    obtain ⟨l, hl, he⟩ := exists_walk_dist hnn hr
    exact exists_isWalk_iff.2 ⟨l, hl, he⟩
  some_le y ℓ h m c hw := by
    unfold odist at h
    split_ifs at h with hr
    cases h
    have := lwalk_of_isWalk hw
    rw [← this.2]; exact dist_le hnn this.1
  none y h m c hw := by
    unfold odist at h
    split_ifs at h with hr
    exact hr ⟨_, (lwalk_of_isWalk hw).1⟩

/-- With no arcs at all, nothing is reachable in the indexed sense. -/
theorem isDist_of_isEmpty [IsEmpty A] (r : X) : IsDist G r (fun _ => none) where
  some_walk _ _ h := by cases h
  some_le _ _ h := by cases h
  none _ _ _ c _ := isEmptyElim (c 0)

/-! ### Tight arcs -/

/-- The arc `a` is *tight* for the source `r`: it lies on a shortest walk from `r`. -/
def Tight (G : Digraph X A) (r : X) (a : A) : Prop :=
  Reach G r (G.src a) ∧ dist G r (G.src a) + G.len a = dist G r (G.dst a)

/-- **Unique tight arcs** (the article's unique shortest paths, in local form): for every source,
every other vertex has at most one tight incoming arc. -/
def UniqTight (G : Digraph X A) : Prop :=
  ∀ r a b, Tight G r a → Tight G r b → G.dst a = G.dst b → G.dst a ≠ r → a = b

section TightArcs

variable (hnn : ∀ a, 0 ≤ G.len a)
include hnn

/-- The last arc of a shortest walk is tight. -/
lemma tight_of_last {r z : X} {l : List A} {a : A} (h : LWalk G r z (l ++ [a]))
    (hmin : wlen G (l ++ [a]) = dist G r z) : Tight G r a := by
  obtain ⟨y, h1, h2, e1, e2, e3⟩ := dist_split hnn h hmin
  obtain ⟨rfl, h2'⟩ := LWalk.cons_iff.1 h2
  obtain rfl := LWalk.nil_iff.1 h2'
  refine ⟨⟨l, h1⟩, ?_⟩
  have := dist_le hnn h2
  simp at e2 this
  omega

/-- Every vertex other than the source reached from it has a tight incoming arc. -/
lemma exists_tight {r y : X} (h : Reach G r y) (hy : y ≠ r) : ∃ a, Tight G r a ∧ G.dst a = y := by
  obtain ⟨l, hl, he⟩ := exists_walk_dist hnn h
  rcases List.eq_nil_or_concat l with rfl | ⟨l', a, rfl⟩
  · exact absurd (LWalk.nil_iff.1 hl).symm hy
  · rw [List.concat_eq_append] at hl he
    exact ⟨a, tight_of_last hnn hl he, (LWalk.concat_iff.1 hl).2⟩

end TightArcs

/-- `TReach G r y w`: `w` is reached from `y` along arcs that are tight for `r`. -/
inductive TReach (G : Digraph X A) (r : X) : X → X → Prop
  | refl (y : X) : TReach G r y y
  | tail {y : X} {a : A} : TReach G r y (G.src a) → Tight G r a → TReach G r y (G.dst a)

lemma TReach.trans {r x y z : X} (h : TReach G r x y) (h' : TReach G r y z) : TReach G r x z := by
  induction h' with
  | refl => exact h
  | tail _ ha ih => exact .tail ih ha

section TReachDist

variable (hnn : ∀ a, 0 ≤ G.len a)
include hnn

/-- Along tight arcs, a walk of length the difference of the distances from the source. -/
lemma TReach.walk {r y w : X} (h : TReach G r y w) (hy : Reach G r y) :
    Reach G r w ∧ ∃ l, LWalk G y w l ∧ wlen G l = dist G r w - dist G r y := by
  induction h with
  | refl => exact ⟨hy, [], .nil _, by simp⟩
  | @tail a _ ha ih =>
    obtain ⟨-, l, hl, he⟩ := ih
    refine ⟨ha.1.arc, l ++ [a], hl.concat rfl, ?_⟩
    rw [wlen_append]; simp; have := ha.2; omega

/-- **On a tight chain from `y` to `w`, `y` lies on a shortest walk from `r` to `w`.** -/
lemma TReach.dist_eq {r y w : X} (h : TReach G r y w) (hy : Reach G r y) :
    Reach G y w ∧ dist G y w = dist G r w - dist G r y := by
  obtain ⟨hw, l, hl, he⟩ := h.walk hnn hy
  have h1 := dist_le hnn hl
  have h2 := dist_triangle hnn hy ⟨l, hl⟩
  exact ⟨⟨l, hl⟩, by omega⟩

end TReachDist

/-! ### Shortest walks -/

/-- `L` is a walk of least length from `r` to `y`. -/
def IsSP (G : Digraph X A) (r y : X) (L : List A) : Prop :=
  LWalk G r y L ∧ wlen G L = dist G r y

section SP

variable (hnn : ∀ a, 0 ≤ G.len a)
include hnn

lemma exists_isSP {r y : X} (h : Reach G r y) : ∃ L, IsSP G r y L := exists_walk_dist hnn h

/-- **A shortest walk splits into a shortest walk and tight arcs.** -/
lemma IsSP.split {r y : X} {L₁ L₂ : List A} (h : IsSP G r y (L₁ ++ L₂)) :
    ∃ z, IsSP G r z L₁ ∧ LWalk G z y L₂ ∧ TReach G r z y := by
  induction L₂ generalizing L₁ with
  | nil =>
    obtain ⟨z, h1, h2⟩ := h.1.split
    obtain rfl := LWalk.nil_iff.1 h2
    simp only [List.append_nil] at h
    exact ⟨z, h, .nil _, .refl _⟩
  | cons b L₂ ih =>
    rw [show L₁ ++ b :: L₂ = (L₁ ++ [b]) ++ L₂ by simp] at h
    obtain ⟨z', hz', hw', ht'⟩ := ih h
    obtain ⟨hw1, hz⟩ := LWalk.concat_iff.1 hz'.1
    subst hz
    have hb : Tight G r b := tight_of_last hnn hz'.1 hz'.2
    obtain ⟨z, h1, h2, e1, -, -⟩ := dist_split hnn hz'.1 hz'.2
    obtain ⟨hzb, -⟩ := LWalk.cons_iff.1 h2
    subst hzb
    exact ⟨_, ⟨h1, e1⟩, .cons hw', TReach.trans (.tail (.refl _) hb) ht'⟩

/-- The arcs of a shortest walk are tight; the start of each is reached and lies on a tight chain
to the end. -/
lemma IsSP.mem_src {r y : X} {L : List A} (h : IsSP G r y L) {a : A} (ha : a ∈ L) :
    Reach G r (G.src a) ∧ TReach G r (G.src a) y ∧ dist G r (G.src a) + G.len a ≤ dist G r y ∧
      Tight G r a := by
  obtain ⟨L₁, L₂, rfl, -, -⟩ := h.1.mem_split ha
  obtain ⟨z, hz, hw, ht⟩ := h.split hnn
  obtain ⟨hza, -⟩ := LWalk.cons_iff.1 hw
  subst hza
  have h' : IsSP G r y ((L₁ ++ [a]) ++ L₂) := by simpa using h
  obtain ⟨z', hz', hw', -⟩ := h'.split hnn
  have ht' := tight_of_last hnn hz'.1 hz'.2
  obtain ⟨-, rfl⟩ := LWalk.concat_iff.1 hz'.1
  have e1 := dist_le hnn hw'
  have e2 := dist_triangle hnn ⟨_, hz'.1⟩ ⟨_, hw'⟩
  have e3 := h.2
  refine ⟨⟨_, hz.1⟩, ht, ?_, ht'⟩
  have := hz'.2
  simp only [wlen_append, wlen_cons, wlen_nil] at this e3
  have := wlen_nonneg hnn L₂
  rw [← hz.2]; omega

lemma IsSP.mem_dst {r y : X} {L : List A} (h : IsSP G r y L) {a : A} (ha : a ∈ L) :
    Reach G r (G.dst a) ∧ TReach G r (G.dst a) y ∧ dist G r (G.dst a) ≤ dist G r y := by
  obtain ⟨L₁, L₂, rfl, -, -⟩ := h.1.mem_split ha
  have h' : IsSP G r y ((L₁ ++ [a]) ++ L₂) := by simpa using h
  obtain ⟨z', hz', hw', ht'⟩ := h'.split hnn
  obtain ⟨-, rfl⟩ := LWalk.concat_iff.1 hz'.1
  have e3 := h.2
  have := hz'.2
  simp only [wlen_append, wlen_cons, wlen_nil] at this e3
  have := wlen_nonneg hnn L₂
  exact ⟨⟨_, hz'.1⟩, ht', by omega⟩

/-- The last arc of a shortest walk. -/
lemma IsSP.concat {r y : X} {L : List A} {a : A} (h : IsSP G r y (L ++ [a])) :
    IsSP G r (G.src a) L ∧ G.dst a = y ∧ Tight G r a := by
  obtain ⟨z, hz, hw, -⟩ := h.split hnn
  obtain ⟨rfl, hw'⟩ := LWalk.cons_iff.1 hw
  exact ⟨hz, LWalk.nil_iff.1 hw', tight_of_last hnn h.1 h.2⟩

end SP

section Pos

variable (hpos : ∀ a, 0 < G.len a)
include hpos

lemma nonneg_of_pos : ∀ a, 0 ≤ G.len a := fun a => (hpos a).le

/-- **With positive lengths, a shortest walk visits distinct vertices** (its tails). -/
lemma IsSP.nodup_src {r y : X} {L : List A} (h : IsSP G r y L) : (L.map G.src).Nodup := by
  induction L using List.reverseRecOn generalizing y with
  | nil => simp
  | append_singleton L a ih =>
    obtain ⟨h1, -, -⟩ := h.concat (nonneg_of_pos hpos)
    rw [List.map_append, List.nodup_append]
    refine ⟨ih h1, by simp, ?_⟩
    simp only [List.mem_map, List.mem_singleton, ne_eq, forall_exists_index, and_imp]
    rintro _ b hb rfl _ c hc rfl
    rw [hc]
    obtain ⟨-, -, e, -⟩ := h1.mem_src (nonneg_of_pos hpos) hb
    have := hpos b
    intro hh; rw [hh] at e; omega

/-- With positive lengths, a shortest walk visits distinct vertices (its heads). -/
lemma IsSP.nodup_dst {r y : X} {L : List A} (h : IsSP G r y L) : (L.map G.dst).Nodup := by
  induction L using List.reverseRecOn generalizing y with
  | nil => simp
  | append_singleton L a ih =>
    obtain ⟨h1, -, ha⟩ := h.concat (nonneg_of_pos hpos)
    rw [List.map_append, List.nodup_append]
    refine ⟨ih h1, by simp, ?_⟩
    simp only [List.mem_map, List.mem_singleton, ne_eq, forall_exists_index, and_imp]
    rintro _ b hb rfl _ c hc rfl
    rw [hc]
    obtain ⟨-, -, e⟩ := h1.mem_dst (nonneg_of_pos hpos) hb
    have := hpos a
    have := ha.2
    intro hh; rw [hh] at e; omega

/-- With positive lengths, a tight chain from `y` to `w` gives `dist r y ≤ dist r w`, with
equality only for `y = w`. -/
lemma TReach.dist_lt {r y w : X} (h : TReach G r y w) (hne : y ≠ w) :
    dist G r y < dist G r w := by
  induction h with
  | refl => exact absurd rfl hne
  | @tail a h' ha ih =>
    have := hpos a
    have := ha.2
    by_cases hy : y = G.src a
    · subst hy; omega
    · have := ih hy; omega

lemma TReach.dist_le {r y w : X} (h : TReach G r y w) : dist G r y ≤ dist G r w := by
  by_cases hyw : y = w
  · rw [hyw]
  · exact (h.dist_lt hpos hyw).le

end Pos

end MSSP

end PlanarFlow
