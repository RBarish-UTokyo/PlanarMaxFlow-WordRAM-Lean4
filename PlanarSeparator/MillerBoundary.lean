module

public import PlanarSeparator.SimpleCycle

/-!
# Boundaries of connected face sets are simple cycles

Let `W` be a set of faces of a plane map such that `W` and its complement are both connected
through edges (two faces are adjacent if they lie on the two sides of an edge). Then the edges
with exactly one side in `W` — the boundary of `W` — are exactly the edges of a simple cycle
(`PlanarSeparator.Map.IsPlane.exists_scycle_bd`). This is the topological fact behind the level
cycles of Miller's simple cycle separator theorem.

## The proof

The boundary of `W` is a closed cochain (the coboundary of the indicator of `W`). Every nonzero
closed cochain contains the edges of a simple cycle (`PlanarSeparator.Map.exists_scycle_of_closed`):
a longest path in its support can be continued at its last vertex, where the support has even
degree, and the continuation must return to the path. The edges of a simple cycle form a closed
cochain, which by the combinatorial Jordan curve theorem
(`PlanarSeparator.Map.IsPlane.exists_face_cochain`) is the coboundary of a function on the faces.
This function is constant on `W` and on its complement, which are connected through edges off the
boundary; hence the cycle is the whole boundary.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset

namespace Map

variable {D P : Type*} {M : Map D P}

/-! ### The cochain of a simple cycle -/

namespace SCycle

variable (C : M.SCycle)

/-- A dart lies on the simple cycle `C` (in either direction). -/
def Mem (d : D) : Prop := ∃ i < C.k, d = C.d i ∨ d = M.α (C.d i)

lemma mem_α_iff {d : D} : C.Mem (M.α d) ↔ C.Mem d := by
  constructor
  · rintro ⟨i, hi, h | h⟩
    · exact ⟨i, hi, Or.inr (by rw [← h, M.α_α])⟩
    · exact ⟨i, hi, Or.inl (M.α_injective h)⟩
  · rintro ⟨i, hi, rfl | rfl⟩
    · exact ⟨i, hi, Or.inr rfl⟩
    · exact ⟨i, hi, Or.inl (M.α_α _)⟩

lemma mem_d {i : ℕ} (hi : i < C.k) : C.Mem (C.d i) := ⟨i, hi, Or.inl rfl⟩

/-- A simple cycle is *proper* if it does not run back and forth along a single edge. -/
def Proper : Prop := C.k = 2 → C.d 0 ≠ M.α (C.d 1)

open Classical in
/-- The cochain of the edges of a simple cycle. -/
noncomputable def cochain (d : D) : ZMod 2 := if C.Mem d then 1 else 0

lemma cochain_α (d : D) : C.cochain (M.α d) = C.cochain d := by
  classical
  by_cases h : C.Mem d
  · simp [cochain, h, (C.mem_α_iff).2 h]
  · simp [cochain, h, mt (C.mem_α_iff).1 h]

lemma cochain_ne_zero_iff {d : D} : C.cochain d ≠ 0 ↔ C.Mem d := by
  classical
  unfold cochain
  split_ifs with h <;> simp [h]

lemma mod_succ {i : ℕ} (hi : i < C.k) : (i + 1) % C.k = if i + 1 < C.k then i + 1 else 0 := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [show i + 1 = C.k by omega, Nat.mod_self]

lemma vert_α_d {i : ℕ} (hi : i < C.k) :
    M.vert (M.α (C.d i)) = M.vert (C.d (if i + 1 < C.k then i + 1 else 0)) := by
  rw [C.vert_α i hi, C.mod_succ hi]

variable [DecidableEq P]

lemma mem_verts_of_mem {d : D} (h : C.Mem d) : M.vert d ∈ C.verts := by
  obtain ⟨i, hi, rfl | rfl⟩ := h
  · exact C.mem_verts.2 ⟨i, hi, rfl⟩
  · rw [C.vert_α_d hi]
    exact C.mem_verts.2 ⟨_, by split_ifs <;> omega, rfl⟩

variable [Fintype D] [DecidableEq D]

/-- **The edges of a proper simple cycle form a closed cochain**: at every vertex of the cycle
exactly two darts of the cycle start, the outgoing dart and the reversal of the incoming one. -/
theorem sum_cochain (hC : C.Proper) (v : P) : ∑ d with M.vert d = v, C.cochain d = 0 := by
  classical
  by_cases hv : v ∈ C.verts
  · obtain ⟨i, hi, rfl⟩ := C.mem_verts.1 hv
    -- the previous index
    set j := if i = 0 then C.k - 1 else i - 1 with hj
    have hj' : (i = 0 ∧ j = C.k - 1) ∨ (i ≠ 0 ∧ j = i - 1) := by
      rw [hj]; split_ifs with h <;> omega
    have hjk : j < C.k := by omega
    have hji : (if j + 1 < C.k then j + 1 else 0) = i := by
      split_ifs <;> omega
    have hne : C.d i ≠ M.α (C.d j) := by
      intro h
      have h1 : M.vert (C.d (if i + 1 < C.k then i + 1 else 0)) = M.vert (C.d j) := by
        rw [← C.vert_α_d hi, h, M.α_α]
      have h2 := C.inj _ (by split_ifs <;> omega) _ hjk h1
      by_cases hk1 : C.k = 1
      · have hi0 : i = 0 := by omega
        have hj0 : j = 0 := by omega
        subst hi0
        rw [hj0] at h
        exact M.α_ne _ h.symm
      by_cases hk2 : C.k = 2
      · apply hC hk2
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
        · have : j = 1 := by omega
          rw [this] at h
          exact h
        · have : j = 0 := by omega
          rw [this] at h
          rw [h, M.α_α]
      · split_ifs at h2 <;> omega
    have hfilter : ({d | M.vert d = M.vert (C.d i) ∧ C.Mem d} : Finset D) =
        {C.d i, M.α (C.d j)} := by
      ext d
      simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · rintro ⟨hd, k', hk', rfl | rfl⟩
        · left
          rw [C.inj _ hk' _ hi hd]
        · right
          rw [C.vert_α_d hk'] at hd
          have := C.inj _ (by split_ifs <;> omega) _ hi hd
          have : k' = j := by
            split_ifs at this <;> omega
          rw [this]
      · rintro (rfl | rfl)
        · exact ⟨rfl, C.mem_d hi⟩
        · refine ⟨?_, (C.mem_α_iff).2 (C.mem_d hjk)⟩
          rw [C.vert_α_d hjk, hji]
    rw [sum_filter]
    have : ∀ d : D, (if M.vert d = M.vert (C.d i) then C.cochain d else 0) =
        if M.vert d = M.vert (C.d i) ∧ C.Mem d then 1 else 0 := by
      intro d
      by_cases h1 : M.vert d = M.vert (C.d i) <;> by_cases h2 : C.Mem d <;>
        simp [h1, h2, cochain]
    rw [sum_congr rfl fun d _ => this d, ← sum_filter, hfilter, sum_pair hne]
    decide
  · refine sum_eq_zero fun d hd => ?_
    by_contra h
    exact hv ((mem_filter.1 hd).2 ▸ C.mem_verts_of_mem ((C.cochain_ne_zero_iff).1 h))

end SCycle

/-! ### Simple cycles in closed cochains -/

/-- A path whose darts satisfy `S`: darts `e 0, …, e (m - 1)` from `v 0` to `v m` through the
pairwise distinct vertices `v 0, …, v m`. -/
structure SPathIn (M : Map D P) (S : D → Prop) where
  /-- The number of darts. -/
  m : ℕ
  /-- The darts. -/
  e : ℕ → D
  /-- The vertices. -/
  v : ℕ → P
  mem : ∀ i < m, S (e i)
  tail : ∀ i < m, M.vert (e i) = v i
  head : ∀ i < m, M.vert (M.α (e i)) = v (i + 1)
  inj : ∀ i ≤ m, ∀ j ≤ m, v i = v j → i = j

namespace SPathIn

variable {S : D → Prop} (p : SPathIn M S)

lemma m_lt_card [Fintype P] : p.m < Fintype.card P := by
  classical
  have : (range (p.m + 1)).card ≤ Fintype.card P := by
    rw [← card_univ]
    refine card_le_card_of_injOn p.v (fun _ _ => mem_coe.2 (mem_univ _)) ?_
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    exact p.inj i (by omega) j (by omega) h
  rw [card_range] at this
  omega

/-- Extending a path by a dart leading to a new vertex. -/
def extend {d : D} (hS : S d) (hd : M.vert d = p.v p.m)
    (hnew : ∀ i ≤ p.m, p.v i ≠ M.vert (M.α d)) : SPathIn M S where
  m := p.m + 1
  e i := if i < p.m then p.e i else d
  v i := if i ≤ p.m then p.v i else M.vert (M.α d)
  mem i hi := by
    split_ifs
    · exact p.mem i (by omega)
    · exact hS
  tail i hi := by
    by_cases h1 : i < p.m
    · simp only [h1, ↓reduceIte, show i ≤ p.m by omega]
      exact p.tail i h1
    · simp only [h1, ↓reduceIte, show i ≤ p.m by omega]
      rw [show i = p.m by omega]; exact hd
  head i hi := by
    by_cases h1 : i < p.m
    · simp only [h1, ↓reduceIte, show i + 1 ≤ p.m by omega]
      exact p.head i h1
    · simp only [h1, ↓reduceIte, show ¬ i + 1 ≤ p.m by omega]
  inj i hi j hj h := by
    split_ifs at h with h1 h2 h2
    · exact p.inj i h1 j h2 h
    · exact absurd h (hnew i h1)
    · exact absurd h.symm (hnew j h2)
    · omega

lemma close_vert {d : D} {j : ℕ} (hj : j ≤ p.m) (hd : M.vert d = p.v p.m) {i : ℕ}
    (hi : i < p.m - j + 1) :
    M.vert (if i < p.m - j then p.e (j + i) else d) = p.v (j + i) := by
  split_ifs with h
  · exact p.tail _ (by omega)
  · rw [hd, show j + i = p.m by omega]

/-- Closing a path with a dart back to one of its vertices gives a simple cycle. -/
def close {d : D} {j : ℕ} (hj : j ≤ p.m) (hd : M.vert d = p.v p.m)
    (hback : M.vert (M.α d) = p.v j) : M.SCycle where
  k := p.m - j + 1
  d i := if i < p.m - j then p.e (j + i) else d
  pos := by omega
  vert_α i hi := by
    have hmod : (i + 1) % (p.m - j + 1) = if i + 1 < p.m - j + 1 then i + 1 else 0 := by
      split_ifs with h
      · exact Nat.mod_eq_of_lt h
      · rw [show i + 1 = p.m - j + 1 by omega, Nat.mod_self]
    rw [hmod, p.close_vert hj hd (by split_ifs <;> omega)]
    by_cases h1 : i < p.m - j
    · simp only [h1, ↓reduceIte, show i + 1 < p.m - j + 1 by omega]
      rw [p.head _ (by omega)]
      rfl
    · simp only [h1, ↓reduceIte, show ¬ i + 1 < p.m - j + 1 by omega]
      rw [hback]
      rfl
  inj i hi j' hj' h := by
    rw [p.close_vert hj hd hi, p.close_vert hj hd hj'] at h
    have := p.inj _ (by omega) _ (by omega) h
    omega

lemma close_d {d : D} {j : ℕ} (hj : j ≤ p.m) (hd : M.vert d = p.v p.m)
    (hback : M.vert (M.α d) = p.v j) (i : ℕ) :
    (p.close hj hd hback).d i = if i < p.m - j then p.e (j + i) else d := rfl

lemma close_k {d : D} {j : ℕ} (hj : j ≤ p.m) (hd : M.vert d = p.v p.m)
    (hback : M.vert (M.α d) = p.v j) : (p.close hj hd hback).k = p.m - j + 1 := rfl

end SPathIn

section Closed

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- **Every nonzero closed cochain contains a simple cycle**: a proper simple cycle all of whose
darts lie in the support of the cochain. -/
theorem exists_scycle_of_closed (c : D → ZMod 2) (hcα : ∀ d, c (M.α d) = c d)
    (hc : ∀ v, ∑ d with M.vert d = v, c d = 0) {d₀ : D} (hd₀ : c d₀ ≠ 0) :
    ∃ C : M.SCycle, C.Proper ∧ ∀ d, C.Mem d → c d ≠ 0 := by
  classical
  have hmem : ∀ (C : M.SCycle), (∀ i < C.k, c (C.d i) ≠ 0) → ∀ d, C.Mem d → c d ≠ 0 := by
    rintro C hC d ⟨i, hi, rfl | rfl⟩
    · exact hC i hi
    · rw [hcα]; exact hC i hi
  -- a loop is a simple cycle
  by_cases hloop : M.vert (M.α d₀) = M.vert d₀
  · refine ⟨⟨1, fun _ => d₀, one_pos, fun i hi => by simpa using hloop, fun i hi j hj _ => by
      omega⟩, fun h => absurd h (show (1 : ℕ) ≠ 2 by decide), hmem _ fun _ _ => hd₀⟩
  set S : D → Prop := fun d => c d ≠ 0
  -- the path of one dart
  let p₁ : SPathIn M S := {
    m := 1
    e := fun _ => d₀
    v := fun i => if i = 0 then M.vert d₀ else M.vert (M.α d₀)
    mem := fun _ _ => hd₀
    tail := fun i hi => by simp [show i = 0 by omega]
    head := fun i hi => by simp [show i = 0 by omega]
    inj := fun i hi j hj h => by
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
        rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · rfl
      · exact absurd h.symm (by simpa using hloop)
      · exact absurd h (by simpa using hloop)
      · rfl }
  -- a longest path
  set Q : ℕ → Prop := fun m => ∃ p : SPathIn M S, p.m = m
  have hQ1 : Q 1 := ⟨p₁, rfl⟩
  set mm := Nat.findGreatest Q (Fintype.card P)
  have h1c : 1 ≤ Fintype.card P := by
    have := p₁.m_lt_card
    simp only [p₁] at this
    omega
  have hmm1 : 1 ≤ mm := Nat.le_findGreatest h1c hQ1
  obtain ⟨p, hp⟩ : Q mm := Nat.findGreatest_spec (P := Q) h1c hQ1
  have hmax : ∀ q : SPathIn M S, q.m ≤ p.m := by
    intro q
    rw [hp]
    exact Nat.le_findGreatest q.m_lt_card.le ⟨q, rfl⟩
  have hpm : 1 ≤ p.m := hp ▸ hmm1
  -- the last dart, reversed
  set a := M.α (p.e (p.m - 1))
  have ha : M.vert a = p.v p.m := by
    rw [p.head _ (by omega), Nat.sub_add_cancel hpm]
  have hca : c a ≠ 0 := by rw [hcα]; exact p.mem _ (by omega)
  -- another dart of the support at the last vertex
  obtain ⟨d', hd'v, hd'a, hd'c⟩ : ∃ d', M.vert d' = p.v p.m ∧ d' ≠ a ∧ c d' ≠ 0 := by
    by_contra hno
    push Not at hno
    have h := hc (p.v p.m)
    rw [sum_eq_single_of_mem a (by simp [ha]) fun d hd hda => hno d (mem_filter.1 hd).2 hda]
      at h
    exact hca h
  by_cases hback : ∃ j ≤ p.m, p.v j = M.vert (M.α d')
  · obtain ⟨j, hj, hjv⟩ := hback
    refine ⟨p.close hj hd'v hjv.symm, ?_, hmem _ fun i hi => ?_⟩
    · intro hk
      rw [SPathIn.close_k] at hk
      rw [SPathIn.close_d, SPathIn.close_d]
      simp only [show 0 < p.m - j by omega, show ¬ 1 < p.m - j by omega, ↓reduceIte, add_zero]
      intro h
      apply hd'a
      rw [show d' = M.α (p.e j) by rw [h, M.α_α], show j = p.m - 1 by omega]
    · rw [SPathIn.close_d]
      split_ifs with h
      · exact p.mem _ (by rw [SPathIn.close_k] at hi; omega)
      · exact hd'c
  · push Not at hback
    have := hmax (p.extend hd'c hd'v hback)
    simp [SPathIn.extend] at this

end Closed

/-! ### Connected sets of faces -/

section Bd

variable [Fintype D] [DecidableEq D]

/-- Two faces of `W` on the two sides of an edge. -/
def FAdj (W : Finset M.Face) (f g : M.Face) : Prop :=
  f ∈ W ∧ g ∈ W ∧ ∃ d, M.face d = f ∧ M.face (M.α d) = g

/-- A set of faces is *connected* if any two of its faces are joined by a sequence of faces of
the set, each adjacent to the next across an edge. -/
def FConn (W : Finset M.Face) : Prop := ∀ f ∈ W, ∀ g ∈ W, Relation.ReflTransGen (FAdj W) f g

/-- A function on the faces which agrees on the two sides of every edge inside a connected set
of faces is constant on it. -/
lemma FConn.const {W : Finset M.Face} (hW : FConn W) {β : Type*} {h : M.Face → β}
    (hh : ∀ d, M.face d ∈ W → M.face (M.α d) ∈ W → h (M.face d) = h (M.face (M.α d)))
    {f g : M.Face} (hf : f ∈ W) (hg : g ∈ W) : h f = h g := by
  have hp := hW f hf g hg
  clear hg
  induction hp with
  | refl => rfl
  | tail _ hab ih =>
    obtain ⟨h1, h2, d, rfl, rfl⟩ := hab
    exact ih.trans (hh d h1 h2)

/-- The boundary cochain of a set of faces: the edges with exactly one side in the set. -/
noncomputable def bdc (W : Finset M.Face) (d : D) : ZMod 2 :=
  (if M.face d ∈ W then 1 else 0) + (if M.face (M.α d) ∈ W then 1 else 0)

lemma bdc_α (W : Finset M.Face) (d : D) : bdc W (M.α d) = bdc W d := by
  simp only [bdc, M.α_α]
  ring

lemma bdc_eq_zero_iff (W : Finset M.Face) (d : D) :
    bdc W d = 0 ↔ (M.face d ∈ W ↔ M.face (M.α d) ∈ W) := by
  unfold bdc
  by_cases h1 : M.face d ∈ W <;> by_cases h2 : M.face (M.α d) ∈ W <;> simp [h1, h2]; decide

lemma sum_bdc [DecidableEq P] (W : Finset M.Face) (v : P) :
    ∑ d with M.vert d = v, bdc W d = 0 := by
  simp only [bdc, sum_add_distrib]
  rw [← sum_congr rfl fun d _ => congrArg (fun F => if F ∈ W then (1 : ZMod 2) else 0)
    (M.face_σ d), M.sum_vert_σ v (fun d => if M.face d ∈ W then (1 : ZMod 2) else 0),
    Kasteleyn.ZMod.two_add_self]

variable [Fintype P] [DecidableEq P]

/-- **The boundary of a connected set of faces with connected complement is a simple cycle.**
In a plane map, if a set `W` of faces and its complement are connected through edges and some
edge has exactly one side in `W`, then there is a proper simple cycle whose edges are exactly the
edges with exactly one side in `W`. -/
theorem IsPlane.exists_scycle_bd (hM : M.IsPlane) {W : Finset M.Face} (hW : FConn W)
    (hWc : FConn Wᶜ) {d₀ : D} (hd₀ : M.face d₀ ∈ W) (hd₀' : M.face (M.α d₀) ∉ W) :
    ∃ C : M.SCycle, C.Proper ∧ ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ C.Mem d := by
  classical
  have hc0 : bdc W d₀ ≠ 0 := by
    rw [Ne, bdc_eq_zero_iff]
    tauto
  obtain ⟨C, hCp, hCm⟩ := exists_scycle_of_closed (bdc W) (bdc_α W) (sum_bdc W) hc0
  obtain ⟨h, hh⟩ := hM.exists_face_cochain C.cochain C.cochain_α (C.sum_cochain hCp)
  -- off the boundary the cochain of the cycle vanishes
  have hoff : ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) → C.cochain d = 0 := by
    intro d hd
    by_contra hne
    exact hCm d ((C.cochain_ne_zero_iff).1 hne) ((bdc_eq_zero_iff W d).2 hd)
  have hsame : ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) →
      h (M.face d) = h (M.face (M.α d)) := by
    intro d hd
    have := hh d
    rw [hoff d hd] at this
    exact Kasteleyn.ZMod.two_eq_of_add_eq_zero this
  have hin : ∀ f ∈ W, h f = h (M.face d₀) := fun f hf =>
    hW.const (fun d h1 h2 => hsame d (iff_of_true h1 h2)) hf hd₀
  have hout : ∀ f ∉ W, h f = h (M.face (M.α d₀)) := fun f hf =>
    hWc.const (fun d h1 h2 => hsame d (iff_of_false (mem_compl.1 h1) (mem_compl.1 h2)))
      (mem_compl.2 hf) (mem_compl.2 hd₀')
  -- on the boundary it takes the value `h (face d₀) + h (face (α d₀))`
  have hon : ∀ d, ¬ (M.face d ∈ W ↔ M.face (M.α d) ∈ W) →
      C.cochain d = h (M.face d₀) + h (M.face (M.α d₀)) := by
    intro d hd
    rw [← hh d]
    by_cases h1 : M.face d ∈ W
    · have h2 : M.face (M.α d) ∉ W := fun h2 => hd (iff_of_true h1 h2)
      rw [hin _ h1, hout _ h2]
    · have h2 : M.face (M.α d) ∈ W := by tauto
      rw [hin _ h2, hout _ h1, add_comm]
  have hval : h (M.face d₀) + h (M.face (M.α d₀)) ≠ 0 := by
    have h0 := C.mem_d C.pos
    have hb := hCm _ h0
    rw [Ne, bdc_eq_zero_iff] at hb
    rw [← hon _ hb]
    exact (C.cochain_ne_zero_iff).2 h0
  refine ⟨C, hCp, fun d => ⟨fun hd hm => (C.cochain_ne_zero_iff).2 hm (hoff d hd), fun hm => ?_⟩⟩
  by_contra hd
  exact hm ((C.cochain_ne_zero_iff).1 (by rw [hon d hd]; exact hval))

end Bd

/-! ### The boundary of a component of the faces avoiding a set of vertices -/

lemma rtg_symm {α : Type*} {r : α → α → Prop} (hr : ∀ a b, r a b → r b a) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hr _ _ hbc) ih

/-- Two faces on the two sides of an edge. -/
def FAdj' (M : Map D P) (f g : M.Face) : Prop := ∃ d, M.face d = f ∧ M.face (M.α d) = g

lemma fAdj'_symm {f g : M.Face} (h : FAdj' M f g) : FAdj' M g f := by
  obtain ⟨d, rfl, rfl⟩ := h
  exact ⟨M.α d, rfl, by rw [M.α_α]⟩

/-- **The faces of a connected map are connected through edges.** -/
lemma Connected.face_rtg (hM : M.Connected) (f g : M.Face) :
    Relation.ReflTransGen (FAdj' M) f g := by
  obtain ⟨d₁, rfl⟩ := M.face_surjective f
  obtain ⟨d₂, rfl⟩ := M.face_surjective g
  refine hM.induction (p := fun d => Relation.ReflTransGen (FAdj' M) (M.face d₁) (M.face d))
    (fun d hd => ?_) (fun d hd => hd.tail ⟨d, rfl, rfl⟩) Relation.ReflTransGen.refl d₂
  rw [face_σ]
  exact hd.tail ⟨d, rfl, rfl⟩

lemma FAdj.symm [Fintype D] [DecidableEq D] {W : Finset M.Face} {f g : M.Face}
    (h : FAdj W f g) : FAdj W g f :=
  ⟨h.2.1, h.1, fAdj'_symm h.2.2⟩

section Comp

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- A face touches a set of vertices if one of its corners lies in it. -/
def Touch (B : Finset P) (f : M.Face) : Prop := ∃ d, M.face d = f ∧ M.vert d ∈ B

variable (M) in
open Classical in
/-- The faces touching a set of vertices. -/
noncomputable def zone (B : Finset P) : Finset M.Face := {f | Touch B f}

lemma mem_zone {B : Finset P} {f : M.Face} : f ∈ M.zone B ↔ Touch B f := by
  classical
  simp [zone]

lemma face_mem_zone {B : Finset P} {d : D} (h : M.vert d ∈ B) : M.face d ∈ M.zone B :=
  mem_zone.2 ⟨d, rfl, h⟩

variable (M) in
open Classical in
/-- The component of a face `f₀` among the faces avoiding a set `B` of vertices: the faces
avoiding `B` reached from `f₀` through edges, by faces avoiding `B`. -/
noncomputable def comp (B : Finset P) (f₀ : M.Face) : Finset M.Face :=
  {g | g ∉ M.zone B ∧ Relation.ReflTransGen (FAdj (M.zone B)ᶜ) f₀ g}

lemma mem_comp {B : Finset P} {f₀ g : M.Face} :
    g ∈ M.comp B f₀ ↔ g ∉ M.zone B ∧ Relation.ReflTransGen (FAdj (M.zone B)ᶜ) f₀ g := by
  classical
  simp [comp]

lemma comp_subset (B : Finset P) (f₀ : M.Face) : M.comp B f₀ ⊆ (M.zone B)ᶜ := fun _ h =>
  mem_compl.2 (mem_comp.1 h).1

lemma mem_comp_self {B : Finset P} {f₀ : M.Face} (h : f₀ ∉ M.zone B) : f₀ ∈ M.comp B f₀ :=
  mem_comp.2 ⟨h, Relation.ReflTransGen.refl⟩

/-- The component is closed under adjacency among the faces avoiding `B`. -/
lemma mem_comp_of_adj {B : Finset P} {f₀ : M.Face} {d : D} (h1 : M.face d ∈ M.comp B f₀)
    (h2 : M.face (M.α d) ∉ M.zone B) : M.face (M.α d) ∈ M.comp B f₀ := by
  obtain ⟨h1z, h1r⟩ := mem_comp.1 h1
  exact mem_comp.2 ⟨h2, h1r.tail ⟨mem_compl.2 h1z, mem_compl.2 h2, d, rfl, rfl⟩⟩

lemma comp_fConn (B : Finset P) (f₀ : M.Face) : FConn (M.comp B f₀) := by
  -- every face of the component is reached from `f₀` inside the component
  have key : ∀ g ∈ M.comp B f₀, Relation.ReflTransGen (FAdj (M.comp B f₀)) f₀ g := by
    intro g hg
    obtain ⟨-, hr⟩ := mem_comp.1 hg
    clear hg
    induction hr with
    | refl => exact Relation.ReflTransGen.refl
    | @tail b c hb hbc ih =>
      have hcb := hbc
      obtain ⟨hb', hc', -⟩ := hbc
      exact ih.tail ⟨mem_comp.2 ⟨mem_compl.1 hb', hb⟩,
        mem_comp.2 ⟨mem_compl.1 hc', hb.tail hcb⟩, hcb.2.2⟩
  intro f hf g hg
  exact (rtg_symm (fun _ _ h => FAdj.symm h) (key f hf)).trans (key g hg)

/-- Around a vertex all of whose faces lie in `W`, these faces are connected inside `W`. -/
lemma rtg_face_σ_pow {W : Finset M.Face} {v : P} (hW : ∀ d, M.vert d = v → M.face d ∈ W)
    {d : D} (hd : M.vert d = v) (n : ℕ) :
    Relation.ReflTransGen (FAdj W) (M.face d) (M.face ((M.σ ^ n) d)) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    refine ih.tail ⟨hW _ (by rw [M.vert_σ_pow, hd]), ?_, (M.σ ^ n) d, rfl, ?_⟩
    · rw [pow_succ', Equiv.Perm.mul_apply]
      exact hW _ (by rw [M.vert_σ, M.vert_σ_pow, hd])
    · rw [pow_succ', Equiv.Perm.mul_apply, face_σ]

/-- **The faces touching a set of vertices closed under the parents of a spanning tree are
connected.** -/
lemma zone_fConn (hM : M.IsPlane) (T : M.SpTree) {B : Finset P} (hr : T.root ∈ B)
    (hB : ∀ v ∈ B, T.parent v ∈ B) : FConn (M.zone B) := by
  obtain ⟨d₀, hd₀⟩ := hM.exists_dart T.root
  have hat : ∀ v ∈ B, ∀ d, M.vert d = v → M.face d ∈ M.zone B := fun v hv d hd =>
    face_mem_zone (hd ▸ hv)
  have key : ∀ v, v ∈ B → ∀ d, M.vert d = v →
      Relation.ReflTransGen (FAdj (M.zone B)) (M.face d₀) (M.face d) := by
    intro v
    induction v using T.induction with
    | hroot =>
      intro _ d hd
      obtain ⟨n, rfl⟩ := M.exists_σ_pow_eq (hd₀.trans hd.symm)
      exact rtg_face_σ_pow (hat _ hr) hd₀ n
    | hstep v hv ih =>
      intro hvB d hd
      have hp := hB v hvB
      have e1 := ih hp (M.α (T.par v hv)) (by rw [T.parent_of_ne hv])
      have e2 : FAdj (M.zone B) (M.face (M.α (T.par v hv))) (M.face (T.par v hv)) :=
        ⟨hat _ hp _ (by rw [T.parent_of_ne hv]), hat _ hvB _ (T.vert_par v hv),
          M.α (T.par v hv), rfl, by rw [M.α_α]⟩
      obtain ⟨n, rfl⟩ := M.exists_σ_pow_eq ((T.vert_par v hv).trans hd.symm)
      exact (e1.tail e2).trans (rtg_face_σ_pow (hat _ hvB) (T.vert_par v hv) n)
  intro f hf g hg
  obtain ⟨d, rfl, hd⟩ := mem_zone.1 hf
  obtain ⟨e, rfl, he⟩ := mem_zone.1 hg
  exact (rtg_symm (fun _ _ h => FAdj.symm h) (key _ hd d rfl)).trans (key _ he e rfl)

/-- **The complement of a component is connected**: every face off the component is joined,
off the component, to a face touching `B`, and these are connected. -/
lemma compl_comp_fConn (hM : M.IsPlane) {B : Finset P} (hZ : FConn (M.zone B))
    {d₀ : D} (hd₀ : M.vert d₀ ∈ B) (f₀ : M.Face) : FConn (M.comp B f₀)ᶜ := by
  set K := M.comp B f₀
  have hZK : M.zone B ⊆ Kᶜ := fun f hf => mem_compl.2 fun h => (mem_comp.1 h).1 hf
  have hsymm : ∀ a b, FAdj Kᶜ a b → FAdj Kᶜ b a := fun _ _ h => FAdj.symm h
  -- every face off the component reaches a face touching `B`, off the component
  have reach : ∀ g ∉ K, ∃ y ∈ M.zone B, Relation.ReflTransGen (FAdj Kᶜ) g y := by
    intro g hg
    by_cases hgz : g ∈ M.zone B
    · exact ⟨g, hgz, Relation.ReflTransGen.refl⟩
    have hpath := rtg_symm (fun _ _ h => fAdj'_symm h)
      (hM.connected.face_rtg (M.face d₀) g)
    have claim : ∀ x, Relation.ReflTransGen (FAdj' M) g x →
        (x ∉ M.zone B ∧ x ∉ K ∧ Relation.ReflTransGen (FAdj Kᶜ) g x) ∨
          ∃ y ∈ M.zone B, Relation.ReflTransGen (FAdj Kᶜ) g y := by
      intro x hx
      induction hx with
      | refl => exact Or.inl ⟨hgz, hg, Relation.ReflTransGen.refl⟩
      | @tail b c _ hbc ih =>
        rcases ih with ⟨hbz, hbK, hb⟩ | h
        · obtain ⟨d, rfl, rfl⟩ := hbc
          have hcK : M.face (M.α d) ∉ K := by
            intro hc
            apply hbK
            have := mem_comp_of_adj (d := M.α d) (by exact hc) (by rwa [M.α_α])
            rwa [M.α_α] at this
          have hstep : FAdj Kᶜ (M.face d) (M.face (M.α d)) :=
            ⟨mem_compl.2 hbK, mem_compl.2 hcK, d, rfl, rfl⟩
          by_cases hcz : M.face (M.α d) ∈ M.zone B
          · exact Or.inr ⟨_, hcz, hb.tail hstep⟩
          · exact Or.inl ⟨hcz, hcK, hb.tail hstep⟩
        · exact Or.inr h
    rcases claim _ hpath with ⟨h, -, -⟩ | h
    · exact absurd (face_mem_zone hd₀) h
    · exact h
  -- faces touching `B` are connected off the component
  have hZ' : ∀ a ∈ M.zone B, ∀ b ∈ M.zone B, Relation.ReflTransGen (FAdj Kᶜ) a b := by
    intro a ha b hb
    exact Relation.ReflTransGen.mono (fun x y hxy => ⟨hZK hxy.1, hZK hxy.2.1, hxy.2.2⟩) _ _
      (hZ a ha b hb)
  intro a ha b hb
  obtain ⟨ya, hya, ha'⟩ := reach a (mem_compl.1 ha)
  obtain ⟨yb, hyb, hb'⟩ := reach b (mem_compl.1 hb)
  exact (ha'.trans (hZ' _ hya _ hyb)).trans (rtg_symm hsymm hb')

/-- Some edge leaves the component. -/
lemma exists_bd_comp (hM : M.IsPlane) {B : Finset P} {d₀ : D} (hd₀ : M.vert d₀ ∈ B)
    {f₀ : M.Face} (hf₀ : f₀ ∉ M.zone B) :
    ∃ d, M.face d ∈ M.comp B f₀ ∧ M.face (M.α d) ∉ M.comp B f₀ := by
  by_contra hno
  push Not at hno
  have : ∀ x, Relation.ReflTransGen (FAdj' M) f₀ x → x ∈ M.comp B f₀ := by
    intro x hx
    induction hx with
    | refl => exact mem_comp_self hf₀
    | tail _ hbc ih =>
      obtain ⟨d, rfl, rfl⟩ := hbc
      exact hno d ih
  exact (mem_comp.1 (this _ (hM.connected.face_rtg f₀ (M.face d₀)))).1 (face_mem_zone hd₀)

/-- **The boundary of a component of the faces avoiding a set of vertices is a simple cycle.**
Let `T` be a spanning tree of a plane map, `B` a set of vertices containing the root and closed
under parents, and `f₀` a face with no corner in `B`. Then the boundary of the component of `f₀`
among the faces with no corner in `B` is a proper simple cycle; each of its edges has the
component on one side and a face touching `B` on the other. -/
theorem IsPlane.exists_scycle_comp (hM : M.IsPlane) (T : M.SpTree) {B : Finset P}
    (hr : T.root ∈ B) (hB : ∀ v ∈ B, T.parent v ∈ B) {f₀ : M.Face} (hf₀ : f₀ ∉ M.zone B) :
    ∃ C : M.SCycle, C.Proper ∧
      (∀ d, (M.face d ∈ M.comp B f₀ ↔ M.face (M.α d) ∈ M.comp B f₀) ↔ ¬ C.Mem d) ∧
      ∀ d, M.face d ∈ M.comp B f₀ → M.face (M.α d) ∉ M.comp B f₀ →
        M.face (M.α d) ∈ M.zone B := by
  obtain ⟨d₀, hd₀⟩ := hM.exists_dart T.root
  have hd₀B : M.vert d₀ ∈ B := hd₀ ▸ hr
  obtain ⟨d, h1, h2⟩ := exists_bd_comp hM hd₀B hf₀
  obtain ⟨C, hCp, hC⟩ := hM.exists_scycle_bd (comp_fConn B f₀)
    (compl_comp_fConn hM (zone_fConn hM T hr hB) hd₀B f₀) h1 h2
  refine ⟨C, hCp, hC, fun e he1 he2 => ?_⟩
  by_contra hz
  exact he2 (mem_comp_of_adj he1 hz)

/-- In a map whose faces are triangles, an edge leaving the component has both ends off `B`,
and the third corner of the face on the other side lies in `B`. -/
lemma bd_comp_triangle {B : Finset P} {f₀ : M.Face} {d : D}
    (h3 : M.φ (M.φ (M.φ (M.α d))) = M.α d) (h1 : M.face d ∈ M.comp B f₀)
    (hz : M.face (M.α d) ∈ M.zone B) :
    M.vert d ∉ B ∧ M.vert (M.α d) ∉ B ∧ M.vert (M.φ (M.φ (M.α d))) ∈ B := by
  have hnz := (mem_comp.1 h1).1
  have hd : M.vert d ∉ B := fun h => hnz (face_mem_zone h)
  have hαd : M.vert (M.α d) ∉ B := fun h => hnz (by
    rw [← M.face_φ d]
    exact face_mem_zone (by rwa [M.vert_φ]))
  refine ⟨hd, hαd, ?_⟩
  obtain ⟨e, he, heB⟩ := mem_zone.1 hz
  rcases M.eq_of_face_eq_of_φ_three h3 he with rfl | rfl | rfl
  · exact absurd heB hαd
  · rw [M.vert_φ, M.α_α] at heB
    exact absurd heB hd
  · exact heB

end Comp

end Map

end PlanarSeparator
