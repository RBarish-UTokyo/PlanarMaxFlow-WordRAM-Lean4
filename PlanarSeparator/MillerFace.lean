module

public import PlanarSeparator.MillerTri

/-!
# Simple cycle separators of triangulations with weights on vertices and faces

Let `M` be a plane map without loops all of whose faces are triangles, with `n` vertices, and
`w ≥ 0` weights of total at most `1` on its vertices and faces. Then `M` has a simple cycle `C`
of at most `6 √(3 n) + 4` darts, bounding a set `Z` of faces, such that on each side the
vertices strictly on that side and the faces on that side which are not *along* `C` (with no edge
on `C`) weigh at most `2/3` (`PlanarSeparator.Map.exists_short_cycle_separator_face`). At most
`C.k` faces along `C` lie on each side (`PlanarSeparator.Map.card_inter_along_le`).

For weights on darts, each dart counting on the side of its face
(`PlanarSeparator.Map.exists_short_cycle_separator_dart`), and for a set `S` of darts: among the
darts of `S` off `C`, those on either side number at most `2/3 #S + 2 C.k`
(`PlanarSeparator.Map.exists_short_cycle_separator_card`).

This is weaker than the form stated by G. L. Miller (*Finding small simple cycle separators for
2-connected planar graphs*, J. Comput. Syst. Sci. 32 (1986), 265–279), where all the faces on a
side count, under the hypothesis that no face weighs more than `2/3`: here the faces along the
cycle are not counted. Their number is at most the length of the cycle.

## The proof

The stellar subdivision `M.stellar` (a centre in every face, joined to its three corners) is a
plane triangulation whose vertices are the vertices and the faces of `M`; the triangulated case
with vertex weights gives a simple cycle `C'` of it bounding a set `Z'` of triangles
(`PlanarSeparator.Map.exists_short_cycle_separator_stellar`). A face of `M` is put in `Z` if two
of its three triangles lie in `Z'` (`PlanarSeparator.Map.maj`); this replaces every passage
`a → centre → b` of `C'` through the centre of a face by the edge `a b` of the face.

* Both sides of a simple cycle are connected (`PlanarSeparator.Map.fConn_of_bd`, from the fact
  that a closed cochain carried by a proper simple cycle carries all of it,
  `PlanarSeparator.Map.SCycle.ne_zero_of_closed`), and so are `Z` and its complement
  (`PlanarSeparator.Map.fConn_maj`); hence the boundary of `Z` is a simple cycle `C`
  (`PlanarSeparator.Map.IsPlane.exists_scycle_bd`), whose vertices lie on `C'`.
* A vertex strictly inside `C` lies strictly inside `C'`, and so does the centre of a face of `Z`
  not along `C`: otherwise `C'` would bound one or two triangles
  (`PlanarSeparator.Map.maj_eq_univ_of_minority`).
* If `Z` is empty or everything, `C'` bounds one or two triangles, and the boundary of the face of
  one of them separates (`PlanarSeparator.Map.exists_of_maj_eq_empty`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset StDart

namespace Map

variable {D P : Type*} {M : Map D P}

/-! ### Closed cochains inside a simple cycle -/

namespace SCycle

variable [Fintype D] [DecidableEq D] [DecidableEq P] (C : M.SCycle)

open Classical in
/-- At a vertex of a proper simple cycle start exactly two darts of the cycle. -/
lemma filter_mem_eq (hC : C.Proper) {i : ℕ} (hi : i < C.k) :
    ({d | M.vert d = M.vert (C.d i) ∧ C.Mem d} : Finset D) = {C.d i, M.α (C.d (C.pre i))} ∧
      C.d i ≠ M.α (C.d (C.pre i)) := by
  set j := C.pre i with hj
  have hj' : (i = 0 ∧ j = C.k - 1) ∨ (i ≠ 0 ∧ j = i - 1) := by
    rw [hj, SCycle.pre]; split_ifs with h <;> omega
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
  refine ⟨?_, hne⟩
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

open Classical in
/-- **A closed cochain carried by a proper simple cycle is constant along it.** -/
theorem eq_of_closed (hC : C.Proper) (c : D → ZMod 2) (hcα : ∀ d, c (M.α d) = c d)
    (hc : ∀ v, ∑ d with M.vert d = v, c d = 0) (hsupp : ∀ d, c d ≠ 0 → C.Mem d) {i : ℕ}
    (hi : i < C.k) : c (C.d i) = c (C.d 0) := by
  have step : ∀ j < C.k, c (C.d j) = c (C.d (C.pre j)) := by
    intro j hj
    obtain ⟨h1, h2⟩ := C.filter_mem_eq hC hj
    have := hc (M.vert (C.d j))
    rw [← sum_filter_of_ne (p := C.Mem) fun d _ h => hsupp d h, filter_filter, h1,
      sum_pair h2, hcα] at this
    exact Kasteleyn.ZMod.two_eq_of_add_eq_zero this
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [step _ hi, show C.pre (i + 1) = i by simp [SCycle.pre]]
    exact ih (by omega)

/-- **A nonzero closed cochain carried by a proper simple cycle carries all of it.** -/
theorem ne_zero_of_closed (hC : C.Proper) (c : D → ZMod 2) (hcα : ∀ d, c (M.α d) = c d)
    (hc : ∀ v, ∑ d with M.vert d = v, c d = 0) (hsupp : ∀ d, c d ≠ 0 → C.Mem d) {d₀ : D}
    (hd₀ : c d₀ ≠ 0) {d : D} (hd : C.Mem d) : c d ≠ 0 := by
  have hall : ∀ i < C.k, c (C.d i) ≠ 0 := by
    obtain ⟨i, hi, h | h⟩ := hsupp d₀ hd₀
    · intro j hj
      rw [C.eq_of_closed hC c hcα hc hsupp hj, ← C.eq_of_closed hC c hcα hc hsupp hi, ← h]
      exact hd₀
    · intro j hj
      rw [C.eq_of_closed hC c hcα hc hsupp hj, ← C.eq_of_closed hC c hcα hc hsupp hi, ← hcα,
        ← h]
      exact hd₀
  obtain ⟨i, hi, rfl | rfl⟩ := hd
  · exact hall i hi
  · rw [hcα]
    exact hall i hi

end SCycle

/-! ### Boundaries of sets of faces -/

section Bdc

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- In a connected map, a set of faces without boundary is empty or everything. -/
lemma eq_empty_or_univ_of_bdc (hM : M.Connected) {W : Finset M.Face} (h : ∀ d, bdc W d = 0) :
    W = ∅ ∨ W = univ := by
  by_cases hW : W = ∅
  · exact Or.inl hW
  right
  obtain ⟨f, hf⟩ := nonempty_iff_ne_empty.2 hW
  have hc := hM.face_const (g := fun f => decide (f ∈ W)) (fun d => by
    have := (bdc_eq_zero_iff W d).1 (h d)
    simp only [decide_eq_decide]
    exact this.symm)
  ext g
  simp only [mem_univ, iff_true]
  have := hc f g
  simp only [decide_eq_decide] at this
  exact this.1 hf

/-- A simple cycle bounding a set of faces is proper. -/
lemma proper_of_bd {C : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) : C.Proper := by
  intro hk h01
  have h0 : 0 < C.k := by omega
  have hb : ∀ d, bdc Z d ≠ 0 ↔ C.Mem d := fun d => by
    rw [Ne, bdc_eq_zero_iff, hbd, not_not]
  have hs := sum_bdc Z (M.vert (C.d 0))
  rw [sum_eq_single_of_mem (C.d 0) (by simp) fun d hd hne => ?_] at hs
  · exact (hb _).2 (C.mem_d h0) hs
  · by_contra hd'
    obtain ⟨i, hi, h | h⟩ := (hb d).1 hd'
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact hne h
      · rw [h] at hd
        have := C.inj 1 (by omega) 0 h0 (mem_filter.1 hd).2
        omega
    · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · have e : M.α (C.d 0) = C.d 1 := by rw [h01, M.α_α]
        rw [h, e] at hd
        have := C.inj 1 (by omega) 0 h0 (mem_filter.1 hd).2
        omega
      · rw [h, ← h01] at hne
        exact hne rfl

/-- **A set of faces whose boundary lies on the boundary cycle of `Z`** is `Z` or its
complement. -/
lemma eq_or_eq_compl_of_bdc (hM : M.Connected) {C : M.SCycle} {Z X : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d)
    (hX : ∀ d, bdc X d ≠ 0 → C.Mem d) {d₀ : D} (hd₀ : bdc X d₀ ≠ 0) : Z = X ∨ Z = Xᶜ := by
  have hall := fun d => C.ne_zero_of_closed (proper_of_bd hbd) (bdc X) (bdc_α X) (sum_bdc X) hX
    hd₀ (d := d)
  have hiff : ∀ d, (M.face d ∈ X ↔ M.face (M.α d) ∈ X) ↔ (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) := by
    intro d
    rw [hbd, ← bdc_eq_zero_iff]
    constructor
    · intro h hm
      exact hall d hm h
    · intro h
      by_contra h'
      exact h (hX d h')
  rcases eq_empty_or_univ_of_bdc hM (W := symmDiff Z X) (fun d => by
    rw [bdc_eq_zero_iff, mem_symmDiff, mem_symmDiff]
    have := hiff d
    tauto) with h | h
  · left
    ext f
    have := congrArg (f ∈ ·) h
    simp only [mem_symmDiff, notMem_empty, eq_iff_iff, iff_false] at this
    tauto
  · right
    ext f
    have := congrArg (f ∈ ·) h
    simp only [mem_symmDiff, mem_univ, eq_iff_iff, iff_true] at this
    rw [mem_compl]
    tauto

/-- **The faces on one side of a simple cycle are connected** (the combinatorial Jordan curve
theorem for the inside). -/
theorem fConn_of_bd (hM : M.Connected) {C : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) : FConn Z := by
  classical
  intro f hf g hg
  set A : Finset M.Face := {h | Relation.ReflTransGen (FAdj Z) f h}
  have hA : ∀ {h}, h ∈ A ↔ Relation.ReflTransGen (FAdj Z) f h := by simp [A]
  have hfA : f ∈ A := hA.2 Relation.ReflTransGen.refl
  have hAZ : ∀ {h}, h ∈ A → h ∈ Z := by
    intro h hh
    rcases Relation.ReflTransGen.cases_tail (hA.1 hh) with rfl | ⟨_, _, h2⟩
    · exact hf
    · exact h2.2.1
  have hX1 : ∀ d, M.face d ∈ A → M.face (M.α d) ∉ A → C.Mem d := by
    intro d h1 h2
    by_contra hm
    have hZ := (hbd d).2 hm
    exact h2 (hA.2 ((hA.1 h1).tail ⟨hAZ h1, hZ.1 (hAZ h1), d, rfl, rfl⟩))
  have hX : ∀ d, bdc A d ≠ 0 → C.Mem d := by
    intro d hd
    rw [Ne, bdc_eq_zero_iff] at hd
    by_cases h1 : M.face d ∈ A
    · exact hX1 d h1 fun h2 => hd (iff_of_true h1 h2)
    · have h2 : M.face (M.α d) ∈ A := by tauto
      exact (C.mem_α_iff).1 (hX1 (M.α d) h2 (by rwa [M.α_α]))
  suffices g ∈ A from hA.1 this
  by_cases h0 : ∃ d₀, bdc A d₀ ≠ 0
  · obtain ⟨d₀, hd₀⟩ := h0
    rcases eq_or_eq_compl_of_bdc hM hbd hX hd₀ with h | h
    · rwa [← h]
    · exact absurd hfA (by rw [← mem_compl, ← h]; exact hf)
  · push Not at h0
    rcases eq_empty_or_univ_of_bdc hM h0 with h | h
    · rw [h] at hfA
      simp at hfA
    · rw [h]
      exact mem_univ _

end Bdc

/-! ### Triangles -/

section Tri

variable {δ : D} (h : M.IsTriangle δ)
include h

lemma IsTriangle.φ_ne : M.φ δ ≠ δ := fun e => h.edge_ne₁ (by rw [e])

lemma IsTriangle.φ_φ_ne : M.φ (M.φ δ) ≠ δ := fun e => h.edge_ne₂ (by rw [e])

lemma IsTriangle.φ_φ_ne_φ : M.φ (M.φ δ) ≠ M.φ δ := fun e => h.edge_ne₃ (by rw [e])

lemma IsTriangle.α_ne_φ : M.α δ ≠ M.φ δ := fun e => h.edge_ne₁ (by rw [← e, edge_α])

lemma IsTriangle.α_ne_φ_φ : M.α δ ≠ M.φ (M.φ δ) := fun e => h.edge_ne₂ (by rw [← e, edge_α])

end Tri

lemma IsTriangle.φ_α_ne {δ : D} (h : M.IsTriangle (M.α δ)) : M.φ (M.α δ) ≠ δ := fun e =>
  h.edge_ne₁ (by rw [e, edge_α])

/-- The two sides of an edge of a triangle are different faces. -/
lemma IsTriangle.face_α_ne [Fintype D] {δ : D} (h : M.IsTriangle δ) :
    M.face (M.α δ) ≠ M.face δ := by
  intro e
  rcases M.eq_of_face_eq_of_φ_three h.φ_three e with e | e | e
  · exact M.α_ne δ e
  · exact h.α_ne_φ e
  · exact h.α_ne_φ_φ e

/-! ### The triangles of the stellar subdivision -/

section Stellar

variable [Fintype D] [DecidableEq D]

/-- The triangle of the stellar subdivision on the dart `d`: `old d → up (φ d) → down d`. -/
def stTri (M : Map D P) (d : D) : M.stellar.Face := M.stellar.face (old d)

lemma stellar_face_old (d : D) : M.stellar.face (old d) = M.stTri d := rfl

lemma stellar_face_up' (e : D) : M.stellar.face (up e) = M.stTri (M.φ.symm e) :=
  M.stellar_face_up e

lemma stellar_face_down' (d : D) : M.stellar.face (down d) = M.stTri d :=
  M.stellar_face_down d

lemma stTri_injective : Function.Injective M.stTri := by
  intro d e h
  obtain ⟨n, hn⟩ := (M.stellar.face_eq_face_iff.1 h).exists_nat_pow_eq
  have key : ∀ n : ℕ, (M.stellar.φ ^ n) (old d) = old d ∨
      (M.stellar.φ ^ n) (old d) = up (M.φ d) ∨ (M.stellar.φ ^ n) (old d) = down d := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with h | h | h <;> rw [h] <;> simp
  rcases key n with h' | h' | h' <;> rw [h'] at hn
  · exact StDart.old.inj hn
  · exact absurd hn (by simp)
  · exact absurd hn (by simp)

lemma stTri_surjective (F : M.stellar.Face) : ∃ d, M.stTri d = F := by
  obtain ⟨x, rfl⟩ := M.stellar.face_surjective F
  cases x with
  | old d => exact ⟨d, rfl⟩
  | up e => exact ⟨M.φ.symm e, (M.stellar_face_up' e).symm⟩
  | down d => exact ⟨d, (M.stellar_face_down' d).symm⟩

/-- The three darts of a triangle of the stellar subdivision. -/
lemma eq_of_stellar_face {x : StDart D} {d : D} (h : M.stellar.face x = M.stTri d) :
    x = old d ∨ x = up (M.φ d) ∨ x = down d := by
  rcases M.stellar.eq_of_face_eq_of_φ_three (M.stellar_φ_three (old d)) h with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right
    rw [h]
    simp

/-- The stellar subdivision of a map without loops has no loops. -/
lemma stellar_loopless (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (x : StDart D) :
    M.stellar.vert (M.stellar.α x) ≠ M.stellar.vert x := by
  cases x with
  | old d => simpa using hl d
  | up d => simp
  | down d => simp

variable [Fintype P] [DecidableEq P]

/-! ### The majority rule -/

/-- A face of `M` is in the *majority set* of a set `Z'` of faces of the stellar subdivision if
two consecutive triangles of it (hence two of its three triangles, for a triangle) are in `Z'`. -/
noncomputable def maj (Z' : Finset M.stellar.Face) : Finset M.Face := by
  classical exact {f | ∃ d, M.face d = f ∧ M.stTri d ∈ Z' ∧ M.stTri (M.φ d) ∈ Z'}

lemma mem_maj {Z' : Finset M.stellar.Face} {f : M.Face} :
    f ∈ maj Z' ↔ ∃ d, M.face d = f ∧ M.stTri d ∈ Z' ∧ M.stTri (M.φ d) ∈ Z' := by
  simp only [maj, Finset.mem_filter, Finset.mem_univ, true_and]

variable (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d)
include h3

lemma face_mem_maj_iff {Z' : Finset M.stellar.Face} {d : D} :
    M.face d ∈ maj Z' ↔ (M.stTri d ∈ Z' ∧ M.stTri (M.φ d) ∈ Z') ∨
      (M.stTri (M.φ d) ∈ Z' ∧ M.stTri (M.φ (M.φ d)) ∈ Z') ∨
      (M.stTri (M.φ (M.φ d)) ∈ Z' ∧ M.stTri d ∈ Z') := by
  rw [mem_maj]
  constructor
  · rintro ⟨e, he, h1, h2⟩
    rcases M.eq_of_face_eq_of_φ_three (h3 d) he with rfl | rfl | rfl
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · rw [h3] at h2
      exact Or.inr (Or.inr ⟨h1, h2⟩)
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨d, rfl, h1, h2⟩
    · exact ⟨M.φ d, M.face_φ d, h1, h2⟩
    · exact ⟨M.φ (M.φ d), by rw [M.face_φ, M.face_φ], h1, by rw [h3]; exact h2⟩

lemma maj_compl (Z' : Finset M.stellar.Face) : maj Z'ᶜ = (maj Z')ᶜ := by
  ext f
  obtain ⟨d, rfl⟩ := M.face_surjective f
  rw [mem_compl, face_mem_maj_iff h3, face_mem_maj_iff h3]
  simp only [mem_compl]
  tauto

/-- If no two consecutive darts of a face satisfy `S`, the triangles off `S` lying in `Z'`
make every face a majority face. -/
lemma maj_eq_univ {Z' : Finset M.stellar.Face} (S : D → Prop)
    (hS : ∀ e, S e → ¬ S (M.φ e) ∧ ¬ S (M.φ (M.φ e))) (hZ : ∀ e, ¬ S e → M.stTri e ∈ Z') :
    maj Z' = univ := by
  ext f
  obtain ⟨d, rfl⟩ := M.face_surjective f
  simp only [mem_univ, iff_true]
  rw [face_mem_maj_iff h3]
  by_cases h1 : S d
  · exact Or.inr (Or.inl ⟨hZ _ (hS d h1).1, hZ _ (hS d h1).2⟩)
  by_cases h2 : S (M.φ d)
  · have := (hS _ h2).1
    exact Or.inr (Or.inr ⟨hZ _ this, hZ _ h1⟩)
  · exact Or.inl ⟨hZ _ h1, hZ _ h2⟩

lemma maj_eq_empty {Z' : Finset M.stellar.Face} (S : D → Prop)
    (hS : ∀ e, S e → ¬ S (M.φ e) ∧ ¬ S (M.φ (M.φ e))) (hZ : ∀ e, M.stTri e ∈ Z' → S e) :
    maj Z' = ∅ := by
  ext f
  simp only [notMem_empty, iff_false]
  intro hf
  obtain ⟨e, -, h1, h2⟩ := mem_maj.1 hf
  exact (hS e (hZ e h1)).1 (hZ _ h2)

end Stellar

/-! ### Simple cycles of the stellar subdivision -/

section Core

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
  (htri : ∀ δ : D, M.IsTriangle δ) {C' : M.stellar.SCycle}
  {Z' : Finset M.stellar.Face}
  (hbd' : ∀ x, (M.stellar.face x ∈ Z' ↔ M.stellar.face (M.stellar.α x) ∈ Z') ↔ ¬ C'.Mem x)

include hbd'

lemma bd_old (d : D) : (M.stTri d ∈ Z' ↔ M.stTri (M.α d) ∈ Z') ↔ ¬ C'.Mem (old d) :=
  hbd' (old d)

lemma bd_spoke (d : D) :
    (M.stTri d ∈ Z' ↔ M.stTri (M.φ d) ∈ Z') ↔ ¬ C'.Mem (down (M.φ d)) := by
  have := hbd' (down (M.φ d))
  rw [stellar_α, stα_down, stellar_face_up', stellar_face_down', Equiv.symm_apply_apply] at this
  rw [← this]
  exact iff_comm

lemma mem_up_iff (d : D) : C'.Mem (up d) ↔ C'.Mem (down d) := by
  rw [← C'.mem_α_iff]
  rfl

/-- A set `X` of faces such that every dart with its face in `X` and the other side off `X`
lies on `C'` has `C'` as its boundary. -/
lemma eq_or_eq_compl_of_bd' (hM : M.IsPlane) {X : Finset M.stellar.Face}
    (hX : ∀ y, M.stellar.face y ∈ X → M.stellar.face (M.stellar.α y) ∉ X → C'.Mem y) {y₀}
    (hy₀ : M.stellar.face y₀ ∈ X) (hy₀' : M.stellar.face (M.stellar.α y₀) ∉ X) :
    Z' = X ∨ Z' = Xᶜ := by
  refine eq_or_eq_compl_of_bdc (isPlane_stellar hM).connected hbd' (fun x hx => ?_)
    (d₀ := y₀) (by rw [Ne, bdc_eq_zero_iff]; tauto)
  rw [Ne, bdc_eq_zero_iff] at hx
  by_cases h1 : M.stellar.face x ∈ X
  · exact hX x h1 fun h2 => hx (iff_of_true h1 h2)
  · have h2 : M.stellar.face (M.stellar.α x) ∈ X := by tauto
    exact (C'.mem_α_iff).1 (hX _ h2 (by rwa [M.stellar.α_α]))

/-- If the three edges of the triangle on `u` lie on `C'`, then `C'` bounds this triangle. -/
lemma eq_one (hM : M.IsPlane) {u : D} (h0 : C'.Mem (old u)) (h1 : C'.Mem (down u))
    (h2 : C'.Mem (down (M.φ u))) : Z' = {M.stTri u} ∨ Z' = {M.stTri u}ᶜ := by
  refine eq_or_eq_compl_of_bd' hbd' hM (y₀ := old u) (fun y hy _ => ?_) (mem_singleton_self _)
    (fun h => M.α_ne u (stTri_injective (mem_singleton.1 h)))
  rcases eq_of_stellar_face (mem_singleton.1 hy) with rfl | rfl | rfl
  · exact h0
  · exact (mem_up_iff hbd' _).2 h2
  · exact h1

include htri in
/-- If the four spokes of the triangles on the two sides of the edge of `u` lie on `C'`, then
`C'` bounds these two triangles. -/
lemma eq_two (hM : M.IsPlane) {u : D} (h1 : C'.Mem (down u)) (h2 : C'.Mem (down (M.φ u)))
    (h3 : C'.Mem (down (M.α u))) (h4 : C'.Mem (down (M.φ (M.α u)))) :
    Z' = {M.stTri u, M.stTri (M.α u)} ∨ Z' = {M.stTri u, M.stTri (M.α u)}ᶜ := by
  refine eq_or_eq_compl_of_bd' hbd' hM (y₀ := down u) (fun y hy hy' => ?_) (by simp
    [stellar_face_down']) ?_
  · rcases mem_insert.1 hy with hy | hy
    · rcases eq_of_stellar_face hy with rfl | rfl | rfl
      · exact absurd (by simp [stellar_face_old]) hy'
      · exact (mem_up_iff hbd' _).2 h2
      · exact h1
    · rcases eq_of_stellar_face (mem_singleton.1 hy) with rfl | rfl | rfl
      · exact absurd (by simp [stellar_face_old, M.α_α]) hy'
      · exact (mem_up_iff hbd' _).2 h4
      · exact h3
  · rw [stellar_α, stα_down, stellar_face_up']
    simp only [mem_insert, mem_singleton, not_or]
    refine ⟨fun h => (htri u).φ_ne ?_, fun h => (htri (M.α u)).φ_α_ne ?_⟩
    · nth_rw 1 [← stTri_injective h]
      simp
    · rw [← stTri_injective h]
      simp

include htri

/-- **A minority triangle.** If the triangle on `u` is the only triangle of its face off `Z'`
and the face across the edge of `u` is a majority face, then every face is a majority face: the
cycle `C'` bounds one or two triangles. -/
lemma maj_eq_univ_of_minority (hM : M.IsPlane) {u : D} (hu : M.stTri u ∉ Z')
    (hu1 : M.stTri (M.φ u) ∈ Z') (hu2 : M.stTri (M.φ (M.φ u)) ∈ Z')
    (hα : M.face (M.α u) ∈ maj Z') : maj Z' = univ := by
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  have s1 : C'.Mem (down (M.φ u)) := by
    by_contra h
    exact hu (((bd_spoke hbd' u).2 h).2 hu1)
  have s2 : C'.Mem (down u) := by
    by_contra h
    have hb := (bd_spoke hbd' (M.φ (M.φ u))).2 (by rwa [h3])
    rw [h3] at hb
    exact hu (hb.1 hu2)
  by_cases h0 : C'.Mem (old u)
  · rcases eq_one hbd' hM h0 s2 s1 with h | h
    · exact absurd (h ▸ mem_singleton_self _) hu
    · refine maj_eq_univ h3 (fun e => e = u) (fun e he => ?_) (fun e he => ?_)
      · subst he
        exact ⟨(htri e).φ_ne, (htri e).φ_φ_ne⟩
      · rw [h, mem_compl, mem_singleton]
        exact fun h' => he (stTri_injective h')
  · have hαu : M.stTri (M.α u) ∉ Z' := fun h' => hu (((bd_old hbd' u).2 h0).2 h')
    rw [face_mem_maj_iff h3] at hα
    have hp : M.stTri (M.φ (M.α u)) ∈ Z' ∧ M.stTri (M.φ (M.φ (M.α u))) ∈ Z' := by tauto
    have s3 : C'.Mem (down (M.φ (M.α u))) := by
      by_contra h
      exact hαu (((bd_spoke hbd' _).2 h).2 hp.1)
    have s4 : C'.Mem (down (M.α u)) := by
      by_contra h
      have hb := (bd_spoke hbd' (M.φ (M.φ (M.α u)))).2 (by rwa [h3])
      rw [h3] at hb
      exact hαu (hb.1 hp.2)
    rcases eq_two htri hbd' hM s2 s1 s4 s3 with h | h
    · exact absurd (h ▸ mem_insert_self _ _) hu
    · refine maj_eq_univ h3 (fun e => e = u ∨ e = M.α u) (fun e he => ?_) (fun e he => ?_)
      · have a1 := (htri u).α_ne_φ
        have a2 := (htri u).α_ne_φ_φ
        have a3 := (htri (M.α u)).φ_α_ne
        have a4 := (htri (M.α u)).α_ne_φ_φ
        rw [M.α_α] at a4
        rcases he with rfl | rfl
        · exact ⟨not_or.2 ⟨(htri e).φ_ne, Ne.symm a1⟩,
            not_or.2 ⟨(htri e).φ_φ_ne, Ne.symm a2⟩⟩
        · exact ⟨not_or.2 ⟨a3, (htri _).φ_ne⟩, not_or.2 ⟨Ne.symm a4, (htri _).φ_φ_ne⟩⟩
      · rw [h, mem_compl, mem_insert, mem_singleton, not_or]
        exact ⟨fun h' => he (Or.inl (stTri_injective h')),
          fun h' => he (Or.inr (stTri_injective h'))⟩

/-- A majority face with a triangle off `Z'`, across which lies a majority face. -/
lemma maj_eq_univ_of_minority' (hM : M.IsPlane) {u : D} (hf : M.face u ∈ maj Z')
    (hu : M.stTri u ∉ Z') (hα : M.face (M.α u) ∈ maj Z') : maj Z' = univ := by
  rw [face_mem_maj_iff (fun d => (htri d).φ_three)] at hf
  have : M.stTri (M.φ u) ∈ Z' ∧ M.stTri (M.φ (M.φ u)) ∈ Z' := by tauto
  exact maj_eq_univ_of_minority htri hbd' hM hu this.1 this.2 hα

omit hbd' htri in
lemma α_φ_symm (d : D) : M.α (M.φ.symm d) = M.σ.symm d := by
  rw [Equiv.eq_symm_apply, M.σ_α_φ_symm]

omit htri hbd' in
lemma vert_α_φ_symm (d : D) : M.vert (M.α (M.φ.symm d)) = M.vert d := by
  rw [α_φ_symm, M.vert_σ_symm]

/-- **A vertex of `C'` all of whose faces are majority faces**: then every face is. -/
lemma maj_eq_univ_of_mem_verts (hM : M.IsPlane) {v : P}
    (hall : ∀ d, M.vert d = v → M.face d ∈ maj Z') (hv : .inl v ∈ C'.verts) :
    maj Z' = univ := by
  obtain ⟨i, hi, hx⟩ := C'.mem_verts.1 hv
  have hm := C'.mem_d hi
  have hσ : ∀ d, M.vert d = v → M.face (M.α d) ∈ maj Z' := fun d hd => by
    rw [← face_σ]
    exact hall _ (by rw [M.vert_σ, hd])
  generalize C'.d i = x at hx hm
  cases x with
  | old d =>
    simp only [stellar_vert_old, Sum.inl.injEq] at hx
    have hb := (bd_old hbd' d).not.2 (not_not.2 hm)
    by_cases hA : M.stTri d ∈ Z'
    · have hA' : M.stTri (M.α d) ∉ Z' := fun h => hb (iff_of_true hA h)
      exact maj_eq_univ_of_minority' htri hbd' hM (hσ d hx) hA' (by rw [M.α_α]; exact hall d hx)
    · exact maj_eq_univ_of_minority' htri hbd' hM (hall d hx) hA (hσ d hx)
  | up d =>
    simp only [stellar_vert_up, Sum.inl.injEq] at hx
    have hm' := (mem_up_iff hbd' d).1 hm
    have hm'' : ¬¬ C'.Mem (down (M.φ (M.φ.symm d))) := by
      rw [Equiv.apply_symm_apply]; exact not_not.2 hm'
    have hb := (bd_spoke hbd' (M.φ.symm d)).not.2 hm''
    rw [Equiv.apply_symm_apply] at hb
    by_cases hA : M.stTri d ∈ Z'
    · have hA' : M.stTri (M.φ.symm d) ∉ Z' := fun h => hb (iff_of_true h hA)
      refine maj_eq_univ_of_minority' htri hbd' hM (by rw [face_φ_symm]; exact hall d hx) hA'
        ?_
      rw [α_φ_symm]
      exact hall _ (by rw [M.vert_σ_symm, hx])
    · exact maj_eq_univ_of_minority' htri hbd' hM (hall d hx) hA (hσ d hx)
  | down d => simp at hx

omit htri in
/-- Off `C'`, a face of `M` at a vertex is a majority face if and only if its triangle at the
vertex lies in `Z'`. -/
lemma face_mem_maj_iff_of_notMem (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d) {v : P}
    (hv : .inl v ∉ C'.verts) {d : D} (hd : M.vert d = v) :
    M.face d ∈ maj Z' ↔ M.stTri d ∈ Z' := by
  have hs : ¬ C'.Mem (down d) := fun h =>
    hv (by rw [← hd]; exact C'.mem_verts_of_mem ((mem_up_iff hbd' d).2 h))
  have hb := (bd_spoke hbd' (M.φ.symm d)).2 (by rwa [Equiv.apply_symm_apply])
  rw [← M.face_φ_symm d, face_mem_maj_iff h3]
  simp only [Equiv.apply_symm_apply] at hb ⊢
  tauto

omit htri in
/-- Off `C'`, all the faces of `M` at a vertex are on the same side of the majority set. -/
lemma face_mem_maj_iff_α (h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d) {v : P}
    (hv : .inl v ∉ C'.verts) {d : D} (hd : M.vert d = v) :
    M.face d ∈ maj Z' ↔ M.face (M.α d) ∈ maj Z' := by
  rw [← face_σ, face_mem_maj_iff_of_notMem hbd' h3 hv hd,
    face_mem_maj_iff_of_notMem hbd' h3 hv (by rw [M.vert_σ, hd])]
  exact face_iff_of_notMem_verts hbd' hv (d := old d) (d' := old (M.σ d)) (by simp [hd])
    (by simp [M.vert_σ, hd])

end Core

/-! ### Faces along a cycle, and complements -/

section Along

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- The faces along a simple cycle: the faces with a dart on it. -/
noncomputable def SCycle.along (C : M.SCycle) : Finset M.Face := by
  classical exact {f | ∃ d, M.face d = f ∧ C.Mem d}

lemma SCycle.mem_along {C : M.SCycle} {f : M.Face} :
    f ∈ C.along ↔ ∃ d, M.face d = f ∧ C.Mem d := by
  simp only [SCycle.along, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **At most `k` faces along a cycle of `k` darts lie on each side.** -/
lemma card_inter_along_le {C : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) : #(Z ∩ C.along) ≤ C.k := by
  classical
  have : Z ∩ C.along ⊆ (range C.k).image fun i =>
      if M.face (C.d i) ∈ Z then M.face (C.d i) else M.face (M.α (C.d i)) := by
    intro f hf
    obtain ⟨hfZ, hfa⟩ := mem_inter.1 hf
    obtain ⟨d, rfl, i, hi, rfl | rfl⟩ := SCycle.mem_along.1 hfa
    · exact mem_image.2 ⟨i, mem_range.2 hi, by simp [hfZ]⟩
    · have hn : M.face (C.d i) ∉ Z := fun h => (hbd _).1 (iff_of_true h hfZ) (C.mem_d hi)
      exact mem_image.2 ⟨i, mem_range.2 hi, by simp [hn]⟩
  exact (card_le_card this).trans (card_image_le.trans (card_range _).le)

/-- On the complement of the inside lie the outside vertices. -/
lemma sideIn_compl (hex : ∀ v : P, ∃ d, M.vert d = v) {C : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) :
    sideIn C Zᶜ = sideOut C Z := by
  ext v
  rw [mem_sideIn, mem_sideOut, mem_sideIn]
  constructor
  · rintro ⟨hv, d, hd, hdZ⟩
    refine ⟨hv, fun ⟨_, d', hd', hd'Z⟩ => mem_compl.1 hdZ ?_⟩
    exact (face_iff_of_notMem_verts hbd hv hd' hd).1 hd'Z
  · rintro ⟨hv, hn⟩
    obtain ⟨d, hd⟩ := hex v
    exact ⟨hv, d, hd, mem_compl.2 fun h => hn ⟨hv, d, hd, h⟩⟩

lemma sideOut_compl (hex : ∀ v : P, ∃ d, M.vert d = v) {C : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) :
    sideOut C Zᶜ = sideIn C Z := by
  rw [← sideIn_compl hex (bd_compl hbd), compl_compl]

end Along

/-! ### Transfer of the sides from the stellar subdivision -/

section Transfer

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
  (htri : ∀ δ : D, M.IsTriangle δ) {C' : M.stellar.SCycle}
  {Z' : Finset M.stellar.Face}
  (hbd' : ∀ x, (M.stellar.face x ∈ Z' ↔ M.stellar.face (M.stellar.α x) ∈ Z') ↔ ¬ C'.Mem x)
  {C : M.SCycle} (hbd : ∀ d, (M.face d ∈ maj Z' ↔ M.face (M.α d) ∈ maj Z') ↔ ¬ C.Mem d)

include htri hbd' hbd

lemma inl_mem_sideIn (hM : M.IsPlane) (hne : maj Z' ≠ univ) {v : P}
    (hv : v ∈ sideIn C (maj Z')) : .inl v ∈ sideIn C' Z' := by
  obtain ⟨hvC, d, hd, hdZ⟩ := mem_sideIn.1 hv
  have hall : ∀ e, M.vert e = v → M.face e ∈ maj Z' := fun e he =>
    (face_iff_of_notMem_verts hbd hvC hd he).1 hdZ
  have hv' : (.inl v : P ⊕ M.Face) ∉ C'.verts := fun h =>
    hne (maj_eq_univ_of_mem_verts htri hbd' hM hall h)
  refine mem_sideIn.2 ⟨hv', old d, by simp [hd], ?_⟩
  exact (face_mem_maj_iff_of_notMem hbd' (fun d => (htri d).φ_three) hv' hd).1 hdZ

lemma inr_mem_sideIn (hM : M.IsPlane) (hne : maj Z' ≠ univ) {f : M.Face} (hf : f ∈ maj Z')
    (hfa : f ∉ C.along) : .inr f ∈ sideIn C' Z' := by
  obtain ⟨d, rfl, h1, -⟩ := mem_maj.1 hf
  refine mem_sideIn.2 ⟨fun h => ?_, down d, rfl, by rw [stellar_face_down']; exact h1⟩
  have hα : ∀ u, M.face u = M.face d → M.face (M.α u) ∈ maj Z' := fun u hu =>
    ((hbd u).2 fun hm => hfa (SCycle.mem_along.2 ⟨u, hu, hm⟩)).1 (hu ▸ hf)
  obtain ⟨i, hi, hx⟩ := C'.mem_verts.1 h
  have hm := C'.mem_d hi
  generalize C'.d i = x at hx hm
  cases x with
  | old e => simp at hx
  | up e => simp at hx
  | down e =>
    simp only [stellar_vert_down, Sum.inr.injEq] at hx
    have hm'' : ¬¬ C'.Mem (down (M.φ (M.φ.symm e))) := by
      rw [Equiv.apply_symm_apply]; exact not_not.2 hm
    have hb := (bd_spoke hbd' (M.φ.symm e)).not.2 hm''
    rw [Equiv.apply_symm_apply] at hb
    by_cases hA : M.stTri e ∈ Z'
    · have hA' : M.stTri (M.φ.symm e) ∉ Z' := fun h => hb (iff_of_true h hA)
      exact hne (maj_eq_univ_of_minority' htri hbd' hM (by rw [face_φ_symm, hx]; exact hf) hA'
        (hα _ (by rw [face_φ_symm, hx])))
    · exact hne (maj_eq_univ_of_minority' htri hbd' hM (by rw [hx]; exact hf) hA (hα _ hx))

/-- **The weight inside the cycle of `M`** is at most the weight strictly inside `C'`. -/
lemma sum_le_sum_sideIn (hM : M.IsPlane) (hne : maj Z' ≠ univ) {w : P ⊕ M.Face → ℝ}
    (hw : ∀ x, 0 ≤ w x) :
    ∑ v ∈ sideIn C (maj Z'), w (.inl v) + ∑ f ∈ maj Z' \ C.along, w (.inr f) ≤
      ∑ x ∈ sideIn C' Z', w x := by
  rw [← sum_disjSum]
  refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun x _ _ => hw x
  rcases x with v | f
  · exact inl_mem_sideIn htri hbd' hbd hM hne (by simpa using hx)
  · have hx' : f ∈ maj Z' \ C.along := by simpa using hx
    exact inr_mem_sideIn htri hbd' hbd hM hne (mem_sdiff.1 hx').1 (mem_sdiff.1 hx').2

end Transfer

/-! ### The majority set is connected -/

section Conn

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- **The majority set of a connected set of triangles is connected.** -/
lemma fConn_maj {Z' : Finset M.stellar.Face} (hZ' : FConn Z') : FConn (maj Z') := by
  intro f hf g hg
  obtain ⟨df, rfl, hf1, -⟩ := mem_maj.1 hf
  obtain ⟨dg, rfl, hg1, -⟩ := mem_maj.1 hg
  have key : ∀ b, Relation.ReflTransGen (FAdj Z') (M.stTri df) b → ∀ e, M.stTri e = b →
      (M.face e ∈ maj Z' → Relation.ReflTransGen (FAdj (maj Z')) (M.face df) (M.face e)) ∧
      (M.face e ∉ maj Z' → M.face (M.α e) ∈ maj Z' ∧
        Relation.ReflTransGen (FAdj (maj Z')) (M.face df) (M.face (M.α e))) := by
    intro b hb
    induction hb with
    | refl =>
      intro e he
      rw [stTri_injective he]
      exact ⟨fun _ => Relation.ReflTransGen.refl, fun h => absurd hf h⟩
    | tail _ hab ih =>
      intro e he
      obtain ⟨ha, hb', x, hxa, hxb⟩ := hab
      subst he
      cases x with
      | old d =>
        have he : e = M.α d := stTri_injective hxb.symm
        subst he
        obtain ⟨ih1, ih2⟩ := ih d hxa
        refine ⟨fun hαd => ?_, fun hαd => ?_⟩
        · by_cases hd : M.face d ∈ maj Z'
          · exact (ih1 hd).tail ⟨hd, hαd, d, rfl, rfl⟩
          · exact (ih2 hd).2
        · rw [M.α_α]
          by_cases hd : M.face d ∈ maj Z'
          · exact ⟨hd, ih1 hd⟩
          · exact absurd (ih2 hd).1 hαd
      | up e' =>
        have he : e = e' := stTri_injective (by rw [← hxb, stellar_α, stα_up, stellar_face_down'])
        subst he
        have ha' : M.stTri (M.φ.symm e) ∈ Z' := by
          rw [← M.stellar_face_up']; exact hxa ▸ ha
        have hmaj : M.face (M.φ.symm e) ∈ maj Z' :=
          mem_maj.2 ⟨_, rfl, ha', by rw [Equiv.apply_symm_apply]; exact hb'⟩
        rw [face_φ_symm] at hmaj
        refine ⟨fun _ => ?_, fun h => absurd hmaj h⟩
        have := (ih (M.φ.symm e) (by rw [← M.stellar_face_up']; exact hxa)).1
          (by rwa [face_φ_symm])
        rwa [face_φ_symm] at this
      | down d =>
        have he : e = M.φ.symm d := by
          refine stTri_injective (M := M) ?_
          rw [← hxb, ← M.stellar_face_up']
          rfl
        subst he
        rw [stellar_face_down'] at hxa
        have hmaj : M.face (M.φ.symm d) ∈ maj Z' :=
          mem_maj.2 ⟨_, rfl, hb', by rw [Equiv.apply_symm_apply]; exact hxa ▸ ha⟩
        refine ⟨fun _ => ?_, fun h => absurd hmaj h⟩
        rw [face_φ_symm] at hmaj ⊢
        exact (ih d hxa).1 hmaj
  exact (key _ (hZ' _ hf1 _ hg1) dg rfl).1 hg

end Conn

/-! ### The boundary of a triangle -/

section TriCycle

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
  (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) {t : D} (ht : M.IsTriangle t)

/-- The boundary of a triangle of a map without loops, as a simple cycle of three darts. -/
def triCycle : M.SCycle where
  k := 3
  d i := if i = 0 then t else if i = 1 then M.φ t else M.φ (M.φ t)
  pos := by norm_num
  vert_α i hi := by
    interval_cases i
    · exact (M.vert_φ t).symm
    · exact (M.vert_φ _).symm
    · show M.vert (M.α (M.φ (M.φ t))) = M.vert t
      conv_rhs => rw [← ht.φ_three]
      exact (M.vert_φ _).symm
  inj i hi j hj h := by
    have e1 : M.vert (M.φ t) ≠ M.vert t := by rw [M.vert_φ]; exact hl t
    have e2 : M.vert (M.φ (M.φ t)) ≠ M.vert (M.φ t) := by rw [M.vert_φ]; exact hl _
    have e3 : M.vert t ≠ M.vert (M.φ (M.φ t)) := by
      conv_lhs => rw [← ht.φ_three]
      rw [M.vert_φ]; exact hl _
    interval_cases i <;> interval_cases j <;>
    first
      | rfl
      | exact absurd h e1
      | exact absurd h.symm e1
      | exact absurd h e2
      | exact absurd h.symm e2
      | exact absurd h e3
      | exact absurd h.symm e3

lemma triCycle_k : (triCycle hl ht).k = 3 := rfl

lemma mem_triCycle {d : D} :
    (triCycle hl ht).Mem d ↔ M.face d = M.face t ∨ M.face (M.α d) = M.face t := by
  have hface : ∀ i < 3, M.face ((triCycle hl ht).d i) = M.face t := by
    intro i hi
    interval_cases i
    · rfl
    · exact M.face_φ t
    · show M.face (M.φ (M.φ t)) = M.face t
      rw [face_φ, face_φ]
  constructor
  · rintro ⟨i, hi, rfl | rfl⟩
    · exact Or.inl (hface i hi)
    · rw [M.α_α]
      exact Or.inr (hface i hi)
  · have key : ∀ e, M.face e = M.face t → ∃ i < 3, e = (triCycle hl ht).d i := by
      intro e he
      rcases M.eq_of_face_eq_of_φ_three ht.φ_three he with rfl | rfl | rfl
      · exact ⟨0, by norm_num, rfl⟩
      · exact ⟨1, by norm_num, rfl⟩
      · exact ⟨2, by norm_num, rfl⟩
    rintro (h | h)
    · obtain ⟨i, hi, rfl⟩ := key d h
      exact ⟨i, hi, Or.inl rfl⟩
    · obtain ⟨i, hi, hi'⟩ := key _ h
      exact ⟨i, hi, Or.inr (by rw [← hi', M.α_α])⟩

/-- The boundary of a triangle bounds its face. -/
lemma bd_triCycle (htri : ∀ δ : D, M.IsTriangle δ) (d : D) :
    (M.face d ∈ ({M.face t} : Finset M.Face) ↔ M.face (M.α d) ∈ ({M.face t} : Finset M.Face)) ↔
      ¬ (triCycle hl ht).Mem d := by
  rw [mem_triCycle, mem_singleton, mem_singleton]
  have hne := (htri d).face_α_ne
  have : ¬ (M.face d = M.face t ∧ M.face (M.α d) = M.face t) := fun h =>
    hne (h.2.trans h.1.symm)
  tauto

end TriCycle

/-! ### The degenerate case: the cycle `C'` bounds one or two triangles -/

section Fallback

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
  (htri : ∀ δ : D, M.IsTriangle δ) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
  {C' : M.stellar.SCycle} {Z' : Finset M.stellar.Face}
  (hbd' : ∀ x, (M.stellar.face x ∈ Z' ↔ M.stellar.face (M.stellar.α x) ∈ Z') ↔ ¬ C'.Mem x)

include htri hl hbd'

/-- **The degenerate case.** If no face of `M` is a majority face, then `C'` bounds one or two
triangles, and the boundary of the face of one of them separates: nothing lies inside it, and
everything strictly outside it lies strictly outside `C'`. -/
lemma exists_of_maj_eq_empty (hM : M.IsPlane) (hmaj : maj Z' = ∅) {w : P ⊕ M.Face → ℝ}
    (hw : ∀ x, 0 ≤ w x) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k = 3 ∧
      (∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) ∧
      ∑ v ∈ sideIn C Z, w (.inl v) + ∑ f ∈ Z \ C.along, w (.inr f) = 0 ∧
      ∑ v ∈ sideOut C Z, w (.inl v) + ∑ f ∈ Zᶜ \ C.along, w (.inr f) ≤
        ∑ x ∈ sideOut C' Z', w x := by
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  -- a triangle in `Z'`
  obtain ⟨t, ht⟩ : ∃ t, M.stTri t ∈ Z' := by
    have := (hbd' (C'.d 0)).not.2 (not_not.2 (C'.mem_d C'.pos))
    by_cases h : M.stellar.face (C'.d 0) ∈ Z'
    · obtain ⟨t, ht⟩ := stTri_surjective (M.stellar.face (C'.d 0))
      exact ⟨t, ht ▸ h⟩
    · have h' : M.stellar.face (M.stellar.α (C'.d 0)) ∈ Z' := by tauto
      obtain ⟨t, ht⟩ := stTri_surjective (M.stellar.face (M.stellar.α (C'.d 0)))
      exact ⟨t, ht ▸ h'⟩
  have hnm : ∀ e, M.face e ∉ maj Z' := fun e => by rw [hmaj]; exact notMem_empty _
  have hn1 : ∀ {e}, M.stTri e ∈ Z' → M.stTri (M.φ e) ∉ Z' := fun he h =>
    hnm _ (mem_maj.2 ⟨_, rfl, he, h⟩)
  have hn2 : ∀ {e}, M.stTri e ∈ Z' → M.stTri (M.φ (M.φ e)) ∉ Z' := fun he h =>
    hnm _ (mem_maj.2 ⟨M.φ (M.φ _), by rw [face_φ, face_φ], h, by rw [h3]; exact he⟩)
  have hs1 : ∀ {e}, M.stTri e ∈ Z' → C'.Mem (down (M.φ e)) := fun {e} he => by
    by_contra h
    exact hn1 he (((bd_spoke hbd' _).2 h).1 he)
  have hs2 : ∀ {e}, M.stTri e ∈ Z' → C'.Mem (down e) := fun {e} he => by
    by_contra h
    have hb := (bd_spoke hbd' (M.φ (M.φ e))).2 (by rwa [h3])
    rw [h3] at hb
    exact hn2 he (hb.2 he)
  -- `Z'` consists of the triangles on `t` and `α t`
  have hZ' : ∀ F ∈ Z', F = M.stTri t ∨ F = M.stTri (M.α t) := by
    by_cases h0 : C'.Mem (old t)
    · rcases eq_one hbd' hM h0 (hs2 ht) (hs1 ht) with h | h
      · intro F hF
        rw [h] at hF
        exact Or.inl (mem_singleton.1 hF)
      · exact absurd (h ▸ ht) (by simp)
    · have hαt : M.stTri (M.α t) ∈ Z' := ((bd_old hbd' t).2 h0).1 ht
      rcases eq_two htri hbd' hM (hs2 ht) (hs1 ht) (hs2 hαt) (hs1 hαt) with h | h
      · intro F hF
        rw [h] at hF
        simpa using hF
      · exact absurd (h ▸ ht) (by simp)
  set K : Finset (P ⊕ M.Face) :=
    {.inl (M.vert t), .inl (M.vert (M.α t)), .inr (M.face t), .inr (M.face (M.α t))} with hKdef
  have hK : ∀ y, M.stellar.face y ∈ Z' → M.stellar.vert y ∈ K := by
    intro y hy
    rcases hZ' _ hy with h | h <;> rcases eq_of_stellar_face h with rfl | rfl | rfl <;>
      simp [K, M.α_α, M.vert_σ]
  have hC'K : ∀ x ∈ C'.verts, x ∈ K := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := C'.mem_verts.1 hx
    have := (hbd' (C'.d i)).not.2 (not_not.2 (C'.mem_d hi))
    by_cases h : M.stellar.face (C'.d i) ∈ Z'
    · exact hK _ h
    · have h' : M.stellar.face (M.stellar.σ (C'.d i)) ∈ Z' := by rw [face_σ]; tauto
      rw [← M.stellar.vert_σ]
      exact hK _ h'
  have hout : ∀ x ∉ K, x ∈ sideOut C' Z' := fun x hx =>
    mem_sideOut.2 ⟨fun h => hx (hC'K x h), fun h => by
      obtain ⟨-, y, rfl, hy⟩ := mem_sideIn.1 h
      exact hx (hK y hy)⟩
  -- the boundary of the face of `t`
  set C := triCycle hl (htri t) with hC
  have hC0 : C.Mem t := C.mem_d (i := 0) C.pos
  refine ⟨C, {M.face t}, rfl, bd_triCycle hl (htri t) htri, ?_, ?_⟩
  · have e1 : sideIn C {M.face t} = ∅ := by
      ext v
      simp only [notMem_empty, iff_false]
      intro hv
      obtain ⟨hvC, d, rfl, hd⟩ := mem_sideIn.1 hv
      exact hvC (C.mem_verts_of_mem ((mem_triCycle hl (htri t)).2 (Or.inl (mem_singleton.1 hd))))
    have e2 : ({M.face t} : Finset M.Face) \ C.along = ∅ := by
      rw [sdiff_eq_empty_iff_subset, singleton_subset_iff]
      exact SCycle.mem_along.2 ⟨t, rfl, hC0⟩
    rw [e1, e2, sum_empty, sum_empty, add_zero]
  · rw [← sum_disjSum]
    refine sum_le_sum_of_subset_of_nonneg (fun x hx => hout x ?_) fun x _ _ => hw x
    rcases x with v | f
    · have hvC := (mem_sideOut.1 (by simpa using hx)).1
      intro hK'
      simp only [hKdef, mem_insert, mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false]
        at hK'
      rcases hK' with rfl | rfl
      · exact hvC (C.mem_verts.2 ⟨0, C.pos, rfl⟩)
      · exact hvC (C.mem_verts.2 ⟨1, show 1 < 3 by norm_num, M.vert_φ t⟩)
    · have hx' : f ≠ M.face t ∧ f ∉ C.along := by simpa using hx
      intro hK'
      simp only [hKdef, mem_insert, mem_singleton, Sum.inr.injEq, reduceCtorEq, false_or]
        at hK'
      rcases hK' with rfl | rfl
      · exact hx'.1 rfl
      · exact hx'.2 (SCycle.mem_along.2 ⟨M.α t, rfl, (C.mem_α_iff).2 hC0⟩)

end Fallback

/-! ### Counting the faces of a triangulation -/

section Count

variable [Fintype D] [DecidableEq D]

lemma filter_face_eq_of_triangle {δ : D} (h : M.IsTriangle δ) :
    ({d | M.face d = M.face δ} : Finset D) = {δ, M.φ δ, M.φ (M.φ δ)} := by
  ext d
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · exact M.eq_of_face_eq_of_φ_three h.φ_three
  · rintro (rfl | rfl | rfl) <;> simp only [face_φ]

/-- A map all of whose faces are triangles has three darts per face. -/
lemma card_darts_eq_three_mul (htri : ∀ δ : D, M.IsTriangle δ) :
    Fintype.card D = 3 * Fintype.card M.Face := by
  rw [← card_univ, card_eq_sum_card_fiberwise (f := M.face) (t := univ) (fun _ _ => mem_univ _),
    mul_comm, ← smul_eq_mul, ← card_univ, ← sum_const]
  refine sum_congr rfl fun f _ => ?_
  obtain ⟨d, rfl⟩ := M.face_surjective f
  rw [filter_face_eq_of_triangle (htri d), card_insert_of_notMem, card_pair (htri d).φ_φ_ne_φ.symm]
  simp only [mem_insert, mem_singleton, not_or]
  exact ⟨(htri d).φ_ne.symm, (htri d).φ_φ_ne.symm⟩

/-- **A plane triangulation with `n` vertices has `2 n - 4` faces.** -/
lemma card_add_card_face [Fintype P] [DecidableEq P] (hM : M.IsPlane)
    (htri : ∀ δ : D, M.IsTriangle δ) :
    Fintype.card P + Fintype.card M.Face + 4 = 3 * Fintype.card P := by
  have h1 := hM.euler
  have h2 := M.card_darts
  have h3 := card_darts_eq_three_mul htri
  omega

end Count

/-! ### The theorem -/

section Main

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- **Simple cycle separators of triangulations with weights on vertices and faces.** Let `M`
be a plane map without loops all of whose faces are triangles, with `n` vertices, and `w`
nonnegative weights of total at most `1` on its vertices and faces. Then `M` has a simple
cycle `C` of at most `6 √(3 n) + 4` darts bounding a set `Z` of faces, such that

* the vertices strictly inside (off `C`, with their faces in `Z`) and the faces in `Z` not along
  `C` weigh at most `2/3`,
* the vertices strictly outside and the faces off `Z` not along `C` weigh at most `2/3`.

The faces *along* `C` are the faces with an edge on `C`; at most `C.k` of them lie on each side
(`PlanarSeparator.Map.card_inter_along_le`). Their weight is not controlled: a single face of
weight `1` cannot be split by any cycle, and the faces through which the cycle of the stellar
subdivision passes are sent to one side.

The cycle is obtained from the cycle of the stellar subdivision
(`PlanarSeparator.Map.exists_short_cycle_separator_stellar`) by replacing each passage
`a → centre → b` through the centre of a face by the edge `a b` of this face: the new inside is
the set of faces of `M` two of whose three triangles lie inside. -/
theorem exists_short_cycle_separator_face (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ)
    (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) {w : P ⊕ M.Face → ℝ} (hw : ∀ x, 0 ≤ w x)
    (h1 : ∑ x, w x ≤ 1) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 6 * Nat.sqrt (3 * Fintype.card P) + 4 ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ v ∈ sideIn C Z, w (.inl v) + ∑ f ∈ Z \ C.along, w (.inr f) ≤ 2 / 3 ∧
      ∑ v ∈ sideOut C Z, w (.inl v) + ∑ f ∈ Zᶜ \ C.along, w (.inr f) ≤ 2 / 3 := by
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  obtain ⟨C', Z', hk', hsep', hin', hout'⟩ := exists_short_cycle_separator_stellar hM hl hw h1
  have hsq := Nat.sqrt_le_sqrt
    (h := (card_add_card_face hM htri).le.trans' (Nat.le_add_right _ 4))
  have hbd' := hsep'.bd
  have hbdc' := bd_compl hbd'
  have hex' := (isPlane_stellar hM).exists_dart
  have hconn' := (isPlane_stellar hM).connected
  by_cases hnd : ∃ d₀, M.face d₀ ∈ maj Z' ∧ M.face (M.α d₀) ∉ maj Z'
  · obtain ⟨d₀, hd₀, hd₀'⟩ := hnd
    have hW : FConn (maj Z') := fConn_maj (fConn_of_bd hconn' hbd')
    have hWc : FConn (maj Z')ᶜ := by
      rw [← maj_compl h3]
      exact fConn_maj (fConn_of_bd hconn' hbdc')
    obtain ⟨C, -, hbd⟩ := hM.exists_scycle_bd hW hWc hd₀ hd₀'
    have hbdc := bd_compl hbd
    rw [← maj_compl h3] at hbdc
    have hne : maj Z' ≠ univ := fun h => hd₀' (h ▸ mem_univ _)
    have hne' : maj Z'ᶜ ≠ univ := by
      rw [maj_compl h3]
      intro h
      have : M.face d₀ ∈ (maj Z')ᶜ := by rw [h]; exact mem_univ _
      exact mem_compl.1 this hd₀
    refine ⟨C, maj Z', ?_, isCycleSep_of_bd hbd, ?_, ?_⟩
    · have hsub : C.verts.map Function.Embedding.inl ⊆ C'.verts := by
        intro x hx
        obtain ⟨v, hv, rfl⟩ := mem_map.1 hx
        obtain ⟨i, hi, rfl⟩ := C.mem_verts.1 hv
        by_contra h
        exact (hbd _).1 (face_mem_maj_iff_α hbd' h3 h rfl) (C.mem_d hi)
      have := card_le_card hsub
      rw [card_map, C.card_verts, C'.card_verts] at this
      omega
    · exact (sum_le_sum_sideIn htri hbd' hbd hM hne hw).trans hin'
    · have := sum_le_sum_sideIn htri hbdc' hbdc hM hne' hw
      rw [maj_compl h3, sideIn_compl hM.exists_dart hbd, sideIn_compl hex' hbd'] at this
      exact this.trans hout'
  · push Not at hnd
    have hb : ∀ d, bdc (maj Z') d = 0 := fun d => by
      rw [bdc_eq_zero_iff]
      exact ⟨hnd d, fun h => by have := hnd (M.α d) h; rwa [M.α_α] at this⟩
    rcases eq_empty_or_univ_of_bdc hM.connected hb with h | h
    · obtain ⟨C, Z, hk, hbd, hin, hout⟩ := exists_of_maj_eq_empty htri hl hbd' hM h hw
      exact ⟨C, Z, by omega, isCycleSep_of_bd hbd, by rw [hin]; norm_num, hout.trans hout'⟩
    · have h' : maj Z'ᶜ = ∅ := by rw [maj_compl h3, h, compl_univ]
      obtain ⟨C, Z, hk, hbd, hin, hout⟩ := exists_of_maj_eq_empty htri hl hbdc' hM h' hw
      rw [sideOut_compl hex' hbd'] at hout
      exact ⟨C, Z, by omega, isCycleSep_of_bd hbd, by rw [hin]; norm_num, hout.trans hin'⟩

end Main

/-! ### Weights on darts -/

section Darts

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

/-- **Simple cycle separators of triangulations with weights on darts.** Let `M` be a plane map
without loops all of whose faces are triangles, with `n` vertices, and `w` nonnegative weights of
total at most `1` on its darts. Then `M` has a simple cycle `C` of at most `6 √(3 n) + 4` darts
bounding a set `Z` of faces such that the darts whose face lies in `Z` and is not along `C`, and
the darts whose face lies off `Z` and is not along `C`, weigh at most `2/3` each. -/
theorem exists_short_cycle_separator_dart (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ)
    (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) {w : D → ℝ} (hw : ∀ d, 0 ≤ w d)
    (h1 : ∑ d, w d ≤ 1) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 6 * Nat.sqrt (3 * Fintype.card P) + 4 ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      ∑ d with M.face d ∈ Z \ C.along, w d ≤ 2 / 3 ∧
      ∑ d with M.face d ∈ Zᶜ \ C.along, w d ≤ 2 / 3 := by
  classical
  set W : P ⊕ M.Face → ℝ := fun x => Sum.elim (fun _ => 0) (fun f => ∑ d with M.face d = f, w d) x
  have hW : ∀ x, 0 ≤ W x := by
    rintro (v | f)
    · exact le_rfl
    · exact sum_nonneg fun d _ => hw d
  have hfib : ∀ F : Finset M.Face, ∑ f ∈ F, W (.inr f) = ∑ d with M.face d ∈ F, w d := by
    intro F
    rw [← sum_fiberwise_of_maps_to (s := ({d | M.face d ∈ F} : Finset D)) (t := F)
      (g := M.face) (fun d hd => (mem_filter.1 hd).2)]
    refine sum_congr rfl fun f hf => ?_
    simp only [W, Sum.elim_inr]
    rw [filter_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro rfl; exact ⟨hf, rfl⟩
    · exact fun h => h.2
  have h1' : ∑ x, W x ≤ 1 := by
    rw [Fintype.sum_sum_type, hfib univ]
    have e : ∑ v : P, W (.inl v) = 0 := sum_eq_zero fun _ _ => rfl
    rw [e, zero_add]
    simpa using h1
  obtain ⟨C, Z, hk, hsep, hin, hout⟩ := exists_short_cycle_separator_face hM htri hl hW h1'
  refine ⟨C, Z, hk, hsep, ?_, ?_⟩
  · rw [← hfib]
    have := sum_nonneg fun v (_ : v ∈ sideIn C Z) => hW (.inl v)
    linarith
  · rw [← hfib]
    have := sum_nonneg fun v (_ : v ∈ sideOut C Z) => hW (.inl v)
    linarith

open Classical in
/-- A face along a cycle has at most two darts off the cycle. -/
lemma card_filter_not_mem_le (htri : ∀ δ : D, M.IsTriangle δ) {C : M.SCycle} {f : M.Face}
    (hf : f ∈ C.along) : #({d | M.face d = f ∧ ¬ C.Mem d} : Finset D) ≤ 2 := by
  classical
  obtain ⟨e, rfl, he⟩ := SCycle.mem_along.1 hf
  have hsub : ({d | M.face d = M.face e ∧ ¬ C.Mem d} : Finset D) ⊆
      ({e, M.φ e, M.φ (M.φ e)} : Finset D).erase e := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := (mem_filter.1 hd).2
    refine mem_erase.2 ⟨fun h => hd2 (h ▸ he), ?_⟩
    rw [← filter_face_eq_of_triangle (htri e)]
    simp [hd1]
  refine (card_le_card hsub).trans ?_
  rw [card_erase_of_mem (mem_insert_self _ _), card_insert_of_notMem,
    card_pair (htri e).φ_φ_ne_φ.symm]
  simp only [mem_insert, mem_singleton, not_or]
  exact ⟨(htri e).φ_ne.symm, (htri e).φ_φ_ne.symm⟩

open Classical in
/-- The darts off a simple cycle with their faces in a set of faces, counted against the darts
of the faces off the cycle. -/
lemma card_le_of_along (htri : ∀ δ : D, M.IsTriangle δ) {C : M.SCycle} (S : Finset D)
    (Y : Finset M.Face) :
    #{d ∈ S | M.face d ∈ Y ∧ ¬ C.Mem d} ≤ #{d ∈ S | M.face d ∈ Y \ C.along} +
      2 * #(Y ∩ C.along) := by
  classical
  have hsub : ({d ∈ S | M.face d ∈ Y ∧ ¬ C.Mem d} : Finset D) ⊆
      {d ∈ S | M.face d ∈ Y \ C.along} ∪
        ({d | M.face d ∈ Y ∩ C.along ∧ ¬ C.Mem d} : Finset D) := by
    intro d hd
    obtain ⟨hdS, hdY, hdC⟩ := mem_filter.1 hd
    by_cases ha : M.face d ∈ C.along
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, mem_inter.2 ⟨hdY, ha⟩, hdC⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨hdS, mem_sdiff.2 ⟨hdY, ha⟩⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_left ?_ _))
  rw [card_eq_sum_card_fiberwise (f := M.face) (t := Y ∩ C.along)
    fun d hd => (mem_filter.1 hd).2.1, mul_comm, ← smul_eq_mul, ← sum_const]
  refine sum_le_sum fun f hf => (card_le_card fun d hd => ?_).trans
    (card_filter_not_mem_le htri (mem_inter.1 hf).2)
  obtain ⟨hd1, hd2⟩ := mem_filter.1 hd
  exact mem_filter.2 ⟨mem_univ _, hd2, (mem_filter.1 hd1).2.2⟩

open Classical in
/-- **Splitting a set of darts by a short simple cycle.** Let `M` be a plane map without loops
all of whose faces are triangles, with `n` vertices, and `S` a set of darts. Then `M` has a simple
cycle `C` of at most `6 √(3 n) + 4` darts bounding a set `Z` of faces such that, among the darts
of `S` off `C`, those with their face in `Z` and those with their face off `Z` number at most
`2/3 #S + 2 C.k` each. Every dart of `S` off `C` has its reversal on the same side
(`IsCycleSep.bd`), so if `S` is closed under reversal so are the two parts. -/
theorem exists_short_cycle_separator_card (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ)
    (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (S : Finset D) :
    ∃ (C : M.SCycle) (Z : Finset M.Face), C.k ≤ 6 * Nat.sqrt (3 * Fintype.card P) + 4 ∧
      IsCycleSep C Z (sideIn C Z) (sideOut C Z) ∧
      3 * #{d ∈ S | M.face d ∈ Z ∧ ¬ C.Mem d} ≤ 2 * #S + 6 * C.k ∧
      3 * #{d ∈ S | M.face d ∉ Z ∧ ¬ C.Mem d} ≤ 2 * #S + 6 * C.k := by
  classical
  set w : D → ℝ := fun d => if d ∈ S then 1 / (#S : ℝ) else 0
  have hw : ∀ d, 0 ≤ w d := fun d => by
    simp only [w]
    split_ifs <;> positivity
  have hsum : ∀ T : Finset D, ∑ d ∈ T, w d = #(T ∩ S) * (1 / (#S : ℝ)) := by
    intro T
    simp only [w]
    rw [← sum_filter, sum_const, nsmul_eq_mul, filter_mem_eq_inter]
  have h1 : ∑ d, w d ≤ 1 := by
    rw [hsum, univ_inter]
    rcases Nat.eq_zero_or_pos #S with h | h
    · rw [h]; norm_num
    · rw [mul_one_div, div_self (by positivity)]
  obtain ⟨C, Z, hk, hsep, hin, hout⟩ := exists_short_cycle_separator_dart hM htri hl hw h1
  -- the darts of `S` with their face in a set not along `C`
  have hpart : ∀ Y : Finset M.Face, ∑ d with M.face d ∈ Y, w d ≤ 2 / 3 →
      3 * #{d ∈ S | M.face d ∈ Y} ≤ 2 * #S := by
    intro Y hY
    rw [hsum] at hY
    have e : ({d | M.face d ∈ Y} : Finset D) ∩ S = {d ∈ S | M.face d ∈ Y} := by
      ext d
      simp [and_comm]
    rw [e] at hY
    rcases Nat.eq_zero_or_pos #S with h | h
    · rw [h, card_eq_zero.2 (by rw [card_eq_zero.1 h]; rfl)]
    · have hS : (0 : ℝ) < #S := by exact_mod_cast h
      rw [mul_one_div, div_le_iff₀ hS] at hY
      exact_mod_cast (by linarith : (3 * #{d ∈ S | M.face d ∈ Y} : ℝ) ≤ 2 * #S)
  have hbd := hsep.bd
  have h1' := card_le_of_along htri (C := C) S Z
  have h2' := card_le_of_along htri (C := C) S Zᶜ
  have h3' := card_inter_along_le hbd
  have h4' := card_inter_along_le (bd_compl hbd)
  have h5 := hpart _ hin
  have h6 := hpart _ hout
  refine ⟨C, Z, hk, hsep, by omega, le_trans (Nat.mul_le_mul_left 3 (card_le_card
    (t := ({d ∈ S | M.face d ∈ Zᶜ ∧ ¬ C.Mem d} : Finset D)) fun d hd => ?_)) (by omega)⟩
  simp only [mem_filter, mem_compl] at hd ⊢
  exact hd

end Darts

/-! ### The hypotheses can be met -/

/-- The map of a single edge: two vertices, two darts, one face. -/
def edgeMap : Map Bool Bool where
  α := ⟨not, not, fun b => by cases b <;> rfl, fun b => by cases b <;> rfl⟩
  σ := Equiv.refl Bool
  vert := id
  α_α d := by cases d <;> rfl
  α_ne d := by cases d <;> decide
  vert_σ _ := rfl
  sameCycle d d' h := by
    subst h
    exact Equiv.Perm.SameCycle.refl _ _

lemma edgeMap_isPlane : edgeMap.IsPlane where
  exists_dart v := ⟨v, rfl⟩
  connected d d' := by
    by_cases h : d' = d
    · subst h
      exact Relation.ReflTransGen.refl
    · refine Relation.ReflTransGen.single (Or.inr ?_)
      cases d <;> cases d' <;> simp_all [edgeMap]
  euler := by
    have hF : Fintype.card edgeMap.Face = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨edgeMap.face true, fun f => ?_⟩
      obtain ⟨d, rfl⟩ := edgeMap.face_surjective f
      cases d
      · rw [← edgeMap.face_φ false]
        rfl
      · rfl
    have hE : Fintype.card edgeMap.Edge = 1 := by
      rw [Fintype.card_eq_one_iff]
      refine ⟨edgeMap.edge true, fun e => ?_⟩
      obtain ⟨d, rfl⟩ := edgeMap.edge_surjective e
      cases d
      · rw [← edgeMap.edge_α false]
        rfl
      · rfl
    rw [hF, hE]
    rfl

lemma edgeMap_loopless (d : Bool) : edgeMap.vert (edgeMap.α d) ≠ edgeMap.vert d := by
  cases d <;> decide

/-- **The hypotheses of `PlanarSeparator.Map.exists_short_cycle_separator_face` can be met**:
the stellar subdivision of the map of a single edge (three vertices, two triangles) is a plane
map without loops all of whose faces are triangles; the weights may be taken to be `0`. -/
theorem stellar_edgeMap :
    edgeMap.stellar.IsPlane ∧ (∀ δ, edgeMap.stellar.IsTriangle δ) ∧
      ∀ d, edgeMap.stellar.vert (edgeMap.stellar.α d) ≠ edgeMap.stellar.vert d :=
  ⟨isPlane_stellar edgeMap_isPlane, edgeMap.isTriangle_stellar edgeMap_loopless,
    stellar_loopless edgeMap_loopless⟩

end Map

end PlanarSeparator
