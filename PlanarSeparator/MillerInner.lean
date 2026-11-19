module

public import PlanarSeparator.MillerTri

/-!
# The inner region of Miller's theorem, explicitly

For the band argument (`PlanarSeparator.Map.exists_band_separator`), a heavy component `H` at a
level `l₀ ≥ 1` is bounded by a simple cycle `C` (`PlanarSeparator.Map.IsPlane.exists_scycle_comp`)
and the breadth-first tree is redirected along `C` (`PlanarSeparator.Map.inner_of_scycle`). This
file describes the result by the darts a program can test one at a time: the darts `x` with
`face x ∈ H` and `face (α x) ∉ H` (the *outgoing* darts of `H`).

* `PlanarSeparator.Map.SCycle.orient`: the darts of a proper simple cycle bounding a set of faces
  `W` all have their faces on the same side of `W`.
* `PlanarSeparator.Map.SCycle.rot`, `PlanarSeparator.Map.SCycle.rev`: a simple cycle started at
  another index, and reversed.
* `PlanarSeparator.Map.exists_oriented`: for any outgoing dart `x₀`, the outgoing darts are the
  darts of a proper simple cycle bounding `W` starting with `x₀`.
* `PlanarSeparator.Map.inner_explicit`: the inner region at a heavy component, with `c₀` the
  vertex of any outgoing dart `x₀`, `K₀` the vertices of the outgoing darts, and the redirected
  tree `T₁` given by its parent darts: `α x` at the head of every outgoing dart `x` (other than
  `c₀`), the parent dart of `T` elsewhere.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset

namespace Map

variable {D P : Type*} {M : Map D P}

namespace SCycle

/-- The successor index is injective. -/
lemma suc_inj (C : M.SCycle) {i j : ℕ} (hi : i < C.k) (hj : j < C.k) (h : C.suc i = C.suc j) :
    i = j := by
  unfold suc at h; split_ifs at h <;> omega

lemma pre_suc (C : M.SCycle) {i : ℕ} (hi : i < C.k) : C.pre (C.suc i) = i := by
  by_cases h : i + 1 < C.k
  · simp only [suc, h, ↓reduceIte, pre, Nat.add_eq_zero_iff, one_ne_zero, and_false,
      Nat.add_sub_cancel]
  · simp only [suc, h, ↓reduceIte, pre]; omega

/-- **The cycle started at the index `s`.** -/
def rot (C : M.SCycle) (s : ℕ) (hs : s < C.k) : M.SCycle where
  k := C.k
  d i := C.d (C.idxAt s i)
  pos := C.pos
  vert_α i hi := by
    rw [C.vert_α_d_suc (C.idxAt_lt hs hi), C.mod_succ hi]
    congr 2
    unfold suc idxAt; split_ifs <;> omega
  inj i hi j hj h := by
    have := C.inj _ (C.idxAt_lt hs hi) _ (C.idxAt_lt hs hj) h
    unfold idxAt at this; split_ifs at this <;> omega

/-- **The reversed cycle.** -/
def rev (C : M.SCycle) : M.SCycle where
  k := C.k
  d i := M.α (C.d (C.k - 1 - i))
  pos := C.pos
  vert_α i hi := by
    rw [M.α_α, C.mod_succ hi, C.vert_α_d_suc (by split_ifs <;> omega)]
    congr 2
    unfold suc; split_ifs <;> omega
  inj i hi j hj h := by
    rw [C.vert_α_d_suc (by omega), C.vert_α_d_suc (by omega)] at h
    have := C.suc_inj (by omega) (by omega) (C.inj _ (C.suc_lt (by omega)) _
      (C.suc_lt (by omega)) h)
    omega

lemma rot_d (C : M.SCycle) {s : ℕ} (hs : s < C.k) (i : ℕ) :
    (C.rot s hs).d i = C.d (C.idxAt s i) := rfl

lemma rot_k (C : M.SCycle) {s : ℕ} (hs : s < C.k) : (C.rot s hs).k = C.k := rfl

lemma rev_k (C : M.SCycle) : C.rev.k = C.k := rfl

lemma mem_rot (C : M.SCycle) {s : ℕ} (hs : s < C.k) {d : D} : (C.rot s hs).Mem d ↔ C.Mem d := by
  constructor
  · rintro ⟨i, hi, h⟩
    exact ⟨_, C.idxAt_lt hs hi, h⟩
  · rintro ⟨i, hi, h⟩
    refine ⟨C.off s i, C.off_lt hs hi, ?_⟩
    rw [rot_d, C.idxAt_off hs hi]
    exact h

lemma mem_rev (C : M.SCycle) {d : D} : C.rev.Mem d ↔ C.Mem d := by
  constructor
  · rintro ⟨i, hi, h | h⟩
    · exact ⟨_, (by rw [rev_k] at hi; omega : C.k - 1 - i < C.k), Or.inr h⟩
    · refine ⟨_, (by rw [rev_k] at hi; omega : C.k - 1 - i < C.k), Or.inl ?_⟩
      rw [h]; exact M.α_α _
  · rintro ⟨i, hi, h | h⟩
    · refine ⟨C.k - 1 - i, by rw [rev_k]; omega, Or.inr ?_⟩
      show d = M.α (M.α (C.d (C.k - 1 - (C.k - 1 - i))))
      rw [M.α_α, show C.k - 1 - (C.k - 1 - i) = i by omega]; exact h
    · refine ⟨C.k - 1 - i, by rw [rev_k]; omega, Or.inl ?_⟩
      show d = M.α (C.d (C.k - 1 - (C.k - 1 - i)))
      rw [show C.k - 1 - (C.k - 1 - i) = i by omega]; exact h

lemma rot_proper (C : M.SCycle) {s : ℕ} (hs : s < C.k) (hC : C.Proper) : (C.rot s hs).Proper := by
  intro h2
  rw [rot_k] at h2
  rw [rot_d, rot_d]
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
  · have e0 : C.idxAt 0 0 = 0 := by unfold idxAt; split_ifs <;> omega
    have e1 : C.idxAt 0 1 = 1 := by unfold idxAt; split_ifs <;> omega
    rw [e0, e1]; exact hC h2
  · have e0 : C.idxAt 1 0 = 1 := by unfold idxAt; split_ifs <;> omega
    have e1 : C.idxAt 1 1 = 0 := by unfold idxAt; split_ifs <;> omega
    rw [e0, e1]
    intro e
    exact hC h2 (by rw [e, M.α_α])

lemma rev_proper (C : M.SCycle) (hC : C.Proper) : C.rev.Proper := by
  intro h2
  rw [rev_k] at h2
  show M.α (C.d (C.k - 1 - 0)) ≠ M.α (M.α (C.d (C.k - 1 - 1)))
  rw [M.α_α, show C.k - 1 - 0 = 1 by omega, show C.k - 1 - 1 = 0 by omega]
  intro e
  exact hC h2 e.symm

variable [DecidableEq P]

lemma verts_rot (C : M.SCycle) {s : ℕ} (hs : s < C.k) : (C.rot s hs).verts = C.verts := by
  ext v
  rw [mem_verts, mem_verts]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨_, C.idxAt_lt hs hi, h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨C.off s i, C.off_lt hs hi, by rw [rot_d, C.idxAt_off hs hi]; exact h⟩

lemma verts_rev (C : M.SCycle) : C.rev.verts = C.verts := by
  ext v
  rw [mem_verts, mem_verts]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [rev_k] at hi
    refine ⟨_, C.suc_lt (show C.k - 1 - i < C.k by omega), ?_⟩
    rw [← C.vert_α_d_suc (by omega)]; exact h
  · rintro ⟨i, hi, h⟩
    refine ⟨C.k - 1 - C.pre i, by rw [rev_k]; omega, ?_⟩
    show M.vert (M.α (C.d (C.k - 1 - (C.k - 1 - C.pre i)))) = v
    rw [show C.k - 1 - (C.k - 1 - C.pre i) = C.pre i by have := C.pre_lt hi; omega,
      C.vert_α_d_suc (C.pre_lt hi), C.suc_pre hi]
    exact h

/-! ### The orientation of a boundary cycle -/

variable [Fintype D] {W : Finset M.Face}

/-- **Consecutive darts of a boundary cycle have their faces on the same side.** Turning around
the common vertex from the reversal of the first dart to the second one meets no other dart of
the cycle, and the side does not change at the darts off the cycle. -/
lemma orient_suc (C : M.SCycle) (hCp : C.Proper)
    (hC : ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ C.Mem d) {i : ℕ} (hi : i < C.k) :
    M.face (C.d (C.suc i)) ∈ W ↔ M.face (C.d i) ∈ W := by
  classical
  set x := M.α (C.d i)
  set y := C.d (C.suc i)
  have hxy : M.vert x = M.vert y := C.vert_α_d_suc hi
  have hne : x ≠ y := by
    by_cases hs : C.suc i = i
    · intro e
      have hy : y = C.d i := by show C.d (C.suc i) = C.d i; rw [hs]
      exact M.α_ne _ (e.trans hy)
    · exact fun e => (C.ne_of_proper hCp hi (C.suc_lt hi) (Ne.symm hs)).2 e.symm
  have hex : ∃ n, (M.σ ^ n) x = y := M.exists_σ_pow_eq hxy
  set n := Nat.find hex with hn
  have hny : (M.σ ^ n) x = y := Nat.find_spec hex
  have hmin : ∀ j < n, (M.σ ^ j) x ≠ y := fun j hj => Nat.find_min hex hj
  have hn1 : 1 ≤ n := by
    by_contra h
    rw [show n = 0 by omega, pow_zero] at hny
    exact hne hny
  have hoff : ∀ j, 1 ≤ j → j < n → ¬ C.Mem ((M.σ ^ j) x) := by
    intro j hj1 hjn hm
    have hv : M.vert ((M.σ ^ j) x) = M.vert y := by rw [M.vert_σ_pow, hxy]
    obtain ⟨i', hi', h | h⟩ := hm
    · rw [h] at hv
      have := C.inj _ hi' _ (C.suc_lt hi) hv
      exact hmin j hjn (by rw [h, this])
    · rw [h, C.vert_α_d_suc hi'] at hv
      have e := C.suc_inj hi' hi (C.inj _ (C.suc_lt hi') _ (C.suc_lt hi) hv)
      rw [e] at h
      apply hmin (n - j) (by omega)
      have hsplit : (M.σ ^ n) x = (M.σ ^ (n - j)) ((M.σ ^ j) x) := by
        rw [← Equiv.Perm.mul_apply (M.σ ^ (n - j)) (M.σ ^ j) x, ← pow_add,
          Nat.sub_add_cancel hjn.le]
      rw [← hny, hsplit, h]
  have key : ∀ j, 1 ≤ j → j ≤ n → (M.face ((M.σ ^ j) x) ∈ W ↔ M.face (C.d i) ∈ W) := by
    intro j hj1 hjn
    induction j, hj1 using Nat.le_induction with
    | base => rw [pow_one, face_σ, M.α_α]
    | succ j hj ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, face_σ, ← (hC _).2 (hoff j hj (by omega))]
      exact ih (by omega)
  rw [← hny]
  exact key n hn1 le_rfl

/-- **The darts of a boundary cycle all have their faces on the same side.** -/
lemma orient (C : M.SCycle) (hCp : C.Proper)
    (hC : ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ C.Mem d) :
    ∀ i < C.k, (M.face (C.d i) ∈ W ↔ M.face (C.d 0) ∈ W) := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [← ih (by omega), ← C.orient_suc hCp hC (by omega : i < C.k)]
    unfold suc; rw [ite_eq_left (by omega)]

end SCycle

/-! ### The outgoing darts of a set of faces -/

variable [DecidableEq P] [Fintype D]

/-- **The outgoing darts form a cycle from any of them.** If a proper simple cycle bounds `W`,
then for every dart `x₀` with `face x₀ ∈ W` and `face (α x₀) ∉ W` there is a proper simple cycle
bounding `W`, with the same vertices, whose first dart is `x₀` and whose darts are exactly the
darts `x` with `face x ∈ W` and `face (α x) ∉ W`. -/
theorem exists_oriented {W : Finset M.Face} (C : M.SCycle) (hCp : C.Proper)
    (hC : ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ C.Mem d) {x₀ : D}
    (h1 : M.face x₀ ∈ W) (h2 : M.face (M.α x₀) ∉ W) :
    ∃ C' : M.SCycle, C'.Proper ∧ C'.d 0 = x₀ ∧ C'.verts = C.verts ∧
      (∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ C'.Mem d) ∧
      ∀ x, (M.face x ∈ W ∧ M.face (M.α x) ∉ W ↔ ∃ i < C'.k, x = C'.d i) := by
  have hm : C.Mem x₀ := by
    by_contra h
    exact h2 (((hC x₀).2 h).1 h1)
  -- a cycle with the right first dart and orientation
  obtain ⟨C', hCp', h0, hv, hmem, hor⟩ : ∃ C' : M.SCycle, C'.Proper ∧ C'.d 0 = x₀ ∧
      C'.verts = C.verts ∧ (∀ d, C'.Mem d ↔ C.Mem d) ∧ ∀ i < C'.k, M.face (C'.d i) ∈ W := by
    obtain ⟨s, hs, hx | hx⟩ := hm
    · have hd0 : (C.rot s hs).d 0 = x₀ := by
        rw [SCycle.rot_d, hx]; unfold SCycle.idxAt; rw [ite_eq_left (by omega), Nat.add_zero]
      refine ⟨C.rot s hs, C.rot_proper hs hCp, hd0, C.verts_rot hs, fun d => C.mem_rot hs, ?_⟩
      have hb : ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ (C.rot s hs).Mem d :=
        fun d => by rw [C.mem_rot hs]; exact hC d
      intro i hi
      rw [(C.rot s hs).orient (C.rot_proper hs hCp) hb i hi, SCycle.rot_d]
      unfold SCycle.idxAt; rw [ite_eq_left (by omega), Nat.add_zero, ← hx]; exact h1
    · set C₁ := C.rev
      have hs' : C.k - 1 - s < C₁.k := by rw [SCycle.rev_k]; omega
      have hx₁ : C₁.d (C.k - 1 - s) = x₀ := by
        show M.α (C.d (C.k - 1 - (C.k - 1 - s))) = x₀
        rw [show C.k - 1 - (C.k - 1 - s) = s by omega, hx]
      have hp₁ := C.rev_proper hCp
      refine ⟨C₁.rot _ hs', C₁.rot_proper hs' hp₁, ?_, by rw [C₁.verts_rot, C.verts_rev],
        fun d => by rw [C₁.mem_rot, C.mem_rev], ?_⟩
      · rw [SCycle.rot_d]; unfold SCycle.idxAt; rw [ite_eq_left (by omega), Nat.add_zero, hx₁]
      have hb : ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ (C₁.rot _ hs').Mem d :=
        fun d => by rw [C₁.mem_rot, C.mem_rev]; exact hC d
      intro i hi
      rw [(C₁.rot _ hs').orient (C₁.rot_proper hs' hp₁) hb i hi, SCycle.rot_d]
      unfold SCycle.idxAt; rw [ite_eq_left (by omega), Nat.add_zero, hx₁]; exact h1
  have hb' : ∀ d, (M.face d ∈ W ↔ M.face (M.α d) ∈ W) ↔ ¬ C'.Mem d := fun d => by
    rw [hmem]; exact hC d
  refine ⟨C', hCp', h0, hv, hb', fun x => ⟨fun ⟨hx1, hx2⟩ => ?_, ?_⟩⟩
  · have hmx : C'.Mem x := by
      by_contra h
      exact hx2 (((hb' x).2 h).1 hx1)
    obtain ⟨i, hi, h | h⟩ := hmx
    · exact ⟨i, hi, h⟩
    · exfalso
      rw [h] at hx1
      exact (hb' _).1 (iff_of_true (hor i hi) hx1) (C'.mem_d hi)
  · rintro ⟨i, hi, rfl⟩
    refine ⟨hor i hi, fun h => ?_⟩
    exact (hb' _).1 (iff_of_true (hor i hi) h) (C'.mem_d hi)

/-- The vertices redirected along a whole cycle from its first dart: all but the first. -/
lemma SCycle.mem_arcR_all (C : M.SCycle) (v : P) :
    v ∈ C.arcR 0 (C.k - 1) ↔ v ∈ C.verts ∧ v ≠ M.vert (C.d 0) := by
  have hk := C.pos
  rw [C.mem_arcR]
  constructor
  · rintro ⟨hv, h1, -⟩
    refine ⟨hv, fun h => ?_⟩
    rw [h, C.idx_vert hk] at h1
    unfold SCycle.off at h1
    simp at h1
  · rintro ⟨hv, hne⟩
    obtain ⟨hi, he⟩ := C.idx_spec hv
    refine ⟨hv, ?_, ?_⟩ <;> unfold SCycle.off <;> simp only [Nat.zero_le, ↓reduceIte,
      Nat.sub_zero]
    · by_contra h0
      apply hne
      rw [← he, show C.idx v = 0 by omega]
    · omega

/-- The parent darts of the tree redirected along a whole cycle from its first dart: the reversal
of the dart of the cycle arriving at a vertex of the cycle other than the first. -/
lemma SpTree.arcTree_par_all (T : M.SpTree) (C : M.SCycle) (hr : T.root ∉ C.verts)
    (hC : ∀ i < C.k, T.height (M.vert (C.d i)) = T.height (M.vert (C.d 0))) {j : ℕ}
    (hj : j < C.k) (hne : M.vert (M.α (C.d j)) ≠ M.vert (C.d 0))
    (h : M.vert (M.α (C.d j)) ≠ (T.arcTree C 0 (C.k - 1) C.pos hr hC).root) :
    (T.arcTree C 0 (C.k - 1) C.pos hr hC).par (M.vert (M.α (C.d j))) h = M.α (C.d j) := by
  have hv : M.vert (M.α (C.d j)) ∈ C.verts := C.mem_verts_of_mem ((C.mem_α_iff).2 (C.mem_d hj))
  have hR := (C.mem_arcR_all _).2 ⟨hv, hne⟩
  show (T.redirect _ _ _ _ _ _ _ _ _).par _ h = _
  rw [SpTree.redirect_par_of_mem T h hR, SCycle.arcNxt, C.vert_α_d_suc hj,
    C.idx_vert (C.suc_lt hj), C.pre_suc hj]

lemma SpTree.arcTree_par_off (T : M.SpTree) (C : M.SCycle) (hr : T.root ∉ C.verts)
    (hC : ∀ i < C.k, T.height (M.vert (C.d i)) = T.height (M.vert (C.d 0))) {v : P}
    (hv : v ∉ C.verts ∨ v = M.vert (C.d 0))
    (h : v ≠ (T.arcTree C 0 (C.k - 1) C.pos hr hC).root) (h' : v ≠ T.root) :
    (T.arcTree C 0 (C.k - 1) C.pos hr hC).par v h = T.par v h' := by
  have hR : v ∉ C.arcR 0 (C.k - 1) := fun hm => by
    rw [C.mem_arcR_all] at hm
    rcases hv with hv | hv
    · exact hv hm.1
    · exact hm.2 hv
  show (T.redirect _ _ _ _ _ _ _ _ _).par _ h = _
  exact SpTree.redirect_par_of_notMem T h' hR

/-- **The inner region of a heavy component, explicitly.** Let `H` be a component at a level
`l₀ ≥ 1` of a plane triangulation with a breadth-first tree `T`, with a strict inside of weight
`> 2/3`, and `x₀` a dart leaving `H` (`face x₀ ∈ H`, `face (α x₀) ∉ H`). Then there is an inner
region (`PlanarSeparator.Map.Inner`) for `H` with `c₀` the vertex of `x₀`, `K₀` (at level `l₀`)
the vertices of the darts leaving `H`, and a tree `T₁` with the root of `T` whose parent darts
are `α x` at the head of every dart `x` leaving `H` (other than the vertex of `x₀`) and those of
`T` at the other vertices. -/
theorem inner_explicit [Fintype P] [DecidableEq D] (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ)
    {T : M.SpTree} (hT : IsBFS T) {w : P → ℝ} {l₀ : ℕ} (hl0 : 1 ≤ l₀) {f : M.Face}
    (hf : f ∉ M.zone (T.low l₀)) (hheavy : 2 / 3 < ∑ v ∈ ins (M.comp (T.low l₀) f), w v)
    {x₀ : D} (h1 : M.face x₀ ∈ M.comp (T.low l₀) f)
    (h2 : M.face (M.α x₀) ∉ M.comp (T.low l₀) f) :
    ∃ (K₀ : Finset P) (T₁ : M.SpTree),
      Inner T w l₀ (M.comp (T.low l₀) f) K₀ (M.vert x₀) T₁ ∧ K₀ ⊆ T.lvl l₀ ∧
      T₁.root = T.root ∧
      (∀ v, v ∈ K₀ ↔ ∃ x, (M.face x ∈ M.comp (T.low l₀) f ∧
        M.face (M.α x) ∉ M.comp (T.low l₀) f) ∧ M.vert x = v) ∧
      (∀ x, M.face x ∈ M.comp (T.low l₀) f → M.face (M.α x) ∉ M.comp (T.low l₀) f →
        M.vert (M.α x) ≠ M.vert x₀ → ∀ h, T₁.par (M.vert (M.α x)) h = M.α x) ∧
      (∀ v h h', ((∀ x, M.face x ∈ M.comp (T.low l₀) f →
        M.face (M.α x) ∉ M.comp (T.low l₀) f → M.vert (M.α x) ≠ v) ∨ v = M.vert x₀) →
          T₁.par v h = T.par v h') := by
  classical
  set H := M.comp (T.low l₀) f
  obtain ⟨C, hCp, hC, -⟩ := hM.exists_scycle_comp T (root_mem_low hT hl0)
    (fun v hv => parent_mem_low hT hv) hf
  obtain ⟨C', -, h0, -, hC', hS⟩ := exists_oriented C hCp hC h1 h2
  obtain ⟨hr, hCh, hI, hK⟩ := inner_of_scycle hM htri hT hl0 hheavy C' hC'
  rw [h0] at hI
  refine ⟨C'.verts, _, hI, hK, rfl, fun v => ?_, fun x hx1 hx2 hne h => ?_,
    fun v h h' hv => ?_⟩
  · rw [C'.mem_verts]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨_, (hS _).2 ⟨i, hi, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi, rfl⟩ := (hS x).1 hx
      exact ⟨i, hi, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := (hS x).1 ⟨hx1, hx2⟩
    exact T.arcTree_par_all C' hr hCh hj (by rw [h0]; exact hne) h
  · refine T.arcTree_par_off C' hr hCh ?_ h h'
    rcases hv with hv | hv
    · left
      intro hm
      obtain ⟨i, hi, rfl⟩ := C'.mem_verts.1 hm
      have hp := C'.pre_lt hi
      obtain ⟨y1, y2⟩ := (hS (C'.d (C'.pre i))).2 ⟨_, hp, rfl⟩
      exact hv _ y1 y2 (by rw [C'.vert_α_d_suc hp, C'.suc_pre hi])
    · right; rw [hv, h0]

end Map

end PlanarSeparator
