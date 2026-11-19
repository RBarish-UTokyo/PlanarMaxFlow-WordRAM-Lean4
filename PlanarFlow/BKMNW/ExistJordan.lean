module

public import PlanarFlow.BKMNW.ExistFace
public import PlanarSeparator.MillerFace

/-!
# A vertex met twice by a face separates

* `PlanarSeparator.Map.IsPlane.exists_isCycleSep`: **a proper simple cycle of a plane map bounds a
  set of faces and separates** (`PlanarSeparator.Map.IsCycleSep`): its cochain is closed, hence a
  coboundary (`PlanarSeparator.Map.IsPlane.exists_face_cochain`).
* `PlanarSeparator.Map.not_reach_of_face_twice`: **a vertex met twice by the boundary of a face
  separates the corners following it**: in a plane map without loops, the cycle of length two of
  the stellar subdivision through the vertex and the centre of the face, along the spokes of the
  two corners, has the two following corners on opposite sides.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Map

open Finset StDart

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] {M : Map D P}

/-- **A proper simple cycle of a plane map bounds a set of faces and separates** (the Jordan curve
theorem for maps): its cochain is closed, hence the coboundary of a set of faces. -/
theorem IsPlane.exists_isCycleSep (hM : M.IsPlane) {C : M.SCycle} (hC : C.Proper) :
    ∃ Z : Finset M.Face, IsCycleSep C Z (sideIn C Z) (sideOut C Z) := by
  classical
  obtain ⟨h, hh⟩ := hM.exists_face_cochain C.cochain C.cochain_α (C.sum_cochain hC)
  refine ⟨univ.filter fun f => h f = 1, isCycleSep_of_bd fun d => ?_⟩
  rw [← C.cochain_ne_zero_iff, ← hh d]
  simp only [mem_filter, mem_univ, true_and]
  generalize h (M.face d) = a
  generalize h (M.face (M.α d)) = b
  revert a b
  decide

/-- The cycle of the stellar subdivision through a vertex and the centre of a face, along the
spokes of two corners `x`, `y` of the face at the vertex. -/
def twoCycle {x y : D} (hf : M.face x = M.face y) (hv : M.vert x = M.vert y) :
    M.stellar.SCycle where
  k := 2
  d i := if i = 0 then up x else down y
  pos := by norm_num
  vert_α i hi := by
    interval_cases i
    · simp [hf]
    · simp [hv]
  inj i hi j hj h := by
    interval_cases i <;> interval_cases j <;> simp_all

/-- **A vertex met twice by the boundary of a face separates** the corners following it: in a
plane map without loops, if two distinct darts `x`, `y` of a face leave the same vertex `v`, then
no path avoiding `v` joins the heads of `x` and `y` (along reversals and steps around a vertex
other than `v`). The cycle of the stellar subdivision through `v` and the centre of the face
along the two corners separates them. -/
theorem not_reach_of_face_twice (hM : M.IsPlane) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
    {x y : D} (hxy : x ≠ y) (hf : M.φ.SameCycle x y) (hv : M.vert x = M.vert y) :
    ¬ Relation.ReflTransGen (fun a b => (b = M.α a ∨ M.vert b = M.vert a) ∧
      M.vert b ≠ M.vert x) (M.α x) (M.α y) := by
  classical
  have hface : M.face x = M.face y := M.face_eq_face_iff.2 hf
  set C := twoCycle hface hv with hCdef
  have hC : C.Proper := fun _ => by simp [C, twoCycle, hxy]
  obtain ⟨Z, hZ⟩ := (isPlane_stellar hM).exists_isCycleSep hC
  set T : D → M.stellar.Face := fun d => M.stellar.face (old d) with hT
  have hmem : ∀ δ, C.Mem δ ↔ δ = up x ∨ δ = down x ∨ δ = down y ∨ δ = up y := by
    intro δ
    simp only [SCycle.Mem, C, twoCycle]
    constructor
    · rintro ⟨i, hi, h⟩
      interval_cases i
      · simp at h; tauto
      · simp at h; tauto
    · rintro (h | h | h | h)
      · exact ⟨0, by norm_num, Or.inl (by simp [h])⟩
      · exact ⟨0, by norm_num, Or.inr (by simp [h])⟩
      · exact ⟨1, by norm_num, Or.inl (by simp [h])⟩
      · exact ⟨1, by norm_num, Or.inr (by simp [h])⟩
  have hbd := hZ.bd
  have h1 : T (M.φ.symm x) ∈ Z ↔ T x ∉ Z := by
    have := hbd (up x)
    rw [stellar_face_up, stellar_α, stα_up, stellar_face_down] at this
    have hm : C.Mem (up x) := (hmem _).2 (Or.inl rfl)
    tauto
  have h2 : T y ∈ Z ↔ T (M.φ.symm y) ∉ Z := by
    have := hbd (down y)
    rw [stellar_face_down, stellar_α, stα_down, stellar_face_up] at this
    have hm : C.Mem (down y) := (hmem _).2 (Or.inr (Or.inr (Or.inl rfl)))
    tauto
  have h3 : ∀ d, M.φ d ≠ x → M.φ d ≠ y → (T d ∈ Z ↔ T (M.φ d) ∈ Z) := by
    intro d hx hy
    have := hbd (up (M.φ d))
    rw [stellar_face_up, stellar_α, stα_up, stellar_face_down, Equiv.symm_apply_apply] at this
    have hm : ¬ C.Mem (up (M.φ d)) := by
      rw [hmem]
      rintro (h | h | h | h)
      · exact hx (StDart.up.inj h)
      · cases h
      · cases h
      · exact hy (StDart.up.inj h)
    exact this.2 hm
  -- the arc of the face from `x` to `y`
  have hex : ∃ n, 0 < n ∧ (M.φ ^ n) x = y := by
    obtain ⟨n, hn⟩ := hf.exists_nat_pow_eq
    refine ⟨n, Nat.pos_of_ne_zero fun h => hxy ?_, hn⟩
    rw [h, pow_zero, Equiv.Perm.one_apply] at hn; exact hn
  set n := Nat.find hex with hn
  have hnpos : 0 < n := (Nat.find_spec hex).1
  have hny : (M.φ ^ n) x = y := (Nat.find_spec hex).2
  have hmin : ∀ m, 0 < m → m < n → (M.φ ^ m) x ≠ y := fun m hm hmn h =>
    Nat.find_min hex hmn ⟨hm, h⟩
  have harc : ∀ i, i < n → (T x ∈ Z ↔ T ((M.φ ^ i) x) ∈ Z) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      refine (ih (by omega)).trans ?_
      have e : M.φ ((M.φ ^ i) x) = (M.φ ^ (i + 1)) x := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [← e]
      refine h3 _ (fun h => ?_) (fun h => hmin (i + 1) (by omega) hi (e ▸ h))
      -- a shorter return to `x` would give a shorter path to `y`
      have hx' : (M.φ ^ (i + 1)) x = x := e ▸ h
      refine hmin (n - (i + 1)) (by omega) (by omega) ?_
      rw [← hny]
      conv_rhs => rw [show n = (n - (i + 1)) + (i + 1) by omega, pow_add, Equiv.Perm.mul_apply,
        hx']
  have hlast : (M.φ ^ (n - 1)) x = M.φ.symm y := by
    rw [Equiv.eq_symm_apply, ← Equiv.Perm.mul_apply, ← pow_succ',
      show n - 1 + 1 = n by omega, hny]
  have hTxy : T y ∈ Z ↔ T x ∉ Z := by
    rw [h2, ← hlast, ← harc (n - 1) (by omega)]
  -- the heads of `x` and `y` lie on opposite sides
  have hside : ∀ u, M.vert u ≠ M.vert x →
      ((.inl (M.vert u) : P ⊕ M.Face) ∈ sideIn C Z ∨ (.inl (M.vert u) : P ⊕ M.Face) ∈ sideOut C Z) ∧
      (.inl (M.vert u) : P ⊕ M.Face) ∉ C.verts := by
    intro u hu
    have hnot : (.inl (M.vert u) : P ⊕ M.Face) ∉ C.verts := by
      rw [SCycle.mem_verts]
      rintro ⟨i, hi, h⟩
      have hi2 : i < 2 := hi
      interval_cases i <;> simp [C, twoCycle] at h
      exact hu h.symm
    refine ⟨?_, hnot⟩
    have := hZ.cover
    have hu' : (.inl (M.vert u) : P ⊕ M.Face) ∈ C.verts ∪ sideIn C Z ∪ sideOut C Z := by
      rw [this]; exact mem_univ _
    simp only [mem_union] at hu'
    tauto
  have hwx : ((.inl (M.vert (M.α x)) : P ⊕ M.Face) ∈ sideIn C Z ↔ T x ∈ Z) := by
    obtain ⟨hc, -⟩ := hside (M.α x) (hl x)
    have hA := hZ.inA (up (M.φ x))
    have hB := hZ.inB (up (M.φ x))
    simp only [stellar_vert_up, vert_φ, stellar_face_up, Equiv.symm_apply_apply] at hA hB
    constructor
    · exact hA
    · intro hTx
      rcases hc with h | h
      · exact h
      · exact absurd hTx (hB h)
  have hwy : ((.inl (M.vert (M.α y)) : P ⊕ M.Face) ∈ sideIn C Z ↔ T y ∈ Z) := by
    obtain ⟨hc, -⟩ := hside (M.α y) (by rw [hv]; exact hl y)
    have hA := hZ.inA (up (M.φ y))
    have hB := hZ.inB (up (M.φ y))
    simp only [stellar_vert_up, vert_φ, stellar_face_up, Equiv.symm_apply_apply] at hA hB
    constructor
    · exact hA
    · intro hTy
      rcases hc with h | h
      · exact h
      · exact absurd hTy (hB h)
  intro hreach
  have key : ∀ a, Relation.ReflTransGen (fun a b => (b = M.α a ∨ M.vert b = M.vert a) ∧
      M.vert b ≠ M.vert x) (M.α x) a → M.vert a ≠ M.vert x ∧
      ((.inl (M.vert a) : P ⊕ M.Face) ∈ sideIn C Z ↔
        (.inl (M.vert (M.α x)) : P ⊕ M.Face) ∈ sideIn C Z) := by
    intro a ha
    induction ha with
    | refl => exact ⟨hl x, Iff.rfl⟩
    | tail _ hst ih =>
      rename_i b c _
      obtain ⟨hbx, ihs⟩ := ih
      obtain ⟨hcb, hcx⟩ := hst
      refine ⟨hcx, ?_⟩
      rcases hcb with e | e
      · subst e
        obtain ⟨hcb', hnb⟩ := hside b hbx
        obtain ⟨hcc, hnc⟩ := hside (M.α b) hcx
        have n1 := hZ.noEdge (old b)
        have n2 := hZ.noEdge (old (M.α b))
        simp only [stellar_vert_old, stellar_α, stα_old, M.α_α] at n1 n2
        rw [← ihs]
        constructor
        · intro h
          rcases hcb' with h' | h'
          · exact h'
          · exact absurd h' (n2 h)
        · intro h
          rcases hcc with h' | h'
          · exact h'
          · exact absurd h' (n1 h)
      · rw [e]; exact ihs
  have := (key _ hreach).2
  rw [hwy, hwx, hTxy] at this
  tauto

end Map

end PlanarSeparator
