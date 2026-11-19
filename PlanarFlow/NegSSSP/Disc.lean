module

public import PlanarFlow.NegSSSP.SepMaps
public import PlanarFlow.MSSP.NonCrossing

/-!
# The closed side of a simple cycle as a plane map with the cycle as a face

Let `M` be a plane map without loops (of `PlanarSeparator`), `C` a simple cycle of `M` and `Z` a
set of faces bounded by `C` (the darts of `C` are exactly the darts with one side in `Z`). The
**disc** of `Z` is the submap of the darts with a side in `Z` (`discDarts`), with the rotation of
`M` cut down to them (its first return, `PlanarFlow.Orbit.ret`), as a map of `PlanarFlow`
(`discMap`). Its faces are the faces of `Z`, and one more face, outside, whose boundary walk is
the cycle `C`:

* `discMap_isPlane`, `discMap_rotTrans`, `discMap_faceTrans`: the disc is a plane map with
  transitive rotations and faces (the faces of `Z` are connected, `PlanarSeparator.Map.fConn_of_bd`,
  and deleting edges keeps the Euler gap zero, `PlanarFlow.Orbit.gap_ret_eq_zero`);
* `discMap_tail_eq_iff`: two darts of the disc have the same tail if and only if they have the
  same vertex in `M`;
* `exists_disc_faceCycle`: **the cycle `C` is the boundary walk of a face of the disc**
  (`PlanarFlow.MSSP.FaceCycle`, the form of the faces from which Klein's multiple-source shortest
  paths start), through all the vertices of `C`. After a dart `e` of `C` with its face outside
  `Z`, the boundary walk of the disc turns around the head of `e` through faces outside `Z` until
  the next dart with a side in `Z`, which is the next dart of `C` (`dσ_outer`).

This is the setting of the article (Mozes and Wulff-Nilsen, Section 2: a region lies inside one of
the cycles bounding it, its external face), here for the two sides of one separating cycle.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map

variable {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] {M : Map X P}

/-! ### The reversed cycle -/

namespace SCycleRv

variable (C : M.SCycle)

/-- **The reversed cycle**: the reverses of the darts of `C`, in the opposite order. -/
def rv : M.SCycle where
  k := C.k
  d i := M.α (C.d (C.k - 1 - i))
  pos := C.pos
  vert_α i hi := by
    rw [M.α_α]
    rcases Nat.lt_or_ge (i + 1) C.k with h | h
    · rw [Nat.mod_eq_of_lt h, C.vert_α _ (by omega)]
      congr 2
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · have hi' : i = C.k - 1 := by omega
      subst hi'
      rw [show C.k - 1 + 1 = C.k by omega, Nat.mod_self, C.vert_α _ (by omega),
        show C.k - 1 - 0 + 1 = C.k by omega, Nat.mod_self, Nat.sub_self]
  inj i hi j hj h := by
    rw [C.vert_α _ (by omega), C.vert_α _ (by omega)] at h
    have := C.inj _ (Nat.mod_lt _ C.pos) _ (Nat.mod_lt _ C.pos) h
    rcases Nat.lt_or_ge (C.k - 1 - i + 1) C.k with h1 | h1 <;>
      rcases Nat.lt_or_ge (C.k - 1 - j + 1) C.k with h2 | h2
    · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this; omega
    · rw [Nat.mod_eq_of_lt h1, show C.k - 1 - j + 1 = C.k by omega, Nat.mod_self] at this
      omega
    · rw [Nat.mod_eq_of_lt h2, show C.k - 1 - i + 1 = C.k by omega, Nat.mod_self] at this
      omega
    · omega

@[simp] lemma rv_k : (rv C).k = C.k := rfl

lemma rv_d (i : ℕ) : (rv C).d i = M.α (C.d (C.k - 1 - i)) := rfl

lemma rv_mem {d : X} : (rv C).Mem d ↔ C.Mem d := by
  constructor
  · rintro ⟨i, hi, h | h⟩
    · exact ⟨C.k - 1 - i, by simp at hi; omega, Or.inr h⟩
    · rw [rv_d, M.α_α] at h
      exact ⟨C.k - 1 - i, by simp at hi; omega, Or.inl h⟩
  · rintro ⟨i, hi, h | h⟩
    · refine ⟨C.k - 1 - i, by simp; omega, Or.inr ?_⟩
      rw [rv_d, M.α_α, show C.k - 1 - (C.k - 1 - i) = i by omega]; exact h
    · refine ⟨C.k - 1 - i, by simp; omega, Or.inl ?_⟩
      rw [rv_d, show C.k - 1 - (C.k - 1 - i) = i by omega]; exact h

lemma rv_verts {v : P} (hv : v ∈ C.verts) : ∃ i < C.k, M.vert ((rv C).d i) = v := by
  obtain ⟨j, hj, rfl⟩ := C.mem_verts.1 hv
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · refine ⟨0, C.pos, ?_⟩
    rw [rv_d, C.vert_α _ (by have := C.pos; omega), show C.k - 1 - 0 + 1 = C.k by
      have := C.pos; omega, Nat.mod_self]
  · refine ⟨C.k - j, by omega, ?_⟩
    rw [rv_d, C.vert_α _ (by omega), show C.k - 1 - (C.k - j) + 1 = j by omega,
      Nat.mod_eq_of_lt hj]

end SCycleRv

/-! ### The disc of a set of faces -/

section Disc

variable (M) in
/-- **The darts of the disc of `Z`**: the darts with a side in `Z`. -/
noncomputable def discDarts (Z : Finset M.Face) : Finset X := by
  classical exact univ.filter fun δ => M.face δ ∈ Z ∨ M.face (M.α δ) ∈ Z

lemma mem_discDarts {Z : Finset M.Face} {δ : X} :
    δ ∈ discDarts M Z ↔ M.face δ ∈ Z ∨ M.face (M.α δ) ∈ Z := by
  classical
  unfold discDarts; simp

lemma discDarts_rev (Z : Finset M.Face) : Stable (revPerm (combOfSep M)) (discDarts M Z) :=
  fun δ hδ => by
    rw [mem_discDarts] at hδ ⊢
    simp only [revPerm_apply, combOfSep_rev, M.α_α]
    tauto

variable (M) in
/-- **The rotation of the disc**: the first return of the rotation of `M` to the darts of the
disc. -/
noncomputable abbrev dσ (Z : Finset M.Face) : Perm X := ret (rotPerm (combOfSep M)) (discDarts M Z)

variable (M) in
/-- **The disc of `Z`**: the darts with a side in `Z`, as a map of `PlanarFlow`. -/
noncomputable def discMap (Z : Finset M.Face) :
    CombMap (SDart (discDarts M Z)) (SVert (dσ M Z) (discDarts M Z))
      (SFace (dσ M Z) (discDarts M Z) (revPerm (combOfSep M))) :=
  subMap (discDarts M Z) (revPerm_isInv (combOfSep M)) (stable_ret _ _) (discDarts_rev Z)

lemma face_φ_pow (n : ℕ) (d : X) : M.face ((M.φ ^ n) d) = M.face d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, M.face_φ, ih]

lemma rotPerm_ofSep (y : X) : rotPerm (combOfSep M) y = M.σ y := combOfSep_rot M y

lemma face_σ (y : X) : M.face (M.σ y) = M.face (M.α y) := by
  have : M.σ y = M.φ (M.α y) := by rw [M.φ_apply, M.α_α]
  rw [this, M.face_φ]

lemma vert_rotPerm_iterate (n : ℕ) (y : X) : M.vert ((rotPerm (combOfSep M))^[n] y) = M.vert y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, ih, rotPerm_ofSep, M.vert_σ]

/-- Inside a face of `Z`, the boundary walk of the disc is that of `M`. -/
lemma dσ_of_face {Z : Finset M.Face} {δ : X} (h : M.face δ ∈ Z) : dσ M Z (M.α δ) = M.φ δ := by
  have hx : M.α δ ∈ discDarts M Z := mem_discDarts.2 (Or.inr (by rwa [M.α_α]))
  have hφ : rotPerm (combOfSep M) (M.α δ) = M.φ δ := by rw [rotPerm_ofSep, M.φ_apply]
  rw [dσ, ret_eq_self_of hx (by rw [hφ]; exact mem_discDarts.2 (Or.inl (by rwa [M.face_φ]))), hφ]

/-- **After a dart of the outer face, the boundary walk of the disc continues with a dart of the
outer face from the head of that dart**: it turns around the head through faces off `Z`. -/
lemma dσ_outer {Z : Finset M.Face} {e : X} (h1 : M.face e ∉ Z) (h2 : M.face (M.α e) ∈ Z) :
    M.face (dσ M Z (M.α e)) ∉ Z ∧ M.face (M.α (dσ M Z (M.α e))) ∈ Z ∧
      M.vert (dσ M Z (M.α e)) = M.vert (M.α e) := by
  set π := rotPerm (combOfSep M)
  have hx : M.α e ∈ discDarts M Z := mem_discDarts.2 (Or.inl h2)
  have key : ∀ j, 1 ≤ j → j ≤ retIdx π (discDarts M Z) (M.α e) →
      M.face (π^[j] (M.α e)) ∉ Z := by
    intro j hj1 hj
    induction j with
    | zero => omega
    | succ j ih =>
      rw [iterate_succ_apply', rotPerm_ofSep, face_σ]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [iterate_zero_apply, M.α_α]; exact h1
      · have hnot := not_mem_of_lt_retIdx (π := π) hx hj0 (by omega)
        rw [mem_discDarts, not_or] at hnot
        exact hnot.2
  have hpos := retIdx_pos (π := π) (A := discDarts M Z) (M.α e)
  have hmem := iterate_retIdx_mem (π := π) hx
  rw [dσ, ret_apply_of_mem hx]
  have hf := key _ hpos le_rfl
  refine ⟨hf, ?_, vert_rotPerm_iterate _ _⟩
  rcases mem_discDarts.1 hmem with h | h
  · exact absurd h hf
  · exact h

variable {C : M.SCycle} {Z : Finset M.Face}

lemma mem_discDarts_of_mem (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) {δ : X}
    (h : C.Mem δ) : δ ∈ discDarts M Z := by
  rw [mem_discDarts]
  have := (hbd δ).not.2 (not_not.2 h)
  tauto

/-- **The disc is plane.** -/
theorem discMap_isPlane (hM : M.IsPlane) (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔
    ¬ C.Mem d) : (discMap M Z).IsPlane := by
  classical
  have hZ := fConn_of_bd hM.connected hbd
  set ι := revPerm (combOfSep M)
  have hι : ∀ y, ι y = M.α y := fun _ => rfl
  -- inside a face of `Z`
  have hstep : ∀ d, M.face d ∈ Z → Conn ι (dσ M Z) d (M.φ d) := fun d hd =>
    (conn_inv d).trans (.single (Or.inl (by rw [hι, dσ_of_face hd])))
  have hsame : ∀ d, M.face d ∈ Z → ∀ n : ℕ, Conn ι (dσ M Z) d ((M.φ ^ n) d) := by
    intro d hd n
    induction n with
    | zero => exact .refl
    | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      exact ih.trans (hstep _ (by rwa [face_φ_pow]))
  have hface : ∀ d d', M.face d ∈ Z → M.face d' = M.face d → Conn ι (dσ M Z) d d' := by
    intro d d' hd he
    obtain ⟨n, hn⟩ := (M.face_eq_face_iff.1 he.symm).exists_nat_pow_eq
    rw [← hn]; exact hsame d hd n
  have hfaces : ∀ d, M.face d ∈ Z → ∀ g, Relation.ReflTransGen (FAdj Z) (M.face d) g →
      ∀ d', M.face d' = g → Conn ι (dσ M Z) d d' := by
    intro d hd g hg
    induction hg with
    | refl => exact fun d' he => hface d d' hd he
    | tail _ hst ih =>
      obtain ⟨-, hg', e, he1, he2⟩ := hst
      intro d' hd'
      refine (ih e he1).trans ((conn_inv e).trans (hface _ d' ?_ (hd'.trans he2.symm)))
      rw [show ι e = M.α e from rfl, he2]; exact hg'
  have hin : ∀ x ∈ discDarts M Z, ∃ x', M.face x' ∈ Z ∧ Conn ι (dσ M Z) x x' ∧
      Conn ι (dσ M Z) x' x := by
    intro x hx
    rcases mem_discDarts.1 hx with h | h
    · exact ⟨x, h, .refl, .refl⟩
    · exact ⟨M.α x, h, conn_inv x, by
        have := conn_inv (ι := ι) (σ := dσ M Z) (M.α x)
        rwa [show ι (M.α x) = x from M.α_α x] at this⟩
  have hx₀ : C.d 0 ∈ discDarts M Z := mem_discDarts_of_mem hbd ⟨0, C.pos, Or.inl rfl⟩
  have hne : Nonempty X := ⟨C.d 0⟩
  refine subMap_isPlane _ _ _ hx₀ (fun x hx y hy => ?_) ?_
  · obtain ⟨x', hx', h1, -⟩ := hin x hx
    obtain ⟨y', hy', -, h2⟩ := hin y hy
    exact h1.trans ((hfaces x' hx' _ (hZ _ hx' _ hy') y' rfl).trans h2)
  · exact gap_ret_eq_zero (revPerm_isInv _) (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
      (subset_univ _) (discDarts_rev Z)
      (gap_rot_eq_zero (combOfSep_isPlane hM) (combOfSep_rotTrans M) (combOfSep_faceTrans M) hne).2

theorem discMap_rotTrans : (discMap M Z).RotTrans := subMap_rotTrans _ _ _

theorem discMap_faceTrans : (discMap M Z).FaceTrans := subMap_faceTrans _ _ _

/-- Two darts of the disc have the same tail if and only if they have the same vertex in `M`. -/
lemma discMap_tail_eq_iff {x y : SDart (discDarts M Z)} :
    (discMap M Z).tail x = (discMap M Z).tail y ↔ M.vert x.1 = M.vert y.1 := by
  rw [discMap, subMap_tail, subMap_tail, sVert_eq_iff, sameCycle_ret x.2 y.2,
    sameCycle_rotPerm (combOfSep_rotTrans M)]
  rfl

/-! ### The cycle is a face of the disc -/

variable (Z) in
/-- A dart of the outer face of the disc: its face is off `Z`, that of its reverse in `Z`. -/
def Out (δ : X) : Prop := M.face δ ∉ Z ∧ M.face (M.α δ) ∈ Z

lemma succ_mod_inj {k i j : ℕ} (hi : i < k) (hj : j < k) (h : (i + 1) % k = (j + 1) % k) :
    i = j := by
  rcases Nat.lt_or_ge (i + 1) k with h1 | h1 <;> rcases Nat.lt_or_ge (j + 1) k with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_of_lt h1, show j + 1 = k by omega, Nat.mod_self] at h; omega
  · rw [Nat.mod_eq_of_lt h2, show i + 1 = k by omega, Nat.mod_self] at h; omega
  · omega

lemma out_step (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) {i : ℕ}
    (hi : i < C.k) (h : Out Z (C.d i)) :
    dσ M Z (M.α (C.d i)) = C.d ((i + 1) % C.k) ∧ Out Z (C.d ((i + 1) % C.k)) := by
  obtain ⟨h1, h2, h3⟩ := dσ_outer h.1 h.2
  have hmem : C.Mem (dσ M Z (M.α (C.d i))) := by
    by_contra hn
    exact h1 (((hbd _).2 hn).2 h2)
  rw [C.vert_α _ hi] at h3
  obtain ⟨j, hj, he | he⟩ := hmem
  · have := C.inj _ hj _ (Nat.mod_lt _ C.pos) (he ▸ h3)
    subst this
    exact ⟨he, he ▸ ⟨h1, h2⟩⟩
  · rw [he, C.vert_α _ hj] at h3
    have := succ_mod_inj hj hi (C.inj _ (Nat.mod_lt _ C.pos) _ (Nat.mod_lt _ C.pos) h3)
    subst this
    exact absurd h.2 (he ▸ h1)

lemma out_all (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) {i₀ : ℕ}
    (hi₀ : i₀ < C.k) (h : Out Z (C.d i₀)) : ∀ i < C.k, Out Z (C.d i) := by
  have key : ∀ t, Out Z (C.d ((i₀ + t) % C.k)) := by
    intro t
    induction t with
    | zero => rwa [Nat.add_zero, Nat.mod_eq_of_lt hi₀]
    | succ t ih =>
      have := (out_step hbd (Nat.mod_lt _ C.pos) ih).2
      rwa [Nat.mod_add_mod, add_assoc] at this
  intro i hi
  have := key (i + C.k - i₀)
  rwa [show i₀ + (i + C.k - i₀) = i + C.k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi] at this

/-- **The cycle is the boundary walk of a face of the disc**, when its darts are on the outer
face. -/
theorem faceCycle_of_out (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) {i₀ : ℕ} (hi₀ : i₀ < C.k)
    (h : Out Z (C.d i₀)) :
    ∃ g : ℕ → SDart (discDarts M Z), MSSP.FaceCycle (discMap M Z) C.k g ∧
      ∀ i < C.k, (g i).1 = C.d i := by
  have hall := out_all hbd hi₀ h
  have hmem : ∀ i, C.d (i % C.k) ∈ discDarts M Z := fun i =>
    mem_discDarts_of_mem hbd ⟨_, Nat.mod_lt _ C.pos, Or.inl rfl⟩
  set g : ℕ → SDart (discDarts M Z) := fun i => ⟨C.d (i % C.k), hmem i⟩ with hg
  have hgv : ∀ i < C.k, (g i).1 = C.d i := fun i hi => by simp [hg, Nat.mod_eq_of_lt hi]
  have hnext : ∀ i < C.k, (discMap M Z).next (g i) = g ((i + 1) % C.k) := by
    intro i hi
    apply Subtype.ext
    simp only [discMap, subMap_next]
    rw [hgv i hi, show (revPerm (combOfSep M)) (C.d i) = M.α (C.d i) from rfl,
      (out_step hbd hi (hall i hi)).1, hgv _ (Nat.mod_lt _ C.pos)]
  have h2 : 2 ≤ C.k := by
    by_contra hk
    have hk1 : C.k = 1 := by have := C.pos; omega
    have := C.vert_α 0 C.pos
    rw [hk1, Nat.mod_self] at this
    exact hl _ this
  refine ⟨g, ⟨h2, ?_, hnext, ?_⟩, hgv⟩
  · intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [← ih (by omega), ← Nat.mod_eq_of_lt hi, ← hnext i (by omega), (discMap M Z).face_next]
  · intro i hi j hj e
    rw [discMap_tail_eq_iff, hgv i hi, hgv j hj] at e
    exact C.inj _ hi _ hj e

/-- **The cycle `C` is the boundary walk of a face of the disc of `Z`**, through all the vertices
of `C`. -/
theorem exists_disc_faceCycle (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) :
    ∃ g : ℕ → SDart (discDarts M Z), MSSP.FaceCycle (discMap M Z) C.k g ∧
      ∀ v ∈ C.verts, ∃ i < C.k, M.vert (g i).1 = v := by
  by_cases h : Out Z (C.d 0)
  · obtain ⟨g, hg, hgv⟩ := faceCycle_of_out hl hbd C.pos h
    refine ⟨g, hg, fun v hv => ?_⟩
    obtain ⟨i, hi, rfl⟩ := C.mem_verts.1 hv
    exact ⟨i, hi, by rw [hgv i hi]⟩
  · have hm : C.Mem (C.d 0) := ⟨0, C.pos, Or.inl rfl⟩
    have hb := (hbd (C.d 0)).not.2 (not_not.2 hm)
    have hout : Out Z ((SCycleRv.rv C).d (C.k - 1)) := by
      rw [SCycleRv.rv_d, show C.k - 1 - (C.k - 1) = 0 by omega, Out, M.α_α]
      unfold Out at h
      tauto
    have hbd' : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ (SCycleRv.rv C).Mem d :=
      fun d => by rw [SCycleRv.rv_mem]; exact hbd d
    obtain ⟨g, hg, hgv⟩ := faceCycle_of_out hl hbd' (by simp; have := C.pos; omega) hout
    refine ⟨g, hg, fun v hv => ?_⟩
    obtain ⟨i, hi, e⟩ := SCycleRv.rv_verts C hv
    exact ⟨i, hi, by rw [hgv i hi]; exact e⟩

end Disc

end NegSSSP

end PlanarFlow
