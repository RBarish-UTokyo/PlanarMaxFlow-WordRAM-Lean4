module

public import PlanarFlow.Klein.Bridge

/-!
# Copies of the sources inside a face

Klein's algorithm, as verified here (`PlanarFlow.MSSP.Hyp`, `PlanarFlow.Klein.SameReach`), asks
that no dart of the piece enter a root (`Hyp.noIn`) and that all the roots reach the same
vertices. For multiple-source shortest paths from the vertices `t i = tail (g i)` of a face cycle
`g` of a plane map `M` in a piece `S` with nonnegative lengths `ℓ`, neither need hold. This file
builds a plane map `srcMap hf` in which both hold and from whose roots the distances in the
piece of `M` from the vertices `t i` are read off.

Inside the face of `g`, two rings of `k` new vertices are drawn: the roots `r i` (the new face
cycle, `srcG hf`) and, between them and the face, the vertices `s i`. For every `i` there are
eight new darts (`SrcKind`): the ring `r i → r (i + 1)`, the darts `r i → s i`, `s i → t i` and
`s i → s (i + 1)`, and their reverses. The face of `g` is cut into the face of the ring, `k`
quadrilaterals `r i, s i, s (i + 1), r (i + 1)` and `k` quadrilaterals
`s i, t i, t (i + 1), s (i + 1)`.

The piece `srcPiece S` consists of the copies of the darts of `S`, the darts `r i → s i` and
`s i → t i` of length `0`, and the darts `s i → s (i + 1)` of length
`W = 1 + ∑_{d ∈ S} ℓ d` (`srcW`), more than any distance in the piece of `M`.

* `srcMap_isPlane`, `srcMap_rotTrans`, `srcMap_faceCycle`: the map is plane with transitive
  rotations, and the ring is a face cycle through the roots.
* `srcMap_hypNN`, `srcMap_sameReach`: **the hypotheses of Klein's algorithm hold** (`HypNN`: no
  dart of the piece enters a root, whose only dart in the piece leaves it for `s i`; `SameReach`:
  every root reaches every `s j` by the ring of the `s j`).
* `odist_src`: **a walk from `r i` of length less than `W` is a walk from `t i` in the piece of
  `M`**, preceded by `r i → s i → t i`; so the distances from `r i` less than `W` at the copies
  of the vertices are the distances from `t i` in the piece of `M`.
* `srcAns`, `srcAns_eq`: the answers of Klein's trip on `srcMap hf` (`kleinNN`), cut off at `W`,
  **are the distances in the piece of `M` from the vertices of the face**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP Function

/-- The kinds of the darts added for every vertex of the face: the ring of the roots
(`ring : r i → r (i + 1)`), the darts `down : r i → s i`, `out : s i → t i`,
`side : s i → s (i + 1)`, and their reverses. -/
inductive SrcKind
  | ring | ringR | down | up | out | outR | side | sideR
  deriving DecidableEq

instance : Fintype SrcKind :=
  ⟨{.ring, .ringR, .down, .up, .out, .outR, .side, .sideR}, fun x => by cases x <;> simp⟩

lemma card_srcKind : Fintype.card SrcKind = 8 := rfl

/-- The next index around the face. -/
def fsucc {k : ℕ} (i : Fin k) : Fin k := finRotate k i

/-- The previous index around the face. -/
def fpred {k : ℕ} (i : Fin k) : Fin k := (finRotate k).symm i

@[simp] lemma fsucc_fpred {k : ℕ} (i : Fin k) : fsucc (fpred i) = i :=
  Equiv.apply_symm_apply _ i

@[simp] lemma fpred_fsucc {k : ℕ} (i : Fin k) : fpred (fsucc i) = i :=
  Equiv.symm_apply_apply _ i

lemma val_fsucc {k : ℕ} (i : Fin k) : (fsucc i : ℕ) = (i + 1) % k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := i.2; omega⟩
  unfold fsucc
  rw [coe_finRotate]
  split_ifs with h
  · subst h; simp
  · rw [Nat.mod_eq_of_lt (by have := Fin.val_lt_last h; omega)]

/-- The darts of the map with the sources copied: the darts of `M` and eight darts for every
vertex of the face. -/
abbrev SrcD (D : Type*) (k : ℕ) := D ⊕ (Fin k × SrcKind)

/-- The vertices: those of `M`, the roots `(i, false)` and the vertices `(i, true)` between the
roots and the face. -/
abbrev SrcV (V : Type*) (k : ℕ) := V ⊕ (Fin k × Bool)

/-- The faces: those of `M` (the face of `g` becomes the face of the ring), and two
quadrilaterals for every vertex of the face, between the roots and the middle ring (`true`) and
between the middle ring and the face (`false`). -/
abbrev SrcF (F : Type*) (k : ℕ) := F ⊕ (Fin k × Bool)

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D}

/-! ### The darts of the face -/

section Idx

variable (k g) in
open Classical in
/-- The index of a dart of the face cycle, `none` for the other darts. -/
noncomputable def gIdx (d : D) : Option (Fin k) :=
  if h : ∃ i : Fin k, g i = d then some h.choose else none

lemma gIdx_some {d : D} {i : Fin k} (h : gIdx k g d = some i) : g i = d := by
  unfold gIdx at h
  split_ifs at h with h'
  rw [← Option.some_inj.1 h]
  exact h'.choose_spec

lemma gIdx_g (hf : FaceCycle M k g) (i : Fin k) : gIdx k g (g i) = some i := by
  have h : ∃ j : Fin k, g j = g i := ⟨i, rfl⟩
  unfold gIdx
  simp only [h, ↓reduceDIte]
  exact congrArg some (Fin.ext (hf.inj _ h.choose.2 _ i.2 (congrArg M.tail h.choose_spec)))

lemma gIdx_none {d : D} (h : ∀ i : Fin k, g i ≠ d) : gIdx k g d = none := by
  unfold gIdx
  have h' : ¬ ∃ i : Fin k, g i = d := fun ⟨i, hi⟩ => h i hi
  simp only [h', ↓reduceDIte]

lemma next_g (hf : FaceCycle M k g) (i : Fin k) : M.next (g i) = g (fsucc i) := by
  rw [hf.next i i.2, val_fsucc]

lemma gIdx_next (hf : FaceCycle M k g) {d : D} (h : gIdx k g d = none) :
    gIdx k g (M.next d) = none := by
  refine gIdx_none fun i hi => ?_
  have e : M.next (g (fpred i)) = M.next d := by
    rw [next_g hf, fsucc_fpred, hi]
  rw [← M.next_injective e, gIdx_g hf] at h
  exact absurd h (by simp)

end Idx

/-! ### The map -/

section Map

variable (M k g)

/-- The reverse of a dart. -/
def srcRev : SrcD D k → SrcD D k
  | .inl d => .inl (M.rev d)
  | .inr (i, .ring) => .inr (i, .ringR)
  | .inr (i, .ringR) => .inr (i, .ring)
  | .inr (i, .down) => .inr (i, .up)
  | .inr (i, .up) => .inr (i, .down)
  | .inr (i, .out) => .inr (i, .outR)
  | .inr (i, .outR) => .inr (i, .out)
  | .inr (i, .side) => .inr (i, .sideR)
  | .inr (i, .sideR) => .inr (i, .side)

/-- The tail of a dart. -/
def srcTail : SrcD D k → SrcV V k
  | .inl d => .inl (M.tail d)
  | .inr (i, .ring) => .inr (i, false)
  | .inr (i, .ringR) => .inr (fsucc i, false)
  | .inr (i, .down) => .inr (i, false)
  | .inr (i, .up) => .inr (i, true)
  | .inr (i, .out) => .inr (i, true)
  | .inr (i, .outR) => .inl (M.tail (g i))
  | .inr (i, .side) => .inr (i, true)
  | .inr (i, .sideR) => .inr (fsucc i, true)

/-- The next dart along the boundary walk of a face. -/
noncomputable def srcNext : SrcD D k → SrcD D k
  | .inl d => (gIdx k g d).elim (.inl (M.next d)) fun i => .inr (fsucc i, .outR)
  | .inr (i, .outR) => .inr (fpred i, .sideR)
  | .inr (i, .sideR) => .inr (i, .out)
  | .inr (i, .out) => .inl (g i)
  | .inr (i, .side) => .inr (fsucc i, .up)
  | .inr (i, .up) => .inr (fpred i, .ringR)
  | .inr (i, .ringR) => .inr (i, .down)
  | .inr (i, .down) => .inr (i, .side)
  | .inr (i, .ring) => .inr (fsucc i, .ring)

/-- The face of a dart. -/
noncomputable def srcFace : SrcD D k → SrcF F k
  | .inl d => (gIdx k g d).elim (.inl (M.face d)) fun i => .inr (i, false)
  | .inr (i, .out) => .inr (i, false)
  | .inr (i, .sideR) => .inr (i, false)
  | .inr (i, .outR) => .inr (fpred i, false)
  | .inr (i, .side) => .inr (i, true)
  | .inr (i, .ringR) => .inr (i, true)
  | .inr (i, .down) => .inr (i, true)
  | .inr (i, .up) => .inr (fpred i, true)
  | .inr (_, .ring) => .inl (M.face (g 0))

/-- The inverse of `next` on `M`. -/
noncomputable def nextInv : D ≃ D :=
  (Equiv.ofBijective M.next M.next_injective.bijective_of_finite).symm

/-- The previous dart along the boundary walk of a face. -/
noncomputable def srcPrev : SrcD D k → SrcD D k
  | .inl d => (gIdx k g d).elim (.inl (nextInv M d)) fun i => .inr (i, .out)
  | .inr (i, .outR) => .inl (g (fpred i))
  | .inr (i, .sideR) => .inr (fsucc i, .outR)
  | .inr (i, .out) => .inr (i, .sideR)
  | .inr (i, .side) => .inr (i, .down)
  | .inr (i, .up) => .inr (fpred i, .side)
  | .inr (i, .ringR) => .inr (fsucc i, .up)
  | .inr (i, .down) => .inr (i, .ringR)
  | .inr (i, .ring) => .inr (fpred i, .ring)

variable {M k g}

lemma nextInv_next (d : D) : nextInv M (M.next d) = d :=
  (Equiv.ofBijective M.next M.next_injective.bijective_of_finite).symm_apply_apply d

lemma srcPrev_next (hf : FaceCycle M k g) (d : SrcD D k) :
    srcPrev M k g (srcNext M k g d) = d := by
  rcases d with d | ⟨i, _ | _ | _ | _ | _ | _ | _ | _⟩
  · rcases h : gIdx k g d with _ | i
    · simp [srcNext, srcPrev, h, gIdx_next hf h, nextInv_next]
    · simp [srcNext, srcPrev, h, gIdx_some h]
  · simp [srcNext, srcPrev]
  · simp [srcNext, srcPrev]
  · simp [srcNext, srcPrev]
  · simp [srcNext, srcPrev]
  · simp [srcNext, srcPrev, gIdx_g hf]
  all_goals simp [srcNext, srcPrev]

lemma srcTail_next (hf : FaceCycle M k g) (d : SrcD D k) :
    srcTail M k g (srcNext M k g d) = srcTail M k g (srcRev M k d) := by
  rcases d with d | ⟨i, _ | _ | _ | _ | _ | _ | _ | _⟩
  · rcases h : gIdx k g d with _ | i
    · simp [srcNext, srcTail, srcRev, h, M.tail_next]
    · obtain rfl := gIdx_some h
      simp only [srcNext, gIdx_g hf, Option.elim, srcTail, srcRev]
      rw [← next_g hf, M.tail_next]
  all_goals simp [srcNext, srcTail, srcRev]

lemma srcFace_next (hf : FaceCycle M k g) (d : SrcD D k) :
    srcFace M k g (srcNext M k g d) = srcFace M k g d := by
  rcases d with d | ⟨i, _ | _ | _ | _ | _ | _ | _ | _⟩
  · rcases h : gIdx k g d with _ | i
    · simp [srcNext, srcFace, h, gIdx_next hf h, M.face_next]
    · simp [srcNext, srcFace, h]
  · simp [srcNext, srcFace]
  · simp [srcNext, srcFace]
  · simp [srcNext, srcFace]
  · simp [srcNext, srcFace]
  · simp [srcNext, srcFace, gIdx_g hf]
  all_goals simp [srcNext, srcFace]

/-- **The map with the sources copied inside the face of `g`.** -/
noncomputable def srcMap (hf : FaceCycle M k g) : CombMap (SrcD D k) (SrcV V k) (SrcF F k) where
  rev := srcRev M k
  rev_rev d := by rcases d with d | ⟨i, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [srcRev, M.rev_rev]
  rev_ne d := by rcases d with d | ⟨i, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [srcRev, M.rev_ne]
  tail := srcTail M k g
  face := srcFace M k g
  next := srcNext M k g
  next_injective := (LeftInverse.injective (srcPrev_next hf))
  face_next := srcFace_next hf
  tail_next := srcTail_next hf

end Map

/-! ### The ring of the roots -/

section Ring

lemma k_pos (hf : FaceCycle M k g) : 0 < k := by have := hf.two_le; omega

/-- **The ring of the roots**: the face cycle of `srcMap hf`. -/
def srcG (hf : FaceCycle M k g) (n : ℕ) : SrcD D k :=
  .inr (⟨n % k, Nat.mod_lt _ (k_pos hf)⟩, .ring)

/-- **The ring is a face cycle through the roots.** -/
theorem srcMap_faceCycle (hf : FaceCycle M k g) : FaceCycle (srcMap hf) k (srcG hf) where
  two_le := hf.two_le
  face _ _ := rfl
  next i _ := by
    show srcNext M k g (.inr (_, .ring)) = .inr (_, .ring)
    simp only [srcNext]
    congr 2
    ext
    simp only [val_fsucc]
    rw [Nat.mod_mod, Nat.mod_add_mod]
  inj i hi j hj h := by
    simp only [srcMap, srcTail, srcG, Sum.inr.injEq, Prod.mk.injEq, Fin.mk.injEq,
      and_true] at h
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h

lemma srcTail_srcG (hf : FaceCycle M k g) {j : ℕ} (hj : j < k) :
    (srcMap hf).tail (srcG hf j) = .inr (⟨j, hj⟩, false) := by
  simp only [srcMap, srcTail, srcG, Nat.mod_eq_of_lt hj]

end Ring

/-! ### Planarity -/

section Plane

open Relation BKMNW

variable (hf : FaceCycle M k g)

lemma srcMap_adj_symm (a b : SrcV V k) (h : (srcMap hf).Adj a b) : (srcMap hf).Adj b a := by
  obtain ⟨d, rfl, rfl⟩ := h
  exact ⟨(srcMap hf).rev d, rfl, (srcMap hf).head_rev d⟩

lemma srcMap_dualAdj_symm (a b : SrcF F k) (h : (srcMap hf).DualAdj a b) :
    (srcMap hf).DualAdj b a := by
  obtain ⟨d, rfl, rfl⟩ := h
  exact ⟨(srcMap hf).rev d, rfl, by rw [(srcMap hf).rev_rev]⟩

lemma srcMap_conn (hM : M.IsPlane) (a b : SrcV V k) : ReflTransGen (srcMap hf).Adj a b := by
  have lift : ∀ x y, ReflTransGen M.Adj x y →
      ReflTransGen (srcMap hf).Adj (.inl x) (.inl y) := by
    intro x y h
    induction h with
    | refl => exact .refl
    | tail _ hst ih =>
      obtain ⟨d, rfl, rfl⟩ := hst
      exact ih.tail ⟨.inl d, rfl, rfl⟩
  have hall : ∀ a, ReflTransGen (srcMap hf).Adj a (.inl (M.tail (g 0))) := by
    rintro (x | ⟨i, _ | _⟩)
    · exact lift _ _ (hM.conn _ _)
    · exact .head ⟨.inr (i, .down), rfl, rfl⟩
        (.head ⟨.inr (i, .out), rfl, rfl⟩ (lift _ _ (hM.conn _ _)))
    · exact .head ⟨.inr (i, .out), rfl, rfl⟩ (lift _ _ (hM.conn _ _))
  exact (hall a).trans (reflTransGen_symm' (srcMap_adj_symm hf) (hall b))

lemma srcMap_dualConn (hM : M.IsPlane) (a b : SrcF F k) :
    ReflTransGen (srcMap hf).DualAdj a b := by
  have hI : ∀ i, ReflTransGen (srcMap hf).DualAdj (.inr (i, true)) (.inl (M.face (g 0))) :=
    fun i => .single ⟨.inr (i, .ringR), rfl, rfl⟩
  have hO : ∀ i, ReflTransGen (srcMap hf).DualAdj (.inr (i, false)) (.inl (M.face (g 0))) :=
    fun i => .head ⟨.inr (i, .sideR), rfl, rfl⟩ (hI i)
  have hface : ∀ e : D, ReflTransGen (srcMap hf).DualAdj (.inl (M.face e)) (.inl (M.face (g 0))) →
      ReflTransGen (srcMap hf).DualAdj ((srcMap hf).face (.inl e)) (.inl (M.face (g 0))) := by
    intro e h
    rcases he : gIdx k g e with _ | i
    · have : (srcMap hf).face (.inl e) = .inl (M.face e) := by simp [srcMap, srcFace, he]
      rw [this]; exact h
    · have : (srcMap hf).face (.inl e) = .inr (i, false) := by simp [srcMap, srcFace, he]
      rw [this]; exact hO i
  have key : ∀ x, ReflTransGen M.DualAdj x (M.face (g 0)) →
      ReflTransGen (srcMap hf).DualAdj (.inl x) (.inl (M.face (g 0))) := by
    intro x hx
    induction hx using Relation.ReflTransGen.head_induction_on with
    | refl => exact .refl
    | head h _ ih =>
      obtain ⟨d, rfl, rfl⟩ := h
      rcases hd : gIdx k g d with _ | i
      · have e1 : (srcMap hf).face (.inl d) = .inl (M.face d) := by simp [srcMap, srcFace, hd]
        exact .head ⟨.inl d, e1, rfl⟩ (hface (M.rev d) ih)
      · rw [← gIdx_some hd, hf.face i i.2]
  have hall : ∀ a, ReflTransGen (srcMap hf).DualAdj a (.inl (M.face (g 0))) := by
    rintro (x | ⟨i, _ | _⟩)
    · exact key x (hM.dualConn _ _)
    · exact hO i
    · exact hI i
  exact (hall a).trans (reflTransGen_symm' (srcMap_dualAdj_symm hf) (hall b))

/-- **The map with the sources copied is plane.** -/
theorem srcMap_isPlane (hM : M.IsPlane) : (srcMap hf).IsPlane where
  nonempty := ⟨.inl (M.tail (g 0))⟩
  conn := srcMap_conn hf hM
  dualConn := srcMap_dualConn hf hM
  euler := by
    have e := hM.euler
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      card_srcKind]
    omega

end Plane

/-! ### Transitive rotations -/

section Rot

open BKMNW

variable (hf : FaceCycle M k g)

lemma srcMap_rot (d : SrcD D k) : (srcMap hf).rot d = srcNext M k g (srcRev M k d) := rfl

lemma rot_inl (e : D) : ItReach (srcMap hf).rot (.inl e) (.inl (M.rot e)) := by
  rcases h : gIdx k g (M.rev e) with _ | j
  · refine .of_eq ?_
    show srcNext M k g (srcRev M k (.inl e)) = .inl (M.next (M.rev e))
    simp [srcRev, srcNext, h]
  · have hj := gIdx_some h
    refine ⟨2, ?_⟩
    show srcNext M k g (srcRev M k (srcNext M k g (srcRev M k (.inl e)))) =
      .inl (M.next (M.rev e))
    simp only [srcRev, srcNext, h, Option.elim]
    rw [← hj, next_g hf]

lemma rot_iter (n : ℕ) (e : D) : ItReach (srcMap hf).rot (.inl e) (.inl (M.rot^[n] e)) := by
  induction n generalizing e with
  | zero => exact .rfl'
  | succ n ih => rw [iterate_succ_apply]; exact (rot_inl hf e).trans (ih _)

lemma rot_at_old {d : SrcD D k} {v : V} (h : (srcMap hf).tail d = .inl v) :
    ∃ x y : D, M.tail x = v ∧ M.tail y = v ∧ ItReach (srcMap hf).rot (.inl x) d ∧
      ItReach (srcMap hf).rot d (.inl y) := by
  rcases d with e | ⟨i, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [srcMap, srcTail] at h
  · exact ⟨e, e, h, h, .rfl', .rfl'⟩
  · subst h
    refine ⟨M.rev (g (fpred i)), g i, ?_, rfl, .of_eq ?_, .of_eq ?_⟩
    · rw [← M.tail_next, next_g hf, fsucc_fpred]
    · simp [srcMap_rot, srcRev, srcNext, M.rev_rev, gIdx_g hf]
    · simp [srcMap_rot, srcRev, srcNext]

lemma rot_at_root {d : SrcD D k} {i : Fin k} (h : (srcMap hf).tail d = .inr (i, false)) :
    ItReach (srcMap hf).rot d (.inr (i, .ring)) ∧
      ItReach (srcMap hf).rot (.inr (i, .ring)) d := by
  have s1 : ∀ j : Fin k, (srcMap hf).rot (.inr (j, .ring)) = .inr (j, .down) := fun j => rfl
  have s2 : ∀ j : Fin k, (srcMap hf).rot (.inr (j, .down)) = .inr (fpred j, .ringR) :=
    fun j => rfl
  have s3 : ∀ j : Fin k, (srcMap hf).rot (.inr (j, .ringR)) = .inr (fsucc j, .ring) :=
    fun j => rfl
  rcases d with e | ⟨j, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [srcMap, srcTail] at h
  · subst h; exact ⟨.rfl', .rfl'⟩
  · subst h
    exact ⟨.of_eq (s3 j), (ItReach.of_eq (s1 _)).trans (.of_eq (by rw [s2, fpred_fsucc]))⟩
  · subst h
    exact ⟨(ItReach.of_eq (s2 j)).trans (.of_eq (by rw [s3, fsucc_fpred])), .of_eq (s1 j)⟩

lemma rot_at_mid {d : SrcD D k} {i : Fin k} (h : (srcMap hf).tail d = .inr (i, true)) :
    ItReach (srcMap hf).rot d (.inr (i, .up)) ∧ ItReach (srcMap hf).rot (.inr (i, .up)) d := by
  have s1 : ∀ j : Fin k, (srcMap hf).rot (.inr (j, .up)) = .inr (j, .side) := fun j => rfl
  have s2 : ∀ j : Fin k, (srcMap hf).rot (.inr (j, .side)) = .inr (j, .out) := fun j => rfl
  have s3 : ∀ j : Fin k, (srcMap hf).rot (.inr (j, .out)) = .inr (fpred j, .sideR) :=
    fun j => rfl
  have s4 : ∀ j : Fin k, (srcMap hf).rot (.inr (j, .sideR)) = .inr (fsucc j, .up) :=
    fun j => rfl
  rcases d with e | ⟨j, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [srcMap, srcTail] at h
  · subst h; exact ⟨.rfl', .rfl'⟩
  · subst h
    exact ⟨(ItReach.of_eq (s3 j)).trans (.of_eq (by rw [s4, fsucc_fpred])),
      (ItReach.of_eq (s1 j)).trans (.of_eq (s2 j))⟩
  · subst h
    exact ⟨(ItReach.of_eq (s2 j)).trans ((ItReach.of_eq (s3 j)).trans
      (.of_eq (by rw [s4, fsucc_fpred]))), .of_eq (s1 j)⟩
  · subst h
    exact ⟨.of_eq (s4 j), (ItReach.of_eq (s1 _)).trans ((ItReach.of_eq (s2 _)).trans
      (.of_eq (by rw [s3, fpred_fsucc])))⟩

/-- **The map with the sources copied has transitive rotations.** -/
theorem srcMap_rotTrans (hrot : M.RotTrans) : (srcMap hf).RotTrans := by
  intro d d' h
  rcases hd : (srcMap hf).tail d with v | ⟨i, _ | _⟩
  · obtain ⟨x, y, hx, hy, -, h1⟩ := rot_at_old hf hd
    obtain ⟨x', y', hx', hy', h2, -⟩ := rot_at_old hf (h.symm.trans hd)
    obtain ⟨n, hn⟩ := hrot y x' (hy.trans hx'.symm)
    have := rot_iter hf n y
    rw [hn] at this
    exact h1.trans (this.trans h2)
  · exact (rot_at_root hf hd).1.trans (rot_at_root hf (h.symm.trans hd)).2
  · exact (rot_at_mid hf hd).1.trans (rot_at_mid hf (h.symm.trans hd)).2

end Rot

/-! ### The piece and the hypotheses of Klein's algorithm -/

section Piece

variable (k) in
/-- The darts of the piece: the copies of the darts of `S` and the darts `down : r i → s i`,
`out : s i → t i` and `side : s i → s (i + 1)`. -/
def inSrc (S : Finset D) : SrcD D k → Bool
  | .inl d => decide (d ∈ S)
  | .inr (_, .down) => true
  | .inr (_, .out) => true
  | .inr (_, .side) => true
  | _ => false

variable (k) in
/-- **The piece of the map with the sources copied.** -/
def srcPiece (S : Finset D) : Finset (SrcD D k) := univ.filter fun d => inSrc k S d = true

lemma mem_srcPiece {S : Finset D} {d : SrcD D k} : d ∈ srcPiece k S ↔ inSrc k S d = true := by
  simp [srcPiece]

/-- **The lengths**: `ℓ` on the copies, `W` on the darts `side`, `0` elsewhere. -/
def srcLen (ℓ : D → ℤ) (W : ℤ) : SrcD D k → ℤ
  | .inl d => ℓ d
  | .inr (_, .side) => W
  | _ => 0

/-- The length of the darts `side`: more than the total length of the piece. -/
def srcW (S : Finset D) (ℓ : D → ℤ) : ℤ := 1 + ∑ d ∈ S, ℓ d

lemma srcW_pos {S : Finset D} {ℓ : D → ℤ} (hnn : ∀ d ∈ S, 0 ≤ ℓ d) : 0 < srcW S ℓ := by
  have := sum_nonneg hnn
  unfold srcW; omega

variable (hf : FaceCycle M k g) {S : Finset D}

/-- **The map with the sources copied meets the hypotheses of Klein's algorithm** for
nonnegative lengths (`HypNN`): it is plane with transitive rotations, the ring is a face cycle,
and no dart of the piece enters a root. -/
theorem srcMap_hypNN (hM : M.IsPlane) (hrot : M.RotTrans) {ℓ : D → ℤ}
    (hnn : ∀ d ∈ S, 0 ≤ ℓ d) {W : ℤ} (hW : 0 ≤ W) :
    HypNN (srcMap hf) k (srcG hf) (srcPiece k S) (srcLen ℓ W) where
  plane := srcMap_isPlane hf hM
  rot := srcMap_rotTrans hf hrot
  face := srcMap_faceCycle hf
  nonneg d hd := by
    rw [mem_srcPiece] at hd
    rcases d with e | ⟨i, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [inSrc] at hd <;>
      simp [srcLen, hW]
    exact hnn e hd
  noIn d hd := by
    rintro ⟨i, hi, h⟩
    rw [srcTail_srcG hf hi] at h
    change Sum.inr _ = srcTail M k g (srcRev M k d) at h
    rw [mem_srcPiece] at hd
    rcases d with e | ⟨j, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [inSrc] at hd <;>
      simp [srcTail, srcRev] at h

/-- The only dart of the piece leaving a root is `down`. -/
lemma src_root {ℓ' : SrcD D k → ℤ} {i : Fin k} (a : {d // d ∈ srcPiece k S})
    (h : (pieceGraph (srcMap hf) (srcPiece k S) ℓ').src a = .inr (i, false)) :
    a.1 = .inr (i, .down) := by
  obtain ⟨d, hd⟩ := a
  rw [mem_srcPiece] at hd
  rcases d with e | ⟨j, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [inSrc] at hd <;>
    simp [pieceGraph, srcMap, srcTail] at h ⊢
  exact h

/-- A vertex reached from a root other than the root is reached from the next vertex `s i`. -/
lemma reach_of_root {ℓ' : SrcD D k → ℤ} {i : Fin k} {v : SrcV V k}
    (h : Reach (pieceGraph (srcMap hf) (srcPiece k S) ℓ') (.inr (i, false)) v)
    (hv : v ≠ .inr (i, false)) :
    Reach (pieceGraph (srcMap hf) (srcPiece k S) ℓ') (.inr (i, true)) v := by
  obtain ⟨l, hl⟩ := h
  rcases l with _ | ⟨a, l⟩
  · exact absurd (LWalk.nil_iff.1 hl).symm hv
  obtain ⟨hs, hl'⟩ := LWalk.cons_iff.1 hl
  have ha := src_root hf a hs
  refine ⟨l, ?_⟩
  have e : (pieceGraph (srcMap hf) (srcPiece k S) ℓ').dst a = .inr (i, true) := by
    simp [pieceGraph, ha, srcMap, CombMap.head, srcRev, srcTail]
  rwa [e] at hl'

/-- The middle ring: every `s i` reaches every `s j`. -/
lemma reach_mid {ℓ' : SrcD D k → ℤ} (i : Fin k) (n : ℕ) :
    Reach (pieceGraph (srcMap hf) (srcPiece k S) ℓ') (.inr (i, true))
      (.inr (⟨(i + n) % k, Nat.mod_lt _ (k_pos hf)⟩, true)) := by
  induction n with
  | zero =>
    have : (⟨(i + 0) % k, Nat.mod_lt _ (k_pos hf)⟩ : Fin k) = i := by
      ext; simp [Nat.mod_eq_of_lt i.2]
    rw [this]; exact Reach.refl _
  | succ n ih =>
    set a : {d // d ∈ srcPiece k S} :=
      ⟨.inr (⟨(i + n) % k, Nat.mod_lt _ (k_pos hf)⟩, .side), by simp [mem_srcPiece, inSrc]⟩
    have hd : (pieceGraph (srcMap hf) (srcPiece k S) ℓ').dst a =
        .inr (⟨(i + (n + 1)) % k, Nat.mod_lt _ (k_pos hf)⟩, true) := by
      simp only [pieceGraph, a, srcMap, CombMap.head, srcRev, srcTail, Sum.inr.injEq,
        Prod.mk.injEq, and_true]
      ext
      simp only [val_fsucc]
      rw [Nat.mod_add_mod, add_assoc]
    rw [← hd]
    exact ih.arc

lemma reach_mid' {ℓ' : SrcD D k → ℤ} (i j : Fin k) :
    Reach (pieceGraph (srcMap hf) (srcPiece k S) ℓ') (.inr (i, true)) (.inr (j, true)) := by
  have h := reach_mid hf (S := S) (ℓ' := ℓ') i (j + k - i)
  have e : (⟨(i + (j + k - i)) % k, Nat.mod_lt _ (k_pos hf)⟩ : Fin k) = j := by
    ext
    simp only
    rw [show (i : ℕ) + (j + k - i) = j + k by have := i.2; omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt j.2]
  rwa [e] at h

/-- **The roots reach the same vertices** (`SameReach`), for every choice of lengths: a vertex
reached from a root other than the root is reached from the middle ring. -/
theorem srcMap_sameReach (ℓ' : SrcD D k → ℤ) :
    SameReach (srcMap hf) k (srcG hf) (srcPiece k S) ℓ' := by
  intro i hi j hj v hv hiv
  rw [srcTail_srcG hf hi] at hiv
  rw [srcTail_srcG hf hj]
  have hne : v ≠ .inr (⟨i, hi⟩, false) := fun h =>
    hv ⟨i, hi, by rw [srcTail_srcG hf hi, h]⟩
  have h1 := reach_of_root hf hiv hne
  have h2 : Reach (pieceGraph (srcMap hf) (srcPiece k S) ℓ') (.inr (⟨j, hj⟩, false))
      (.inr (⟨j, hj⟩, true)) :=
    (Reach.refl (G := pieceGraph (srcMap hf) (srcPiece k S) ℓ') ((pieceGraph (srcMap hf)
      (srcPiece k S) ℓ').src ⟨.inr (⟨j, hj⟩, .down), by simp [mem_srcPiece, inSrc]⟩)).arc
  exact h2.trans ((reach_mid' hf _ _).trans h1)

end Piece

/-! ### Distances -/

section Dist

variable (hf : FaceCycle M k g) {S : Finset D} {ℓ : D → ℤ} {W : ℤ}

/-- The copy of an arc of the piece of `M`. -/
def liftA (a : {d // d ∈ S}) : {d // d ∈ srcPiece k S} :=
  ⟨.inl a.1, by simp [mem_srcPiece, inSrc, a.2]⟩

/-- A walk of the piece of `M` is a walk between the copies, of the same length. -/
lemma lift_walk {x y : V} {l : List {d // d ∈ S}} (h : LWalk (pieceGraph M S ℓ) x y l) :
    LWalk (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) (.inl x) (.inl y)
        (l.map liftA) ∧
      wlen (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) (l.map liftA) =
        wlen (pieceGraph M S ℓ) l := by
  induction h with
  | nil x => exact ⟨.nil _, rfl⟩
  | @cons a y l _ ih =>
    rw [List.map_cons]
    refine ⟨LWalk.cons_iff.2 ⟨rfl, ih.1⟩, ?_⟩
    rw [wlen_cons, ih.2]
    rfl

/-- A walk from a copy of a vertex stays among the copies: it is a walk of the piece of `M`. -/
lemma down_walk {x : V} {y' : SrcV V k} {l' : List {d // d ∈ srcPiece k S}}
    (h : LWalk (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) (.inl x) y' l') :
    ∃ y l, y' = .inl y ∧ LWalk (pieceGraph M S ℓ) x y l ∧
      wlen (pieceGraph M S ℓ) l = wlen (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) l' := by
  induction l' generalizing x with
  | nil => exact ⟨x, [], (LWalk.nil_iff.1 h).symm, .nil x, rfl⟩
  | cons a l ih =>
    obtain ⟨hs, hw⟩ := LWalk.cons_iff.1 h
    obtain ⟨d, hd⟩ := a
    have hd' := mem_srcPiece.1 hd
    rcases d with e | ⟨j, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [inSrc] at hd' <;>
      simp [pieceGraph, srcMap, srcTail] at hs
    obtain ⟨y, l0, rfl, hw0, hlen⟩ := ih (x := M.head e) hw
    refine ⟨y, ⟨e, hd'⟩ :: l0, rfl, LWalk.cons_iff.2 ⟨hs, hw0⟩, ?_⟩
    rw [wlen_cons, wlen_cons, hlen]
    rfl

variable {hf} in
/-- A walk from `s m` to a copy has length at least `W`, or is `s m → t m` followed by a walk
of the piece of `M` from `t m`, of the same length. -/
lemma from_mid (hnn : ∀ a, 0 ≤ (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)).len a)
    {m : Fin k} {v : V} {l' : List {d // d ∈ srcPiece k S}}
    (h : LWalk (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) (.inr (m, true)) (.inl v)
      l') :
    W ≤ wlen (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) l' ∨
      ∃ l, LWalk (pieceGraph M S ℓ) (M.tail (g m)) v l ∧
        wlen (pieceGraph M S ℓ) l =
          wlen (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) l' := by
  rcases l' with _ | ⟨⟨d, hd⟩, l⟩
  · exact absurd (LWalk.nil_iff.1 h) (by simp)
  obtain ⟨hs, hw⟩ := LWalk.cons_iff.1 h
  have hd' := mem_srcPiece.1 hd
  rcases d with e | ⟨j, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [inSrc] at hd' <;>
    simp [pieceGraph, srcMap, srcTail] at hs
  · subst hs
    obtain ⟨y, l0, hy, hw0, hlen⟩ := down_walk hf (x := M.tail (g j)) hw
    cases Sum.inl.inj hy
    refine Or.inr ⟨l0, hw0, ?_⟩
    rw [hlen, wlen_cons]
    show _ = 0 + _
    rw [zero_add]
  · refine Or.inl ?_
    rw [wlen_cons]
    have := wlen_nonneg hnn l
    show W ≤ W + _
    omega

variable {hf} in
/-- A walk from the root `r i` to a copy has length at least `W`, or is `r i → s i → t i`
followed by a walk of the piece of `M` from `t i`, of the same length. -/
lemma from_root (hnn : ∀ a, 0 ≤ (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)).len a)
    {i : Fin k} {v : V} {l' : List {d // d ∈ srcPiece k S}}
    (h : LWalk (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) (.inr (i, false)) (.inl v)
      l') :
    W ≤ wlen (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) l' ∨
      ∃ l, LWalk (pieceGraph M S ℓ) (M.tail (g i)) v l ∧
        wlen (pieceGraph M S ℓ) l =
          wlen (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) l' := by
  rcases l' with _ | ⟨a, l⟩
  · exact absurd (LWalk.nil_iff.1 h) (by simp)
  obtain ⟨hs, hw⟩ := LWalk.cons_iff.1 h
  have ha := src_root hf a hs
  have e1 : (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)).dst a = .inr (i, true) := by
    simp [pieceGraph, ha, srcMap, CombMap.head, srcRev, srcTail]
  have e2 : (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)).len a = 0 := by
    simp [pieceGraph, ha, srcLen]
  rw [e1] at hw
  rw [wlen_cons, e2, zero_add]
  exact from_mid hnn hw

/-- A walk of the piece of `M` from `t i`, preceded by `r i → s i → t i`. -/
lemma to_root {i : Fin k} {v : V} {l : List {d // d ∈ S}}
    (h : LWalk (pieceGraph M S ℓ) (M.tail (g i)) v l) :
    ∃ l', LWalk (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) (.inr (i, false)) (.inl v)
      l' ∧ wlen (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ W)) l' =
        wlen (pieceGraph M S ℓ) l := by
  obtain ⟨h1, h2⟩ := lift_walk hf (W := W) h
  refine ⟨⟨.inr (i, .down), by simp [mem_srcPiece, inSrc]⟩ ::
    ⟨.inr (i, .out), by simp [mem_srcPiece, inSrc]⟩ :: l.map liftA,
    LWalk.cons_iff.2 ⟨rfl, LWalk.cons_iff.2 ⟨rfl, h1⟩⟩, ?_⟩
  rw [wlen_cons, wlen_cons, h2]
  show (0 : ℤ) + (0 + _) = _
  rw [zero_add, zero_add]

/-- **Every distance in the piece is less than `W`.** -/
lemma dist_lt_srcW (hnn : ∀ d ∈ S, 0 ≤ ℓ d) {x y : V}
    (h : Reach (pieceGraph M S ℓ) x y) : dist (pieceGraph M S ℓ) x y < srcW S ℓ := by
  have hnn' : ∀ a : {d // d ∈ S}, 0 ≤ (pieceGraph M S ℓ).len a := fun a => hnn a.1 a.2
  obtain ⟨l, hl⟩ := h
  obtain ⟨l', hl', -, hnd⟩ := exists_nodup_walk hl
  have h1 := dist_le hnn' hl'
  have h2 : wlen (pieceGraph M S ℓ) l' ≤ ∑ d ∈ S, ℓ d := by
    unfold wlen
    rw [← List.sum_toFinset _ (hnd.of_map _)]
    calc ∑ a ∈ l'.toFinset, (pieceGraph M S ℓ).len a
        ≤ ∑ a : {d // d ∈ S}, (pieceGraph M S ℓ).len a :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun a _ _ => hnn' a
      _ = ∑ d ∈ S, ℓ d := sum_coe_sort S ℓ
  unfold srcW; omega

/-- The cut-off at `W`: values below `W` are kept. -/
def cutW (W x : ℤ) : Option ℤ := if x < W then some x else none

/-- **The distances from the root `r i`, cut off at `W`, at the copies of the vertices, are the
distances in the piece of `M` from `t i`.** -/
theorem odist_src (hnn : ∀ d ∈ S, 0 ≤ ℓ d) (i : Fin k) (v : V) :
    (odist (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ (srcW S ℓ))) (.inr (i, false))
      (.inl v)).bind (cutW (srcW S ℓ)) = odist (pieceGraph M S ℓ) (M.tail (g i)) v := by
  have hnn' : ∀ a : {d // d ∈ S}, 0 ≤ (pieceGraph M S ℓ).len a := fun a => hnn a.1 a.2
  have hW : 0 ≤ srcW S ℓ := (srcW_pos hnn).le
  have hnnQ : ∀ a, 0 ≤ (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ (srcW S ℓ))).len a := by
    rintro ⟨d, hd⟩
    have := mem_srcPiece.1 hd
    rcases d with e | ⟨j, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [inSrc] at this <;>
      simp [pieceGraph, srcLen, hW]
    exact hnn e this
  unfold odist
  by_cases hr : Reach (pieceGraph M S ℓ) (M.tail (g i)) v
  · obtain ⟨l, hl, hlen⟩ := exists_walk_dist hnn' hr
    obtain ⟨l', hl', hlen'⟩ := to_root hf (W := srcW S ℓ) hl
    have hr' : Reach (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ (srcW S ℓ)))
        (.inr (i, false)) (.inl v) := ⟨l', hl'⟩
    have h1 := dist_le hnnQ hl'
    obtain ⟨m, hm, hmlen⟩ := exists_walk_dist hnnQ hr'
    have hlt := dist_lt_srcW hnn hr
    have e : dist (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ (srcW S ℓ)))
        (.inr (i, false)) (.inl v) = dist (pieceGraph M S ℓ) (M.tail (g i)) v := by
      rcases from_root hnnQ hm with h2 | ⟨l0, hl0, hlen0⟩
      · omega
      · have := dist_le hnn' hl0; omega
    simp only [hr, hr', ↓reduceIte, Option.bind_some, cutW, e, hlt]
  · simp only [hr, ↓reduceIte]
    by_cases hr' : Reach (pieceGraph (srcMap hf) (srcPiece k S) (srcLen ℓ (srcW S ℓ)))
        (.inr (i, false)) (.inl v)
    · obtain ⟨m, hm, hmlen⟩ := exists_walk_dist hnnQ hr'
      rcases from_root hnnQ hm with h2 | ⟨l0, hl0, -⟩
      · simp only [hr', ↓reduceIte, Option.bind_some, cutW]
        split_ifs with h3
        · omega
        · rfl
      · exact absurd ⟨l0, hl0⟩ hr
    · simp [hr']

end Dist

/-! ### Klein's answers -/

section Answers

variable (hf : FaceCycle M k g) (hM : M.IsPlane) (hrot : M.RotTrans) {S : Finset D}
  {ℓ : D → ℤ} (hnn : ∀ d ∈ S, 0 ≤ ℓ d)

/-- **The answers of Klein's trip on the map with the sources copied** (`kleinNN`, on the
perturbed lengths): from the root `r j`, at the copy of `v`, cut off at `W`. -/
noncomputable def srcAns (j : ℕ) (v : V) : Option ℤ :=
  (kleinNN (srcMap_hypNN hf hM hrot hnn (srcW_pos hnn).le) (srcMap_sameReach hf _) j
    (.inl v)).bind (cutW (srcW S ℓ))

/-- **Klein's answers on the map with the sources copied are the distances in the piece of `M`
from the vertices of the face.** -/
theorem srcAns_eq {j : ℕ} (hj : j < k) :
    srcAns hf hM hrot hnn j = odist (pieceGraph M S ℓ) (M.tail (g j)) := by
  funext v
  unfold srcAns
  rw [kleinNN_eq]
  have e : tripSrc (srcMap hf) k (srcG hf) j = .inr (⟨j, hj⟩, false) := by
    unfold tripSrc; rw [Nat.mod_eq_of_lt hj]; exact srcTail_srcG hf hj
  rw [e]
  exact odist_src hf hnn ⟨j, hj⟩ v

/-- Klein's answers on the map with the sources copied meet the specification of distances. -/
theorem srcAns_isDist {j : ℕ} (hj : j < k) :
    BKMNW.IsDist (pieceGraph M S ℓ) (M.tail (g j)) (srcAns hf hM hrot hnn j) := by
  rw [srcAns_eq hf hM hrot hnn hj]
  exact BKMNW.isDist_odist (fun a => hnn a.1 a.2) _

end Answers

end Klein

end PlanarFlow
