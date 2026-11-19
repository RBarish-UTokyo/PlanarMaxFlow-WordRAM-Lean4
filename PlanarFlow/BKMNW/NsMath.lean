module

public import PlanarFlow.BKMNW.NegCallH
public import PlanarFlow.BKMNW.OrbLab
public import PlanarFlow.BKMNW.LinRet

/-!
# The identifiers and the numbering of a negSSSP call, from a dart order (pure part)

The negative-length shortest paths of a call run on the dual `M.dual` of a map `M` whose darts are
numbered `0 … m-1` by `en` (the frame's dart order). This file fixes the global identifiers
`nsIds` of such a call and describes every word of the root frame (`InP`) by functions of the
indices, so that a machine program working on index arrays can write them.

* `enL en m` (the darts in the order of `en`), `ixOf` (the index of a dart), `EnumOK` (`en` a
  bijection of `[0, m)` onto the darts, every face has a dart, transitive faces);
* `phiI` (the face permutation `next` on the indices), `rvI` (the reverse), `labI` (the orbit
  label `olab phiI`), **`nsIds`**: `uL = enL en m` (so `gd (en i) = i`, `gd_en`), the vertex
  identifier of a face of `M` (a vertex of the dual) the orbit label of any of its darts
  (`gv_face`), `G = m`;
* the grouping key `keyI` (tail face, head face of the dual dart), `sameEnds_iff`, the edge key
  `ekI`, **`mem_repsN_iff`** (the kept darts by the maximum of `m - ekI` over the group),
  **`minLen_eq`** (the least length by the maximum of `Z - LN` over the group), **`rtL_eq`**;
* the index lists `cLi`, `rLi`, `fLi` with **`cL_eq`**, **`rL_eq`**, **`fL_eq`**, and the words
  **`cδ_eq'`**, **`cα_eq'`**, **`cσ_eq'`**, the numbers `card_eq`, `ck_eq`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset Function Equiv Orbit CombMap NegSSSP NegSSSP.Frame OrbLab

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### The dart order -/

/-- The darts in the order of `en`. -/
def enL (en : ℕ → D) (m : ℕ) : List D := (List.range m).map en

/-- The index of a dart in the order of `en`. -/
def ixOf (en : ℕ → D) (m : ℕ) (d : D) : ℕ := (enL en m).idxOf d

/-- **The hypotheses on the dart order**: `en` a bijection of `[0, m)` onto the darts; every face
of `M` has a dart; the faces are the orbits of `next`. -/
structure EnumOK (M : CombMap D V F) (en : ℕ → D) (m : ℕ) : Prop where
  inj : ∀ i < m, ∀ j < m, en i = en j → i = j
  surj : ∀ d, ∃ i < m, en i = d
  fsurj : ∀ f, ∃ d, M.face d = f
  ft : M.FaceTrans

variable {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

lemma length_enL : (enL en m).length = m := by simp [enL]

lemma getElem_enL {i : ℕ} (hi : i < (enL en m).length) : (enL en m)[i] = en i := by
  simp [enL]

lemma enL_nodup (h : EnumOK M en m) : (enL en m).Nodup :=
  List.Nodup.map_on (fun x hx y hy e => h.inj x (List.mem_range.1 hx) y (List.mem_range.1 hy) e)
    List.nodup_range

lemma mem_enL (h : EnumOK M en m) (d : D) : d ∈ enL en m := by
  obtain ⟨i, hi, rfl⟩ := h.surj d
  exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩

lemma ixOf_en (h : EnumOK M en m) {i : ℕ} (hi : i < m) : ixOf en m (en i) = i := by
  have hl : i < (enL en m).length := by rw [length_enL]; exact hi
  unfold ixOf
  rw [← getElem_enL hl]
  exact (enL_nodup h).idxOf_getElem i hl

lemma ixOf_lt (h : EnumOK M en m) (d : D) : ixOf en m d < m := by
  have := List.idxOf_lt_length_iff.2 (mem_enL h d)
  rw [length_enL] at this
  exact this

lemma en_ixOf (h : EnumOK M en m) (d : D) : en (ixOf en m d) = d := by
  have hl := List.idxOf_lt_length_iff.2 (mem_enL h d)
  have := List.getElem_idxOf hl
  rw [getElem_enL] at this
  exact this

lemma en_inj_iff (h : EnumOK M en m) {i j : ℕ} (hi : i < m) (hj : j < m) :
    en i = en j ↔ i = j := ⟨h.inj i hi j hj, fun e => e ▸ rfl⟩

/-! ### The face permutation on the indices -/

variable (M en m) in
/-- The face permutation `next` on the indices. -/
noncomputable def phiI (i : ℕ) : ℕ := ixOf en m (M.next (en i))

variable (M en m) in
/-- The reverse on the indices. -/
noncomputable def rvI (i : ℕ) : ℕ := ixOf en m (M.rev (en i))

variable (M en m) in
/-- The orbit label of the face permutation. -/
noncomputable def labI (i : ℕ) : ℕ := olab (phiI M en m) i

lemma en_phiI (h : EnumOK M en m) (i : ℕ) : en (phiI M en m i) = M.next (en i) := en_ixOf h _

lemma en_rvI (h : EnumOK M en m) (i : ℕ) : en (rvI M en m i) = M.rev (en i) := en_ixOf h _

lemma rvI_lt (h : EnumOK M en m) (i : ℕ) : rvI M en m i < m := ixOf_lt h _

lemma rvI_rvI (h : EnumOK M en m) {i : ℕ} (hi : i < m) : rvI M en m (rvI M en m i) = i := by
  unfold rvI
  rw [en_ixOf h, M.rev_rev, ixOf_en h hi]

lemma phi_permOn (h : EnumOK M en m) : PermOn (phiI M en m) m where
  lt x _ := ixOf_lt h _
  inj x hx y hy e := by
    have := congrArg en e
    rw [en_phiI h, en_phiI h] at this
    exact h.inj x hx y hy (M.next_injective this)

lemma en_phiI_iter (h : EnumOK M en m) (i : ℕ) :
    ∀ t, en ((phiI M en m)^[t] i) = M.next^[t] (en i)
  | 0 => rfl
  | t + 1 => by rw [iterate_succ_apply', iterate_succ_apply', en_phiI h, en_phiI_iter h i t]

lemma face_next_iter (d : D) : ∀ t, M.face (M.next^[t] d) = M.face d
  | 0 => rfl
  | t + 1 => by rw [iterate_succ_apply', M.face_next, face_next_iter d t]

lemma labI_lt (h : EnumOK M en m) {i : ℕ} (hi : i < m) : labI M en m i < m :=
  olab_lt (phi_permOn h) hi

/-- Two darts lie on the same face iff their indices have the same label. -/
lemma face_eq_iff (h : EnumOK M en m) {i j : ℕ} (hi : i < m) (hj : j < m) :
    M.face (en i) = M.face (en j) ↔ labI M en m i = labI M en m j := by
  rw [labI, labI, olab_eq_iff (phi_permOn h) hi hj]
  constructor
  · intro e
    obtain ⟨t, ht⟩ := h.ft _ _ e
    refine ⟨t, h.inj _ (OrbLab.iter_lt (phi_permOn h) hi t) j hj ?_⟩
    rw [en_phiI_iter h, ht]
  · rintro ⟨t, rfl⟩
    rw [en_phiI_iter h, face_next_iter]

/-! ### The identifiers -/

variable (M) in
/-- **The identifiers of the call**: the darts in the order of `en`, the identifier of a face
the label of any of its darts, `G = m`. -/
noncomputable def nsIds (h : EnumOK M en m) (d₀ : D) : GIds D F where
  uL := enL en m
  nodup := enL_nodup h
  comp := mem_enL h
  gv f := labI M en m (ixOf en m (Classical.choose (h.fsurj f)))
  gv_inj f f' e := by
    have h1 := Classical.choose_spec (h.fsurj f)
    have h2 := Classical.choose_spec (h.fsurj f')
    rw [← (face_eq_iff h (ixOf_lt h _) (ixOf_lt h _)), en_ixOf h, en_ixOf h, h1, h2] at e
    exact e
  G := m
  gv_lt f := labI_lt h (ixOf_lt h _)
  d₀ := d₀

variable (h : EnumOK M en m) (d₀ : D)
include h

@[simp] lemma nsIds_G : (nsIds M h d₀).G = m := rfl

lemma gd_eq (d : D) : (nsIds M h d₀).gd d = ixOf en m d := rfl

lemma gd_en {i : ℕ} (hi : i < m) : (nsIds M h d₀).gd (en i) = i := ixOf_en h hi

lemma gv_face {i : ℕ} (hi : i < m) : (nsIds M h d₀).gv (M.face (en i)) = labI M en m i := by
  show labI M en m (ixOf en m (Classical.choose (h.fsurj (M.face (en i))))) = _
  have h1 := Classical.choose_spec (h.fsurj (M.face (en i)))
  have := (face_eq_iff h (ixOf_lt h (Classical.choose (h.fsurj (M.face (en i))))) hi).1
    (by rw [en_ixOf h, h1])
  exact this

lemma gv_dtail {i : ℕ} (hi : i < m) :
    (nsIds M h d₀).gv (M.dual.tail (en i)) = labI M en m i := gv_face h d₀ hi

lemma gv_dhead {i : ℕ} (hi : i < m) :
    (nsIds M h d₀).gv (M.dual.head (en i)) = labI M en m (rvI M en m i) := by
  show (nsIds M h d₀).gv (M.face (M.rev (en i))) = _
  rw [← en_rvI h, gv_face h d₀ (rvI_lt h i)]

/-! ### The grouping by the ends of the dual darts -/

variable (M en m) in
/-- The key of the ends (tail face, head face) of a dual dart. -/
noncomputable def keyI (i : ℕ) : ℕ :=
  (labI M en m i + 1) * (m + 1) + (labI M en m (rvI M en m i) + 1)

variable (M en m) in
/-- The edge key of a dart: the least index of the dart and its reverse. -/
noncomputable def ekI (i : ℕ) : ℕ := min i (rvI M en m i)

omit h in
lemma key_inj {a b c e m : ℕ} (hb : b < m) (he : e < m)
    (h : (a + 1) * (m + 1) + (b + 1) = (c + 1) * (m + 1) + (e + 1)) : a = c ∧ b = e := by
  rcases lt_trichotomy a c with hac | rfl | hac
  · have : (a + 1 + 1) * (m + 1) ≤ (c + 1) * (m + 1) := Nat.mul_le_mul_right _ (by omega)
    have e : (a + 1 + 1) * (m + 1) = (a + 1) * (m + 1) + (m + 1) := by ring
    omega
  · omega
  · have : (c + 1 + 1) * (m + 1) ≤ (a + 1) * (m + 1) := Nat.mul_le_mul_right _ (by omega)
    have e : (c + 1 + 1) * (m + 1) = (c + 1) * (m + 1) + (m + 1) := by ring
    omega

lemma keyI_eq_iff {i j : ℕ} (hi : i < m) (hj : j < m) :
    keyI M en m j = keyI M en m i ↔
      labI M en m j = labI M en m i ∧ labI M en m (rvI M en m j) = labI M en m (rvI M en m i) := by
  constructor
  · intro e
    exact key_inj (labI_lt h (rvI_lt h j)) (labI_lt h (rvI_lt h i)) e
  · rintro ⟨e1, e2⟩
    unfold keyI; rw [e1, e2]

lemma dtail_eq_iff {i j : ℕ} (hi : i < m) (hj : j < m) :
    M.dual.tail (en j) = M.dual.tail (en i) ↔ labI M en m j = labI M en m i :=
  face_eq_iff h hj hi

lemma dhead_eq_iff {i j : ℕ} (hi : i < m) (hj : j < m) :
    M.dual.head (en j) = M.dual.head (en i) ↔
      labI M en m (rvI M en m j) = labI M en m (rvI M en m i) := by
  show M.face (M.rev (en j)) = M.face (M.rev (en i)) ↔ _
  rw [← en_rvI h, ← en_rvI h]
  exact face_eq_iff h (rvI_lt h j) (rvI_lt h i)

/-- **Same ends iff same key.** -/
lemma sameEnds_iff {i j : ℕ} (hi : i < m) (hj : j < m) :
    (M.dual.tail (en j) = M.dual.tail (en i) ∧ M.dual.head (en j) = M.dual.head (en i)) ↔
      keyI M en m j = keyI M en m i := by
  rw [dtail_eq_iff h hi hj, dhead_eq_iff h hi hj, keyI_eq_iff h hi hj]

lemma ekeyN_en {i : ℕ} (hi : i < m) :
    ekeyN M.dual (nsIds M h d₀).gd (en i) = ekI M en m i := by
  unfold ekeyN ekI
  show min _ ((nsIds M h d₀).gd (M.rev (en i))) = _
  rw [gd_en h d₀ hi, ← en_rvI h, gd_en h d₀ (rvI_lt h i)]

lemma ekI_lt {i : ℕ} (hi : i < m) : ekI M en m i < m := by
  unfold ekI; exact lt_of_le_of_lt (min_le_left _ _) hi

variable (M en m) in
/-- The group of a dart: the indices with the same key. -/
noncomputable def grpI (i : ℕ) : Finset ℕ := (range m).filter fun j => keyI M en m j = keyI M en m i

omit h in
lemma mem_grpI {i j : ℕ} : j ∈ grpI M en m i ↔ j < m ∧ keyI M en m j = keyI M en m i := by
  simp [grpI]

omit h in
lemma self_mem_grpI {i : ℕ} (hi : i < m) : i ∈ grpI M en m i := mem_grpI.2 ⟨hi, rfl⟩

/-- **The kept darts**: not a loop of the dual, and the maximum of `m - ekI` over the group is
reached at the dart. -/
theorem mem_repsN_iff {i : ℕ} (hi : i < m) :
    en i ∈ repsN M.dual (nsIds M h d₀).gd ↔ labI M en m i ≠ labI M en m (rvI M en m i) ∧
      (grpI M en m i).sup (fun j => m - ekI M en m j) ≤ m - ekI M en m i := by
  rw [mem_repsN]
  have e1 : M.dual.tail (en i) ≠ M.dual.head (en i) ↔
      labI M en m i ≠ labI M en m (rvI M en m i) := by
    rw [← gv_dtail h d₀ hi, ← gv_dhead h d₀ hi]
    exact ⟨fun hne e => hne ((nsIds M h d₀).gv_inj e), fun hne e => hne (by rw [e])⟩
  rw [e1, Finset.sup_le_iff]
  refine and_congr Iff.rfl ⟨fun H j hj => ?_, fun H x hx1 hx2 => ?_⟩
  · obtain ⟨hjm, hk⟩ := mem_grpI.1 hj
    obtain ⟨e2, e3⟩ := (sameEnds_iff h hi hjm).2 hk
    have := H (en j) e2 e3
    rw [ekeyN_en h d₀ hi, ekeyN_en h d₀ hjm] at this
    have := ekI_lt h hjm
    omega
  · have hxm := ixOf_lt h x
    rw [← en_ixOf h x] at hx1 hx2 ⊢
    have hk := (sameEnds_iff h hi hxm).1 ⟨hx1, hx2⟩
    have := H _ (mem_grpI.2 ⟨hxm, hk⟩)
    rw [ekeyN_en h d₀ hi, ekeyN_en h d₀ hxm]
    have := ekI_lt h hi
    have := ekI_lt h hxm
    omega

/-- **The least length** of the group, from the maximum of `Z - LN` (lengths in the offset
encoding `LN = ℓ + K`, `0 ≤ ℓ + K ≤ Z`). -/
theorem minLen_eq (ℓ : D → ℤ) (K Z : ℕ) (hlo : ∀ j < m, 0 ≤ ℓ (en j) + K)
    (hhi : ∀ j < m, ℓ (en j) + K ≤ Z) {i : ℕ} (hi : i < m) :
    ((Z - (grpI M en m i).sup (fun j => Z - (ℓ (en j) + K).toNat) : ℕ) : ℤ) =
      minLen M.dual ℓ (en i) + K := by
  obtain ⟨x, hx1, hx2, ex⟩ := exists_minLen (N := M.dual) ℓ (en i)
  have hxm := ixOf_lt h x
  rw [← en_ixOf h x] at hx1 hx2 ex
  set j₀ := ixOf en m x
  have hj₀ : j₀ ∈ grpI M en m i := mem_grpI.2 ⟨hxm, (sameEnds_iff h hi hxm).1 ⟨hx1, hx2⟩⟩
  have hmin : ∀ j ∈ grpI M en m i, ℓ (en j₀) ≤ ℓ (en j) := fun j hj => by
    obtain ⟨hjm, hk⟩ := mem_grpI.1 hj
    obtain ⟨e2, e3⟩ := (sameEnds_iff h hi hjm).2 hk
    rw [← ex]; exact minLen_le (N := M.dual) ℓ e2 e3
  have hsup : (grpI M en m i).sup (fun j => Z - (ℓ (en j) + K).toNat) =
      Z - (ℓ (en j₀) + K).toNat := by
    refine le_antisymm (Finset.sup_le fun j hj => ?_) (Finset.le_sup (f := fun j => Z - (ℓ (en j) + K).toNat) hj₀)
    have := hmin j hj
    have := hlo j (mem_grpI.1 hj).1
    have := hlo j₀ hxm
    omega
  rw [hsup, ex]
  have := hlo j₀ hxm
  have := hhi j₀ hxm
  omega

/-- The sum over the darts as a sum over the indices. -/
lemma sum_en (f : D → ℤ) : ∑ x, f x = ∑ i ∈ range m, f (en i) := by
  symm
  refine Finset.sum_nbij en (fun _ _ => mem_univ _) (fun a ha b hb e => ?_) (fun y _ => ?_)
    (fun _ _ => rfl)
  · exact h.inj a (mem_range.1 ha) b (mem_range.1 hb) e
  · obtain ⟨i, hi, rfl⟩ := h.surj y
    exact ⟨i, by simpa using hi, rfl⟩

/-- **The offset of the root**: `rtL = Σ_i |MLN i - K|` with `MLN i = minLen + K`. -/
theorem rtL_eq (ℓ : D → ℤ) (K : ℕ) (MLN : ℕ → ℕ)
    (hM : ∀ i < m, (MLN i : ℤ) = minLen M.dual ℓ (en i) + K) :
    rtL M ℓ = ∑ i ∈ range m, ((MLN i - K) + (K - MLN i)) := by
  unfold rtL
  rw [sum_en h]
  have : ∑ i ∈ range m, |minLen M.dual ℓ (en i)| =
      ((∑ i ∈ range m, ((MLN i - K) + (K - MLN i)) : ℕ) : ℤ) := by
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have := hM i (mem_range.1 hi)
    rcases le_total K (MLN i) with hk | hk
    · rw [Nat.sub_eq_zero_of_le hk, Nat.cast_sub hk, abs_of_nonneg (by omega)]; push_cast; omega
    · rw [Nat.sub_eq_zero_of_le hk, Nat.cast_sub hk, abs_of_nonpos (by omega)]; push_cast; omega
  rw [this, Int.toNat_natCast]

/-! ### The canonical numbering on the indices -/

variable (M en m) in
/-- The keep flag of an index. -/
noncomputable def keepB (i : ℕ) : Bool := decide (en i ∈ repsN M.dual (nsIds M h d₀).gd)

variable (M en m) in
/-- The kept indices in increasing order (prefix `[0, i)`). -/
noncomputable def cLp (i : ℕ) : List ℕ := (List.range i).filter (keepB M en m h d₀)

variable (M en m) in
/-- The kept indices. -/
noncomputable def cLi : List ℕ := cLp M en m h d₀ m

variable (M en m) in
/-- The reverses not kept of the first `t` kept indices. -/
noncomputable def rLp (t : ℕ) : List ℕ :=
  (((cLi M en m h d₀).take t).filter (fun x => !keepB M en m h d₀ (rvI M en m x))).map (rvI M en m)

variable (M en m) in
/-- The reverses not kept of the kept indices. -/
noncomputable def rLi : List ℕ :=
  ((cLi M en m h d₀).filter (fun x => !keepB M en m h d₀ (rvI M en m x))).map (rvI M en m)

variable (M en m) in
/-- The canonical list of the closure on the indices. -/
noncomputable def fLi : List ℕ := cLi M en m h d₀ ++ rLi M en m h d₀

lemma rLp_full : rLp M en m h d₀ (cLi M en m h d₀).length = rLi M en m h d₀ := by
  unfold rLp rLi; rw [List.take_length]

lemma cL_eq : cL (nsIds M h d₀) (repsN M.dual (nsIds M h d₀).gd) = (cLi M en m h d₀).map en := by
  unfold cL cLi cLp
  show ((List.range m).map en).filter _ = _
  rw [List.filter_map]
  rfl

lemma rL_eq : rL (nsIds M h d₀) M.dual (repsN M.dual (nsIds M h d₀).gd) =
    (rLi M en m h d₀).map en := by
  unfold rL rLi
  rw [cL_eq, List.filter_map, List.map_map, List.map_map]
  have e1 : ((fun d => decide (M.dual.rev d ∉ repsN M.dual (nsIds M h d₀).gd)) ∘ en) =
      fun x => !keepB M en m h d₀ (rvI M en m x) := by
    funext x
    have : M.dual.rev (en x) = en (rvI M en m x) := (en_rvI h x).symm
    simp only [comp_apply, keepB, this, decide_not]
  have e2 : M.dual.rev ∘ en = en ∘ rvI M en m := by
    funext x; simp only [comp_apply, en_rvI h]; rfl
  rw [e1, e2]

lemma fL_eq : fL (nsIds M h d₀) M.dual (repsN M.dual (nsIds M h d₀).gd) =
    (fLi M en m h d₀).map en := by
  unfold fL fLi; rw [cL_eq, rL_eq, List.map_append]

lemma cLp_lt {i x : ℕ} (hx : x ∈ cLp M en m h d₀ i) : x < i := by
  unfold cLp at hx; rw [List.mem_filter, List.mem_range] at hx; exact hx.1

lemma cLi_lt {x : ℕ} (hx : x ∈ cLi M en m h d₀) : x < m := cLp_lt h d₀ hx

lemma mem_cLi {x : ℕ} : x ∈ cLi M en m h d₀ ↔ x < m ∧ keepB M en m h d₀ x = true := by
  unfold cLi cLp; rw [List.mem_filter, List.mem_range]

lemma fLi_lt {x : ℕ} (hx : x ∈ fLi M en m h d₀) : x < m := by
  unfold fLi rLi at hx
  rw [List.mem_append, List.mem_map] at hx
  rcases hx with hx | ⟨y, -, rfl⟩
  · exact cLi_lt h d₀ hx
  · exact rvI_lt h _

lemma idxOf_map_en {l : List ℕ} (hl : ∀ x ∈ l, x < m) {x : ℕ} (hx : x < m) :
    (l.map en).idxOf (en x) = l.idxOf x := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons]
    have ha := hl a (by simp)
    have := ih (fun y hy => hl y (by simp [hy]))
    by_cases e : a = x
    · subst e; simp
    · have h1 : (en a == en x) = false := by
        rw [beq_eq_false_iff_ne]; exact fun e' => e (h.inj a ha x hx e')
      have h2 : (a == x) = false := beq_eq_false_iff_ne.2 e
      rw [h1, h2, this]

lemma fLi_nodup : (fLi M en m h d₀).Nodup := by
  have := fL_nodup (g := nsIds M h d₀) (N := M.dual) (repsN M.dual (nsIds M h d₀).gd)
  rw [fL_eq] at this
  exact this.of_map _

lemma mem_fLi_iff {x : ℕ} (hx : x < m) :
    x ∈ fLi M en m h d₀ ↔ en x ∈ rcl M.dual (repsN M.dual (nsIds M h d₀).gd) := by
  rw [← mem_fL (g := nsIds M h d₀), fL_eq, List.mem_map]
  exact ⟨fun hm => ⟨x, hm, rfl⟩, fun ⟨y, hy, e⟩ => by
    rwa [← h.inj y (fLi_lt h d₀ hy) x hx e]⟩

lemma card_eq : (repsN M.dual (nsIds M h d₀).gd).card = (cLi M en m h d₀).length := by
  rw [← length_cL (g := nsIds M h d₀), cL_eq, List.length_map]

lemma ck_eq : ck M.dual (repsN M.dual (nsIds M h d₀).gd) = (fLi M en m h d₀).length := by
  unfold ck
  rw [← length_fL (g := nsIds M h d₀) (N := M.dual), fL_eq, List.length_map]

lemma cδ_eq' {t : ℕ} (ht : t < (fLi M en m h d₀).length) :
    cδ (nsIds M h d₀) M.dual (repsN M.dual (nsIds M h d₀).gd) t = en (fLi M en m h d₀)[t] := by
  unfold cδ
  rw [fL_eq, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact ht), List.getElem_map]

lemma cα_eq' {t : ℕ} (ht : t < (fLi M en m h d₀).length) :
    cα (nsIds M h d₀) M.dual (repsN M.dual (nsIds M h d₀).gd) t =
      (fLi M en m h d₀).idxOf (rvI M en m (fLi M en m h d₀)[t]) := by
  unfold cα
  rw [cδ_eq' h d₀ ht, fL_eq]
  show (List.map en _).idxOf (M.rev _) = _
  rw [← en_rvI h, idxOf_map_en h (fun x hx => fLi_lt h d₀ hx) (rvI_lt h _)]

lemma rotPerm_dual_en (i : ℕ) : rotPerm M.dual (en i) = M.next (en i) := by
  rw [rotPerm_apply]
  show M.rot (M.rev (en i)) = _
  unfold CombMap.rot
  rw [M.rev_rev]

/-- **The first return in the index numbering**: if the dart of index `s < m` is the first return
of the rotation of the dual to the closure from the dart of `fLi[t]`, then `cσ t` is the position
of `s` in `fLi`. -/
lemma cσ_eq' {t s : ℕ} (ht : t < (fLi M en m h d₀).length) (hs : s < m)
    (e : en s = ret (rotPerm M.dual) (rcl M.dual (repsN M.dual (nsIds M h d₀).gd))
      (en (fLi M en m h d₀)[t])) :
    cσ (nsIds M h d₀) M.dual (repsN M.dual (nsIds M h d₀).gd) t = (fLi M en m h d₀).idxOf s := by
  unfold cσ
  rw [cδ_eq' h d₀ ht, ← e, fL_eq, idxOf_map_en h (fun x hx => fLi_lt h d₀ hx) hs]

end NsStep

end BKMNW

end PlanarFlow
