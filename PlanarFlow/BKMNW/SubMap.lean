module

public import PlanarFlow.Plane.Submap
public import PlanarFlow.BKMNW.CutBuild

/-!
# The combinatorial map of a submap, and its planarity

A submap (`PlanarFlow/Plane/Submap.lean`) is a set `B` of darts closed under the reversal `ι`
with a rotation `σ` mapping `B` into itself. `subMap` is the combinatorial map on the darts of
`B`: its vertices are the orbits of `σ` (`SVert`), its faces the orbits of the face walk
`σ * ι` (`SFace`), its boundary walk is `σ * ι`.

* `subMap_isPlane`: **the map of a connected submap with zero Euler gap is plane**: Euler's
  formula is the vanishing of the gap, counted by orbits (`card_sVert`, `card_sFace`).
* `subMap_rotTrans`, `subMap_faceTrans`: its rotations and faces are transitive (they are orbits
  by construction), so the multiple-source shortest-path data structure applies to it
  (`PlanarFlow.BKMNW.msspPlane_spec`).
* `gap_rot_eq_zero`: **a plane map with transitive rotations and faces is a submap with zero
  gap** (all its darts, its rotation), so by `PlanarFlow.Orbit.gap_ret_eq_zero` and
  `PlanarFlow.Orbit.gap_con_eq_zero` every submap obtained from it by deleting and contracting
  edges has zero gap, and its map is plane as soon as it is connected.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Orbit

open Finset Function Equiv CombMap Relation

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The map of a submap -/

section SubMap

variable (σ : Perm α) (B : Finset α)

/-- The darts of the submap. -/
abbrev SDart := {x : α // x ∈ B}

/-- Two darts of the submap in the same orbit of `σ`. -/
def orbSetoid : Setoid (SDart B) where
  r x y := σ.SameCycle x.1 y.1
  iseqv := ⟨fun _ => Perm.SameCycle.refl _ _, fun h => h.symm, fun h h' => h.trans h'⟩

/-- The vertices of the submap: the orbits of the rotation. -/
abbrev SVert := Quotient (orbSetoid σ B)

/-- The faces of the submap: the orbits of the face walk. -/
abbrev SFace (ι : Perm α) := SVert (σ * ι) B

noncomputable instance : Fintype (SVert σ B) := by classical exact Quotient.fintype _

noncomputable instance : DecidableEq (SVert σ B) := Classical.decEq _

variable {σ B}

lemma sVert_eq_iff {x y : SDart B} :
    (Quotient.mk (orbSetoid σ B) x = Quotient.mk _ y) ↔ σ.SameCycle x.1 y.1 :=
  ⟨Quotient.exact, fun h => Quotient.sound h⟩

/-- **The number of vertices of the submap** is the number of orbits meeting `B`. -/
theorem card_sVert : Fintype.card (SVert σ B) = nOrb σ B := by
  classical
  let f : SVert σ B → {c // c ∈ B.image (cls σ)} :=
    Quotient.lift (fun x => ⟨cls σ x.1, mem_image_of_mem _ x.2⟩)
      (fun x y h => Subtype.ext (cls_eq_iff.2 h))
  have hf : Bijective f := by
    constructor
    · intro a b h
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      exact Quotient.sound (cls_eq_iff.1 (congrArg Subtype.val h))
    · rintro ⟨c, hc⟩
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
      exact ⟨Quotient.mk _ ⟨x, hx⟩, rfl⟩
  rw [Fintype.card_of_bijective hf, Fintype.card_coe]
  rfl

/-- A connected submap has one component. -/
lemma comp_eq_one {ι : Perm α} (hι : IsInv ι) {x₀ : α} (hx₀ : x₀ ∈ B) (hconn : ∀ x ∈ B, ∀ y ∈ B, Conn ι σ x y) :
    comp ι σ B = 1 := by
  rw [comp, card_eq_one]
  refine ⟨ccls ι σ x₀, eq_singleton_iff_unique_mem.2 ⟨mem_image_of_mem _ hx₀, fun c hc => ?_⟩⟩
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hc
  exact (ccls_eq_iff hι).2 (hconn x hx x₀ hx₀)

variable {ι : Perm α} (hι : IsInv ι) (hσ : Stable σ B) (hB : Stable ι B)

variable (B) in
/-- **The combinatorial map of a submap.** -/
noncomputable def subMap : CombMap (SDart B) (SVert σ B) (SFace σ B ι) where
  rev x := ⟨ι x.1, hB _ x.2⟩
  rev_rev _ := Subtype.ext (hι.invol _)
  rev_ne x h := hι.ne x.1 (congrArg Subtype.val h)
  tail x := Quotient.mk _ x
  face x := Quotient.mk _ x
  next x := ⟨(σ * ι) x.1, (hσ.mul hB) _ x.2⟩
  next_injective _ _ h := Subtype.ext ((σ * ι).injective (congrArg Subtype.val h))
  face_next _ := Quotient.sound (Perm.sameCycle_apply_left.2 (Perm.SameCycle.refl _ _))
  tail_next _ := Quotient.sound (Perm.sameCycle_apply_left.2 (Perm.SameCycle.refl _ _))

@[simp] lemma subMap_rev (x : SDart B) : ((subMap B hι hσ hB).rev x).1 = ι x.1 := rfl

@[simp] lemma subMap_next (x : SDart B) : ((subMap B hι hσ hB).next x).1 = σ (ι x.1) := rfl

lemma subMap_tail (x : SDart B) : (subMap B hι hσ hB).tail x = Quotient.mk _ x := rfl

lemma subMap_face (x : SDart B) : (subMap B hι hσ hB).face x = Quotient.mk _ x := rfl

@[simp] lemma subMap_rot (x : SDart B) : ((subMap B hι hσ hB).rot x).1 = σ x.1 := by
  simp [CombMap.rot, hι.invol]

lemma subMap_rot_iterate (x : SDart B) (n : ℕ) :
    (((subMap B hι hσ hB).rot)^[n] x).1 = σ^[n] x.1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, ih, subMap_rot, ← iterate_succ_apply]

lemma subMap_next_iterate (x : SDart B) (n : ℕ) :
    (((subMap B hι hσ hB).next)^[n] x).1 = (σ * ι)^[n] x.1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply, ih, subMap_next, ← Perm.mul_apply, ← iterate_succ_apply]

/-- **The rotations of the map of a submap are transitive.** -/
theorem subMap_rotTrans : (subMap B hι hσ hB).RotTrans := by
  intro x y h
  obtain ⟨n, hn⟩ := sameCycle_iff.1 (Quotient.exact h)
  exact ⟨n, Subtype.ext (by rw [subMap_rot_iterate, hn])⟩

/-- **The faces of the map of a submap are transitive.** -/
theorem subMap_faceTrans : (subMap B hι hσ hB).FaceTrans := by
  intro x y h
  obtain ⟨n, hn⟩ := sameCycle_iff.1 (Quotient.exact h)
  exact ⟨n, Subtype.ext (by rw [subMap_next_iterate, hn])⟩

lemma card_sFace : Fintype.card (SFace σ B ι) = nOrb (σ * ι) B := card_sVert

/-- **The map of a connected submap with zero Euler gap is plane.** -/
theorem subMap_isPlane {x₀ : α} (hx₀ : x₀ ∈ B) (hconn : ∀ x ∈ B, ∀ y ∈ B, Conn ι σ x y)
    (h0 : gap ι σ B = 0) : (subMap B hι hσ hB).IsPlane where
  nonempty := ⟨Quotient.mk _ ⟨x₀, hx₀⟩⟩
  conn a b := by
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    rename_i x y
    have key : ∀ z, Conn ι σ x.1 z → ∀ hz : z ∈ B,
        ReflTransGen (subMap B hι hσ hB).Adj (Quotient.mk _ x) (Quotient.mk _ ⟨z, hz⟩) := by
      intro z h
      induction h with
      | refl => intro _; exact .refl
      | tail h1 hst ih =>
        rename_i b c
        intro hc
        have hb : b ∈ B := hσ.of_conn hB x.2 h1
        refine (ih hb).trans ?_
        rcases hst with rfl | rfl
        · have : Quotient.mk (orbSetoid σ B) ⟨σ b, hc⟩ = Quotient.mk _ ⟨b, hb⟩ :=
            Quotient.sound (Perm.sameCycle_apply_left.2 (Perm.SameCycle.refl _ _))
          rw [this]
        · exact .single ⟨⟨b, hb⟩, rfl, rfl⟩
    exact key y.1 (hconn x.1 x.2 y.1 y.2) y.2
  dualConn a b := by
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    rename_i x y
    have key : ∀ z, Conn ι (σ * ι) x.1 z → ∀ hz : z ∈ B,
        ReflTransGen (subMap B hι hσ hB).DualAdj (Quotient.mk _ x) (Quotient.mk _ ⟨z, hz⟩) := by
      intro z h
      induction h with
      | refl => intro _; exact .refl
      | tail h1 hst ih =>
        rename_i b c
        intro hc
        have hb : b ∈ B := (hσ.mul hB).of_conn hB x.2 h1
        refine (ih hb).trans ?_
        rcases hst with rfl | rfl
        · have : Quotient.mk (orbSetoid (σ * ι) B) ⟨(σ * ι) b, hc⟩ = Quotient.mk _ ⟨b, hb⟩ :=
            Quotient.sound (Perm.sameCycle_apply_left.2 (Perm.SameCycle.refl _ _))
          rw [this]
        · exact .single ⟨⟨b, hb⟩, rfl, rfl⟩
    exact key y.1 ((conn_mul_iff hι).2 (hconn x.1 x.2 y.1 y.2)) y.2
  euler := by
    have h1 := comp_eq_one hι hx₀ hconn
    rw [card_sVert, card_sFace, Fintype.card_coe]
    unfold gap eul at h0
    rw [h1] at h0
    omega

end SubMap

/-! ### Plane maps are submaps with zero gap -/

section Root

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] (M : CombMap D V F)

/-- The reversal, as a permutation. -/
def revPerm : Perm D := Function.Involutive.toPerm M.rev M.rev_rev

/-- The rotation, as a permutation. -/
noncomputable def rotPerm : Perm D :=
  Equiv.ofBijective M.rot (Finite.injective_iff_bijective.1 M.rot_injective)

@[simp] lemma revPerm_apply (d : D) : revPerm M d = M.rev d := rfl

@[simp] lemma rotPerm_apply (d : D) : rotPerm M d = M.rot d := rfl

lemma rotPerm_mul_revPerm (d : D) : (rotPerm M * revPerm M) d = M.next d := by
  simp [CombMap.rot, M.rev_rev]

lemma revPerm_isInv : IsInv (revPerm M) := ⟨M.rev_rev, M.rev_ne⟩

variable {M}

lemma iterate_rotPerm (d : D) (n : ℕ) : (rotPerm M)^[n] d = M.rot^[n] d := rfl

lemma iterate_nextPerm (d : D) (n : ℕ) : (rotPerm M * revPerm M)^[n] d = M.next^[n] d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, iterate_succ_apply, ← ih, rotPerm_mul_revPerm]

lemma tail_rot_iterate (d : D) (n : ℕ) : M.tail (M.rot^[n] d) = M.tail d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, ih, M.tail_rot]

lemma face_next_iterate (d : D) (n : ℕ) : M.face (M.next^[n] d) = M.face d := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, ih, M.face_next]

lemma sameCycle_rotPerm (hrot : M.RotTrans) {d d' : D} :
    (rotPerm M).SameCycle d d' ↔ M.tail d = M.tail d' := by
  rw [sameCycle_iff]
  constructor
  · rintro ⟨n, rfl⟩; rw [iterate_rotPerm, tail_rot_iterate]
  · intro h; exact hrot d d' h

lemma sameCycle_nextPerm (hface : M.FaceTrans) {d d' : D} :
    (rotPerm M * revPerm M).SameCycle d d' ↔ M.face d = M.face d' := by
  rw [sameCycle_iff]
  constructor
  · rintro ⟨n, rfl⟩; rw [iterate_nextPerm, face_next_iterate]
  · intro h; obtain ⟨n, hn⟩ := hface d d' h; exact ⟨n, by rw [iterate_nextPerm, hn]⟩

lemma tail_surjective (hM : M.IsPlane) (hD : Nonempty D) : Surjective M.tail := by
  intro v
  obtain ⟨d₀⟩ := hD
  rcases (hM.conn v (M.tail d₀)).cases_head with h | ⟨b, ⟨e, he, -⟩, -⟩
  · exact ⟨d₀, h.symm⟩
  · exact ⟨e, he⟩

lemma face_surjective (hM : M.IsPlane) (hD : Nonempty D) : Surjective M.face := by
  intro v
  obtain ⟨d₀⟩ := hD
  rcases (hM.dualConn v (M.face d₀)).cases_head with h | ⟨b, ⟨e, he, -⟩, -⟩
  · exact ⟨d₀, h.symm⟩
  · exact ⟨e, he⟩

lemma card_image_eq_of_iff {β γ : Type*} [DecidableEq β] [DecidableEq γ] [Fintype γ]
    {f : D → β} {g : D → γ} (h : ∀ x y, f x = f y ↔ g x = g y) (hg : Surjective g) :
    (univ.image f).card = Fintype.card γ := by
  classical
  rw [le_antisymm (card_image_le_of_fiber fun x _ y _ e => (h x y).2 e)
    (card_image_le_of_fiber fun x _ y _ e => (h x y).1 e)]
  rw [image_univ_of_surjective hg, card_univ]

/-- **A plane map with transitive rotations and faces is a connected submap with zero Euler
gap.** -/
theorem gap_rot_eq_zero (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hD : Nonempty D) :
    (∀ x y, Conn (revPerm M) (rotPerm M) x y) ∧ gap (revPerm M) (rotPerm M) univ = 0 := by
  classical
  have hconn : ∀ x y, Conn (revPerm M) (rotPerm M) x y := by
    have key : ∀ a b, ReflTransGen M.Adj a b → ∀ x y, M.tail x = a → M.tail y = b →
        Conn (revPerm M) (rotPerm M) x y := by
      intro a b h
      induction h with
      | refl =>
        intro x y hx hy
        exact conn_of_sameCycle ((sameCycle_rotPerm hrot).2 (hx.trans hy.symm))
      | tail _ hst ih =>
        obtain ⟨e, he, rfl⟩ := hst
        intro x y hx hy
        refine (ih x e hx he).trans ((conn_inv (ι := revPerm M) e).trans ?_)
        exact conn_of_sameCycle ((sameCycle_rotPerm hrot).2 (by rw [revPerm_apply, hy]; rfl))
    exact fun x y => key _ _ (hM.conn (M.tail x) (M.tail y)) x y rfl rfl
  refine ⟨hconn, ?_⟩
  obtain ⟨d₀⟩ := hD
  have hc := comp_eq_one (revPerm_isInv M) (mem_univ d₀) (fun x _ y _ => hconn x y)
  have hV : nOrb (rotPerm M) univ = Fintype.card V :=
    card_image_eq_of_iff (fun x y => by rw [cls_eq_iff, sameCycle_rotPerm hrot])
      (tail_surjective hM ⟨d₀⟩)
  have hF : nOrb (rotPerm M * revPerm M) univ = Fintype.card F :=
    card_image_eq_of_iff (fun x y => by rw [cls_eq_iff, sameCycle_nextPerm hface])
      (face_surjective hM ⟨d₀⟩)
  have he := hM.euler
  obtain ⟨k, hk⟩ := even_card (revPerm_isInv M) (B := univ) (fun _ _ => mem_univ _)
  unfold gap eul
  rw [hc, hV, hF, card_univ]
  rw [card_univ] at hk
  omega

end Root

end Orbit

end PlanarFlow
