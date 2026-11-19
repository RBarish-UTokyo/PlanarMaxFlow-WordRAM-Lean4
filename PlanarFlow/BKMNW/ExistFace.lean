module

public import PlanarFlow.BKMNW.Exist

/-!
# The faces of the piece maps of a triangulation

Miller's theorem is applied to the piece maps (the pieces of the decomposition, their holes
contracted, `PlanarFlow.BKMNW.PieceInv`), which are not triangulations: the darts between two
vertices of a hole are left out, which merges faces. This file shows that on a triangulation
the faces of every piece map stay of one of two kinds (`FOK`):

* **small**: the face of `x` lies in `{x, φ x, φ⁻¹ x}` for the face walk `φ = σ * ι` (at most
  three darts), or
* **around a hole**: every dart of the face has an end in one hole.

Main results:

* `FOK.contract`: contracting edges keeps the faces small or around a hole (the faces of the
  contraction are the faces cut down to the remaining darts).
* `pface_ret_of_subset`: deleting darts outside the face of `x` does not change it.
* `FOK.child`: **the child piece maps of a split keep the property**, when the child is given by a
  set of vertices off the new hole (its darts those with an end in the set). A face of the child is
  a face of the parent with the darts of the separator removed, or is glued from such faces at the
  new hole, along darts left out of the child; then every dart of it has an end in the new hole.

A face around a hole with at least four darts meets the hole twice, which makes the hole a cut
vertex of the piece map (`PlanarSeparator.Map.not_reach_of_face_twice`). So the piece maps whose
holes are not cut vertices have small faces only, and their stellar subdivisions are triangulations
on which the passages of a cycle through the centre of a face can be replaced by an edge of the
face.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- The face of a dart `x` of a piece map with rotation `σ` on the darts `B`: the darts of `B` in
the orbit of `x` under the face walk `σ * ι`. -/
noncomputable def pface (σ : Perm D) (B : Finset D) (x : D) : Finset D :=
  B.filter fun y => (σ * revPerm M).SameCycle x y

lemma mem_pface {σ : Perm D} {B : Finset D} {x y : D} :
    y ∈ pface M σ B x ↔ y ∈ B ∧ (σ * revPerm M).SameCycle x y := mem_filter

lemma pface_eq_of_mem {σ : Perm D} {B : Finset D} {x y : D} (hy : y ∈ pface M σ B x) :
    pface M σ B y = pface M σ B x := by
  ext z
  simp only [mem_pface]
  have := (mem_pface.1 hy).2
  exact and_congr_right fun _ => ⟨fun h => this.trans h, fun h => this.symm.trans h⟩

lemma self_mem_pface {σ : Perm D} {B : Finset D} {x : D} (hx : x ∈ B) : x ∈ pface M σ B x :=
  mem_pface.2 ⟨hx, Perm.SameCycle.refl _ _⟩

variable (M) in
/-- **The faces of a piece map are small or run around a hole**: the face of every dart `x` lies
in `{x, φ x, φ⁻¹ x}` for the face walk `φ` (it has at most three darts), or every dart of it has
an end in a hole. -/
def FOK (σ : Perm D) (B : Finset D) (Hs : List (Finset V)) : Prop :=
  ∀ x ∈ B, (∀ z ∈ pface M σ B x, z = x ∨ z = (σ * revPerm M) x ∨ z = (σ * revPerm M).symm x) ∨
    ∃ H ∈ Hs, ∀ z ∈ pface M σ B x, M.tail z ∈ H ∨ M.head z ∈ H

lemma con_mul_rev (σ : Perm D) (A : Finset D) :
    con (revPerm M) σ A * revPerm M = ret (σ * revPerm M) A := by
  unfold con; rw [mul_assoc, (revPerm_isInv M).mul_self, mul_one]

/-- **Contracting edges keeps the faces small or around a hole**: the faces of the contraction are
those of the map, cut down to the remaining darts. -/
lemma FOK.contract {σ : Perm D} {B A : Finset D} {Hs : List (Finset V)} (h : FOK M σ B Hs)
    (hA : A ⊆ B) : FOK M (Orbit.con (revPerm M) σ A) A Hs := by
  intro x hx
  have e : ∀ y, y ∈ pface M (Orbit.con (revPerm M) σ A) A x ↔ y ∈ A ∧ y ∈ pface M σ B x := by
    intro y
    simp only [mem_pface, con_mul_rev]
    constructor
    · rintro ⟨hy, hc⟩; exact ⟨hy, hA hy, (sameCycle_ret hx hy).1 hc⟩
    · rintro ⟨hy, -, hc⟩; exact ⟨hy, (sameCycle_ret hx hy).2 hc⟩
  rcases h x (hA hx) with hs | ⟨H, hH, hal⟩
  · left
    intro z hz
    obtain ⟨hzA, hz'⟩ := (e z).1 hz
    rw [con_mul_rev]
    rcases hs z hz' with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (ret_eq_self_of hx hzA).symm)
    · refine Or.inr (Or.inr ?_)
      have : ret (σ * revPerm M) A ((σ * revPerm M).symm x) = x := by
        rw [ret_eq_self_of hzA (by rw [Equiv.apply_symm_apply]; exact hx),
          Equiv.apply_symm_apply]
      exact ((Equiv.symm_apply_eq _).2 this.symm).symm
  · exact Or.inr ⟨H, hH, fun z hz => hal z ((e z).1 hz).2⟩

/-- The vertices of the piece map with the separator contracted, before the darts outside the
child are deleted: the vertices of `M` with the holes of the children contracted. -/
lemma PieceInv.con_vert {P : Finset D} {Hs : List (Finset V)} {σ : Perm D}
    (h : PieceInv M P Hs σ) (hd : Hs.Pairwise Disjoint) {ρ : HPath M} (hρ : ρ.Simple Hs)
    (hρP : ∀ e ∈ ρ.darts, e ∈ pdarts M P Hs) :
    ∀ x ∈ pdarts M P Hs \ ρ.darts.toFinset, ∀ y ∈ pdarts M P Hs \ ρ.darts.toFinset,
      (Orbit.con (revPerm M) σ (pdarts M P Hs \ ρ.darts.toFinset)).SameCycle x y ↔
        HRel (childHoles Hs ρ.mverts) (M.tail x) (M.tail y) := by
  have hB := stable_pdarts h.rev Hs
  have hR : ∀ x ∈ pdarts M P Hs, ∀ y ∈ pdarts M P Hs, σ.SameCycle x y ↔
      (vmap M (cls Hs)).tail x = (vmap M (cls Hs)).tail y := fun x hx y hy => by
    rw [h.vert x hx y hy]; exact hRel_iff_cls hd
  obtain ⟨-, hsc⟩ := sameCycle_con_path (ρ.toQ Hs hd hρ) h.stable hB hρP hR
    (fun _ _ _ => eq_comm)
  have hsc' : ∀ x ∈ pdarts M P Hs \ ρ.darts.toFinset, ∀ y ∈ pdarts M P Hs \ ρ.darts.toFinset,
      (Orbit.con (revPerm M) σ (pdarts M P Hs \ ρ.darts.toFinset)).SameCycle x y ↔
        cls Hs (M.tail x) = cls Hs (M.tail y) ∨ (cls Hs (M.tail x) ∈ (ρ.toQ Hs hd hρ).verts ∧
          cls Hs (M.tail y) ∈ (ρ.toQ Hs hd hρ).verts) := hsc
  intro x hx y hy
  rw [hsc' x hx y hy, hRel_childHoles, hRel_iff_cls hd, HPath.cls_mem_toQ_verts,
    HPath.cls_mem_toQ_verts]

/-- A step of the face walk after deleting darts is a step before deleting them, when it lands on
a remaining dart. -/
lemma ret_mul_rev_eq {τ : Perm D} {Bc : Finset D} (hBc : Stable (revPerm M) Bc) {y : D}
    (hy : y ∈ Bc) (h : (τ * revPerm M) y ∈ Bc) :
    (ret τ Bc * revPerm M) y = (τ * revPerm M) y := by
  simp only [Perm.mul_apply] at h ⊢
  exact ret_eq_self_of (hBc y hy) h

/-- **A face all of whose darts remain is a face after deleting the other darts.** -/
lemma pface_ret_of_subset {τ : Perm D} {A Bc : Finset D} (hτA : Stable (τ * revPerm M) A)
    (hBcA : Bc ⊆ A) (hBc : Stable (revPerm M) Bc) {x : D} (hx : x ∈ Bc)
    (hsub : pface M τ A x ⊆ Bc) : pface M (ret τ Bc) Bc x = pface M τ A x := by
  have hit : ∀ n, (ret τ Bc * revPerm M)^[n] x = (τ * revPerm M)^[n] x ∧
      (τ * revPerm M)^[n] x ∈ pface M τ A x := by
    intro n
    induction n with
    | zero => exact ⟨rfl, self_mem_pface (hBcA hx)⟩
    | succ n ih =>
      obtain ⟨e, hm⟩ := ih
      have hm' : (τ * revPerm M)^[n + 1] x ∈ pface M τ A x := by
        refine mem_pface.2 ⟨?_, sameCycle_iterate _ _ _⟩
        rw [iterate_succ_apply']
        exact hτA _ (mem_pface.1 hm).1
      refine ⟨?_, hm'⟩
      rw [iterate_succ_apply', iterate_succ_apply', e]
      refine ret_mul_rev_eq hBc (hsub hm) ?_
      rw [← iterate_succ_apply' (τ * revPerm M)]; exact hsub hm'
  ext y
  simp only [mem_pface]
  constructor
  · rintro ⟨hy, hc⟩
    obtain ⟨n, rfl⟩ := sameCycle_iff.1 hc
    rw [(hit n).1]; exact ⟨hBcA ((hit n).1 ▸ hy), sameCycle_iterate _ _ _⟩
  · rintro ⟨hy, hc⟩
    obtain ⟨n, rfl⟩ := sameCycle_iff.1 hc
    rw [← (hit n).1]
    exact ⟨(hit n).1 ▸ hsub (hit n).2, sameCycle_iterate _ _ _⟩

lemma HPath.rev_mem_darts (ρ : HPath M) {e : D} (he : e ∈ ρ.darts) : M.rev e ∈ ρ.darts := by
  obtain ⟨j, hj, rfl | rfl⟩ := ρ.mem_darts.1 he
  · exact ρ.mem_darts.2 ⟨j, hj, Or.inr rfl⟩
  · rw [M.rev_rev]; exact ρ.mem_darts.2 ⟨j, hj, Or.inl rfl⟩

lemma stable_pdarts_sdiff {P : Finset D} {Hs : List (Finset V)} (hP : RevClosed M P)
    (ρ : HPath M) : Stable (revPerm M) (pdarts M P Hs \ ρ.darts.toFinset) := fun d hd => by
  rw [mem_sdiff, List.mem_toFinset] at hd ⊢
  refine ⟨stable_pdarts hP Hs d hd.1, fun h => hd.2 ?_⟩
  have := ρ.rev_mem_darts h; rwa [revPerm_apply, M.rev_rev] at this

/-- **The faces of a child piece map are small or run around a hole**, if those of its parent
are. The child is given by a set `Lv` of vertices off the new hole, closed under the relation of
the holes of the children, such that the darts of the child piece map are the remaining darts with
an end in `Lv`, and every dart off the new hole has both ends in `Lv` or none. A face of the child
piece map either is a face of the parent piece map (with the darts of the separator removed), or
is glued from such faces along darts left out of the child; then every dart of it has an end in the
new hole. -/
theorem FOK.child {P Pc : Finset D} {Hs : List (Finset V)} {σ : Perm D}
    (h : PieceInv M P Hs σ) (hd : Hs.Pairwise Disjoint) {ρ : HPath M} (hρ : ρ.Simple Hs)
    (hρP : ∀ e ∈ ρ.darts, e ∈ pdarts M P Hs) (hF : FOK M σ (pdarts M P Hs) Hs)
    (hrev : RevClosed M Pc)
    (hsub : pdarts M Pc (childHoles Hs ρ.mverts) ⊆ pdarts M P Hs \ ρ.darts.toFinset)
    {Lv : Finset V} (hLvc : ∀ a ∈ Lv, ∀ b, HRel (childHoles Hs ρ.mverts) a b → b ∈ Lv)
    (hcomp : ∀ d ∈ pdarts M P Hs, M.tail d ∉ newHole Hs ρ.mverts →
      M.head d ∉ newHole Hs ρ.mverts → (M.tail d ∈ Lv ↔ M.head d ∈ Lv))
    (hBc : ∀ d ∈ pdarts M P Hs \ ρ.darts.toFinset,
      d ∈ pdarts M Pc (childHoles Hs ρ.mverts) ↔ (M.tail d ∈ Lv ∨ M.head d ∈ Lv)) :
    FOK M (childRot M σ (pdarts M P Hs) ρ.darts (pdarts M Pc (childHoles Hs ρ.mverts)))
      (pdarts M Pc (childHoles Hs ρ.mverts)) (childHoles Hs ρ.mverts) := by
  set A := pdarts M P Hs \ ρ.darts.toFinset with hA
  set Bc := pdarts M Pc (childHoles Hs ρ.mverts) with hBcdef
  set τ := Orbit.con (revPerm M) σ A with hτ
  have hFA : FOK M τ A Hs := hF.contract sdiff_subset
  have hcls := h.con_vert hd hρ hρP
  have hAι : Stable (revPerm M) A := stable_pdarts_sdiff h.rev ρ
  have hτA : Stable τ A := stable_con (revPerm_isInv M) hAι
  have hψA : Stable (τ * revPerm M) A := hτA.mul hAι
  have hBcι : Stable (revPerm M) Bc := stable_pdarts hrev _
  have hcr : childRot M σ (pdarts M P Hs) ρ.darts Bc = ret τ Bc := rfl
  have hnext : ∀ z ∈ A, HRel (childHoles Hs ρ.mverts) (M.head z)
      (M.tail ((τ * revPerm M) z)) := fun z hz => by
    have := (hcls (M.rev z) (hAι z hz) (τ (M.rev z)) (hτA _ (hAι z hz))).1 ⟨1, by simp [hτ, hA]⟩
    simpa [Perm.mul_apply] using this
  -- a dart of the child off the new hole whose contracted face does not lie in the child
  have key : ∀ z ∈ Bc, M.tail z ∉ newHole Hs ρ.mverts → M.head z ∉ newHole Hs ρ.mverts →
      pface M τ A z ⊆ Bc := by
    intro z hz ht hh
    have hzA := hsub hz
    have hzP : z ∈ pdarts M P Hs := (mem_sdiff.1 hzA).1
    have hlv : M.tail z ∈ Lv ∧ M.head z ∈ Lv := by
      have h1 := (hBc z hzA).1 hz
      have h2 := hcomp z hzP ht hh
      tauto
    intro w hw
    have hwA := (mem_pface.1 hw).1
    refine (hBc w hwA).2 ?_
    rcases hFA z hzA with hs | ⟨H, hH, hal⟩
    · rcases hs w hw with rfl | rfl | rfl
      · exact Or.inl hlv.1
      · exact Or.inl (hLvc _ hlv.2 _ (hnext z hzA))
      · right
        have := hnext _ hwA
        rw [Equiv.apply_symm_apply] at this
        exact hLvc _ hlv.1 _ (hRel_symm this)
    · by_cases hm : Disjoint H ρ.mverts
      · have hHch : H ∈ childHoles Hs ρ.mverts :=
          List.mem_append_left _ (List.mem_filter.2 ⟨hH, by simpa using hm⟩)
        obtain ⟨ez, hezH, hezL⟩ : ∃ e ∈ H, e ∈ Lv := by
          rcases hal z (self_mem_pface hzA) with h1 | h1
          · exact ⟨_, h1, hlv.1⟩
          · exact ⟨_, h1, hlv.2⟩
        rcases hal w hw with h1 | h1
        · exact Or.inl (hLvc _ hezL _ (Or.inr ⟨H, hHch, hezH, h1⟩))
        · exact Or.inr (hLvc _ hezL _ (Or.inr ⟨H, hHch, hezH, h1⟩))
      · exfalso
        have hsubH : H ⊆ newHole Hs ρ.mverts := fun v hv => mem_newHole.2 (Or.inr ⟨H, hH, hm, hv⟩)
        rcases hal z (self_mem_pface hzA) with h1 | h1
        · exact ht (hsubH h1)
        · exact hh (hsubH h1)
  intro x hx
  rw [hcr]
  by_cases hall : ∀ z ∈ pface M (ret τ Bc) Bc x, pface M τ A z ⊆ Bc
  · have hxs := hall x (self_mem_pface hx)
    have e := pface_ret_of_subset hψA hsub hBcι hx hxs
    rw [e]
    rcases hFA x (hsub hx) with hs | ⟨H, hH, hal⟩
    · left
      intro z hz
      rcases hs z hz with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (ret_mul_rev_eq hBcι hx (hxs hz)).symm)
      · refine Or.inr (Or.inr ?_)
        have h1 : (ret τ Bc * revPerm M) ((τ * revPerm M).symm x) = x := by
          rw [ret_mul_rev_eq hBcι (hxs hz) (by rw [Equiv.apply_symm_apply]; exact hx),
            Equiv.apply_symm_apply]
        exact ((Equiv.symm_apply_eq _).2 h1.symm).symm
    · obtain ⟨H', hH', hsub'⟩ := coarse_childHoles Hs ρ.mverts H hH
      refine Or.inr ⟨H', hH', fun z hz => ?_⟩
      rcases hal z hz with h1 | h1
      · exact Or.inl (hsub' h1)
      · exact Or.inr (hsub' h1)
  · push Not at hall
    obtain ⟨z₀, hz₀, hz₀n⟩ := hall
    refine Or.inr ⟨newHole Hs ρ.mverts, List.mem_append_right _ (List.mem_singleton_self _),
      fun z hz => ?_⟩
    by_contra hne
    push Not at hne
    have hzBc := (mem_pface.1 hz).1
    have hs := key z hzBc hne.1 hne.2
    have e := pface_ret_of_subset hψA hsub hBcι hzBc hs
    have hz₀' : z₀ ∈ pface M (ret τ Bc) Bc z := by rw [pface_eq_of_mem hz]; exact hz₀
    rw [e] at hz₀'
    exact hz₀n (by rw [pface_eq_of_mem hz₀']; exact hs)

end BKMNW

end PlanarFlow
