module

public import PlanarFlow.BKMNW.SmXC

/-!
# The children's rotations over the whole parent piece (pure)

The rotation `st` of the core's piece map `B = pdarts (core Q P) Hs` is given only on `B`. To
compute a child's rotation `chRot` over **all** the darts of the parent record (the domain of
`crProg`), extend `st` by the identity outside `B`: the first return `ret st B` (on `B`, `st`
itself, `ret_stable_apply`). The child's rotation does not change (`childRot_ret`):

* `ret_congr_on`: first returns agree on a set stable under `π` where `π = π'` and `A`, `A'`
  agree;
* `ret_stable_apply`, **`childRot_ret`**: `childRot (ret st B) P L Bc = childRot st B L Bc`
  (`B ⊆ P` closed under `rev`, `st` stable on `B`, `Bc ⊆ B \ L`);
* `hpath_rev_mem` (the darts of a path through the holes are closed under `rev`),
  **`childBc_sub`** (`pdarts (core Q X) (childHoles Hs C) ⊆ pdarts (core Q P) Hs \ ρ.darts`),
  **`mem_childBc_iff`** (for `d ∈ P`: `d ∈ pdarts (core Q X) (childHoles Hs C) ↔
  d ∈ pdarts X (childHoles Hs C) ∧ d ∈ pdarts (core Q P) Hs`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit

section RetCongr

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **First returns agree** on a set `E` stable under `π`, where `π = π'` and `A`, `A'` agree. -/
lemma ret_congr_on {π π' : Perm α} {A A' E : Finset α} (hS : Stable π E)
    (h : ∀ z ∈ E, π z = π' z) (hA : ∀ z ∈ E, z ∈ A ↔ z ∈ A') {x : α} (hx : x ∈ E) :
    ret π A x = ret π' A' x := by
  have it := iterate_congr hS h hx
  by_cases hxA : x ∈ A
  · have hxA' : x ∈ A' := (hA x hx).1 hxA
    rw [ret_apply_of_mem hxA, ret_apply_of_mem hxA']
    have e : retIdx π A x = retIdx π' A' x := by
      apply le_antisymm
      · apply retIdx_le hxA (retIdx_pos x)
        refine (hA _ (hS.iterate hx _)).2 ?_
        rw [it]; exact iterate_retIdx_mem hxA'
      · apply retIdx_le hxA' (retIdx_pos x)
        rw [← it]
        exact (hA _ (hS.iterate hx _)).1 (iterate_retIdx_mem hxA)
    rw [e, it]
  · have hxA' : x ∉ A' := fun h' => hxA ((hA x hx).2 h')
    rw [ret_apply_of_not_mem hxA, ret_apply_of_not_mem hxA']

/-- On a stable set, the first return is the permutation itself. -/
lemma ret_stable_apply {st : Perm α} {B : Finset α} (h : Stable st B) {x : α} (hx : x ∈ B) :
    ret st B x = st x := by
  rw [ret_apply_of_mem hx]
  have : retIdx st B x = 1 :=
    le_antisymm (retIdx_le hx one_pos (by simpa using h x hx)) (retIdx_pos x)
  rw [this]; rfl

end RetCongr

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The child's rotation from the extension of `st` by the identity** (see the module
docstring). -/
theorem childRot_ret {st : Perm D} {B P : Finset D} {L : List D} {Bc : Finset D}
    (hst : Stable st B) (hBP : B ⊆ P) (hBr : ∀ x ∈ B, M.rev x ∈ B)
    (hBc : Bc ⊆ B \ L.toFinset) :
    childRot M (ret st B) P L Bc = childRot M st B L Bc := by
  set π1 : Perm D := ret (ret st B * revPerm M) (P \ L.toFinset) * revPerm M with hπ1
  set π2 : Perm D := ret (st * revPerm M) (B \ L.toFinset) * revPerm M with hπ2
  have hS0 : Stable (st * revPerm M) B := fun z hz => by
    rw [Perm.mul_apply, revPerm_apply]; exact hst _ (hBr z hz)
  have agree : ∀ z ∈ B, π2 z = π1 z := fun z hz => by
    rw [hπ1, hπ2, Perm.mul_apply, Perm.mul_apply, revPerm_apply]
    refine ret_congr_on hS0 (fun y hy => ?_) (fun y hy => ?_) (hBr z hz)
    · rw [Perm.mul_apply, Perm.mul_apply, revPerm_apply, ret_stable_apply hst (hBr y hy)]
    · simp only [mem_sdiff]
      exact ⟨fun h => ⟨hBP h.1, h.2⟩, fun h => ⟨hy, h.2⟩⟩
  have hS2 : Stable π2 B := fun z hz => by
    rw [hπ2, Perm.mul_apply, revPerm_apply]
    by_cases hm : M.rev z ∈ B \ L.toFinset
    · exact (mem_sdiff.1 (ret_mem hm)).1
    · rw [ret_apply_of_not_mem hm]; exact hBr z hz
  ext x
  unfold childRot con
  show ret π1 Bc x = ret π2 Bc x
  by_cases hx : x ∈ B
  · exact (ret_congr_on hS2 agree (fun _ _ => Iff.rfl) hx).symm
  · have hxc : x ∉ Bc := fun h => hx (mem_sdiff.1 (hBc h)).1
    rw [ret_apply_of_not_mem hxc, ret_apply_of_not_mem hxc]

/-- The darts of a path through the holes are closed under `rev`. -/
lemma hpath_rev_mem (ρ : HPath M) : ∀ x ∈ ρ.darts, M.rev x ∈ ρ.darts := fun x hx => by
  obtain ⟨j, hj, rfl | rfl⟩ := ρ.mem_darts.1 hx
  · exact ρ.mem_darts.2 ⟨j, hj, Or.inr rfl⟩
  · rw [M.rev_rev]; exact ρ.mem_darts.2 ⟨j, hj, Or.inl rfl⟩

/-- **The child's core piece map avoids the path and lies in the parent's.** -/
lemma childBc_sub {Q : Finset V} {P X : Finset D} {Hs : List (Finset V)} (ρ : HPath M)
    (hXP : X ⊆ P) :
    pdarts M (core M Q X) (childHoles Hs ρ.mverts) ⊆
      pdarts M (core M Q P) Hs \ ρ.darts.toFinset := by
  intro d hd'
  refine mem_sdiff.2 ⟨pdarts_childHoles_subset (core_mono hXP) hd', fun hdρ => ?_⟩
  rw [List.mem_toFinset] at hdρ
  obtain ⟨h1, h2⟩ := ρ.ends_mem hdρ
  exact (mem_pdarts.1 hd').2 ⟨newHole Hs ρ.mverts,
    List.mem_append_right _ (List.mem_singleton_self _), subset_newHole h1, subset_newHole h2⟩

/-- **The darts of the child's core piece map** among the darts of the parent's piece. -/
lemma mem_childBc_iff {Q : Finset V} {P X : Finset D} {Hs : List (Finset V)} {C : Finset V}
    (hXP : X ⊆ P) {d : D} :
    d ∈ pdarts M (core M Q X) (childHoles Hs C) ↔
      d ∈ pdarts M X (childHoles Hs C) ∧ d ∈ pdarts M (core M Q P) Hs := by
  constructor
  · intro h
    refine ⟨mem_pdarts.2 ⟨(mem_core.1 (mem_pdarts.1 h).1).1, (mem_pdarts.1 h).2⟩,
      pdarts_childHoles_subset (core_mono hXP) h⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨hdX, hin⟩ := mem_pdarts.1 h1
    obtain ⟨-, ht, hh⟩ := mem_core.1 (mem_pdarts.1 h2).1
    exact mem_pdarts.2 ⟨mem_core.2 ⟨hdX, ht, hh⟩, hin⟩

end MfDrv

end BKMNW

end PlanarFlow
