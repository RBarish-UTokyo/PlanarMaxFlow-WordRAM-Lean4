module

public import PlanarFlow.BKMNW.ExistGroup

/-!
# The invariant at the root of a map with pendant edges

For a plane map `M` with transitive rotations and faces all of whose faces are triangles, the map
`M.pendant e he` with a pendant edge at every vertex meets the invariant `CInv` at the root, with
the pendant vertices as `Q` (`cinv_pendant`): the core of the whole map is `M` itself, its
rotation the rotation of the map with the pendant edges cut down to the darts of `M`, and its faces
the faces of `M`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

lemma pdarts_nil {M : CombMap D V F} (P : Finset D) : pdarts M P [] = P := by
  ext d
  rw [mem_pdarts]
  simp [Inner]

variable (V) in
/-- The pendant vertices of a map with pendant edges. -/
def pendQ : Finset (V ⊕ V) := univ.image Sum.inr

@[simp] lemma inl_not_mem_pendQ (v : V) : Sum.inl v ∉ pendQ V := by simp [pendQ]

@[simp] lemma inr_mem_pendQ (v : V) : Sum.inr v ∈ pendQ V := by simp [pendQ]

section Pend

variable {M : CombMap D V F} {e : V → D} (he : ∀ v, M.tail (e v) = v)

/-- The core of the map with pendant edges: the darts of `M`. -/
lemma mem_core_pendant {x : D ⊕ (V × Bool)} :
    x ∈ core (M.pendant e he) (pendQ V) univ ↔ x.isLeft := by
  rw [mem_core]
  rcases x with d | ⟨v, _ | _⟩
  · have h1 : (M.pendant e he).tail (Sum.inl d) = Sum.inl (M.tail d) := rfl
    have h2 : (M.pendant e he).head (Sum.inl d) = Sum.inl (M.head d) := rfl
    simp [h1, h2]
  · have h1 : (M.pendant e he).tail (Sum.inr (v, false)) = Sum.inr v := rfl
    simp [h1]
  · have h1 : (M.pendant e he).head (Sum.inr (v, true)) = Sum.inr v := rfl
    simp [h1]

/-- **The faces of the core**: the rotation of the map with pendant edges cut down to the darts
of `M`, followed by the reversal, is the face permutation of `M`. -/
lemma ret_rot_pendant (d : D) :
    (ret (rotPerm (M.pendant e he)) (core (M.pendant e he) (pendQ V) univ) *
      revPerm (M.pendant e he)) (Sum.inl d) = Sum.inl (M.next d) := by
  set K := core (M.pendant e he) (pendQ V) univ
  have hK : ∀ t : D, (Sum.inl t : D ⊕ (V × Bool)) ∈ K := fun t =>
    (mem_core_pendant he).2 rfl
  rw [Perm.mul_apply, revPerm_apply, CombMap.pendant_rev_inl]
  have hrot : (rotPerm (M.pendant e he)) (Sum.inl (M.rev d)) =
      if M.next d = e (M.head d) then Sum.inr (M.head d, true) else Sum.inl (M.next d) := by
    rw [rotPerm_apply]
    show CombMap.pNext M e (CombMap.pRev M (Sum.inl (M.rev d))) = _
    simp [CombMap.pRev, CombMap.pNext, M.rev_rev]
  by_cases h : M.next d = e (M.head d)
  · simp only [h, ↓reduceIte] at hrot
    have h2 : (rotPerm (M.pendant e he))^[2] (Sum.inl (M.rev d)) = Sum.inl (M.next d) := by
      rw [Function.iterate_succ_apply', Function.iterate_one, hrot, rotPerm_apply, h]
      rfl
    rw [ret_eq_of (hK _) (n := 2) (by norm_num) (by rw [h2]; exact hK _)
      (fun m h0 h1 => by
        rw [show m = 1 by omega, Function.iterate_one, hrot, mem_core_pendant]
        simp), h2]
  · simp only [h, ↓reduceIte] at hrot
    rw [ret_eq_self_of (hK _) (by rw [hrot]; exact hK _), hrot]

/-- **The invariant at the root of a map with pendant edges** whose faces are triangles. -/
theorem cinv_pendant (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (htri : ∀ d, M.next (M.next (M.next d)) = d) :
    CInv (M.pendant e he) (pendQ V) univ [] := by
  set M' := M.pendant e he with hM'
  set K := core M' (pendQ V) univ with hK
  have hD : Nonempty D := ⟨e hM.nonempty.some⟩
  have hP' : M'.IsPlane := CombMap.pendant_isPlane he hM
  have hrot' : M'.RotTrans := CombMap.pendant_rotTrans he hrot
  have hface' : M'.FaceTrans := CombMap.pendant_faceTrans he hface
  have hroot := pieceInv_root hP' hrot' hface' ⟨Sum.inl hD.some⟩
  have hKrev : Stable (revPerm M') K := fun x hx =>
    revClosed_core (Q := pendQ V) (fun _ _ => mem_univ _) x hx
  have hKl : ∀ x ∈ K, ∃ d, x = Sum.inl d := fun x hx => by
    rcases x with d | x
    · exact ⟨d, rfl⟩
    · exact absurd ((mem_core_pendant he).1 hx) (by simp)
  have hinK : ∀ d : D, (Sum.inl d : D ⊕ (V × Bool)) ∈ K := fun d => (mem_core_pendant he).2 rfl
  refine ⟨by simp [hunion_nil'], ret (rotPerm M') K, ⟨revClosed_core (fun _ _ => mem_univ _),
    ?_, ?_, ?_⟩, ?_, ?_⟩ <;> try simp only [pdarts_nil]
  · exact stable_ret _ _
  · have h0 := hroot.gap
    rw [pdarts_univ_nil] at h0
    exact gap_ret_eq_zero (revPerm_isInv M') (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
      (subset_univ K) hKrev h0
  · intro x hx y hy
    rw [sameCycle_ret hx hy]
    exact hroot.vert x (by rw [pdarts_univ_nil]; exact mem_univ _) y
      (by rw [pdarts_univ_nil]; exact mem_univ _)
  · -- the faces are triangles
    intro x hx
    left
    intro z hz
    obtain ⟨d, rfl⟩ := hKl x hx
    set φ := ret (rotPerm M') K * revPerm M' with hφ
    have hit : ∀ n t, φ^[n] (Sum.inl t) = Sum.inl (M.next^[n] t) := by
      intro n
      induction n with
      | zero => intro t; rfl
      | succ n ih =>
        intro t
        rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
        exact ret_rot_pendant he _
    obtain ⟨n, rfl⟩ := sameCycle_iff.1 (mem_pface.1 hz).2
    have h3 : M.next^[3] d = d := htri d
    have hmod : M.next^[n] d = M.next^[n % 3] d := by
      conv_lhs => rw [← Nat.mod_add_div n 3]
      rw [Function.iterate_add_apply]
      congr 1
      induction n / 3 with
      | zero => rfl
      | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, h3, ih]
    rw [hit, hmod]
    have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases (n % 3)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (by rw [← Function.iterate_one φ, hit]))
    · refine Or.inr (Or.inr ((Equiv.eq_symm_apply _).2 ?_))
      have := hit 1 (M.next^[2] d)
      rw [Function.iterate_one] at this
      rw [this, ← Function.iterate_add_apply]
      exact congrArg Sum.inl h3
  · -- connected
    have hc := (pcOK_univ hM hrot hface (∅ : Finset V) ∅).conn
    unfold HConn
    simp only [pdarts_nil]
    intro x hx y hy
    obtain ⟨a, rfl⟩ := hKl x hx
    obtain ⟨b, rfl⟩ := hKl y hy
    have h := hc a (by rw [pdarts_univ_nil]; exact mem_univ _) b
      (by rw [pdarts_univ_nil]; exact mem_univ _)
    refine ReflTransGen.lift Sum.inl ?_ _ _ h
    intro s t hst
    refine ⟨hinK t, ?_⟩
    rcases hst.2 with h1 | h1
    · exact Or.inl (by rw [h1]; rfl)
    · rcases h1 with h1 | ⟨H, hH, -⟩
      · exact Or.inr (Or.inl (show (Sum.inl (M.tail s) : V ⊕ V) = Sum.inl (M.tail t) by
          rw [h1]))
      · simp at hH

end Pend

end BKMNW

end PlanarFlow
