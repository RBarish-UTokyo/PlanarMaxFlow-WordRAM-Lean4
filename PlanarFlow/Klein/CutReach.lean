module

public import PlanarFlow.Klein.Run
public import PlanarFlow.BKMNW.CutBuild

/-!
# The roots of a cut reach the same vertices

The maximum-flow algorithm calls multiple-source shortest paths on the cut of the dual graph
minus a simple path (`PlanarFlow/BKMNW/CutBuild.lean`): a plane map whose piece consists of the
copies of the darts off the path and, for every root `t`, a pendant arc from `t` to the copy of
the face of `t`. This file shows that the hypothesis `PlanarFlow.Klein.SameReach` of the pivot
bound holds there, for every choice of lengths.

* `face_tour_reach`: the copies of the faces of `t` and of the next root `tour t` reach each
  other by copies of darts off the path (the same face when `t` lies on the path; otherwise the
  copy of `t` and of its reverse join them).
* `cutOf_sameReach`: **the roots of the cut reach the same vertices off the face**: a walk from a
  root leaves it by its pendant arc, and the copies of the faces of all the roots reach each other.
* `cut_hyp_sameReach`: **for every plane map with transitive rotations and faces and every simple
  path of at least one dart, the cut with the perturbed lengths meets `Hyp` and `SameReach`**: the
  pivot bound `PlanarFlow.Klein.klein_pivots` applies on the maps on which the maximum-flow
  algorithm calls multiple-source shortest paths (a non-trivial witness of both hypotheses).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP BKMNW Function

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

section Cut

variable {M : CombMap D V F} {L : List D} (hL : ∀ e ∈ L, M.rev e ∈ L) (ℓ' : CutD M L → ℤ)

local notation "𝒢" => pieceGraph (cutMap hL) (cutPiece M L) ℓ'

/-- The copy of a dart off the path, as an arc of the piece. -/
def copyArc (e : D) (he : e ∉ L) : {d // d ∈ cutPiece M L} :=
  ⟨.inl ⟨e, he⟩, by simp [mem_cutPiece, inPiece]⟩

/-- Two faces whose copies reach each other. -/
def Conn (a b : F) : Prop :=
  Reach 𝒢 (.inl a) (.inl b) ∧ Reach 𝒢 (.inl b) (.inl a)

lemma conn_trans {a b c : F} (h1 : Conn hL ℓ' a b) (h2 : Conn hL ℓ' b c) : Conn hL ℓ' a c :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

lemma copy_reach {e : D} (he : e ∉ L) :
    Reach 𝒢 (.inl (M.face e)) (.inl (M.face (M.rev e))) :=
  (Reach.refl (G := pieceGraph (cutMap hL) (cutPiece M L) ℓ') _).arc (a := copyArc e he)

/-- **The copies of the faces of consecutive roots reach each other.** -/
lemma face_tour_reach (t : CutT M L) :
    Conn hL ℓ' (M.face t.1) (M.face (tourT hL t).1) := by
  rw [tourT_val]
  by_cases ht : t.1 ∈ L
  · rw [tour_of_mem ht, M.face_next]; exact ⟨Reach.refl _, Reach.refl _⟩
  · rw [tour_of_not_mem ht, M.face_rot]
    refine ⟨copy_reach hL ℓ' ht, ?_⟩
    have := copy_reach hL ℓ' (rev_not_mem hL ht)
    rwa [M.rev_rev] at this

lemma face_iterate_reach (t0 : CutT M L) (n : ℕ) :
    Conn hL ℓ' (M.face t0.1) (M.face ((tourT hL)^[n] t0).1) := by
  induction n with
  | zero => exact ⟨Reach.refl _, Reach.refl _⟩
  | succ n ih => rw [iterate_succ_apply']; exact conn_trans hL ℓ' ih (face_tour_reach hL ℓ' _)

/-- A walk from a root that leaves it passes through the copy of the face of the root. -/
lemma reach_from_root {t : CutT M L} {v : CutV M L} (h : Reach 𝒢 (.inr t) v) (hv : v ≠ .inr t) :
    Reach 𝒢 (.inl (M.face t.1)) v := by
  obtain ⟨l, hl⟩ := h
  rcases l with _ | ⟨a, l⟩
  · exact absurd (LWalk.nil_iff.1 hl).symm hv
  obtain ⟨hsrc, hl'⟩ := LWalk.cons_iff.1 hl
  obtain ⟨d, hd⟩ := a
  rcases d with e | t' | t' | t' | t' <;> simp [mem_cutPiece, inPiece] at hd
  · exact absurd hsrc (by simp [pieceGraph, cutMap, cutTail])
  · have : t' = t := by simpa [pieceGraph, cutMap, cutTail] using hsrc
    subst this
    exact ⟨l, hl'⟩

/-- **The roots of the cut reach the same vertices off the face.** -/
theorem cutOf_sameReach (t0 : CutT M L) :
    SameReach (cutMap hL) (minimalPeriod (tourT hL) t0) (cutG hL t0) (cutPiece M L) ℓ' := by
  intro i _ j _ v hv hiv
  have hri : (cutMap hL).tail (cutG hL t0 i) = .inr ((tourT hL)^[i] t0) := rfl
  have hrj : (cutMap hL).tail (cutG hL t0 j) = .inr ((tourT hL)^[j] t0) := rfl
  rw [hri] at hiv
  rw [hrj]
  have hne : v ≠ .inr ((tourT hL)^[i] t0) := fun h => hv ⟨i, by assumption, by rw [hri, h]⟩
  have h1 := reach_from_root hL ℓ' hiv hne
  -- from the root `j` to the copy of its face, then to the copy of the face of `i`
  have hj : Reach 𝒢 (.inr ((tourT hL)^[j] t0)) (.inl (M.face ((tourT hL)^[j] t0).1)) :=
    (Reach.refl (G := pieceGraph (cutMap hL) (cutPiece M L) ℓ')
      ((pieceGraph (cutMap hL) (cutPiece M L) ℓ').src
        ⟨.inr (.inl ((tourT hL)^[j] t0)), by simp [mem_cutPiece, inPiece]⟩)).arc
  have hji : Conn hL ℓ' (M.face ((tourT hL)^[j] t0).1) (M.face ((tourT hL)^[i] t0).1) :=
    conn_trans hL ℓ' ⟨(face_iterate_reach hL ℓ' t0 j).2, (face_iterate_reach hL ℓ' t0 j).1⟩
      (face_iterate_reach hL ℓ' t0 i)
  exact hj.trans (hji.1.trans h1)

end Cut

/-- **On the maps on which the maximum-flow algorithm calls multiple-source shortest paths, the
hypotheses of the pivot bound hold**: for a plane map with transitive rotations and faces, a
simple path `P` of at least one dart and lengths nonnegative off the path, the cut along `P` with
the perturbed lengths meets `Hyp` and `SameReach`. -/
theorem cut_hyp_sameReach {M : CombMap D V F} (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) (P : SPath M) (ℓ : D → ℤ) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e)
    (hk : 0 < P.k) :
    ∃ C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts),
      Hyp C.map C.k C.g C.piece (pert C.len) ∧ SameReach C.map C.k C.g C.piece (pert C.len) := by
  have hL := P.rev_mem_darts'
  have horb : ∀ t, ItReach (tourT hL) ⟨P.d 0, tail_mem_cutS (P.d_mem 0 hk)⟩ t := by
    intro t
    obtain ⟨e, he, h⟩ := mem_cutS.1 t.2
    obtain ⟨i, hi, hi'⟩ := P.tail_mem_darts he
    obtain ⟨n, hn⟩ := tour_reach hrot P hk hi (h.symm.trans hi')
    exact ⟨n, Subtype.ext (by rw [tourT_iterate_val]; exact hn)⟩
  have htwo : tourT hL ⟨P.d 0, tail_mem_cutS (P.d_mem 0 hk)⟩ ≠
      ⟨P.d 0, tail_mem_cutS (P.d_mem 0 hk)⟩ := by
    intro h
    have h1 := congrArg Subtype.val h
    rw [tourT_val, tour_of_mem (P.d_mem 0 hk)] at h1
    have h2 := congrArg M.tail h1
    rw [M.tail_next, M.tail_rev, P.head_d 0 hk, P.tail_d 0 hk] at h2
    exact absurd (P.inj 1 hk 0 (Nat.zero_le _) h2) one_ne_zero
  have hcount : P.darts.toFinset.card + 2 = 2 * (cutS M P.darts).card := by
    rw [P.card_darts, P.card_cutS hk]; ring
  refine ⟨cutOf hL _ ℓ hnn hM hface horb htwo hcount, ?_, ?_⟩
  · exact (cutOf hL _ ℓ hnn hM hface horb htwo hcount).hyp.hyp
  · exact cutOf_sameReach hL _ _

/-- **The hypotheses of the pure pivot loop around a face hold on the cuts** on which the
maximum-flow algorithm calls multiple-source shortest paths (`klein_pure_pivots` applies there):
`Hyp`, `SameReach`, and a nonempty piece. -/
theorem cut_hyp_sameReach_nonempty {M : CombMap D V F} (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) (P : SPath M) (ℓ : D → ℤ) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e)
    (hk : 0 < P.k) :
    ∃ C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts),
      Hyp C.map C.k C.g C.piece (pert C.len) ∧ SameReach C.map C.k C.g C.piece (pert C.len) ∧
        C.piece.Nonempty := by
  obtain ⟨C, h1, h2⟩ := cut_hyp_sameReach hM hrot hface P ℓ hnn hk
  obtain ⟨d, hd, -⟩ := C.pend 0 (by have := h1.face.two_le; omega)
  exact ⟨C, h1, h2, d, hd⟩

end Klein

end PlanarFlow
