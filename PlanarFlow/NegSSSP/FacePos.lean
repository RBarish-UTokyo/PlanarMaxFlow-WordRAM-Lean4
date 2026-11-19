module

public import PlanarFlow.NegSSSP.FaceSplit

/-!
# The face of the one-face instance of a side, along the cycle

`PlanarFlow.NegSSSP.side_oneFace` gives, for a side `W` of the stellar subdivision of the piece
map bounded by a simple cycle `C`, a one-face instance (`OneFace`) whose face is the boundary walk
of the disc of `W` along `C` (`exists_disc_faceCycle`). Here the face is exposed: it is the cycle
`C` or its reverse, oriented with `W` on the inner side (`Out W` on every dart), so that the
positions of the sources on the face, as `cornerProg_face` takes them, are their positions along
that cycle.

* `exists_disc_faceCycle_out`: the face `g` of the disc is `C'` dart by dart, `C'` being `C` or
  its reverse (same darts, same length, every dart `Out W`).
* `side_faceInst`: the one-face instance of `side_oneFace` with its face `g` along `C'`: a vertex
  `v` with `ψ v` at position `i` of `C'` has `Q.tail (g i) = j v` (the position hypothesis of
  `cornerProg_face`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW

universe u v w

section Disc

variable {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] {M : Map X P}
variable {C : M.SCycle} {Z : Finset M.Face}

/-- **The face of the disc of `Z` along the cycle `C`, oriented**: it is, dart by dart, the cycle
`C` or its reverse `C'` (same darts, same length), every dart of `C'` lying outside `Z` with its
reverse inside. -/
theorem exists_disc_faceCycle_out (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) :
    ∃ C' : M.SCycle, C'.k = C.k ∧ (∀ d, C'.Mem d ↔ C.Mem d) ∧ (∀ i < C.k, Out Z (C'.d i)) ∧
      (∀ v ∈ C.verts, ∃ i < C.k, M.vert (C'.d i) = v) ∧
      ∃ g : ℕ → SDart (discDarts M Z), MSSP.FaceCycle (discMap M Z) C.k g ∧
        ∀ i < C.k, (g i).1 = C'.d i := by
  by_cases h : Out Z (C.d 0)
  · obtain ⟨g, hg, hgv⟩ := faceCycle_of_out hl hbd C.pos h
    exact ⟨C, rfl, fun _ => Iff.rfl, out_all hbd C.pos h, fun v hv => C.mem_verts.1 hv,
      g, hg, hgv⟩
  · have hm : C.Mem (C.d 0) := ⟨0, C.pos, Or.inl rfl⟩
    have hb := (hbd (C.d 0)).not.2 (not_not.2 hm)
    have hout : Out Z ((SCycleRv.rv C).d (C.k - 1)) := by
      rw [SCycleRv.rv_d, show C.k - 1 - (C.k - 1) = 0 by omega, Out, M.α_α]
      unfold Out at h
      tauto
    have hbd' : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ (SCycleRv.rv C).Mem d :=
      fun d => by rw [SCycleRv.rv_mem]; exact hbd d
    have hk1 : C.k - 1 < (SCycleRv.rv C).k := by
      show C.k - 1 < C.k
      have := C.pos; omega
    obtain ⟨g, hg, hgv⟩ := faceCycle_of_out hl hbd' hk1 hout
    exact ⟨SCycleRv.rv C, rfl, fun _ => SCycleRv.rv_mem C, out_all hbd' hk1 hout,
      fun v hv => SCycleRv.rv_verts C hv, g, hg, hgv⟩

end Disc

section Side

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

set_option maxHeartbeats 1000000 in
/-- **The one-face instance of a side with its face along the cycle.** As `side_oneFace`, and the
face `g` of the instance runs along `C'`, the cycle `C` or its reverse (every dart `Out W`): a
vertex `v` with `ψ v` the vertex of `C'` at position `i < C.k` is the tail `Q.tail (g i) = j v`
of the `i`-th dart of the face. -/
theorem side_faceInst (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {C : (kst N K).SCycle} {W : Finset (kst N K).Face}
    (hbd : ∀ δ, ((kst N K).face δ ∈ W ↔ (kst N K).face ((kst N K).α δ) ∈ W) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, b ∈ verts N (side N K W) ∧ Sum.inl (ψ b) ∈ C.verts)
    {R : Finset D} (hR : Disjoint (verts N R) (verts N K)) :
    ∃ C' : (kst N K).SCycle, C'.k = C.k ∧ (∀ δ, C'.Mem δ ↔ C.Mem δ) ∧
      (∀ i < C.k, Out W (C'.d i)) ∧
      ∃ (DQ VQ FQ : Type u) (_ : Fintype DQ) (_ : DecidableEq DQ) (_ : Fintype VQ)
        (_ : DecidableEq VQ) (_ : Fintype FQ) (_ : DecidableEq FQ) (Q : CombMap DQ VQ FQ)
        (g : ℕ → DQ) (P' : Finset D) (e : D → DQ) (j : V → VQ),
        FaceInst N (side N K W ∪ R) Bs (18 * K.card) C.k Q g P' e j ∧
        ∀ i < C.k, ∀ v, (kst N K).vert (C'.d i) = .inl (ψ v) → Q.tail (g i) = j v := by
  classical
  have hS := kmap_isPlane hM hrot hface hK0 hK
  have hl := kmap_loopless hrot hKr
  have hl' := stellar_loopless hl
  obtain ⟨C', hk', hmem', hout', hCv, g, hg, hgC⟩ := exists_disc_faceCycle_out hl' hbd
  set Q := discMap (kst N K) W with hQ
  set e : D → SDart (discDarts (kst N K) W) := fun d =>
    if h : ∃ h' : d ∈ rcl N K, (kst N K).face (old ⟨d, h'⟩) ∈ W then
      ⟨old ⟨d, h.1⟩, mem_discDarts.2 (Or.inl h.2)⟩ else g 0 with he
  set j : V → SVert (dσ (kst N K) W) (discDarts (kst N K) W) := fun v =>
    if h : ∃ x : SDart (discDarts (kst N K) W), (kst N K).vert x.1 = .inl (ψ v) then
      Q.tail h.choose else Q.tail (g 0) with hj
  have hjx : ∀ v (x : SDart (discDarts (kst N K) W)), (kst N K).vert x.1 = .inl (ψ v) →
      j v = Q.tail x := by
    intro v x hx
    have h : ∃ x : SDart (discDarts (kst N K) W), (kst N K).vert x.1 = .inl (ψ v) := ⟨x, hx⟩
    simp only [hj, h, ↓reduceDIte]
    exact discMap_tail_eq_iff.2 (h.choose_spec.trans hx.symm)
  have hed : ∀ d (hd : d ∈ side N K W), (e d).1 = old ⟨d, (mem_side.1 hd).2.1⟩ := by
    intro d hd
    have h := (mem_side.1 hd).2
    simp only [he, h, ↓reduceDIte]
  have hwit : ∀ v ∈ verts N (side N K W), ∃ x : SDart (discDarts (kst N K) W),
      (kst N K).vert x.1 = .inl (ψ v) := by
    intro v hv
    obtain ⟨d, hd, hdv⟩ := mem_verts_iff'.1 hv
    obtain ⟨⟨δ, hδ, hδv⟩, ⟨δ', hδ', hδv'⟩⟩ := side_vert hψ hd
    rcases hdv with rfl | rfl
    · exact ⟨⟨δ, mem_discDarts.2 (Or.inl hδ)⟩, hδv⟩
    · exact ⟨⟨δ', mem_discDarts.2 (Or.inl hδ')⟩, hδv'⟩
  have hvK : verts N (side N K W) ⊆ verts N K := verts_mono (side_subset W)
  have hBsub : verts N (side N K W) ∪ Bs = verts N (side N K W) :=
    union_eq_left.2 fun b hb => (hBs b hb).1
  refine ⟨C', hk', hmem', hout', _, _, _, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, Q, g, side N K W, e, j, ?_,
    fun i hi v hv => (hjx v (g i) (by rw [hgC i hi]; exact hv)).symm⟩
  refine
    { plane := discMap_isPlane (isPlane_stellar hS) hbd
      rot := discMap_rotTrans
      face := discMap_faceTrans
      cycle := hg
      card := ?_
      sub := subset_union_left
      closed := ?_
      injE := ?_
      injJ := ?_
      tail := ?_
      head := ?_
      src := ?_ }
  · have h1 : Fintype.card (SVert (dσ (kst N K) W) (discDarts (kst N K) W)) ≤
        Fintype.card (SDart (discDarts (kst N K) W)) :=
      Fintype.card_le_of_surjective _ Quotient.mk_surjective
    have h2 : Fintype.card (SFace (dσ (kst N K) W) (discDarts (kst N K) W)
        (revPerm (combOfSep (kst N K)))) ≤ Fintype.card (SDart (discDarts (kst N K) W)) :=
      Fintype.card_le_of_surjective _ Quotient.mk_surjective
    have h3 : Fintype.card (SDart (discDarts (kst N K) W)) ≤ 6 * K.card := by
      rw [Fintype.card_coe]
      refine (card_le_univ _).trans ?_
      rw [StDart.card, Fintype.card_coe]
      have := card_rcl_le (N := N) K
      omega
    omega
  · intro d hd ht
    rcases mem_union.1 hd with hd | hd
    · exact hd
    · rw [hBsub] at ht
      exact absurd (hvK ht) (disjoint_left.1 hR (tail_mem_verts hd))
  · intro d₁ hd₁ d₂ hd₂ h
    have := congrArg Subtype.val h
    rw [hed d₁ hd₁, hed d₂ hd₂] at this
    exact congrArg Subtype.val (StDart.old.inj this)
  · rw [← coe_union, hBsub]
    intro v hv w hw h
    obtain ⟨x, hx⟩ := hwit v hv
    obtain ⟨y, hy⟩ := hwit w hw
    rw [hjx v x hx, hjx w y hy, discMap_tail_eq_iff, hx, hy] at h
    exact kψ_inj hrot hψ (hvK hv) (hvK hw) (Sum.inl.inj h)
  · intro d hd
    symm
    refine hjx _ _ ?_
    rw [hed d hd, stellar_vert_old, hψ ⟨d, _⟩]
  · intro d hd
    symm
    refine hjx _ (Q.rev (e d)) ?_
    show (kst N K).vert ((kst N K).α (e d).1) = _
    rw [hed d hd, stellar_α, stα_old, stellar_vert_old, ← hψ, pieceSep_α, tail_rev]
  · intro b hb
    obtain ⟨i, hi, hgi⟩ := hCv _ (hBs b hb).2
    exact ⟨i, hi, (hjx b (g i) (by rw [hgC i hi]; exact hgi)).symm⟩

end Side

end NegSSSP

end PlanarFlow
