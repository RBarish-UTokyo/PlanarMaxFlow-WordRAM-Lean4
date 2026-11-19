module

public import PlanarFlow.NegSSSP.KEncPert
public import PlanarFlow.NegSSSP.FaceWalk

/-!
# The node run on the concrete one-face instances of the split

`PlanarFlow.NegSSSP.node_exec_valBy` runs one node of the negative-length recursion for **any**
one-face instances `fd₀`, `fd₁` of the two parts and any encodings meeting `FEncValBy`.
`side_faceInst` and `faceWalk_faceInst` only assert that a one-face instance of a side exists.
Here the instance of a side is a definition, the disc of the side in the stellar subdivision
`kst N K` of the piece map, its face started where the walk of `faceWalk` starts:

* `discCyc C Z`: the cycle `C` or its reverse, the one with `Z` on its inner side
  (`discCyc_k`, `discCyc_mem`, `discCyc_spec`).
* `discFace hbd i₀`: the face of the disc of `Z`, the darts of `discCyc C Z` from position
  `i₀` on.
* `sideFD …`: **the one-face instance of a side**, a `FaceData` of the part
  `X = side N K Z ∪ R` (`Q = discMap (kst N K) Z`, the face `discFace hbd i₀`, the darts
  `side N K Z`, explicit embeddings `sideE`, `sideJ`); `sideFD_pos`: a position `t` on the walk
  whose dart leaves the vertex `ψ v` of the piece map is a position of `v` on the face of the
  instance (the hypothesis of `cornerProg_face`).
* `faceWalk_side`: **`faceWalk` writes those positions**: from the plain encoding of the piece
  map and the marks of a side, the word written for a source `b` is a position `t` with the
  dart of the walk at `t` leaving `ψ b`, for the start `i₀` of the walk.
* `node_exec_side`: **`node_exec_valBy` with `fd₀`, `fd₁` the instances `sideFD` of the two
  sides** of a cut of the piece map (the parts `side N K Z ∪ R₀` and `side N K Zᶜ ∪ R₁`), the
  bounds `fd.q ≤ 18 m`, `fd.k² ≤ 1200 m` discharged from `K ⊆ P` and the length of the cycle,
  and the positions of the boundary vertices in the form `faceWalk_side` writes them.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW

universe u v w

/-! ### The cycle of the disc, oriented -/

section DiscCyc

variable {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P] [DecidableEq P] {M : Map X P}

open Classical in
/-- **The cycle `C` oriented with `Z` inside**: `C` if its first dart is `Out Z`, otherwise
its reverse. -/
noncomputable def discCyc (C : M.SCycle) (Z : Finset M.Face) : M.SCycle :=
  if Out Z (C.d 0) then C else SCycleRv.rv C

lemma discCyc_k (C : M.SCycle) (Z : Finset M.Face) : (discCyc C Z).k = C.k := by
  unfold discCyc; split_ifs <;> rfl

lemma discCyc_mem (C : M.SCycle) (Z : Finset M.Face) (d : X) :
    (discCyc C Z).Mem d ↔ C.Mem d := by
  unfold discCyc; split_ifs
  · exact Iff.rfl
  · exact SCycleRv.rv_mem C

/-- **The oriented cycle bounds the disc** (as `exists_disc_faceCycle_out`, for the cycle
`discCyc C Z`): every dart is `Out Z`, every vertex of `C` is a tail, and the darts are a face
of the disc. -/
theorem discCyc_spec {C : M.SCycle} {Z : Finset M.Face} (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) :
    (∀ i < C.k, Out Z ((discCyc C Z).d i)) ∧
      (∀ v ∈ C.verts, ∃ i < C.k, M.vert ((discCyc C Z).d i) = v) ∧
      ∃ g : ℕ → SDart (discDarts M Z), MSSP.FaceCycle (discMap M Z) C.k g ∧
        ∀ i < C.k, (g i).1 = (discCyc C Z).d i := by
  classical
  by_cases h : Out Z (C.d 0)
  · have e : discCyc C Z = C := by simp only [discCyc, h, ↓reduceIte]
    rw [e]
    obtain ⟨g, hg, hgv⟩ := faceCycle_of_out hl hbd C.pos h
    exact ⟨out_all hbd C.pos h, fun v hv => C.mem_verts.1 hv, g, hg, hgv⟩
  · have e : discCyc C Z = SCycleRv.rv C := by simp only [discCyc, h, ↓reduceIte]
    rw [e]
    have hm : C.Mem (C.d 0) := ⟨0, C.pos, Or.inl rfl⟩
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
    exact ⟨out_all hbd' hk1 hout, fun v hv => SCycleRv.rv_verts C hv, g, hg, hgv⟩

lemma discCyc_d_mem {C : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) (i : ℕ) :
    (discCyc C Z).d (i % C.k) ∈ discDarts M Z :=
  mem_discDarts_of_mem hbd ((discCyc_mem C Z _).1
    ⟨i % C.k, by rw [discCyc_k]; exact Nat.mod_lt _ C.pos, Or.inl rfl⟩)

/-- **The face of the disc of `Z` started at position `i₀`**: the darts of `discCyc C Z` from
`i₀` on, cyclically. -/
noncomputable def discFace {C : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) (i₀ : ℕ) :
    ℕ → SDart (discDarts M Z) :=
  fun t => ⟨(discCyc C Z).d ((i₀ + t) % C.k), discCyc_d_mem hbd (i₀ + t)⟩

lemma discFace_val {C : M.SCycle} {Z : Finset M.Face}
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) (i₀ t : ℕ) :
    (discFace hbd i₀ t).1 = (discCyc C Z).d ((i₀ + t) % C.k) := rfl

/-- **The face of the disc is a face cycle**, from any start. -/
theorem discFace_cycle {C : M.SCycle} {Z : Finset M.Face} (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
    (hbd : ∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) (i₀ : ℕ) :
    MSSP.FaceCycle (discMap M Z) C.k (discFace hbd i₀) := by
  obtain ⟨-, -, g, hg, hgv⟩ := discCyc_spec hl hbd
  have e : discFace hbd i₀ = fun t => g ((i₀ + t) % C.k) := by
    funext t
    apply Subtype.ext
    rw [discFace_val, hgv _ (Nat.mod_lt _ C.pos)]
  rw [e]
  exact faceCycle_shift hg i₀

end DiscCyc

/-! ### The one-face instance of a side, as a definition -/

section Side

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {K : Finset D} {ψ : V → SVert (kσ N K) (rcl N K)} {C : (kst N K).SCycle}
  {Z : Finset (kst N K).Face}

open Classical in
/-- **The embedding of the darts of a side into its disc**: a dart of `K` whose triangle is in
`Z` is its old dart in the stellar subdivision (any dart of the disc otherwise). -/
noncomputable def sideE
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    (d : D) : SDart (discDarts (kst N K) Z) :=
  if h : ∃ h' : d ∈ rcl N K, (kst N K).face (old ⟨d, h'⟩) ∈ Z then
    ⟨old ⟨d, h.1⟩, mem_discDarts.2 (Or.inl h.2)⟩ else discFace hbd 0 0

open Classical in
/-- **The embedding of the vertices of a side into its disc**: the vertex `ψ v` of the piece
map, as the tail of a dart of the disc leaving it (any vertex of the disc otherwise). -/
noncomputable def sideJ
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    (ψ : V → SVert (kσ N K) (rcl N K)) (v : V) :
    SVert (dσ (kst N K) Z) (discDarts (kst N K) Z) :=
  if h : ∃ x : SDart (discDarts (kst N K) Z), (kst N K).vert x.1 = .inl (ψ v) then
    (discMap (kst N K) Z).tail h.choose else (discMap (kst N K) Z).tail (discFace hbd 0 0)

lemma sideJ_eq
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    (v : V) (x : SDart (discDarts (kst N K) Z)) (hx : (kst N K).vert x.1 = .inl (ψ v)) :
    sideJ hbd ψ v = (discMap (kst N K) Z).tail x := by
  have h : ∃ x : SDart (discDarts (kst N K) Z), (kst N K).vert x.1 = .inl (ψ v) := ⟨x, hx⟩
  unfold sideJ
  simp only [h, ↓reduceDIte]
  exact discMap_tail_eq_iff.2 (h.choose_spec.trans hx.symm)

lemma sideE_val
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {d : D} (hd : d ∈ side N K Z) : (sideE hbd d).1 = old ⟨d, (mem_side.1 hd).2.1⟩ := by
  have h := (mem_side.1 hd).2
  unfold sideE
  simp only [h, ↓reduceDIte]

set_option maxHeartbeats 1000000 in
/-- **The disc of a side is a one-face instance of the part** `side N K Z ∪ R` (as
`side_faceInst`), with the explicit face `discFace hbd i₀` (any start `i₀`) and embeddings
`sideE`, `sideJ`. -/
theorem sideFD_inst (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, b ∈ verts N (side N K Z) ∧ Sum.inl (ψ b) ∈ C.verts)
    {R : Finset D} (hR : Disjoint (verts N R) (verts N K)) (i₀ : ℕ) :
    FaceInst N (side N K Z ∪ R) Bs (18 * K.card) C.k (discMap (kst N K) Z) (discFace hbd i₀)
      (side N K Z) (sideE hbd) (sideJ hbd ψ) := by
  classical
  have hS := kmap_isPlane hM hrot hface hK0 hK
  have hl := kmap_loopless hrot hKr
  have hl' := stellar_loopless hl
  obtain ⟨-, hCv, -⟩ := discCyc_spec hl' hbd
  have hwit : ∀ v ∈ verts N (side N K Z), ∃ x : SDart (discDarts (kst N K) Z),
      (kst N K).vert x.1 = .inl (ψ v) := by
    intro v hv
    obtain ⟨d, hd, hdv⟩ := mem_verts_iff'.1 hv
    obtain ⟨⟨δ, hδ, hδv⟩, ⟨δ', hδ', hδv'⟩⟩ := side_vert hψ hd
    rcases hdv with rfl | rfl
    · exact ⟨⟨δ, mem_discDarts.2 (Or.inl hδ)⟩, hδv⟩
    · exact ⟨⟨δ', mem_discDarts.2 (Or.inl hδ')⟩, hδv'⟩
  have hvK : verts N (side N K Z) ⊆ verts N K := verts_mono (side_subset Z)
  have hBsub : verts N (side N K Z) ∪ Bs = verts N (side N K Z) :=
    union_eq_left.2 fun b hb => (hBs b hb).1
  refine
    { plane := discMap_isPlane (isPlane_stellar hS) hbd
      rot := discMap_rotTrans
      face := discMap_faceTrans
      cycle := discFace_cycle hl' hbd i₀
      card := ?_
      sub := subset_union_left
      closed := ?_
      injE := ?_
      injJ := ?_
      tail := ?_
      head := ?_
      src := ?_ }
  · have h1 : Fintype.card (SVert (dσ (kst N K) Z) (discDarts (kst N K) Z)) ≤
        Fintype.card (SDart (discDarts (kst N K) Z)) :=
      Fintype.card_le_of_surjective _ Quotient.mk_surjective
    have h2 : Fintype.card (SFace (dσ (kst N K) Z) (discDarts (kst N K) Z)
        (revPerm (combOfSep (kst N K)))) ≤ Fintype.card (SDart (discDarts (kst N K) Z)) :=
      Fintype.card_le_of_surjective _ Quotient.mk_surjective
    have h3 : Fintype.card (SDart (discDarts (kst N K) Z)) ≤ 6 * K.card := by
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
    rw [sideE_val hbd hd₁, sideE_val hbd hd₂] at this
    exact congrArg Subtype.val (StDart.old.inj this)
  · rw [← coe_union, hBsub]
    intro v hv w hw h
    obtain ⟨x, hx⟩ := hwit v hv
    obtain ⟨y, hy⟩ := hwit w hw
    rw [sideJ_eq hbd v x hx, sideJ_eq hbd w y hy, discMap_tail_eq_iff, hx, hy] at h
    exact kψ_inj hrot hψ (hvK hv) (hvK hw) (Sum.inl.inj h)
  · intro d hd
    symm
    refine sideJ_eq hbd _ _ ?_
    rw [sideE_val hbd hd, stellar_vert_old, hψ ⟨d, _⟩]
  · intro d hd
    symm
    refine sideJ_eq hbd _ ((discMap (kst N K) Z).rev (sideE hbd d)) ?_
    show (kst N K).vert ((kst N K).α (sideE hbd d).1) = _
    rw [sideE_val hbd hd, stellar_α, stα_old, stellar_vert_old, ← hψ, pieceSep_α, tail_rev]
  · intro b hb
    obtain ⟨i, hi, hgi⟩ := hCv _ (hBs b hb).2
    obtain ⟨t, ht, et⟩ := exists_shift_idx (Nat.mod_lt i₀ C.pos) hi
    refine ⟨t, ht, (sideJ_eq hbd b (discFace hbd i₀ t) ?_).symm⟩
    rw [discFace_val, ← Nat.mod_add_mod, et]
    exact hgi

/-- **The one-face instance of a side**: the disc of `Z` in the stellar subdivision `kst N K` of
the piece map, its face `discFace hbd i₀` (the darts of `discCyc C Z` from position `i₀` on),
the darts `side N K Z` embedded by `sideE`, the vertices by `sideJ`, for the part
`X = side N K Z ∪ R` and the sources `Bs` (`sideFD_inst`); `q = 18 |K|`, `k = C.k`. -/
noncomputable def sideFD (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, b ∈ verts N (side N K Z) ∧ Sum.inl (ψ b) ∈ C.verts)
    {R : Finset D} (hR : Disjoint (verts N R) (verts N K)) {X : Finset D}
    (hX : X = side N K Z ∪ R) (i₀ : ℕ) : FaceData N X Bs where
  q := 18 * K.card
  k := C.k
  DQ := SDart (discDarts (kst N K) Z)
  VQ := SVert (dσ (kst N K) Z) (discDarts (kst N K) Z)
  FQ := SFace (dσ (kst N K) Z) (discDarts (kst N K) Z) (revPerm (combOfSep (kst N K)))
  Q := discMap (kst N K) Z
  g := discFace hbd i₀
  P' := side N K Z
  e := sideE hbd
  j := sideJ hbd ψ
  inst := hX ▸ sideFD_inst hM hrot hface hKr hK0 hK hψ hbd hBs hR i₀

/-- **The positions of `sideFD`**: a position `t` such that the dart of `discCyc C Z` at
`(i₀ + t) mod k` leaves the vertex `ψ v` is a position of `v` on the face of the instance (the
hypothesis of `cornerProg_face`). -/
theorem sideFD_pos (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, b ∈ verts N (side N K Z) ∧ Sum.inl (ψ b) ∈ C.verts)
    {R : Finset D} (hR : Disjoint (verts N R) (verts N K)) {X : Finset D}
    (hX : X = side N K Z ∪ R) (i₀ : ℕ) {t : ℕ} (ht : t < C.k) {v : V}
    (hv : (kst N K).vert ((discCyc C Z).d ((i₀ + t) % C.k)) = .inl (ψ v)) :
    t < (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).k ∧
      (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).Q.tail
        ((sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).g t) =
      (sideFD hM hrot hface hKr hK0 hK hψ hbd hBs hR hX i₀).j v :=
  ⟨ht, (sideJ_eq hbd v (discFace hbd i₀ t) hv).symm⟩

end Side

/-! ### The positions written by the walk -/

section Walk

open PlanarSeparator.MillerProg Orbit WordRAM WordRAM.Machine

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {P : Input} {W : ℕ}

/-- **`faceWalk` writes the positions of the concrete instance** (`faceWalk_faceInst` with the
cycle `discCyc C Z` of `sideFD`): from the plain encoding of the piece map and the marks of the
side `Z`, `faceWalk` ends within `72 m + 13 C.k + 18` steps, for some start `i₀ < C.k` of the
walk, with the number of the dart `discCyc C Z` at `(i₀ + t) mod C.k` at `T₀ + 3 (nV + nF) + t`
and, for every source `b`, a position `t < C.k` at `T₀ + 2 (nV + nF) + vn (ψ b)` with the dart
of `discCyc C Z` at `(i₀ + t) mod C.k` leaving `ψ b` (so `sideFD_pos` applies, for the face
`discFace hbd i₀`). -/
theorem faceWalk_side (hrot : N.RotTrans) {K : Finset D} (hKr : K ⊆ reps N)
    {ψ : V → SVert (kσ N K) (rcl N K)}
    {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}
    (hbd : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, Sum.inl (ψ b) ∈ C.verts)
    {m nV nF : ℕ} (c : SDart (rcl N K) ≃ Fin m) (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) {bα bφ bφi bvn bfn bz sv T₀ : ℕ} {c₀ : Config}
    (hE : Enc (kmap N K) c vn fn c₀.nmem bα bφ bφi bvn bfn)
    (hz : ∀ x, ((kst N K).face (old x) ∈ Z ↔ c₀.nmem (bz + c x) = sv))
    (hlay : bα + m ≤ T₀ ∧ bφ + m ≤ T₀ ∧ bφi + m ≤ T₀ ∧ bvn + m ≤ T₀ ∧ bfn + m ≤ T₀ ∧
      bz + m ≤ T₀)
    (hW : T₀ + 3 * (nV + nF) + 6 * m + 3 ≤ W) (hw : WordsBounded W c₀)
    (h10 : c₀.nreg 10 = 1) (h800 : c₀.nreg 800 = m) (h801 : c₀.nreg 801 = bα)
    (h802 : c₀.nreg 802 = bφ) (h803 : c₀.nreg 803 = bφi) (h804 : c₀.nreg 804 = bvn)
    (h805 : c₀.nreg 805 = bfn) (h806 : c₀.nreg 806 = bz) (h807 : c₀.nreg 807 = nV)
    (h808 : c₀.nreg 808 = nF) (h809 : c₀.nreg 809 = sv) (h810 : c₀.nreg 810 = T₀) :
    ∃ c' t, Exec P W faceWalk c₀ c' t ∧ t ≤ 72 * m + 13 * C.k + 18 ∧ c'.nreg 829 = C.k ∧
      SFr 820 840 c₀ c' ∧
      (∀ a, a < T₀ ∨ T₀ + 3 * (nV + nF) + 6 * m ≤ a → c'.nmem a = c₀.nmem a) ∧
      ∃ i₀ < C.k,
        (∀ t < C.k, c'.nmem (T₀ + 3 * (nV + nF) + t) =
          (kmap N K).stCode c ((discCyc C Z).d ((i₀ + t) % C.k))) ∧
        ∀ b ∈ Bs, c'.nmem (T₀ + 2 * (nV + nF) + vn (ψ b)) < C.k ∧
          (kst N K).vert ((discCyc C Z).d ((i₀ + c'.nmem (T₀ + 2 * (nV + nF) + vn (ψ b))) %
            C.k)) = .inl (ψ b) := by
  have hl' := stellar_loopless (kmap_loopless hrot hKr)
  obtain ⟨hout', hCv, -⟩ := discCyc_spec hl' hbd
  have hk' := discCyc_k C Z
  have hmem' := discCyc_mem C Z
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hlay
  set A := wArr c₀.nmem sv nV bα bφ bφi bvn bfn bz with hA
  obtain ⟨e1, e2, e3, e4, e5⟩ := enc_lt hE
  have hL : WLay A m bα bφ bφi bvn bfn bz nF T₀ W :=
    ⟨e1, e2, e3, e4, e5, l1, l2, l3, l4, l5, l6, hW⟩
  have hC : WCtx A m bα bφ bφi bvn bfn bz nF T₀ c₀ :=
    ⟨h10, h800, h801, h802, h803, h804, h805, h806, h807, h808, h809, h810,
      fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩
  have hY := wCyc_of (nV := nV) (sv := sv) (bz := bz) hE hz hbd hmem' (hk' ▸ hout')
  have hkpos : 0 < (discCyc C Z).k := (discCyc C Z).pos
  obtain ⟨c', s, i₀, ex, hs, hi₀, r829, fr, wP, wC, -, wo⟩ :=
    faceWalk_exec (P := P) hL hY hkpos c₀ hw hC
  rw [hk'] at hs hi₀ r829 wP wC
  have htlS : ∀ i, A.tlS ((kmap N K).stCode c ((discCyc C Z).d i)) = (kmap N K).stVi vn fn
      ((kst N K).vert ((discCyc C Z).d i)) := fun i => (wArr_st hE hz _).2.1
  refine ⟨c', s, ex, hs, r829, fr, wo, i₀, hi₀, wC, fun b hb => ?_⟩
  obtain ⟨i, hi, hvi⟩ := hCv _ (hBs b hb)
  obtain ⟨t, ht, et⟩ := exists_shift_idx hi₀ hi
  have hP : c'.nmem (T₀ + 2 * (nV + nF) + vn (ψ b)) = t := by
    have := wP t ht
    rw [et, htlS i, hvi, stVi_inl] at this
    exact this
  rw [hP, et]
  exact ⟨ht, hvi⟩

end Walk

/-! ### The node on the concrete instances -/

section Node

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

set_option maxHeartbeats 8000000 in
/-- **`node_exec_valBy` on the concrete instances of the split**: the whole node as one run
(`nodeProg`), with the one-face instances of the two parts the instances `sideFD` of the two
sides `Z₀`, `Z₁` of the stellar subdivision `kst N K` of the piece map, both bounded by the
cycle `Cy` (the parts `P₀ = side N K Z₀ ∪ R₀`, `P₁ = side N K Z₁ ∪ R₁`, the faces started at
`i₀`, `i₁`), for any encodings meeting `FEncValBy` for those instances. The bounds
`fd.q ≤ 18 m`, `fd.k² ≤ 1200 m` of `node_exec_valBy` come from `K ⊆ P` and
`Cy.k² ≤ 1200 m`, and the positions of the boundary vertices are given in the form
`faceWalk_side` writes them: the dart of the walk at the position leaves the vertex `ψ x`. -/
theorem node_exec_side (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {P P₀ P₁ : Finset D} (hS : SplitF N P P₀ P₁) (hB : (bdry N P₀ P₁).Nonempty) (ℓ : D → ℤ)
    (δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K) (hKP : K ⊆ P)
    {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {Cy : (kst N K).SCycle} (hCy : Cy.k ^ 2 ≤ 1200 * P.card) {Z₀ Z₁ : Finset (kst N K).Face}
    (hbd₀ : ∀ δ, ((kst N K).face δ ∈ Z₀ ↔ (kst N K).face ((kst N K).α δ) ∈ Z₀) ↔ ¬ Cy.Mem δ)
    (hbd₁ : ∀ δ, ((kst N K).face δ ∈ Z₁ ↔ (kst N K).face ((kst N K).α δ) ∈ Z₁) ↔ ¬ Cy.Mem δ)
    (hBs₀ : ∀ b ∈ bdry N P₀ P₁, b ∈ verts N (side N K Z₀) ∧ Sum.inl (ψ b) ∈ Cy.verts)
    (hBs₁ : ∀ b ∈ bdry N P₀ P₁, b ∈ verts N (side N K Z₁) ∧ Sum.inl (ψ b) ∈ Cy.verts)
    {R₀ R₁ : Finset D} (hR₀ : Disjoint (verts N R₀) (verts N K))
    (hR₁ : Disjoint (verts N R₁) (verts N K)) (hX₀ : P₀ = side N K Z₀ ∪ R₀)
    (hX₁ : P₁ = side N K Z₁ ∪ R₁) (i₀ i₁ : ℕ) :
    let fd₀ := sideFD hM hrot hface hKr hK0 hK hψ hbd₀ hBs₀ hR₀ hX₀ i₀
    let fd₁ := sideFD hM hrot hface hKr hK0 hK hψ hbd₁ hBs₁ hR₁ hX₁ i₁
    ∀ {n₀ Bw₀ : ℕ}
      {σ₀ : Klein.SrcD fd₀.DQ fd₀.k ≃ Fin (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k))}
      {Pk₀ : Input}, FEncValBy fd₀ (redLen N ℓ δ₀) n₀ Bw₀ σ₀ Pk₀ →
    ∀ {n₁ Bw₁ : ℕ}
      {σ₁ : Klein.SrcD fd₁.DQ fd₁.k ≃ Fin (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k))}
      {Pk₁ : Input}, FEncValBy fd₁ (redLen N ℓ δ₁) n₁ Bw₁ σ₁ Pk₁ →
        ∀ {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}, NodeEnc N P₀ P₁ m w e ν ι →
        b = (bdry N P₀ P₁).card →
        ∀ (L₀ L₁ Pb₀ Pb₁ β₀ β₁ Rk₀ Rk₁ Z M₀ Y S W' : ℕ) (I : Input) (c : Config),
          M₀ = m + w + 1 → loB m w ≤ Z → bfWP b < Z →
          Bw₀ + 16 * (n₀ + 1) < Z → Bw₁ + 16 * (n₁ + 1) < Z →
          n₀ + fd₀.k * fd₀.k ≤ Z → n₁ + fd₁.k * fd₁.k ≤ Z →
          3 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 3 + fd₀.k * fd₀.k ≤ Z →
          3 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 3 + fd₁.k * fd₁.k ≤ Z →
          Z + 22 * M₀ ≤ Y →
          (w ≤ S ∧ b * b ≤ S ∧ fd₀.k ≤ S ∧ fd₁.k ≤ S ∧ 3 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 3 ≤ S ∧
            3 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 3 ≤ S) →
          (Y + 16 * S ≤ Pb₀ ∧ Y + 16 * S ≤ Pb₁ ∧ Y + 16 * S ≤ β₀ ∧ Y + 16 * S ≤ β₁ ∧
            Y + 16 * S ≤ Rk₀ ∧ Y + 16 * S ≤ Rk₁) →
          (Y + 16 * S ≤ W' ∧ Pb₀ + w ≤ W' ∧ Pb₁ + w ≤ W' ∧ Rk₀ + (3 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 3) ≤ W' ∧
            Rk₁ + (3 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 3) ≤ W' ∧ L₀ + 1 ≤ W' ∧ L₁ + 1 ≤ W') →
          ((Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀)) : ℤ) : ℝ) ≤ 2 ^ L₀ →
          ((Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁)) : ℤ) : ℝ) ≤ 2 ^ L₁ →
          WordsBounded W' c → NCtx m w b Z M₀ c → XCtx Y S c →
          (∀ d < m, c.nmem (Z + 0 * M₀ + d) = encT N e ν d) →
          (∀ d < m, c.nmem (Z + 1 * M₀ + d) = encH N e ν d) →
          (∀ d < m, c.nmem (Z + 2 * M₀ + d) = encS P₀ e d) →
          (∀ d < m, c.rmem (Z + 3 * M₀ + d) = ℓ (e d)) →
          (∀ v < w, c.rmem (Z + 4 * M₀ + v) = δ₀ (ι v)) →
          (∀ v < w, c.rmem (Z + 5 * M₀ + v) = δ₁ (ι v)) →
          (∀ a < Z, c.nmem a = 0) →
          (∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₀ + ν x) < Cy.k ∧
            (kst N K).vert ((discCyc Cy Z₀).d ((i₀ + c.nmem (Pb₀ + ν x)) % Cy.k)) =
              .inl (ψ x)) →
          (∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₁ + ν x) < Cy.k ∧
            (kst N K).vert ((discCyc Cy Z₁).d ((i₁ + c.nmem (Pb₁ + ν x)) % Cy.k)) =
              .inl (ψ x)) →
          KSlot (Klein.srcMap fd₀.inst.cycle) fd₀.k (Klein.srcG fd₀.inst.cycle)
            (Klein.srcPiece fd₀.k (fd₀.P'.image fd₀.e))
            (MSSP.pertBy σ₀ (Klein.srcLen (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))
              (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀)))))
            σ₀ Bw₀ n₀ β₀ Rk₀ W' Pk₀ c →
          KSlot (Klein.srcMap fd₁.inst.cycle) fd₁.k (Klein.srcG fd₁.inst.cycle)
            (Klein.srcPiece fd₁.k (fd₁.P'.image fd₁.e))
            (MSSP.pertBy σ₁ (Klein.srcLen (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))
              (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁)))))
            σ₁ Bw₁ n₁ β₁ Rk₁ W' Pk₁ c →
          ∃ c' t, ∃ o : Option (V → ℤ),
            Exec I W' (nodeProg ⟨fd₀.k, Fintype.card (Klein.SrcD fd₀.DQ fd₀.k), n₀, Bw₀, Pk₀.data.length, β₀, Rk₀, Pb₀, L₀,
            Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))⟩
              ⟨fd₁.k, Fintype.card (Klein.SrcD fd₁.DQ fd₁.k), n₁, Bw₁, Pk₁.data.length, β₁, Rk₁, Pb₁, L₁,
            Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))⟩) c c' t ∧
            t ≤ 8 + (61 * m + 12) +
            ((3 * (32886 * 2372500000 * P.card * lg P.card) + rdCost b L₀ (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k)) + 19 * fd₀.k + 10 * b +
              33 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 300) +
            (3 * (32886 * 2372500000 * P.card * lg P.card) + rdCost b L₁ (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k)) + 19 * fd₁.k + 10 * b +
              33 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 300) + 14) +
            (bfCostP b + 4 * bfWP b + 22 * (b * b) + 2 * (cNegMach C).dij (w + 1) (m + w) +
              232 * m + 450 * w + 92 * b + 2917) ∧
            PotOut ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).join (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁))) o ∧
            (∀ bf : DDG V → DDG V → Option (V → ℤ), bf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) = o →
              (step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = none ∧ c'.nreg 990 ≠ 0) ∨
              (∃ f, step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = some f ∧ c'.nreg 990 = 0 ∧
                ∀ x ∈ verts N (P₀ ∪ P₁), c'.rmem (Z + 20 * M₀ + ν x) = f x)) ∧
            c'.output = c.output := by
  intro fd₀ fd₁ n₀ Bw₀ σ₀ Pk₀ hv₀ n₁ Bw₁ σ₁ Pk₁ hv₁
  have hq : 18 * K.card ≤ 18 * P.card := Nat.mul_le_mul_left 18 (card_le_card hKP)
  intro m w b e ν ι hN hb L₀ L₁ Pb₀ Pb₁ β₀ β₁ Rk₀ Rk₁ Z M₀ Y S W' I c a1 a2 a3 a4 a5 a6 a7 a8 a9
    a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 hpos₀ hpos₁
  exact node_exec_valBy C hfr hmssp hS hB ℓ δ₀ δ₁ hδ₀ hδ₁ fd₀ hq hCy hv₀ fd₁ hq hCy hv₁ hN hb L₀ L₁ Pb₀ Pb₁ β₀ β₁ Rk₀ Rk₁ Z M₀ Y S W' I c a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11
    a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25
    (fun x hx => sideFD_pos hM hrot hface hKr hK0 hK hψ hbd₀ hBs₀ hR₀ hX₀ i₀ (hpos₀ x hx).1
      (hpos₀ x hx).2)
    (fun x hx => sideFD_pos hM hrot hface hKr hK0 hK hψ hbd₁ hBs₁ hR₁ hX₁ i₁ (hpos₁ x hx).1
      (hpos₁ x hx).2)

end Node

end NegSSSP

end PlanarFlow
