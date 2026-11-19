module

public import PlanarFlow.NegSSSP.Disc
public import PlanarFlow.NegSSSP.SimpleRot

/-!
# Splitting a piece by a simple cycle, with the boundary on one face

The recursion of Klein, Mozes and Weimann splits a piece by a cycle separator, so that the
vertices shared by the two parts lie on the cycle, which bounds a face of each part completed by
the other side (Mozes and Wulff-Nilsen, the article, Section 2: a region lies inside the cycle
bounding it, its external face, the rest triangulated with arcs that shortest paths do not use).
Multiple-source shortest paths from these vertices are then one call of Klein's algorithm from a
face. This file makes this precise for a piece `K` of the simple graph of a plane map `N`
(`PlanarFlow.NegSSSP.reps`) whose darts are connected (`DConn`):

* `OneFace N P B q k` (`FaceInst`): **the sources `B` of the piece `P` lie on one face**: a
  plane map `Q` with transitive rotations and faces and at most `q` vertices, faces and darts,
  with a face cycle of `k` darts (`PlanarFlow.MSSP.FaceCycle`, the input of Klein's algorithm,
  `PlanarFlow.Klein.klein_exec`) through all the sources, into which the darts of `P` reached
  from `B` embed with their vertices. The distances in `P` from the sources are the distances in
  the embedded piece of `Q` (Klein's `PlanarFlow.MSSP.pieceGraph`, whose other darts are absent):
  `PlanarFlow.NegSSSP.FaceInst.isDist`.
* `kmap N K`: the piece map of `K` (its darts and their reverses, the rotation of `N` cut down to
  them), a plane map without loops (`kmap_isPlane`, `kmap_loopless`); `kst N K`: its stellar
  subdivision, a plane triangulation.
* `exists_cycle_cut`: **the split by a short simple cycle**. Miller's theorem on `kst N K`, the
  weight on the triangles of the darts of `K`
  (`PlanarSeparator.Map.exists_short_cycle_separator_card`), gives a simple cycle `C` of
  `c ≤ 6 √(12 #K) + 4` darts bounding a set `Z` of triangles. The darts of `K` whose triangle is
  in `Z` (`side N K Z`) and the others (`side N K Zᶜ`) have at most `(2 #K + 12 c) / 3` darts
  each; a vertex of both has triangles on both sides, so it lies on `C` (`mem_cycle_of_bdry`):
  at most `c` shared vertices. For each part, the disc of its side in `kst N K`
  (`PlanarFlow.NegSSSP.discMap`, with at most `18 #K` vertices, faces and darts) has `C` as a face
  (`PlanarFlow.NegSSSP.exists_disc_faceCycle`) and contains the part: `OneFace` holds with
  `q = 18 #K` and `k = c` (`side_oneFace`), also with a rest of the piece sharing no vertex with
  `K` added to the part.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW

universe u v w

/-! ### Multiple-source shortest paths from one face -/

section OneFace

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V]

/-- **The sources `B` of the piece `P` on one face of a plane map `Q`**: `Q` is plane with
transitive rotations and faces and at most `q` vertices, faces and darts, `g` is the boundary walk
of a face of `Q` of `k` darts (`PlanarFlow.MSSP.FaceCycle`), the darts `P'` of `P` reached from
`B` (every dart of `P` leaving a vertex of `P'` or of `B` is in `P'`) embed into `Q` by `e`, their
vertices by `j`, and every source is the tail of a dart of the face. The distances in the piece
`P` from a source are then those in the piece `e '' P'` of `Q` (Klein's setting,
`PlanarFlow.MSSP.pieceGraph`), from a vertex of the face `g`. -/
structure FaceInst (N : CombMap D V F) (P : Finset D) (B : Finset V) (q k : ℕ)
    {DQ VQ FQ : Type u} [Fintype DQ] [DecidableEq DQ] [Fintype VQ] [DecidableEq VQ]
    [Fintype FQ] [DecidableEq FQ] (Q : CombMap DQ VQ FQ) (g : ℕ → DQ) (P' : Finset D)
    (e : D → DQ) (j : V → VQ) : Prop where
  plane : Q.IsPlane
  rot : Q.RotTrans
  face : Q.FaceTrans
  cycle : MSSP.FaceCycle Q k g
  card : Fintype.card VQ + Fintype.card FQ + Fintype.card DQ ≤ q
  sub : P' ⊆ P
  closed : ∀ d ∈ P, N.tail d ∈ verts N P' ∪ B → d ∈ P'
  injE : Set.InjOn e P'
  injJ : Set.InjOn j (verts N P' ∪ B)
  tail : ∀ d ∈ P', Q.tail (e d) = j (N.tail d)
  head : ∀ d ∈ P', Q.head (e d) = j (N.head d)
  src : ∀ b ∈ B, ∃ i < k, Q.tail (g i) = j b

/-- **Multiple-source shortest paths in the piece `P` from the sources `B` are one call from a
face**: of a plane map with at most `q` vertices, faces and darts, along a face of `k` darts
(`FaceInst`). -/
def OneFace (N : CombMap D V F) (P : Finset D) (B : Finset V) (q k : ℕ) : Prop :=
  ∃ (DQ VQ FQ : Type u) (_ : Fintype DQ) (_ : DecidableEq DQ) (_ : Fintype VQ)
    (_ : DecidableEq VQ) (_ : Fintype FQ) (_ : DecidableEq FQ) (Q : CombMap DQ VQ FQ)
    (g : ℕ → DQ) (P' : Finset D) (e : D → DQ) (j : V → VQ), FaceInst N P B q k Q g P' e j

end OneFace

/-! ### Connected sets of darts -/

section Conn

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {N : CombMap D V F}

variable (N) in
/-- The darts of `K` and their reverses. -/
def rcl (K : Finset D) : Finset D := K ∪ K.image N.rev

lemma mem_rcl {K : Finset D} {x : D} : x ∈ rcl N K ↔ x ∈ K ∨ N.rev x ∈ K := by
  unfold rcl
  rw [mem_union, mem_image]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (by rwa [N.rev_rev])
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨_, h, N.rev_rev x⟩

lemma rcl_stable (K : Finset D) : Stable (revPerm N) (rcl N K) := fun x hx => by
  rw [mem_rcl] at hx ⊢
  simp only [revPerm_apply, N.rev_rev]
  tauto

lemma subset_rcl (K : Finset D) : K ⊆ rcl N K := subset_union_left

lemma rcl_subset_reps {K : Finset D} (hK : K ⊆ reps N) : rcl N K ⊆ reps N := fun x hx => by
  rcases mem_rcl.1 hx with h | h
  · exact hK h
  · have := reps_rev (hK h); rwa [N.rev_rev] at this

lemma card_rcl_le (K : Finset D) : (rcl N K).card ≤ 2 * K.card := by
  unfold rcl
  have := card_union_le K (K.image N.rev)
  have := card_image_le (s := K) (f := N.rev)
  omega

lemma verts_eq_tails (K : Finset D) : verts N K = (rcl N K).image N.tail := by
  ext v
  simp only [verts, rcl, mem_union, mem_image]
  constructor
  · rintro (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩)
    · exact ⟨d, Or.inl hd, rfl⟩
    · exact ⟨N.rev d, Or.inr ⟨d, hd, rfl⟩, rfl⟩
  · rintro ⟨x, hx | ⟨d, hd, rfl⟩, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨d, hd, rfl⟩

variable (N) in
/-- Two darts share an end. -/
def Share (a b : D) : Prop :=
  N.tail a = N.tail b ∨ N.tail a = N.head b ∨ N.head a = N.tail b ∨ N.head a = N.head b

variable (N) in
/-- **A connected set of darts**: any two are joined by darts of the set, each sharing an end with
the next. -/
def DConn (K : Finset D) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ReflTransGen (fun a b => a ∈ K ∧ b ∈ K ∧ Share N a b) x y

/-- **The rotation cut down to a connected set of darts and their reverses connects them.** -/
lemma conn_rcl (hrot : N.RotTrans) {K : Finset D} (hK : DConn N K) :
    ∀ x ∈ rcl N K, ∀ y ∈ rcl N K, Conn (revPerm N) (ret (rotPerm N) (rcl N K)) x y := by
  set B := rcl N K
  have hsame : ∀ x ∈ B, ∀ y ∈ B, N.tail x = N.tail y →
      Conn (revPerm N) (ret (rotPerm N) B) x y := fun x hx y hy h =>
    conn_of_sameCycle ((sameCycle_ret_iff hrot hx hy).2 h)
  have hrev : ∀ x, Conn (revPerm N) (ret (rotPerm N) B) x (N.rev x) := fun x => conn_inv x
  have hrev' : ∀ x, Conn (revPerm N) (ret (rotPerm N) B) (N.rev x) x := fun x => by
    have := conn_inv (ι := revPerm N) (σ := ret (rotPerm N) B) (N.rev x)
    rwa [revPerm_apply, N.rev_rev] at this
  have hKB : ∀ a ∈ K, a ∈ B := fun a ha => subset_rcl K ha
  have hKB' : ∀ a ∈ K, N.rev a ∈ B := fun a ha => rcl_stable K a (hKB a ha)
  have hshare : ∀ a ∈ K, ∀ b ∈ K, Share N a b → Conn (revPerm N) (ret (rotPerm N) B) a b := by
    intro a ha b hb h
    rcases h with h | h | h | h
    · exact hsame a (hKB a ha) b (hKB b hb) h
    · exact (hsame a (hKB a ha) _ (hKB' b hb) (by rw [tail_rev]; exact h)).trans (hrev' b)
    · exact (hrev a).trans (hsame _ (hKB' a ha) b (hKB b hb) (by rw [tail_rev]; exact h))
    · exact ((hrev a).trans (hsame _ (hKB' a ha) _ (hKB' b hb) (by simpa using h))).trans
        (hrev' b)
  have hK' : ∀ a ∈ K, ∀ b, ReflTransGen (fun a b => a ∈ K ∧ b ∈ K ∧ Share N a b) a b →
      Conn (revPerm N) (ret (rotPerm N) B) a b := by
    intro a ha b h
    induction h with
    | refl => exact .refl
    | tail _ hst ih => exact ih.trans (hshare _ hst.1 _ hst.2.1 hst.2.2)
  have hto : ∀ x ∈ B, ∃ a ∈ K, Conn (revPerm N) (ret (rotPerm N) B) x a ∧
      Conn (revPerm N) (ret (rotPerm N) B) a x := by
    intro x hx
    rcases mem_rcl.1 hx with h | h
    · exact ⟨x, h, .refl, .refl⟩
    · exact ⟨N.rev x, h, hrev x, hrev' x⟩
  intro x hx y hy
  obtain ⟨a, ha, h1, -⟩ := hto x hx
  obtain ⟨b, hb, -, h2⟩ := hto y hy
  exact (h1.trans (hK' a ha b (hK a ha b hb))).trans h2

end Conn

/-! ### The piece map of a connected piece and its stellar subdivision -/

section Cut

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {N : CombMap D V F}

variable (N) in
/-- The rotation cut down to the darts of `K` and their reverses. -/
noncomputable abbrev kσ (K : Finset D) : Perm D := ret (rotPerm N) (rcl N K)

variable (N) in
/-- **The piece map of `K`** (its darts and their reverses), as a map of `PlanarSeparator`. -/
noncomputable abbrev kmap (K : Finset D) :
    PlanarSeparator.Map (SDart (rcl N K)) (SVert (kσ N K) (rcl N K)) :=
  pieceSep N (stable_ret (rotPerm N) (rcl N K)) (rcl_stable K)

variable (N) in
/-- **The stellar subdivision of the piece map of `K`**: a plane triangulation. -/
noncomputable abbrev kst (K : Finset D) :=
  (kmap N K).stellar

lemma mem_verts_iff' {P : Finset D} {v : V} :
    v ∈ verts N P ↔ ∃ d ∈ P, N.tail d = v ∨ N.head d = v := by
  unfold verts
  simp only [mem_union, mem_image]
  constructor
  · rintro (⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩)
    · exact ⟨d, hd, Or.inl rfl⟩
    · exact ⟨d, hd, Or.inr rfl⟩
  · rintro ⟨d, hd, rfl | rfl⟩
    · exact Or.inl ⟨d, hd, rfl⟩
    · exact Or.inr ⟨d, hd, rfl⟩

lemma verts_mono {P P' : Finset D} (h : P ⊆ P') : verts N P ⊆ verts N P' := fun v hv => by
  obtain ⟨d, hd, e⟩ := mem_verts_iff'.1 hv
  exact mem_verts_iff'.2 ⟨d, h hd, e⟩

lemma kmap_isPlane (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {K : Finset D}
    (hK0 : K.Nonempty) (hK : DConn N K) : (kmap N K).IsPlane := by
  obtain ⟨x₀, hx₀⟩ := hK0
  exact pieceSep_isPlane _ _ (subset_rcl K hx₀) (conn_rcl hrot hK)
    (gap_reps hM hrot hface ⟨x₀⟩ fun x hx => rcl_stable K x hx)

lemma kmap_loopless (hrot : N.RotTrans) {K : Finset D} (hKr : K ⊆ reps N)
    (x : SDart (rcl N K)) : (kmap N K).vert ((kmap N K).α x) ≠ (kmap N K).vert x := by
  rw [Ne, pieceSep_vert_eq, sameCycle_ret_iff hrot ((kmap N K).α x).2 x.2, pieceSep_α, tail_rev]
  exact fun h => reps_loop (rcl_subset_reps hKr x.2) h.symm

/-- The vertices of the piece map, from the vertices of `N`. -/
lemma exists_kψ (hrot : N.RotTrans) {K : Finset D} (hK0 : K.Nonempty) :
    ∃ ψ : V → SVert (kσ N K) (rcl N K), ∀ x : SDart (rcl N K),
      ψ (N.tail x.1) = (kmap N K).vert x := by
  classical
  obtain ⟨x₀, hx₀⟩ := hK0
  refine ⟨fun v => if h : ∃ x : SDart (rcl N K), N.tail x.1 = v then Quotient.mk _ h.choose
    else Quotient.mk _ ⟨x₀, subset_rcl K hx₀⟩, fun x => ?_⟩
  have h : ∃ y : SDart (rcl N K), N.tail y.1 = N.tail x.1 := ⟨x, rfl⟩
  simp only [h, ↓reduceDIte, pieceSep_vert]
  exact Quotient.sound ((sameCycle_ret_iff hrot h.choose.2 x.2).2 h.choose_spec)

lemma kψ_inj (hrot : N.RotTrans) {K : Finset D} {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x) {v w : V}
    (hv : v ∈ verts N K) (hw : w ∈ verts N K) (h : ψ v = ψ w) : v = w := by
  rw [verts_eq_tails] at hv hw
  obtain ⟨x, hx, rfl⟩ := mem_image.1 hv
  obtain ⟨y, hy, rfl⟩ := mem_image.1 hw
  have := hψ ⟨x, hx⟩
  rw [h, hψ ⟨y, hy⟩, pieceSep_vert_eq] at this
  exact ((sameCycle_ret_iff hrot hy hx).1 this).symm

variable (N) in
/-- **The darts of `K` on the side `W`**: those whose triangle in the stellar subdivision is in
`W`. -/
noncomputable def side (K : Finset D) (W : Finset (kst N K).Face) : Finset D := by
  classical exact K.filter fun d => ∃ h : d ∈ rcl N K, (kst N K).face (old ⟨d, h⟩) ∈ W

lemma mem_side {K : Finset D} {W : Finset (kst N K).Face} {d : D} :
    d ∈ side N K W ↔ d ∈ K ∧ ∃ h : d ∈ rcl N K, (kst N K).face (old ⟨d, h⟩) ∈ W := by
  classical
  unfold side; rw [mem_filter]

lemma side_subset {K : Finset D} (W : Finset (kst N K).Face) : side N K W ⊆ K :=
  fun _ hd => (mem_side.1 hd).1

/-- **Both ends of a dart on the side `W` are vertices of triangles in `W`.** -/
lemma side_vert {K : Finset D} {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {W : Finset (kst N K).Face} {d : D} (hd : d ∈ side N K W) :
    (∃ δ, (kst N K).face δ ∈ W ∧ (kst N K).vert δ = .inl (ψ (N.tail d))) ∧
      ∃ δ, (kst N K).face δ ∈ W ∧ (kst N K).vert δ = .inl (ψ (N.head d)) := by
  obtain ⟨-, h, hW⟩ := mem_side.1 hd
  refine ⟨⟨old ⟨d, h⟩, hW, by rw [stellar_vert_old, hψ ⟨d, h⟩]⟩,
    ⟨up ((kmap N K).φ ⟨d, h⟩), ?_, ?_⟩⟩
  · rw [stellar_face_up, Equiv.symm_apply_apply]; exact hW
  · rw [stellar_vert_up, vert_φ, ← hψ, pieceSep_α, tail_rev]

/-- **The vertices of both sides lie on the cycle.** -/
lemma mem_cycle_of_bdry {K : Finset D} {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}
    (hsep : IsCycleSep C Z (sideIn C Z) (sideOut C Z)) {v : V}
    (hv : v ∈ bdry N (side N K Z) (side N K Zᶜ)) : Sum.inl (ψ v) ∈ C.verts := by
  obtain ⟨h0, h1⟩ := mem_inter.1 hv
  obtain ⟨d₀, hd₀, e₀⟩ := mem_verts_iff'.1 h0
  obtain ⟨d₁, hd₁, e₁⟩ := mem_verts_iff'.1 h1
  obtain ⟨δ₀, hf₀, hv₀⟩ : ∃ δ, (kst N K).face δ ∈ Z ∧ (kst N K).vert δ = .inl (ψ v) := by
    rcases e₀ with rfl | rfl
    · exact (side_vert hψ hd₀).1
    · exact (side_vert hψ hd₀).2
  obtain ⟨δ₁, hf₁, hv₁⟩ : ∃ δ, (kst N K).face δ ∈ Zᶜ ∧ (kst N K).vert δ = .inl (ψ v) := by
    rcases e₁ with rfl | rfl
    · exact (side_vert hψ hd₁).1
    · exact (side_vert hψ hd₁).2
  have hc := hsep.cover
  have hx : Sum.inl (ψ v) ∈ C.verts ∪ sideIn C Z ∪ sideOut C Z := by rw [hc]; exact mem_univ _
  rcases mem_union.1 hx with hx | hx
  · rcases mem_union.1 hx with hx | hx
    · exact hx
    · exact absurd (hsep.inA δ₁ (hv₁ ▸ hx)) (mem_compl.1 hf₁)
  · exact absurd hf₀ (hsep.inB δ₀ (hv₀ ▸ hx))

/-- **The sources on the cycle are on one face of the disc of the side `W`**: the darts of the
side `W` with the rest `R` of a piece (sharing no vertex with `K`) have their multiple-source
shortest paths from sources on the cycle `C` bounding `W` as one call from a face, on the disc of
`W` in the stellar subdivision (`discMap`), with at most `18 #K` vertices, faces and darts, along
the face `C`. -/
theorem side_oneFace (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {K : Finset D}
    (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K) {ψ : V → SVert (kσ N K) (rcl N K)}
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {C : (kst N K).SCycle} {W : Finset (kst N K).Face}
    (hbd : ∀ δ, ((kst N K).face δ ∈ W ↔ (kst N K).face ((kst N K).α δ) ∈ W) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, b ∈ verts N (side N K W) ∧ Sum.inl (ψ b) ∈ C.verts)
    {R : Finset D} (hR : Disjoint (verts N R) (verts N K)) :
    OneFace N (side N K W ∪ R) Bs (18 * K.card) C.k := by
  classical
  have hS := kmap_isPlane hM hrot hface hK0 hK
  have hl := kmap_loopless hrot hKr
  have hl' := stellar_loopless hl
  obtain ⟨g, hg, hgv⟩ := exists_disc_faceCycle hl' hbd
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
  -- the vertices of the side are vertices of the disc
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
  refine ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, Q, g, side N K W, e, j, ?_⟩
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
    obtain ⟨i, hi, hgi⟩ := hgv _ (hBs b hb).2
    exact ⟨i, hi, (hjx b (g i) hgi).symm⟩

/-- **The split of a connected piece by a short simple cycle** (Miller's theorem on the stellar
subdivision of its piece map, `PlanarSeparator.Map.exists_short_cycle_separator_card`, weighing
the darts of `K`): two parts of at most `(2 #K + 12 c) / 3` darts each, for a cycle of
`c ≤ 6 √(12 #K) + 4` darts; the vertices shared by the parts lie on the cycle, so there are at
most `c` of them, and for each part, with any rest `R` sharing no vertex with `K`, the multiple-
source shortest paths from them are one call from a face (`OneFace`), of a plane map with at most
`18 #K` vertices, faces and darts, along a face of `c` darts. -/
theorem exists_cycle_cut (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K) :
    ∃ (A₀ A₁ : Finset D) (c : ℕ), A₀ ∪ A₁ = K ∧ Disjoint A₀ A₁ ∧
      c ≤ 6 * Nat.sqrt (12 * K.card) + 4 ∧
      3 * A₀.card ≤ 2 * K.card + 12 * c ∧ 3 * A₁.card ≤ 2 * K.card + 12 * c ∧
      (bdry N A₀ A₁).card ≤ c ∧
      ∀ R : Finset D, Disjoint (verts N R) (verts N K) →
        OneFace N (A₀ ∪ R) (bdry N A₀ A₁) (18 * K.card) c ∧
        OneFace N (A₁ ∪ R) (bdry N A₀ A₁) (18 * K.card) c := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_kψ hrot hK0
  have hS := kmap_isPlane hM hrot hface hK0 hK
  have hl := kmap_loopless hrot hKr
  obtain ⟨x₀, hx₀⟩ := hK0
  have hx₀' : x₀ ∈ rcl N K := subset_rcl K hx₀
  set S' : Finset (StDart (SDart (rcl N K))) := (K.subtype (· ∈ rcl N K)).image old with hS'
  have hS'card : S'.card = K.card := by
    rw [hS', card_image_of_injective _ (fun a b h => StDart.old.inj h), card_subtype,
      filter_true_of_mem fun d hd => subset_rcl K hd]
  obtain ⟨C, Z, hk, hsep, hin, hout⟩ :=
    exists_short_cycle_separator_card (isPlane_stellar hS) ((kmap N K).isTriangle_stellar hl)
      (stellar_loopless hl) S'
  change 3 * (S'.filter fun δ => (kst N K).face δ ∈ Z ∧ ¬ C.Mem δ).card ≤ _ at hin
  change 3 * (S'.filter fun δ => (kst N K).face δ ∉ Z ∧ ¬ C.Mem δ).card ≤ _ at hout
  -- the length of the cycle
  have hk' : C.k ≤ 6 * Nat.sqrt (12 * K.card) + 4 := by
    have h1 : Fintype.card (SVert (kσ N K) (rcl N K)) + Fintype.card (kmap N K).Face ≤
        2 * (rcl N K).card := card_pieceSep_le _ _
    have h2 := card_rcl_le (N := N) K
    change C.k ≤ 6 * Nat.sqrt (3 * Fintype.card (SVert (kσ N K) (rcl N K) ⊕
      (kmap N K).Face)) + 4 at hk
    rw [Fintype.card_sum] at hk
    have h3 : 3 * (Fintype.card (SVert (kσ N K) (rcl N K)) + Fintype.card (kmap N K).Face) ≤
        12 * K.card := by omega
    exact hk.trans (by have := Nat.sqrt_le_sqrt h3; omega)
  -- counting the darts of a side
  have hcount : ∀ W : Finset (kst N K).Face,
      (side N K W).card ≤ (S'.filter fun δ => (kst N K).face δ ∈ W).card := by
    intro W
    refine card_le_card_of_injOn
      (fun d => if h : d ∈ rcl N K then old ⟨d, h⟩ else old ⟨x₀, hx₀'⟩) ?_ ?_
    · intro d hd
      obtain ⟨hdK, h, hW⟩ := mem_side.1 hd
      simp only [h, ↓reduceDIte, mem_coe, mem_filter, hS', mem_image, mem_subtype]
      exact ⟨⟨⟨d, h⟩, hdK, rfl⟩, hW⟩
    · intro a ha b hb hab
      obtain ⟨-, h, -⟩ := mem_side.1 ha
      obtain ⟨-, h', -⟩ := mem_side.1 hb
      simp only [h, h', ↓reduceDIte] at hab
      exact congrArg Subtype.val (StDart.old.inj hab)
  have hmem : (univ.filter C.Mem).card ≤ 2 * C.k := by
    have hsub : univ.filter C.Mem ⊆
        (range C.k).image C.d ∪ (range C.k).image fun i => (kst N K).α (C.d i) := by
      intro δ hδ
      obtain ⟨i, hi, h | h⟩ := (mem_filter.1 hδ).2
      · exact mem_union_left _ (mem_image.2 ⟨i, mem_range.2 hi, h.symm⟩)
      · exact mem_union_right _ (mem_image.2 ⟨i, mem_range.2 hi, h.symm⟩)
    have h1 := card_le_card hsub
    have h2 := card_union_le ((range C.k).image C.d)
      ((range C.k).image fun i => (kst N K).α (C.d i))
    have h3 := card_image_le (s := range C.k) (f := C.d)
    have h4 := card_image_le (s := range C.k) (f := fun i => (kst N K).α (C.d i))
    rw [card_range] at h3 h4
    omega
  have hZ : (side N K Z).card ≤
      (S'.filter fun δ => (kst N K).face δ ∈ Z ∧ ¬ C.Mem δ).card + 2 * C.k := by
    refine (hcount Z).trans ((card_le_card ?_).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left hmem _)))
    intro δ hδ
    obtain ⟨h1, h2⟩ := mem_filter.1 hδ
    by_cases hm : C.Mem δ
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hm⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨h1, h2, hm⟩)
  have hZc : (side N K Zᶜ).card ≤
      (S'.filter fun δ => (kst N K).face δ ∉ Z ∧ ¬ C.Mem δ).card + 2 * C.k := by
    refine (hcount Zᶜ).trans ((card_le_card ?_).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left hmem _)))
    intro δ hδ
    obtain ⟨h1, h2⟩ := mem_filter.1 hδ
    by_cases hm : C.Mem δ
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hm⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨h1, mem_compl.1 h2, hm⟩)
  -- the vertices shared by the two sides
  have hbK : bdry N (side N K Z) (side N K Zᶜ) ⊆ verts N K := fun v hv =>
    verts_mono (side_subset Z) (mem_inter.1 hv).1
  have hbcard : (bdry N (side N K Z) (side N K Zᶜ)).card ≤ C.k := by
    rw [← C.card_verts]
    refine card_le_card_of_injOn (fun v => Sum.inl (ψ v)) (fun v hv => ?_) (fun v hv w hw h => ?_)
    · exact mem_cycle_of_bdry hψ hsep hv
    · exact kψ_inj hrot hψ (hbK hv) (hbK hw) (Sum.inl.inj h)
  refine ⟨side N K Z, side N K Zᶜ, C.k, ?_, ?_, hk', ?_, ?_, hbcard, fun R hR => ⟨?_, ?_⟩⟩
  · ext d
    simp only [mem_union, mem_side, mem_compl]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hz : (kst N K).face (old ⟨d, subset_rcl K h⟩) ∈ Z
      · exact Or.inl ⟨h, subset_rcl K h, hz⟩
      · exact Or.inr ⟨h, subset_rcl K h, hz⟩
  · refine disjoint_left.2 fun d h0 h1 => ?_
    obtain ⟨-, h, hz⟩ := mem_side.1 h0
    obtain ⟨-, h', hz'⟩ := mem_side.1 h1
    exact mem_compl.1 hz' hz
  · rw [hS'card] at hin; omega
  · rw [hS'card] at hout; omega
  · exact side_oneFace hM hrot hface hKr ⟨x₀, hx₀⟩ hK hψ hsep.bd
      (fun b hb => ⟨(mem_inter.1 hb).1, mem_cycle_of_bdry hψ hsep hb⟩) hR
  · exact side_oneFace hM hrot hface hKr ⟨x₀, hx₀⟩ hK hψ (bd_compl hsep.bd)
      (fun b hb => ⟨(mem_inter.1 hb).2, mem_cycle_of_bdry hψ hsep hb⟩) hR

end Cut

end NegSSSP

end PlanarFlow
