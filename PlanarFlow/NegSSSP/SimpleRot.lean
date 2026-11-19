module

public import PlanarFlow.NegSSSP.Simple
public import PlanarFlow.BKMNW.SubMap
public import PlanarSeparator.Nested

/-!
# The simple graph of a plane map is plane, and sparse

Let `N` be a plane map with transitive rotations and faces, and `sgraph N` its simple graph (one
dart kept for every ordered pair of adjacent vertices, `PlanarFlow.NegSSSP.reps`).

* `srot`, `srot_isPlane`: **the simple graph has a plane rotation system**: the rotation of `N`
  cut down to the kept darts (its first return `PlanarFlow.Orbit.ret`). Euler's formula holds
  because deleting edges keeps the Euler gap zero (`PlanarFlow.Orbit.gap_ret_eq_zero`) and the
  kept darts are connected.
* `exists_goodTree`: hence **separator trees with separators and boundaries of `O(√m)` vertices
  exist** (`PlanarSeparator.exists_sepTree`, Lipton, Rose and Tarjan).
* `card_wset_le`: **the kept darts with both ends in a set `W` of vertices number at most
  `12 |W|`**: the submap of these darts has zero Euler gap, and its faces have three darts at
  least, except those through a vertex of degree one (no loops, no multiple edges).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv CombMap Orbit Relation NestedDissection NestedDissection.SepTree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {N : CombMap D V F}

/-! ### First returns of the rotation -/

lemma tail_ret (A : Finset D) (x : D) : N.tail (ret (rotPerm N) A x) = N.tail x := by
  obtain ⟨K, hK⟩ := ret_iterate_eq (π := rotPerm N) (A := A) x 1
  simp only [iterate_one] at hK
  rw [hK, iterate_rotPerm, tail_rot_iterate]

lemma sameCycle_ret_iff (hrot : N.RotTrans) {A : Finset D} {x y : D} (hx : x ∈ A) (hy : y ∈ A) :
    (ret (rotPerm N) A).SameCycle x y ↔ N.tail x = N.tail y := by
  rw [sameCycle_ret hx hy, sameCycle_rotPerm hrot]

lemma sameCycle_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (p : Perm α) (a b : α) :
    (e.permCongr p).SameCycle (e a) (e b) ↔ p.SameCycle a b := by
  have hit : ∀ n x, (e.permCongr p)^[n] (e x) = e (p^[n] x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [iterate_succ_apply, Equiv.permCongr_apply, e.symm_apply_apply, ih,
        ← iterate_succ_apply]
  rw [sameCycle_iff, sameCycle_iff]
  simp only [hit, e.apply_eq_iff_eq]

/-! ### The darts of the simple graph -/

variable (N) in
/-- The darts of the simple graph are the kept darts. -/
noncomputable def dartEquiv : {d // d ∈ reps N} ≃ (sgraph N).Dart :=
  Equiv.ofBijective (fun d => ⟨(N.tail d.1, N.head d.1), d.1, d.2, rfl, rfl⟩) (by
    constructor
    · intro a b h
      have h1 := congrArg (fun x : (sgraph N).Dart => x.fst) h
      have h2 := congrArg (fun x : (sgraph N).Dart => x.snd) h
      exact Subtype.ext (reps_simple a.2 b.2 h1 h2)
    · intro x
      obtain ⟨d, hd, h1, h2⟩ := x.adj
      exact ⟨⟨d, hd⟩, (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext h1 h2)⟩)

lemma dartEquiv_fst (d : {d // d ∈ reps N}) : (dartEquiv N d).fst = N.tail d.1 := rfl

lemma dartEquiv_snd (d : {d // d ∈ reps N}) : (dartEquiv N d).snd = N.head d.1 := rfl

lemma symm_fst (x : (sgraph N).Dart) : N.tail ((dartEquiv N).symm x).1 = x.fst := by
  conv_rhs => rw [← (dartEquiv N).apply_symm_apply x]
  rfl

variable (N) in
/-- The rotation of `N` cut down to the kept darts. -/
noncomputable def rotB : Perm {d // d ∈ reps N} :=
  (ret (rotPerm N) (reps N)).subtypePerm fun _ => ret_mem_iff

variable (N) in
/-- The reversal on the kept darts. -/
noncomputable def revB : Perm {d // d ∈ reps N} :=
  (revPerm N).subtypePerm fun _ => ⟨fun h => by simpa [N.rev_rev] using reps_rev (N := N) h,
    fun h => reps_rev h⟩

lemma dartEquiv_revB (a : {d // d ∈ reps N}) : dartEquiv N (revB N a) = (dartEquiv N a).symm :=
  (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext rfl (by
    change N.tail (N.rev (N.rev a.1)) = N.tail a.1
    rw [N.rev_rev]))

variable (N) in
/-- **The rotation system of the simple graph.** -/
noncomputable def srot (hrot : N.RotTrans) : Kasteleyn.RotationSystem (sgraph N) where
  rot := (dartEquiv N).permCongr (rotB N)
  fst_rot d := by
    rw [Equiv.permCongr_apply, dartEquiv_fst, ← symm_fst d]
    exact tail_ret (N := N) _ _
  sameCycle_of_fst_eq d d' h := by
    rw [← (dartEquiv N).apply_symm_apply d, ← (dartEquiv N).apply_symm_apply d',
      sameCycle_permCongr, rotB, Perm.sameCycle_subtypePerm,
      sameCycle_ret_iff hrot ((dartEquiv N).symm d).2 ((dartEquiv N).symm d').2, symm_fst,
      symm_fst]
    exact h

/-! ### Planarity -/

lemma reflTransGen_sgraph : ∀ {a b : V}, ReflTransGen N.Adj a b →
    ReflTransGen (sgraph N).Adj a b := by
  intro a b h
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    rename_i b c _
    obtain ⟨d, h1, h2⟩ := hst
    by_cases hl : N.tail d = N.head d
    · rw [← h2, ← hl, h1]; exact ih
    · obtain ⟨d', hd', e1, e2⟩ := exists_reps hl
      exact ih.tail ⟨d', hd', e1.trans h1, e2.trans h2⟩

/-- With a kept dart, every vertex is the tail of a kept dart. -/
lemma exists_reps_tail (hM : N.IsPlane) {d₀ : D} (hd₀ : d₀ ∈ reps N) (v : V) :
    ∃ d ∈ reps N, N.tail d = v := by
  rcases (reflTransGen_sgraph (hM.conn v (N.tail d₀))).cases_head with h | ⟨x, ⟨d, hd, h1, -⟩, -⟩
  · exact ⟨d₀, hd₀, h.symm⟩
  · exact ⟨d, hd, h1⟩

lemma conn_reps (hrot : N.RotTrans) (hM : N.IsPlane) :
    ∀ x ∈ reps N, ∀ y ∈ reps N, Conn (revPerm N) (ret (rotPerm N) (reps N)) x y := by
  have key : ∀ a b, ReflTransGen (sgraph N).Adj a b → ∀ x ∈ reps N, ∀ y ∈ reps N,
      N.tail x = a → N.tail y = b → Conn (revPerm N) (ret (rotPerm N) (reps N)) x y := by
    intro a b h
    induction h with
    | refl =>
      intro x hx y hy h1 h2
      exact conn_of_sameCycle ((sameCycle_ret_iff hrot hx hy).2 (h1.trans h2.symm))
    | tail _ hst ih =>
      rename_i b c _
      obtain ⟨d, hd, h1, h2⟩ := hst
      intro x hx y hy hx' hy'
      refine (ih x hx d hd hx' h1).trans ((conn_inv (ι := revPerm N) d).trans ?_)
      exact conn_of_sameCycle ((sameCycle_ret_iff hrot (reps_rev hd) hy).2
        (by rw [hy', ← h2]; rfl))
  exact fun x hx y hy => key _ _ (reflTransGen_sgraph (hM.conn _ _)) x hx y hy rfl rfl

lemma gap_reps (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) (hD : Nonempty D)
    {A : Finset D} (hA : ∀ x ∈ A, N.rev x ∈ A) :
    gap (revPerm N) (ret (rotPerm N) A) A = 0 :=
  gap_ret_eq_zero (revPerm_isInv N) (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
    (subset_univ A) (fun x hx => hA x hx) (gap_rot_eq_zero hM hrot hface hD).2

lemma card_vert_reps (hrot : N.RotTrans) (hM : N.IsPlane) {d₀ : D} (hd₀ : d₀ ∈ reps N) :
    nOrb (ret (rotPerm N) (reps N)) (reps N) = Fintype.card V := by
  have h1 : nOrb (ret (rotPerm N) (reps N)) (reps N) = ((reps N).image N.tail).card :=
    le_antisymm
      (card_image_le_of_fiber fun x hx y hy e =>
        (cls_eq_iff).2 ((sameCycle_ret_iff hrot hx hy).2 e))
      (card_image_le_of_fiber fun x hx y hy e =>
        (sameCycle_ret_iff hrot hx hy).1 ((cls_eq_iff).1 e))
  rw [h1, ← card_univ]
  congr 1
  ext v
  simp only [mem_image, mem_univ, iff_true]
  exact exists_reps_tail hM hd₀ v

lemma faceNext_eq (hrot : N.RotTrans) :
    (srot N hrot).faceNext = (dartEquiv N).permCongr (rotB N * revB N) := by
  refine Equiv.ext fun x => ?_
  have h : (dartEquiv N).symm ((Kasteleyn.dartRev _) x) = revB N ((dartEquiv N).symm x) := by
    rw [Equiv.symm_apply_eq, dartEquiv_revB, Equiv.apply_symm_apply]; rfl
  simp only [Kasteleyn.RotationSystem.faceNext, Equiv.trans_apply, srot, Equiv.permCongr_apply,
    Perm.mul_apply, h]

lemma card_face_reps (hrot : N.RotTrans) :
    Fintype.card (srot N hrot).Face =
      nOrb (ret (rotPerm N) (reps N) * revPerm N) (reps N) := by
  have hs : (rotB N * revB N) = (ret (rotPerm N) (reps N) * revPerm N).subtypePerm
      (fun x => ⟨fun h => by
        have := reps_rev (N := N) (ret_mem_iff.1 h); simpa [N.rev_rev] using this,
        fun h => ret_mem_iff.2 (reps_rev h)⟩) := by
    ext x; rfl
  have key := card_image_eq_of_iff (D := (sgraph N).Dart)
    (f := fun x => cls (ret (rotPerm N) (reps N) * revPerm N) ((dartEquiv N).symm x).1)
    (g := (srot N hrot).face) (fun x y => by
      rw [cls_eq_iff]
      change _ ↔ Quotient.mk _ x = Quotient.mk _ y
      rw [Quotient.eq]
      change _ ↔ (srot N hrot).faceNext.SameCycle x y
      rw [faceNext_eq, ← (dartEquiv N).apply_symm_apply x, ← (dartEquiv N).apply_symm_apply y,
        sameCycle_permCongr, hs, Perm.sameCycle_subtypePerm, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply])
    (fun f => Quotient.inductionOn f fun x => ⟨x, rfl⟩)
  rw [← key, nOrb]
  congr 1
  ext c
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨_, ((dartEquiv N).symm x).2, rfl⟩
  · rintro ⟨d, hd, rfl⟩; exact ⟨dartEquiv N ⟨d, hd⟩, by rw [Equiv.symm_apply_apply]⟩

/-- **The rotation system of the simple graph is plane**, when there is a kept dart. -/
theorem srot_isPlane (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {d₀ : D}
    (hd₀ : d₀ ∈ reps N) : (srot N hrot).IsPlane where
  connected := by
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => (SimpleGraph.reachable_iff_reflTransGen u v).2
      (reflTransGen_sgraph (hM.conn u v)), hM.nonempty⟩
  euler := by
    have hc := comp_eq_one (revPerm_isInv N) hd₀ (conn_reps hrot hM)
    have hg := gap_reps hM hrot hface ⟨d₀⟩ (A := reps N) (fun _ h => reps_rev h)
    have hV := card_vert_reps hrot hM hd₀
    have hF := card_face_reps hrot
    have hE := SimpleGraph.dart_card_eq_twice_card_edges (G := sgraph N)
    rw [Fintype.card_congr (dartEquiv N).symm, Fintype.card_coe] at hE
    unfold gap eul at hg
    rw [hc, hV, ← hF] at hg
    omega

/-- **Separator trees of the simple graph** with separators and boundaries of at most
`50000 √m` vertices exist, when there is a kept dart. -/
theorem exists_goodTree (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {d₀ : D}
    (hd₀ : d₀ ∈ reps N) : ∃ t, GoodTree N t := by
  obtain ⟨t, h1, h2, h3, h4⟩ := PlanarSeparator.exists_sepTree (srot_isPlane hM hrot hface hd₀)
  exact ⟨t, h1, h2, h3, h4⟩

/-! ### Sparsity -/

/-- Counting orbits: if the orbits avoiding `X` have three elements at least, there are at most
`|X| + |A| / 3` orbits. -/
lemma nOrb_le_of_three {φ : Perm D} {A X : Finset D} (hφ : Stable φ A) (hXA : X ⊆ A)
    (h3 : ∀ x ∈ A, (∀ y ∈ X, ¬ φ.SameCycle x y) → φ x ≠ x ∧ φ (φ x) ≠ x ∧ φ (φ x) ≠ φ x) :
    3 * nOrb φ A ≤ 3 * X.card + A.card := by
  classical
  set O := A.image (cls φ)
  set O₁ := X.image (cls φ)
  have hO₁ : O₁ ⊆ O := image_subset_image hXA
  have hcard : O.card = O₁.card + (O \ O₁).card := by
    rw [card_sdiff_of_subset hO₁]; have := card_le_card hO₁; omega
  have h1 : O₁.card ≤ X.card := card_image_le
  have hmem : ∀ {x z : D}, z ∈ cls φ x ↔ φ.SameCycle x z := by
    intro x z; unfold cls; simp
  have h2 : 3 * (O \ O₁).card ≤ A.card := by
    have hdisj : (↑(O \ O₁) : Set (Finset D)).PairwiseDisjoint (fun c => c ∩ A) := by
      intro c hc c' hc' hne
      simp only [coe_sdiff, Set.mem_sdiff, mem_coe] at hc hc'
      obtain ⟨x, -, rfl⟩ := mem_image.1 hc.1
      obtain ⟨x', -, rfl⟩ := mem_image.1 hc'.1
      refine disjoint_left.2 fun z hz hz' => hne ?_
      rw [mem_inter, hmem] at hz hz'
      exact cls_eq_iff.2 (hz.1.trans hz'.1.symm)
    have hsum : ∑ c ∈ O \ O₁, (c ∩ A).card ≤ A.card := by
      rw [← card_biUnion hdisj]
      exact card_le_card fun z hz => by
        obtain ⟨c, -, hc⟩ := mem_biUnion.1 hz; exact (mem_inter.1 hc).2
    have hge : ∀ c ∈ O \ O₁, 3 ≤ (c ∩ A).card := by
      intro c hc
      obtain ⟨hcO, hcO₁⟩ := mem_sdiff.1 hc
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hcO
      have hX : ∀ y ∈ X, ¬ φ.SameCycle x y := fun y hy h =>
        hcO₁ (mem_image.2 ⟨y, hy, (cls_eq_iff.2 h).symm⟩)
      obtain ⟨n1, n2, n3⟩ := h3 x hx hX
      have hs : ({x, φ x, φ (φ x)} : Finset D) ⊆ cls φ x ∩ A := by
        intro z hz
        simp only [mem_insert, mem_singleton] at hz
        rw [mem_inter, hmem]
        rcases hz with rfl | rfl | rfl
        · exact ⟨Perm.SameCycle.refl _ _, hx⟩
        · exact ⟨Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _), hφ _ hx⟩
        · exact ⟨Perm.sameCycle_apply_right.2 (Perm.sameCycle_apply_right.2
            (Perm.SameCycle.refl _ _)), hφ _ (hφ _ hx)⟩
      refine le_trans ?_ (card_le_card hs)
      rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
      · simpa using n3.symm
      · simp only [mem_insert, mem_singleton, not_or]
        exact ⟨fun h => n1 h.symm, fun h => n2 h.symm⟩
    have := card_nsmul_le_sum (O \ O₁) (fun c => (c ∩ A).card) 3 hge
    simp only [smul_eq_mul] at this
    omega
  unfold nOrb
  change 3 * O.card ≤ _
  omega

variable (N) in
/-- The kept darts with both ends in `W`. -/
noncomputable def wset (W : Finset V) : Finset D := by
  classical exact (reps N).filter fun d => N.tail d ∈ W ∧ N.head d ∈ W

lemma mem_wset {W : Finset V} {d : D} :
    d ∈ wset N W ↔ d ∈ reps N ∧ N.tail d ∈ W ∧ N.head d ∈ W := by
  classical
  unfold wset; simp

/-- **Sparsity of the simple graph**: at most `12 |W|` kept darts have both ends in `W`. -/
theorem card_wset_le (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    (W : Finset V) : (wset N W).card ≤ 12 * W.card := by
  classical
  set A := wset N W
  rcases A.eq_empty_or_nonempty with hA0 | ⟨d₀, -⟩
  · rw [hA0]; simp
  have hAι : ∀ x ∈ A, N.rev x ∈ A := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := mem_wset.1 hx
    exact mem_wset.2 ⟨reps_rev h1, by simpa using h3, by simpa using h2⟩
  set π := ret (rotPerm N) A
  have hg : gap (revPerm N) π A = 0 := gap_reps hM hrot hface ⟨d₀⟩ hAι
  have hAs : Stable (revPerm N) A := hAι
  -- the vertices
  have hV : nOrb π A ≤ W.card := by
    refine (card_image_le_of_fiber (g := N.tail) fun x hx y hy e =>
      (cls_eq_iff).2 ((sameCycle_ret_iff hrot hx hy).2 e)).trans (card_le_card ?_)
    intro v hv
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hv
    exact (mem_wset.1 hx).2.1
  -- the darts alone at their vertex
  set X := A.filter fun x => π x = x
  have hXA : X ⊆ A := filter_subset _ _
  have hX : X.card ≤ nOrb π A := by
    refine le_trans (le_of_eq ?_) (card_le_card (image_subset_image hXA))
    refine (card_image_of_injOn fun x hx y hy e => ?_).symm
    have hfix : π x = x := (mem_filter.1 hx).2
    obtain ⟨n, hn⟩ := sameCycle_iff.1 (cls_eq_iff.1 e)
    rw [← hn]
    exact (iterate_fixed hfix n).symm
  -- the faces
  have hF : 3 * nOrb (π * revPerm N) A ≤ 3 * X.card + A.card := by
    refine nOrb_le_of_three ((stable_ret _ A).mul hAs) hXA fun x hx hXx => ?_
    have hxr := (mem_wset.1 hx).1
    have hl := reps_loop hxr
    have tπ : ∀ z, N.tail (π z) = N.tail z := tail_ret A
    have n1 : (π * revPerm N) x ≠ x := by
      intro h
      have := congrArg N.tail h
      rw [Perm.mul_apply, tπ, revPerm_apply, tail_rev] at this
      exact hl this.symm
    refine ⟨n1, fun h => ?_, fun h => n1 ((π * revPerm N).injective h)⟩
    set y := (π * revPerm N) x with hy
    have hyA : y ∈ A := (stable_ret _ A).mul hAs x hx
    have ty : N.tail y = N.head x := by
      rw [hy, Perm.mul_apply, tπ, revPerm_apply, tail_rev]
    have tx : N.tail x = N.head y := by
      have := congrArg N.tail h
      rw [Perm.mul_apply, tπ, revPerm_apply, tail_rev] at this
      exact this.symm
    have hyx : y = N.rev x := reps_simple (mem_wset.1 hyA).1 (reps_rev hxr)
      (by rw [ty, tail_rev]) (by rw [← tx, head_rev])
    have hfix : π (N.rev x) = N.rev x := by
      have : y = π (N.rev x) := rfl
      rw [← this, hyx]
    exact hXx (N.rev x) (mem_filter.2 ⟨hAι x hx, hfix⟩)
      (by rw [← hyx]; exact Perm.sameCycle_apply_right.2 (Perm.SameCycle.refl _ _))
  unfold gap eul at hg
  have hc : (0 : ℤ) ≤ comp (revPerm N) π A := Nat.cast_nonneg _
  omega

/-- The kept darts with an end in `U` have both ends in `U` and its boundary. -/
lemma eset_subset_wset (U : Finset V) :
    eset N U ⊆ wset N (U ∪ NestedDissection.bdry (sgraph N) U) := by
  intro d hd
  obtain ⟨hr, ht | hh⟩ := mem_eset.1 hd
  · refine mem_wset.2 ⟨hr, mem_union_left _ ht, ?_⟩
    by_cases h : N.head d ∈ U
    · exact mem_union_left _ h
    · exact mem_union_right _ (by
        simp only [NestedDissection.bdry, mem_filter, mem_univ, true_and]
        exact ⟨h, _, ht, d, hr, rfl, rfl⟩)
  · refine mem_wset.2 ⟨hr, ?_, mem_union_left _ hh⟩
    by_cases h : N.tail d ∈ U
    · exact mem_union_left _ h
    · exact mem_union_right _ (by
        simp only [NestedDissection.bdry, mem_filter, mem_univ, true_and]
        exact ⟨h, _, hh, N.rev d, reps_rev hr, by simp, by simp⟩)

end NegSSSP

end PlanarFlow
