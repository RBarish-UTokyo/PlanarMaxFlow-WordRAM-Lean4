module

public import PlanarFlow.BKMNW.Matching
public import PlanarSeparator.MillerTri

/-!
# Triangulating with darts of capacity zero

Line 1 of Algorithm 1 of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput.
46(4), 2017) adds arcs of capacity zero to triangulate the graph, as needed by cycle separators.
This file does it with the stellar subdivision (`PlanarSeparator.Map.stellar`): a new vertex in
every face, joined to every corner of the face by a spoke of capacity zero in both directions.

## The two kinds of maps

The maps of `PlanarFlow` (`PlanarFlow.CombMap`: reversal, tails, faces, boundary walks) and those
of `PlanarSeparator` (`PlanarSeparator.Map`: reversal and rotation as permutations, vertices)
describe the same objects:

* `CombMap.ofSep N`: the map of `PlanarFlow` of a map `N` of `PlanarSeparator` (`next = φ`, the
  faces are the cycles of `φ`); it is plane when `N` is, with transitive rotations and faces
  (`ofSep_isPlane`, `ofSep_rotTrans`, `ofSep_faceTrans`).
* `CombMap.toSep M hrot`: the map of `PlanarSeparator` of a map `M` of `PlanarFlow` with
  transitive rotations (the rotation is `rot`); it is plane when `M` is plane with transitive
  faces and a dart (`toSep_isPlane`), and its faces are those of `M` (`card_toSep_face`).

## The triangulation

* `CombMap.triMap M hrot = ofSep (toSep M hrot).stellar`, with darts `StDart D` (`old d`, and
  the spokes `up d`, `down d`), vertices `V ⊕ Face` (the vertices of `M` and the centres of its
  faces): plane with transitive rotations and faces (`triMap_isPlane`, `triMap_rotTrans`,
  `triMap_faceTrans`), three times as many darts (`card_triMap_darts`), all of whose faces are
  triangles with three distinct edges when `M` has no loop (`triMap_isTriangle`).
* `isMax_restrict`: for an embedding of a map `M` into a map `M'` in which the darts outside the
  image have capacity zero, the restriction of a maximum flow of `M'` is a maximum flow of `M`.
* `maxflow_tri`: **the algorithm `algo` on the triangulated map with the spokes of capacity zero,
  restricted to the darts of `M`, is a maximum flow of `M`**, on every plane map with transitive
  rotations and faces (the hypotheses of `PlanarFlow.BKMNW.maxflow_plane`).
* `maxflow_tri_cost`: the same for `runL` on a decomposition of the triangulated map meeting
  `PlanarFlow.BKMNW.BalDecA`, with the cost bound `O(n log³ n)` in the number `n` of darts of `M`.
  They exist when every vertex of `M` is a terminal (`exists_balDecA_tri`, with `s = 3 n`); with
  `s` independent of `n` they are proved to exist on the preprocessed map below, not on the
  triangulated map itself (`PlanarFlow.BKMNW.exists_balDecA_pre`).

## Pendant terminals

Footnote 4 of the article replaces a terminal `u` by a new terminal `u'` joined to `u`, so that
the separators can avoid the terminals (a simple cycle never passes through a vertex of degree
one). With the pendant edges of `PlanarFlow.CombMap.pendant` (one at every vertex):

* `isMax_pendant`: with capacity `∑ u` in both directions on the pendant edges of the terminals
  and zero on the others (`pendCap`), the restriction of a maximum flow between the pendant
  neighbours of the terminals is a maximum flow of `M`; the new terminals have degree one
  (`pendant_tail_eq_inr`).
* `maxflow_pre`: **the algorithm `algo` on the preprocessed map** (`preMap`: triangulation, then
  pendant terminals), **restricted to the darts of `M`, is a maximum flow of `M`**, on every plane
  map with transitive rotations and faces; the preprocessed map has at most `7 n` darts
  (`card_preMap_darts`). The cost theorem `PlanarFlow.BKMNW.runL_isMax_costA` applies to it for
  any decomposition meeting `BalDecA`; such decompositions exist when `M` has no loop
  (`PlanarFlow.BKMNW.exists_balDecA_pre`, `PlanarFlow/BKMNW/ExistPre.lean`), which gives the
  unconditional bound `PlanarFlow.BKMNW.maxflow_pre_cost`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace CombMap

open Finset

/-! ### From the maps of `PlanarSeparator` -/

section OfSep

variable {D P : Type*} (N : PlanarSeparator.Map D P)

/-- **The map of `PlanarFlow` of a map of `PlanarSeparator`**: the reversal `α`, the vertices,
the faces (the cycles of the face permutation `φ`), and `next = φ`. -/
def ofSep : CombMap D P N.Face where
  rev := N.α
  rev_rev := N.α_α
  rev_ne := N.α_ne
  tail := N.vert
  face := N.face
  next := N.φ
  next_injective := N.φ.injective
  face_next := N.face_φ
  tail_next d := N.vert_φ d

@[simp] lemma ofSep_rev (d : D) : (ofSep N).rev d = N.α d := rfl
@[simp] lemma ofSep_tail (d : D) : (ofSep N).tail d = N.vert d := rfl
@[simp] lemma ofSep_face (d : D) : (ofSep N).face d = N.face d := rfl
@[simp] lemma ofSep_next (d : D) : (ofSep N).next d = N.φ d := rfl

lemma ofSep_rot (d : D) : (ofSep N).rot d = N.σ d := by
  simp [CombMap.rot, PlanarSeparator.Map.φ_apply, N.α_α]

variable [Fintype D]

theorem ofSep_rotTrans : (ofSep N).RotTrans := fun d d' h => by
  obtain ⟨n, hn⟩ := (N.sameCycle d d' h).exists_nat_pow_eq
  refine ⟨n, ?_⟩
  have e : (ofSep N).rot = N.σ := funext (ofSep_rot N)
  rw [e, ← Equiv.Perm.coe_pow]
  exact hn

theorem ofSep_faceTrans : (ofSep N).FaceTrans := fun d d' h => by
  obtain ⟨n, hn⟩ := (N.face_eq_face_iff.1 h).exists_nat_pow_eq
  refine ⟨n, ?_⟩
  have e : (ofSep N).next = N.φ := rfl
  rw [e, ← Equiv.Perm.coe_pow]
  exact hn

variable [DecidableEq D] [Fintype P] [DecidableEq P]

/-- **The map of a plane map of `PlanarSeparator` is plane.** -/
theorem ofSep_isPlane {N : PlanarSeparator.Map D P} (hN : N.IsPlane) : (ofSep N).IsPlane where
  nonempty := hN.nonempty
  conn a b := by
    obtain ⟨da, rfl⟩ := hN.exists_dart a
    obtain ⟨db, rfl⟩ := hN.exists_dart b
    induction hN.connected da db with
    | refl => exact .refl
    | tail _ hst ih =>
      rcases hst with rfl | rfl
      · rwa [N.vert_σ]
      · exact ih.tail ⟨_, rfl, rfl⟩
  dualConn x y := by
    obtain ⟨dx, rfl⟩ := N.face_surjective x
    obtain ⟨dy, rfl⟩ := N.face_surjective y
    induction hN.connected dx dy with
    | refl => exact .refl
    | tail _ hst ih =>
      rcases hst with rfl | rfl
      · exact ih.tail ⟨_, rfl, (N.face_σ _).symm⟩
      · exact ih.tail ⟨_, rfl, rfl⟩
  euler := by
    have h1 := hN.euler
    have h2 := N.card_darts
    omega

end OfSep

/-! ### To the maps of `PlanarSeparator` -/

section ToSep

variable {D V F : Type*} [Fintype D] [DecidableEq D] (M : CombMap D V F)

/-- **The map of `PlanarSeparator` of a map with transitive rotations**: the reversal and the
rotation as permutations, the tails as vertices. -/
noncomputable def toSep (hrot : M.RotTrans) : PlanarSeparator.Map D V where
  α := Function.Involutive.toPerm M.rev M.rev_rev
  σ := Equiv.ofBijective M.rot (Finite.injective_iff_bijective.1 M.rot_injective)
  vert := M.tail
  α_α := M.rev_rev
  α_ne := M.rev_ne
  vert_σ := M.tail_rot
  sameCycle d d' h := by
    obtain ⟨k, hk⟩ := hrot d d' h
    exact ⟨k, by rw [zpow_natCast, Equiv.Perm.coe_pow]; exact hk⟩

variable {M}

@[simp] lemma toSep_α (hrot : M.RotTrans) (d : D) : (M.toSep hrot).α d = M.rev d := rfl
@[simp] lemma toSep_σ (hrot : M.RotTrans) (d : D) : (M.toSep hrot).σ d = M.rot d := rfl
@[simp] lemma toSep_vert (hrot : M.RotTrans) (d : D) : (M.toSep hrot).vert d = M.tail d := rfl

@[simp] lemma toSep_φ (hrot : M.RotTrans) (d : D) : (M.toSep hrot).φ d = M.next d := by
  simp [PlanarSeparator.Map.φ_apply, CombMap.rot, M.rev_rev]

lemma toSep_φ_pow (hrot : M.RotTrans) (n : ℕ) (d : D) :
    ((M.toSep hrot).φ ^ n) d = M.next^[n] d := by
  rw [Equiv.Perm.coe_pow]
  have e : ⇑(M.toSep hrot).φ = M.next := funext (toSep_φ hrot)
  rw [e]

lemma face_next_iterate (n : ℕ) (d : D) : M.face (M.next^[n] d) = M.face d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', M.face_next, ih]

/-- The faces of `toSep M hrot` to the faces of `M`. -/
noncomputable def toSepFace (hrot : M.RotTrans) : (M.toSep hrot).Face → F :=
  Quotient.lift M.face fun d d' h => by
    obtain ⟨n, hn⟩ := (show (M.toSep hrot).φ.SameCycle d d' from h).exists_nat_pow_eq
    rw [← hn, toSep_φ_pow, face_next_iterate]

@[simp] lemma toSepFace_face (hrot : M.RotTrans) (d : D) :
    toSepFace hrot ((M.toSep hrot).face d) = M.face d := rfl

variable [Fintype F]

/-- **The faces of `toSep M hrot` are those of `M`**, for a plane map with transitive rotations
and faces and a dart. -/
theorem card_toSep_face [Fintype V] (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    [Nonempty D] : Fintype.card (M.toSep hrot).Face = Fintype.card F := by
  refine Fintype.card_of_bijective (f := toSepFace hrot) ⟨fun x y h => ?_, fun x => ?_⟩
  · obtain ⟨d, rfl⟩ := (M.toSep hrot).face_surjective x
    obtain ⟨d', rfl⟩ := (M.toSep hrot).face_surjective y
    simp only [toSepFace_face] at h
    obtain ⟨k, hk⟩ := hface d d' h
    exact (M.toSep hrot).face_eq_face_iff.2 ⟨k, by rw [zpow_natCast, toSep_φ_pow, hk]⟩
  · obtain ⟨d₀⟩ := ‹Nonempty D›
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hM.dualConn (M.face d₀) x) with
      h | ⟨c, -, d, -, hd⟩
    · exact ⟨(M.toSep hrot).face d₀, by rw [toSepFace_face, h]⟩
    · exact ⟨(M.toSep hrot).face (M.rev d), by rw [toSepFace_face, hd]⟩

lemma reach_rot_iterate (hrot : M.RotTrans) (k : ℕ) (d : D) :
    Relation.ReflTransGen (fun a b => b = (M.toSep hrot).σ a ∨ b = (M.toSep hrot).α a) d
      (M.rot^[k] d) := by
  induction k with
  | zero => exact .refl
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.tail (Or.inl rfl)

/-- **The map of `PlanarSeparator` of a plane map with transitive rotations and faces and a dart
is plane.** -/
theorem toSep_isPlane [Fintype V] [DecidableEq V] (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) [Nonempty D] : (M.toSep hrot).IsPlane where
  exists_dart v := by
    obtain ⟨e, he⟩ := exists_tail_eq hM
    exact ⟨e v, he v⟩
  connected d d' := by
    have key : ∀ b, Relation.ReflTransGen M.Adj (M.tail d) b → ∃ x, M.tail x = b ∧
        Relation.ReflTransGen (fun a b => b = (M.toSep hrot).σ a ∨ b = (M.toSep hrot).α a) d x := by
      intro b hb
      induction hb with
      | refl => exact ⟨d, rfl, .refl⟩
      | tail _ hst ih =>
        obtain ⟨x, hx, hdx⟩ := ih
        obtain ⟨e, he1, he2⟩ := hst
        obtain ⟨k, hk⟩ := hrot x e (by rw [hx, he1])
        refine ⟨M.rev e, by rw [tail_rev, he2], ?_⟩
        exact (hdx.trans (hk ▸ reach_rot_iterate hrot k x)).tail (Or.inr rfl)
    obtain ⟨x, hx, hdx⟩ := key _ (hM.conn (M.tail d) (M.tail d'))
    obtain ⟨k, hk⟩ := hrot x d' hx
    exact hdx.trans (hk ▸ reach_rot_iterate hrot k x)
  euler := by
    have h1 := hM.euler
    have h2 := (M.toSep hrot).card_darts
    have h3 := card_toSep_face hM hrot hface
    omega

end ToSep

/-! ### The triangulation -/

section Tri

open PlanarSeparator.StDart

variable {D V F : Type*} [Fintype D] [DecidableEq D] (M : CombMap D V F)

/-- **The triangulated map**: the stellar subdivision of `M`, with darts `old d` and the spokes
`up d` (from the tail of `d` to the centre of its face) and `down d` (back), and vertices the
vertices of `M` and the centres of its faces. -/
noncomputable def triMap (hrot : M.RotTrans) :
    CombMap (PlanarSeparator.StDart D) (V ⊕ (M.toSep hrot).Face)
      (M.toSep hrot).stellar.Face :=
  ofSep (M.toSep hrot).stellar

variable {M}

@[simp] lemma triMap_rev_old (hrot : M.RotTrans) (d : D) :
    (M.triMap hrot).rev (old d) = old (M.rev d) := rfl
@[simp] lemma triMap_rev_up (hrot : M.RotTrans) (d : D) :
    (M.triMap hrot).rev (up d) = down d := rfl
@[simp] lemma triMap_rev_down (hrot : M.RotTrans) (d : D) :
    (M.triMap hrot).rev (down d) = up d := rfl
@[simp] lemma triMap_tail_old (hrot : M.RotTrans) (d : D) :
    (M.triMap hrot).tail (old d) = .inl (M.tail d) := rfl
@[simp] lemma triMap_tail_up (hrot : M.RotTrans) (d : D) :
    (M.triMap hrot).tail (up d) = .inl (M.tail d) := rfl
@[simp] lemma triMap_tail_down (hrot : M.RotTrans) (d : D) :
    (M.triMap hrot).tail (down d) = .inr ((M.toSep hrot).face d) := rfl

theorem triMap_rotTrans (hrot : M.RotTrans) : (M.triMap hrot).RotTrans := ofSep_rotTrans _

theorem triMap_faceTrans (hrot : M.RotTrans) : (M.triMap hrot).FaceTrans := ofSep_faceTrans _

/-- **The triangulated map of a plane map with transitive rotations and faces and a dart is
plane.** -/
theorem triMap_isPlane [Fintype V] [DecidableEq V] [Fintype F] (hM : M.IsPlane)
    (hrot : M.RotTrans) (hface : M.FaceTrans) [Nonempty D] : (M.triMap hrot).IsPlane :=
  ofSep_isPlane (PlanarSeparator.Map.isPlane_stellar (toSep_isPlane hM hrot hface))

/-- The triangulated map has three times as many darts. -/
theorem card_triMap_darts : Fintype.card (PlanarSeparator.StDart D) = 3 * Fintype.card D :=
  PlanarSeparator.StDart.card

/-- **The faces of the triangulated map are triangles**, with three distinct edges, when `M` has
no loop. -/
theorem triMap_isTriangle (hrot : M.RotTrans) (hl : ∀ d, M.head d ≠ M.tail d)
    (x : PlanarSeparator.StDart D) : (M.toSep hrot).stellar.IsTriangle x :=
  PlanarSeparator.Map.isTriangle_stellar _ (fun d => hl d) x

end Tri

end CombMap

namespace BKMNW

open Finset CombMap

/-! ### Restricting a maximum flow -/

section Restrict

variable {D V F D' V' F' : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']

/-- **An embedding of maps**: injections of the darts and the vertices commuting with the
reversal and the tails. -/
structure Embeds (M : CombMap D V F) (M' : CombMap D' V' F') (ιd : D → D') (ιv : V → V') :
    Prop where
  injd : Function.Injective ιd
  injv : Function.Injective ιv
  rev : ∀ d, M'.rev (ιd d) = ιd (M.rev d)
  tail : ∀ d, M'.tail (ιd d) = ιv (M.tail d)

variable {M : CombMap D V F} {M' : CombMap D' V' F'} {ιd : D → D'} {ιv : V → V'}

lemma Embeds.rev_out (h : Embeds M M' ιd ιv) {d' : D'} (hd : ∀ d, ιd d ≠ d') (d : D) :
    ιd d ≠ M'.rev d' := fun e => hd (M.rev d) (by rw [← h.rev, e, M'.rev_rev])

/-- The net outflow at the image of a vertex of a function vanishing off the image of the darts
is that of its restriction. -/
lemma Embeds.div_eq (h : Embeds M M' ιd ιv) (g : D' → ℤ)
    (hg : ∀ d', (∀ d, ιd d ≠ d') → g d' = 0) (v : V) :
    M'.div g (ιv v) = M.div (fun d => g (ιd d)) v := by
  unfold CombMap.div
  symm
  rw [← sum_image (f := g) (s := univ.filter fun d => M.tail d = v)
    (fun a _ b _ e => h.injd e)]
  refine sum_subset (fun x hx => ?_) (fun x hx hx' => ?_)
  · obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
    simp only [mem_filter, mem_univ, true_and] at hd ⊢
    rw [h.tail, hd]
  · refine hg x fun d e => hx' ?_
    subst e
    simp only [mem_filter, mem_univ, true_and] at hx
    exact mem_image.2 ⟨d, by simpa using h.injv (by rw [← h.tail]; exact hx), rfl⟩

/-- The net outflow off the image of the vertices of a function vanishing off the image of the
darts is zero. -/
lemma Embeds.div_out (h : Embeds M M' ιd ιv) (g : D' → ℤ)
    (hg : ∀ d', (∀ d, ιd d ≠ d') → g d' = 0) {v' : V'} (hv : ∀ v, ιv v ≠ v') :
    M'.div g v' = 0 := by
  unfold CombMap.div
  refine sum_eq_zero fun x hx => hg x fun d e => hv (M.tail d) ?_
  subst e
  simp only [mem_filter, mem_univ, true_and] at hx
  rw [← h.tail, hx]

lemma Embeds.val_eq (h : Embeds M M' ιd ιv) (g : D' → ℤ)
    (hg : ∀ d', (∀ d, ιd d ≠ d') → g d' = 0) (S : Finset V) :
    val M' (S.image ιv) g = val M S (fun d => g (ιd d)) := by
  unfold val
  rw [sum_image fun a _ b _ e => h.injv e]
  exact sum_congr rfl fun v _ => h.div_eq g hg v

/-- **The restriction of a maximum flow**: if `M` embeds into `M'`, the capacities agree on the
image and vanish off it, then the restriction of a maximum flow of `M'` from the image of `S` to
the image of `T` is a maximum flow of `M` from `S` to `T`. -/
theorem isMax_restrict (h : Embeds M M' ιd ιv) {u : D → ℤ} {u' : D' → ℤ}
    (hu : ∀ d, u' (ιd d) = u d) (hout : ∀ d', (∀ d, ιd d ≠ d') → u' d' = 0)
    {S T : Finset V} {f' : D' → ℤ} (hf : IsMax M' u' (S.image ιv) (T.image ιv) f') :
    IsMax M u S T (fun d => f' (ιd d)) := by
  have hps := hf.1.toIsPseudo
  -- the flow vanishes off the image
  have h0 : ∀ d', (∀ d, ιd d ≠ d') → f' d' = 0 := fun d' hd => by
    have h1 := hps.le_cap d'
    have h2 := hps.le_cap (M'.rev d')
    rw [hout d' hd] at h1
    rw [hout _ (h.rev_out hd), hps.antisymm d'] at h2
    omega
  have hni : ∀ {v : V} {X : Finset V}, v ∉ X → ιv v ∉ X.image ιv := fun hv h' => by
    obtain ⟨w, hw, e⟩ := mem_image.1 h'
    exact hv (h.injv e ▸ hw)
  refine ⟨⟨⟨fun d => ?_, fun d => ?_⟩, fun v hS hT => ?_⟩, fun g hg => ?_⟩
  · show f' (ιd (M.rev d)) = - f' (ιd d)
    rw [← h.rev, hps.antisymm]
  · show f' (ιd d) ≤ u d
    rw [← hu]; exact hps.le_cap _
  · rw [← h.div_eq f' h0]
    exact hf.1.conserve _ (hni hS) (hni hT)
  -- extending a flow of `M` by zero
  set g' : D' → ℤ := Function.extend ιd g 0 with hg'def
  have hg'i : ∀ d, g' (ιd d) = g d := fun d => h.injd.extend_apply g 0 d
  have hg'o : ∀ d', (∀ d, ιd d ≠ d') → g' d' = 0 := fun d' hd => by
    rw [hg'def, Function.extend_apply' _ _ _ fun ⟨d, e⟩ => hd d e]; rfl
  have hgr : (fun d => g' (ιd d)) = g := funext hg'i
  have hflow : IsFlow M' u' (S.image ιv) (T.image ιv) g' := by
    refine ⟨⟨fun d' => ?_, fun d' => ?_⟩, fun v' hS hT => ?_⟩
    · by_cases hd : ∃ d, ιd d = d'
      · obtain ⟨d, rfl⟩ := hd
        rw [h.rev, hg'i, hg'i, hg.antisymm]
      · push Not at hd
        rw [hg'o _ (h.rev_out hd), hg'o _ hd, neg_zero]
    · by_cases hd : ∃ d, ιd d = d'
      · obtain ⟨d, rfl⟩ := hd
        rw [hg'i, hu]; exact hg.le_cap d
      · push Not at hd
        rw [hg'o _ hd, hout _ hd]
    · by_cases hv : ∃ v, ιv v = v'
      · obtain ⟨v, rfl⟩ := hv
        rw [h.div_eq g' hg'o, hgr]
        exact hg.conserve v (fun h' => hS (mem_image_of_mem _ h'))
          (fun h' => hT (mem_image_of_mem _ h'))
      · push Not at hv
        exact h.div_out g' hg'o hv
  have := hf.2 g' hflow
  rwa [h.val_eq g' hg'o, h.val_eq f' h0, hgr] at this

end Restrict

/-! ### Pendant terminals -/

section Pendant

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {M : CombMap D V F} {e : V → D}

/-- **The capacities with pendant terminals** (footnote 4 of the article): those of `M` on its
darts, `big` in both directions on the pendant edge of every terminal, zero on the other pendant
edges. The sources and the sinks are then the pendant neighbours of `S` and `T`. -/
def pendCap (u : D → ℤ) (S T : Finset V) (big : ℤ) : D ⊕ (V × Bool) → ℤ
  | .inl d => u d
  | .inr (v, _) => if v ∈ S ∪ T then big else 0

lemma pendCap_nonneg {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) (S T : Finset V) {big : ℤ} (hb : 0 ≤ big)
    (x : D ⊕ (V × Bool)) : 0 ≤ pendCap u S T big x := by
  rcases x with d | ⟨v, b⟩
  · exact hu d
  · simp only [pendCap]; split_ifs <;> omega

/-- The net outflow of a flow at a vertex is at most the total capacity. -/
lemma abs_div_le {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {g : D → ℤ} (hg : IsPseudo M u g) (v : V) :
    |M.div g v| ≤ ∑ d, u d := by
  have h1 : M.div g v ≤ ∑ d, u d := by
    unfold CombMap.div
    exact (sum_le_sum fun d _ => hg.le_cap d).trans
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun d _ _ => hu d)
  have h2 : -M.div g v ≤ ∑ d, u d := by
    unfold CombMap.div
    rw [← sum_neg_distrib]
    have e : ∑ d, u d = ∑ d, u (M.rev d) :=
      (Fintype.sum_equiv (Function.Involutive.toPerm M.rev M.rev_rev) _ _ fun _ => rfl).symm
    rw [e]
    refine (sum_le_sum fun d _ => ?_).trans
      (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun d _ _ => hu (M.rev d))
    have := hg.le_cap (M.rev d)
    rw [hg.antisymm] at this
    exact this
  exact abs_le.2 ⟨by omega, h1⟩

/-- **Footnote 4 of the article: the restriction of a maximum flow with pendant terminals.** With a
pendant edge at every vertex, of capacity `∑ u` in both directions at the terminals and zero
elsewhere, the restriction to the darts of `M` of a maximum flow from the pendant neighbours of
`S` to those of `T` is a maximum flow of `M` from `S` to `T`. -/
theorem isMax_pendant (he : ∀ v, M.tail (e v) = v) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d)
    {S T : Finset V} {f : D ⊕ (V × Bool) → ℤ}
    (hf : IsMax (M.pendant e he) (pendCap u S T (∑ d, u d)) (S.image Sum.inr) (T.image Sum.inr)
      f) :
    IsMax M u S T (fun d => f (.inl d)) := by
  have hps := hf.1.toIsPseudo
  have h0 : ∀ v, v ∉ S ∪ T → ∀ b, f (.inr (v, b)) = 0 := fun v hv b => by
    have h1 := hps.le_cap (.inr (v, b))
    have h2 := hps.le_cap (.inr (v, !b))
    have h3 := hps.antisymm (.inr (v, b))
    simp only [pendCap, hv, ite_false] at h1 h2
    simp only [pendant_rev_inr] at h3
    omega
  have hni : ∀ (v : V) (X : Finset V), (Sum.inl v : V ⊕ V) ∉ X.image Sum.inr := by simp
  -- with conservation at the vertices of `M`, the values agree
  have hval : ∀ g : D ⊕ (V × Bool) → ℤ, IsPseudo (M.pendant e he) (pendCap u S T (∑ d, u d)) g →
      (∀ v, (M.pendant e he).div g (.inl v) = 0) →
      val (M.pendant e he) (S.image Sum.inr) g = val M S (fun d => g (.inl d)) := by
    intro g hg hc
    unfold val
    rw [sum_image fun _ _ _ _ h => Sum.inr.inj h]
    refine sum_congr rfl fun v _ => ?_
    have h1 := hc v
    rw [pdiv_inl he] at h1
    have h2 := hg.antisymm (.inr (v, true))
    simp only [pendant_rev_inr, Bool.not_true] at h2
    rw [pdiv_inr he]
    omega
  refine ⟨⟨⟨fun d => hps.antisymm (.inl d), fun d => hps.le_cap (.inl d)⟩, fun v hS hT => ?_⟩,
    fun g hg => ?_⟩
  · have h1 := hf.1.conserve (.inl v) (hni v S) (hni v T)
    rw [pdiv_inl he, h0 v (by simp [hS, hT]) true, add_zero] at h1
    exact h1
  -- extending a flow of `M`
  let g' : D ⊕ (V × Bool) → ℤ := fun
    | .inl d => g d
    | .inr (v, true) => - M.div g v
    | .inr (v, false) => M.div g v
  have hg'c : ∀ v, (M.pendant e he).div g' (.inl v) = 0 := fun v => by
    rw [pdiv_inl he]; simp [g']
  have hflow : IsFlow (M.pendant e he) (pendCap u S T (∑ d, u d)) (S.image Sum.inr)
      (T.image Sum.inr) g' := by
    refine ⟨⟨fun x => ?_, fun x => ?_⟩, fun x hS hT => ?_⟩
    · rcases x with d | ⟨v, _ | _⟩
      · exact hg.antisymm d
      · simp [g']
      · simp [g']
    · have hab := abs_div_le hu hg.toIsPseudo
      rcases x with d | ⟨v, b⟩
      · exact hg.le_cap d
      · simp only [pendCap]
        split_ifs with hv
        · have := hab v
          cases b <;> simp only [g'] <;> rw [abs_le] at this <;> omega
        · simp only [mem_union, not_or] at hv
          have := hg.conserve v hv.1 hv.2
          cases b <;> simp [g', this]
    · rcases x with v | v
      · exact hg'c v
      · rw [pdiv_inr he]
        exact hg.conserve v (fun h => hS (mem_image_of_mem _ h))
          (fun h => hT (mem_image_of_mem _ h))
  have := hf.2 g' hflow
  rwa [hval g' hflow.toIsPseudo hg'c, hval f hps fun v => hf.1.conserve _ (hni v S) (hni v T)]
    at this

/-- The pendant neighbour `inr v` of `v` is the tail of exactly one dart, `inr (v, false)`: the
terminals of the map with pendant terminals have degree one. -/
lemma pendant_tail_eq_inr (he : ∀ v, M.tail (e v) = v) (x : D ⊕ (V × Bool)) (v : V) :
    (M.pendant e he).tail x = .inr v ↔ x = .inr (v, false) := by
  rcases x with d | ⟨w, _ | _⟩ <;> simp

end Pendant

/-! ### The algorithm on the triangulated map -/

section Tri

open PlanarSeparator.StDart

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The capacities of the triangulated map: those of `M` on its darts, zero on the spokes. -/
def triCap (u : D → ℤ) : PlanarSeparator.StDart D → ℤ
  | old d => u d
  | up _ => 0
  | down _ => 0

lemma triMap_embeds (hrot : M.RotTrans) : Embeds M (M.triMap hrot) old Sum.inl :=
  ⟨fun _ _ e => old.inj e, Sum.inl_injective, fun _ => rfl, fun _ => rfl⟩

lemma triCap_out (u : D → ℤ) (x : PlanarSeparator.StDart D) (hx : ∀ d, old d ≠ x) :
    triCap u x = 0 := by
  cases x with
  | old d => exact absurd rfl (hx d)
  | up _ => rfl
  | down _ => rfl

lemma triCap_nonneg {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) (x : PlanarSeparator.StDart D) :
    0 ≤ triCap u x := by
  cases x with
  | old d => exact hu d
  | up _ => exact le_rfl
  | down _ => exact le_rfl

/-- With no dart, every function is a maximum flow. -/
lemma isMax_of_isEmpty [IsEmpty D] (u : D → ℤ) (S T : Finset V) (f : D → ℤ) :
    IsMax M u S T f := by
  have hdiv : ∀ (g : D → ℤ) v, M.div g v = 0 := fun g v => by
    unfold CombMap.div; exact sum_eq_zero fun d _ => isEmptyElim d
  refine ⟨⟨⟨fun d => isEmptyElim d, fun d => isEmptyElim d⟩, fun v _ _ => hdiv f v⟩,
    fun g _ => ?_⟩
  simp [val, hdiv]

/-- **Maximum flow through the triangulated map**: on a plane map with transitive rotations and
faces, with nonnegative capacities and disjoint sources and sinks, the algorithm `algo` run on the
triangulated map (`PlanarFlow.CombMap.triMap`) with the spokes of capacity zero, restricted to the
darts of `M`, is a maximum flow of `M`. -/
theorem maxflow_tri (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {u : D → ℤ}
    (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) :
    IsMax M u S T (fun d =>
      algo (M.triMap hrot) (triCap u) (S.image Sum.inl) (T.image Sum.inl) (old d)) := by
  by_cases hD : Nonempty D
  · exact isMax_restrict (triMap_embeds hrot) (fun _ => rfl) (triCap_out u)
      (maxflow_plane (triMap_isPlane hM hrot hface) (triMap_rotTrans hrot)
        (triMap_faceTrans hrot) (triCap_nonneg hu)
        ((disjoint_image Sum.inl_injective).2 hST))
  · have : IsEmpty D := not_nonempty_iff.1 hD
    exact isMax_of_isEmpty u S T _

/-- **Maximum flow through the triangulated map, with the cost bound, for a decomposition of the
triangulated map meeting `BalDecA`**: on a plane map with `n ≥ 1` darts, transitive rotations
and faces, nonnegative capacities and disjoint sources and sinks, `runL` on the triangulated map
(of `3 n` darts) with the spokes of capacity zero, restricted to the darts of `M`, is a maximum
flow of `M`, and its cost is at most
`(s + 11)² ((27 Cₙ + 25) K (3 n) lg³ (3 n) + K₀ (3 n) lg (3 n))` with
`Cₙ = (η + 1) (25 + 7 κ² + 2 η (34 + 14 κ²))`. The decomposition is a hypothesis: it can be met
(`exists_balDecA_tri`); with `s` independent of `n` its existence on the triangulated map is not
proved here (on the preprocessed map it is: `PlanarFlow.BKMNW.maxflow_pre_cost`). -/
theorem maxflow_tri_cost (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) {κ η s : ℕ}
    {τ : ADec (M.triMap hrot)}
    (hτ : BalDecA (M.triMap hrot) (S.image Sum.inl) (T.image Sum.inl) κ η s τ)
    {O : PlaneOracles.{w}} (hO : O.Spec) {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    (hD : 0 < Fintype.card D) :
    IsMax M u S T (fun d =>
      runL (M.triMap hrot) (triCap u) τ O (S.image Sum.inl) (T.image Sum.inl) (old d)) ∧
      runLCost (M.triMap hrot) c τ ≤ (s + 11) ^ 2 * ((27 * ((η + 1) * (25 + 7 * κ ^ 2 +
        2 * η * (34 + 14 * κ ^ 2))) + 25) * K * (3 * Fintype.card D) *
          lg (3 * Fintype.card D) ^ 3 + K₀ * (3 * Fintype.card D) * lg (3 * Fintype.card D)) := by
  have : Nonempty D := Fintype.card_pos_iff.1 hD
  have hD' : 0 < Fintype.card (PlanarSeparator.StDart D) := by
    rw [card_triMap_darts]; omega
  obtain ⟨h1, h2⟩ := runL_isMax_costA (triMap_isPlane hM hrot hface) (triMap_rotTrans hrot)
    (triMap_faceTrans hrot) (triCap_nonneg hu) ((disjoint_image Sum.inl_injective).2 hST) hτ hO
    hc hD'
  rw [card_triMap_darts] at h2
  exact ⟨isMax_restrict (triMap_embeds hrot) (fun _ => rfl) (triCap_out u) h1, h2⟩

/-! ### The preprocessing of the article: triangulation and pendant terminals -/

variable {hrot : M.RotTrans}

variable (hrot) in
/-- The darts at which the pendant edges of the triangulated map are drawn: a dart of `M` at every
vertex of `M`, a spoke at every centre. -/
noncomputable def triE (e₀ : V → D) : V ⊕ (M.toSep hrot).Face → PlanarSeparator.StDart D
  | .inl v => old (e₀ v)
  | .inr x => down x.out

lemma triE_tail {e₀ : V → D} (he₀ : ∀ v, M.tail (e₀ v) = v) :
    ∀ w, (M.triMap hrot).tail (triE hrot e₀ w) = w
  | .inl v => by simp [triE, he₀]
  | .inr x => by
    simp only [triE, triMap_tail_down, Sum.inr.injEq]
    exact Quotient.out_eq x

variable (hrot) in
/-- **The preprocessed map** (line 1 and footnote 4 of the article): the triangulated map
`triMap`, with a pendant edge at every vertex. -/
noncomputable def preMap {e₀ : V → D} (he₀ : ∀ v, M.tail (e₀ v) = v) :
    CombMap (PlanarSeparator.StDart D ⊕ ((V ⊕ (M.toSep hrot).Face) × Bool))
      ((V ⊕ (M.toSep hrot).Face) ⊕ (V ⊕ (M.toSep hrot).Face)) (M.toSep hrot).stellar.Face :=
  (M.triMap hrot).pendant (triE hrot e₀) (triE_tail he₀)

/-- The capacities of the preprocessed map: those of `M` on its darts, zero on the spokes, the
total capacity in both directions on the pendant edges of the terminals, zero on the other pendant
edges. -/
noncomputable def preCap (u : D → ℤ) (S T : Finset V) :
    PlanarSeparator.StDart D ⊕ ((V ⊕ (M.toSep hrot).Face) × Bool) → ℤ :=
  pendCap (triCap u) (S.image Sum.inl) (T.image Sum.inl) (∑ x, triCap u x)

/-- The terminals of the preprocessed map: the pendant neighbours of the terminals of `M`. -/
noncomputable def preTerm (S : Finset V) :
    Finset ((V ⊕ (M.toSep hrot).Face) ⊕ (V ⊕ (M.toSep hrot).Face)) :=
  (S.image Sum.inl).image Sum.inr

/-- **Maximum flow through the preprocessing of the article**: on a plane map with transitive
rotations and faces, with nonnegative capacities and disjoint sources and sinks, the algorithm
`algo` run on the preprocessed map (`preMap`: the triangulation by spokes of capacity zero, and a
pendant edge at every vertex, the terminals replaced by their pendant neighbours), restricted to
the darts of `M`, is a maximum flow of `M`. The preprocessed map is plane with transitive
rotations and faces, its faces are triangles except those with a pendant edge
(`triMap_isTriangle`), its terminals have degree one (`pendant_tail_eq_inr`), and it has
`3 n + 2 (V + F) ≤ 7 n` darts (`card_preMap_darts`). -/
theorem maxflow_pre (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {u : D → ℤ}
    (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) {e₀ : V → D}
    (he₀ : ∀ v, M.tail (e₀ v) = v) :
    IsMax M u S T (fun d =>
      algo (preMap hrot he₀) (preCap u S T) (preTerm S) (preTerm T) (.inl (old d))) := by
  have : Nonempty D := ⟨e₀ hM.nonempty.some⟩
  have hP := triMap_isPlane hM hrot hface
  have h1 := maxflow_plane (CombMap.pendant_isPlane (triE_tail he₀) hP)
    (CombMap.pendant_rotTrans (triE_tail he₀) (triMap_rotTrans hrot))
    (CombMap.pendant_faceTrans (triE_tail he₀) (triMap_faceTrans hrot))
    (pendCap_nonneg (triCap_nonneg hu) _ _ (sum_nonneg fun x _ => triCap_nonneg hu x))
    ((disjoint_image Sum.inr_injective).2 ((disjoint_image Sum.inl_injective).2 hST))
    (u := preCap u S T) (S := preTerm S) (T := preTerm T)
  exact isMax_restrict (triMap_embeds hrot) (fun _ => rfl) (triCap_out u)
    (isMax_pendant (triE_tail he₀) (triCap_nonneg hu) h1)

/-- **The size of the preprocessed map**: `3 n + 2 (V + F)` darts for a map with `n` darts, `V`
vertices and `F` faces, at most `7 n` when every vertex has a dart. -/
theorem card_preMap_darts [Nonempty D] (hM : M.IsPlane) (hface : M.FaceTrans) {e₀ : V → D}
    (he₀ : ∀ v, M.tail (e₀ v) = v) :
    Fintype.card (PlanarSeparator.StDart D ⊕ ((V ⊕ (M.toSep hrot).Face) × Bool)) =
      3 * Fintype.card D + 2 * (Fintype.card V + Fintype.card F) ∧
    Fintype.card (PlanarSeparator.StDart D ⊕ ((V ⊕ (M.toSep hrot).Face) × Bool)) ≤
      7 * Fintype.card D := by
  have hF := card_toSep_face hM hrot hface
  have hV : Fintype.card V ≤ Fintype.card D :=
    Fintype.card_le_of_surjective M.tail fun v => ⟨e₀ v, he₀ v⟩
  have hF' : Fintype.card (M.toSep hrot).Face ≤ Fintype.card D :=
    Fintype.card_le_of_surjective _ (M.toSep hrot).face_surjective
  have e : Fintype.card (PlanarSeparator.StDart D ⊕ ((V ⊕ (M.toSep hrot).Face) × Bool)) =
      3 * Fintype.card D + 2 * (Fintype.card V + Fintype.card (M.toSep hrot).Face) := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_sum, Fintype.card_bool,
      card_triMap_darts]
    ring
  refine ⟨by rw [e, hF], by rw [e]; omega⟩

/-! ### Decompositions of the triangulated map -/

variable (hrot)

/-- The spokes at the centre of the face `x`. -/
def IsSpoke (x : (M.toSep hrot).Face) : PlanarSeparator.StDart D → Prop
  | old _ => False
  | up d => (M.toSep hrot).face d = x
  | down d => (M.toSep hrot).face d = x

/-- The darts of `M` among those of the triangulated map. -/
def IsOld : PlanarSeparator.StDart D → Prop
  | old _ => True
  | up _ => False
  | down _ => False

instance : DecidablePred (IsOld (D := D)) := fun y => by
  cases y <;> simp only [IsOld] <;> infer_instance

open Classical in
/-- The star of the centre of the face `x`: its spokes. -/
noncomputable def triStar (x : (M.toSep hrot).Face) : Finset (PlanarSeparator.StDart D) :=
  univ.filter (IsSpoke hrot x)

open Classical in
/-- The darts of the map, with the stars of the centres of the faces of the list `L`. -/
noncomputable def triPiece (L : List (M.toSep hrot).Face) : Finset (PlanarSeparator.StDart D) :=
  univ.filter IsOld ∪ L.toFinset.biUnion (triStar hrot)

/-- The centres of the faces of `R`, one hole each. -/
def triHoles (R : List (M.toSep hrot).Face) : List (Finset (V ⊕ (M.toSep hrot).Face)) :=
  R.map fun y => {Sum.inr y}

/-- **A chain decomposition of the triangulated map**: the centres of the faces of `L` one at a
time, each a separator of one vertex, whose star is the right child. -/
noncomputable def triChain (x₀ : PlanarSeparator.StDart D) :
    List (M.toSep hrot).Face → ADec (M.triMap hrot)
  | [] => .leaf (univ.filter IsOld)
  | x :: L => .node (triChain x₀ L) (.leaf (triStar hrot x)) (SPath.point x₀ (Sum.inr x)).toSep

variable {hrot}

lemma mem_triStar {x : (M.toSep hrot).Face} {y : PlanarSeparator.StDart D} :
    y ∈ triStar hrot x ↔ IsSpoke hrot x y := by
  classical simp [triStar]

lemma mem_triPiece {L : List (M.toSep hrot).Face} {y : PlanarSeparator.StDart D} :
    y ∈ triPiece hrot L ↔ IsOld y ∨ ∃ x ∈ L, IsSpoke hrot x y := by
  classical simp [triPiece, mem_triStar]

lemma triHoles_append (R : List (M.toSep hrot).Face) (x : (M.toSep hrot).Face) :
    triHoles hrot (R ++ [x]) = triHoles hrot R ++ [{Sum.inr x}] := by
  simp [triHoles]

lemma mem_hunion_triHoles {R : List (M.toSep hrot).Face} {w : V ⊕ (M.toSep hrot).Face} :
    w ∈ hunion (triHoles hrot R) ↔ ∃ y ∈ R, w = Sum.inr y := by
  rw [mem_hunion]
  simp [triHoles]

lemma triMap_head_old (d : D) : (M.triMap hrot).head (old d) = .inl (M.head d) := rfl
lemma triMap_head_up (d : D) :
    (M.triMap hrot).head (up d) = .inr ((M.toSep hrot).face d) := rfl
lemma triMap_head_down (d : D) : (M.triMap hrot).head (down d) = .inl (M.tail d) := rfl

/-- No dart of the triangulated map lies inside a hole at a centre. -/
lemma pdarts_tri (P : Finset (PlanarSeparator.StDart D)) (R : List (M.toSep hrot).Face) :
    pdarts (M.triMap hrot) P (triHoles hrot R) = P := by
  ext y
  rw [mem_pdarts]
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  rintro ⟨H, hH, h1, h2⟩
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 hH
  cases y with
  | old d => simp at h1
  | up d => simp at h1
  | down d => rw [triMap_head_down] at h2; simp at h2

/-- **The darts of the map with any stars are connected**, the centres not contracted. -/
theorem hConn_triPiece (hM : M.IsPlane) (L R : List (M.toSep hrot).Face) :
    HConn (M.triMap hrot) (triPiece hrot L) (triHoles hrot R) := by
  rw [HConn, pdarts_tri]
  set P := triPiece hrot L
  set Rel := fun a b => b ∈ P ∧ (b = (M.triMap hrot).rev a ∨
    HRel (triHoles hrot R) ((M.triMap hrot).tail a) ((M.triMap hrot).tail b))
  have hold : ∀ d, old d ∈ P := fun d => mem_triPiece.2 (Or.inl trivial)
  have hsame : ∀ {a b}, b ∈ P → (M.triMap hrot).tail a = (M.triMap hrot).tail b → Rel a b :=
    fun hb e => ⟨hb, Or.inr (Or.inl e)⟩
  have hrev : ∀ {a}, (M.triMap hrot).rev a ∈ P → Rel a ((M.triMap hrot).rev a) :=
    fun hb => ⟨hb, Or.inl rfl⟩
  have holds : ∀ d e, Relation.ReflTransGen Rel (old d) (old e) := by
    intro d e
    have key : ∀ b, Relation.ReflTransGen M.Adj (M.tail d) b → ∀ e, M.tail e = b →
        Relation.ReflTransGen Rel (old d) (old e) := by
      intro b hb
      induction hb with
      | refl => exact fun e he => .single (hsame (hold e) (by simp [he]))
      | tail _ hbc ih =>
        obtain ⟨x, hx1, hx2⟩ := hbc
        intro e he
        exact ((ih x hx1).tail (hrev (hold _))).tail (hsame (hold e) (by simp [he, hx2]))
    exact key _ (hM.conn _ _) e rfl
  -- every dart of the piece reaches a dart of `M`, and back
  have hspoke : ∀ {y}, y ∈ P → ∃ d, Relation.ReflTransGen Rel y (old d) ∧
      Relation.ReflTransGen Rel (old d) y := by
    intro y hy
    cases y with
    | old d => exact ⟨d, .refl, .refl⟩
    | up d =>
      exact ⟨d, .single (hsame (hold d) rfl), .single (hsame hy rfl)⟩
    | down d =>
      have hup : up d ∈ P := by
        obtain h | ⟨x, hx, h⟩ := mem_triPiece.1 hy
        · exact absurd h id
        · exact mem_triPiece.2 (Or.inr ⟨x, hx, h⟩)
      exact ⟨d, (Relation.ReflTransGen.single (hrev (a := down d) hup)).tail
          (hsame (hold d) rfl),
        (Relation.ReflTransGen.single (hsame (a := old d) hup rfl)).tail
          (hrev (a := up d) hy)⟩
  intro x hx y hy
  obtain ⟨dx, h1, -⟩ := hspoke hx
  obtain ⟨dy, -, h2⟩ := hspoke hy
  exact (h1.trans (holds dx dy)).trans h2

/-- **The star of a centre is connected.** -/
theorem hConn_triStar (x : (M.toSep hrot).Face) (R : List (M.toSep hrot).Face) :
    HConn (M.triMap hrot) (triStar hrot x) (triHoles hrot R) := by
  rw [HConn, pdarts_tri]
  set P := triStar hrot x
  set Rel := fun a b => b ∈ P ∧ (b = (M.triMap hrot).rev a ∨
    HRel (triHoles hrot R) ((M.triMap hrot).tail a) ((M.triMap hrot).tail b))
  have hdown : ∀ {y}, y ∈ P → ∃ d, (M.toSep hrot).face d = x ∧ down d ∈ P ∧
      Relation.ReflTransGen Rel y (down d) ∧ Relation.ReflTransGen Rel (down d) y := by
    intro y hy
    have hy' := mem_triStar.1 hy
    cases y with
    | old d => exact absurd hy' id
    | up d =>
      have hd : down d ∈ P := mem_triStar.2 hy'
      exact ⟨d, hy', hd, .single ⟨hd, Or.inl rfl⟩, .single ⟨hy, Or.inl rfl⟩⟩
    | down d => exact ⟨d, hy', hy, .refl, .refl⟩
  intro a ha b hb
  obtain ⟨da, ea, -, h1, -⟩ := hdown ha
  obtain ⟨db, eb, hdb, -, h2⟩ := hdown hb
  exact (h1.tail ⟨hdb, Or.inr (Or.inl (by simp [ea, eb]))⟩).trans h2

lemma triPiece_cons (x : (M.toSep hrot).Face) (L : List (M.toSep hrot).Face) :
    triPiece hrot (x :: L) = triPiece hrot L ∪ triStar hrot x := by
  ext y
  simp only [mem_union, mem_triPiece, mem_triStar, List.mem_cons]
  constructor
  · rintro (h | ⟨z, rfl | hz, h⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr ⟨z, hz, h⟩)
  · rintro ((h | ⟨z, hz, h⟩) | h)
    · exact Or.inl h
    · exact Or.inr ⟨z, Or.inr hz, h⟩
    · exact Or.inr ⟨x, Or.inl rfl, h⟩

lemma triChain_piece (x₀ : PlanarSeparator.StDart D) :
    ∀ L : List (M.toSep hrot).Face, (triChain hrot x₀ L).piece = triPiece hrot L
  | [] => by classical ext y; simp [triChain, ADec.piece, triPiece]
  | x :: L => by
    simp only [triChain, ADec.piece, triChain_piece x₀ L, triPiece_cons]

lemma triPiece_univ : triPiece hrot (univ : Finset (M.toSep hrot).Face).toList = univ := by
  ext y
  simp only [mem_univ, iff_true, mem_triPiece, mem_toList, true_and]
  cases y with
  | old d => exact Or.inl trivial
  | up d => exact Or.inr ⟨_, rfl⟩
  | down d => exact Or.inr ⟨_, rfl⟩

/-- **The chain decomposition of the triangulated map meets the hypotheses of correctness and
`ADec.BalA`** (with every split balanced in size, the pieces having at most `3 n` darts), when
every vertex of `M` is a terminal: the vertices shared by a star and the rest are terminals or
its centre, and no piece touches a hole (the star of a centre leaves with it). -/
theorem triChain_spec [Nonempty D] (hM : M.IsPlane) {S T : Finset V} (hcov : ∀ v, v ∈ S ∪ T)
    (κ η : ℕ) (x₀ : PlanarSeparator.StDart D) :
    ∀ (L R : List (M.toSep hrot).Face), L.Nodup → (∀ x ∈ L, x ∉ R) →
      (triChain hrot x₀ L).piece = triPiece hrot L ∧
      (triChain hrot x₀ L).Good (M.triMap hrot) (S.image Sum.inl) (T.image Sum.inl)
        (triHoles hrot R) ∧
      (triChain hrot x₀ L).PGood (M.triMap hrot) (triHoles hrot R) ∧
      (triChain hrot x₀ L).LeafOK (M.triMap hrot) (S.image Sum.inl) (T.image Sum.inl)
        (triHoles hrot R) ∧
      (triChain hrot x₀ L).BalA (M.triMap hrot) κ η (3 * Fintype.card D) true (triHoles hrot R)
  | [], R, _, _ => by
    have e : univ.filter IsOld = triPiece hrot ([] : List (M.toSep hrot).Face) := by
      classical ext y; simp [triPiece]
    refine ⟨triChain_piece x₀ [], fun y hy => ?_, ?_, Or.inr fun y hy => ?_, trivial⟩
    · cases y <;> simp [IsOld] at hy ⊢
    · show HConn _ (univ.filter IsOld) _
      rw [e]; exact hConn_triPiece hM [] R
    · rw [pdarts_tri] at hy
      cases y with
      | old d =>
        rcases mem_union.1 (hcov (M.tail d)) with h | h
        · exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ h))
        · exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ h))
      | up d => simp [IsOld] at hy
      | down d => simp [IsOld] at hy
  | x :: L, R, hnd, hLR => by
    obtain ⟨hxL, hnd'⟩ := List.nodup_cons.1 hnd
    have hxR : x ∉ R := hLR x (List.mem_cons_self ..)
    obtain ⟨p, g, pg, lo, ba⟩ := triChain_spec hM hcov κ η x₀ L (R ++ [x]) hnd' fun y hy => by
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hLR y (List.mem_cons_of_mem _ hy), fun e => hxL (e ▸ hy)⟩
    rw [triHoles_append] at g pg lo ba
    have hv : (SPath.point (M' := M.triMap hrot) x₀ (Sum.inr x)).verts = {Sum.inr x} :=
      SPath.point_verts _ _
    rw [← hv] at g pg lo ba
    -- the star and the rest
    have hdisj : Disjoint (triPiece hrot L) (triStar hrot x) := by
      refine disjoint_left.2 fun y h1 h2 => ?_
      have h2' := mem_triStar.1 h2
      rcases mem_triPiece.1 h1 with h | ⟨z, hz, h⟩
      · cases y <;> simp_all [IsOld, IsSpoke]
      · cases y with
        | old d => exact h
        | up d => exact hxL (by simp only [IsSpoke] at h h2'; rwa [← h, h2'] at hz)
        | down d => exact hxL (by simp only [IsSpoke] at h h2'; rwa [← h, h2'] at hz)
    obtain ⟨d₀⟩ := ‹Nonempty D›
    have hl0 : 0 < (triPiece hrot L).card :=
      card_pos.2 ⟨old d₀, mem_triPiece.2 (Or.inl trivial)⟩
    obtain ⟨dx, hdx⟩ := (M.toSep hrot).face_surjective x
    have hdown : down dx ∈ triStar hrot x := mem_triStar.2 hdx
    have hr0 : 0 < (triStar hrot x).card := card_pos.2 ⟨_, hdown⟩
    have hrev : RevClosed (M.triMap hrot) (triStar hrot x) := fun y hy => by
      have := mem_triStar.1 hy
      cases y <;> simp [IsSpoke] at this ⊢ <;> exact mem_triStar.2 this
    -- the vertices of the star are terminals or its centre
    have hbd : bd (M.triMap hrot) (triPiece hrot L) (triStar hrot x) ⊆
        S.image Sum.inl ∪ T.image Sum.inl ∪
          (hunion (triHoles hrot R) ∪
            (SPath.point (M' := M.triMap hrot) x₀ (Sum.inr x)).verts) := by
      intro w hw
      obtain ⟨-, y, hy, rfl⟩ := mem_bd.1 hw
      have hy' := mem_triStar.1 hy
      cases y with
      | old d => exact absurd hy' id
      | up d =>
        simp only [triMap_tail_up]
        rcases mem_union.1 (hcov (M.tail d)) with h | h
        · exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ h))
        · exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ h))
      | down d =>
        simp only [IsSpoke] at hy'
        rw [hv, triMap_tail_down, hy']
        exact mem_union_right _ (mem_union_right _ (mem_singleton_self _))
    have havoid : Disjoint (SPath.point (M' := M.triMap hrot) x₀ (Sum.inr x)).verts
        (S.image Sum.inl ∪ T.image Sum.inl ∪ hunion (triHoles hrot R)) := by
      rw [hv, disjoint_singleton_left]
      simp only [mem_union, mem_image, mem_hunion_triHoles, not_or]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rintro ⟨_, -, h⟩; exact Sum.inl_ne_inr h
      · rintro ⟨_, -, h⟩; exact Sum.inl_ne_inr h
      · rintro ⟨y, hy, e⟩; exact hxR (Sum.inr_injective e ▸ hy)
    have hm : (SPath.point (M' := M.triMap hrot) x₀ (Sum.inr x)).toSep.path.mverts =
        (SPath.point (M' := M.triMap hrot) x₀ (Sum.inr x)).verts := SPath.toH_mverts _
    have hvd : Disjoint (SPath.point (M' := M.triMap hrot) x₀ (Sum.inr x)).verts
        (hunion (triHoles hrot R)) := disjoint_of_subset_right subset_union_right havoid
    have ech : childHoles (triHoles hrot R)
        (SPath.point (M' := M.triMap hrot) x₀ (Sum.inr x)).toSep.path.mverts =
          triHoles hrot R ++ [(SPath.point (M' := M.triMap hrot) x₀ (Sum.inr x)).verts] := by
      rw [hm]; exact childHoles_of_disjoint hvd
    rw [← ech] at g pg lo ba
    -- no hole is touched
    have hη : nTouch (M.triMap hrot) (triPiece hrot L ∪ triStar hrot x) (triHoles hrot R) = 0 := by
      classical
      unfold nTouch
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro H hH
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hH
      simp only [mem_singleton, exists_eq_left, decide_eq_true_eq, Touch]
      rintro ⟨y, hy, he⟩
      rw [← triPiece_cons] at hy
      rcases mem_triPiece.1 hy with h | ⟨w, hw, h⟩
      · cases y <;> simp_all [IsOld]
      · cases y with
        | old d => exact h
        | up d => simp at he
        | down d =>
          simp only [IsSpoke, triMap_tail_down, Sum.inr.injEq] at h he
          exact hLR w hw (by rw [← h, he]; exact hz)
    have hcard : (triPiece hrot L ∪ triStar hrot x).card ≤ 3 * Fintype.card D :=
      (card_le_univ _).trans (card_triMap_darts (D := D)).le
    refine ⟨by simp only [triChain, ADec.piece, triChain_piece x₀ L, triPiece_cons], ?_, ?_, ?_, ?_⟩
    · simp only [triChain, ADec.Good, ADec.piece, triChain_piece x₀ L]
      refine ⟨g, hrev, hdisj, by rw [hm]; exact hbd, ?_, SPath.toSep_segOK _ hvd⟩
      rw [hm]; exact disjoint_of_subset_right subset_union_left havoid
    · simp only [triChain, ADec.PGood, ADec.piece, triChain_piece x₀ L]
      refine ⟨?_, SPath.toH_simple _ hvd,
        fun e he => by simp [SPath.toSep, SPath.toH_darts, ADec.point_darts] at he, pg, ?_,
        fun σ hσ => ?_⟩
      · rw [← triPiece_cons]; exact hConn_triPiece hM _ R
      · rw [ech, hv, ← triHoles_append]; exact hConn_triStar x _
      · rw [show σ = SPath.point x₀ (Sum.inr x) by simpa [SPath.toSep] using hσ]
        exact ⟨fun e he => by simp [ADec.point_darts] at he, down dx, mem_union_right _ hdown,
          by simp [SPath.point, triMap_tail_down, hdx]⟩
    · simp only [triChain, ADec.LeafOK]
      refine ⟨lo, Or.inr fun y hy => ?_⟩
      rw [ech, hv, ← triHoles_append, pdarts_tri] at hy
      have hy' := mem_triStar.1 hy
      cases y with
      | old d => exact absurd hy' id
      | up d =>
        simp only [triMap_tail_up]
        rcases mem_union.1 (hcov (M.tail d)) with h | h
        · exact mem_union_left _ (mem_union_left _ (mem_image_of_mem _ h))
        · exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ h))
      | down d =>
        simp only [IsSpoke] at hy'
        rw [triMap_tail_down, hy', ech, hunion_append, hv]
        exact mem_union_right _ (mem_union_right _ (mem_singleton_self _))
    · simp only [triChain, ADec.BalA, ADec.piece, triChain_piece x₀ L]
      refine ⟨hdisj, hl0, hr0, ⟨by simp [SPath.toSep], fun σ hσ => ?_⟩, by omega,
        Or.inl ⟨Or.inl hcard, ba, trivial⟩⟩
      rw [show σ = SPath.point x₀ (Sum.inr x) by simpa [SPath.toSep] using hσ]
      simp [SPath.point]

/-- **Decompositions meeting `BalDecA` exist on the triangulated map** of every plane map with
transitive rotations and a dart, for all `κ`, `η`, when every vertex of `M` is a terminal (with
`s = 3 n`, so that the bound of `maxflow_tri_cost` is then `O(n² log³ n)`). This shows that the
hypotheses of `maxflow_tri_cost` can be met; for maps with vertices that are not terminals, the
existence of decompositions meeting `BalDecA` with `s` independent of `n` is proved on the
preprocessed map (`PlanarFlow.BKMNW.exists_balDecA_pre`), not on the triangulated map. -/
theorem exists_balDecA_tri [Nonempty D] (hM : M.IsPlane) {S T : Finset V}
    (hcov : ∀ v, v ∈ S ∪ T) (κ η : ℕ) :
    ∃ τ : ADec (M.triMap hrot), BalDecA (M.triMap hrot) (S.image Sum.inl) (T.image Sum.inl) κ η
      (3 * Fintype.card D) τ := by
  obtain ⟨d₀⟩ := ‹Nonempty D›
  obtain ⟨p, g, pg, lo, ba⟩ := triChain_spec (hrot := hrot) hM hcov κ η (old d₀)
    (univ : Finset (M.toSep hrot).Face).toList [] (nodup_toList _) (by simp)
  exact ⟨_, by rw [p, triPiece_univ], g, pg, lo, ba⟩

end Tri

end BKMNW

end PlanarFlow
