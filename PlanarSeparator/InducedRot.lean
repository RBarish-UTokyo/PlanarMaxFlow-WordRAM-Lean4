module

public import PlanarFlow.NegSSSP.SimpleRot
public import PlanarFlow.BKMNW.CutBuild

/-!
# The induced rotation system: first return to a vertex set

Let `R` be a rotation system of a graph `G` on `V`, and let `e : V' ↪ V` embed a vertex set.
The graph induced on the range of `e`, pulled back to `V'`, is `G.comap e`; its darts are the
darts of `G` with both ends in the range (`inDarts`). Its **induced rotation** (`indRot`) sends
a dart to the first dart after it in the rotation of `R` around its tail that again has its head
in the range (the first return `PlanarFlow.Orbit.ret` of the rotation to `inDarts`).

* **`PlanarSeparator.InducedRot.indRot_isPlane`**: if `R` is plane, `G.comap e` is connected
  and `V'` has at least two vertices, the induced rotation system is plane. Euler's formula
  holds because deleting edges keeps the Euler gap zero (`PlanarFlow.Orbit.gap_ret_eq_zero`), as
  for the simple graph of a plane map (`PlanarFlow.NegSSSP.srot_isPlane`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace InducedRot

open Finset Function Equiv PlanarFlow PlanarFlow.Orbit PlanarFlow.CombMap PlanarFlow.NegSSSP
  Relation

variable {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V'] [DecidableEq V']
  {G : SimpleGraph V} [DecidableRel G.Adj] (R : Kasteleyn.RotationSystem G) (e : V' ↪ V)

instance instDecAdjComap : DecidableRel (G.comap e).Adj :=
  fun a b => inferInstanceAs (Decidable (G.Adj (e a) (e b)))

variable (G) in
/-- The darts of `G` with both ends in the range of `e`. -/
def inDarts : Finset G.Dart := univ.filter fun d => d.fst ∈ univ.map e ∧ d.snd ∈ univ.map e

variable {e} in
lemma mem_inDarts {d : G.Dart} : d ∈ inDarts G e ↔ d.fst ∈ univ.map e ∧ d.snd ∈ univ.map e := by
  simp [inDarts]

variable (G) in
/-- A dart of the pulled back graph as a dart of `G`. -/
def lift (x : (G.comap e).Dart) : G.Dart := ⟨(e x.fst, e x.snd), x.adj⟩

variable (G) in
lemma lift_mem (x : (G.comap e).Dart) : lift G e x ∈ inDarts G e :=
  mem_inDarts.2 ⟨mem_map_of_mem _ (mem_univ _), mem_map_of_mem _ (mem_univ _)⟩

variable (G) in
/-- The darts of the pulled back graph are the darts of `G` with both ends in the range. -/
noncomputable def iDartE : (G.comap e).Dart ≃ {d // d ∈ inDarts G e} :=
  Equiv.ofBijective (fun x => ⟨lift G e x, lift_mem G e x⟩) (by
    constructor
    · intro x y h
      have h1 := congrArg (fun d : {d // d ∈ inDarts G e} => d.1.fst) h
      have h2 := congrArg (fun d : {d // d ∈ inDarts G e} => d.1.snd) h
      simp only [lift] at h1 h2
      exact (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext (e.injective h1) (e.injective h2))
    · intro ⟨d, hd⟩
      obtain ⟨a, -, ha⟩ := mem_map.1 (mem_inDarts.1 hd).1
      obtain ⟨b, -, hb⟩ := mem_map.1 (mem_inDarts.1 hd).2
      have hab : (G.comap e).Adj a b := by
        show G.Adj (e a) (e b); rw [ha, hb]; exact d.adj
      refine ⟨⟨(a, b), hab⟩, Subtype.ext ?_⟩
      exact (SimpleGraph.Dart.ext_iff _ _).2 (Prod.ext ha hb))

variable (G) in
lemma iDartE_val (x : (G.comap e).Dart) : (iDartE G e x).1 = lift G e x := rfl

variable (G) in
lemma e_fst_symm (y : {d // d ∈ inDarts G e}) : e ((iDartE G e).symm y).fst = y.1.fst := by
  conv_rhs => rw [← (iDartE G e).apply_symm_apply y]
  rfl

local notation "NR" => CombMap.ofRotation R

lemma tail_eq (d : G.Dart) : (NR).tail d = d.fst := rfl

variable (G) in
lemma rev_mem {d : G.Dart} (hd : d ∈ inDarts G e) : d.symm ∈ inDarts G e := by
  rw [mem_inDarts] at hd ⊢; exact ⟨hd.2, hd.1⟩

/-- The first return of the rotation to `inDarts G e`, on `inDarts G e`. -/
noncomputable def iRotB : Perm {d // d ∈ inDarts G e} :=
  (ret (rotPerm NR) (inDarts G e)).subtypePerm fun _ => ret_mem_iff

/-- The reversal on `inDarts G e`. -/
noncomputable def iRevB : Perm {d // d ∈ inDarts G e} :=
  (revPerm NR).subtypePerm fun d => ⟨fun h => by
    have := rev_mem G e h; exact this, fun h => rev_mem G e h⟩

/-- **The induced rotation system** on `G.comap e`: the first return of the rotation of `R` to
the darts with both ends in the range of `e`. -/
noncomputable def indRot : Kasteleyn.RotationSystem (G.comap e) where
  rot := (iDartE G e).symm.permCongr (iRotB R e)
  fst_rot x := by
    apply e.injective
    rw [Equiv.permCongr_apply, Equiv.symm_symm, e_fst_symm G]
    show (NR).tail (ret (rotPerm NR) (inDarts G e) (iDartE G e x).1) = e x.fst
    rw [tail_ret]; rfl
  sameCycle_of_fst_eq x y h := by
    rw [← (iDartE G e).symm_apply_apply x, ← (iDartE G e).symm_apply_apply y, sameCycle_permCongr,
      iRotB, Perm.sameCycle_subtypePerm,
      sameCycle_ret_iff (MSSP.ofRotation_rotTrans R) (iDartE G e x).2 (iDartE G e y).2]
    show e x.fst = e y.fst
    rw [h]

/-! ### Planarity -/

lemma conn_inDarts (hc : (G.comap e).Connected) :
    ∀ x ∈ inDarts G e, ∀ y ∈ inDarts G e, Conn (revPerm NR) (ret (rotPerm NR) (inDarts G e)) x y := by
  have hrot := MSSP.ofRotation_rotTrans R
  have key : ∀ a b, ReflTransGen (G.comap e).Adj a b → ∀ x ∈ inDarts G e, ∀ y ∈ inDarts G e,
      x.fst = e a → y.fst = e b → Conn (revPerm NR) (ret (rotPerm NR) (inDarts G e)) x y := by
    intro a b h
    induction h with
    | refl =>
      intro x hx y hy h1 h2
      exact conn_of_sameCycle ((sameCycle_ret_iff hrot hx hy).2 (h1.trans h2.symm))
    | tail _ hst ih =>
      rename_i b c _
      intro x hx y hy hx' hy'
      have hd := lift_mem G e ⟨(b, c), hst⟩
      refine (ih x hx _ hd hx' rfl).trans ((conn_inv (ι := revPerm NR) _).trans ?_)
      exact conn_of_sameCycle ((sameCycle_ret_iff hrot (rev_mem G e hd) hy).2
        (by rw [tail_eq, tail_eq, hy']; rfl))
  intro x hx y hy
  obtain ⟨a, -, ha⟩ := mem_map.1 (mem_inDarts.1 hx).1
  obtain ⟨b, -, hb⟩ := mem_map.1 (mem_inDarts.1 hy).1
  exact key a b ((SimpleGraph.reachable_iff_reflTransGen a b).1 (hc.preconnected a b)) x hx y hy
    ha.symm hb.symm

lemma exists_dart (hc : (G.comap e).Connected) (h2 : 1 < Fintype.card V') (a : V') :
    ∃ x : (G.comap e).Dart, x.fst = a := by
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card h2 a
  rcases ((SimpleGraph.reachable_iff_reflTransGen a b).1 (hc.preconnected a b)).cases_head
    with h | ⟨z, hz, -⟩
  · exact absurd h.symm hb
  · exact ⟨⟨(a, z), hz⟩, rfl⟩

lemma card_vert (hc : (G.comap e).Connected) (h2 : 1 < Fintype.card V') :
    nOrb (ret (rotPerm NR) (inDarts G e)) (inDarts G e) = Fintype.card V' := by
  have hrot := MSSP.ofRotation_rotTrans R
  have h1 : nOrb (ret (rotPerm NR) (inDarts G e)) (inDarts G e) =
      ((inDarts G e).image (fun d : G.Dart => d.fst)).card :=
    le_antisymm
      (card_image_le_of_fiber fun x hx y hy h =>
        (cls_eq_iff).2 ((sameCycle_ret_iff hrot hx hy).2 h))
      (card_image_le_of_fiber fun x hx y hy h =>
        (sameCycle_ret_iff hrot hx hy).1 ((cls_eq_iff).1 h))
  rw [h1, ← card_univ, ← card_map e]
  congr 1
  ext v
  constructor
  · intro hv
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hv
    exact (mem_inDarts.1 hd).1
  · intro hv
    obtain ⟨a, -, rfl⟩ := mem_map.1 hv
    obtain ⟨x, hx⟩ := exists_dart e hc h2 a
    exact mem_image.2 ⟨lift G e x, lift_mem G e x, by rw [← hx]; rfl⟩

lemma faceNext_eq :
    (indRot R e).faceNext = (iDartE G e).symm.permCongr (iRotB R e * iRevB R e) := by
  refine Equiv.ext fun x => ?_
  have h : iDartE G e ((Kasteleyn.dartRev _) x) = iRevB R e (iDartE G e x) := by
    apply Subtype.ext
    rfl
  simp only [Kasteleyn.RotationSystem.faceNext, Equiv.trans_apply, indRot, Equiv.permCongr_apply,
    Perm.mul_apply, Equiv.symm_symm, h]

lemma card_face :
    Fintype.card (indRot R e).Face =
      nOrb (ret (rotPerm NR) (inDarts G e) * revPerm NR) (inDarts G e) := by
  have hs : (iRotB R e * iRevB R e) = (ret (rotPerm NR) (inDarts G e) * revPerm NR).subtypePerm
      (fun x => ⟨fun h => by
        have := rev_mem G e (ret_mem_iff.1 h); exact this,
        fun h => ret_mem_iff.2 (rev_mem G e h)⟩) := by
    refine Equiv.ext fun x => ?_; rfl
  have key := card_image_eq_of_iff (D := (G.comap e).Dart)
    (f := fun x => cls (ret (rotPerm NR) (inDarts G e) * revPerm NR) (iDartE G e x).1)
    (g := (indRot R e).face) (fun x y => by
      rw [cls_eq_iff]
      change _ ↔ Quotient.mk _ x = Quotient.mk _ y
      rw [Quotient.eq]
      change _ ↔ (indRot R e).faceNext.SameCycle x y
      rw [faceNext_eq, ← (iDartE G e).symm_apply_apply x, ← (iDartE G e).symm_apply_apply y,
        sameCycle_permCongr, hs, Perm.sameCycle_subtypePerm, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply])
    (fun f => Quotient.inductionOn f fun x => ⟨x, rfl⟩)
  rw [← key, nOrb]
  congr 1
  ext c
  simp only [mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨_, (iDartE G e x).2, rfl⟩
  · rintro ⟨d, hd, rfl⟩; exact ⟨(iDartE G e).symm ⟨d, hd⟩, by rw [Equiv.apply_symm_apply]⟩

/-- **The induced rotation system is plane**: for a plane rotation system `R` of `G`, a
connected induced subgraph `G.comap e` with at least two vertices. -/
theorem indRot_isPlane (hR : R.IsPlane) (hc : (G.comap e).Connected)
    (h2 : 1 < Fintype.card V') : (indRot R e).IsPlane where
  connected := hc
  euler := by
    have : Nonempty V' := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨x₀, -⟩ := exists_dart e hc h2 (Classical.arbitrary V')
    have hc1 := comp_eq_one (revPerm_isInv NR) (lift_mem G e x₀) (conn_inDarts R e hc)
    have hg := gap_ret_eq_zero (revPerm_isInv NR) (fun _ _ => mem_univ _)
      (fun _ _ => mem_univ _) (subset_univ (inDarts G e)) (fun x hx => rev_mem G e hx)
      (gap_rot_eq_zero (CombMap.ofRotation_isPlane hR) (MSSP.ofRotation_rotTrans R)
        (BKMNW.ofRotation_faceTrans R) ⟨lift G e x₀⟩).2
    have hV := card_vert R e hc h2
    have hF := card_face R e
    have hE := SimpleGraph.dart_card_eq_twice_card_edges (G := G.comap e)
    rw [Fintype.card_congr (iDartE G e), Fintype.card_coe] at hE
    unfold gap eul at hg
    rw [hc1, hV, ← hF] at hg
    omega

end InducedRot

end PlanarSeparator
