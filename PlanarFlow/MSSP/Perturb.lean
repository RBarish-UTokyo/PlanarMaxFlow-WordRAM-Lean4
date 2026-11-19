module

public import PlanarFlow.MSSP.Bridge
public import Mathlib.Combinatorics.Colex
public import PlanarFlow.Plane.Rotation

/-!
# Unique shortest paths by perturbation

The article of Das, Kipouridis, Probst Gutenberg and Wulff-Nilsen (SOSA 2022) assumes unique
shortest paths. For nonnegative integer lengths this is obtained by a perturbation: give the arcs
distinct indices `ι a < c` and replace the length `len a` by `2^c · len a + 2^(ι a)`
(`IsPerturb`). The perturbed lengths are positive, and

* `IsPerturb.dist_div`: distances are preserved after division by `2^c`: the perturbed distance
  is `2^c · dist + s` with `0 ≤ s < 2^c` (a shortest walk without repeated arcs has a perturbation
  of at most `∑_{i < c} 2^i < 2^c`);
* `IsPerturb.uniqTight`: tight arcs are unique: two shortest walks of the same perturbed length
  use the same set of arcs (binary expansions are unique), and a shortest walk enters every
  vertex once.

For plane maps (`HypNN`, the article's setting with nonnegative lengths), the perturbed lengths
`pert ℓ` meet `PlanarFlow.MSSP.Hyp` (`HypNN.hyp`), and the data structure run on them gives the
distances for `ℓ` after division (`dkpw_pert`, `dkpwNN_msspOut`). The maps of rotation systems
have transitive rotations (`ofRotation_rotTrans`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace MSSP

open Finset

section Generic

variable {X A : Type*}

lemma lwalk_of_eq {G G' : Digraph X A} (hs : G'.src = G.src) (hd : G'.dst = G.dst) {x y : X}
    {l : List A} (h : LWalk G x y l) : LWalk G' x y l := by
  induction h with
  | nil => exact .nil _
  | @cons a y l _ ih =>
    have := LWalk.cons (G := G') (a := a) (by rw [congrFun hd a]; exact ih)
    rwa [congrFun hs a] at this

/-- **A walk has a sub-walk with the same ends and no repeated vertex.** -/
lemma exists_nodup_walk {G : Digraph X A} [DecidableEq X] {x y : X} {l : List A}
    (h : LWalk G x y l) : ∃ l', LWalk G x y l' ∧ l'.Sublist l ∧ (l'.map G.src).Nodup := by
  induction h with
  | nil x => exact ⟨[], .nil x, .refl _, by simp⟩
  | @cons a y l₀ _ ih =>
    obtain ⟨l', hl', hsub, hnd⟩ := ih
    by_cases hx : G.src a ∈ l'.map G.src
    · obtain ⟨b, hb, hba⟩ := List.mem_map.1 hx
      obtain ⟨p, q, rfl⟩ := List.append_of_mem hb
      obtain ⟨z, -, hz⟩ := hl'.split
      obtain ⟨hzb, -⟩ := LWalk.cons_iff.1 hz
      subst hzb
      refine ⟨b :: q, hba ▸ hz, ?_, ?_⟩
      · exact ((List.sublist_append_right p (b :: q)).trans hsub).cons a
      · rw [List.map_append] at hnd
        exact (List.nodup_append.1 hnd).2.1
    · exact ⟨a :: l', .cons hl', hsub.cons_cons a, List.nodup_cons.2 ⟨hx, hnd⟩⟩

/-- `G'` is **the perturbation** of `G` by the distinct indices `ι a < c`. -/
structure IsPerturb (G G' : Digraph X A) (ι : A → ℕ) (c : ℕ) : Prop where
  src : G'.src = G.src
  dst : G'.dst = G.dst
  len : ∀ a, G'.len a = 2 ^ c * G.len a + 2 ^ ι a
  inj : Function.Injective ι
  lt : ∀ a, ι a < c

/-- The perturbation of a list of arcs. -/
def psum (ι : A → ℕ) (l : List A) : ℕ := (l.map fun a => 2 ^ ι a).sum

variable {G G' : Digraph X A} {ι : A → ℕ} {c : ℕ} (hP : IsPerturb G G' ι c)
include hP

lemma IsPerturb.lwalk_iff {x y : X} {l : List A} : LWalk G' x y l ↔ LWalk G x y l :=
  ⟨lwalk_of_eq hP.src.symm hP.dst.symm, lwalk_of_eq hP.src hP.dst⟩

lemma IsPerturb.reach_iff {x y : X} : Reach G' x y ↔ Reach G x y :=
  ⟨fun ⟨l, h⟩ => ⟨l, hP.lwalk_iff.1 h⟩, fun ⟨l, h⟩ => ⟨l, hP.lwalk_iff.2 h⟩⟩

lemma IsPerturb.wlen_eq (l : List A) : wlen G' l = 2 ^ c * wlen G l + (psum ι l : ℤ) := by
  induction l with
  | nil => simp [psum]
  | cons a l ih => simp only [wlen_cons, ih, hP.len, psum, List.map_cons, List.sum_cons]; push_cast; ring

lemma IsPerturb.psum_lt {l : List A} (hl : l.Nodup) : psum ι l < 2 ^ c := by
  have hnd : (l.map ι).Nodup := hl.map hP.inj
  have : psum ι l = ∑ i ∈ (l.map ι).toFinset, 2 ^ i := by
    rw [List.sum_toFinset _ hnd, psum, List.map_map]; rfl
  rw [this]
  exact Nat.geomSum_lt le_rfl fun i hi => by
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hi)
    exact hP.lt a

/-- Lists without repetition with the same perturbation have the same arcs. -/
lemma IsPerturb.mem_of_psum_eq {l₁ l₂ : List A} (h₁ : l₁.Nodup) (h₂ : l₂.Nodup)
    (h : psum ι l₁ = psum ι l₂) {a : A} (ha : a ∈ l₁) : a ∈ l₂ := by
  classical
  have e : ∀ l : List A, l.Nodup → psum ι l = ∑ i ∈ (l.map ι).toFinset, 2 ^ i := by
    intro l hl
    rw [List.sum_toFinset _ (hl.map hP.inj), psum, List.map_map]; rfl
  rw [e _ h₁, e _ h₂] at h
  have hs : (l₁.map ι).toFinset = (l₂.map ι).toFinset := by
    have := congrArg (fun n => n.bitIndices.toFinset) h
    simpa only [Finset.toFinset_bitIndices_sum_two_pow] using this
  have : ι a ∈ (l₂.map ι).toFinset := hs ▸ List.mem_toFinset.2 (List.mem_map_of_mem ha)
  obtain ⟨b, hb, hab⟩ := List.mem_map.1 (List.mem_toFinset.1 this)
  rwa [← hP.inj hab]

variable (hnn : ∀ a, 0 ≤ G.len a)
include hnn

lemma IsPerturb.pos (a : A) : 0 < G'.len a := by
  rw [hP.len]; have := hnn a; positivity

/-- **Perturbed distances**: `2^c · dist ≤ dist' < 2^c · (dist + 1)`. -/
theorem IsPerturb.dist_bounds [DecidableEq X] {x y : X} (h : Reach G x y) :
    2 ^ c * dist G x y ≤ dist G' x y ∧ dist G' x y < 2 ^ c * (dist G x y + 1) := by
  have hpos := hP.pos hnn
  have hnn' : ∀ a, 0 ≤ G'.len a := fun a => (hpos a).le
  constructor
  · obtain ⟨L, hL⟩ := exists_isSP hnn' (hP.reach_iff.2 h)
    have hd := dist_le hnn (hP.lwalk_iff.1 hL.1)
    rw [← hL.2, hP.wlen_eq]
    have : (0 : ℤ) ≤ psum ι L := Int.natCast_nonneg _
    have h2 : (0 : ℤ) < 2 ^ c := by positivity
    nlinarith
  · obtain ⟨L, hL, hLe⟩ := exists_walk_dist hnn h
    obtain ⟨L', hL', hsub, hnd⟩ := exists_nodup_walk hL
    have h1 : wlen G L' ≤ wlen G L := by
      unfold wlen
      exact (hsub.map G.len).sum_le_sum fun x hx => by
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx; exact hnn a
    have h2 := dist_le hnn hL'
    have h3 := dist_le hnn' (hP.lwalk_iff.2 hL')
    have h4 := hP.psum_lt (hnd.of_map _)
    rw [hP.wlen_eq] at h3
    have : (psum ι L' : ℤ) < 2 ^ c := by exact_mod_cast h4
    have h5 : wlen G L' = dist G x y := by omega
    rw [h5] at h3
    linarith

/-- **The distances are the perturbed distances divided by `2^c`.** -/
theorem IsPerturb.dist_div [DecidableEq X] {x y : X} (h : Reach G x y) :
    dist G x y = dist G' x y / 2 ^ c := by
  obtain ⟨h1, h2⟩ := hP.dist_bounds hnn h
  have hc : (0 : ℤ) < 2 ^ c := by positivity
  obtain ⟨s, hs⟩ : ∃ s, dist G' x y = 2 ^ c * dist G x y + s := ⟨_, (add_sub_cancel _ _).symm⟩
  rw [hs] at h1 h2 ⊢
  rw [show 2 ^ c * dist G x y + s = s + dist G x y * 2 ^ c by ring,
    Int.add_mul_ediv_right _ _ hc.ne', Int.ediv_eq_zero_of_lt (by linarith) (by linarith),
    zero_add]

/-- **The perturbation makes tight arcs unique.** -/
theorem IsPerturb.uniqTight [DecidableEq X] : UniqTight G' := by
  have hpos := hP.pos hnn
  have hnn' : ∀ a, 0 ≤ G'.len a := fun a => (hpos a).le
  intro r a b ha hb hab hy
  -- shortest walks ending with `a` and with `b`
  have walk : ∀ e : A, Tight G' r e → ∃ L, IsSP G' r (G'.dst e) (L ++ [e]) := by
    intro e he
    obtain ⟨L, hL⟩ := exists_isSP hnn' he.1
    refine ⟨L, hL.1.concat rfl, ?_⟩
    rw [wlen_append, hL.2]; simp only [wlen_cons, wlen_nil, add_zero]; exact he.2
  obtain ⟨La, hLa⟩ := walk a ha
  obtain ⟨Lb, hLb⟩ := walk b hb
  rw [hab] at hLa
  have nda := (hLa.nodup_src hpos).of_map _
  have ndb := (hLb.nodup_src hpos).of_map _
  -- the same perturbation
  have hps : psum ι (La ++ [a]) = psum ι (Lb ++ [b]) := by
    have e1 := hLa.2; have e2 := hLb.2
    rw [hP.wlen_eq] at e1 e2
    have p1 := hP.psum_lt nda; have p2 := hP.psum_lt ndb
    have hc : (0 : ℤ) < 2 ^ c := by positivity
    have m1 : (2 ^ c * wlen G (La ++ [a]) + (psum ι (La ++ [a]) : ℤ)) % 2 ^ c =
        psum ι (La ++ [a]) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity)
        (by exact_mod_cast p1)]
    have m2 : (2 ^ c * wlen G (Lb ++ [b]) + (psum ι (Lb ++ [b]) : ℤ)) % 2 ^ c =
        psum ι (Lb ++ [b]) := by
      rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity)
        (by exact_mod_cast p2)]
    have : (psum ι (La ++ [a]) : ℤ) = psum ι (Lb ++ [b]) := by rw [← m1, ← m2, e1, e2]
    exact_mod_cast this
  have hmem := hP.mem_of_psum_eq nda ndb hps (List.mem_append_right _ (List.mem_singleton_self a))
  by_contra hne
  rcases List.mem_append.1 hmem with hm | hm
  · -- `a` enters `dst b` before the end of the walk of `b`
    have hnd := hLb.nodup_dst hpos
    rw [List.map_append, List.nodup_append] at hnd
    exact hnd.2.2 _ (List.mem_map_of_mem hm) _ (List.mem_singleton_self _) hab
  · exact hne (List.mem_singleton.1 hm)

end Generic

/-! ### Plane maps with nonnegative lengths -/

section Planar

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The article's setting with nonnegative lengths**: as `PlanarFlow.MSSP.Hyp`, without the
positivity of the lengths and the uniqueness of shortest paths. -/
structure HypNN (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (S : Finset D) (ℓ : D → ℤ) : Prop where
  plane : M.IsPlane
  rot : M.RotTrans
  face : FaceCycle M k g
  nonneg : ∀ d ∈ S, 0 ≤ ℓ d
  noIn : ∀ d ∈ S, ¬ IsRoot M k g (M.head d)

/-- The perturbed lengths: `2^|D| · ℓ d + 2^(index of d)`. -/
noncomputable def pert (ℓ : D → ℤ) (d : D) : ℤ :=
  2 ^ Fintype.card D * ℓ d + 2 ^ (Fintype.equivFin D d : ℕ)

variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

lemma isPerturb_pert (M : CombMap D V F) (S : Finset D) (ℓ : D → ℤ) :
    IsPerturb (pieceGraph M S ℓ) (pieceGraph M S (pert ℓ))
      (fun a => (Fintype.equivFin D a.1 : ℕ)) (Fintype.card D) where
  src := rfl
  dst := rfl
  len _ := rfl
  inj _ _ h := Subtype.ext ((Fintype.equivFin D).injective (Fin.ext h))
  lt a := (Fintype.equivFin D a.1).isLt

/-- **The perturbed lengths meet the article's assumptions.** -/
theorem HypNN.hyp (H : HypNN M k g S ℓ) : Hyp M k g S (pert ℓ) where
  plane := H.plane
  rot := H.rot
  face := H.face
  pos d hd := (isPerturb_pert M S ℓ).pos (fun a => H.nonneg a.1 a.2) ⟨d, hd⟩
  noIn := H.noIn
  uniq := (isPerturb_pert M S ℓ).uniqTight (fun a => H.nonneg a.1 a.2)

/-- **The data structure on the perturbed lengths gives the distances**: from every root of the
face, the answers divided by `2^|D|` are the distances in the piece with the lengths `ℓ`. -/
theorem dkpw_pert (H : HypNN M k g S ℓ) {j : ℕ} (hj : j < k) (φ : F) (B : Finset V) (v : V) :
    (dkpw M k g S (pert ℓ) (M.tail (g j)) v).map (· / 2 ^ Fintype.card D) =
      msspDist M S ℓ φ B (M.tail (g j)) v := by
  have hP := isPerturb_pert M S ℓ
  have hnn : ∀ a : {d // d ∈ S}, 0 ≤ (pieceGraph M S ℓ).len a := fun a => H.nonneg a.1 a.2
  rw [dkpw_eq H.hyp hj φ B]
  unfold msspDist odist
  split_ifs with hS h1 h2 h2
  · rw [Option.map_some, ← hP.dist_div hnn h2]
  · exact absurd (hP.reach_iff.1 h1) h2
  · exact absurd (hP.reach_iff.2 h2) h1
  · rfl
  · rfl

/-- **The data structure for nonnegative lengths**: run on the perturbed lengths, answers divided
by `2^|D|`. -/
noncomputable def dkpwNN (M : CombMap D V F) (k : ℕ) (g : ℕ → D) (P : Finset D) (ℓ : D → ℤ)
    (b v : V) : Option ℤ :=
  (dkpw M k g P (pert ℓ) b v).map (· / 2 ^ Fintype.card D)

/-- **The data structure for nonnegative lengths is a correct multiple-source shortest path
output** for the roots of the face. -/
theorem dkpwNN_msspOut (H : HypNN M k g S ℓ) :
    MSSPOut (pieceGraph M S ℓ) (roots M k g) (dkpwNN M k g S ℓ) := by
  intro b hb
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hb
  rw [mem_range] at hj
  have h := msspDist_spec M S ℓ (M.face (g j)) {M.tail (g j)} H.nonneg
    (fun b hb => ⟨g j, rfl, by rw [mem_singleton.1 hb]⟩) _ (mem_singleton_self _)
  have e : dkpwNN M k g S ℓ (M.tail (g j)) =
      msspDist M S ℓ (M.face (g j)) {M.tail (g j)} (M.tail (g j)) :=
    funext fun v => dkpw_pert H hj _ _ v
  rw [e]; exact h

/-- **The maps of rotation systems have transitive rotations.** -/
theorem ofRotation_rotTrans {W : Type*} [Fintype W] {Γ : SimpleGraph W} [DecidableRel Γ.Adj]
    (R : Kasteleyn.RotationSystem Γ) :
    (CombMap.ofRotation R).RotTrans := by
  intro d d' h
  obtain ⟨n, hn⟩ := R.exists_rot_pow_eq (d := d) (d' := d') h
  refine ⟨n, ?_⟩
  have e : (CombMap.ofRotation R).rot = ⇑R.rot := by
    funext x; simp [CombMap.rot, CombMap.ofRotation]
  rw [e, ← Equiv.Perm.iterate_eq_pow] at *
  exact hn

end Planar

end MSSP

end PlanarFlow
