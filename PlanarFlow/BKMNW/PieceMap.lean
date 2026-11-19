module

public import PlanarFlow.BKMNW.SubMap
public import PlanarFlow.BKMNW.Sep

/-!
# Piece maps: the pieces of the decomposition as plane maps

The article (Section 2, lines 3–7 of Algorithm 1) runs the recursion on the subgraphs `G₁`,
`G₂` enclosed and not enclosed by the separator, **with the separator contracted into one node**
`v` added to `A`; the separator is a cycle of the graph in which the earlier separators are
contracted, it may pass through their nodes, and `v` contains them. This file builds these
subgraphs as plane maps, of the size of the pieces.

## The piece map of a piece

A piece is a set `P` of darts with holes `Hs` (pairwise disjoint sets of vertices: the vertices of
the separators of its ancestors, merged with the holes they meet, `PlanarFlow.BKMNW.childHoles`).
Its map (`pdarts`, `PieceInv`) has

* the darts of `P` not inside a hole (`Inner`): the darts of the contracted separators, and the
  chords of a hole, which the contraction turns into loops at the hole node, are left out (the
  article leaves out the self loop `e`);
* as vertices the vertices of `M`, each hole contracted into one vertex (`HRel`);
* the rotation obtained from the rotation of `M` by deleting and contracting edges
  (`PlanarFlow.Orbit.ret`, `PlanarFlow.Orbit.con`), computed from the rotation of the parent
  piece map in time linear in its size (`childRot`): contract the darts of the separator, then
  delete the darts outside the child.

`PieceInv P Hs σ` states that the rotation `σ` on `pdarts M P Hs` has zero Euler gap and that its
orbits are the vertices of `M`, the holes contracted.

## Main results

* `sameCycle_con_path`: **contracting a simple path merges its vertices into one**, and changes no
  other vertex. Applied to the map whose vertices are the classes of the vertices (`vmap`, `cls`:
  the hole containing a vertex, or the vertex alone), it contracts a simple path through the holes
  (`HPath.toQ`).
* `pieceInv_root`: the whole map, with no holes, satisfies `PieceInv` (`M` plane with transitive
  rotations and faces).
* `PieceInv.child`: **the child piece maps satisfy `PieceInv`**, when the separator is a simple
  path through the holes (`HPath.Simple`) with its darts in the piece map: the holes it meets are
  merged with it into one vertex (`childHoles`).
* `PieceInv.isPlane`: **a piece map is plane** when the piece is connected after contracting the
  holes (`HConn`) and has a dart outside the holes; its rotations and faces are transitive.
* `ADec.PGood`: every piece of the decomposition is connected after contracting its holes, and
  contains its separator, a simple path through its holes; `ADec.PMOk.of_pieceInv`: along a good
  decomposition with such pieces, every piece map satisfies `PieceInv`, so every piece map with a
  dart outside its holes is plane.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv CombMap Relation Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Contracting a simple path -/

namespace SPath

/-- The darts of the path before `d j`, with their reverses. -/
def pre (P : SPath M) (j : ℕ) : Finset D := (range j).biUnion fun i => {P.d i, M.rev (P.d i)}

lemma mem_pre {P : SPath M} {j : ℕ} {e : D} :
    e ∈ P.pre j ↔ ∃ i < j, e = P.d i ∨ e = M.rev (P.d i) := by
  simp [pre]

lemma pre_succ (P : SPath M) (j : ℕ) :
    P.pre (j + 1) = insert (P.d j) (insert (M.rev (P.d j)) (P.pre j)) := by
  ext e; simp only [pre, range_add_one, biUnion_insert, mem_union, mem_insert, mem_singleton]
  tauto

lemma pre_k (P : SPath M) : P.pre P.k = P.darts.toFinset := by
  ext e; rw [mem_pre, List.mem_toFinset, P.mem_darts]

lemma pre_zero (P : SPath M) : P.pre 0 = ∅ := by simp [pre]

lemma d_not_mem_pre (P : SPath M) {j : ℕ} (hj : j < P.k) : P.d j ∉ P.pre j := by
  rw [mem_pre]
  rintro ⟨i, hi, h | h⟩
  · have := P.d_inj hj (by omega) h; omega
  · exact P.d_ne_rev hj (by omega) h

lemma rev_d_not_mem_pre (P : SPath M) {j : ℕ} (hj : j < P.k) : M.rev (P.d j) ∉ P.pre j := by
  rw [mem_pre]
  rintro ⟨i, hi, h | h⟩
  · exact P.d_ne_rev (i := i) (j := j) (by omega) hj h.symm
  · have := P.d_inj hj (by omega) (M.rev_injective h); omega

end SPath

lemma sdiff_insert_insert (A s : Finset D) (a b : D) :
    A \ insert a (insert b s) = ((A \ s).erase a).erase b := by
  ext z; simp only [mem_sdiff, mem_insert, mem_erase]; tauto

/-- **Contracting a simple path merges its vertices into one vertex** and changes no other vertex:
if the orbits of the rotation `σ` on `A` are the classes of a relation `R` between the tails, and
the vertices of the path are related only to themselves, then after contracting the darts of the
path the orbits are the classes of `R` with the vertices of the path joined. -/
theorem sameCycle_con_path (P : SPath M) {σ : Perm D} {A : Finset D} (hσ : Stable σ A)
    (hA : Stable (revPerm M) A) (hPA : ∀ e ∈ P.darts, e ∈ A) {R : V → V → Prop}
    (hR : ∀ x ∈ A, ∀ y ∈ A, σ.SameCycle x y ↔ R (M.tail x) (M.tail y))
    (hiso : ∀ i ≤ P.k, ∀ w, R (P.p i) w ↔ w = P.p i) :
    Stable (revPerm M) (A \ P.darts.toFinset) ∧
    ∀ x ∈ A \ P.darts.toFinset, ∀ y ∈ A \ P.darts.toFinset,
      (con (revPerm M) σ (A \ P.darts.toFinset)).SameCycle x y ↔
        R (M.tail x) (M.tail y) ∨ (M.tail x ∈ P.verts ∧ M.tail y ∈ P.verts) := by
  have hι := revPerm_isInv M
  have key : ∀ j ≤ P.k, Stable (revPerm M) (A \ P.pre j) ∧ ∀ x ∈ A \ P.pre j, ∀ y ∈ A \ P.pre j,
      (con (revPerm M) σ (A \ P.pre j)).SameCycle x y ↔
        R (M.tail x) (M.tail y) ∨ (M.tail x ∈ P.init j ∧ M.tail y ∈ P.init j) := by
    intro j
    induction j with
    | zero =>
      intro _
      rw [P.pre_zero, sdiff_empty]
      refine ⟨hA, fun x hx y hy => ?_⟩
      rw [sameCycle_congr (stable_con hι hA) (fun z hz => con_self_apply hι hσ hA hz) hx,
        hR x hx y hy]
      constructor
      · exact Or.inl
      · rintro (h | ⟨ha, hb⟩)
        · exact h
        · obtain ⟨t, ht, e1⟩ := P.mem_init.1 ha
          obtain ⟨t', ht', e2⟩ := P.mem_init.1 hb
          rw [← e1, ← e2, show t = 0 by omega, show t' = 0 by omega]
          exact (hiso 0 (Nat.zero_le _) _).2 rfl
    | succ j ih =>
      intro hj
      obtain ⟨hAj, ihR⟩ := ih (by omega)
      have hjk : j < P.k := by omega
      have hdA : P.d j ∈ A \ P.pre j :=
        mem_sdiff.2 ⟨hPA _ (P.d_mem j hjk), P.d_not_mem_pre hjk⟩
      have hrdA : revPerm M (P.d j) ∈ A \ P.pre j :=
        mem_sdiff.2 ⟨hPA _ (P.rev_d_mem j hjk), P.rev_d_not_mem_pre hjk⟩
      have e : A \ P.pre (j + 1) = ((A \ P.pre j).erase (P.d j)).erase (revPerm M (P.d j)) := by
        rw [P.pre_succ, sdiff_insert_insert]; rfl
      have t1 : M.tail (P.d j) = P.p j := P.tail_d j hjk
      have t2 : M.tail (revPerm M (P.d j)) = P.p (j + 1) := P.head_d j hjk
      have c1 : ∀ z ∈ A \ P.pre j, (con (revPerm M) σ (A \ P.pre j)).SameCycle (P.d j) z ↔
          M.tail z ∈ P.init j := fun z hz => by
        rw [ihR _ hdA z hz, t1, hiso j hjk.le]
        constructor
        · rintro (h | ⟨-, h⟩)
          · rw [h]; exact P.p_mem_init le_rfl
          · exact h
        · exact fun h => Or.inr ⟨P.p_mem_init le_rfl, h⟩
      have c2 : ∀ z ∈ A \ P.pre j,
          (con (revPerm M) σ (A \ P.pre j)).SameCycle (revPerm M (P.d j)) z ↔
            M.tail z = P.p (j + 1) := fun z hz => by
        rw [ihR _ hrdA z hz, t2, hiso (j + 1) hj]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact h
          · exact absurd ((P.p_mem_init_iff hj hjk.le).1 h) (by omega)
        · exact Or.inl
      have hne : ¬ (con (revPerm M) σ (A \ P.pre j)).SameCycle (P.d j) (revPerm M (P.d j)) := by
        rw [c1 _ hrdA, t2, P.p_mem_init_iff hj hjk.le]; omega
      have hinit : ∀ a, a ∈ P.init (j + 1) ↔ a ∈ P.init j ∨ a = P.p (j + 1) := fun a => by
        simp only [P.mem_init]
        constructor
        · rintro ⟨t, ht, rfl⟩
          rcases Nat.lt_or_ge t (j + 1) with h | h
          · exact Or.inl ⟨t, by omega, rfl⟩
          · exact Or.inr (by rw [show t = j + 1 by omega])
        · rintro (⟨t, ht, rfl⟩ | rfl)
          · exact ⟨t, by omega, rfl⟩
          · exact ⟨j + 1, le_rfl, rfl⟩
      rw [e]
      have hsub : ((A \ P.pre j).erase (P.d j)).erase (revPerm M (P.d j)) ⊆ A \ P.pre j :=
        (erase_subset _ _).trans (erase_subset _ _)
      refine ⟨stable_erase_pair hι hAj hdA, fun x hx y hy => ?_⟩
      have mx := hsub hx
      have my := hsub hy
      rw [← con_con hι hsub, sameCycle_con_erase hι (stable_con hι hAj) hAj hdA hne hx hy,
        ihR x mx y my, c1 x mx, c1 y my, c2 x mx, c2 y my, hinit, hinit]
      tauto
  obtain ⟨h1, h2⟩ := key P.k le_rfl
  rw [P.pre_k] at h1 h2
  exact ⟨h1, h2⟩

/-! ### Holes -/

/-- Two vertices are equal or lie in a common hole: the vertices of the piece map. -/
def HRel (Hs : List (Finset V)) (a b : V) : Prop := a = b ∨ ∃ H ∈ Hs, a ∈ H ∧ b ∈ H

lemma hRel_append {Hs : List (Finset V)} {C : Finset V} {a b : V} :
    HRel (Hs ++ [C]) a b ↔ HRel Hs a b ∨ (a ∈ C ∧ b ∈ C) := by
  simp only [HRel, List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | ⟨H, hH | rfl, ha, hb⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨H, hH, ha, hb⟩)
    · exact Or.inr ⟨ha, hb⟩
  · rintro ((h | ⟨H, hH, ha, hb⟩) | ⟨ha, hb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨H, Or.inl hH, ha, hb⟩
    · exact Or.inr ⟨C, Or.inr rfl, ha, hb⟩

lemma hRel_of_not_mem {Hs : List (Finset V)} {a : V} (ha : a ∉ hunion Hs) {w : V} :
    HRel Hs a w ↔ w = a := by
  simp only [HRel]
  constructor
  · rintro (rfl | ⟨H, hH, h, -⟩)
    · rfl
    · exact absurd (subset_hunion hH h) ha
  · rintro rfl; exact Or.inl rfl

lemma hRel_symm' {Hs : List (Finset V)} {a b : V} (h : HRel Hs a b) : HRel Hs b a := by
  rcases h with h | ⟨H, hH, h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨H, hH, h2, h1⟩

/-- **The holes of the children merge the holes met by the separator**: two vertices are equal
or in a common hole of the children if and only if they are equal or in a common hole, or both
in the new hole. -/
lemma hRel_childHoles {Hs : List (Finset V)} {C : Finset V} {a b : V} :
    HRel (childHoles Hs C) a b ↔ HRel Hs a b ∨ (a ∈ newHole Hs C ∧ b ∈ newHole Hs C) := by
  simp only [HRel, childHoles, List.mem_append, List.mem_filter, List.mem_singleton,
    decide_eq_true_eq]
  constructor
  · rintro (h | ⟨H, ⟨hH, -⟩ | rfl, ha, hb⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨H, hH, ha, hb⟩)
    · exact Or.inr ⟨ha, hb⟩
  · rintro ((h | ⟨H, hH, ha, hb⟩) | ⟨ha, hb⟩)
    · exact Or.inl h
    · by_cases hd : Disjoint H C
      · exact Or.inr ⟨H, Or.inl ⟨hH, hd⟩, ha, hb⟩
      · exact Or.inr ⟨newHole Hs C, Or.inr rfl, mem_newHole.2 (Or.inr ⟨H, hH, hd, ha⟩),
          mem_newHole.2 (Or.inr ⟨H, hH, hd, hb⟩)⟩
    · exact Or.inr ⟨newHole Hs C, Or.inr rfl, ha, hb⟩

/-- Two vertices in a common hole are in a common hole of the children. -/
lemma HRel.childHoles {Hs : List (Finset V)} {C : Finset V} {a b : V} (h : HRel Hs a b) :
    HRel (childHoles Hs C) a b := hRel_childHoles.2 (Or.inl h)

/-! ### The class of a vertex -/

open Classical in
/-- **The class of a vertex**: the hole containing it, or the vertex alone. With pairwise
disjoint holes, two vertices have the same class if and only if they are equal or lie in a common
hole (`hRel_iff_cls`): the classes are the vertices of the piece map. -/
noncomputable def cls (Hs : List (Finset V)) (v : V) : Finset V :=
  if h : ∃ H ∈ Hs, v ∈ H then h.choose else {v}

lemma cls_of_mem {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {H : Finset V} (hH : H ∈ Hs)
    {v : V} (hv : v ∈ H) : cls Hs v = H := by
  unfold cls
  split_ifs with hex
  · obtain ⟨h1, h2⟩ := hex.choose_spec
    by_contra hne
    exact disjoint_left.1 (disjoint_of_pairwise hd h1 hH hne) h2 hv
  · exact absurd ⟨H, hH, hv⟩ hex

lemma cls_of_not_mem {Hs : List (Finset V)} {v : V} (hv : v ∉ hunion Hs) : cls Hs v = {v} := by
  unfold cls
  split_ifs with hex
  · obtain ⟨H, hH, h⟩ := hex; exact absurd (subset_hunion hH h) hv
  · rfl

lemma mem_cls_self (Hs : List (Finset V)) (v : V) : v ∈ cls Hs v := by
  unfold cls
  split_ifs with h
  · exact h.choose_spec.2
  · exact mem_singleton_self v

/-- **With pairwise disjoint holes, the classes are the vertices of the piece map.** -/
lemma hRel_iff_cls {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {a b : V} :
    HRel Hs a b ↔ cls Hs a = cls Hs b := by
  constructor
  · rintro (rfl | ⟨H, hH, ha, hb⟩)
    · rfl
    · rw [cls_of_mem hd hH ha, cls_of_mem hd hH hb]
  · intro e
    by_cases ha : a ∈ hunion Hs
    · obtain ⟨H, hH, haH⟩ := mem_hunion.1 ha
      have hb : b ∈ H := by rw [← cls_of_mem hd hH haH, e]; exact mem_cls_self Hs b
      exact Or.inr ⟨H, hH, haH, hb⟩
    · have hb : b ∈ cls Hs a := by rw [e]; exact mem_cls_self Hs b
      rw [cls_of_not_mem ha, mem_singleton] at hb
      exact Or.inl hb.symm

variable (M) in
/-- **The map with its vertices renamed** by `g` (same darts, reversal and faces): with `g` the
class of a vertex, a path through the holes is a simple path of this map. -/
def vmap {W : Type*} (g : V → W) : CombMap D W F where
  rev := M.rev
  rev_rev := M.rev_rev
  rev_ne := M.rev_ne
  tail d := g (M.tail d)
  face := M.face
  next := M.next
  next_injective := M.next_injective
  face_next := M.face_next
  tail_next d := congrArg g (M.tail_next d)

/-- **A simple path through the holes**: the head of `d j` is `p (j + 1)` or lies in a hole with
it, and the vertices `p 0, …, p k` are distinct and in distinct holes. -/
def HPath.Simple (ρ : HPath M) (Hs : List (Finset V)) : Prop :=
  (∀ j < ρ.k, HRel Hs (M.head (ρ.d j)) (ρ.p (j + 1))) ∧
    ∀ i ≤ ρ.k, ∀ j ≤ ρ.k, HRel Hs (ρ.p i) (ρ.p j) → i = j

/-- A simple path avoiding the holes is a simple path through the holes. -/
lemma SPath.toH_simple (π : SPath M) {Hs : List (Finset V)} (h : Disjoint π.verts (hunion Hs)) :
    π.toH.Simple Hs := by
  refine ⟨fun j hj => Or.inl (π.head_d j hj), fun i hi j hj (e : HRel Hs (π.p i) (π.p j)) => ?_⟩
  rw [hRel_of_not_mem (disjoint_left.1 h (π.p_mem_init hi))] at e
  exact π.inj i hi j hj e.symm

/-- **A simple path through the holes, as a simple path of the classes** (`vmap M (cls Hs)`). -/
noncomputable def HPath.toQ (ρ : HPath M) (Hs : List (Finset V)) (hd : Hs.Pairwise Disjoint)
    (h : ρ.Simple Hs) : SPath (vmap M (cls Hs)) where
  k := ρ.k
  d := ρ.d
  p j := cls Hs (ρ.p j)
  tail_d j hj := by show cls Hs (M.tail (ρ.d j)) = _; rw [ρ.tail_d j hj]
  head_d j hj := (hRel_iff_cls hd).1 (h.1 j hj)
  inj i hi j hj e := h.2 i hi j hj ((hRel_iff_cls hd).2 e)

/-- **The classes on the path are the classes of the new hole.** -/
lemma HPath.cls_mem_toQ_verts {ρ : HPath M} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    (h : ρ.Simple Hs) {v : V} :
    cls Hs v ∈ (ρ.toQ Hs hd h).verts ↔ v ∈ newHole Hs ρ.mverts := by
  rw [SPath.verts, SPath.mem_init]
  show (∃ t ≤ ρ.k, cls Hs (ρ.p t) = cls Hs v) ↔ _
  -- the classes of the vertices of the path
  have key : ∀ m ∈ ρ.mverts, ∃ t ≤ ρ.k, cls Hs (ρ.p t) = cls Hs m := by
    intro m hm
    rcases ρ.mem_mverts.1 hm with ⟨t, ht, rfl⟩ | ⟨j, hj, rfl⟩
    · exact ⟨t, ht, rfl⟩
    · exact ⟨j + 1, hj, ((hRel_iff_cls hd).1 (h.1 j hj)).symm⟩
  rw [mem_newHole]
  constructor
  · rintro ⟨t, ht, e⟩
    rcases (hRel_iff_cls hd).2 e with e | ⟨H, hH, h1, h2⟩
    · exact Or.inl (e ▸ ρ.p_mem_mverts ht)
    · exact Or.inr ⟨H, hH, not_disjoint_iff.2 ⟨_, h1, ρ.p_mem_mverts ht⟩, h2⟩
  · rintro (hv | ⟨H, hH, hHC, hv⟩)
    · exact key v hv
    · obtain ⟨m, hmH, hm⟩ := not_disjoint_iff.1 hHC
      obtain ⟨t, ht, e⟩ := key m hm
      exact ⟨t, ht, e.trans ((hRel_iff_cls hd).1 (Or.inr ⟨H, hH, hmH, hv⟩))⟩

variable (M) in
/-- A dart inside a hole: both its ends in one hole. -/
def Inner (Hs : List (Finset V)) (d : D) : Prop := ∃ H ∈ Hs, M.tail d ∈ H ∧ M.head d ∈ H

lemma inner_rev {Hs : List (Finset V)} {d : D} : Inner M Hs (M.rev d) ↔ Inner M Hs d := by
  simp only [Inner, tail_rev, head_rev]
  exact exists_congr fun H => and_congr_right fun _ => and_comm

variable (M) in
/-- **The darts of the piece map**: the darts of the piece not inside a hole. -/
noncomputable def pdarts (P : Finset D) (Hs : List (Finset V)) : Finset D := by
  classical exact P.filter fun d => ¬ Inner M Hs d

lemma mem_pdarts {P : Finset D} {Hs : List (Finset V)} {d : D} :
    d ∈ pdarts M P Hs ↔ d ∈ P ∧ ¬ Inner M Hs d := by
  classical simp [pdarts]

lemma pdarts_subset (P : Finset D) (Hs : List (Finset V)) : pdarts M P Hs ⊆ P := fun _ h =>
  (mem_pdarts.1 h).1

lemma stable_pdarts {P : Finset D} (hP : RevClosed M P) (Hs : List (Finset V)) :
    Stable (revPerm M) (pdarts M P Hs) := fun d hd => by
  rw [mem_pdarts] at hd ⊢
  exact ⟨hP d hd.1, by rw [revPerm_apply, inner_rev]; exact hd.2⟩

lemma pdarts_univ_nil : pdarts M (univ : Finset D) [] = univ := by
  ext d; simp [mem_pdarts, Inner]

variable (M) in
/-- **A piece connected after contracting its holes**: any two darts of the piece map are joined by
steps to the reverse dart, or to a dart whose tail is the same vertex of the piece map. -/
def HConn (P : Finset D) (Hs : List (Finset V)) : Prop :=
  ∀ x ∈ pdarts M P Hs, ∀ y ∈ pdarts M P Hs, ReflTransGen
    (fun a b => b ∈ pdarts M P Hs ∧ (b = M.rev a ∨ HRel Hs (M.tail a) (M.tail b))) x y

/-! ### The piece maps -/

variable (M) in
/-- **The invariant of a piece map**: the rotation `σ` maps the darts of the piece map into
themselves, has zero Euler gap, and its orbits are the vertices of `M` with the holes
contracted. -/
structure PieceInv (P : Finset D) (Hs : List (Finset V)) (σ : Perm D) : Prop where
  rev : RevClosed M P
  stable : Stable σ (pdarts M P Hs)
  gap : gap (revPerm M) σ (pdarts M P Hs) = 0
  vert : ∀ x ∈ pdarts M P Hs, ∀ y ∈ pdarts M P Hs,
    σ.SameCycle x y ↔ HRel Hs (M.tail x) (M.tail y)

/-- **The whole map is a piece map**, with no holes. -/
theorem pieceInv_root (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hD : Nonempty D) : PieceInv M univ [] (rotPerm M) := by
  refine ⟨fun _ _ => mem_univ _, ?_, ?_, ?_⟩ <;> rw [pdarts_univ_nil]
  · exact fun _ _ => mem_univ _
  · exact (gap_rot_eq_zero hM hrot hface hD).2
  · intro x _ y _
    rw [sameCycle_rotPerm hrot]
    simp [HRel]

variable (M) in
/-- **The rotation of a child piece map**, from the rotation `σ` of the parent piece map on its
darts `B`: contract the darts `L` of the separator, then delete the darts outside the child
`Bc`. -/
noncomputable def childRot (σ : Perm D) (B : Finset D) (L : List D) (Bc : Finset D) : Perm D :=
  ret (con (revPerm M) σ (B \ L.toFinset)) Bc

/-- A dart of a child piece map is a dart of the parent piece map. -/
lemma pdarts_childHoles_subset {P Pc : Finset D} {Hs : List (Finset V)} {C : Finset V}
    (hPc : Pc ⊆ P) : pdarts M Pc (childHoles Hs C) ⊆ pdarts M P Hs := fun d hd => by
  rw [mem_pdarts] at hd ⊢
  refine ⟨hPc hd.1, fun ⟨H, hH, h1, h2⟩ => hd.2 ?_⟩
  obtain ⟨H', hH', hsub⟩ := exists_childHoles (C := C) hH
  exact ⟨H', hH', hsub h1, hsub h2⟩

/-- **The child piece maps satisfy the invariant**, when the separator is a simple path through
the holes of the parent piece map (the holes pairwise disjoint): contracting its darts merges the
holes it meets with it into one vertex, the new hole. -/
theorem PieceInv.child {P Pc : Finset D} {Hs : List (Finset V)} {σ : Perm D}
    (h : PieceInv M P Hs σ) (hd : Hs.Pairwise Disjoint) {ρ : HPath M} (hρ : ρ.Simple Hs)
    (hρP : ∀ e ∈ ρ.darts, e ∈ pdarts M P Hs) (hPc : Pc ⊆ P) (hrev : RevClosed M Pc) :
    PieceInv M Pc (childHoles Hs ρ.mverts)
      (childRot M σ (pdarts M P Hs) ρ.darts (pdarts M Pc (childHoles Hs ρ.mverts))) := by
  have hι := revPerm_isInv M
  have hB := stable_pdarts h.rev Hs
  have hR : ∀ x ∈ pdarts M P Hs, ∀ y ∈ pdarts M P Hs, σ.SameCycle x y ↔
      (vmap M (cls Hs)).tail x = (vmap M (cls Hs)).tail y := fun x hx y hy => by
    rw [h.vert x hx y hy]; exact hRel_iff_cls hd
  obtain ⟨hA', hsc⟩ := sameCycle_con_path (ρ.toQ Hs hd hρ) h.stable hB hρP hR
    (fun _ _ _ => eq_comm)
  have hA'' : Stable (revPerm M) (pdarts M P Hs \ ρ.darts.toFinset) := hA'
  have hsc' : ∀ x ∈ pdarts M P Hs \ ρ.darts.toFinset, ∀ y ∈ pdarts M P Hs \ ρ.darts.toFinset,
      (con (revPerm M) σ (pdarts M P Hs \ ρ.darts.toFinset)).SameCycle x y ↔
        cls Hs (M.tail x) = cls Hs (M.tail y) ∨ (cls Hs (M.tail x) ∈ (ρ.toQ Hs hd hρ).verts ∧
          cls Hs (M.tail y) ∈ (ρ.toQ Hs hd hρ).verts) := hsc
  have hsub : pdarts M Pc (childHoles Hs ρ.mverts) ⊆ pdarts M P Hs \ ρ.darts.toFinset := by
    intro d hd'
    refine mem_sdiff.2 ⟨pdarts_childHoles_subset hPc hd', fun hdρ => ?_⟩
    rw [List.mem_toFinset] at hdρ
    obtain ⟨h1, h2⟩ := ρ.ends_mem hdρ
    exact (mem_pdarts.1 hd').2 ⟨newHole Hs ρ.mverts,
      List.mem_append_right _ (List.mem_singleton_self _), subset_newHole h1, subset_newHole h2⟩
  have hstc : Stable (con (revPerm M) σ (pdarts M P Hs \ ρ.darts.toFinset))
      (pdarts M P Hs \ ρ.darts.toFinset) := stable_con hι hA''
  refine ⟨hrev, stable_ret _ _, ?_, fun x hx y hy => ?_⟩
  · exact gap_ret_eq_zero hι hstc hA'' hsub (stable_pdarts hrev _)
      (gap_con_eq_zero hι h.stable hB sdiff_subset hA'' h.gap)
  · rw [childRot, sameCycle_ret hx hy, hsc' x (hsub hx) y (hsub hy), hRel_childHoles,
      hRel_iff_cls hd, HPath.cls_mem_toQ_verts, HPath.cls_mem_toQ_verts]

/-- The orbits of the rotation of a piece map are its vertices: connected pieces give connected
submaps. -/
lemma PieceInv.conn {P : Finset D} {Hs : List (Finset V)} {σ : Perm D} (h : PieceInv M P Hs σ)
    (hc : HConn M P Hs) : ∀ x ∈ pdarts M P Hs, ∀ y ∈ pdarts M P Hs, Conn (revPerm M) σ x y := by
  intro x hx y hy
  have key : ∀ z, ReflTransGen (fun a b => b ∈ pdarts M P Hs ∧
      (b = M.rev a ∨ HRel Hs (M.tail a) (M.tail b))) x z → z ∈ pdarts M P Hs ∧
        Conn (revPerm M) σ x z := by
    intro z hz
    induction hz with
    | refl => exact ⟨hx, .refl⟩
    | tail _ hst ih =>
      rename_i b c _
      refine ⟨hst.1, ih.2.trans ?_⟩
      rcases hst.2 with e | e
      · exact .single (Or.inr e)
      · exact conn_of_sameCycle ((h.vert b ih.1 c hst.1).2 e)
  exact (key y (hc x hx y hy)).2

/-- **A piece map is plane** when the piece is connected after contracting its holes and has a
dart outside the holes; its rotations and faces are transitive. -/
theorem PieceInv.isPlane {P : Finset D} {Hs : List (Finset V)} {σ : Perm D}
    (h : PieceInv M P Hs σ) (hc : HConn M P Hs) {x₀ : D} (hx₀ : x₀ ∈ pdarts M P Hs) :
    (subMap (pdarts M P Hs) (revPerm_isInv M) h.stable (stable_pdarts h.rev Hs)).IsPlane ∧
      (subMap (pdarts M P Hs) (revPerm_isInv M) h.stable (stable_pdarts h.rev Hs)).RotTrans ∧
      (subMap (pdarts M P Hs) (revPerm_isInv M) h.stable (stable_pdarts h.rev Hs)).FaceTrans :=
  ⟨subMap_isPlane _ _ _ hx₀ (h.conn hc) h.gap, subMap_rotTrans _ _ _, subMap_faceTrans _ _ _⟩

namespace ADec

/-- The last vertex of a separator of at least one dart is the tail of a dart of its piece: the
reverse of its last dart. -/
lemma _root_.PlanarFlow.BKMNW.SPath.exists_last_of_pos (π : SPath M) {P : Finset D}
    (hP : ∀ e ∈ π.darts, e ∈ P) (hk : 0 < π.k) : ∃ x ∈ P, M.tail x = π.p π.k := by
  refine ⟨M.rev (π.d (π.k - 1)), hP _ (π.rev_d_mem _ (by omega)), ?_⟩
  have := π.head_d (π.k - 1) (by omega)
  rw [show π.k - 1 + 1 = π.k by omega] at this
  rw [tail_rev]; exact this

variable (M) in
/-- **Pieces as in the article**: every piece of the decomposition is connected after contracting
its holes, its separator is a simple path through its holes (`HPath.Simple`) whose darts are darts
of its piece map, and every part of the separator off the holes lies in the piece, its last
vertex a vertex of the piece (for a part of at least one dart, this follows from the previous
condition; a part may be a path of one vertex). -/
def PGood : ADec M → List (Finset V) → Prop
  | leaf Q, Hs => HConn M Q Hs
  | node l r π, Hs => HConn M (l.piece ∪ r.piece) Hs ∧ π.path.Simple Hs ∧
      (∀ e ∈ π.path.darts, e ∈ pdarts M (l.piece ∪ r.piece) Hs) ∧
      l.PGood (childHoles Hs π.path.mverts) ∧ r.PGood (childHoles Hs π.path.mverts) ∧
      ∀ σ ∈ π.segs, (∀ e ∈ σ.darts, e ∈ l.piece ∪ r.piece) ∧
        ∃ x ∈ l.piece ∪ r.piece, M.tail x = σ.p σ.k

lemma PGood.hConn {Hs : List (Finset V)} :
    ∀ {τ : ADec M}, τ.PGood M Hs → HConn M τ.piece Hs
  | leaf _, h => h
  | node _ _ _, h => h.1

variable (M) in
/-- **The piece maps along the decomposition**, from the rotation `σ` of the piece map of the
root: every piece map satisfies `PieceInv`, its rotation computed from its parent's by
`childRot`. -/
def PMOk : ADec M → List (Finset V) → Perm D → Prop
  | leaf Q, Hs, σ => PieceInv M Q Hs σ
  | node l r π, Hs, σ => PieceInv M (l.piece ∪ r.piece) Hs σ ∧
      l.PMOk (childHoles Hs π.path.mverts)
        (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts
          (pdarts M l.piece (childHoles Hs π.path.mverts))) ∧
      r.PMOk (childHoles Hs π.path.mverts)
        (childRot M σ (pdarts M (l.piece ∪ r.piece) Hs) π.path.darts
          (pdarts M r.piece (childHoles Hs π.path.mverts)))

lemma PMOk.pieceInv {Hs : List (Finset V)} {σ : Perm D} :
    ∀ {τ : ADec M}, τ.PMOk M Hs σ → PieceInv M τ.piece Hs σ
  | leaf _, h => h
  | node _ _ _, h => h.1

/-- **Every piece map along a good decomposition with its pieces as in the article satisfies the
invariant**, from pairwise disjoint holes at the root (the holes stay pairwise disjoint along the
decomposition, `pairwise_childHoles`). -/
theorem PMOk.of_pieceInv {S T : Finset V} :
    ∀ (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D), Hs.Pairwise Disjoint →
      τ.Good M S T Hs → τ.PGood M Hs → PieceInv M τ.piece Hs σ → τ.PMOk M Hs σ
  | leaf _, _, _, _, _, _, h => h
  | node l r π, Hs, σ, hd, hg, hp, h => by
    obtain ⟨gl, gr, -⟩ := hg
    obtain ⟨-, hs, hπ, pl, pr, -⟩ := hp
    have hd' := pairwise_childHoles (C := π.path.mverts) hd
    exact ⟨h, PMOk.of_pieceInv l _ _ hd' gl pl (h.child hd hs hπ subset_union_left gl.revClosed),
      PMOk.of_pieceInv r _ _ hd' gr pr (h.child hd hs hπ subset_union_right gr.revClosed)⟩

/-- The whole map, with no holes, is connected. -/
lemma hConn_univ (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) (hD : Nonempty D) :
    HConn M (univ : Finset D) [] := by
  have key : ∀ x y, ReflTransGen (fun a b => b ∈ (univ : Finset D) ∧
      (b = M.rev a ∨ HRel ([] : List (Finset V)) (M.tail a) (M.tail b))) x y := by
    intro x y
    have hconn := (gap_rot_eq_zero hM hrot hface hD).1 x y
    induction hconn with
    | refl => exact .refl
    | tail _ hst ih =>
      rename_i b c _
      refine ih.tail ⟨mem_univ _, ?_⟩
      rcases hst with rfl | rfl
      · exact Or.inr (Or.inl (M.tail_rot b).symm)
      · exact Or.inl rfl
  intro x _ y _
  rw [pdarts_univ_nil]
  exact key x y

end ADec

end BKMNW

end PlanarFlow
