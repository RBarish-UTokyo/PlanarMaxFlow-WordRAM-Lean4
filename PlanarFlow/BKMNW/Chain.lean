module

public import PlanarFlow.BKMNW.Local

/-!
# A decomposition meeting the hypotheses of the correctness theorem, on every plane map

`PlanarFlow.BKMNW.runL_isMax` holds for every decomposition `τ` of the darts that is good
(`ADec.Good`), whose pieces are as in the article (`ADec.PGood`) and whose leaves are solved by the
leaf solver (`ADec.LeafOK`). This file shows that such a decomposition exists on every plane map
with transitive rotations and faces, for all sources and sinks (`exists_dec`), and gives one
(`chainDec`).

## Why separators of one vertex

The separators must avoid the terminals (`ADec.Good`). If they also avoid the holes, the vertices
of a separator are holes of all the pieces below it, and with separators of at least one dart and
leaves of at most one edge no decomposition exists as soon as two edges touch terminals: every
inner node needs its own separator edge with no terminal and no hole at its ends, and these edges
are pairwise distinct (two nodes on a branch have disjoint separators, two nodes off a branch
disjoint pieces); a full binary tree with `m` leaves of one edge has `m - 1` inner nodes, so
`m - 1` of the `m` edges would be separators. Giving each terminal a pendant copy (footnote 4 of
the article) does not help: the pendant edges touch terminals, and on the path `s, a, b, c, t`
with pendant copies of `s` and `t` there are `4` edges and only `2` edges between non-terminals.
(The article avoids this by triangulating with edges of capacity zero, and by contracting each
separator into a node that later separators may pass through, as `ADec.Good` allows.)

The chain below uses neither separators through holes nor preprocessing of the terminals, but
two relaxations:

* a separator may be a **path of one vertex** (a cycle reduced to one vertex, contracted into
  itself), which needs only one vertex that is neither a terminal nor a hole; and
* a leaf may be **any piece all of whose vertices are terminals or holes**: the leaf solver
  saturates every dart going up in the order sources, holes, sinks
  (`PlanarFlow.BKMNW.leafSolve_spec_ranked`).

## The decomposition

`ADec.chain x₀ L` takes the vertices of the list `L` one at a time as separators of one vertex: a
node whose left child is the rest of the chain, on the whole map, and whose right child is the
empty leaf. At the bottom, every vertex with a dart is a terminal or a hole, and the whole map is
one leaf. Every recursive step runs on the piece map of the whole map (with the vertices already
taken as holes), so the decomposition is correct but not balanced: it is the witness that the
hypotheses of the correctness theorem can be met, not the decomposition of the article, whose
existence for the cost bound needs Miller's cycle separators (`PlanarFlow.BKMNW.ADec.Bal`).

* `hConn_append`: adding a hole disjoint from the other holes keeps a piece connected after
  contracting its holes.
* `chain_spec`: the chain is good, its pieces are as in the article, its leaves are solved.
* `chainDec`, `chainDec_spec`, `exists_dec`: **the decomposition of a plane map**, for all sources
  and sinks.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Relation

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Adding a hole -/

/-- Two vertices of a hole off the other holes are related only to each other. -/
lemma hRel_eq_of_not_mem {Hs : List (Finset V)} {a b : V} (hb : b ∉ hunion Hs)
    (h : HRel Hs a b) : a = b := by
  rcases h with h | ⟨H, hH, -, h2⟩
  · exact h
  · exact absurd (subset_hunion hH h2) hb

lemma hRel_symm {Hs : List (Finset V)} {a b : V} (h : HRel Hs a b) : HRel Hs b a := by
  rcases h with h | ⟨H, hH, h1, h2⟩
  · exact Or.inl h.symm
  · exact Or.inr ⟨H, hH, h2, h1⟩

/-- **Adding a hole disjoint from the other holes keeps a piece connected after contracting its
holes**: the darts left out of the piece map lie inside the new hole, and a step through them is
a step between two vertices of the new hole. -/
theorem hConn_append {P : Finset D} {Hs : List (Finset V)} {C : Finset V}
    (hC : Disjoint C (hunion Hs)) (h : HConn M P Hs) : HConn M P (Hs ++ [C]) := by
  intro x hx y hy
  have hsub : pdarts M P (Hs ++ [C]) ⊆ pdarts M P Hs := fun d hd => by
    rw [mem_pdarts] at hd ⊢
    exact ⟨hd.1, fun ⟨H, hH, h1, h2⟩ => hd.2 ⟨H, List.mem_append_left _ hH, h1, h2⟩⟩
  -- a dart of the old piece map left out of the new one lies inside `C`
  have hout : ∀ z, z ∈ pdarts M P Hs → z ∉ pdarts M P (Hs ++ [C]) →
      M.tail z ∈ C ∧ M.head z ∈ C := fun z h1 h2 => by
    rw [mem_pdarts] at h1 h2
    push Not at h2
    obtain ⟨H, hH, ht, hh⟩ := h2 h1.1
    rcases List.mem_append.1 hH with hH | hH
    · exact absurd ⟨H, hH, ht, hh⟩ h1.2
    · rw [List.mem_singleton] at hH; subst hH; exact ⟨ht, hh⟩
  have hCn : ∀ v ∈ C, v ∉ hunion Hs := fun v hv => disjoint_left.1 hC hv
  have key : ∀ z, ReflTransGen (fun a b => b ∈ pdarts M P Hs ∧
      (b = M.rev a ∨ HRel Hs (M.tail a) (M.tail b))) x z →
      z ∈ pdarts M P Hs ∧
      (z ∈ pdarts M P (Hs ++ [C]) → ReflTransGen (fun a b => b ∈ pdarts M P (Hs ++ [C]) ∧
        (b = M.rev a ∨ HRel (Hs ++ [C]) (M.tail a) (M.tail b))) x z) ∧
      (z ∉ pdarts M P (Hs ++ [C]) → ∃ w, ReflTransGen (fun a b => b ∈ pdarts M P (Hs ++ [C]) ∧
        (b = M.rev a ∨ HRel (Hs ++ [C]) (M.tail a) (M.tail b))) x w ∧ M.tail w ∈ C) := by
    intro z hz
    induction hz with
    | refl => exact ⟨hsub hx, fun _ => .refl, fun h' => absurd hx h'⟩
    | tail _ hst ih =>
      rename_i b c _
      obtain ⟨hb0, ihin, ihout⟩ := ih
      obtain ⟨hc0, hbc⟩ := hst
      refine ⟨hc0, fun hc => ?_, fun hc => ?_⟩
      · by_cases hb : b ∈ pdarts M P (Hs ++ [C])
        · refine (ihin hb).tail ⟨hc, ?_⟩
          rcases hbc with e | e
          · exact Or.inl e
          · exact Or.inr (hRel_append.2 (Or.inl e))
        · obtain ⟨w, hw, hwC⟩ := ihout hb
          obtain ⟨hbt, hbh⟩ := hout b hb0 hb
          rcases hbc with e | e
          · exfalso
            rw [mem_pdarts] at hc
            exact hc.2 ⟨C, List.mem_append_right _ (List.mem_singleton_self _),
              by rw [e, CombMap.tail_rev]; exact hbh, by rw [e, CombMap.head_rev]; exact hbt⟩
          · have e' : M.tail c = M.tail b := hRel_eq_of_not_mem (hCn _ hbt) (hRel_symm e)
            exact hw.tail ⟨hc, Or.inr (hRel_append.2 (Or.inr ⟨hwC, e' ▸ hbt⟩))⟩
      · obtain ⟨hct, hch⟩ := hout c hc0 hc
        by_cases hb : b ∈ pdarts M P (Hs ++ [C])
        · rcases hbc with e | e
          · exfalso
            rw [mem_pdarts] at hb
            exact hb.2 ⟨C, List.mem_append_right _ (List.mem_singleton_self _),
              by rw [← CombMap.head_rev, ← e]; exact hch,
              by rw [← CombMap.tail_rev, ← e]; exact hct⟩
          · exact ⟨b, ihin hb, by rw [hRel_eq_of_not_mem (hCn _ hct) e]; exact hct⟩
        · exact ihout hb
  exact (key y (h x (hsub hx) y (hsub hy))).2.1 hy

lemma hConn_empty (Hs : List (Finset V)) : HConn M (∅ : Finset D) Hs := fun x hx => by
  have := pdarts_subset (M := M) ∅ Hs hx; simp at this

/-! ### The chain -/

namespace ADec

variable (M) in
/-- **The chain decomposition**: the vertices of `L` one at a time, each as a separator of one
vertex, the whole map as the piece of every node and the empty piece as the other child. The
dart `x₀` is only a placeholder in the paths of one vertex (`PlanarFlow.BKMNW.SPath.point`). -/
def chain (x₀ : D) : List V → ADec M
  | [] => leaf univ
  | v :: L => node (chain x₀ L) (leaf ∅) (SPath.point x₀ v).toSep

lemma point_darts (x₀ : D) (v : V) : (SPath.point (M' := M) x₀ v).darts = [] := by
  simp [SPath.darts, SPath.point]

lemma chain_piece (x₀ : D) : ∀ L : List V, (chain M x₀ L).piece = univ
  | [] => rfl
  | v :: L => by simp [chain, piece, chain_piece x₀ L]

/-- **The chain decomposition meets the hypotheses of the correctness theorem**, when the vertices
of the list are distinct, neither terminals nor holes, have a dart each, and together with the
terminals and the holes contain the tails of all the darts. -/
theorem chain_spec (x₀ : D) {S T : Finset V} :
    ∀ (L : List V) (Hs : List (Finset V)), L.Nodup →
      (∀ v ∈ L, v ∉ S ∧ v ∉ T ∧ v ∉ hunion Hs ∧ ∃ d, M.tail d = v) → HConn M univ Hs →
      (∀ d, M.tail d ∈ S ∪ T ∪ hunion Hs ∨ M.tail d ∈ L) →
      (chain M x₀ L).Good M S T Hs ∧ (chain M x₀ L).PGood M Hs ∧ (chain M x₀ L).LeafOK M S T Hs
  | [], Hs, _, _, hc, hcov =>
    ⟨fun _ _ => mem_univ _, hc, Or.inr fun d _ => by simpa using hcov d⟩
  | v :: L, Hs, hnd, hL, hc, hcov => by
    obtain ⟨hvS, hvT, hvH, d₀, hd₀⟩ := hL v (List.mem_cons_self ..)
    have hnd' := (List.nodup_cons.1 hnd)
    have hv : (SPath.point (M' := M) x₀ v).verts = {v} := SPath.point_verts _ _
    have hCd : Disjoint ({v} : Finset V) (hunion Hs) := disjoint_singleton_left.2 hvH
    have hm : (SPath.point (M' := M) x₀ v).toSep.path.mverts = {v} := by
      rw [SPath.toSep, SPath.toH_mverts, hv]
    have ech : childHoles Hs (SPath.point (M' := M) x₀ v).toSep.path.mverts = Hs ++ [{v}] := by
      rw [hm]; exact childHoles_of_disjoint hCd
    obtain ⟨g, p, o⟩ := chain_spec x₀ L (Hs ++ [{v}]) hnd'.2
      (fun w hw => by
        obtain ⟨h1, h2, h3, h4⟩ := hL w (List.mem_cons_of_mem _ hw)
        refine ⟨h1, h2, ?_, h4⟩
        rw [hunion_append, mem_union, mem_singleton, not_or]
        exact ⟨h3, fun e => hnd'.1 (e ▸ hw)⟩)
      (hConn_append hCd hc)
      (fun d => by
        rcases hcov d with h | h
        · left; rw [hunion_append]; simp only [mem_union] at h ⊢; tauto
        · rcases List.mem_cons.1 h with h | h
          · left; rw [hunion_append, h]; simp
          · exact Or.inr h)
    rw [← ech] at g p o
    have hvd : Disjoint (SPath.point (M' := M) x₀ v).verts (hunion Hs) := by rw [hv]; exact hCd
    refine ⟨⟨g, fun _ _ => by simp_all, by simp [piece], fun w hw => ?_, ?_,
        (SPath.point x₀ v).toSep_segOK hvd⟩,
      ⟨by rw [chain_piece]; simpa [piece] using hc, (SPath.point x₀ v).toH_simple hvd,
        by simp [SPath.toSep, SPath.toH_darts, point_darts], p, hConn_empty _,
        fun σ hσ => ?_⟩, o, Or.inl (by simp)⟩
    · obtain ⟨-, ⟨d, hd, -⟩⟩ := mem_bd.1 hw; simp [piece] at hd
    · rw [hm, disjoint_singleton_left]; simp only [mem_union, not_or]; exact ⟨hvS, hvT⟩
    · rw [show σ = SPath.point x₀ v by simpa [SPath.toSep] using hσ]
      exact ⟨by simp [point_darts], d₀, by simp [chain_piece], hd₀⟩

end ADec

/-! ### The decomposition of a plane map -/

variable (M) in
/-- The vertices that are not terminals and have a dart. -/
noncomputable def freeVerts (S T : Finset V) : Finset V :=
  univ.filter fun v => v ∉ S ∧ v ∉ T ∧ ∃ d, M.tail d = v

variable (M) in
open Classical in
/-- **The decomposition of a map**: the chain over the vertices that are not terminals (one leaf,
the whole map, when the map has no dart). -/
noncomputable def chainDec (S T : Finset V) : ADec M :=
  if h : Nonempty D then ADec.chain M (Classical.choice h) (freeVerts M S T).toList
  else .leaf univ

/-- **The decomposition of a plane map meets the hypotheses of the correctness theorem**: it covers
the darts, is good, its pieces are as in the article, and its leaves are solved by the leaf
solver. -/
theorem chainDec_spec (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (S T : Finset V) :
    (chainDec M S T).piece = univ ∧ (chainDec M S T).Good M S T [] ∧
      (chainDec M S T).PGood M [] ∧ (chainDec M S T).LeafOK M S T [] := by
  unfold chainDec
  split_ifs with hD
  · obtain ⟨g, p, o⟩ := ADec.chain_spec (M := M) (Classical.choice hD) (S := S) (T := T)
      (freeVerts M S T).toList [] (nodup_toList _)
      (fun v hv => by
        rw [mem_toList, freeVerts, mem_filter] at hv
        exact ⟨hv.2.1, hv.2.2.1, by simp [hunion], hv.2.2.2⟩)
      (ADec.hConn_univ hM hrot hface hD)
      (fun d => by
        by_cases h : M.tail d ∈ S ∪ T
        · exact Or.inl (mem_union_left _ h)
        · right
          rw [mem_toList, freeVerts, mem_filter]
          simp only [mem_union, not_or] at h
          exact ⟨mem_univ _, h.1, h.2, d, rfl⟩)
    exact ⟨ADec.chain_piece _ _, g, p, o⟩
  · have hD' : IsEmpty D := not_nonempty_iff.1 hD
    refine ⟨rfl, fun d _ => isEmptyElim d, fun d => isEmptyElim d, Or.inl ?_⟩
    simp

/-- **A decomposition meeting the hypotheses of `PlanarFlow.BKMNW.runL_isMax` exists on every plane
map** with transitive rotations and faces, for all sources and sinks. -/
theorem exists_dec (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) (S T : Finset V) :
    ∃ τ : ADec M, τ.piece = univ ∧ τ.Good M S T [] ∧ τ.PGood M [] ∧ τ.LeafOK M S T [] :=
  ⟨_, chainDec_spec hM hrot hface S T⟩

end BKMNW

end PlanarFlow
