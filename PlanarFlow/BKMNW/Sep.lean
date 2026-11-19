module

public import PlanarFlow.BKMNW.Cost

/-!
# Separators and the recursive decomposition

The recursion of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J. Comput. 46(4),
2017, Algorithm 1, lines 1–5) splits a piece with a simple cycle separator (Miller), balanced
alternately with respect to the size of the piece and to the number of holes (the technique of
Klein–Subramanian and Fakcharoenphol–Rao), so that every piece touches at most a constant number
of holes (six in the article). The cycle without one edge is the simple path on which the fixing
procedure runs.

`SepOut` states what one call of the separator subroutine must return, in the terms of the
recursion (`PlanarFlow.BKMNW.ADec.Good`, `PlanarFlow.BKMNW.ADec.Bal`), and `SepSpec` that it
does so for every piece with more than `s` darts touching at most `η` holes. `ADec.build`
computes the decomposition from the subroutine, and `ADec.build_spec` proves that it covers the
piece, is good for the correctness theorem, is balanced for the cost theorem, and that its leaves
have at most `s` darts.

`SepSpec` quantifies over all pieces closed under reversal and **cannot be met in general**,
so `ADec.build_spec` is a statement about a subroutine that
does not exist for every map; it is kept as the recurrence of the article, and is not used by the
correctness theorem `PlanarFlow.BKMNW.maxflow_plane`, whose decomposition is
`PlanarFlow.BKMNW.chainDec`. The balanced decompositions needed for the cost are discussed at
`PlanarFlow.BKMNW.BalDec`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- **The output of the separator subroutine** on a piece `P` with holes `Hs`: two nonempty
disjoint pieces closed under reversal partitioning `P`, each with at most two thirds of its
darts, and a simple path of `k ≤ κ √m` darts (`2 k ≤ m`), whose vertices contain the vertices
shared by the two pieces that are not terminals, avoid the terminals and the holes, and such
that each piece touches at most `η` of the holes `Hs` and the path. -/
structure SepOut (S T : Finset V) (κ η : ℕ) (P : Finset D) (Hs : List (Finset V))
    (P₀ P₁ : Finset D) (π : SPath M) : Prop where
  union : P₀ ∪ P₁ = P
  disj : Disjoint P₀ P₁
  rev₀ : RevClosed M P₀
  rev₁ : RevClosed M P₁
  bal₀ : 3 * P₀.card ≤ 2 * P.card
  bal₁ : 3 * P₁.card ≤ 2 * P.card
  pos₀ : 0 < P₀.card
  pos₁ : 0 < P₁.card
  len : π.k ^ 2 ≤ κ ^ 2 * P.card
  len₂ : 2 * π.k ≤ P.card
  bd : bd M P₀ P₁ ⊆ S ∪ T ∪ (hunion Hs ∪ π.verts)
  avoid : Disjoint π.verts (S ∪ T ∪ hunion Hs)
  holes₀ : nTouch M P₀ (Hs ++ [π.verts]) ≤ η
  holes₁ : nTouch M P₁ (Hs ++ [π.verts]) ≤ η

/-- **The specification of the separator subroutine.** -/
def SepSpec (M : CombMap D V F) (S T : Finset V) (κ η s : ℕ)
    (sep : Finset D → List (Finset V) → Finset D × Finset D × SPath M) : Prop :=
  ∀ P Hs, RevClosed M P → s < P.card → nTouch M P Hs ≤ η →
    SepOut M S T κ η P Hs (sep P Hs).1 (sep P Hs).2.1 (sep P Hs).2.2

namespace ADec

/-- **The recursive decomposition** computed by a separator subroutine: split every piece with
more than `s` darts (as long as the split makes progress). -/
noncomputable def build (sep : Finset D → List (Finset V) → Finset D × Finset D × SPath M)
    (s : ℕ) (P : Finset D) (Hs : List (Finset V)) : ADec M :=
  if _h : s < P.card ∧ (sep P Hs).1.card < P.card ∧ (sep P Hs).2.1.card < P.card then
    node (build sep s (sep P Hs).1 (childHoles Hs (sep P Hs).2.2.toSep.path.mverts))
      (build sep s (sep P Hs).2.1 (childHoles Hs (sep P Hs).2.2.toSep.path.mverts))
      (sep P Hs).2.2.toSep
  else leaf P
termination_by P.card
decreasing_by
  · exact _h.2.1
  · exact _h.2.2

/-- **The decomposition built from a separator subroutine meeting its specification** covers the
piece, is good (for `PlanarFlow.BKMNW.arun_spec`), balanced (for `PlanarFlow.BKMNW.arunCost_le`
and `PlanarFlow.BKMNW.pieceCost_le_cube`), and its leaves have at most `s` darts. -/
theorem build_spec {S T : Finset V} {κ η s : ℕ}
    {sep : Finset D → List (Finset V) → Finset D × Finset D × SPath M}
    (hsep : SepSpec M S T κ η s sep) :
    ∀ (n : ℕ) (P : Finset D) (Hs : List (Finset V)), P.card ≤ n → RevClosed M P →
      nTouch M P Hs ≤ η →
      (build sep s P Hs).piece = P ∧ (build sep s P Hs).Good M S T Hs ∧
        (build sep s P Hs).Bal M κ η Hs ∧ (build sep s P Hs).LeafLe s := by
  intro n
  induction n with
  | zero =>
    intro P Hs hP hrev _
    rw [build]
    split_ifs with h
    · omega
    · exact ⟨rfl, hrev, trivial, by simp only [ADec.LeafLe]; omega⟩
  | succ n ih =>
    intro P Hs hP hrev hη
    by_cases hs : s < P.card
    · have hsp := hsep P Hs hrev hs hη
      have h1 : (sep P Hs).1.card < P.card := by have := hsp.bal₀; have := hsp.pos₁; omega
      have h2 : (sep P Hs).2.1.card < P.card := by have := hsp.bal₁; have := hsp.pos₀; omega
      rw [build]
      split_ifs with h
      swap
      · exact absurd ⟨hs, h1, h2⟩ h
      have hav : Disjoint (sep P Hs).2.2.verts (hunion Hs) :=
        disjoint_of_subset_right subset_union_right hsp.avoid
      have ech : childHoles Hs (sep P Hs).2.2.toSep.path.mverts =
          Hs ++ [(sep P Hs).2.2.verts] := by
        rw [SPath.toSep, SPath.toH_mverts]; exact childHoles_of_disjoint hav
      obtain ⟨e1, g1, b1, l1⟩ := ih _ (childHoles Hs (sep P Hs).2.2.toSep.path.mverts) (by omega)
        hsp.rev₀ (by rw [ech]; exact hsp.holes₀)
      obtain ⟨e2, g2, b2, l2⟩ := ih _ (childHoles Hs (sep P Hs).2.2.toSep.path.mverts) (by omega)
        hsp.rev₁ (by rw [ech]; exact hsp.holes₁)
      have hm : (sep P Hs).2.2.toSep.path.mverts = (sep P Hs).2.2.verts := SPath.toH_mverts _
      refine ⟨by simp only [piece, e1, e2, hsp.union], ⟨g1, g2, ?_, ?_, ?_,
          (sep P Hs).2.2.toSep_segOK hav⟩,
        ⟨b1, b2, ?_, ?_, ?_, ?_, ?_, ⟨by simp [SPath.toSep], fun σ hσ => ?_⟩, ?_⟩,
        ⟨l1, l2⟩⟩ <;>
        try simp only [e1, e2, hsp.union]
      · exact hsp.disj
      · rw [hm]; exact hsp.bd
      · rw [hm]; exact disjoint_of_subset_right subset_union_left hsp.avoid
      · exact hsp.disj
      · exact hsp.pos₀
      · exact hsp.pos₁
      · exact hsp.bal₀
      · exact hsp.bal₁
      · rw [List.mem_singleton.1 hσ]; exact ⟨hsp.len, hsp.len₂⟩
      · exact hη
    · rw [build]
      split_ifs with h
      · exact absurd h.1 hs
      · exact ⟨rfl, hrev, trivial, by simp only [ADec.LeafLe]; omega⟩

end ADec

end BKMNW

end PlanarFlow
