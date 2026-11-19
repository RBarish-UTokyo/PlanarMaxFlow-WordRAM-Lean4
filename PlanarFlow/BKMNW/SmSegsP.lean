module

public import PlanarFlow.BKMNW.SmSem

/-!
# The parts of the separator of a node of `smD`

**`smD_node_segs`**: at a node `.node l r π` of the small decomposition `smD M pk S T P Hs`, the
parts `π.segs` are determined by the path's darts (none, or `{x, rev x}` for a dart `x` of the
piece map) and whether a hole meets the path:
* no darts, a hole met: `segs = []` (`holeSep`);
* darts `{x, rev x}`, a hole met: `segs = [point]` (`peelSep`, a part without darts);
* no darts, no hole met: `segs = [point]` (a pendant edge at a terminal);
* darts `{x, rev x}`, no hole met: `segs = [ofDart x]` with `x = pk (smB …)` and
  `rev x ∈ smB …` (so `x` is the one of the two of least `gid` under `PkMin`).
This is what the program writing `SegsOut` for `sepSm` reads off the outputs of `sepSm`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The parts of the separator of a node of `smD`** (see the module docstring). -/
theorem smD_node_segs {pk : Finset D → D} {S T : Finset V}
    (hpk : ∀ X : Finset D, X.Nonempty → pk X ∈ X) {P : Finset D} {Hs : List (Finset V)}
    (hrc : RevClosed M P) {l r : ADec M} {π : HSep M}
    (h : smD M pk S T P Hs = .node l r π) :
    (π.segs = [] ∧ π.path.darts.toFinset = ∅ ∧ ∃ H ∈ Hs, ¬ Disjoint H π.path.mverts) ∨
    ((∃ x ∈ pdarts M P Hs, π.path.darts.toFinset = {x, M.rev x}) ∧
      (∃ H ∈ Hs, ¬ Disjoint H π.path.mverts) ∧ ∃ y v, π.segs = [SPath.point y v]) ∨
    (π.path.darts.toFinset = ∅ ∧ (∀ H ∈ Hs, Disjoint H π.path.mverts) ∧
      ∃ y v, π.segs = [SPath.point y v]) ∨
    ((∀ H ∈ Hs, Disjoint H π.path.mverts) ∧ ∃ x, ∃ hx : M.head x ≠ M.tail x,
      x = pk (smB M S T P Hs) ∧ M.rev x ∈ smB M S T P Hs ∧ x ∈ pdarts M P Hs ∧
      π.path.darts.toFinset = {x, M.rev x} ∧ π.segs = [SPath.ofDart x hx]) := by
  rw [smD] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 h8 h9
  -- the peel: `peelSep x`
  · injection h with _ _ eπ
    subst eπ
    obtain ⟨hxP, hxt, hxh⟩ := mem_filter.1 (hpk _ h2)
    obtain ⟨H, hH, hxH⟩ := mem_hunion.1 hxh
    refine Or.inr (Or.inl ⟨⟨_, hxP, sm_darts_pair _ h3⟩, ⟨H, hH, ?_⟩, _, _, rfl⟩)
    show ¬ Disjoint H (SPath.ofDart _ h3).toH.mverts
    rw [HPath.toH_ofDart_mverts]
    exact not_disjoint_iff.2 ⟨_, hxH, mem_insert_of_mem (mem_singleton_self _)⟩
  -- the dump: `holeSep y`
  · injection h with _ _ eπ
    subst eπ
    have hy := mem_filter.1 (hpk _ h5)
    obtain ⟨H, hH, hyH⟩ := mem_hunion.1 hy.2
    refine Or.inl ⟨rfl, sm_darts_point _ _, H, hH, ?_⟩
    show ¬ Disjoint H (SPath.point (M' := M) _ _).toH.mverts
    rw [HPath.toH_point_mverts]
    exact not_disjoint_iff.2 ⟨_, hyH, mem_singleton_self _⟩
  -- the pendant edge at a terminal
  · injection h with _ _ eπ
    subst eπ
    have hB : (smB M S T P Hs).Nonempty := by
      push Not at h1; obtain ⟨-, d, hd, hb⟩ := h1; exact ⟨d, mem_filter.2 ⟨hd, hb⟩⟩
    obtain ⟨-, hyt⟩ := mem_filter.1 (hpk _ hB)
    refine Or.inr (Or.inr (Or.inl ⟨sm_darts_point _ _, fun H hH => ?_, _, _, rfl⟩))
    show Disjoint H (SPath.point (M' := M) _ _).toH.mverts
    rw [HPath.toH_point_mverts, disjoint_singleton_right]
    exact fun hm => hyt (mem_union_right _ (mem_hunion.2 ⟨H, hH, hm⟩))
  -- the edge
  · injection h with _ _ eπ
    subst eπ
    have hB : (smB M S T P Hs).Nonempty := by
      push Not at h1; obtain ⟨-, d, hd, hb⟩ := h1; exact ⟨d, mem_filter.2 ⟨hd, hb⟩⟩
    set x := pk (smB M S T P Hs) with hxd
    obtain ⟨hxP, hxt⟩ := mem_filter.1 (hpk _ hB)
    have hxh : M.head x ∉ hunion Hs := fun hm => h2 ⟨x, mem_filter.2 ⟨hxP, hxt, hm⟩⟩
    have hrx : M.rev x ∈ smB M S T P Hs := by
      refine mem_filter.2 ⟨stable_pdarts hrc Hs _ hxP, ?_⟩
      rw [CombMap.tail_rev]
      intro hm
      rcases mem_union.1 hm with hm | hm
      · exact h8 hm
      · exact hxh hm
    refine Or.inr (Or.inr (Or.inr ⟨fun H hH => ?_, x, h9, rfl, hrx, hxP, sm_darts_pair _ h9,
      rfl⟩))
    show Disjoint H (SPath.ofDart _ h9).toH.mverts
    rw [HPath.toH_ofDart_mverts]
    refine disjoint_left.2 fun v hvH hv => ?_
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hxt (mem_union_right _ (mem_hunion.2 ⟨H, hH, hvH⟩))
    · exact hxh (mem_hunion.2 ⟨H, hH, hvH⟩)

end BKMNW

end PlanarFlow
