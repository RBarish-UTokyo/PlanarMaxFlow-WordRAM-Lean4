module

public import PlanarFlow.BKMNW.LrV
public import PlanarFlow.BKMNW.DecGuard

/-!
# The tags of the large split: a large child is a node (pure)

**`guard_kid_ntag`**: at a node `.node lt rt π` of the guarded decomposition
`decS (guardS gSz spS) (guardS gHl spH) sm chS s P Hs σ b` of a large piece (`s < #P`), a large
child (`s < #X`) has the tag `1` (`decS_node_guard`, `decS_node_guard_kids`,
`decS_guard_isNode`). This discharges the hypotheses `hlargeL`, `hlargeR` of `lrecT_rec` for the
headline's decomposition; `dec_flag_eq` (the flag `decide (1 - [holeStep] = 1) = !holeStep`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset MfDrv

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F} {St : Type*}

/-- **A large child of a node of the guarded decomposition is a node.** -/
theorem guard_kid_ntag {S T : Finset V} {κ s : ℕ}
    {Inv : Finset D → List (Finset V) → St → Prop}
    {spS spH : Finset D → List (Finset V) → St → SplitAns M}
    {sm : Finset D → List (Finset V) → ADec M}
    {chS : Finset D → List (Finset V) → St → HSep M → Finset D → St}
    (hF : SplitFnsS M S T κ s Inv spS spH sm chS)
    (hsm : ∀ P Hs, RevClosed M P → (sm P Hs).piece = P) {P : Finset D} {Hs : List (Finset V)}
    {σ : St} {b : Bool} (hs : s < P.card) {lt rt : ADec M} {π : HSep M}
    (h : decS M (guardS M (gSz M S T s Inv) spS) (guardS M (gHl M S T s Inv) spH) sm chS s P Hs
      σ b = .node lt rt π) :
    (s < lt.piece.card → ntag lt = 1) ∧ (s < rt.piece.card → ntag rt = 1) := by
  obtain ⟨-, -, -, -, -, -, el, er, -, -⟩ := decS_node_guard hF hsm hs h
  have kids := decS_node_guard_kids hF hsm hs h
  obtain ⟨pl, il, tl⟩ := kids lt.piece (by simp)
  obtain ⟨pr, ir, tr⟩ := kids rt.piece (by simp)
  refine ⟨fun hl => ?_, fun hr => ?_⟩
  · obtain ⟨a, b', c', e⟩ := decS_guard_isNode hF pl il hl tl
    rw [el, e]; rfl
  · obtain ⟨a, b', c', e⟩ := decS_guard_isNode hF pr ir hr tr
    rw [er, e]; rfl

/-- The flag of the children's records: `1 - [holeStep]` read as a Boolean is `!holeStep`. -/
lemma dec_flag_eq (b : Bool) : decide (1 - (if b = true then 1 else 0) = 1) = !b := by
  cases b <;> rfl

end BKMNW

end PlanarFlow
