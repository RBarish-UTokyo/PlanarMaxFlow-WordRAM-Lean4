module

public import PlanarFlow.BKMNW.NcChs

/-!
# No family of s-t flow choices exists on all calls

`SubSpecS`, `SubSpecS'` choose `chs : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1
x.2.2) → StChoice (pmap h)`, and `mfMain_cMachSGEG` takes a fallback `fb` of the same type.
**That type is empty**: the empty piece `(.leaf ∅, [], 1)` satisfies `PieceInv` (every condition
is about the darts of the piece), its piece map has no face, and a `StChoice` holds dual trees,
each with a root face. So the existential of `SubSpecS'` is never met, and the fallback cannot be
supplied.

* `pieceInv_empty`: `PieceInv M ∅ Hs σ`;
* **`chs_isEmpty`**: `IsEmpty ((x : MCall M) → (h : PieceInv …) → StChoice (pmap h))`.

The fix (used by `ThSpecR.lean`): a family of node subroutines that exists.

* **`NcStep.stFlowT gid I x h`**: the s-t flow of `stChoiceOf` (the `gid`-order of the call, the
  input `I`) where a `gid`-order and a dual tree exist (as `stChsG`), else the zero flow;
* **`NcStep.machNFT gid I pch`** (`= machNF gid I chs pch` with `(chs x h).flow` replaced by
  `stFlowT gid I x h`);
* **`NcStep.stFlowT_eq`**: at a plane piece map with transitive rotations and `gid` injective on
  its darts, `stFlowT gid I x h` is the flow of the valid choice `stChoiceOf …` (so the machine's
  s-t flow call `stCallZ_lay`, which writes the flow of `stChoiceOf` at a frame, computes it);
  **`NcStep.nSpecOn_machNFT`** (`NSpecOn` from `Injective gid` and `PushSpec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset Function Equiv CombMap MfDrv Orbit

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The empty piece is a piece. -/
lemma pieceInv_empty (Hs : List (Finset V)) (σ : Perm D) : PieceInv M ∅ Hs σ := by
  have he : pdarts M ∅ Hs = ∅ := by
    ext d; simp [mem_pdarts]
  refine ⟨fun _ h => by simp at h, ?_, ?_, ?_⟩
  · rw [he]; intro x hx; simp at hx
  · rw [he]; simp [gap, eul, Orbit.comp, nOrb]
  · rw [he]; intro x hx; simp at hx

/-- **No family of s-t flow choices on all calls exists**: at the empty piece the piece map has
no face, so it has no dual tree. -/
theorem chs_isEmpty :
    IsEmpty ((x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → STFlow.StChoice (pmap h)) := by
  refine ⟨fun f => ?_⟩
  have h : PieceInv M (ADec.leaf (M := M) ∅).piece ([] : List (Finset V)) 1 := pieceInv_empty [] 1
  have ch := f (.leaf ∅, [], 1) h
  have r := (ch.tree 0 ∅ ∅).root
  induction r using Quotient.inductionOn with
  | h y => exact absurd y.2 (by simp [ADec.piece, mem_pdarts])

end NsStep

namespace NcStep

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine STFlow NsStep MfDrv StCall

universe w'

variable {D V F : Type w'} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

open Classical in
/-- **The s-t flow of the machine at a call**: the flow of the choices `stChoiceOf` of the
`gid`-order of the call where it and a dual tree exist (as `stChsG`), else zero. -/
noncomputable def stFlowT (gid : D → ℕ) (I : Input) (x : MCall M)
    (h : PieceInv M x.1.piece x.2.1 x.2.2) :
    (SDart (pdarts M x.1.piece x.2.1) → ℤ) → Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1)) →
      Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1)) → SDart (pdarts M x.1.piece x.2.1) → ℤ :=
  if hx : ∃ en, GOrd gid x h en then
    if hT : Nonempty (STFlow.DTree (pmap h)) then
      (@stChoiceOf _ _ _ _ _ _ _ _ _ (pmap h) hx.choose _ hx.choose_spec.enum I hT).flow
    else fun _ _ _ _ => 0
  else fun _ _ _ _ => 0

/-- **The node subroutines of the machine at every call** (`machNF` with the s-t flow
`stFlowT`; unlike `machNF … chs …`, this family exists). -/
noncomputable def machNFT (gid : D → ℕ) (I : Input)
    (pch : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      PushFn (Orbit.SDart (pdarts M x.1.piece x.2.1)) (Orbit.SVert x.2.2 (pdarts M x.1.piece x.2.1))) :
    NFam M :=
  fun x h => implG (pmap h) (pch x h) (Klein.msspPlaneK (pmap h)) (frRef _) (negLay gid I x h)
    (stFlowT gid I x h)

/-- **At a plane piece map with transitive rotations** (`gid` injective on its darts),
`stFlowT` is the flow of the valid choice `stChoiceOf` of the `gid`-order of the call. -/
theorem stFlowT_eq (gid : D → ℕ) (I : Input) (x : MCall M) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    (hpl : (pmap h).IsPlane) (hrot : (pmap h).RotTrans)
    (hinj : ∀ a ∈ pdarts M x.1.piece x.2.1, ∀ b ∈ pdarts M x.1.piece x.2.1, gid a = gid b → a = b) :
    ∃ (hx : ∃ en, GOrd gid x h en) (hT : Nonempty (STFlow.DTree (pmap h))),
      stFlowT gid I x h =
        (@stChoiceOf _ _ _ _ _ _ _ _ _ (pmap h) hx.choose _ hx.choose_spec.enum I hT).flow ∧
      (@stChoiceOf _ _ _ _ _ _ _ _ _ (pmap h) hx.choose _ hx.choose_spec.enum I hT).OK := by
  have hpos := pmap_card_pos h hpl
  have hx := gOrd_exists gid x h hinj hpos
  have hT := dtree_nonempty hpl hrot hx.choose_spec.enum hpos (pmap_tail_surj h)
  refine ⟨hx, hT, ?_, ?_⟩
  · unfold stFlowT
    simp only [hx, hT, ↓reduceDIte]
  · exact stChoiceOf_OK hpl hx.choose_spec.enum
      (enumOK_dual hx.choose_spec.enum hrot (pmap_tail_surj h)) hpos I

/-- **`machNFT` meets `NSpecOn`** (`Injective gid`, the push-back meeting `PushSpec`). -/
theorem nSpecOn_machNFT (gid : D → ℕ) (I : Input)
    (pch : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      PushFn (Orbit.SDart (pdarts M x.1.piece x.2.1)) (Orbit.SVert x.2.2 (pdarts M x.1.piece x.2.1)))
    (Reach : MCall M → Prop) (hgid : Injective gid)
    (hpush : ∀ x, Reach x → ∀ h, (pmap h).IsPlane → PushSpec (pmap h) (pch x h)) :
    NSpecOn M (machNFT gid I pch) Reach := by
  intro x hx h hpl hrot hface u hu
  obtain ⟨_, _, e, hok⟩ := stFlowT_eq gid I x h hpl hrot fun a _ b _ e => hgid e
  change (implG (pmap h) (pch x h) (Klein.msspPlaneK (pmap h)) (frRef _) (negLay gid I x h)
    (stFlowT gid I x h)).Spec u
  rw [e]
  exact implG_spec hpl hu (hpush x hx h hpl) (Klein.msspPlaneK_spec hpl hrot hface) (frRef_spec _)
    (negLay_spec _ _ _ _) (STFlow.StChoice.spec hpl hok)

end NcStep

end BKMNW

end PlanarFlow
