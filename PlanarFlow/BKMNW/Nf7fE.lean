module

public import PlanarFlow.BKMNW.Nf7fD

/-!
# `FixHypF'` for `fixP7`

**`Pp.fixHypF'_fixP7_of`**: given the per-address statements `FixPosW`, `FixZeroW` and
`200000 ≤ C`, the program `fixP7 msP` meets
`FixHypF' (fixP7 msP) msP Scr cost Rm wzm C C₀ (wzF7 wzm) (rF7 C C₀ Rm)` for every MSSP call program
`msP`, scratch `Scr`, step bound `cost`, room `Rm` and zero area `wzm`:
at every instance of the final assembly, `FixPSpecN'` holds with the steps `fx7fT` (exactly the
`fixRun` field of the call), the room `rO x = rOF7 C C₀ Rm #pdarts(x) Z ≤ rF7 C C₀ Rm N Z`, the
zero area `wzF7 wzm`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver MfDrv
  PlanarSeparator.StDart NcStep

/-- **`fixP7` meets `FixHypF'`** from the per-address statements (see the module docstring). -/
theorem fixHypF'_fixP7_of (hPW : FixPosW.{0}) (hZW : FixZeroW.{0}) {C C₀ : ℕ} (hC : 200000 ≤ C)
    {msP : Stmt} {Scr : ℕ → Prop} {cost Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ} :
    FixHypF' (fixP7 msP) msP Scr cost Rm wzm C C₀ (wzF7 wzm) (rF7 C C₀ Rm) := by
  intro hMS hcost hScr D V F _ _ _ _ _ _ M hM hrot hface ep hep u hu S T hST hne N en d₀ gid ν
    hN hsurj hgid hν hQ hTS L pc sc gS gH τ u' S' T' Reach c I W Z Wz hW1 hW2 hW3
  have hginj : Injective gid := by
    intro y₁ y₂ e
    obtain ⟨i₁, hi₁, rfl⟩ := hsurj y₁
    obtain ⟨i₂, hi₂, rfl⟩ := hsurj y₂
    rw [hgid i₁ hi₁, hgid i₂ hi₂] at e
    rw [e]
  have hST' : Disjoint (nlTerm M S) (nlTerm M T) := by
    rw [disjoint_left]
    intro w h1 h2
    simp only [nlTerm, mem_filter, mem_univ, true_and] at h1 h2
    exact disjoint_left.1 hST h1 h2
  have hu₁ : ∀ y : SDart (nlDarts M), 0 ≤ (fun y : SDart (nlDarts M) => u y.1) y :=
    fun y => hu y.1
  have hu' : ∀ d, 0 ≤ u' d :=
    pendCap_nonneg (triCap_nonneg hu₁) _ _ (sum_nonneg fun x _ => triCap_nonneg hu₁ x)
  have hS'T' : Disjoint S' T' :=
    (disjoint_image Sum.inr_injective).2 ((disjoint_image Sum.inl_injective).2 hST')
  have hRc := calls_closed τ [] (rotPerm L)
  have hO := NcStep.nSpecOn_machNFT gid I (NsStep.pchCall gid) Reach hginj
    (fun x _ h hpl => NsStep.pushSpec_pchCall gid x h hpl)
  refine ⟨fx7fT L (machNFT gid I (NsStep.pchCall gid)) u' S' T' C C₀,
    fun x => rOF7 C C₀ Rm (pdarts L x.1.piece x.2.1).card Z, ?_, ?_, ?_⟩
  · exact FixPSpecN''.toN' hu' hS'T' hO hRc
      (fixP7_specN'' (M := L) (gid := gid) (u := u') (S := S') (T := T') (Z := Z) (I := I) (W := W)
        (Wz := Wz) hPW hZW hC (fun x hP => by
          apply (config := { synthAssignedInstances := false }) hMS) hScr hcost (NsStep.pchCall gid) Reach)
  · intro x _
    exact rOF7_le_rF7 C C₀ Rm ((card_le_univ (pdarts L x.1.piece x.2.1)).trans hN.le) Z
  · intro l r π Hs σ h j πj _ hj
    rw [fx7fT_eq _ u' S' T' C C₀ h hj]

end Pp

end BKMNW

end PlanarFlow
