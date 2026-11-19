module

public import PlanarFlow.NegSSSP.NdStep

/-!
# The whole recursion with the machine's node step, given its full branch

**`Driver.drive_msplit_nodeS`**: the negative-length recursion as one natural-word run of
`driver testS (leafS Gt) splitS0 (nodeS Gt Fs)` with the invariant `GZ0` (`drive_msplit_node0`
with `hnode := nodeS_exec`): every field of `NSpecR` is a theorem except the full branch `Fs`
of the node step in its own case (both children with an outcome and a shared vertex), the
hypothesis `hF`. The total bound is that of `drive_msplit_mach`,
`(A + B + 80) · (cMach C C₀).negsssp (#D) + B + 22`, for constants `A`, `B` meeting `hl`, `hn`
with the node cost `ndCost m k w + ncF P₀ P₁`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Driver

open Finset WordRAM WordRAM.Machine BKMNW Frame

universe w

variable {I : Input} {W : ℕ}

/-- **The recursion with the machine's node step, given its full branch.** -/
theorem drive_msplit_nodeS (C C₀ : ℕ) {D V F : Type w} [Fintype D] [DecidableEq D]
    [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F}
    (g : GIds D F) (hM : M.dual.IsPlane) (hrot : M.dual.RotTrans) (hface : M.dual.FaceTrans)
    {ℓ₀ : D → ℤ} (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d)
    {L Hb Gt : ℕ} (hGt : spWs (Fintype.card D) < Gt) (hGH : Gt + g.G ≤ Hb)
    (hℓ : ∀ x, |minLen M.dual ℓ₀ x| ≤ L) (hsumL : ∑ x, |minLen M.dual ℓ₀ x| ≤ L)
    (hWL : 8 * Fintype.card D * Fintype.card D * (L + 1) + 3 * L + 2 ≤ W)
    (hWL7 : 7 * L + 2 ≤ W) (hW6 : 1000000 ≤ W) {Fs : Stmt}
    {ncF : Finset D → Finset D → ℕ} {rF : Finset D → ℕ} {RF : ℕ} (hRF : ∀ Q, rF Q ≤ RF)
    (hF : ∀ n P d e bl el er c f₀ f₁, GZ0 Hb c → WordsBounded W c →
      c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el →
      c.nreg 3008 = el + 5 → c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e →
      e ≤ bl → bl + 5 ≤ el → el + 5 ≤ er → bl + rF P ≤ W →
      InPR g M.dual (minLen M.dual ℓ₀) L (n + 1) P d e c →
      Cnd (msplit g M.dual) (n + 1) P →
      PotOut (pg M.dual (msplit g M.dual P).1 (minLen M.dual ℓ₀)) (some f₀) →
      PotOut (pg M.dual (msplit g M.dual P).2 (minLen M.dual ℓ₀)) (some f₁) →
      Res g M.dual L (msplit g M.dual P).1 (some f₀) (bl + 5) el c →
      Res g M.dual L (msplit g M.dual P).2 (some f₁) (el + 5) er c →
      (bdry M.dual (msplit g M.dual P).1 (msplit g M.dual P).2).Nonempty →
      ∃ c' t o, Exec I W Fs c c' t ∧ t ≤ ncF (msplit g M.dual P).1 (msplit g M.dual P).2 ∧
        GZ0 Hb c' ∧ RegKeep c c' ∧ HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
        PotOut (pg M.dual P (minLen M.dual ℓ₀)) o ∧ Res g M.dual L P o d e c')
    (hHb : 0 < Hb) {A B : ℕ}
    (hl : ∀ P : Finset D, P.card ≤ 1000000 →
      11 + lfCost P.card (ck M.dual P) (verts M.dual P).card ≤
        A * (cNegMach C).leaf P.card + B)
    (hn : ∀ P₀ P₁ : Finset D, SplitF M.dual (P₀ ∪ P₁) P₀ P₁ →
      11 + (splitSCost (P₀ ∪ P₁).card (ck M.dual (P₀ ∪ P₁)) + wsCost (ck M.dual (P₀ ∪ P₁))) +
        (ndCost (P₀ ∪ P₁).card (ck M.dual (P₀ ∪ P₁)) (verts M.dual (P₀ ∪ P₁)).card +
          ncF P₀ P₁) ≤
        A * (cNegMach C).node (P₀ ∪ P₁).card (bdry M.dual P₀ P₁).card P₀.card
          (verts M.dual P₀).card P₁.card (verts M.dual P₁).card + B)
    {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : GZ0 Hb c)
    (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h)
    (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0)
    (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hroom : h + (Fintype.card D + 1) *
      roomB (Fintype.card D) (66 * Fintype.card D + 31 + RF) ≤ W)
    (hin : InPR g M.dual (minLen M.dual ℓ₀) L (Fintype.card D) (reps M.dual) (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS (leafS Gt) splitS0 (nodeS Gt Fs)) c c' t ∧
      t ≤ (A + B + 80) * (cMach C C₀).negsssp (Fintype.card D) + B + 22 ∧
      PotOut (M.dual.graph ℓ₀) o ∧ Res g M.dual L (reps M.dual) o (Hb + 5) e c' ∧
      GZ0 Hb c' ∧ c'.output = c.output := by
  refine drive_msplit_node0 C C₀ g hM hrot hface hneg hGt hGH hℓ hsumL hWL hW6
    (ncP := fun P₀ P₁ => ndCost (P₀ ∪ P₁).card (ck M.dual (P₀ ∪ P₁))
      (verts M.dual (P₀ ∪ P₁)).card + ncF P₀ P₁)
    (rN := fun P => rNd P.card (ck M.dual P) + rF P) (RN := 66 * Fintype.card D + 31 + RF)
    (fun Q => ?_) (nodeS_exec hM hrot hface (by omega) hGH hℓ hsumL hWL7 hW6 hF) hHb hl hn c
    hc hg r0 r1 r2 r3 m0 m1 m2 he hh hroom hin
  have h1 : Q.card ≤ Fintype.card D := card_le_univ _
  have h2 : ck M.dual Q ≤ Fintype.card D := ck_le_card Q
  have := hRF Q
  show rNd Q.card (ck M.dual Q) + rF Q ≤ _
  unfold rNd; omega

end Driver

end NegSSSP

end PlanarFlow
