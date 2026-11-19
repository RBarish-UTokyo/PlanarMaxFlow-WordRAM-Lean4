module

public import PlanarFlow.NegSSSP.LeafExec

/-!
# `NSpecR` from the test, the split and the leaf of the machine, given a node step

The fields `test` (`nspec_testR`), `spl` (`nspec_splR`) and `leaf` (`leafS_exec`) of `NSpecR`
are proved for the machine's programs `testS`, `splitS`, `leafS Gt` on the canonical frames
(`InPR`, `Res`) with the invariant `GZ Hb Gt g.G`. **`nspecR_of_node`** assembles `NSpecR` from
any node program `nodeS` meeting the field `node` (the node step is the remaining piece), and
**`drive_msplit_node`** is the whole negative-length recursion as one run of the driver, given
the node step: the bound of `drive_msplit_mach`, the room `(#D + 1) R` above the heap top.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Frame

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Driver

variable {I : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-- **`NSpecR` from the machine's test, split and leaf, given a node step.** -/
theorem nspecR_of_node (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {ℓ : D → ℤ} {L Hb Gt : ℕ} (hGt : spWs (Fintype.card D) < Gt) (hGH : Gt + g.G ≤ Hb)
    (hℓ : ∀ x, |ℓ x| ≤ L) (hsumL : ∑ x, |ℓ x| ≤ L)
    (hWL : 8 * Fintype.card D * Fintype.card D * (L + 1) + 3 * L + 2 ≤ W)
    (hW6 : 1000000 ≤ W) {nodeS : Stmt} {ncP : Finset D → Finset D → ℕ}
    {rN : Finset D → ℕ}
    (hnode : ∀ n P d e bl el er c o₀ o₁, GZ Hb Gt g.G c → WordsBounded W c →
      c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el →
      c.nreg 3008 = el + 5 → c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e →
      e ≤ bl → bl + 5 ≤ el → el + 5 ≤ er → bl + rN P ≤ W → InPR g N ℓ L (n + 1) P d e c →
      Cnd (msplit g N) (n + 1) P →
      PotOut (pg N (msplit g N P).1 ℓ) o₀ → PotOut (pg N (msplit g N P).2 ℓ) o₁ →
      Res g N L (msplit g N P).1 o₀ (bl + 5) el c →
      Res g N L (msplit g N P).2 o₁ (el + 5) er c →
      ∃ c' t o, Exec I W nodeS c c' t ∧ t ≤ ncP (msplit g N P).1 (msplit g N P).2 ∧
        GZ Hb Gt g.G c' ∧ RegKeep c c' ∧ HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
        PotOut (pg N P ℓ) o ∧ Res g N L P o d e c') :
    NSpecR N ℓ (msplit g N) I W Hb testS (leafS Gt) splitS nodeS (GZ Hb Gt g.G)
      (InPR g N ℓ L) (Res g N L) (fun _ => 11)
      (fun P => lfCost P.card (ck N P) (verts N P).card)
      (fun P => splitSCost P.card (ck N P)) ncP (fun P => rLf P.card (ck N P))
      (fun P => rSf P.card (ck N P)) rN where
  g_stab c c' hg _ hr hm := gz_stab hGH hg hr hm
  in_stab _ _ _ _ _ _ h hm := inPR_stab h hm
  res_stab _ _ _ _ _ _ h hm := res_stab h hm
  test := nspec_testR hW6
  leaf n P d e h c hg hc r04 _ r03 b1 _ b3 hroom hin _ :=
    leafS_exec hGH hℓ hsumL hWL hg hc r04 r03 b1 b3 hroom hin
  spl := nspec_splR hM hrot hface hGt hGH
  node := hnode

/-- The room bound of the whole recursion (the leaf, the split, and `RN` for the node). -/
def roomB (nD RN : ℕ) : ℕ := 37 * nD + 9 + rSf nD nD + RN

theorem rLf_le_roomB {P : Finset D} (RN : ℕ) :
    rLf P.card (ck N P) ≤ roomB (Fintype.card D) RN := by
  have := ck_le_card (N := N) P
  have : P.card ≤ Fintype.card D := card_le_univ _
  unfold rLf roomB; omega

theorem rSf_le_roomB {P : Finset D} {RN : ℕ} {rN : Finset D → ℕ} (hRN : rN P ≤ RN) :
    rSf P.card (ck N P) + rN P ≤ roomB (Fintype.card D) RN := by
  have h1 := ck_le_card (N := N) P
  have h2 : P.card ≤ Fintype.card D := card_le_univ _
  have := spWs_mono h1
  unfold roomB rSf fsz; omega

end Frame

namespace Driver

open Finset WordRAM WordRAM.Machine BKMNW Frame

universe w

variable {I : Input} {W : ℕ}

/-- **The whole recursion for negative lengths as one natural-word run of the driver, given the
node step**: `drive_msplit_machR` with the machine's test, split and leaf (`nspecR_of_node`);
the node program `nodeS` is any program meeting the field `node` of `NSpecR` with the room
`rN ≤ RN`. Same bound `(A + B + 80) · (cMach C C₀).negsssp (#D) + B + 22`. -/
theorem drive_msplit_node (C C₀ : ℕ) {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F} (g : GIds D F)
    (hM : M.dual.IsPlane) (hrot : M.dual.RotTrans) (hface : M.dual.FaceTrans)
    {ℓ₀ : D → ℤ} (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d)
    {L Hb Gt : ℕ} (hGt : spWs (Fintype.card D) < Gt) (hGH : Gt + g.G ≤ Hb)
    (hℓ : ∀ x, |minLen M.dual ℓ₀ x| ≤ L) (hsumL : ∑ x, |minLen M.dual ℓ₀ x| ≤ L)
    (hWL : 8 * Fintype.card D * Fintype.card D * (L + 1) + 3 * L + 2 ≤ W)
    (hW6 : 1000000 ≤ W) {nodeS : Stmt} {ncP : Finset D → Finset D → ℕ}
    {rN : Finset D → ℕ} {RN : ℕ} (hRN : ∀ Q, rN Q ≤ RN)
    (hnode : ∀ n P d e bl el er c o₀ o₁, GZ Hb Gt g.G c → WordsBounded W c →
      c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el →
      c.nreg 3008 = el + 5 → c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e →
      e ≤ bl → bl + 5 ≤ el → el + 5 ≤ er → bl + rN P ≤ W →
      InPR g M.dual (minLen M.dual ℓ₀) L (n + 1) P d e c →
      Cnd (msplit g M.dual) (n + 1) P →
      PotOut (pg M.dual (msplit g M.dual P).1 (minLen M.dual ℓ₀)) o₀ →
      PotOut (pg M.dual (msplit g M.dual P).2 (minLen M.dual ℓ₀)) o₁ →
      Res g M.dual L (msplit g M.dual P).1 o₀ (bl + 5) el c →
      Res g M.dual L (msplit g M.dual P).2 o₁ (el + 5) er c →
      ∃ c' t o, Exec I W nodeS c c' t ∧ t ≤ ncP (msplit g M.dual P).1 (msplit g M.dual P).2 ∧
        GZ Hb Gt g.G c' ∧ RegKeep c c' ∧ HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
        PotOut (pg M.dual P (minLen M.dual ℓ₀)) o ∧ Res g M.dual L P o d e c')
    (hHb : 0 < Hb) {A B : ℕ}
    (hl : ∀ P : Finset D, P.card ≤ 1000000 →
      11 + lfCost P.card (ck M.dual P) (verts M.dual P).card ≤
        A * (cNegMach C).leaf P.card + B)
    (hn : ∀ P₀ P₁ : Finset D, SplitF M.dual (P₀ ∪ P₁) P₀ P₁ →
      11 + splitSCost (P₀ ∪ P₁).card (ck M.dual (P₀ ∪ P₁)) + ncP P₀ P₁ ≤
        A * (cNegMach C).node (P₀ ∪ P₁).card (bdry M.dual P₀ P₁).card P₀.card
          (verts M.dual P₀).card P₁.card (verts M.dual P₁).card + B)
    {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : GZ Hb Gt g.G c)
    (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb)
    (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0)
    (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hroom : h + (Fintype.card D + 1) * roomB (Fintype.card D) RN ≤ W)
    (hin : InPR g M.dual (minLen M.dual ℓ₀) L (Fintype.card D) (reps M.dual) (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS (leafS Gt) splitS nodeS) c c' t ∧
      t ≤ (A + B + 80) * (cMach C C₀).negsssp (Fintype.card D) + B + 22 ∧
      PotOut (M.dual.graph ℓ₀) o ∧ Res g M.dual L (reps M.dual) o (Hb + 5) e c' ∧
      GZ Hb Gt g.G c' ∧ c'.output = c.output :=
  drive_msplit_machR C C₀ g hM hrot hface hneg
    (fun Q => rLf_le_roomB (N := M.dual) (P := Q) RN)
    (fun Q => rSf_le_roomB (N := M.dual) (P := Q) (hRN Q))
    (nspecR_of_node hM hrot hface hGt hGH hℓ hsumL hWL hW6 hnode) hHb hl hn c hc hg r0 r1 r2 r3
    m0 m1 m2 he hh hroom hin

end Driver

end NegSSSP

end PlanarFlow
