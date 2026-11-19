module

public import PlanarFlow.NegSSSP.NdFullCost

/-!
# The whole negative-length recursion on the machine, unconditionally

**`Driver.drive_negsssp_machine`**: the whole negative-length recursion (Bellman–Ford–Klein–
Mozes–Nussbaum–Wulff-Nilsen at every node, the leaf solver at the leaves) as **one natural-word
run of one fixed program** `driver testS (leafS Gt) splitS0 (nodeS Gt (Fs (WNb #D L) Gt))`
within **`(10¹² + 1 + fsKC + 80) · (cMach C C₀).negsssp (#D) + fsKC + 22`** steps, i.e.
`O(n log² n)` (`cMach.negsssp n = 10920 · negK C · n · lg² n + 1000001 · negK C · n`), with a
polynomial word size: `W ≥ 4 WNb (#D) L + 3L + 2`, `W ≥ 8 (#D)² (L + 1) + 3L + 2`, the heap
room `h + (#D + 1) · roomB (#D) (66 #D + 31 + fsRF (#D)) ≤ W`, and `Hb > WNb (#D) L`,
`Hb ≥ 2 spWs (#D) + 2` (all polynomial in `#D` and `L`). No hypothesis on the full branch is
left: `hF` is `Frame.fs_full`, `hncF` is `fsCost_le` + `fsNcF_node`.

The program's constants `Gt`, `WNb (#D) L` depend on the instance's size and length bound (as
`Gt` did already).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW

/-- The uniform room bound of the full branch. -/
def fsRF (n : ℕ) : ℕ := 10 + (6 + 5 * n + 5 * n) + (6 + 5 * n + 5 * n) + fsRoomB n n (2 * n) (2 * n)

namespace Driver

open Finset WordRAM WordRAM.Machine BKMNW Frame

universe w

variable {I : Input} {W : ℕ}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **The whole negative-length recursion, unconditionally** (see the module docstring). -/
theorem drive_negsssp_machine (C C₀ : ℕ) (hC : 200000 ≤ C) {D V F : Type w} [Fintype D]
    [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    {M : CombMap D V F} (g : GIds D F) (hM : M.dual.IsPlane) (hrot : M.dual.RotTrans)
    (hface : M.dual.FaceTrans)
    {ℓ₀ : D → ℤ} (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d)
    {L Hb Gt : ℕ} (hGt : spWs (Fintype.card D) < Gt) (hGH : Gt + g.G ≤ Hb)
    (hHb2 : 2 * spWs (Fintype.card D) + 2 ≤ Hb) (hWNH : WNb (Fintype.card D) L < Hb)
    (hℓ : ∀ x, |minLen M.dual ℓ₀ x| ≤ L) (hsumL : ∑ x, |minLen M.dual ℓ₀ x| ≤ L)
    (hWL : 8 * Fintype.card D * Fintype.card D * (L + 1) + 3 * L + 2 ≤ W)
    (hWL7 : 7 * L + 2 ≤ W) (hW6 : 1000000 ≤ W)
    (hW4 : 4 * WNb (Fintype.card D) L + 3 * L + 2 ≤ W)
    {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : GZ0 Hb c)
    (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h)
    (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0)
    (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hroom : h + (Fintype.card D + 1) *
      roomB (Fintype.card D) (66 * Fintype.card D + 31 + fsRF (Fintype.card D)) ≤ W)
    (hin : InPR g M.dual (minLen M.dual ℓ₀) L (Fintype.card D) (reps M.dual) (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS (leafS Gt) splitS0
        (nodeS Gt (Fs (WNb (Fintype.card D) L) Gt))) c c' t ∧
      t ≤ (10 ^ 12 + 1 + fsKC + 80) * (cMach C C₀).negsssp (Fintype.card D) + fsKC + 22 ∧
      PotOut (M.dual.graph ℓ₀) o ∧ Res g M.dual L (reps M.dual) o (Hb + 5) e c' ∧
      GZ0 Hb c' ∧ c'.output = c.output := by
  classical
  have hKC : 400 ≤ fsKC := by unfold fsKC; omega
  refine drive_msplit_nodeS_cost (I := I) C C₀ hC g hM hrot hface hneg hGt hGH hℓ hsumL hWL hWL7
    hW6 (ncF := fun P₀ P₁ => fsNcF (P₀ ∪ P₁).card (bdry M.dual P₀ P₁).card)
    (rF := fun P => 10 + fsz (msplit g M.dual P).1.card (ck M.dual (msplit g M.dual P).1) +
      fsz (msplit g M.dual P).2.card (ck M.dual (msplit g M.dual P).2) +
      fsRoomB P.card (ck M.dual P) (verts M.dual P).card
        (bdry M.dual (msplit g M.dual P).1 (msplit g M.dual P).2).card)
    (RF := fsRF (Fintype.card D)) ?_ ?_ (by omega) (A := 10 ^ 12) (B := fsKC) (by norm_num) hKC
    (fun P₀ P₁ _ => fsNcF_node hC _ _ _ _ _ _) c hc hg r0 r1 r2 r3 m0 m1 m2 he hh hroom hin
  · -- the uniform room bound
    intro Q
    generalize hn : Fintype.card D = n
    have h0 : (msplit g M.dual Q).1.card ≤ n := hn ▸ card_le_univ _
    have h1 : (msplit g M.dual Q).2.card ≤ n := hn ▸ card_le_univ _
    have k0 : ck M.dual (msplit g M.dual Q).1 ≤ n := hn ▸ ck_le_card _
    have k1 : ck M.dual (msplit g M.dual Q).2 ≤ n := hn ▸ ck_le_card _
    have hQ : Q.card ≤ n := hn ▸ card_le_univ _
    have hkQ : ck M.dual Q ≤ n := hn ▸ ck_le_card _
    have hvQ : (verts M.dual Q).card ≤ 2 * n := by
      have := NTree.card_verts_le (N := M.dual) Q; omega
    have hbQ : (bdry M.dual (msplit g M.dual Q).1 (msplit g M.dual Q).2).card ≤ 2 * n := by
      have h2 : (bdry M.dual (msplit g M.dual Q).1 (msplit g M.dual Q).2).card ≤
          (verts M.dual (msplit g M.dual Q).1).card :=
        card_le_card fun x hx => (Finset.mem_inter.1 hx).1
      have := NTree.card_verts_le (N := M.dual) (msplit g M.dual Q).1; omega
    have := fsRoomB_mono hQ hkQ hvQ hbQ
    unfold fsRF fsz
    omega
  · -- the full branch
    refine fs_full (I := I) hM hrot hface C hHb2 hGH hWNH hℓ hsumL hW4 hW6
      (ncF := fun P₀ P₁ => fsNcF (P₀ ∪ P₁).card (bdry M.dual P₀ P₁).card)
      (rF := fun P => 10 + fsz (msplit g M.dual P).1.card (ck M.dual (msplit g M.dual P).1) +
        fsz (msplit g M.dual P).2.card (ck M.dual (msplit g M.dual P).2) +
        fsRoomB P.card (ck M.dual P) (verts M.dual P).card
          (bdry M.dual (msplit g M.dual P).1 (msplit g M.dual P).2).card) ?_ ?_ ?_
    · intro P m' nV nF Ck p₀ p₁ henv
      have := fsCost_le C henv
      show _ ≤ fsNcF ((msplit g M.dual P).1 ∪ (msplit g M.dual P).2).card _
      rw [msplit_union]; exact this
    · intro P m' nV nF Ck p₀ p₁ henv
      have := fsRoom_le C henv
      show _ ≤ 10 + _ + _ + _
      omega
    · intro P
      show _ ≤ 10 + _ + _ + fsRoomB _ _ _ _
      unfold fsRoomB
      omega

end Driver

end NegSSSP

end PlanarFlow
