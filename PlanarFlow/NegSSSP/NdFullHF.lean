module

public import PlanarFlow.NegSSSP.NdFullSides

/-!
# The full branch of the node step: `hF`

**`Fs WN Gt`** `= (ndFront ; ndB Gt ; spStage) ; fbA ; fbMid ; fbTail WN` (the full branch, with
`fbMid = (fbJ ; fbK ; fbC1 ; mdProg) ; fbC2`), and **`Frame.fs_full`**: `Fs (WNb #D L) Gt` meets
the hypothesis `hF` of `nodeS_exec` / `drive_msplit_nodeS_cost`, with the cost `ncF` and the room
`rF` of any functions dominating the closed cost `fsCost` and room `fsRoom` on the parameter
envelope `FsEnv` (`hncF`, `hrF`); the global word bounds: `WNb #D L < Hb`,
`2 spWs #D + 2 ≤ Hb`, `4 WNb #D L + 3L + 2 ≤ W`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  PlanarSeparator.MillerProg

/-- **The full branch of the node step.** -/
def Fs (WN Gt : ℕ) : Stmt :=
  .seq (.seq Frame.ndFront (.seq (Frame.ndB Gt) Frame.spStage)) (.seq fbA (.seq fbMid (fbTail WN)))

/-- **The step count of the full branch** from its parameters. -/
def fsCost (C m k w b m' nV nF Ck : ℕ) (p₀ p₁ : FeP) : ℕ :=
  Frame.fsP1Cost m k + ((fbPreCost k + 2 * (33 * m + 405 * m' + 13 * (nV + nF) + 22 * Ck + 155)) +
    (fsMidCost k w p₀ p₁ + fsNodeCost (ndRunCost C m m w b Ck Ck p₀ p₁) p₁.END
      (fbZ (Frame.spB0 k) k m w b p₀ p₁) (m + w + 1) m w))

/-- **The room of the full branch** above the heap top from its parameters. -/
def fsRoom (C m k w b Ck : ℕ) (p₀ p₁ : FeP) : ℕ :=
  200 * k + Frame.spWs k + ndRunCost C m m w b Ck Ck p₀ p₁ + 5 * (m + w) + 8 * (w + 1) + 1

/-- **The parameter envelope** of the full branch (`m` darts, `k = ck`, `w` vertices, `b`
boundary vertices; `m'`, `nV`, `nF` the sizes of the large component's map, `Ck` the length of
the separating cycle, `p₀`, `p₁` the two instances). -/
structure FsEnv (m k w b m' nV nF Ck : ℕ) (p₀ p₁ : FeP) : Prop where
  hbig : 1000000 < m
  hmlek : m ≤ k
  hk2 : k ≤ 2 * m
  hw2 : w ≤ 2 * m
  hbw : b ≤ w
  hm' : m' ≤ k
  hVF : nV + nF ≤ 2 * k
  hCk : Ck ≤ k
  hCk2 : Ck ^ 2 ≤ 1200 * m
  hk₀ : p₀.k = Ck
  hk₁ : p₁.k = Ck
  hnD₀ : p₀.nD ≤ 3 * m'
  hnD₁ : p₁.nD ≤ 3 * m'
  hnV₀ : p₀.nV ≤ p₀.nD
  hnV₁ : p₁.nV ≤ p₁.nD
  hnF₀ : p₀.nF ≤ p₀.nD
  hnF₁ : p₁.nF ≤ p₁.nD
  hfe₀ : feCostDk p₀ ≤ (3114 * m + 13) * (Nat.log 2 m + 8) + 444800 * m + 1384
  hfe₁ : feCostDk p₁ ≤ (3114 * m + 13) * (Nat.log 2 m + 8) + 444800 * m + 1384
  hI0₀ : p₀.I0 = fbY (Frame.spB0 k) k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + 2 * w
  hI0₁ : p₁.I0 = p₀.END

namespace Frame

open Driver

universe u v w

variable {I : Input} {W : ℕ}

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
open Classical in
/-- **The full branch meets `hF`** (see the module docstring). -/
theorem fs_full (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) {ℓ : D → ℤ}
    {L Hb Gt : ℕ} (C : ℕ) (hHb2 : 2 * spWs (Fintype.card D) + 2 ≤ Hb) (hGH : Gt + g.G ≤ Hb)
    (hWNH : WNb (Fintype.card D) L < Hb)
    (hℓ : ∀ x, |ℓ x| ≤ L) (hsumL : ∑ x, |ℓ x| ≤ L)
    (hW4 : 4 * WNb (Fintype.card D) L + 3 * L + 2 ≤ W) (hW6 : 1000000 ≤ W)
    {ncF : Finset D → Finset D → ℕ} {rF : Finset D → ℕ}
    (hncF : ∀ (P : Finset D) (m' nV nF Ck : ℕ) (p₀ p₁ : FeP),
      FsEnv P.card (ck N P) (verts N P).card (bdry N (msplit g N P).1 (msplit g N P).2).card
        m' nV nF Ck p₀ p₁ →
      fsCost C P.card (ck N P) (verts N P).card (bdry N (msplit g N P).1 (msplit g N P).2).card
        m' nV nF Ck p₀ p₁ ≤ ncF (msplit g N P).1 (msplit g N P).2)
    (hrF : ∀ (P : Finset D) (m' nV nF Ck : ℕ) (p₀ p₁ : FeP),
      FsEnv P.card (ck N P) (verts N P).card (bdry N (msplit g N P).1 (msplit g N P).2).card
        m' nV nF Ck p₀ p₁ →
      10 + fsz (msplit g N P).1.card (ck N (msplit g N P).1) +
        fsz (msplit g N P).2.card (ck N (msplit g N P).2) +
        fsRoom C P.card (ck N P) (verts N P).card
          (bdry N (msplit g N P).1 (msplit g N P).2).card Ck p₀ p₁ ≤ rF P)
    (hrF0 : ∀ P : Finset D, 10 + fsz (msplit g N P).1.card (ck N (msplit g N P).1) +
        fsz (msplit g N P).2.card (ck N (msplit g N P).2) + 200 * ck N P + spWs (ck N P) ≤
        rF P) :
    ∀ n P d e bl el er c f₀ f₁, GZ0 Hb c → WordsBounded W c →
      c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = bl + 5 → c.nreg 3007 = el →
      c.nreg 3008 = el + 5 → c.nreg 3009 = er → c.nreg 3003 = er → Hb + 5 ≤ d → d ≤ e →
      e ≤ bl → bl + 5 ≤ el → el + 5 ≤ er → bl + rF P ≤ W → InPR g N ℓ L (n + 1) P d e c →
      Cnd (msplit g N) (n + 1) P →
      PotOut (pg N (msplit g N P).1 ℓ) (some f₀) → PotOut (pg N (msplit g N P).2 ℓ) (some f₁) →
      Res g N L (msplit g N P).1 (some f₀) (bl + 5) el c →
      Res g N L (msplit g N P).2 (some f₁) (el + 5) er c →
      (bdry N (msplit g N P).1 (msplit g N P).2).Nonempty →
      ∃ c' t o, Exec I W (Fs (WNb (Fintype.card D) L) Gt) c c' t ∧
        t ≤ ncF (msplit g N P).1 (msplit g N P).2 ∧
        GZ0 Hb c' ∧ RegKeep c c' ∧ HeapKeep Hb bl d e c c' ∧ c'.output = c.output ∧
        PotOut (pg N P ℓ) o ∧ Res g N L P o d e c' := by
  intro n P d e bl el er c f₀ f₁ hg hc r04 r05 r06 r07 r08 r09 r03 b1 b2 b3 b4 b5 hroom hinR
    hcnd hp0 hp1 hr0 hr1 hB
  obtain ⟨hPr, hin⟩ := hinR
  have hU := msplit_union (g := g) (N := N) P
  have hbig : 1000000 < P.card := hcnd.2.1
  have hmk := ck_ge (N := N) P
  have hk2 : ck N P ≤ 2 * P.card := card_rcl_le P
  have hkD : ck N P ≤ Fintype.card D := ck_le_card P
  have hws : spWs (ck N P) ≤ spWs (Fintype.card D) := spWs_mono hkD
  have he := hin.en
  have hel := hr0.1
  have her := hr1.1
  unfold fsz at he hel her
  have hWNW : WNb (Fintype.card D) L ≤ W := by omega
  have hWbig : 2 * L + 9600 ≤ WNb (Fintype.card D) L := by unfold WNb; omega
  -- the parameter-free room facts
  have hR0 := hrF0 P
  unfold fsz at hR0
  have hroomer : er + 200 * ck N P + spWs (ck N P) ≤ W := by clear * - hR0 hroom hel her; omega
  -- `ndFront ; ndB ; spStage`
  obtain ⟨c₃, t₁, w, ν', x₁, e₁, ht₁, s03, s04, s75, s74, s64, s96, s72, hwv, P1, P2, hT, hH,
    hG0, hG1, hin₃, hx₁, hbx, hBO, hZ3, hSp, hK3, hR3, hrr3, hrm3, ho3⟩ :=
    fs_p1 (I := I) (Gt := Gt) hM hrot hface c hc hg hPr hin r04 r07 r09 r03
      (by clear * - hws hHb2; omega) hGH b1 b3 b4 b5 hr0 hr1 hbig hB
      (by clear * - hroomer; omega) (by clear * - hroomer hWNH hWbig b1 b2 b3 b4 b5; omega)
      (by clear * - hW4; omega) (by clear * - hW6; omega)
  have hdh : d + 4 + 5 * ck N P + P.card ≤ er := by clear * - he b3 b4 b5 hel her; omega
  -- `fbA`
  obtain ⟨A₀, nV, nF, m', cn, vn, fn, ψ, Cy, Zf, hbd₀, hbd₁, hcut, hcutEq, hsZ, hsZc, hψ, hBsC,
    hCk2, hCk, hm', hVF, hE, hXm, hFm, hside, r960, r961, r962, c₄, t₂, e₂, ht₂, hR, hS0, hS1,
    hid, hmem4, hreg4, hrr4, hrm4, ho4⟩ :=
    fs_p2 (P := I) hM hrot hface c₃ e₁.wb_right hPr hin₃ hp0 hp1 (res_abs hr0) (res_abs hr1) hℓ
      s03 s04 s75 s74 s64 s72 hwv P1 hT hH hG0 hG1 hx₁ hbx hBO (fun a ha => (hSp a ha).1) hbig
      hdh (by clear * - b1 hws hHb2; omega) (by clear * - hroomer; omega)
      (by clear * - hW4 hWbig; omega) (by clear * - hW6; omega)
  -- the semantic side: the large component, the cut, the two sides
  set k := ck N P with hkdef
  set b := (bdry N (msplit g N P).1 (msplit g N P).2).card with hbdef
  have hKP : (pcomp N P x₁) ⊆ P := pcomp_subset P x₁
  have hRd : Disjoint (verts N (P \ (pcomp N P x₁))) (verts N (pcomp N P x₁)) := disjoint_verts_pcomp P x₁
  obtain ⟨R₀, R₁, eR0, eR1, hR0, hR1⟩ := cut_parts P (pcomp N P x₁) A₀
  have hA0K : A₀ ⊆ (pcomp N P x₁) := hsZ ▸ side_subset Zf
  have hX₀ : (msplit g N P).1 = side N (pcomp N P x₁) Zf ∪ R₀ := by rw [hcutEq, eR0, hsZ]
  have hX₁ : (msplit g N P).2 = side N (pcomp N P x₁) Zfᶜ ∪ R₁ := by rw [hcutEq, eR1, hsZc]
  have hRv₀ : Disjoint (verts N R₀) (verts N (pcomp N P x₁)) := disj_R hRd hR0
  have hRv₁ : Disjoint (verts N R₁) (verts N (pcomp N P x₁)) := disj_R hRd hR1
  have hbdEq : bdry N (msplit g N P).1 (msplit g N P).2 = bdry N A₀ ((pcomp N P x₁) \ A₀) := by
    rw [hcutEq]; exact cut_bdry hA0K hRd
  have hBs₀ : ∀ x ∈ bdry N (msplit g N P).1 (msplit g N P).2,
      x ∈ verts N (side N (pcomp N P x₁) Zf) ∧ Sum.inl (ψ x) ∈ Cy.verts := fun x hx => by
    rw [hbdEq] at hx
    exact ⟨hsZ ▸ (Finset.mem_inter.1 hx).1, hBsC x hx⟩
  have hBs₁ : ∀ x ∈ bdry N (msplit g N P).1 (msplit g N P).2,
      x ∈ verts N (side N (pcomp N P x₁) Zfᶜ) ∧ Sum.inl (ψ x) ∈ Cy.verts := fun x hx => by
    rw [hbdEq] at hx
    exact ⟨hsZc ▸ (Finset.mem_inter.1 hx).2, hBsC x hx⟩
  have hS0' := hS0
  have hS1' := hS1
  rw [← hbdEq] at hS0' hS1'
  have hKr : (pcomp N P x₁) ⊆ reps N := hKP.trans hPr
  have hK0 : (pcomp N P x₁).Nonempty := ⟨x₁, self_mem_pcomp hx₁⟩
  have hKc : DConn N (pcomp N P x₁) := pcomp_dconn
  have hb1 : 1 ≤ b := Finset.card_pos.2 hB
  have hbw : b ≤ w := by
    rw [hwv]; exact Finset.card_le_card (fun x hx => by
      have := (Finset.mem_inter.1 hx).1; rw [← hU]; exact verts_mono subset_union_left this)
  have hw2 : w ≤ 2 * k := by rw [hwv]; have := NTree.card_verts_le (N := N) P; omega
  -- the two instances' parameters
  obtain ⟨p₀, hp₀⟩ : ∃ p : FeP, p = ⟨c₄.nreg 2240, c₄.nreg 2243, c₄.nreg 2241, c₄.nreg 2242 + 1,
      fbY (spB0 k) k P.card w b ⟨c₄.nreg 2240, c₄.nreg 2243, c₄.nreg 2241, c₄.nreg 2242 + 1, 0, 0⟩
          ⟨c₄.nreg 2244, c₄.nreg 2247, c₄.nreg 2245, c₄.nreg 2246 + 1, 0, 0⟩ +
        16 * fbS w b ⟨c₄.nreg 2240, c₄.nreg 2243, c₄.nreg 2241, c₄.nreg 2242 + 1, 0, 0⟩
          ⟨c₄.nreg 2244, c₄.nreg 2247, c₄.nreg 2245, c₄.nreg 2246 + 1, 0, 0⟩ + 2 * w,
      feIsoB (c₄.nreg 2241 + 2 * c₄.nreg 2243) (c₄.nreg 2240 + 8 * c₄.nreg 2243)
        (c₄.nreg 2242 + 1 + 2 * c₄.nreg 2243)
        (1 + pwS c₄.nmem (er + 50 * k + 3 * c₄.nreg 2240) (er + 50 * k + 4 * c₄.nreg 2240)
          (c₄.nreg 2240))⟩ := ⟨_, rfl⟩
  obtain ⟨p₁, hp₁⟩ : ∃ p : FeP, p = ⟨c₄.nreg 2244, c₄.nreg 2247, c₄.nreg 2245, c₄.nreg 2246 + 1,
      p₀.END,
      feIsoB (c₄.nreg 2245 + 2 * c₄.nreg 2247) (c₄.nreg 2244 + 8 * c₄.nreg 2247)
        (c₄.nreg 2246 + 1 + 2 * c₄.nreg 2247)
        (1 + pwS c₄.nmem (er + 110 * k + 3 * c₄.nreg 2244) (er + 110 * k + 4 * c₄.nreg 2244)
          (c₄.nreg 2244))⟩ := ⟨_, rfl⟩
  have e0 : c₄.nreg 2240 = p₀.nD := by rw [hp₀]
  have e1 : c₄.nreg 2241 = p₀.nV := by rw [hp₀]
  have e2 : c₄.nreg 2242 + 1 = p₀.nF := by rw [hp₀]
  have e3 : c₄.nreg 2243 = p₀.k := by rw [hp₀]
  have f0 : c₄.nreg 2244 = p₁.nD := by rw [hp₁]
  have f1 : c₄.nreg 2245 = p₁.nV := by rw [hp₁]
  have f2 : c₄.nreg 2246 + 1 = p₁.nF := by rw [hp₁]
  have f3 : c₄.nreg 2247 = p₁.k := by rw [hp₁]
  have hI0₀ : p₀.I0 = fbY (spB0 k) k P.card w b p₀ p₁ + 16 * fbS w b p₀ p₁ + 2 * w := by
    rw [hp₁, hp₀]; rfl
  have hI0₁ : p₁.I0 = p₀.END := by rw [hp₁]
  have hL₀ : p₀.Lmax = feIsoB p₀.A p₀.N p₀.FN
      (1 + pwS c₄.nmem (er + 50 * k + 3 * p₀.nD) (er + 50 * k + 4 * p₀.nD) p₀.nD) := by
    rw [hp₀]; rfl
  have hL₁ : p₁.Lmax = feIsoB p₁.A p₁.N p₁.FN
      (1 + pwS c₄.nmem (er + 110 * k + 3 * p₁.nD) (er + 110 * k + 4 * p₁.nD) p₁.nD) := by
    rw [hp₁]; rfl
  -- the sizes of the two sides
  have hred₀ : ∀ x ∈ side N (pcomp N P x₁) Zf,
      redLen N ℓ (fbExt (verts N (msplit g N P).1) f₀ L) x ≤ 3 * L := fun x hx => by
    have := (fbExt_red hp0 (res_abs hr0) (fun y _ => hℓ y)
      (by rw [hX₀]; exact Finset.mem_union_left _ hx)).2
    push_cast at this; omega
  have hred₁ : ∀ x ∈ side N (pcomp N P x₁) Zfᶜ,
      redLen N ℓ (fbExt (verts N (msplit g N P).2) f₁ L) x ≤ 3 * L := fun x hx => by
    have := (fbExt_red hp1 (res_abs hr1) (fun y _ => hℓ y)
      (by rw [hX₁]; exact Finset.mem_union_left _ hx)).2
    push_cast at this; omega
  obtain ⟨z1₀, z2₀, z3₀, z4₀, zW₀⟩ := sideOut_facts hS0 cn hred₀
  obtain ⟨z1₁, z2₁, z3₁, z4₁, zW₁⟩ := sideOut_facts hS1 cn hred₁
  simp only [Nat.reduceAdd] at z1₀ z2₀ z4₀ z1₁ z2₁ z4₁
  have hsd₀ : (side N (pcomp N P x₁) Zf).card ≤ Fintype.card D := card_le_univ _
  have hsd₁ : (side N (pcomp N P x₁) Zfᶜ).card ≤ Fintype.card D := card_le_univ _
  have hk0 : 0 < k := by omega
  have env₀ : FbEnv p₀ (Fintype.card D) L
      (1 + pwS c₄.nmem (er + 50 * k + 3 * p₀.nD) (er + 50 * k + 4 * p₀.nD) p₀.nD) :=
    ⟨by rw [← e0]; clear * - z3₀ hm' hkD; omega, by rw [← e3]; clear * - z4₀ hCk hkD; omega,
      by rw [← e1]; clear * - z1₀ z3₀ hm' hkD; omega,
      by rw [← e2]; clear * - z2₀ z3₀ hm' hkD; omega, hL₀,
      by rw [← e0]; exact zW₀.trans (by have := Nat.mul_le_mul_left (3 * L) hsd₀; omega)⟩
  have env₁ : FbEnv p₁ (Fintype.card D) L
      (1 + pwS c₄.nmem (er + 110 * k + 3 * p₁.nD) (er + 110 * k + 4 * p₁.nD) p₁.nD) :=
    ⟨by rw [← f0]; clear * - z3₁ hm' hkD; omega, by rw [← f3]; clear * - z4₁ hCk hkD; omega,
      by rw [← f1]; clear * - z1₁ z3₁ hm' hkD; omega,
      by rw [← f2]; clear * - z2₁ z3₁ hm' hkD; omega, hL₁,
      by rw [← f0]; exact zW₁.trans (by have := Nat.mul_le_mul_left (3 * L) hsd₁; omega)⟩
  have hB0n : spB0 k ≤ spWs (Fintype.card D) := by unfold spWs at hws ⊢; omega
  obtain ⟨⟨wn1, wn2, wn3, wn4, wn5, wn6, wn7, wn8, wn9⟩, wnB, wnW, wnM, wnE, wnPb, wnI0, wnE0⟩ :=
    fs_WN_le env₀ env₁ (by clear * - hmk hkD; omega) (by clear * - hw2 hk2 hkD; omega)
      (by clear * - hbw hw2 hkD; omega) hkD hB0n hI0₀ hI0₁
  -- `fbMid`
  have M4 : ∀ a, a < er + 10 * k → c₄.nmem a = c₃.nmem a := fun a ha => hmem4 a (Or.inl ha)
  have G4 : ∀ r, (2248 ≤ r ∧ r < 2550) ∨ 2850 < r ∨ (840 < r ∧ r < 2100) →
      c₄.nreg r = c₃.nreg r := fun r hr =>
    hreg4 r (by omega) (by omega) (by omega) (by omega)
  have hsp : spWs k < Hb := by clear * - hws hHb2; omega
  have hHer : Hb ≤ er := by clear * - b1 b2 b3 b4 b5; omega
  have hlow : ∀ a < 2 * (spB0 k + 66 * k + 35) + 2, c₄.nmem a ≤ spB0 k + 66 * k + 35 := by
    intro a ha
    have hws' : spWs k = spB0 k + 66 * k + 35 := rfl
    rw [M4 a (by clear * - ha hws' hws hHb2 hHer; omega)]
    by_cases h1 : a ≤ spWs k
    · rw [← hws']; exact (hSp a h1).2
    · rw [hZ3 a (by omega) (by clear * - ha hws' hws hHb2; omega)]; exact Nat.zero_le _
  have hBspWs : spB0 k + 28 * k + 3 + 4 * m' + m' ≤ er := by
    have hws' : spWs k = spB0 k + 66 * k + 35 := rfl
    clear * - hws' hsp hHer hm'; omega
  obtain ⟨c₆, t₃, e₃, ht₃, v1022, v1023, v1024, v13, v14, v15, v16, v21, v00, v01, N₆, Z6, T6,
    H6, S6, A6₀, A6₁, P6₀, P6₁, Pk6, R6ℓ, R6₀, R6₁, F6, rr6, rm6, o6⟩ :=
    fs_mid (P := I)
      (show PEnc N P P.card k (cδ g N P) (cα g N P) (cσ g N P) from penc_canon (g := g) P) hKP (ν := fun x => ν' (g.gv x))
      (ι := fun v => gInv g N (c₃.nmem (er + 2 * k + v))) (fun x hx => (P1 x hx).2)
      (fun x hx => (P1 x hx).1) cn vn fn ψ hψ (ℓ := ℓ)
      (δ₀ := fbExt (verts N (msplit g N P).1) f₀ L) (δ₁ := fbExt (verts N (msplit g N P).2) f₁ L)
      (p₀ := p₀) (p₁ := p₁) c₄ e₂.wb_right
      (by rw [G4 _ (by decide)]; exact s03) (by rw [G4 _ (by decide)]; exact s04)
      (by rw [G4 _ (by decide)]; exact s75) (by rw [G4 _ (by decide)]; exact s74)
      (by rw [G4 _ (by decide)]; exact s64) (by rw [G4 _ (by decide)]; exact r960)
      (by rw [G4 _ (by decide)]; exact r961) (by rw [G4 _ (by decide)]; exact r962)
      (by rw [G4 _ (by decide)]; exact s96) (by rw [G4 _ (by decide)]; exact s72) hR
      e0 e1 e2 e3 f0 f1 f2 f3 hid
      (fun i hi => by rw [M4 _ (by clear * - hi hmk; omega)]; exact hT i hi)
      (fun i hi => by rw [M4 _ (by clear * - hi hmk; omega)]; exact hH i hi)
      (enc_congr hE fun i hi => ⟨M4 _ (by clear * - hi hBspWs; omega),
        M4 _ (by clear * - hi hBspWs; omega), M4 _ (by clear * - hi hBspWs; omega),
        M4 _ (by clear * - hi hBspWs; omega), M4 _ (by clear * - hi hBspWs; omega)⟩)
      (fun i hi hm => by
        have hws' : spWs k = spB0 k + 66 * k + 35 := rfl
        rw [M4 _ (by clear * - hi hws' hsp hHer; omega)]; exact hXm i hi hm)
      (fun x hx => by
        have hws' : spWs k = spB0 k + 66 * k + 35 := rfl
        rw [M4 _ (by clear * - hx hmk hws' hsp hHer; omega)]; exact hFm x hx)
      hlow
      (by rw [M4 _ (by clear * - hdh; omega)]; exact hin₃.rm)
      (by rw [M4 _ (by clear * - hdh; omega)]; exact hin₃.rk)
      (fun i hi => by rw [M4 _ (by clear * - hi hdh; omega)]; exact hin₃.ln i hi)
      (fun i _ => hℓ _)
      (fun v hv => by rw [M4 _ (by clear * - hv hw2; omega)]; exact hG0 v hv)
      (fun v hv => by rw [M4 _ (by clear * - hv hw2; omega)]; exact hG1 v hv)
      rfl hmk hw2 hm' hVF hk0 hb1 hI0₀ hI0₁
      (by rw [← e0, ← e3]; clear * - z3₀ z4₀ hm' hCk; omega)
      (by rw [← f0, ← f3]; clear * - z3₁ z4₁ hm' hCk; omega) hL₀ hL₁ wnE
      (by clear * - wnW hWNW; omega) (by clear * - wnM hWNW; omega)
      (by clear * - wn6 hWNW; omega) (by clear * - wn7 hWNW; omega)
      (by clear * - hroomer hWNH hWbig b1 b2 b3 b4 b5; omega)
      (by clear * - wn1 hWNH b1; omega) hdh (by clear * - wnM hWNW; omega)
      (by have hws' : spWs k = spB0 k + 66 * k + 35 := rfl
          clear * - hws' hsp hHer hHb2 hws; omega)
      (by have hws' : spWs k = spB0 k + 66 * k + 35 := rfl
          clear * - hws' hroomer; omega)
      (by clear * - hW6; omega)
  -- the two instances on the final memory
  obtain ⟨-, -, -, -, -, -, a0₀, -⟩ := hS0
  obtain ⟨-, -, -, -, -, -, a0₁, -⟩ := hS1
  obtain ⟨i₀, σ₀, νv₀, τ₀, b0₀, b1₀, b2₀, b3₀, FA₀, FP₀⟩ :=
    side_data' hM hrot hface hKr hK0 hKc hψ hbd₀ hBs₀ hRv₀ hX₀ hS0' (mem := c₆.nmem)
      (I0' := p₀.I0) (Pb := fbY (spB0 k) k P.card w b p₀ p₁ + 16 * fbS w b p₀ p₁) (k := k)
      (ν := fun x => ν' (g.gv x))
      (fun j hj => by rw [A6₀ j (by rw [← e0, ← e3, a0₀, z4₀]; exact hj)])
      (fun x hx => by
        rw [P6₀ x hx, show er + 20 * k + 2 * (nV + nF) = er + 20 * k + 2 * nV + 2 * nF by ring])
      hCk
  obtain ⟨i₁, σ₁, νv₁, τ₁, b0₁, b1₁, b2₁, b3₁, FA₁, FP₁⟩ :=
    side_data' hM hrot hface hKr hK0 hKc hψ hbd₁ hBs₁ hRv₁ hX₁ hS1' (mem := c₆.nmem)
      (I0' := p₁.I0) (Pb := fbY (spB0 k) k P.card w b p₀ p₁ + 16 * fbS w b p₀ p₁ + w) (k := k)
      (ν := fun x => ν' (g.gv x))
      (fun j hj => by rw [A6₁ j (by rw [← f0, ← f3, a0₁, z4₁]; exact hj)])
      (fun x hx => by
        rw [P6₁ x hx, show er + 80 * k + 2 * (nV + nF) = er + 80 * k + 2 * nV + 2 * nF by ring])
      hCk
  simp only [Nat.reduceAdd] at b1₀ b2₀ b3₀ b1₁ b2₁ b3₁
  -- the sizes of the instances
  have hcD₀ := b0₀.symm.trans e0
  have hcV₀ := b1₀.symm.trans e1
  have hcF₀ := b2₀.symm.trans e2
  have hck₀ := b3₀.symm.trans e3
  have hcD₁ := b0₁.symm.trans f0
  have hcV₁ := b1₁.symm.trans f1
  have hcF₁ := b2₁.symm.trans f2
  have hck₁ := b3₁.symm.trans f3
  -- the weight words
  have hWc₀ : (Klein.srcW ((sideFD hM hrot hface hKr hK0 hKc hψ hbd₀ hBs₀ hRv₀ hX₀ i₀).P'.image
      (sideFD hM hrot hface hKr hK0 hKc hψ hbd₀ hBs₀ hRv₀ hX₀ i₀).e)
      (faceLen (sideFD hM hrot hface hKr hK0 hKc hψ hbd₀ hBs₀ hRv₀ hX₀ i₀).P'
        (sideFD hM hrot hface hKr hK0 hKc hψ hbd₀ hBs₀ hRv₀ hX₀ i₀).e
        (redLen N ℓ (fbExt (verts N (msplit g N P).1) f₀ L)))).toNat =
      1 + pwS c₄.nmem (er + 50 * k + 3 * p₀.nD) (er + 50 * k + 4 * p₀.nD) p₀.nD := by
    rw [← fdArr_srcW FA₀, hcD₀, pw_shift (k' := p₀.k) A6₀]
  have hWc₁ : (Klein.srcW ((sideFD hM hrot hface hKr hK0 hKc hψ hbd₁ hBs₁ hRv₁ hX₁ i₁).P'.image
      (sideFD hM hrot hface hKr hK0 hKc hψ hbd₁ hBs₁ hRv₁ hX₁ i₁).e)
      (faceLen (sideFD hM hrot hface hKr hK0 hKc hψ hbd₁ hBs₁ hRv₁ hX₁ i₁).P'
        (sideFD hM hrot hface hKr hK0 hKc hψ hbd₁ hBs₁ hRv₁ hX₁ i₁).e
        (redLen N ℓ (fbExt (verts N (msplit g N P).2) f₁ L)))).toNat =
      1 + pwS c₄.nmem (er + 110 * k + 3 * p₁.nD) (er + 110 * k + 4 * p₁.nD) p₁.nD := by
    rw [← fdArr_srcW FA₁, hcD₁, pw_shift (k' := p₁.k) A6₁]
  have hLm₀ := le_feIsoB p₀.A p₀.N p₀.FN
    (1 + pwS c₄.nmem (er + 50 * k + 3 * p₀.nD) (er + 50 * k + 4 * p₀.nD) p₀.nD)
  have hLm₁ := le_feIsoB p₁.A p₁.N p₁.FN
    (1 + pwS c₄.nmem (er + 110 * k + 3 * p₁.nD) (er + 110 * k + 4 * p₁.nD) p₁.nD)
  rw [← hL₀] at hLm₀
  rw [← hL₁] at hLm₁
  -- the word bounds of the node's low arrays
  have hZb := fbZ_bounds (spB0 k) k P.card w b p₀ p₁
  have hYZ : fbZ (spB0 k) k P.card w b p₀ p₁ + 22 * (P.card + w + 1) =
      fbY (spB0 k) k P.card w b p₀ p₁ := rfl
  have hE₀ := pn_end p₀
  have hE₁ := pn_end p₁
  have hWpnW : p₁.END + p₀.Lmax + p₁.Lmax ≤ pnW p₀ p₁ := by unfold pnW; omega
  have hZW : fbZ (spB0 k) k P.card w b p₀ p₁ + 6 * (P.card + w + 1) ≤ pnW p₀ p₁ := by
    clear * - hYZ wnPb wnI0 wnE0 wnE hI0₀; omega
  have hwW : w ≤ pnW p₀ p₁ := by unfold loB at hZb; clear * - hZb hZW; omega
  have hkW : k ≤ pnW p₀ p₁ := by clear * - hZb hZW; omega
  have vA0 : ∀ j < 5 * p₀.nD + p₀.k, c₆.nmem (p₀.I0 + j) ≤ pnW p₀ p₁ := by
    intro j hj
    have hb := fdArr_le FA₀ j (by rw [hcD₀, hck₀]; exact hj)
    rw [hcD₀, hcV₀, hcF₀, hWc₀] at hb
    rw [hI0₁] at hE₁
    clear * - hb hLm₀ hWpnW hE₀ hE₁; omega
  have vA1 : ∀ j < 5 * p₁.nD + p₁.k, c₆.nmem (p₁.I0 + j) ≤ pnW p₀ p₁ := by
    intro j hj
    have hb := fdArr_le FA₁ j (by rw [hcD₁, hck₁]; exact hj)
    rw [hcD₁, hcV₁, hcF₁, hWc₁] at hb
    clear * - hb hLm₁ hWpnW hE₁; omega
  -- the memory facts of the node
  have hMgt : L + 1 < 2 * nodeHN P.card b w (L + 1) + 1 := by unfold nodeHN; omega
  have hc0 : ∀ a, spWs k < a → a < Hb → c₄.nmem a = 0 := fun a h1 h2 => by
    rw [M4 a (by clear * - h2 hHer; omega)]; exact hZ3 a h1 h2
  obtain ⟨hz, hzc, hmW, hdm, hres⟩ := fs_mem (mem := c₆.nmem) (cmem := c₄.nmem)
    (B := L + 1) (WN := WNb (Fintype.card D) L) (Hb := Hb)
    (M := 2 * nodeHN P.card b w (L + 1) + 1) Z6 F6 hc0
    (by have := hZb.2.2.2.2.2.2; unfold spWs; clear * - this; omega) rfl (le_of_eq hYZ) hI0₀
    (by rw [hI0₁]; clear * - hE₀; omega) (by clear * - hE₁; omega) wnE hZW
    (by clear * - wn1; omega) hWNH hHer (by omega)
    (fun i hi => by
      rw [T6 i hi, M4 _ (by clear * - hi hmk; omega), hT i hi]
      have := (P1 _ (tail_mem_verts (cδ_memP (g := g) (N := N) hi))).1
      clear * - this hwW; omega)
    (fun i hi => by
      rw [H6 i hi, M4 _ (by clear * - hi hmk; omega), hH i hi]
      have := (P1 _ (head_mem_verts (cδ_memP (g := g) (N := N) hi))).1
      clear * - this hwW; omega)
    (fun i hi => by
      have hws' : spWs k = spB0 k + 66 * k + 35 := rfl
      rw [S6 i hi, M4 _ (by clear * - hi hmk hws' hsp hHer; omega), hside i hi]
      split_ifs <;> clear * - hwW hb1 hbw <;> omega)
    vA0 vA1
    (fun i hi => by have := Pk6 i hi; clear * - this hkW; omega)
    (fun a ha => by
      rcases ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨i, rfl⟩ : ∃ i, a = pnW p₀ p₁ + 1 +
            (fbZ (spB0 k) k P.card w b p₀ p₁ + 3 * (P.card + w + 1)) + i := ⟨_, (Nat.add_sub_cancel' h1).symm⟩
        have hi : i < P.card := by omega
        have := R6ℓ i hi
        rw [← Nat.add_assoc] at this
        exact res_near this (by have := hℓ (cδ g N P i); push_cast; linarith) hMgt
      · obtain ⟨i, rfl⟩ : ∃ i, a = pnW p₀ p₁ + 1 +
            (fbZ (spB0 k) k P.card w b p₀ p₁ + 4 * (P.card + w + 1)) + i := ⟨_, (Nat.add_sub_cancel' h1).symm⟩
        have hi : i < w := by omega
        have := R6₀ i hi
        rw [← Nat.add_assoc] at this
        exact res_near this (by have := (hG0 i hi).2; push_cast; linarith) hMgt
      · obtain ⟨i, rfl⟩ : ∃ i, a = pnW p₀ p₁ + 1 +
            (fbZ (spB0 k) k P.card w b p₀ p₁ + 5 * (P.card + w + 1)) + i := ⟨_, (Nat.add_sub_cancel' h1).symm⟩
        have hi : i < w := by omega
        have := R6₁ i hi
        rw [← Nat.add_assoc] at this
        exact res_near this (by have := (hG1 i hi).2; push_cast; linarith) hMgt)
  -- the envelope, the room
  have hw2m : w ≤ 2 * P.card := by rw [hwv]; exact NTree.card_verts_le (N := N) P
  have hq₀ : 18 * (pcomp N P x₁).card ≤ 18 * ((msplit g N P).1 ∪ (msplit g N P).2).card := by
    rw [hU]; exact Nat.mul_le_mul_left _ (card_le_card hKP)
  have hCk2' : Cy.k ^ 2 ≤ 1200 * ((msplit g N P).1 ∪ (msplit g N P).2).card := by rw [hU]; exact hCk2
  have hCk2P : Cy.k ^ 2 ≤ 1200 * P.card := hCk2
  have env : FsEnv P.card k w b m' nV nF Cy.k p₀ p₁ :=
    ⟨hbig, hmk, hk2, hw2m, hbw, hm', hVF, hCk, hCk2P, by rw [← e3]; exact z4₀,
      by rw [← f3]; exact z4₁, by rw [← e0]; exact z3₀, by rw [← f0]; exact z3₁,
      by rw [← e0, ← e1]; exact z1₀, by rw [← f0, ← f1]; exact z1₁,
      by rw [← e0, ← e2]; exact z2₀, by rw [← f0, ← f2]; exact z2₁,
      nbFeCostDk_node_le (sideFD hM hrot hface hKr hK0 hKc hψ hbd₀ hBs₀ hRv₀ hX₀ i₀) P.card
        (Nat.mul_le_mul_left _ (card_le_card hKP)) hCk2P p₀ hcD₀.symm hck₀.symm hcV₀.symm
        hcF₀.symm,
      nbFeCostDk_node_le (sideFD hM hrot hface hKr hK0 hKc hψ hbd₁ hBs₁ hRv₁ hX₁ i₁) P.card
        (Nat.mul_le_mul_left _ (card_le_card hKP)) hCk2P p₁ hcD₁.symm hck₁.symm hcV₁.symm
        hcF₁.symm, hI0₀, hI0₁⟩
  have hRm := hrF P m' nV nF Cy.k p₀ p₁ (by rw [← hwv]; exact env)
  rw [← hwv] at hRm
  simp only [← hkdef, ← hbdef] at hRm
  unfold fsz fsRoom at hRm
  have hRW : er + 200 * k + ndRunCost C P.card P.card w b Cy.k Cy.k p₀ p₁ +
      5 * (P.card + w) + 8 * (w + 1) + 1 ≤ W := by
    clear * - hRm hroom hel her hkdef hbdef; omega
  -- the node's semantic inputs
  have hSF : SplitF N ((msplit g N P).1 ∪ (msplit g N P).2) (msplit g N P).1 (msplit g N P).2 := by
    rw [hU]; exact msplit_splitF hM hrot hface hPr hbig
  have hNE := fb_nodeEnc (g := g) (N := N) (P := P) (ν := ν')
    (I := fun v => c₃.nmem (er + 2 * k + v)) hwv P1
  have hN1₀ : Klein.srcN1 (sideFD hM hrot hface hKr hK0 hKc hψ hbd₀ hBs₀ hRv₀ hX₀ i₀).VQ
      (sideFD hM hrot hface hKr hK0 hKc hψ hbd₀ hBs₀ hRv₀ hX₀ i₀).FQ
      (sideFD hM hrot hface hKr hK0 hKc hψ hbd₀ hBs₀ hRv₀ hX₀ i₀).DQ
      (sideFD hM hrot hface hKr hK0 hKc hψ hbd₀ hBs₀ hRv₀ hX₀ i₀).k =
      MSSP.isoN1 p₀.A p₀.N p₀.FN := by
    unfold Klein.srcN1
    rw [Klein.card_srcV, Klein.card_srcD, Klein.card_srcF, hcV₀, hcD₀, hcF₀, hck₀]
    unfold FeP.A FeP.N FeP.FN; rw [Nat.mul_comm p₀.k 8]
  have hN1₁ : Klein.srcN1 (sideFD hM hrot hface hKr hK0 hKc hψ hbd₁ hBs₁ hRv₁ hX₁ i₁).VQ
      (sideFD hM hrot hface hKr hK0 hKc hψ hbd₁ hBs₁ hRv₁ hX₁ i₁).FQ
      (sideFD hM hrot hface hKr hK0 hKc hψ hbd₁ hBs₁ hRv₁ hX₁ i₁).DQ
      (sideFD hM hrot hface hKr hK0 hKc hψ hbd₁ hBs₁ hRv₁ hX₁ i₁).k =
      MSSP.isoN1 p₁.A p₁.N p₁.FN := by
    unfold Klein.srcN1
    rw [Klein.card_srcV, Klein.card_srcD, Klein.card_srcF, hcV₁, hcD₁, hcF₁, hck₁]
    unfold FeP.A FeP.N FeP.FN; rw [Nat.mul_comm p₁.k 8]
  -- the frame from `c₃` to `c₆` above the node's data
  have Hi : ∀ a, WNb (Fintype.card D) L < a → a < er + 10 * k → c₆.nmem a = c₃.nmem a := by
    intro a h1 h2
    rw [← M4 a h2]
    have hspZ : spWs k < fbZ (spB0 k) k P.card w b p₀ p₁ := by
      have := hZb.2.2.2.2.2.2; unfold spWs; clear * - this; omega
    exact F6 a (by clear * - h1 hspZ hZW wn1; omega)
      (Or.inr (by clear * - h1 wn1 hZW; omega)) (Or.inr (by clear * - h1 wn1 hZW; omega))
      (Or.inr (by clear * - h1 wn1 hZW; omega))
      (Or.inr (by clear * - h1 wn1 wnE0 wnE hE₀; omega))
      (Or.inr (by clear * - h1 wn1 wnE hE₁; omega))
      (Or.inr (by clear * - h1 wn1 wnE0 wnE wnI0 wnPb; omega))
      (Or.inr (by clear * - h1 wn1 hZW; omega)) (Or.inr (by clear * - h1 wn1 hZW; omega))
      (Or.inr (by clear * - h1 wn1 hZW; omega)) (Or.inl (by clear * - h2; omega))
  have hin₆ : InP g N ℓ L (n + 1) ((msplit g N P).1 ∪ (msplit g N P).2) d e c₆ := by
    rw [hU]
    exact inP_stab hin₃ fun a h1 h2 => ⟨Hi a (by clear * - h1 b1 hWNH; omega)
      (by clear * - h2 b3 b4 b5; omega), by rw [rm6, hrm4]⟩
  have R6 : ∀ r, 2978 < r → c₆.nreg r = c₃.nreg r := fun r hr => by
    rw [N₆ r (by clear * - hr; omega), G4 r (by clear * - hr; omega)]
  have N6' : ∀ r, (2119 < r ∧ r < 2260) ∨ (2335 < r ∧ r < 2776) → c₆.nreg r = c₄.nreg r :=
    fun r hr => N₆ r (by clear * - hr; omega)
  have hcd : ∀ i < P.card, cδ g N P i = cδ g N ((msplit g N P).1 ∪ (msplit g N P).2) i := by
    rw [hU]; exact fun _ _ => rfl
  -- the node
  obtain ⟨c', t₄, o, e₄, ht₄, hpo, hres', Z1, K1, K2, R1, rr7, rm7, o7⟩ :=
    fs_node (h := er) (df := d) (de := e) C (frRef_spec (Option V)) (msspRef_spec N) hSF hB ℓ
      (fbExt (verts N (msplit g N P).1) f₀ L) (fbExt (verts N (msplit g N P).2) f₁ L)
      (fbExt_pot L hp0) (fbExt_pot L hp1)
      (sideFD hM hrot hface hKr hK0 hKc hψ hbd₀ hBs₀ hRv₀ hX₀ i₀) hq₀ hCk2'
      (sideFD hM hrot hface hKr hK0 hKc hψ hbd₁ hBs₁ hRv₁ hX₁ i₁) hq₀ hCk2'
      σ₀ νv₀ τ₀ σ₁ νv₁ τ₁ p₀ p₁ hcD₀.symm hck₀.symm hcV₀.symm hcF₀.symm hcD₁.symm hck₁.symm
      hcV₁.symm hcF₁.symm hNE rfl
      (fbY (spB0 k) k P.card w b p₀ p₁ + 16 * fbS w b p₀ p₁)
      (fbY (spB0 k) k P.card w b p₀ p₁ + 16 * fbS w b p₀ p₁ + w)
      (fbZ (spB0 k) k P.card w b p₀ p₁) (P.card + w + 1) (fbY (spB0 k) k P.card w b p₀ p₁)
      (fbS w b p₀ p₁) (pnW p₀ p₁) (L + 1) (2 * nodeHN P.card b w (L + 1) + 1)
      (WNb (Fintype.card D) L) I rfl hZb.1 hZb.2.1 hZb.2.2.1 hZb.2.2.2.1
      (by rw [hck₀]; exact hZb.2.2.2.2.1) (by rw [hck₁]; exact hZb.2.2.2.2.2.1)
      (le_of_eq hYZ)
      (by unfold fbS; rw [hck₀, hck₁, ← hbdef]; clear * -; omega) rfl rfl hI0₀ hI0₁
      (by rw [hWc₀]; exact hL₀) (by rw [hWc₁]; exact hL₁) rfl
      ⟨wn1, wn2, wn3, wn4, wn5, by rw [hN1₀]; exact wn6, by rw [hN1₁]; exact wn7,
        by rw [hWc₀]; exact wn8, by rw [hWc₁]; exact wn9⟩ rfl
      c₆ e₃.wb_right hWNW hin₆ (by rw [hU]) (by rw [hU])
      v1022 v13 v14 v1024 v1023 v21
      (by rw [N6' _ (by decide), G4 _ (by decide)]; exact s64)
      (by rw [N6' _ (by decide), G4 _ (by decide)]; exact s74)
      (by rw [N6' _ (by decide), G4 _ (by decide)]; exact s75)
      (by rw [N6' _ (by decide), G4 _ (by decide)]; exact s96)
      (by rw [N6' _ (by decide)]; exact hR.rL1) v15 v16
      (by rw [N6' _ (by decide)]; exact e0) (by rw [N6' _ (by decide)]; exact e3)
      (by rw [N6' _ (by decide)]; exact e1) v00
      (by rw [N6' _ (by decide)]; exact f0) (by rw [N6' _ (by decide)]; exact f3)
      (by rw [N6' _ (by decide)]; exact f1) v01
      (by rw [R6 _ (by decide)]; exact s03) (by rw [R6 _ (by decide)]; exact s04)
      hdm hmW (by clear * - hWbig; omega)
      (fun i hi => by
        rw [Nat.zero_mul, Nat.add_zero, T6 i hi, M4 _ (by clear * - hi hmk; omega), hT i hi]; rfl)
      (fun i hi => by
        rw [Nat.one_mul, H6 i hi, M4 _ (by clear * - hi hmk; omega), hH i hi]; rfl)
      (fun i hi => by
        have hws' : spWs k = spB0 k + 66 * k + 35 := rfl
        rw [S6 i hi, M4 _ (by clear * - hi hmk hws' hsp hHer; omega), hside i hi, ← hcutEq]; rfl)
      hz hres
      (fun i hi => ⟨R6ℓ i hi, by have := hℓ (cδ g N P i); clear * - this; omega⟩)
      (fun v hv => ⟨R6₀ v hv, (hG0 v hv).2⟩) (fun v hv => ⟨R6₁ v hv, (hG1 v hv).2⟩) FP₀ FP₁
      FA₀.rv (fun x => by rw [← hcD₀]; exact FA₀.nt x) (fun x => by rw [← hcD₀]; exact FA₀.nf x)
      (fun x => by rw [← hcD₀]; exact FA₀.is x) (fun x => by rw [← hcD₀]; exact FA₀.ln x)
      (fun i hi => by rw [← hcD₀]; exact FA₀.g i hi)
      FA₁.rv (fun x => by rw [← hcD₁]; exact FA₁.nt x) (fun x => by rw [← hcD₁]; exact FA₁.nf x)
      (fun x => by rw [← hcD₁]; exact FA₁.is x) (fun x => by rw [← hcD₁]; exact FA₁.ln x)
      (fun i hi => by rw [← hcD₁]; exact FA₁.g i hi)
      (by rw [hN1₀, hN1₁, hWc₀, hWc₁]; exact wnB)
      (fun a ha => by
        rw [Hi _ (by clear * - hWNH b1 b2 b3 b4 b5; omega) (by clear * - ha hmk; omega), hT a ha,
          hcd a ha])
      (fun a ha => by
        rw [Hi _ (by clear * - hWNH b1 b2 b3 b4 b5; omega) (by clear * - ha hmk; omega), hH a ha,
          hcd a ha])
      (fun v hv => by
        rw [Hi _ (by clear * - hWNH b1 b2 b3 b4 b5; omega) (by clear * - hv hw2; omega)]
        exact (P2 v hv).2.2)
      (fun v hv => ⟨by rw [hU]; exact (P2 v hv).1, (P2 v hv).2.1⟩)
      (fun x _ => hℓ x)
      ((Finset.sum_le_univ_sum_of_nonneg (fun x => abs_nonneg _)).trans hsumL)
      hzc (by clear * - hWNH b1; omega) (by clear * - b3 b4 b5; omega)
      (by rw [hU]; show er + 200 * k + ndRunCost C P.card P.card w b Cy.k Cy.k p₀ p₁ ≤ W
          clear * - hRW; omega) (by clear * - hRW hk2 hmk; omega) hW4
      (by clear * - hW6; omega)
  -- the conclusions
  have hspW : spWs k < WNb (Fintype.card D) L := by
    have := hZb.2.2.2.2.2.2; unfold spWs; clear * - this hZW wn1; omega
  have hC := hncF P m' nV nF Cy.k p₀ p₁ (by rw [← hwv]; exact env)
  rw [← hwv] at hC
  simp only [← hkdef, ← hbdef] at hC
  unfold fsCost at hC
  rw [hU] at ht₄
  have ht₄' : t₄ ≤ fsNodeCost (ndRunCost C P.card P.card w b Cy.k Cy.k p₀ p₁) p₁.END
      (fbZ (spB0 k) k P.card w b p₀ p₁) (P.card + w + 1) P.card w := ht₄
  rw [hU] at hpo hres'
  refine ⟨c', t₁ + (t₂ + (t₃ + t₄)), o, by unfold Fs; exact .seq e₁ (.seq e₂ (.seq e₃ e₄)),
    by clear * - hC ht₁ ht₂ ht₃ ht₄'; omega,
    ⟨fun r => by rw [rr7, rr6, hrr4, hrr3]; exact hg.1 r,
      fun a ha => by rw [rm7, rm6, hrm4, hrm3]; exact hg.2.1 a ha, fun a ha => ?_⟩,
    fun r hr => by rw [R1 r hr, R6 r (by omega), hR3 r hr],
    fun a h1 h2 h3 => ⟨?_, by rw [rm7, rm6, hrm4, hrm3]⟩, by rw [o7, o6, ho4, ho3], hpo, hres'⟩
  · by_cases ha' : a ≤ WNb (Fintype.card D) L
    · exact Z1 a ha'
    · rw [K1 a (by omega) (by clear * - ha b1; omega),
        Hi a (by omega) (by clear * - ha hHer; omega)]
      exact hZ3 a (by omega) ha
  · rcases h3 with h3 | h3
    · rw [K1 a (by clear * - h1 hWNH; omega) h3,
        Hi a (by clear * - h1 hWNH; omega) (by clear * - h2 b4 b5; omega)]
      exact hK3 a h1 (by clear * - h2 b4 b5; omega)
    · rw [K2 a h3 (by clear * - h2 b4 b5; omega),
        Hi a (by clear * - h1 hWNH; omega) (by clear * - h2 b4 b5; omega)]
      exact hK3 a h1 (by clear * - h2 b4 b5; omega)

end Frame

end NegSSSP

end PlanarFlow
