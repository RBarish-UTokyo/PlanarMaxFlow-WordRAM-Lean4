module

public import PlanarSeparator.Machine.MillerReroute

/-!
# Miller's separator on the machine: the whole program

`millerFull = millerB ; if 0 < r580 ∧ 0 < r581 then deepAll else bandO`, with
`deepAll = s10fb ; (bits of the two tests of deepSep) ; if one holds then fbO else s10rr`: the band
case (`bandO`: the cycle of `δ` in `T₁` with its inside marks), the deep fallback (`fbO`: the
boundary cycle of `Y` with the labels of `Y`) and the rerouting branch (`s10rr`, two arc options).
Every branch leaves the separator in the output registers: the darts at `r640` (their number in
`r641`), the marks of the faces at `r642` with the flag `r643` and the polarity `r644`
(`G ∈ Z ↔ (mark ≠ flag ↔ r644 = 1)`).

**`MillerProg.millerFull_spec`**: within one explicit `O((k + n) log n)` bound, the output is
`bandSep T T₁ l₂ cn (wR wP) δ x₀ g₀` for the dart `x₀` leaving `Y` found by `xfind` (in the deep
case) and the face `g₀` of a dart at the root, and it satisfies
`SepOK (wR wP) (2 (l₂ - l₀) + #K₀ + #(T.lvl l₂))`, in all cases.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Map CycleSearch

/-- The output of the band case: the cycle at `bFc = r630`, the marks at `bIm = r631`. -/
def bandO : List Instr :=
  [.copyN 640 630, .copyN 641 514, .copyN 642 631, .copyN 643 539, .constN 644 1]

/-- The output of the deep fallback: the boundary cycle at `bCy`, the labels at `bL'`. -/
def fbO : List Instr :=
  [.copyN 640 439, .copyN 641 451, .copyN 642 592, .copyN 643 597, .constN 644 0]

/-- `r661 = 1` iff `r168 ≤ 3 r599` (the heavy test of `Y`). -/
def hvBit : Stmt :=
  .seq (block [.addN 662 599 599, .addN 662 662 599])
    (.ifLtN 662 168 (.instr (.constN 661 0)) (.instr (.constN 661 1)))

/-- **The deep case**: the data of `Y`, the two tests, the fallback or the rerouting. -/
def deepAll : Stmt :=
  .seq s10fb <| .seq (eqb 660 584 585) <| .seq hvBit <|
    .ifLtN 430 660 (block fbO) (.ifLtN 430 661 (block fbO) s10rr)

/-- **Miller's simple cycle separator** after the coded triangulation input. -/
def millerFull : Stmt :=
  .seq millerB (.ifLtN 510 580 (.ifLtN 510 581 deepAll (block bandO)) (block bandO))

/-- The input registers of the deep-case continuation and of the output (above `600`). -/
structure S11Regs (k bIm bFc bCv bWC bCN bP1 bI1 bT1 bF1 bM1 bP2 bI2 bT2 bF2 bM2 : ℕ)
    (c : Config) : Prop where
  r605 : c.nreg 605 = k
  r606 : c.nreg 606 = 9 * k
  r607 : c.nreg 607 = 8 * k
  r608 : c.nreg 608 = bIm
  r611 : c.nreg 611 = bP1
  r612 : c.nreg 612 = bI1
  r613 : c.nreg 613 = bT1
  r614 : c.nreg 614 = bF1
  r615 : c.nreg 615 = bM1
  r616 : c.nreg 616 = bP2
  r617 : c.nreg 617 = bI2
  r618 : c.nreg 618 = bT2
  r619 : c.nreg 619 = bF2
  r620 : c.nreg 620 = bM2
  r630 : c.nreg 630 = bFc
  r631 : c.nreg 631 = bIm
  r632 : c.nreg 632 = bCv
  r633 : c.nreg 633 = bWC
  r634 : c.nreg 634 = bCN

section Whole

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

omit [Fintype D] [DecidableEq D] [DecidableEq Q] in
theorem SCycle.k_le_n (C : M.SCycle) {n : ℕ} (vi : Q ≃ Fin n) : C.k ≤ n := by
  classical
  rw [← C.card_verts]
  have := card_le_univ C.verts
  rwa [Fintype.card_congr vi, Fintype.card_fin] at this

theorem sum_moved {cn : Q → Q} {wP : Q → ℕ} {n : ℕ} (vi : Q ≃ Fin n) {wv : ℕ → ℕ}
    (hpos : 0 < ∑ v, wP v)
    (h : ∀ u, wcf cn (wR wP) u = (wv (vi u) : ℝ) / ∑ v, (wP v : ℝ)) :
    ∑ v ∈ range n, wv v = ∑ v, wP v := by
  have hS : (0 : ℝ) < ∑ v, (wP v : ℝ) := by exact_mod_cast hpos
  have h1 : ∑ u, wcf cn (wR wP) u = 1 := by rw [sum_wcf]; exact sum_wR hpos
  simp only [h, ← sum_div] at h1
  rw [div_eq_one_iff_eq hS.ne'] at h1
  rw [sum_range_vi vi]
  exact_mod_cast h1

set_option maxHeartbeats 64000000 in
/-- **Miller's simple cycle separator on the machine.** The face marks lie below
`bF2 + 2 n + 1` (`r642 + k ≤ bF2 + 2 n + 1`), and the memory from `bF2 + 2 n + 1` on is kept. -/
theorem millerFull_spec {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n} {A V : ℕ → ℕ}
    (wP : Q → ℕ) {W : ℕ} {P : Input} {c : Config} {b : ABase} {bIm bMk bTmp bFc : ℕ}
    {bA' bL' bS' bSum' bNx bCy bPos bCv bP1 bI1 bT1 bF1 bM1 bP2 bI2 bT2 bF2 bM2 : ℕ}
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (hk2 : 2 ≤ k)
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hpos : 0 < ∑ v, wP v)
    (hlay : ALay b k n W) (hWt : 11 * k + 3 * ∑ v, wP v + 4 ≤ W)
    (hlay9 : b.bS₂ + n ≤ bIm ∧ bIm + k ≤ bMk ∧ bMk + n ≤ bTmp ∧ bTmp + n ≤ bFc ∧
      bFc + 2 * n + 1 ≤ W)
    (hlay10 : bFc + 2 * n + 1 ≤ bNx ∧ bNx + n ≤ bA' ∧ bA' + k ≤ bL' ∧ bL' + k ≤ bS' ∧
      bS' + k ≤ bSum' ∧ bSum' + k + 1 ≤ bCy ∧ bCy + 3 * k ≤ bPos ∧ bPos + n ≤ W ∧
      bSum' + 3 * k + 4 * n + 1 ≤ W)
    (hlay11 : bPos + n ≤ bCv ∧ bSum' + 3 * k + 4 * n + 1 ≤ bCv ∧ bCv + n ≤ bP1 ∧
      S9Lay k n b.bV bP1 b.bLv bI1 bM1 bT1 bF1 W ∧ bF1 + 2 * n + 1 ≤ bP2 ∧
      S9Lay k n b.bV bP2 b.bLv bI2 bM2 bT2 bF2 W)
    (hc : WordsBounded W c) (hR : ARegs b k n c)
    (hR9 : S9Regs k n b.bV b.bPr b.bLv bIm bMk bTmp bFc c)
    (hR10 : S10Regs k n b.bV b.bLv b.bPr b.bF b.bw bA' bL' bS' bSum' bNx bCy bPos c)
    (hR11 : S11Regs k bIm bFc bCv b.bWC b.bCN bP1 bI1 bT1 bF1 bM1 bP2 bI2 bT2 bF2 bM2 c)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (b.bV + x) = V x)
    (mW : ∀ v, c.nmem (b.bw + vi v) = wP v) (hMk : ∀ v < n, c.nmem (bMk + v) = 0)
    (hz0 : ∀ x ≤ k, c.nmem (bSum' + x) = 0) (hNx0 : ∀ v < n, c.nmem (bNx + v) = 0)
    (hCv0 : ∀ v < n, c.nmem (bCv + v) = 0) (hM10 : ∀ v < n, c.nmem (bM1 + v) = 0)
    (hM20 : ∀ v < n, c.nmem (bM2 + v) = 0) :
    ∃ c' t, Exec P W millerFull c c' t ∧
      t ≤ (231 * Nat.log 2 n + 1134) * k + (60 * n + 152) * Nat.log 2 n + 278 * n + 637 +
        (113 * k + 90 * n + 145) + (281 * k + 51 * n + 69) + (226 * k + 291 * n + 620) ∧
      ∃ (T T₁ : M.SpTree) (l₀ l₂ : ℕ) (K₀ : Finset Q) (cn : Q → Q) (δ x₀ xg : D),
        l₀ < l₂ ∧ l₂ ≤ l₀ + 2 * Nat.sqrt n + 1 ∧ (Nat.sqrt n + 1) * #(T.lvl l₂) ≤ n ∧
        ((l₀ = 0 ∧ K₀ = {T.root}) ∨
          (1 ≤ l₀ ∧ K₀ ⊆ T.lvl l₀ ∧ (Nat.sqrt n + 1) * #(T.lvl l₀) ≤ n)) ∧
        M.vert xg = T.root ∧
        (M.face δ ∉ M.zone (T.low l₂) → M.face (M.α δ) ∉ M.zone (T.low l₂) →
          BdOK (M.comp (T.low l₂) (M.face δ)) x₀) ∧
        c'.nreg 641 = (bandSep T T₁ l₂ cn (wR wP) δ x₀ (M.face xg)).1.k ∧
        (∀ i < (bandSep T T₁ l₂ cn (wR wP) δ x₀ (M.face xg)).1.k,
          c'.nmem (c'.nreg 640 + i) = cd ((bandSep T T₁ l₂ cn (wR wP) δ x₀ (M.face xg)).1.d i)) ∧
        (∀ G : M.Face, G ∈ (bandSep T T₁ l₂ cn (wR wP) δ x₀ (M.face xg)).2 ↔
          (c'.nmem (c'.nreg 642 + fi cd G) ≠ c'.nreg 643 ↔ c'.nreg 644 = 1)) ∧
        SepOK (wR wP) (2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂))
          (bandSep T T₁ l₂ cn (wR wP) δ x₀ (M.face xg)) ∧
        c'.nreg 642 + k ≤ bF2 + 2 * n + 1 ∧ ∀ a, bF2 + 2 * n + 1 ≤ a → c'.nmem a = c.nmem a := by
  classical
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hlay9
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := hlay10
  obtain ⟨u1, u2, u3, hS1, u5, hS2⟩ := hlay11
  have hEnd : bIm + k ≤ bF2 + 2 * n + 1 ∧ bFc + 2 * n + 1 ≤ bF2 + 2 * n + 1 ∧
      bL' + k ≤ bF2 + 2 * n + 1 ∧ bCv ≤ bF2 + 2 * n + 1 ∧ bI1 + k ≤ bF2 + 2 * n + 1 ∧
      bI2 + k ≤ bF2 + 2 * n + 1 := by
    have := hS1.l6; have := hS1.l7; have := hS1.l8; have := hS1.l9
    have := hS2.l6; have := hS2.l7; have := hS2.l8; have := hS2.l9
    omega
  have hl := hlay
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19,
    l20, l21, l22, lW⟩ := hl
  obtain ⟨c₂, t₂, e₂, ht₂, T, T₁, l₀, l₂, K₀, cn, δ, hl02, hl2s, h3, hK, h514, hd, him, hz,
    hband, hbfs, ⟨H, c₀, hI⟩, hcn, hδ, hA, hB, hlight, h160, hroot, hroot₁, mL, hPr, hcf, mA₂,
    mV₂, mW₂, ⟨fdD, hfdD, mF₂⟩, hhi, fr₂, q500, q566, hCN⟩ :=
    millerB_spec (P := P) wP hM hT3 hk2 hAcd hφ hV hpos hlay hWt ⟨hb1, hb2, hb3, hb4, hb5⟩ hc
      hR hR9 mA mV mW hMk
  have hw₂ := e₂.wb_right
  have G₂ : ∀ r, 430 ≤ r → s9band.wr r = false → c₂.nreg r = c.nreg r := fun r a h =>
    e₂.nreg_of_wr (millerB_wr a h)
  have g510 : c₂.nreg 510 = 0 := (G₂ 510 (by omega) (by decide)).trans hR9.r510
  have hl2 : 1 ≤ l₂ := by omega
  have hxg : M.vert (fdD T.root) = T.root := hfdD _
  have hg₀ : M.face (fdD T.root) ∈ M.zone (T.low l₂) :=
    face_mem_zone (by rw [hfdD]; exact root_mem_low hbfs hl2)
  have hr₁ : (vi T₁.root : ℕ) = 0 := by rw [hroot₁]; exact hroot
  have hW1 : 1 ≤ W := by omega
  by_cases hdeep : M.face δ ∉ M.zone (T.low l₂) ∧ M.face (M.α δ) ∉ M.zone (T.low l₂)
  · -- the deep case
    have f580 : c₂.nreg 510 < c₂.nreg 580 := by rw [g510]; exact (hz.2 hdeep).1
    have f581 : c₂.nreg 510 < c₂.nreg 581 := by rw [g510]; exact (hz.2 hdeep).2
    have hvδ : l₂ ≤ T.height (M.vert δ) := by
      have hv : M.vert δ ∉ T.low l₂ := fun h => hdeep.1 (face_mem_zone h)
      rw [mem_low] at hv; omega
    have hl2n' : l₂ < n := by
      have := height_lt_card hbfs (M.vert δ)
      rw [Fintype.card_congr vi, Fintype.card_fin] at this
      omega
    have hl2n : l₂ ≤ n := hl2n'.le
    -- 1. the component `Y`
    obtain ⟨c₃, t₃, e₃, ht₃, hlab₃, h599, h168, hm₃, hr₃, ho₃⟩ :=
      s10hvy_spec (P := P) (T := T) (T₁ := T₁) (vi := vi) (V := V) (δ := δ) (bPr := b.bPr)
        (bLv := b.bLv) wP hM hbfs hT3 hl2 hl2n hAcd hφ hV hfdD hdeep.1
        ⟨by omega, by omega, by omega, by omega, by omega, d3, d4, d5, d9⟩ (by omega) hw₂ h160
        q500 ((G₂ 535 (by omega) (by decide)).trans hR9.r535)
        ((G₂ 502 (by omega) (by decide)).trans hR9.r502)
        ((G₂ 505 (by omega) (by decide)).trans hR9.r505)
        ((G₂ 530 (by omega) (by decide)).trans hR9.r530)
        ((G₂ 567 (by omega) (by decide)).trans hR9.r567)
        ((fr₂ 591 (by omega)).trans hR10.r591) ((fr₂ 592 (by omega)).trans hR10.r592)
        ((fr₂ 593 (by omega)).trans hR10.r593) ((fr₂ 594 (by omega)).trans hR10.r594)
        ((fr₂ 595 (by omega)).trans hR10.r595) ((fr₂ 596 (by omega)).trans hR10.r596)
        mA₂ mV₂ mL hPr mF₂ mW₂ (fun x hx => by rw [hhi _ (by omega)]; exact hz0 x hx)
    have hw₃ := e₃.wb_right
    have K₃ : ∀ r, 430 ≤ r → r < 444 → c₃.nreg r = c.nreg r := fun r a b' => by
      rw [hr₃ r (by omega) (by omega) (by omega) (by omega)]
      exact G₂ r a (by interval_cases r <;> decide)
    have M₃ : ∀ a, a < bA' → c₃.nmem a = c₂.nmem a := fun a ha => hm₃ a (Or.inl ha)
    -- 2. the ancestors
    have hB₃ : BR 0 b.bV bL' k (c₃.nreg 437) bNx bCy bPos n b.bLv b.bPr (c₃.nreg 444)
        (c₃.nreg 445) (c₃.nreg 446) c₃ :=
      ⟨(K₃ 430 (by omega) (by omega)).trans hR10.r430, (K₃ 431 (by omega) (by omega)).trans hR10.r431,
        (K₃ 432 (by omega) (by omega)).trans hR10.r432, (K₃ 433 (by omega) (by omega)).trans hR10.r433,
        (K₃ 434 (by omega) (by omega)).trans hR10.r434, (K₃ 435 (by omega) (by omega)).trans hR10.r435,
        (K₃ 436 (by omega) (by omega)).trans hR10.r436, rfl,
        (K₃ 438 (by omega) (by omega)).trans hR10.r438, (K₃ 439 (by omega) (by omega)).trans hR10.r439,
        (K₃ 440 (by omega) (by omega)).trans hR10.r440, (K₃ 441 (by omega) (by omega)).trans hR10.r441,
        (K₃ 442 (by omega) (by omega)).trans hR10.r442, (K₃ 443 (by omega) (by omega)).trans hR10.r443,
        rfl, rfl, rfl⟩
    obtain ⟨c₄, t₄, e₄, ht₄, g584, g585, htop, hm₄, hr₄, ho₄⟩ := s9top_topA (P := P) (T := T)
      (T₁ := T₁) (vi := vi) (V := V) (δ := δ) (l := l₂) hAcd hV ⟨by omega, by omega, by omega,
        by omega⟩ c₃ hw₃ hB₃
      (by rw [hr₃ 500 (by omega) (by omega) (by omega) (by omega)]; exact q500)
      (by rw [hr₃ 566 (by omega) (by omega) (by omega) (by omega)]; exact q566)
      (by rw [hroot₁, hbfs.root]; omega)
      (fun v => by have := (vi v).2; rw [M₃ _ (by omega)]; exact mL v)
      (fun v h => by have := (vi v).2; rw [M₃ _ (by omega)]; exact hPr v h)
      (fun x hx => by rw [M₃ _ (by omega)]; exact mA₂ x hx)
      (fun x hx => by rw [M₃ _ (by omega)]; exact mV₂ x hx)
    have hw₄ := e₄.wb_right
    have K₄ : ∀ r, 430 ≤ r → r < 444 → c₄.nreg r = c₃.nreg r := fun r a b' =>
      hr₄ r (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega)
    -- 3. the boundary cycle
    have hB₄ : BR 0 b.bV bL' k (c₄.nreg 437) bNx bCy bPos n b.bLv b.bPr (c₄.nreg 444)
        (c₄.nreg 445) (c₄.nreg 446) c₄ :=
      ⟨(K₄ 430 (by omega) (by omega)).trans hB₃.r330, (K₄ 431 (by omega) (by omega)).trans hB₃.r331,
        (K₄ 432 (by omega) (by omega)).trans hB₃.r332, (K₄ 433 (by omega) (by omega)).trans hB₃.r333,
        (K₄ 434 (by omega) (by omega)).trans hB₃.r334, (K₄ 435 (by omega) (by omega)).trans hB₃.r335,
        (K₄ 436 (by omega) (by omega)).trans hB₃.r336, rfl,
        (K₄ 438 (by omega) (by omega)).trans hB₃.r338, (K₄ 439 (by omega) (by omega)).trans hB₃.r339,
        (K₄ 440 (by omega) (by omega)).trans hB₃.r340, (K₄ 441 (by omega) (by omega)).trans hB₃.r341,
        (K₄ 442 (by omega) (by omega)).trans hB₃.r342, (K₄ 443 (by omega) (by omega)).trans hB₃.r343,
        rfl, rfl, rfl⟩
    have M₄ : ∀ a, a < bA' → c₄.nmem a = c₂.nmem a := fun a ha => by rw [hm₄]; exact M₃ a ha
    have q597 : c₄.nreg 597 = c₃.nreg 597 :=
      hr₄ 597 (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)
    obtain ⟨c₅, t₅, e₅, ht₅, x₀, hok, hx₀, h451, hcy, hpos₅, hm₅, hr₅, ho₅⟩ := s10cyc_spec (P := P)
      (T := T) (vi := vi) (δ := δ) hM hbfs hl2 hAcd hV hdeep.1
      ⟨by omega, by omega, by omega, by omega, d7, d8⟩ hw₄ hB₄
      (fun x hx => by rw [M₄ _ (by omega)]; exact mA₂ x hx)
      (fun x hx => by rw [M₄ _ (by omega)]; exact mV₂ x hx)
      (fun y => by
        have := (cd y).2
        rw [hm₄, q597]; exact hlab₃ y)
      (fun v hv => by rw [M₄ _ (by omega), hhi _ (by omega)]; exact hNx0 v hv)
    have hw₅ := e₅.wb_right
    set Y := M.comp (T.low l₂) (M.face δ)
    set C := bdCycle Y x₀ hok
    have R5 : ∀ r, 474 ≤ r → r ≠ 584 → r ≠ 585 → r ≠ 586 → r ≠ 597 → r ≠ 598 → r ≠ 599 →
        c₅.nreg r = c₂.nreg r := fun r a b' d e f g h' => by
      rw [hr₅ r (by omega) (by omega) (Or.inr (by omega)),
        hr₄ r (by omega) (by omega) (Or.inr a) b' d e, hr₃ r (by omega) f g h']
    have I5 : ∀ r, 600 ≤ r → c₅.nreg r = c.nreg r := fun r a => by
      rw [R5 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        fr₂ r (by omega)]
    have hlab₅ : ∀ y : D, c₅.nmem (bL' + (cd y : ℕ) / 3) = c₅.nreg 597 ↔ M.face y ∈ Y := by
      intro y
      have := (cd y).2
      rw [hm₅ _ (Or.inr (by omega)) (fun h => by omega) (fun h => by omega),
        hr₅ 597 (by omega) (by omega) (Or.inr (by omega)), hm₄, q597]
      exact hlab₃ y
    have N5 : ∀ a, a < bNx → c₅.nmem a = c₂.nmem a := fun a ha => by
      rw [hm₅ a (Or.inl ha) (fun h => by omega) (fun h => by omega)]; exact M₄ a (by omega)
    have Z5 : ∀ a, bCv ≤ a → c₅.nmem a = c.nmem a := fun a ha => by
      rw [hm₅ a (Or.inr (by omega)) (fun h => by omega) (fun h => by omega), hm₄,
        hm₃ a (Or.inr (by omega)), hhi a (by omega)]
    have h584₅ : c₅.nreg 584 = vi (topA T T₁ l₂ (M.vert δ)) := by
      rw [hr₅ 584 (by omega) (by omega) (Or.inr (by omega))]; exact g584
    have h585₅ : c₅.nreg 585 = vi (topA T T₁ l₂ (M.vert (M.α δ))) := by
      rw [hr₅ 585 (by omega) (by omega) (Or.inr (by omega))]; exact g585
    have h599₅ : c₅.nreg 599 = ∑ v ∈ ins Y, wP v := by
      rw [hr₅ 599 (by omega) (by omega) (Or.inr (by omega)),
        hr₄ 599 (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega)]
      exact h599
    have h168₅ : c₅.nreg 168 = ∑ v, wP v := by
      rw [hr₅ 168 (by omega) (by omega) (Or.inl (by omega)),
        hr₄ 168 (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega)]
      exact h168
    have hB₅ : BR 0 b.bV bL' k (c₅.nreg 437) bNx bCy bPos n b.bLv b.bPr (c₄.nreg 444)
        (c₅.nreg 445) (c₄.nreg 446) c₅ :=
      hB₄.of2 (fun r a b' d e => hr₅ r d e (Or.inl (by omega))) rfl rfl
    -- 4. the two tests
    obtain ⟨c₆, t₆, e₆, ht₆, b₆, i₆, k₆, m₆, o₆⟩ := eqb_exec (P := P) hW1 660 584 585 c₅ hw₅
    have hw₆ := e₆.wb_right
    have hle : ∑ v ∈ ins Y, wP v ≤ ∑ v, wP v := sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
    obtain ⟨c₇, t₇, e₇, ht₇, b₇, i₇, k₇, m₇, o₇⟩ : ∃ c₇ t₇, Exec P W hvBit c₆ c₇ t₇ ∧ t₇ ≤ 5 ∧
        c₇.nreg 661 ≤ 1 ∧ (c₇.nreg 661 = 1 ↔ c₅.nreg 168 ≤ 3 * c₅.nreg 599) ∧
        (∀ r, r ≠ 661 → r ≠ 662 → c₇.nreg r = c₆.nreg r) ∧ c₇.nmem = c₆.nmem ∧
        c₇.output = c₆.output := by
      have v599 : c₆.nreg 599 = c₅.nreg 599 := k₆ 599 (by omega)
      have v168 : c₆.nreg 168 = c₅.nreg 168 := k₆ 168 (by omega)
      obtain ⟨ca, ta, ea, hta, qa, ka, ma, oa⟩ : ∃ ca ta, Exec P W
          (block [.addN 662 599 599, .addN 662 662 599]) c₆ ca ta ∧ ta = 2 ∧
          ca.nreg 662 = 3 * c₅.nreg 599 ∧ (∀ r, r ≠ 662 → ca.nreg r = c₆.nreg r) ∧
          ca.nmem = c₆.nmem ∧ ca.output = c₆.output := by
        exec_block
        · rw [v599, h599₅]; omega
        · config_simp; rw [v599, h599₅]; omega
        · refine ⟨rfl, by config_simp; rw [v599]; omega, fun r hr => ?_, rfl, rfl⟩
          config_simp; simp only [upd_apply]; split_ifs <;> omega
      have hwa := ea.wb_right
      have u168 : ca.nreg 168 = c₅.nreg 168 := (ka 168 (by omega)).trans v168
      by_cases hs : ca.nreg 662 < ca.nreg 168
      · refine ⟨_, _, .seq ea (.ifLtN_true hs (Exec.constN hwa 661 0 (by omega))), by omega,
          by simp, ?_, fun r a b' => by simp [upd_other _ _ _ a, ka r b'], by simp [ma],
          by simp [oa]⟩
        simp only [Config.nreg_mk, upd_same]
        rw [qa, u168] at hs; omega
      · refine ⟨_, _, .seq ea (.ifLtN_false hs (Exec.constN hwa 661 1 hW1)), by omega,
          by simp, ?_, fun r a b' => by simp [upd_other _ _ _ a, ka r b'], by simp [ma],
          by simp [oa]⟩
        simp only [Config.nreg_mk, upd_same]
        rw [qa, u168] at hs; simp only [true_iff]; omega
    have hw₇ := e₇.wb_right
    have R7 : ∀ r, r ≠ 660 → r ≠ 661 → r ≠ 662 → c₇.nreg r = c₅.nreg r := fun r a b' d => by
      rw [k₇ r b' d, k₆ r a]
    have M7 : c₇.nmem = c₅.nmem := by rw [m₇, m₆]
    have t660 : c₇.nreg 660 = 1 ↔ topA T T₁ l₂ (M.vert δ) = topA T T₁ l₂ (M.vert (M.α δ)) := by
      rw [k₇ 660 (by omega) (by omega), i₆, h584₅, h585₅, Fin.val_inj, vi.apply_eq_iff_eq]
    have t661 : c₇.nreg 661 = 1 ↔ 1 / 3 ≤ ∑ v ∈ ins Y, wR wP v := by
      rw [i₇, h168₅, h599₅]; exact (third_le_iff hpos _).symm
    have v430 : c₇.nreg 430 = 0 := by
      rw [R7 430 (by omega) (by omega) (by omega)]; exact hB₅.r330
    have b660 : c₇.nreg 660 ≤ 1 := by rw [k₇ 660 (by omega) (by omega)]; exact b₆
    -- 5. the fallback output
    obtain ⟨c₈, t₈, e₈, ht₈, q640, q641, q642, q643, q644, m₈, o₈⟩ : ∃ c₈ t₈,
        Exec P W (block fbO) c₇ c₈ t₈ ∧ t₈ = 5 ∧ c₈.nreg 640 = bCy ∧
        c₈.nreg 641 = c₅.nreg 451 ∧ c₈.nreg 642 = bL' ∧ c₈.nreg 643 = c₅.nreg 597 ∧
        c₈.nreg 644 = 0 ∧ c₈.nmem = c₇.nmem ∧ c₈.output = c₇.output := by
      have v439 : c₇.nreg 439 = bCy := by
        rw [R7 439 (by omega) (by omega) (by omega)]; exact hB₅.r339
      have v592 : c₇.nreg 592 = bL' := by
        rw [R7 592 (by omega) (by omega) (by omega),
          R5 592 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
          fr₂ 592 (by omega)]; exact hR10.r592
      have v451 := R7 451 (by omega) (by omega) (by omega)
      have v597 := R7 597 (by omega) (by omega) (by omega)
      unfold fbO
      exec_block
      all_goals try omega
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
      all_goals config_simp
      all_goals first | rfl | assumption
    have fbOut : (topA T T₁ l₂ (M.vert δ) = topA T T₁ l₂ (M.vert (M.α δ)) ∨
        1 / 3 ≤ ∑ v ∈ ins Y, wR wP v) →
        c₈.nreg 641 = (bandSep T T₁ l₂ cn (wR wP) δ x₀ (M.face (fdD T.root))).1.k ∧
        (∀ i < (bandSep T T₁ l₂ cn (wR wP) δ x₀ (M.face (fdD T.root))).1.k,
          c₈.nmem (c₈.nreg 640 + i) =
            cd ((bandSep T T₁ l₂ cn (wR wP) δ x₀ (M.face (fdD T.root))).1.d i)) ∧
        (∀ G : M.Face, G ∈ (bandSep T T₁ l₂ cn (wR wP) δ x₀ (M.face (fdD T.root))).2 ↔
          (c₈.nmem (c₈.nreg 642 + fi cd G) ≠ c₈.nreg 643 ↔ c₈.nreg 644 = 1)) ∧
        SepOK (wR wP) (2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂))
          (bandSep T T₁ l₂ cn (wR wP) δ x₀ (M.face (fdD T.root))) := fun hfb => by
      have r := deep_fallback_sep hM hT3 hbfs (wR_nonneg wP) (sum_wR hpos).le hI hl02 hcn hδ hA hB
        hlight hdeep.1 hdeep.2 hok (g₀ := M.face (fdD T.root)) hfb
      rw [r.1]
      refine ⟨by rw [q641]; exact h451, fun i hi => by rw [q640, m₈, M7]; exact hcy i hi,
        fun G => ?_, r.2 _ hg₀⟩
      rw [q642, q643, q644, m₈, M7]
      have := hlab₅ (M.face_surjective G).choose
      rw [(M.face_surjective G).choose_spec] at this
      show G ∈ Y ↔ (c₅.nmem (bL' + fi cd G) ≠ c₅.nreg 597 ↔ 0 = 1)
      simp only [ne_eq, zero_ne_one, iff_false, not_not]
      exact this.symm
    by_cases x660 : c₇.nreg 430 < c₇.nreg 660
    · have h660 : c₇.nreg 660 = 1 := by rw [v430] at x660; omega
      obtain ⟨o1, o2, o3, o4⟩ := fbOut (Or.inl (t660.1 h660))
      exact ⟨c₈, _, .seq e₂ (.ifLtN_true f580 (.ifLtN_true f581 (.seq (.seq e₃ (.seq e₄ e₅))
        (.seq e₆ (.seq e₇ (.ifLtN_true x660 e₈)))))), by omega, T, T₁, l₀, l₂, K₀, cn, δ, x₀,
        fdD T.root, hl02, hl2s, h3, hK, hxg, fun _ _ => hok, o1, o2, o3, o4,
        by rw [q642]; exact hEnd.2.2.1, fun a ha => by rw [m₈, M7]; exact Z5 a (hEnd.2.2.2.1.trans ha)⟩
    by_cases x661 : c₇.nreg 430 < c₇.nreg 661
    · have h661 : c₇.nreg 661 = 1 := by rw [v430] at x661; omega
      obtain ⟨o1, o2, o3, o4⟩ := fbOut (Or.inr (t661.1 h661))
      exact ⟨c₈, _, .seq e₂ (.ifLtN_true f580 (.ifLtN_true f581 (.seq (.seq e₃ (.seq e₄ e₅))
        (.seq e₆ (.seq e₇ (.ifLtN_false x660 (.ifLtN_true x661 e₈))))))), by omega, T, T₁, l₀,
        l₂, K₀, cn, δ, x₀, fdD T.root, hl02, hl2s, h3, hK, hxg, fun _ _ => hok, o1, o2, o3, o4,
        by rw [q642]; exact hEnd.2.2.1, fun a ha => by rw [m₈, M7]; exact Z5 a (hEnd.2.2.2.1.trans ha)⟩
    -- 6. the rerouting
    have hab : topA T T₁ l₂ (M.vert δ) ≠ topA T T₁ l₂ (M.vert (M.α δ)) := fun h' =>
      x660 (by rw [v430, t660.2 h']; omega)
    have hlt3 : ¬ 1 / 3 ≤ ∑ v ∈ ins Y, wR wP v := fun h' => x661 (by rw [v430, t661.2 h']; omega)
    obtain ⟨hCp, hC⟩ := bdCycle_spec hok
    have hCk : C.k ≤ n := SCycle.k_le_n C vi
    have hKk : (T₁.fcycle δ).k ≤ n := SCycle.k_le_n _ vi
    have hfi : ∀ x : D, fi cd (M.face x) = (cd x : ℕ) / 3 :=
      (coded_of_tmark (T := T₁) (k := k) (cd := cd) (vi := vi) (A := A)
        (Pr := fun u => c₂.nmem (b.bPr + u)) hAcd hφ (fun v h => hPr v h)).fi_face
    have V7 : ∀ r, 600 ≤ r → r < 660 → c₇.nreg r = c.nreg r := fun r a b' => by
      rw [R7 r (by omega) (by omega) (by omega)]; exact I5 r a
    have W7 : ∀ r, 474 ≤ r → r < 590 → r ≠ 584 → r ≠ 585 → r ≠ 586 → r ≠ 597 → r ≠ 598 →
        r ≠ 599 → c₇.nreg r = c₂.nreg r := fun r a b' d e f g h' i' => by
      rw [R7 r (by omega) (by omega) (by omega)]; exact R5 r a d e f g h' i'
    have N7 : ∀ a, a < bNx → c₇.nmem a = c₂.nmem a := fun a ha => by rw [M7]; exact N5 a ha
    have Z7 : ∀ a, bCv ≤ a → c₇.nmem a = c.nmem a := fun a ha => by rw [M7]; exact Z5 a ha
    obtain ⟨c₉, t₉, e₉, ht₉, r641, r640, r642, r642', rmem, ro⟩ :=
      s10rr_spec (T := T) (T₁ := T₁) (C := C) (cn := cn) (cd := cd) (vi := vi) (A := A)
        (V := V) (P := P) (c := c₇) (bV := b.bV) (bL := bL') (h := c₅.nreg 437) (bNx := bNx)
        (bCy := bCy) (bPos := bPos) (bLv := b.bLv) (bPr := b.bPr) (l := c₄.nreg 444)
        (x₀ := c₅.nreg 445) (u := c₄.nreg 446) (bFc := bFc) (bIm := bIm) (bF := b.bF)
        (bCv := bCv) (bWC := b.bWC) (bCN := b.bCN) (l₀ := l₀) (l₂ := l₂) (fl := c₂.nreg 539)
        (hY := c₅.nreg 597) (bP1 := bP1) (bI1 := bI1) (bM1 := bM1) (bT1 := bT1) (bF1 := bF1)
        (bP2 := bP2) (bI2 := bI2) (bM2 := bM2) (bT2 := bT2) (bF2 := bF2) (H := H) (K₀ := K₀)
        (c₀ := c₀) (δ := δ) (wP := wP) (fdD := fdD) hM hT3 hbfs hI hl02 hδ hcn hpos hdeep.1
        hdeep.2 hCp hC hab hAcd hφ hV hfi hfdD hr₁
        ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
          by omega, by omega, u1, u3, by omega, by omega, by omega, u5, by omega, by omega⟩
        hS1 hS2 hw₇ (hB₅.of fun r a b' => R7 r (by omega) (by omega) (by omega))
        ((R7 451 (by omega) (by omega) (by omega)).trans h451)
        ((R7 584 (by omega) (by omega) (by omega)).trans h584₅)
        ((R7 585 (by omega) (by omega) (by omega)).trans h585₅)
        ((W7 500 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)).trans q500)
        ((W7 514 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)).trans h514)
        (W7 539 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega))
        ((W7 566 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)).trans q566)
        (R7 597 (by omega) (by omega) (by omega))
        ((R7 595 (by omega) (by omega) (by omega)).trans ((R5 595 (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega)).trans
          ((fr₂ 595 (by omega)).trans hR10.r595)))
        ((V7 605 (by omega) (by omega)).trans hR11.r605)
        ((V7 606 (by omega) (by omega)).trans hR11.r606)
        ((V7 607 (by omega) (by omega)).trans hR11.r607)
        ((V7 608 (by omega) (by omega)).trans hR11.r608)
        ((V7 630 (by omega) (by omega)).trans hR11.r630)
        ((V7 632 (by omega) (by omega)).trans hR11.r632)
        ((V7 633 (by omega) (by omega)).trans hR11.r633)
        ((V7 634 (by omega) (by omega)).trans hR11.r634)
        ((V7 611 (by omega) (by omega)).trans hR11.r611)
        ((V7 612 (by omega) (by omega)).trans hR11.r612)
        ((V7 613 (by omega) (by omega)).trans hR11.r613)
        ((V7 614 (by omega) (by omega)).trans hR11.r614)
        ((V7 615 (by omega) (by omega)).trans hR11.r615)
        ((V7 616 (by omega) (by omega)).trans hR11.r616)
        ((V7 617 (by omega) (by omega)).trans hR11.r617)
        ((V7 618 (by omega) (by omega)).trans hR11.r618)
        ((V7 619 (by omega) (by omega)).trans hR11.r619)
        ((V7 620 (by omega) (by omega)).trans hR11.r620)
        (fun x hx => by rw [N7 x (by omega)]; exact mA₂ x hx)
        (fun x hx => by rw [N7 _ (by omega)]; exact mV₂ x hx)
        (fun v => by have := (vi v).2; rw [N7 _ (by omega)]; exact mL v)
        (fun v hv => by have := (vi v).2; rw [N7 _ (by omega)]; exact hPr v hv)
        (fun i hi => by rw [M7]; exact hcy i hi)
        (fun i hi => by rw [M7]; exact hpos₅ i hi)
        (fun i hi => by rw [N7 _ (by omega)]; exact hd i hi)
        (fun G => by have := fi_lt' cd G; rw [N7 _ (by omega)]; exact him G)
        (fun v => by have := (vi v).2; rw [N7 _ (by omega)]; exact mF₂ v)
        (fun y => by rw [M7]; exact hlab₅ y)
        (fun v => by have := (vi v).2; rw [N7 _ (by omega)]; exact hcf v)
        (fun v => by have := (vi v).2; rw [N7 _ (by omega)]; exact hCN hl2n' v)
        (fun v hv => by rw [Z7 _ (by omega)]; exact hCv0 v hv)
        (by
          rw [sum_congr rfl fun v hv => N7 (b.bWC + v) (by have := mem_range.1 hv; omega)]
          rw [sum_moved vi hpos (wv := fun v => c₂.nmem (b.bWC + v)) hcf]; omega)
        (fun v hv => by
          rw [Z7 _ (by have := hS1.l6; have := hS1.l7; omega)]; exact hM10 v hv)
        (fun v hv => by
          rw [Z7 _ (by
            have := hS1.l6; have := hS1.l7; have := hS1.l8; have := hS1.l9
            have := hS2.l6; have := hS2.l7; omega)]
          exact hM20 v hv)
    have hbs : bandSep T T₁ l₂ cn (wR wP) δ x₀ (M.face (fdD T.root)) =
        deepPick T₁ C δ (topA T T₁ l₂ (M.vert δ)) (topA T T₁ l₂ (M.vert (M.α δ)))
          (deepWant T₁ cn (wR wP) Y δ) (M.face (fdD T.root)) := by
      rw [bandSep_of_deep hdeep.1 hdeep.2 hok, deepSep,
        ite_eq_right_of_eq_false _ _ (eq_false fun h' => h'.elim hab hlt3)]
    rw [hroot₁] at r641 r640 r642
    have hsep := band_separator_explicit hM hT3 hbfs (wR_nonneg wP) (sum_wR hpos).le hI hl02 hcn
      hδ hA hB hlight (x₀ := x₀) (fun _ _ => hok.2) hg₀
    refine ⟨c₉, _, .seq e₂ (.ifLtN_true f580 (.ifLtN_true f581 (.seq (.seq e₃ (.seq e₄ e₅))
      (.seq e₆ (.seq e₇ (.ifLtN_false x660 (.ifLtN_false x661 e₉))))))), by omega, T, T₁, l₀, l₂,
      K₀, cn, δ, x₀, fdD T.root, hl02, hl2s, h3, hK, hxg, fun _ _ => hok, ?_, ?_, ?_, hsep,
      ?_, fun a ha => by rw [rmem a ha]; exact Z7 a (hEnd.2.2.2.1.trans ha)⟩
    · rw [hbs]; exact r641
    · rw [hbs]; exact r640
    · rw [hbs]; exact r642
    · rcases r642' with h | h <;> rw [h]
      · exact hEnd.2.2.2.2.1
      · exact hEnd.2.2.2.2.2
  · -- the band case
    have hnb : ¬ (0 < c₂.nreg 580 ∧ 0 < c₂.nreg 581) := fun h => hdeep (hz.1 h)
    obtain ⟨hbs, hsep⟩ := hband hnb δ (M.face (fdD T.root))
    have hzb : M.face δ ∈ M.zone (T.low l₂) ∨ M.face (M.α δ) ∈ M.zone (T.low l₂) := by
      by_contra hn; push Not at hn; exact hdeep hn
    obtain ⟨c₃, t₃, e₃, ht₃, q640, q641, q642, q643, q644, m₃, o₃⟩ : ∃ c₃ t₃,
        Exec P W (block bandO) c₂ c₃ t₃ ∧ t₃ = 5 ∧ c₃.nreg 640 = bFc ∧
        c₃.nreg 641 = c₂.nreg 514 ∧ c₃.nreg 642 = bIm ∧ c₃.nreg 643 = c₂.nreg 539 ∧
        c₃.nreg 644 = 1 ∧ c₃.nmem = c₂.nmem ∧ c₃.output = c₂.output := by
      have v630 : c₂.nreg 630 = bFc := (fr₂ 630 (by omega)).trans hR11.r630
      have v631 : c₂.nreg 631 = bIm := (fr₂ 631 (by omega)).trans hR11.r631
      unfold bandO
      exec_block
      all_goals try omega
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
      all_goals config_simp
      all_goals first | rfl | assumption
    have hout : ∀ c' : Config, c'.nreg 641 = c₂.nreg 514 → c'.nreg 640 = bFc → c'.nreg 642 = bIm →
        c'.nreg 643 = c₂.nreg 539 → c'.nreg 644 = 1 → c'.nmem = c₂.nmem →
        c'.nreg 641 = (bandSep T T₁ l₂ cn (wR wP) δ δ (M.face (fdD T.root))).1.k ∧
        (∀ i < (bandSep T T₁ l₂ cn (wR wP) δ δ (M.face (fdD T.root))).1.k,
          c'.nmem (c'.nreg 640 + i) =
            cd ((bandSep T T₁ l₂ cn (wR wP) δ δ (M.face (fdD T.root))).1.d i)) ∧
        (∀ G : M.Face, G ∈ (bandSep T T₁ l₂ cn (wR wP) δ δ (M.face (fdD T.root))).2 ↔
          (c'.nmem (c'.nreg 642 + fi cd G) ≠ c'.nreg 643 ↔ c'.nreg 644 = 1)) :=
      fun c' a1 a2 a3 a4 a5 a6 => by
        rw [hbs]
        refine ⟨by rw [a1]; exact h514, fun i hi => by rw [a2, a6]; exact hd i hi,
          fun G => by rw [a3, a4, a5, a6]; simp only [iff_true]; exact (him G).symm⟩
    by_cases a : c₂.nreg 510 < c₂.nreg 580
    · have a' : ¬ c₂.nreg 510 < c₂.nreg 581 := fun h =>
        hnb ⟨by rw [g510] at a; exact a, by rw [g510] at h; exact h⟩
      exact ⟨c₃, _, .seq e₂ (.ifLtN_true a (.ifLtN_false a' e₃)), by omega, T, T₁, l₀, l₂, K₀,
        cn, δ, δ, fdD T.root, hl02, hl2s, h3, hK, hxg, fun h1 h2 => absurd ⟨h1, h2⟩ hdeep,
        (hout c₃ q641 q640 q642 q643 q644 m₃).1, (hout c₃ q641 q640 q642 q643 q644 m₃).2.1,
        (hout c₃ q641 q640 q642 q643 q644 m₃).2.2, by rw [hbs]; exact hsep,
        by rw [q642]; exact hEnd.1, fun a ha => by rw [m₃]; exact hhi a (hEnd.2.1.trans ha)⟩
    · exact ⟨c₃, _, .seq e₂ (.ifLtN_false a e₃), by omega, T, T₁, l₀, l₂, K₀,
        cn, δ, δ, fdD T.root, hl02, hl2s, h3, hK, hxg, fun h1 h2 => absurd ⟨h1, h2⟩ hdeep,
        (hout c₃ q641 q640 q642 q643 q644 m₃).1, (hout c₃ q641 q640 q642 q643 q644 m₃).2.1,
        (hout c₃ q641 q640 q642 q643 q644 m₃).2.2, by rw [hbs]; exact hsep,
        by rw [q642]; exact hEnd.1, fun a ha => by rw [m₃]; exact hhi a (hEnd.2.1.trans ha)⟩

end Whole

end MillerProg

end PlanarSeparator
