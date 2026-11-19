module

public import PlanarSeparator.Machine.MillerFull
public import PlanarSeparator.Machine.MillerDeep

/-!
# Miller's separator on the machine: the band case and the deep fallback as one program

`millerC = millerB ; if 0 < r580 ∧ 0 < r581 then (s10hvy ; s9top ; s10cyc)`: after steps 1–9 in
the band case (`MillerProg.millerB_spec`), in the deep case of `PlanarSeparator.Map.bandSep` the
component `Y` of `δ` at level `l₂` (labels, weight of its strict inside: `s10hvy_spec`), the two
ancestors at level `l₂` of the ends of `δ` (`s9top_topA`) and the boundary cycle of `Y` from a
dart leaving it (`s10cyc_spec`).

**`millerC_spec`**: in the band case, the explicit separator `bandSep` is the cycle of `δ` in
`T₁` with its inside (on the machine at `bFc`, `bIm`) and is a separator (`SepOK`); in the deep
case the machine holds the tests of `PlanarSeparator.Map.deepSep` (`r584 = r585` for the
ancestors, `r168 ≤ 3 r599` for the weight of `Y`), the faces of `Y` (label `r597` at `bL'`) and
the darts of `bdCycle Y x₀` at `bCy`, and in the fallback branch (one of the two tests) `bandSep`
is `(bdCycle Y x₀, Y)` and is a separator. The rerouting branch of `deepSep` is not covered.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Map CycleSearch

/-- The deep-case passes: the component `Y`, the two ancestors, the boundary cycle of `Y`. -/
def s10fb : Stmt := .seq s10hvy (.seq s9top s10cyc)

/-- **Steps 1–9 with the band case and the data of the deep case.** -/
def millerC : Stmt := .seq millerB (.ifLtN 510 580 (.ifLtN 510 581 s10fb .skip) .skip)

/-- The input registers of the deep-case passes (above `430`, untouched by `millerB`). -/
structure S10Regs (k n bV bLv bPr bF bw bA' bL' bS' bSum' bNx bCy bPos : ℕ) (c : Config) :
    Prop where
  r591 : c.nreg 591 = bA'
  r592 : c.nreg 592 = bL'
  r593 : c.nreg 593 = bS'
  r594 : c.nreg 594 = bSum'
  r595 : c.nreg 595 = bF
  r596 : c.nreg 596 = bw
  r430 : c.nreg 430 = 0
  r431 : c.nreg 431 = 1
  r432 : c.nreg 432 = 3
  r433 : c.nreg 433 = 0
  r434 : c.nreg 434 = bV
  r435 : c.nreg 435 = bL'
  r436 : c.nreg 436 = 3 * k
  r438 : c.nreg 438 = bNx
  r439 : c.nreg 439 = bCy
  r440 : c.nreg 440 = bPos
  r441 : c.nreg 441 = n
  r442 : c.nreg 442 = bLv
  r443 : c.nreg 443 = bPr

theorem millerB_wr {r : ℕ} (h : 430 ≤ r) (h' : s9band.wr r = false) : millerB.wr r = false := by
  have h1 : millerA.wr r = false := Stmt.wr_of_wmax (by have := millerA_wmax; omega)
  simp [millerB, Stmt.wr, h1, h']

section Whole

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

set_option maxHeartbeats 16000000 in
/-- **Steps 1–9 of Miller's separator: the band case and the deep fallback.** -/
theorem millerC_spec {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n} {A V : ℕ → ℕ}
    (wP : Q → ℕ) {W : ℕ} {P : Input} {c : Config} {b : ABase} {bIm bMk bTmp bFc : ℕ}
    {bA' bL' bS' bSum' bNx bCy bPos : ℕ}
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (hk2 : 2 ≤ k)
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hpos : 0 < ∑ v, wP v)
    (hlay : ALay b k n W) (hWt : 11 * k + 3 * ∑ v, wP v + 4 ≤ W)
    (hlay9 : b.bS₂ + n ≤ bIm ∧ bIm + k ≤ bMk ∧ bMk + n ≤ bTmp ∧ bTmp + n ≤ bFc ∧
      bFc + 2 * n + 1 ≤ W)
    (hlay10 : bFc + 2 * n + 1 ≤ bNx ∧ bNx + n ≤ bA' ∧ bA' + k ≤ bL' ∧ bL' + k ≤ bS' ∧
      bS' + k ≤ bSum' ∧ bSum' + k + 1 ≤ bCy ∧ bCy + 3 * k ≤ bPos ∧ bPos + n ≤ W ∧
      bSum' + 3 * k + 4 * n + 1 ≤ W)
    (hc : WordsBounded W c) (hR : ARegs b k n c)
    (hR9 : S9Regs k n b.bV b.bPr b.bLv bIm bMk bTmp bFc c)
    (hR10 : S10Regs k n b.bV b.bLv b.bPr b.bF b.bw bA' bL' bS' bSum' bNx bCy bPos c)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (b.bV + x) = V x)
    (mW : ∀ v, c.nmem (b.bw + vi v) = wP v) (hMk : ∀ v < n, c.nmem (bMk + v) = 0)
    (hz0 : ∀ x ≤ k, c.nmem (bSum' + x) = 0) (hNx0 : ∀ v < n, c.nmem (bNx + v) = 0) :
    ∃ c' t, Exec P W millerC c c' t ∧
      t ≤ (231 * Nat.log 2 n + 1134) * k + (60 * n + 152) * Nat.log 2 n + 278 * n + 637 +
        (113 * k + 90 * n + 145) + (281 * k + 51 * n + 69) ∧
      ∃ (T T₁ : M.SpTree) (l₀ l₂ : ℕ) (K₀ : Finset Q) (cn : Q → Q) (δ : D),
        l₀ < l₂ ∧ l₂ ≤ l₀ + 2 * Nat.sqrt n + 1 ∧ (Nat.sqrt n + 1) * #(T.lvl l₂) ≤ n ∧
        ((l₀ = 0 ∧ K₀ = {T.root}) ∨
          (1 ≤ l₀ ∧ K₀ ⊆ T.lvl l₀ ∧ (Nat.sqrt n + 1) * #(T.lvl l₀) ≤ n)) ∧
        -- the band case
        (¬ (M.face δ ∉ M.zone (T.low l₂) ∧ M.face (M.α δ) ∉ M.zone (T.low l₂)) →
          ¬ (0 < c'.nreg 580 ∧ 0 < c'.nreg 581) ∧
          c'.nreg 514 = (T₁.fcycle δ).k ∧
          (∀ i < (T₁.fcycle δ).k, c'.nmem (bFc + i) = cd ((T₁.fcycle δ).d i)) ∧
          (∀ G : M.Face, c'.nmem (bIm + fi cd G) ≠ c'.nreg 539 ↔ G ∈ T₁.inside δ) ∧
          ∀ (x₀ : D) (g₀ : M.Face),
            bandSep T T₁ l₂ cn (wR wP) δ x₀ g₀ = (T₁.fcycle δ, T₁.inside δ) ∧
            SepOK (wR wP) (2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂)) (T₁.fcycle δ, T₁.inside δ)) ∧
        -- the deep case
        (M.face δ ∉ M.zone (T.low l₂) ∧ M.face (M.α δ) ∉ M.zone (T.low l₂) →
          0 < c'.nreg 580 ∧ 0 < c'.nreg 581 ∧
          (c'.nreg 584 = c'.nreg 585 ↔
            topA T T₁ l₂ (M.vert δ) = topA T T₁ l₂ (M.vert (M.α δ))) ∧
          (c'.nreg 168 ≤ 3 * c'.nreg 599 ↔
            1 / 3 ≤ ∑ v ∈ ins (M.comp (T.low l₂) (M.face δ)), wR wP v) ∧
          (∀ y : D, c'.nmem (bL' + (cd y : ℕ) / 3) = c'.nreg 597 ↔
            M.face y ∈ M.comp (T.low l₂) (M.face δ)) ∧
          ∃ (x₀ : D) (hok : BdOK (M.comp (T.low l₂) (M.face δ)) x₀),
            (cd x₀ : ℕ) = c'.nreg 445 ∧ c'.nreg 451 = (bdCycle _ x₀ hok).k ∧
            (∀ i < (bdCycle _ x₀ hok).k, c'.nmem (bCy + i) = cd ((bdCycle _ x₀ hok).d i)) ∧
            -- the fallback branch of `deepSep`
            ((topA T T₁ l₂ (M.vert δ) = topA T T₁ l₂ (M.vert (M.α δ)) ∨
                1 / 3 ≤ ∑ v ∈ ins (M.comp (T.low l₂) (M.face δ)), wR wP v) →
              ∀ g₀ : M.Face,
                bandSep T T₁ l₂ cn (wR wP) δ x₀ g₀ =
                  (bdCycle _ x₀ hok, M.comp (T.low l₂) (M.face δ)) ∧
                SepOK (wR wP) (2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂))
                  (bdCycle _ x₀ hok, M.comp (T.low l₂) (M.face δ)))) := by
  classical
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hlay9
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := hlay10
  have hl := hlay
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19,
    l20, l21, l22, lW⟩ := hl
  obtain ⟨c₂, t₂, e₂, ht₂, T, T₁, l₀, l₂, K₀, cn, δ, hl02, hl2s, h3, hK, h514, hd, him, hz,
    hband, hbfs, ⟨H, c₀, hI⟩, hcn, hδ, hA, hB, hlight, h160, hroot, hroot₁, mL, hPr, -, mA₂, mV₂,
    mW₂, ⟨fdD, hfdD, mF₂⟩, hhi, fr₂, q500, q566, -⟩ :=
    millerB_spec (P := P) wP hM hT3 hk2 hAcd hφ hV hpos hlay hWt ⟨hb1, hb2, hb3, hb4, hb5⟩ hc
      hR hR9 mA mV mW hMk
  have hw₂ := e₂.wb_right
  have G₂ : ∀ r, 430 ≤ r → s9band.wr r = false → c₂.nreg r = c.nreg r := fun r a h =>
    e₂.nreg_of_wr (millerB_wr a h)
  have g510 : c₂.nreg 510 = 0 := (G₂ 510 (by omega) (by decide)).trans hR9.r510
  set Y := M.comp (T.low l₂) (M.face δ)
  have hl2 : 1 ≤ l₂ := by omega
  by_cases hdeep : M.face δ ∉ M.zone (T.low l₂) ∧ M.face (M.α δ) ∉ M.zone (T.low l₂)
  · -- the deep case
    have f580 : c₂.nreg 510 < c₂.nreg 580 := by rw [g510]; exact (hz.2 hdeep).1
    have f581 : c₂.nreg 510 < c₂.nreg 581 := by rw [g510]; exact (hz.2 hdeep).2
    have hl2n : l₂ ≤ n := by
      have hv : M.vert δ ∉ T.low l₂ := fun h => hdeep.1 (face_mem_zone h)
      rw [mem_low] at hv
      have := height_lt_card hbfs (M.vert δ)
      rw [Fintype.card_congr vi, Fintype.card_fin] at this
      omega
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
    obtain ⟨c₄, t₄, e₄, ht₄, -, -, htop, hm₄, hr₄, ho₄⟩ := s9top_topA (P := P) (T := T)
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
    obtain ⟨c₅, t₅, e₅, ht₅, x₀, hok, hx₀, h451, hcy, -, hm₅, hr₅, ho₅⟩ := s10cyc_spec (P := P)
      (T := T) (vi := vi) (δ := δ) hM hbfs hl2 hAcd hV hdeep.1
      ⟨by omega, by omega, by omega, by omega, d7, d8⟩ hw₄ hB₄
      (fun x hx => by rw [M₄ _ (by omega)]; exact mA₂ x hx)
      (fun x hx => by rw [M₄ _ (by omega)]; exact mV₂ x hx)
      (fun y => by
        have := (cd y).2
        rw [hm₄, q597]; exact hlab₃ y)
      (fun v hv => by rw [M₄ _ (by omega), hhi _ (by omega)]; exact hNx0 v hv)
    have R5 : ∀ r, 474 ≤ r → r ≠ 584 → r ≠ 585 → r ≠ 586 → r ≠ 597 → r ≠ 598 → r ≠ 599 →
        c₅.nreg r = c₂.nreg r := fun r a b' d e f g h' => by
      rw [hr₅ r (by omega) (by omega) (Or.inr (by omega)),
        hr₄ r (by omega) (by omega) (Or.inr a) b' d e, hr₃ r (by omega) f g h']
    have eC : Exec P W millerC c c₅ (t₂ + (t₃ + (t₄ + t₅) + 1 + 1)) :=
      .seq e₂ (.ifLtN_true f580 (.ifLtN_true f581 (.seq e₃ (.seq e₄ e₅))))
    refine ⟨c₅, _, eC, by omega, T, T₁, l₀, l₂, K₀, cn, δ, hl02, hl2s, h3, hK,
      fun h => absurd hdeep h, fun _ => ⟨?_, ?_, ?_, ?_, fun y => ?_, x₀, hok, hx₀, h451, hcy,
        fun hfb g₀ => ?_⟩⟩
    · rw [R5 580 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact (hz.2 hdeep).1
    · rw [R5 581 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact (hz.2 hdeep).2
    · rw [hr₅ 584 (by omega) (by omega) (Or.inr (by omega)),
        hr₅ 585 (by omega) (by omega) (Or.inr (by omega))]
      exact htop
    · rw [hr₅ 168 (by omega) (by omega) (Or.inl (by omega)),
        hr₅ 599 (by omega) (by omega) (Or.inr (by omega)),
        hr₄ 168 (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega),
        hr₄ 599 (by omega) (by omega) (Or.inr (by omega)) (by omega) (by omega) (by omega),
        h168, h599]
      exact (third_le_iff hpos _).symm
    · have := (cd y).2
      rw [hm₅ _ (Or.inr (by omega)) (fun h => by omega) (fun h => by omega),
        hr₅ 597 (by omega) (by omega) (Or.inr (by omega)), hm₄, q597]
      exact hlab₃ y
    · have r := deep_fallback_sep hM hT3 hbfs (wR_nonneg wP) (sum_wR hpos).le hI hl02 hcn hδ hA hB
        hlight hdeep.1 hdeep.2 hok (g₀ := g₀) hfb
      exact ⟨r.1, r.2 (M.face (fdD T.root))
        (face_mem_zone (by rw [hfdD]; exact root_mem_low hbfs hl2))⟩
  · -- the band case
    have hnb : ¬ (0 < c₂.nreg 580 ∧ 0 < c₂.nreg 581) := fun h => hdeep (hz.1 h)
    have bandC := fun x₀ g₀ => hband hnb x₀ g₀
    by_cases a : c₂.nreg 510 < c₂.nreg 580
    · have a' : ¬ c₂.nreg 510 < c₂.nreg 581 := fun h =>
        hnb ⟨by rw [g510] at a; exact a, by rw [g510] at h; exact h⟩
      have eC : Exec P W millerC c c₂ (t₂ + (0 + 2 + 1)) :=
        .seq e₂ (.ifLtN_true a (.ifLtN_false a' (.skip hw₂)))
      exact ⟨c₂, _, eC, by omega, T, T₁, l₀, l₂, K₀, cn, δ, hl02, hl2s, h3, hK,
        fun _ => ⟨hnb, h514, hd, him, bandC⟩, fun h => absurd h hdeep⟩
    · have eC : Exec P W millerC c c₂ (t₂ + (0 + 2)) := .seq e₂ (.ifLtN_false a (.skip hw₂))
      exact ⟨c₂, _, eC, by omega, T, T₁, l₀, l₂, K₀, cn, δ, hl02, hl2s, h3, hK,
        fun _ => ⟨hnb, h514, hd, him, bandC⟩, fun h => absurd h hdeep⟩

end Whole

end MillerProg

end PlanarSeparator
