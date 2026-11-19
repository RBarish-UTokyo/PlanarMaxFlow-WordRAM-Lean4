module

public import PlanarSeparator.Machine.MillerS910
public import PlanarSeparator.BandExplicit

/-!
# Miller's separator on the machine: steps 1–9 in the band case

`millerB = millerA ; s9band`: steps 1–8 (`MillerProg.millerA_spec`), then the darts of the
fundamental cycle of the balanced dart `δ` in the tree `T₁`, its inside marks and the zone tests of
the two faces of `δ` (`MillerProg.s9band_spec`).

**`millerB_spec`**: within

`(231 log₂ n + 1134) k + (60 n + 152) log₂ n + 278 n + 637 + (113 k + 90 n + 145)`

steps, the flags `r580`, `r581` are both positive exactly in the deep case of the explicit
separator `PlanarSeparator.Map.bandSep` (both faces of `δ` avoid the levels `< l₂`); otherwise
(the band case) `bandSep` is the fundamental cycle of `δ` in `T₁` with its inside, the machine
holds its darts at `bFc` (number in `r514`) and marks at `bIm` differing from `r539` exactly on its
faces, and it is a separator (`PlanarSeparator.Map.SepOK`): at most
`2 (l₂ - l₀) + #K₀ + #(T.lvl l₂)` darts, with both sides of weight at most `2/3`, for levels
`l₀ < l₂ ≤ l₀ + 2 ⌊√n⌋ + 1` with `(⌊√n⌋ + 1) #(T.lvl l₂) ≤ n` and `K₀` the root or a set of
vertices of the thin level `l₀`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Map CycleSearch

/-- **Steps 1–9 of Miller's separator, the band case**: `millerA` and `s9band`. -/
def millerB : Stmt := .seq millerA s9band

theorem millerA_wmax : millerA.wmax < 400 := by decide

section Whole

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}

set_option maxHeartbeats 4000000 in
/-- **Steps 1–9 of Miller's separator on the machine, with the output of the band case.** Under
the hypotheses of `millerA_spec`, with the registers `S9Regs` of `s9band` (above `500`) and its
arrays above those of `millerA` (clear cycle marks at `bMk`), `millerB` ends with the case test of
the explicit separator `bandSep` in `r580`, `r581`, and in the band case with the darts and the
inside marks of `bandSep`, which is a separator with at most `2 (l₂ - l₀) + #K₀ + #(T.lvl l₂)`
darts. -/
theorem millerB_spec {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n} {A V : ℕ → ℕ}
    (wP : Q → ℕ) {W : ℕ} {P : Input} {c : Config} {b : ABase} {bIm bMk bTmp bFc : ℕ}
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (hk2 : 2 ≤ k)
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hV : ∀ x, V (cd x) = vi (M.vert x)) (hpos : 0 < ∑ v, wP v)
    (hlay : ALay b k n W) (hWt : 11 * k + 3 * ∑ v, wP v + 4 ≤ W)
    (hlay9 : b.bS₂ + n ≤ bIm ∧ bIm + k ≤ bMk ∧ bMk + n ≤ bTmp ∧ bTmp + n ≤ bFc ∧
      bFc + 2 * n + 1 ≤ W)
    (hc : WordsBounded W c) (hR : ARegs b k n c)
    (hR9 : S9Regs k n b.bV b.bPr b.bLv bIm bMk bTmp bFc c)
    (mA : ∀ x < 3 * k, c.nmem x = A x) (mV : ∀ x < 3 * k, c.nmem (b.bV + x) = V x)
    (mW : ∀ v, c.nmem (b.bw + vi v) = wP v) (hMk : ∀ v < n, c.nmem (bMk + v) = 0) :
    ∃ c' t, Exec P W millerB c c' t ∧
      t ≤ (231 * Nat.log 2 n + 1134) * k + (60 * n + 152) * Nat.log 2 n + 278 * n + 637 +
        (113 * k + 90 * n + 145) ∧
      ∃ (T T₁ : M.SpTree) (l₀ l₂ : ℕ) (K₀ : Finset Q) (cn : Q → Q) (δ : D),
        l₀ < l₂ ∧ l₂ ≤ l₀ + 2 * Nat.sqrt n + 1 ∧ (Nat.sqrt n + 1) * #(T.lvl l₂) ≤ n ∧
        ((l₀ = 0 ∧ K₀ = {T.root}) ∨
          (1 ≤ l₀ ∧ K₀ ⊆ T.lvl l₀ ∧ (Nat.sqrt n + 1) * #(T.lvl l₀) ≤ n)) ∧
        -- the data of step 9 on the machine: the cycle of `δ` in `T₁` and its inside marks
        c'.nreg 514 = (T₁.fcycle δ).k ∧
        (∀ i < (T₁.fcycle δ).k, c'.nmem (bFc + i) = cd ((T₁.fcycle δ).d i)) ∧
        (∀ G : M.Face, c'.nmem (bIm + fi cd G) ≠ c'.nreg 539 ↔ G ∈ T₁.inside δ) ∧
        -- the case test of `bandSep`
        (0 < c'.nreg 580 ∧ 0 < c'.nreg 581 ↔
          M.face δ ∉ M.zone (T.low l₂) ∧ M.face (M.α δ) ∉ M.zone (T.low l₂)) ∧
        -- the band case: the explicit separator is the cycle of `δ` with its inside
        (¬ (0 < c'.nreg 580 ∧ 0 < c'.nreg 581) → ∀ (x₀ : D) (g₀ : M.Face),
          bandSep T T₁ l₂ cn (wR wP) δ x₀ g₀ = (T₁.fcycle δ, T₁.inside δ) ∧
          SepOK (wR wP) (2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂)) (T₁.fcycle δ, T₁.inside δ)) ∧
        -- the state for the deep case: the hypotheses of `band_separator_explicit` and the arrays
        IsBFS T ∧ (∃ H c₀, Inner T (wR wP) l₀ H K₀ c₀ T₁) ∧ IsConc T l₂ cn ∧ ¬ T₁.IsTree δ ∧
        ∑ v ∈ T₁.inC δ, wcf cn (wR wP) v ≤ 2 / 3 ∧ ∑ v ∈ T₁.outC δ, wcf cn (wR wP) v ≤ 2 / 3 ∧
        (∀ f, f ∉ M.zone (T.low l₂) → ∑ v ∈ ins (M.comp (T.low l₂) f), wR wP v ≤ 2 / 3) ∧
        c'.nreg 160 = l₂ ∧ (vi T.root : ℕ) = 0 ∧ T₁.root = T.root ∧
        (∀ v, c'.nmem (b.bLv + vi v) = T.height v) ∧
        (∀ v (h : v ≠ T₁.root), c'.nmem (b.bPr + vi v) = cd (T₁.par v h)) ∧
        (∀ u, wcf cn (wR wP) u = (c'.nmem (b.bWC + vi u) : ℝ) / ∑ v, (wP v : ℝ)) ∧
        (∀ x < 3 * k, c'.nmem x = A x) ∧ (∀ x < 3 * k, c'.nmem (b.bV + x) = V x) ∧
        (∀ v, c'.nmem (b.bw + vi v) = wP v) ∧
        (∃ fdD : Q → D, (∀ u, M.vert (fdD u) = u) ∧ ∀ u, c'.nmem (b.bF + vi u) = cd (fdD u)) ∧
        (∀ a, bFc + 2 * n + 1 ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, 590 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nreg 500 = cd δ ∧ c'.nreg 566 = l₂ ∧
        (l₂ < n → ∀ v, c'.nmem (b.bCN + vi v) = vi (cn v)) := by
  classical
  obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ := hlay9
  have hl := hlay
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16, l17, l18, l19,
    l20, l21, l22, lW⟩ := hl
  obtain ⟨c₁, t₁, e₁, ht₁, T, ls, l₀, l₂, H, K₀, c₀, T₁, cn, δ, hroot, hbfs, hlv, hls, -, -, -,
    hI, hroot₁, ha, hb, hK, hpar, h1, h2, h3, h160, hcn, hcf, hlight, h353, hδ, hA, hB, mA₁, mV₁,
    mW₁, ⟨fdD, hfdD, hfd₁⟩, hhi, hCN⟩ :=
    millerA_spec (P := P) wP hM hT3 hk2 hAcd hφ hV hpos hlay hWt hc hR mA mV mW
  have hw₁ := e₁.wb_right
  have fr₁ : ∀ r, 400 ≤ r → c₁.nreg r = c.nreg r := fun r hr =>
    e₁.nreg_of_wr (Stmt.wr_of_wmax (by have := millerA_wmax; omega))
  have hR9' : S9Regs k n b.bV b.bPr b.bLv bIm bMk bTmp bFc c₁ :=
    ⟨(fr₁ 501 (by omega)).trans hR9.r501, (fr₁ 502 (by omega)).trans hR9.r502,
      (fr₁ 503 (by omega)).trans hR9.r503, (fr₁ 504 (by omega)).trans hR9.r504,
      (fr₁ 505 (by omega)).trans hR9.r505, (fr₁ 506 (by omega)).trans hR9.r506,
      (fr₁ 507 (by omega)).trans hR9.r507, (fr₁ 508 (by omega)).trans hR9.r508,
      (fr₁ 509 (by omega)).trans hR9.r509, (fr₁ 510 (by omega)).trans hR9.r510,
      (fr₁ 511 (by omega)).trans hR9.r511, (fr₁ 530 (by omega)).trans hR9.r530,
      (fr₁ 531 (by omega)).trans hR9.r531, (fr₁ 533 (by omega)).trans hR9.r533,
      (fr₁ 534 (by omega)).trans hR9.r534, (fr₁ 535 (by omega)).trans hR9.r535,
      (fr₁ 536 (by omega)).trans hR9.r536, (fr₁ 537 (by omega)).trans hR9.r537,
      (fr₁ 538 (by omega)).trans hR9.r538, (fr₁ 567 (by omega)).trans hR9.r567⟩
  have hr : (vi T₁.root : ℕ) = 0 := by rw [hroot₁]; exact hroot
  obtain ⟨c₂, t₂, e₂, ht₂, h514, hd, him, hz1, hz2, mA₂, MF, fr₂, q500, q566, -⟩ :=
    s9band_spec (P := P) (T := T) (T₁ := T₁) (vi := vi) (V := V) (δ := δ) hM (by omega) hAcd hφ hV
      hr ⟨l1, by omega, by omega, by omega, by omega, by omega, hb2, hb3, hb4, hb5, by omega⟩
      hw₁ hR9' h353.symm h160 hδ mA₁ mV₁ hlv (fun v h => (hpar v h).symm)
      (fun v hv => by rw [hhi _ (by omega)]; exact hMk v hv)
  have e₀ : Exec P W millerB c c₂ (t₁ + t₂) := .seq e₁ e₂
  have M2 : ∀ a, 11 * k ≤ a → a < bIm → c₂.nmem a = c₁.nmem a := fun a h1 h2 =>
    MF a h1 (Or.inl h2)
  refine ⟨c₂, t₁ + t₂, e₀, by omega, T, T₁, l₀, l₂, K₀, cn, δ, by omega, by omega, h3,
    hK, h514, hd, him, by rw [hz1, hz2], fun hband x₀ g₀ => ?_, hbfs, ⟨H, c₀, hI⟩, hcn, hδ, hA,
    hB, hlight, by rw [e₂.nreg_of_wr (by decide)]; exact h160, hroot, hroot₁,
    fun v => by have := (vi v).2; rw [M2 _ (by omega) (by omega)]; exact hlv v,
    fun v h => by have := (vi v).2; rw [M2 _ (by omega) (by omega)]; exact (hpar v h).symm,
    fun u => by have := (vi u).2; rw [M2 _ (by omega) (by omega)]; exact hcf u, mA₂,
    fun x hx => by rw [M2 _ (by omega) (by omega)]; exact mV₁ x hx,
    fun v => by have := (vi v).2; rw [M2 _ (by omega) (by omega)]; exact mW₁ v,
    ⟨fdD, hfdD, fun u => by have := (vi u).2; rw [M2 _ (by omega) (by omega)]; exact hfd₁ u⟩,
    fun a ha => by rw [MF a (by omega) (Or.inr ha), hhi a (by omega)],
    fun r hr' => by rw [fr₂ r hr', fr₁ r (by omega)], q500, q566,
    fun hl v => by have := (vi v).2; rw [M2 _ (by omega) (by omega)]; exact hCN hl v⟩
  have hz : M.face δ ∈ M.zone (T.low l₂) ∨ M.face (M.α δ) ∈ M.zone (T.low l₂) := by
    by_contra hn
    push Not at hn
    exact hband ⟨hz1.2 hn.1, hz2.2 hn.2⟩
  have hsep := band_separator_explicit hM hT3 hbfs (wR_nonneg wP) (sum_wR hpos).le hI
    (by omega) hcn hδ hA hB hlight (x₀ := x₀)
    (fun n1 n2 => absurd (hz.elim (fun h => absurd h n1) (fun h => absurd h n2)) id)
    (g₀ := M.face (fdD T.root)) (face_mem_zone (by rw [hfdD]; exact root_mem_low hbfs (by omega)))
  rw [bandSep_of_band hz] at hsep
  exact ⟨bandSep_of_band hz, hsep⟩

end Whole

end MillerProg

end PlanarSeparator
