module

public import PlanarFlow.BKMNW.MsCost

/-!
# The MSSP encoder, stage C1 from the node words only

`msDk_exec` and `msC1_exec` (`MsStC`, `MsStC2`) assume Klein's map words `StEnc.KInM` at `IM`,
whose field `is` asks the piece flags `IS` to be `0`; after stage B3 the flags hold the piece, so
those lemmas do not apply to the composed encoder. Their runs only read the node words `NT`, `NH`:
**`msDk_exec'`**, **`msC1_exec'`** are the same statements (same programs `msDk`, `msC1`) with the
hypotheses on `NT`, `NH` only.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

set_option maxHeartbeats 2000000 in
/-- **Dijkstra's run on the cut** (see the module docstring). -/
theorem msDk_exec' {N : CombMap D V F} {nD cV : ℕ} (σ : D ≃ Fin nD) (τv : V ≃ Fin cV)
    {ℓD : D → ℤ} {IM LD Ab H GA : ℕ} {u : V}
    (c : Config) (hc : WordsBounded W c)
    (hNT : ∀ d, c.nmem (IM + Klein.iNT nD + σ d) = 1 + (τv (N.tail d) : ℕ))
    (hNH : ∀ d, c.nmem (IM + Klein.iNH nD + σ d) = 1 + (τv (N.head d) : ℕ))
    (hpos : ∀ d, 0 < ℓD d) (hLD : ∀ d, c.nmem (LD + σ d) = (ℓD d).toNat)
    (hL2 : ∀ d, (ℓD d).toNat ≤ H + H)
    (hreach : ∀ x, MSSP.Reach (MSSP.pieceGraph N univ ℓD) u x)
    (hu : c.nmem (IM + 4 * nD + c.nmem GA) = 1 + (τv u : ℕ))
    (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM) (r88 : c.nreg 8288 = LD)
    (r68 : c.nreg 8268 = Ab) (r35 : c.nreg 7335 = H) (r57 : c.nreg 7957 = cV)
    (r67 : c.nreg 8267 = GA) (hcV : cV ≤ nD)
    (l1 : IM + 6 * nD ≤ Ab) (l2 : LD + nD ≤ Ab) (hW : Ab + 10 * (4 * nD + 1) + 1 + nD ≤ W)
    (hWI : cV * (H + H) + 1 + (H + H) ≤ W) (hGA : IM + 4 * nD + c.nmem GA ≤ W) (h4 : 4 ≤ W) :
    ∃ e t, Exec P W msDk c e t ∧ t ≤ 15 + stdCost (4 * nD + 1) nD ∧
      (∀ x, e.nmem (Ab + 5 * (4 * nD + 1) + 1 + nD + (1 + (τv x : ℕ))) =
        (MSSP.dist (MSSP.pieceGraph N univ ℓD) u x).toNat) ∧
      (∀ x, x ≠ u → ∃ d, e.nmem (Ab + 9 * (4 * nD + 1) + 1 + nD + (1 + (τv x : ℕ))) = σ d ∧
        N.head d = x ∧ MSSP.dist (MSSP.pieceGraph N univ ℓD) u (N.tail d) + ℓD d =
          MSSP.dist (MSSP.pieceGraph N univ ℓD) u x) ∧
      (∀ a, a < Ab ∨ Ab + 10 * (4 * nD + 1) + 1 + nD ≤ a → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 1500 ∨ 2548 ≤ r) → (r < 7860 ∨ 7877 ≤ r) → r ≠ 8264 → r ≠ 8265 → r ≠ 8266 →
        e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a60, a61, a62, a63, a64, a6x, aR, am, ar, arm, ao⟩ :=
    dkSetA_exec (P := P) c hc r50 r82 r88 (by omega) h4
  obtain ⟨c₂, t₂, e₂, ht₂, b65, b70, b71, bR, bm, br, brm, bo⟩ :=
    dkSetB_exec (P := P) c₁ e₁.wb_right (Ab := Ab) (H := H) (cV := cV) (GA := GA)
      (NTb := IM + 4 * nD) ((aR _ (by omega) (by omega) (by omega)).trans r68)
      ((aR _ (by omega) (by omega) (by omega)).trans r35)
      ((aR _ (by omega) (by omega) (by omega)).trans r57) a6x
      ((aR _ (by omega) (by omega) (by omega)).trans r67) a62 (by omega) (by omega)
      (by rw [am]; exact hGA)
  rw [am, hu] at b71
  have m2 : c₂.nmem = c.nmem := by rw [bm, am]
  have hcard : Fintype.card V * (H + H) < cV * (H + H) + 1 := by
    rw [Fintype.card_congr τv, Fintype.card_fin]; omega
  obtain ⟨c₃, t₃, e₃, ht₃, hD, hPa, M₃, R₃, rr₃, rm₃, o₃⟩ :=
    stdP_exec (P := P) (M := N) σ (ιv := fun x => 1 + (τv x : ℕ))
      (fun x y e => τv.injective (Fin.ext (by simp only at e; omega)))
      (fun x => by have := (τv x).2; omega) (by omega) (by omega) hpos (Lmax := H + H)
      (Inf := cV * (H + H) + 1) hL2 hcard (by omega) (u := u) hreach
      (NTb := IM + 4 * nD) (NHb := IM + 4 * nD + nD) (Lb := LD) (Ab := Ab) (by omega)
      (by omega) l2 hW c₂ e₂.wb_right
      (fun d => by rw [m2]; have := hNT d; simp only [Klein.iNT] at this; exact this)
      (fun d => by
        rw [m2]; have := hNH d; simp only [Klein.iNH] at this
        rw [show IM + 4 * nD + nD = IM + 5 * nD by ring]; exact this)
      (fun d => by rw [m2]; exact hLD d)
      ((bR _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans a60)
      ((bR _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans a61)
      ((bR _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans a62)
      ((bR _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans a63)
      ((bR _ (by omega) (by omega) (by omega) (by omega) (by omega)).trans a64) b65 b70 b71
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, hD, hPa,
    fun a ha => by rw [M₃ a ha, m2], fun r h1 h2 h3 h4 h5 => ?_, by rw [rr₃, br, ar],
    by rw [rm₃, brm, arm], by rw [o₃, bo, ao]⟩
  rw [R₃ r (by omega), bR r (by omega) (by omega) (by omega) h4 h5,
    aR r (by omega) h3 h4]

set_option maxHeartbeats 2000000 in
/-- **The two Dijkstra runs** (see the module docstring). -/
theorem msC1_exec' {N : CombMap D V F} {nD cV : ℕ} (σ : D ≃ Fin nD) (τv : V ≃ Fin cV)
    {ℓD : D → ℤ} {IM LD A0 A1 H GG k : ℕ} {u₀ u₁ : V}
    (c : Config) (hc : WordsBounded W c)
    (hNT : ∀ d, c.nmem (IM + Klein.iNT nD + σ d) = 1 + (τv (N.tail d) : ℕ))
    (hNH : ∀ d, c.nmem (IM + Klein.iNH nD + σ d) = 1 + (τv (N.head d) : ℕ))
    (hpos : ∀ d, 0 < ℓD d) (hLD : ∀ d, c.nmem (LD + σ d) = (ℓD d).toNat)
    (hL2 : ∀ d, (ℓD d).toNat ≤ H + H)
    (hreach : ∀ u x, MSSP.Reach (MSSP.pieceGraph N univ ℓD) u x)
    (hu₀ : c.nmem (IM + 4 * nD + c.nmem GG) = 1 + (τv u₀ : ℕ))
    (hu₁ : c.nmem (IM + 4 * nD + c.nmem (IM + 12 * nD + 1 + 1 % k)) = 1 + (τv u₁ : ℕ))
    (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM) (r88 : c.nreg 8288 = LD)
    (r90 : c.nreg 8290 = A0) (r91 : c.nreg 8291 = A1) (r35 : c.nreg 7335 = H)
    (r57 : c.nreg 7957 = cV) (r84 : c.nreg 8284 = GG) (r56 : c.nreg 8156 = k) (hk : 0 < k)
    (hcV : cV ≤ nD) (hGG : c.nmem GG < nD)
    (hG1 : c.nmem (IM + 12 * nD + 1 + 1 % k) < nD)
    (l1 : IM + 12 * nD + 1 + 2 ≤ A0) (l2 : LD + nD ≤ A0) (l3 : GG < A0)
    (l4 : A0 + 10 * (4 * nD + 1) + 1 + nD ≤ A1) (hW : A1 + 10 * (4 * nD + 1) + 1 + nD ≤ W)
    (hWI : cV * (H + H) + 1 + (H + H) ≤ W) (hGA : IM + 4 * nD + nD ≤ W) :
    ∃ e t, Exec P W msC1 c e t ∧ t ≤ 10 + 2 * (15 + stdCost (4 * nD + 1) nD) ∧
      (∀ x, e.nmem (A0 + 5 * (4 * nD + 1) + 1 + nD + (1 + (τv x : ℕ))) =
        (MSSP.dist (MSSP.pieceGraph N univ ℓD) u₀ x).toNat) ∧
      (∀ x, x ≠ u₀ → ∃ d, e.nmem (A0 + 9 * (4 * nD + 1) + 1 + nD + (1 + (τv x : ℕ))) = σ d ∧
        N.head d = x ∧ MSSP.dist (MSSP.pieceGraph N univ ℓD) u₀ (N.tail d) + ℓD d =
          MSSP.dist (MSSP.pieceGraph N univ ℓD) u₀ x) ∧
      (∀ x, e.nmem (A1 + 5 * (4 * nD + 1) + 1 + nD + (1 + (τv x : ℕ))) =
        (MSSP.dist (MSSP.pieceGraph N univ ℓD) u₁ x).toNat) ∧
      (∀ a, a < A0 ∨ A1 + 10 * (4 * nD + 1) + 1 + nD ≤ a → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 1500 ∨ 2548 ≤ r) → (r < 7860 ∨ 7877 ≤ r) → (r < 7360 ∨ 7362 < r) →
        (r < 8264 ∨ 8268 < r) → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have hσ : ∀ d, (σ d : ℕ) < nD := fun d => (σ d).2
  have hτ : ∀ x, (τv x : ℕ) < cV := fun x => (τv x).2
  obtain ⟨c₁, t₁, e₁, ht₁, a68, a67, aR, am, ar, arm, ao⟩ := cSetA_exec (P := P) c hc r90 r84
  have q1 : ∀ r, r ≠ 8267 → r ≠ 8268 → c₁.nreg r = c.nreg r := aR
  obtain ⟨c₂, t₂, e₂, ht₂, d0, p0, M₂, R₂, rr₂, rm₂, o₂⟩ :=
    msDk_exec' (P := P) (N := N) σ τv (ℓD := ℓD) (IM := IM) (LD := LD) (Ab := A0) (H := H)
      (GA := GG) (u := u₀) c₁ e₁.wb_right (fun d => by rw [am]; exact hNT d) (fun d => by rw [am]; exact hNH d) hpos
      (fun d => by rw [am]; exact hLD d) hL2 (hreach u₀) (by rw [am]; exact hu₀)
      (by rw [q1 _ (by omega) (by omega)]; exact r50) (by rw [q1 _ (by omega) (by omega)]; exact r82)
      (by rw [q1 _ (by omega) (by omega)]; exact r88) a68
      (by rw [q1 _ (by omega) (by omega)]; exact r35) (by rw [q1 _ (by omega) (by omega)]; exact r57)
      a67 hcV (by omega) l2 (by omega) hWI (by rw [am]; omega) (by omega)
  have q2 : ∀ r, (r < 1500 ∨ 2548 ≤ r) → (r < 7860 ∨ 7877 ≤ r) → (r < 8264 ∨ 8268 < r) →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [R₂ r h1 h2 (by omega) (by omega) (by omega), q1 r (by omega) (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, b68, b67, bR, bm, br, brm, bo⟩ :=
    cSetB_exec (P := P) c₂ e₂.wb_right (A1 := A1) (nD := nD) (IM := IM) (k := k)
      (by rw [q2 _ (by omega) (by omega) (by omega)]; exact r91)
      (by rw [q2 _ (by omega) (by omega) (by omega)]; exact r50)
      (by rw [q2 _ (by omega) (by omega) (by omega)]; exact r82)
      (by rw [q2 _ (by omega) (by omega) (by omega)]; exact r56) hk (by omega) (by omega)
  have m3 : ∀ a, a < A0 → c₃.nmem a = c.nmem a := fun a ha => by
    rw [bm, M₂ a (Or.inl ha), am]
  have q3 : ∀ r, (r < 1500 ∨ 2548 ≤ r) → (r < 7860 ∨ 7877 ≤ r) → (r < 7360 ∨ 7362 < r) →
      (r < 8264 ∨ 8268 < r) → c₃.nreg r = c.nreg r := fun r h1 h2 h3 h4 => by
    rw [bR r (by omega) (by omega) h3, q2 r h1 h2 h4]
  have h1k : 1 % k ≤ 1 := Nat.mod_le 1 k
  obtain ⟨c₄, t₄, e₄, ht₄, d1, -, M₄, R₄, rr₄, rm₄, o₄⟩ :=
    msDk_exec' (P := P) (N := N) σ τv (ℓD := ℓD) (IM := IM) (LD := LD) (Ab := A1) (H := H)
      (GA := IM + 12 * nD + 1 + 1 % k) (u := u₁) c₃ e₃.wb_right
      (fun d => by
        have := hσ d; rw [m3 _ (by simp only [Klein.iNT]; omega)]; exact hNT d)
      (fun d => by
        have := hσ d; rw [m3 _ (by simp only [Klein.iNH]; omega)]; exact hNH d) hpos
      (fun d => by rw [m3 _ (by have := hσ d; omega)]; exact hLD d) hL2 (hreach u₁)
      (by rw [m3 (IM + 12 * nD + 1 + 1 % k) (by omega),
        m3 _ (by have := hG1; omega)]; exact hu₁)
      (by rw [q3 _ (by omega) (by omega) (by omega) (by omega)]; exact r50)
      (by rw [q3 _ (by omega) (by omega) (by omega) (by omega)]; exact r82)
      (by rw [q3 _ (by omega) (by omega) (by omega) (by omega)]; exact r88) b68
      (by rw [q3 _ (by omega) (by omega) (by omega) (by omega)]; exact r35)
      (by rw [q3 _ (by omega) (by omega) (by omega) (by omega)]; exact r57)
      b67 hcV (by omega) (by omega) hW hWI
      (by rw [m3 _ (by omega)]; have := hG1; omega) (by omega)
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega,
    fun x => ?_, fun x hx => ?_, d1, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_,
    by rw [rr₄, br, rr₂, ar], by rw [rm₄, brm, rm₂, arm], by rw [o₄, bo, o₂, ao]⟩
  · have := hτ x
    rw [M₄ _ (Or.inl (by omega)), bm]; exact d0 x
  · have := hτ x
    rw [M₄ _ (Or.inl (by omega)), bm]; exact p0 x hx
  · rw [M₄ a (by omega), bm, M₂ a (by omega), am]
  · rw [R₄ r h1 h2 (by omega) (by omega) (by omega), q3 r h1 h2 h3 h4]

end MsEnc

end BKMNW

end PlanarFlow
