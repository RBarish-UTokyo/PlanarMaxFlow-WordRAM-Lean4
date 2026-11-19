module

public import PlanarFlow.NegSSSP.KEncNatW
public import PlanarFlow.NegSSSP.LinGlue

/-!
# The isolating lengths of the one-face encoding, on natural words

The lengths given to Klein's program on the natural node are the isolating lengths
`MSSP.isoLen n m B w ι ℓ d = N₁ ℓ d + N₂ + N₃ (w d + B) + ι d` of Tewari–Vinodchandran
(`PlanarFlow/MSSP/Isolate.lean`, `N₃ = n m + 1`, `N₂ = N₃ (2 B n + 1)`, `N₁ = N₂ (n + 1)`), with
`ι = σ` the numbering of the darts of the encoding (`Klein.srcIso`). Here a program on **natural
words only** writes them, by dart number, from the lengths `ℓ ≥ 0` and the shifted weights
`w + B ≥ 0` (the words `B + treeW C d` written by `iwProg_treeW`):

* `isoProg`, `isoProg_natOnly`;
* `isoProg_exec`: on index functions (`SL` at `SLb`, `WW` at `WWb`), within `13 nD + 14`
  steps, the word at `ISb + j` is `N₁ SL j + N₂ + N₃ WW j + j`;
* `isoProg_isoLen`: **the words are the isolating lengths**: with `SL (σ d) = (ℓ d).toNat`
  (`ℓ ≥ 0`) and `WW (σ d) = (w d + B).toNat` (`|w d| ≤ B`), the word at `ISb + σ d` is
  `(isoLen n m B w σ ℓ d).toNat`.
* `srcIso_nonneg`: the isolating lengths of a one-face instance are nonnegative, so the words
  are exact.

Registers: natural `2200 … 2206` (inputs `nD`, `SLb`, `WWb`, `ISb`, `n`, `m`, `B`),
`2210 … 2217` (scratch; `N₃`, `N₂`, `N₁` are left in `2211`, `2212`, `2213`). Natural memory is
written only in `[ISb, ISb + nD)`; no real register or real memory is touched.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- `N₃`, `N₂`, `N₁` into `2211`, `2212`, `2213`; the counter `2214 = 0`, `2210 = 1`. -/
def isoInit : Stmt :=
  block [.constN 2210 1, .constN 2215 2, .mulN 2211 2204 2205, .addN 2211 2211 2210,
    .mulN 2212 2215 2206, .mulN 2212 2212 2204, .addN 2212 2212 2210, .mulN 2212 2211 2212,
    .addN 2213 2204 2210, .mulN 2213 2212 2213, .constN 2214 0]

/-- The dart `j = r2214`: `IS[j] := N₁ SL[j] + N₂ + N₃ WW[j] + j`. -/
def isoBody : Stmt :=
  block [.addN 2216 2201 2214, .loadN 2216 2216, .mulN 2216 2213 2216, .addN 2216 2216 2212,
    .addN 2217 2202 2214, .loadN 2217 2217, .mulN 2217 2211 2217, .addN 2216 2216 2217,
    .addN 2216 2216 2214, .addN 2217 2203 2214, .storeN 2217 2216, .addN 2214 2214 2210]

/-- **The isolating lengths by dart number, on natural words.** -/
def isoProg : Stmt := .seq isoInit (.whileLtN 2214 2200 isoBody)

/-- **`isoProg` has no real instruction** (checked by the kernel). -/
theorem isoProg_natOnly : Klein.natOnly isoProg = true := by kernel_rfl

/-- The word written for the dart `j`. -/
def isoWord (n m B : ℕ) (SL WW : ℕ → ℕ) (j : ℕ) : ℕ :=
  MSSP.isoN1 n m B * SL j + MSSP.isoN2 n m B + MSSP.isoN3 n m * WW j + j

lemma isoN_le (n m B : ℕ) (hn : 1 ≤ n) :
    n * m ≤ MSSP.isoN1 n m B ∧ MSSP.isoN3 n m ≤ MSSP.isoN1 n m B ∧ 2 * B ≤ MSSP.isoN1 n m B ∧
      2 * B * n ≤ MSSP.isoN1 n m B ∧ 2 * B * n + 1 ≤ MSSP.isoN1 n m B ∧
      MSSP.isoN2 n m B ≤ MSSP.isoN1 n m B ∧ n + 1 ≤ MSSP.isoN1 n m B := by
  have e3 : MSSP.isoN3 n m = n * m + 1 := rfl
  have e2 : MSSP.isoN2 n m B = MSSP.isoN3 n m * (2 * B * n + 1) := rfl
  have e1 : MSSP.isoN1 n m B = MSSP.isoN2 n m B * (n + 1) := rfl
  have h21 : MSSP.isoN2 n m B ≤ MSSP.isoN1 n m B := by
    rw [e1]; exact Nat.le_mul_of_pos_right _ (by omega)
  have h32 : MSSP.isoN3 n m ≤ MSSP.isoN2 n m B := by
    rw [e2]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hb2 : 2 * B * n + 1 ≤ MSSP.isoN2 n m B := by
    rw [e2]; exact Nat.le_mul_of_pos_left _ (by rw [e3]; omega)
  have hb : 2 * B ≤ 2 * B * n := Nat.le_mul_of_pos_right _ (by omega)
  have hn1 : n + 1 ≤ MSSP.isoN1 n m B := by
    rw [e1]; exact Nat.le_mul_of_pos_left _ (by have := MSSP.isoN2_pos n m B; omega)
  refine ⟨by omega, by omega, by omega, by omega, by omega, h21, hn1⟩

/-- The layout of `isoProg`. -/
structure ISLay (nD SLb WWb ISb W : ℕ) : Prop where
  wS : SLb + nD ≤ W
  wW : WWb + nD ≤ W
  wI : ISb + nD ≤ W
  dS : SLb + nD ≤ ISb ∨ ISb + nD ≤ SLb
  dW : WWb + nD ≤ ISb ∨ ISb + nD ≤ WWb

set_option maxRecDepth 20000 in
theorem isoInit_exec {n m B : ℕ} (hn : 1 ≤ n) (hN : MSSP.isoN1 n m B ≤ W) (c : Config)
    (hc : WordsBounded W c) (h04 : c.nreg 2204 = n) (h05 : c.nreg 2205 = m)
    (h06 : c.nreg 2206 = B) :
    ∃ c' t, Exec P W isoInit c c' t ∧ t ≤ 11 ∧
      (c'.nreg 2210 = 1 ∧ c'.nreg 2211 = MSSP.isoN3 n m ∧ c'.nreg 2212 = MSSP.isoN2 n m B ∧
        c'.nreg 2213 = MSSP.isoN1 n m B ∧ c'.nreg 2214 = 0 ∧
        (∀ r, r < 2210 ∨ 2218 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := isoN_le n m B hn
  have e3 : MSSP.isoN3 n m = n * m + 1 := rfl
  have e2 : MSSP.isoN2 n m B = MSSP.isoN3 n m * (2 * B * n + 1) := rfl
  have e1 : MSSP.isoN1 n m B = MSSP.isoN2 n m B * (n + 1) := rfl
  unfold isoInit
  exec_block
  all_goals try ((try config_simp); (try simp only [h04, h05, h06]); omega)
  · config_simp; rw [h04, h05, h06, ← e3, ← e2]; omega
  · config_simp; rw [h04, h05, h06, ← e3, ← e2, ← e1]; omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [h04, h05, h06]
  · rw [← e3]
  · rw [← e3, ← e2]
  · rw [← e3, ← e2, ← e1]
  · simp (disch := omega) only [upd_other]

theorem isoProg_exec {nD SLb WWb ISb n m B : ℕ} {SL WW : ℕ → ℕ} (hL : ISLay nD SLb WWb ISb W)
    (hn : 1 ≤ n) (hN : MSSP.isoN1 n m B ≤ W) (hw : ∀ j < nD, isoWord n m B SL WW j ≤ W)
    (c : Config) (hc : WordsBounded W c) (h00 : c.nreg 2200 = nD) (h01 : c.nreg 2201 = SLb)
    (h02 : c.nreg 2202 = WWb) (h03 : c.nreg 2203 = ISb) (h04 : c.nreg 2204 = n)
    (h05 : c.nreg 2205 = m) (h06 : c.nreg 2206 = B) (hSL : ∀ j < nD, c.nmem (SLb + j) = SL j)
    (hWW : ∀ j < nD, c.nmem (WWb + j) = WW j) :
    ∃ c' t, Exec P W isoProg c c' t ∧ t ≤ 14 * nD + 13 ∧
      ((∀ j < nD, c'.nmem (ISb + j) = isoWord n m B SL WW j) ∧
        (∀ a, a < ISb ∨ ISb + nD ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 2210 ∨ 2218 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wW; have := hL.wI; have := hL.dS; have := hL.dW
  unfold isoProg
  refine spec_seq ?_
  refine spec_use (isoInit_exec (P := P) hn hN c hc h04 h05 h06) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a10, a11, a12, a13, a14, an, anm, ar, arm, ao⟩
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ j < i, c'.nmem (ISb + j) = isoWord n m B SL WW j) ∧
      (∀ a, a < ISb ∨ ISb + nD ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2214 ∨ 2218 ≤ r → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 2214) (bR := 2200) (body := isoBody) J (K := 12)
    (n := nD) _ hw₁ a14 (by rw [an _ (by omega), h00]) ?_
    (fun i c₂ hi hw₂ ha hb ⟨g, gnm, gn, gr, grm, go⟩ => by
      have e01 : c₂.nreg 2201 = SLb := by rw [gn _ (by omega), an _ (by omega), h01]
      have e02 : c₂.nreg 2202 = WWb := by rw [gn _ (by omega), an _ (by omega), h02]
      have e03 : c₂.nreg 2203 = ISb := by rw [gn _ (by omega), an _ (by omega), h03]
      have e10 : c₂.nreg 2210 = 1 := by rw [gn _ (by omega), a10]
      have e11 : c₂.nreg 2211 = MSSP.isoN3 n m := by rw [gn _ (by omega), a11]
      have e12 : c₂.nreg 2212 = MSSP.isoN2 n m B := by rw [gn _ (by omega), a12]
      have e13 : c₂.nreg 2213 = MSSP.isoN1 n m B := by rw [gn _ (by omega), a13]
      have xs : c₂.nmem (SLb + i) = SL i := by rw [gnm _ (by omega)]; exact hSL i hi
      have xw : c₂.nmem (WWb + i) = WW i := by rw [gnm _ (by omega)]; exact hWW i hi
      have hwi := hw i hi
      unfold isoWord at hwi
      unfold isoBody
      exec_block
      all_goals try ((try config_simp); (try simp only [e01, e02, e03, e10, e11, e12, e13, ha, xs, xw]); omega)
      refine ⟨by omega, ?_, ?_, ?_⟩
      · config_simp; rw [ha, e10]
      · config_simp; exact hb
      refine ⟨fun j hj => ?_, fun a ha' => ?_, fun r hr => ?_, gr, grm, go⟩
      all_goals config_simp
      · simp only [e01, e02, e03, e11, e12, e13, ha, xs, xw]
        by_cases hji : j = i
        · subst hji; simp [isoWord]
        · rw [upd_other _ _ _ (show ISb + j ≠ ISb + i by omega)]; exact g j (by omega)
      · simp only [e03, ha]
        rw [upd_other _ _ _ (show a ≠ ISb + i by omega)]; exact gnm a ha'
      · rw [← gn r hr]; simp (disch := omega) only [upd_other])) ?_
  · refine ⟨fun j hj => absurd hj (by omega), fun a _ => by rw [anm], fun r _ => rfl, ar, arm, ao⟩
  intro c₂ k₂ hk₂ _ ⟨_, g, gnm, gn, gr, grm, go⟩
  refine ⟨by omega, g, gnm, fun r hr => ?_, gr, grm, go⟩
  rw [gn r (by omega), an r hr]

section Iso

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- **The words of `isoProg` are the isolating lengths**: with `SL (σ d) = (ℓ d).toNat`
(`ℓ ≥ 0`) and `WW (σ d) = (w d + B).toNat` (`|w d| ≤ B`), `isoWord … (σ d)` is
`(isoLen n m B w σ ℓ d).toNat`. -/
theorem isoWord_isoLen {n m B nD : ℕ} (σ : D ≃ Fin nD) {ℓ w : D → ℤ} {SL WW : ℕ → ℕ}
    (hnn : ∀ d, 0 ≤ ℓ d) (hwB : ∀ d, |w d| ≤ B) (hSL : ∀ d, SL (σ d) = (ℓ d).toNat)
    (hWW : ∀ d, WW (σ d) = (w d + B).toNat) (d : D) :
    isoWord n m B SL WW (σ d) = (MSSP.isoLen n m B w (fun d => (σ d : ℕ)) ℓ d).toNat := by
  have hw := hwB d
  rw [abs_le] at hw
  have h1 := Int.toNat_of_nonneg (hnn d)
  have h2 := Int.toNat_of_nonneg (show 0 ≤ w d + B by omega)
  apply Int.ofNat_inj.1
  rw [Int.toNat_of_nonneg]
  · simp only [isoWord, MSSP.isoLen, hSL, hWW]
    push_cast
    rw [h1, h2]
  · unfold MSSP.isoLen
    have := mul_nonneg (Nat.cast_nonneg (α := ℤ) (MSSP.isoN1 n m B)) (hnn d)
    have := mul_nonneg (Nat.cast_nonneg (α := ℤ) (MSSP.isoN3 n m)) (show 0 ≤ w d + B by omega)
    positivity

end Iso

/-- **The isolating lengths of an instance are nonnegative** (the lengths with the sources
copied are, and `|w| ≤ #F'`). -/
theorem srcIso_nonneg {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {k : ℕ} {S : Finset D} {ℓ : D → ℤ} (hnn : ∀ d, 0 ≤ ℓ d)
    {w : Klein.SrcD D k → ℤ} (hwB : ∀ d, |w d| ≤ Fintype.card (Klein.SrcF F k))
    (σ : Klein.SrcD D k ≃ Fin (Fintype.card (Klein.SrcD D k))) (d : Klein.SrcD D k) :
    0 ≤ Klein.srcIso (V := V) (F := F) k S ℓ w σ d := by
  have hW : 0 ≤ Klein.srcW S ℓ := by
    have := sum_nonneg fun d (_ : d ∈ S) => hnn d
    unfold Klein.srcW; omega
  have hl : 0 ≤ Klein.srcLen ℓ (Klein.srcW S ℓ) d := by
    rcases d with d | ⟨i, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [Klein.srcLen, hnn, hW]
  have hw := hwB d
  rw [abs_le] at hw
  unfold Klein.srcIso MSSP.isoLen
  have := mul_nonneg (Nat.cast_nonneg (α := ℤ) (MSSP.isoN1 (Fintype.card (Klein.SrcV V k))
    (Fintype.card (Klein.SrcD D k)) (Fintype.card (Klein.SrcF F k)))) hl
  have := mul_nonneg (Nat.cast_nonneg (α := ℤ) (MSSP.isoN3 (Fintype.card (Klein.SrcV V k))
    (Fintype.card (Klein.SrcD D k)))) (show 0 ≤ w d + (Fintype.card (Klein.SrcF F k) : ℤ) by omega)
  positivity

end NegSSSP

end PlanarFlow
