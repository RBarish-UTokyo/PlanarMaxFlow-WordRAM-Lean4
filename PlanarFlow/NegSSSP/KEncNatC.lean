module

public import PlanarFlow.NegSSSP.KEncNatW
public import PlanarFlow.NegSSSP.LinGlue

/-!
# The residues of the real constants of the one-face encoding, on natural words

The natural slot of the encoding of a one-face instance (`NegSSSP.KSlotN`) holds, at `RkN + a`
(`a < 3 nD + 3`), the residues modulo `Mo = 2 Hc + 1` of Klein's real constants
`Klein.kConst` (the weights `tripWt 0` and the labels `tripφ` by dart number, `0` on the third
block of `nD` words, then `tripL`, `tripTh`, `tripH0`), with `Hc ≥ kleinHI`. Here a program on
**natural words only** writes them, mirroring `kcProg` (`PlanarFlow/NegSSSP/KEncProg.lean`,
real registers) but computing the constants exactly as natural numbers (the lengths of the piece
being nonnegative, `tripW = Σ_S ℓ` and all the constants are natural numbers) and storing their
residues with `modN`; it also computes the **explicit bound**
`Hc = kcnHc nV nF W k = 4800 (k + 1) (nV + 1)² (nF + 1) (W + 1)` (`Klein.kleinHI_le`) and
`Mo = 2 Hc + 1`:

* `kcnProg`, `kcnProg_natOnly` (no real instruction, checked by the kernel);
* `kcnProg_exec`: **on index functions** (flags `fl` at `Sb`, reach bits `rb` at `Rb`, natural
  lengths `Lv` at `Lb`), within `30 nD + 70` steps;
* `kcnProg_kslot`: **its output is the field `res` of `KSlotN`** for any map, piece, lengths
  `ℓ ≥ 0` on the piece and numbering `σ` of the darts, with `Hc = kcnHc #V #F (tripW).toNat k`,
  and `kleinHI ≤ Hc` (`kcnHc_ge`).

Registers: natural `2100 … 2107` (inputs `nD`, `Lb`, `Sb`, `Rb`, `Ob`, `nV`, `k`, `nF`),
`2110 … 2137` (scratch; `Hc` is left in `2125`, `Mo` in `2126`). Natural memory is written only
in `[Ob, Ob + 3 nD + 3)`; no real register or real memory is touched.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### The constants as natural numbers -/

/-- The partial sums `Σ_{j < i, fl j > 0} Lv j`. -/
def kcnSum (fl Lv : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => kcnSum fl Lv i + (if 0 < fl i then Lv i else 0)

lemma kcnSum_mono (fl Lv : ℕ → ℕ) {i j : ℕ} (h : i ≤ j) : kcnSum fl Lv i ≤ kcnSum fl Lv j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by simp only [kcnSum]; omega)

/-- `tripL = 4 nV W + W + 1`. -/
def kcnL (nV Wv : ℕ) : ℕ := 4 * (nV * Wv) + Wv + 1
/-- `tripTh = tripL - 2 nV W`. -/
def kcnTh (nV Wv : ℕ) : ℕ := kcnL nV Wv - 2 * (nV * Wv)
/-- `tripK = tripL + W + 2 nV W`. -/
def kcnK (nV Wv : ℕ) : ℕ := kcnL nV Wv + Wv + 2 * (nV * Wv)
/-- `tripH0 = tripTh + (k + 1) (nV + 1) tripK`. -/
def kcnH0 (nV Wv k : ℕ) : ℕ := kcnTh nV Wv + (k + 1) * ((nV + 1) * kcnK nV Wv)
/-- **The bound of the compared differences**: `4800 (k + 1) (nV + 1)² (nF + 1) (W + 1)`. -/
def kcnHc (nV nF Wv k : ℕ) : ℕ := 4800 * (k + 1) * (nV + 1) * (nV + 1) * (nF + 1) * (Wv + 1)

/-- The intermediate values of the constants are at most `Hc`. -/
theorem kcn_bounds (nV nF Wv k : ℕ) :
    nV * Wv ≤ kcnHc nV nF Wv k ∧ 4 * (nV * Wv) + Wv ≤ kcnHc nV nF Wv k ∧
    kcnL nV Wv ≤ kcnHc nV nF Wv k ∧ kcnK nV Wv ≤ kcnHc nV nF Wv k ∧
    (nV + 1) * kcnK nV Wv ≤ kcnHc nV nF Wv k ∧
    (k + 1) * ((nV + 1) * kcnK nV Wv) ≤ kcnHc nV nF Wv k ∧
    kcnH0 nV Wv k ≤ kcnHc nV nF Wv k ∧ 4800 * (k + 1) ≤ kcnHc nV nF Wv k ∧
    4800 * (k + 1) * (nV + 1) ≤ kcnHc nV nF Wv k ∧
    4800 * (k + 1) * (nV + 1) * (nV + 1) ≤ kcnHc nV nF Wv k ∧
    4800 * (k + 1) * (nV + 1) * (nV + 1) * (nF + 1) ≤ kcnHc nV nF Wv k ∧
    nV + 1 ≤ kcnHc nV nF Wv k ∧ k + 1 ≤ kcnHc nV nF Wv k ∧ nF + 1 ≤ kcnHc nV nF Wv k ∧
    Wv + 1 ≤ kcnHc nV nF Wv k ∧ 4800 ≤ kcnHc nV nF Wv k := by
  have h1 : nV * Wv ≤ (nV + 1) * (Wv + 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : Wv + 1 ≤ (nV + 1) * (Wv + 1) := Nat.le_mul_of_pos_left _ (by omega)
  have h2' : nV + 1 ≤ (nV + 1) * (Wv + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h3 : (nV + 1) * (Wv + 1) ≤ (nV + 1) * ((nV + 1) * (Wv + 1)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have h4 : (nV + 1) * ((nV + 1) * (Wv + 1)) ≤ (k + 1) * ((nV + 1) * ((nV + 1) * (Wv + 1))) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hK : kcnK nV Wv ≤ 8 * ((nV + 1) * (Wv + 1)) := by unfold kcnK kcnL; omega
  have hL : kcnL nV Wv ≤ 5 * ((nV + 1) * (Wv + 1)) := by unfold kcnL; omega
  have hTh : kcnTh nV Wv ≤ kcnL nV Wv := by unfold kcnTh; omega
  have hAK : (nV + 1) * kcnK nV Wv ≤ 8 * ((nV + 1) * ((nV + 1) * (Wv + 1))) :=
    calc (nV + 1) * kcnK nV Wv ≤ (nV + 1) * (8 * ((nV + 1) * (Wv + 1))) :=
          Nat.mul_le_mul_left _ hK
      _ = 8 * ((nV + 1) * ((nV + 1) * (Wv + 1))) := by ring
  have hκAK : (k + 1) * ((nV + 1) * kcnK nV Wv) ≤
      8 * ((k + 1) * ((nV + 1) * ((nV + 1) * (Wv + 1)))) :=
    calc (k + 1) * ((nV + 1) * kcnK nV Wv) ≤
          (k + 1) * (8 * ((nV + 1) * ((nV + 1) * (Wv + 1)))) := Nat.mul_le_mul_left _ hAK
      _ = 8 * ((k + 1) * ((nV + 1) * ((nV + 1) * (Wv + 1)))) := by ring
  have hk1 : k + 1 ≤ (k + 1) * ((nV + 1) * ((nV + 1) * (Wv + 1))) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have hGf : (k + 1) * ((nV + 1) * ((nV + 1) * (Wv + 1))) ≤
      (k + 1) * ((nV + 1) * ((nV + 1) * (Wv + 1))) * (nF + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hH : kcnHc nV nF Wv k =
      4800 * ((k + 1) * ((nV + 1) * ((nV + 1) * (Wv + 1))) * (nF + 1)) := by
    unfold kcnHc; ring
  have p4 : 4800 * (k + 1) * (nV + 1) * (nV + 1) * (nF + 1) ≤ kcnHc nV nF Wv k := by
    unfold kcnHc; exact Nat.le_mul_of_pos_right _ (by omega)
  have p3 : 4800 * (k + 1) * (nV + 1) * (nV + 1) ≤ 4800 * (k + 1) * (nV + 1) * (nV + 1) * (nF + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have p2 : 4800 * (k + 1) * (nV + 1) ≤ 4800 * (k + 1) * (nV + 1) * (nV + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have p1 : 4800 * (k + 1) ≤ 4800 * (k + 1) * (nV + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have p0 : 4800 ≤ 4800 * (k + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have q4 := p4
  have q3 := p3.trans p4
  have q2 := p2.trans (p3.trans p4)
  have q1 := p1.trans (p2.trans (p3.trans p4))
  have q0 := p0.trans (p1.trans (p2.trans (p3.trans p4)))
  clear p0 p1 p2 p3 p4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, q1, q2, q3, q4, ?_, ?_, ?_, ?_, q0⟩
  all_goals clear q0 q1 q2 q3 q4
  all_goals
    have hnF : nF + 1 ≤ (k + 1) * ((nV + 1) * ((nV + 1) * (Wv + 1))) * (nF + 1) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    have e0 : kcnH0 nV Wv k = kcnTh nV Wv + (k + 1) * ((nV + 1) * kcnK nV Wv) := rfl
    generalize kcnHc nV nF Wv k = H at *
    generalize (k + 1) * ((nV + 1) * ((nV + 1) * (Wv + 1))) * (nF + 1) = GF at *
    generalize (k + 1) * ((nV + 1) * ((nV + 1) * (Wv + 1))) = G at *
    generalize (nV + 1) * ((nV + 1) * (Wv + 1)) = A2 at *
    generalize (nV + 1) * (Wv + 1) = A1 at *
    generalize (k + 1) * ((nV + 1) * kcnK nV Wv) = KK at *
    generalize (nV + 1) * kcnK nV Wv = AK at *
    generalize nV * Wv = B at *
    generalize kcnH0 nV Wv k = H0 at *
    generalize kcnTh nV Wv = Th at *
    generalize kcnK nV Wv = K at *
    generalize kcnL nV Wv = L at *
    omega

/-! ### The program -/

/-- The constants `r2110 = 1`, `r2114 = 0` and the sum `r2112 = 0`. -/
def kcnInit : Stmt := block [.constN 2110 1, .constN 2114 0, .constN 2112 0]

/-- The dart `j = r2111` of `tripW`: `r2112 += S[j] > 0 ? L[j] : 0`. -/
def kcnABody : Stmt :=
  .seq (block [.addN 2113 2102 2111, .loadN 2113 2113])
    (.seq (.ifLtN 2114 2113 (block [.addN 2115 2101 2111, .loadN 2115 2115, .addN 2112 2112 2115])
      .skip) (block [.addN 2111 2111 2110]))

/-- `tripW` into `r2112`. -/
def kcnA : Stmt := .seq (block [.constN 2111 0]) (.whileLtN 2111 2100 kcnABody)

/-- `tripL` (`2121`), `tripTh` (`2122`), `tripK` (`2123`), `tripH0` (`2124`). -/
def kcnC1 : Stmt :=
  block [.mulN 2120 2105 2112, .constN 2130 4, .mulN 2121 2130 2120, .addN 2121 2121 2112,
    .addN 2121 2121 2110, .constN 2130 2, .mulN 2131 2130 2120, .subN 2122 2121 2131,
    .addN 2123 2121 2112, .addN 2123 2123 2131, .addN 2132 2105 2110, .mulN 2133 2132 2123,
    .addN 2134 2106 2110, .mulN 2133 2134 2133, .addN 2124 2122 2133]

/-- `Hc` (`2125`), `Mo` (`2126`), `tripL mod Mo` (`2127`). -/
def kcnC2 : Stmt :=
  block [.constN 2125 4800, .mulN 2125 2125 2134, .mulN 2125 2125 2132, .mulN 2125 2125 2132,
    .addN 2135 2107 2110, .mulN 2125 2125 2135, .addN 2135 2112 2110, .mulN 2125 2125 2135,
    .mulN 2126 2130 2125, .addN 2126 2126 2110, .modN 2127 2121 2126]

/-- The residues of `tripL`, `tripTh`, `tripH0` stored at `Ob + 3 nD`, `+ 1`, `+ 2`. -/
def kcnC3 : Stmt :=
  block [.constN 2136 3, .mulN 2136 2136 2100, .addN 2136 2136 2104, .storeN 2136 2127,
    .addN 2136 2136 2110, .modN 2137 2122 2126, .storeN 2136 2137,
    .addN 2136 2136 2110, .modN 2137 2124 2126, .storeN 2136 2137]

/-- The constants: `tripL` (`2121`), `tripTh` (`2122`), `tripK` (`2123`), `tripH0` (`2124`),
`Hc` (`2125`), `Mo` (`2126`), `tripL mod Mo` (`2127`), and the residues of `tripL`, `tripTh`,
`tripH0` stored at `Ob + 3 nD`, `+ 1`, `+ 2`. -/
def kcnC : Stmt := .seq kcnC1 (.seq kcnC2 kcnC3)

/-- The dart `j = r2111`: `Ob[j] := (S[j] > 0 ∧ R[j] > 0 ? L[j] : tripL) mod Mo` (the weight),
`Ob[nD + j] := (S[j] > 0 ? L[j] : 0) mod Mo` (the label), `Ob[2 nD + j] := 0`. -/
def kcnDBody : Stmt :=
  .seq (block [.addN 2113 2102 2111, .loadN 2113 2113, .addN 2115 2103 2111, .loadN 2115 2115,
      .addN 2116 2101 2111, .loadN 2116 2116]) <|
  .seq (.ifLtN 2114 2113
      (.seq (block [.modN 2117 2116 2126])
        (.ifLtN 2114 2115 (block [.copyN 2118 2117]) (block [.copyN 2118 2127])))
      (block [.constN 2117 0, .copyN 2118 2127])) <|
  block [.addN 2119 2104 2111, .storeN 2119 2118, .addN 2119 2119 2100, .storeN 2119 2117,
    .addN 2119 2119 2100, .storeN 2119 2114, .addN 2111 2111 2110]

/-- The weights and the labels by dart. -/
def kcnD : Stmt := .seq (block [.constN 2111 0]) (.whileLtN 2111 2100 kcnDBody)

/-- **The residues of the real constants of the encoding, on natural words.** -/
def kcnProg : Stmt := .seq kcnInit (.seq kcnA (.seq kcnC kcnD))

/-- **`kcnProg` has no real instruction and no real test** (checked by the kernel). -/
theorem kcnProg_natOnly : Klein.natOnly kcnProg = true := by kernel_rfl

/-! ### The data -/

/-- The layout of `kcnProg`: the inputs below `Wd`, apart from the output `[Ob, Ob + 3 nD + 3)`. -/
structure KNLay (nD Lb Sb Rb Ob Wd : ℕ) : Prop where
  wS : Sb + nD ≤ Wd
  wR : Rb + nD ≤ Wd
  wL : Lb + nD ≤ Wd
  wO : Ob + 3 * nD + 3 ≤ Wd
  dS : Sb + nD ≤ Ob ∨ Ob + 3 * nD + 3 ≤ Sb
  dR : Rb + nD ≤ Ob ∨ Ob + 3 * nD + 3 ≤ Rb
  dL : Lb + nD ≤ Ob ∨ Ob + 3 * nD + 3 ≤ Lb

/-- The inputs of `kcnProg` and its constants, kept by every stage. -/
structure KNCtx (nD Lb Sb Rb Ob nV k nF : ℕ) (fl rb Lv : ℕ → ℕ) (c : Config) : Prop where
  r00 : c.nreg 2100 = nD
  r01 : c.nreg 2101 = Lb
  r02 : c.nreg 2102 = Sb
  r03 : c.nreg 2103 = Rb
  r04 : c.nreg 2104 = Ob
  r05 : c.nreg 2105 = nV
  r06 : c.nreg 2106 = k
  r07 : c.nreg 2107 = nF
  r10 : c.nreg 2110 = 1
  r14 : c.nreg 2114 = 0
  fl : ∀ j < nD, c.nmem (Sb + j) = fl j
  rb : ∀ j < nD, c.nmem (Rb + j) = rb j
  lv : ∀ j < nD, c.nmem (Lb + j) = Lv j

variable {nD Lb Sb Rb Ob nV k nF Wd : ℕ} {fl rb Lv : ℕ → ℕ}

theorem KNCtx.frame {c c' : Config} (hL : KNLay nD Lb Sb Rb Ob Wd)
    (h : KNCtx nD Lb Sb Rb Ob nV k nF fl rb Lv c)
    (hn : ∀ r, r ≤ 2110 ∨ r = 2114 → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < Ob ∨ Ob + 3 * nD + 3 ≤ a → c'.nmem a = c.nmem a) :
    KNCtx nD Lb Sb Rb Ob nV k nF fl rb Lv c' := by
  have := hL.dS; have := hL.dR; have := hL.dL
  exact ⟨(hn _ (by omega)).trans h.r00, (hn _ (by omega)).trans h.r01,
    (hn _ (by omega)).trans h.r02, (hn _ (by omega)).trans h.r03,
    (hn _ (by omega)).trans h.r04, (hn _ (by omega)).trans h.r05,
    (hn _ (by omega)).trans h.r06, (hn _ (by omega)).trans h.r07,
    (hn _ (by omega)).trans h.r10, (hn _ (by omega)).trans h.r14,
    fun j hj => (hm _ (by omega)).trans (h.fl j hj), fun j hj => (hm _ (by omega)).trans (h.rb j hj),
    fun j hj => (hm _ (by omega)).trans (h.lv j hj)⟩

/-! ### `tripW` -/

theorem kcnA_exec (hL : KNLay nD Lb Sb Rb Ob Wd) (hS : kcnSum fl Lv nD ≤ W) (hWd : Wd ≤ W)
    (c : Config) (hc : WordsBounded W c) (hC : KNCtx nD Lb Sb Rb Ob nV k nF fl rb Lv c)
    (h12 : c.nreg 2112 = 0) :
    ∃ c' t, Exec P W kcnA c c' t ∧ t ≤ 13 * nD + 3 ∧
      (c'.nreg 2112 = kcnSum fl Lv nD ∧
        (∀ r, r ≤ 2110 ∨ r = 2114 ∨ 2116 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wL
  unfold kcnA
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nreg 2112 = kcnSum fl Lv i ∧
      (∀ r, r ≤ 2110 ∨ r = 2114 ∨ 2116 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 2111) (bR := 2100) (body := kcnABody) J (K := 11)
    (n := nD) _ ‹_› (by config_simp) (by config_simp; exact hC.r00) ?_
    (fun i c₁ hi hw ha hb ⟨g12, gn, gnm, gr, grm, go⟩ => by
      have e01 : c₁.nreg 2101 = Lb := (gn 2101 (by omega)).trans hC.r01
      have e02 : c₁.nreg 2102 = Sb := (gn 2102 (by omega)).trans hC.r02
      have e10 : c₁.nreg 2110 = 1 := (gn 2110 (by omega)).trans hC.r10
      have e14 : c₁.nreg 2114 = 0 := (gn 2114 (by omega)).trans hC.r14
      have xf : c₁.nmem (Sb + i) = fl i := by rw [gnm]; exact hC.fl i hi
      have xl : c₁.nmem (Lb + i) = Lv i := by rw [gnm]; exact hC.lv i hi
      have hSi : kcnSum fl Lv (i + 1) ≤ W := (kcnSum_mono fl Lv (by omega)).trans hS
      unfold kcnABody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e02, ha]); omega)
      refine spec_seq ?_
      by_cases hf : 0 < fl i
      · refine spec_ifLtN_true (by config_simp; rw [e14, e02, ha, xf]; exact hf) ?_
        exec_block
        all_goals try ((try config_simp); (try simp only [e01, e02, ha, e10]); omega)
        · config_simp
          rw [ha, e01, xl, g12]
          simp only [kcnSum, hf, ↓reduceIte] at hSi
          exact hSi
        dsimp only [J]
        config_simp
        simp only [ha, e10, e01, e02, xl, g12]
        refine ⟨by omega, trivial, hb, ?_, fun r hr => ?_, gnm, gr, grm, go⟩
        · simp only [kcnSum, hf, ↓reduceIte]
        · simp only [upd_apply]
          split_ifs <;> first | omega | exact gn r hr
      · refine spec_ifLtN_false (by config_simp; rw [e14, e02, ha, xf]; exact hf) ?_
        refine spec_skip ‹_› ?_
        exec_block
        all_goals try ((try config_simp); (try simp only [ha, e10]); omega)
        dsimp only [J]
        config_simp
        simp only [ha, e10]
        refine ⟨by omega, trivial, hb, ?_, fun r hr => ?_, gnm, gr, grm, go⟩
        · simp only [kcnSum, hf, ↓reduceIte, g12]; omega
        · simp only [upd_apply]
          split_ifs <;> first | omega | exact gn r hr)) ?_
  · refine ⟨by config_simp; exact h12, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, g12, gn, gnm, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, g12, gn, gnm, gr, grm, go⟩

/-! ### The constants -/

theorem kcnC1_exec {Wv Hc : ℕ} (hHW : Hc ≤ W) (c : Config) (hc : WordsBounded W c)
    (e05 : c.nreg 2105 = nV) (e06 : c.nreg 2106 = k) (e10 : c.nreg 2110 = 1)
    (h12 : c.nreg 2112 = Wv)
    (b1 : nV * Wv ≤ Hc) (b2 : 4 * (nV * Wv) + Wv ≤ Hc) (b3 : kcnL nV Wv ≤ Hc)
    (b4 : kcnK nV Wv ≤ Hc) (b5 : (nV + 1) * kcnK nV Wv ≤ Hc)
    (b6 : (k + 1) * ((nV + 1) * kcnK nV Wv) ≤ Hc) (b7 : kcnH0 nV Wv k ≤ Hc)
    (b12 : nV + 1 ≤ Hc) (b13 : k + 1 ≤ Hc) (b16 : 4800 ≤ Hc) :
    ∃ c' t, Exec P W kcnC1 c c' t ∧ t ≤ 15 ∧
      (c'.nreg 2121 = kcnL nV Wv ∧ c'.nreg 2122 = kcnTh nV Wv ∧ c'.nreg 2124 = kcnH0 nV Wv k ∧
        c'.nreg 2130 = 2 ∧ c'.nreg 2132 = nV + 1 ∧ c'.nreg 2134 = k + 1 ∧
        (∀ r, r < 2120 ∨ 2135 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold kcnK at b4 b5 b6
  unfold kcnH0 kcnTh kcnK at b7
  unfold kcnL at b3 b4 b5 b6 b7
  unfold kcnC1
  exec_block
  all_goals try ((try config_simp); (try simp only [e05, e06, e10, h12]); omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [e05, e06, e10, h12]
  · simp only [kcnL]
  · simp only [kcnTh, kcnL]
  · simp only [kcnH0, kcnTh, kcnK, kcnL]
  · simp (disch := omega) only [upd_other]

set_option maxRecDepth 20000 in
theorem kcnC2_exec {Wv : ℕ} (hH : 2 * kcnHc nV nF Wv k + 1 ≤ W) (c : Config)
    (hc : WordsBounded W c) (e07 : c.nreg 2107 = nF) (e10 : c.nreg 2110 = 1)
    (h12 : c.nreg 2112 = Wv) (h21 : c.nreg 2121 = kcnL nV Wv) (h30 : c.nreg 2130 = 2)
    (h32 : c.nreg 2132 = nV + 1) (h34 : c.nreg 2134 = k + 1) :
    ∃ c' t, Exec P W kcnC2 c c' t ∧ t ≤ 11 ∧
      (c'.nreg 2125 = kcnHc nV nF Wv k ∧ c'.nreg 2126 = 2 * kcnHc nV nF Wv k + 1 ∧
        c'.nreg 2127 = kcnL nV Wv % (2 * kcnHc nV nF Wv k + 1) ∧
        (∀ r, r < 2125 ∨ (2128 ≤ r ∧ r ≠ 2135) → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  obtain ⟨-, -, -, -, -, -, -, q1, q2, q3, q4, -, -, q14, q15, q16⟩ := kcn_bounds nV nF Wv k
  have hHW : kcnHc nV nF Wv k ≤ W := by omega
  have q5 : kcnHc nV nF Wv k = 4800 * (k + 1) * (nV + 1) * (nV + 1) * (nF + 1) * (Wv + 1) := rfl
  unfold kcnC2
  exec_block
  · exact q16.trans hHW
  · config_simp; rw [h34]; exact q1.trans hHW
  · config_simp; rw [h34, h32]; exact q2.trans hHW
  · config_simp; rw [h34, h32]; exact q3.trans hHW
  · config_simp; rw [e07, e10]; exact q14.trans hHW
  · config_simp; rw [h34, h32, e07, e10]; exact q4.trans hHW
  · config_simp; rw [h12, e10]; exact q15.trans hHW
  · config_simp; rw [h34, h32, e07, e10, h12, ← q5]; exact hHW
  · config_simp; rw [h34, h32, e07, e10, h12, ← q5, h30]; omega
  · config_simp; rw [h34, h32, e07, e10, h12, ← q5, h30]; omega
  refine ⟨by omega, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · rw [h34, h32, e07, e10, h12, ← q5]
  · rw [h34, h32, e07, e10, h12, ← q5, h30]
  · rw [h34, h32, e07, e10, h12, ← q5, h30, h21]
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl

theorem kcnC3_exec (hW : Ob + 3 * nD + 3 ≤ W) {Lr Tr Hr : ℕ} (c : Config)
    (hc : WordsBounded W c) (e00 : c.nreg 2100 = nD) (e04 : c.nreg 2104 = Ob)
    (e10 : c.nreg 2110 = 1) (h27 : c.nreg 2127 = Lr) (h22 : c.nreg 2122 % c.nreg 2126 = Tr)
    (h24 : c.nreg 2124 % c.nreg 2126 = Hr) :
    ∃ c' t, Exec P W kcnC3 c c' t ∧ t ≤ 10 ∧
      (c'.nmem (Ob + 3 * nD) = Lr ∧ c'.nmem (Ob + 3 * nD + 1) = Tr ∧
        c'.nmem (Ob + 3 * nD + 2) = Hr ∧
        (∀ a, a < Ob + 3 * nD ∨ Ob + 3 * nD + 3 ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 2136 ∨ 2138 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold kcnC3
  exec_block
  all_goals try ((try config_simp); (try simp only [e00, e04, e10]); omega)
  refine ⟨by omega, ?_, ?_, ?_, fun a ha => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [e00, e04, e10, h27]
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  · simp only [upd_apply]; split_ifs <;> first | omega | exact h22
  · simp only [upd_apply]; split_ifs <;> first | omega | exact h24
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl

theorem kcnC_exec (hL : KNLay nD Lb Sb Rb Ob Wd) (hWd : Wd ≤ W) {Wv : ℕ}
    (hH : 2 * kcnHc nV nF Wv k + 1 ≤ W) (c : Config) (hc : WordsBounded W c)
    (hC : KNCtx nD Lb Sb Rb Ob nV k nF fl rb Lv c) (h12 : c.nreg 2112 = Wv) :
    ∃ c' t, Exec P W kcnC c c' t ∧ t ≤ 36 ∧
      (c'.nreg 2125 = kcnHc nV nF Wv k ∧ c'.nreg 2126 = 2 * kcnHc nV nF Wv k + 1 ∧
        c'.nreg 2127 = kcnL nV Wv % (2 * kcnHc nV nF Wv k + 1) ∧
        c'.nmem (Ob + 3 * nD) = kcnL nV Wv % (2 * kcnHc nV nF Wv k + 1) ∧
        c'.nmem (Ob + 3 * nD + 1) = kcnTh nV Wv % (2 * kcnHc nV nF Wv k + 1) ∧
        c'.nmem (Ob + 3 * nD + 2) = kcnH0 nV Wv k % (2 * kcnHc nV nF Wv k + 1) ∧
        (∀ a, a < Ob + 3 * nD ∨ Ob + 3 * nD + 3 ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r ≤ 2110 ∨ r = 2114 ∨ 2140 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, -, -, -, -, b12, b13, -, -, b16⟩ := kcn_bounds nV nF Wv k
  have hHW : kcnHc nV nF Wv k ≤ W := by omega
  unfold kcnC
  refine spec_seq ?_
  refine spec_use (kcnC1_exec (P := P) hHW c hc hC.r05 hC.r06 hC.r10 h12 b1 b2 b3 b4 b5 b6 b7
    b12 b13 b16) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a21, a22, a24, a30, a32, a34, an, anm, ar, arm, ao⟩
  refine spec_seq ?_
  refine spec_use (kcnC2_exec (P := P) hH c₁ hw₁ ((an _ (by omega)).trans hC.r07)
    ((an _ (by omega)).trans hC.r10) ((an _ (by omega)).trans h12) a21 a30 a32 a34) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨b25, b26, b27, bn, bnm, br, brm, bo⟩
  refine spec_use (kcnC3_exec (P := P) (by omega) c₂ hw₂
    ((bn _ (by omega)).trans ((an _ (by omega)).trans hC.r00))
    ((bn _ (by omega)).trans ((an _ (by omega)).trans hC.r04))
    ((bn _ (by omega)).trans ((an _ (by omega)).trans hC.r10)) b27
    (by rw [bn _ (by omega), a22, b26]) (by rw [bn _ (by omega), a24, b26])) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨d1, d2, d3, dnm, dn, dr, drm, d_o⟩
  refine ⟨by omega, ?_, ?_, ?_, d1, d2, d3, fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [dn _ (by omega), b25]
  · rw [dn _ (by omega), b26]
  · rw [dn _ (by omega), b27]
  · rw [dnm a ha, bnm, anm]
  · rw [dn _ (by omega), bn _ (by omega), an _ (by omega)]
  · rw [dr, br, ar]
  · rw [drm, brm, arm]
  · rw [d_o, bo, ao]

/-! ### The weights and the labels -/

/-- The residue written for the weight of the dart `j` (`Lm` the residue of `tripL`). -/
def kcnWtW (fl rb Lv : ℕ → ℕ) (Mo Lm j : ℕ) : ℕ :=
  if 0 < fl j then (if 0 < rb j then Lv j % Mo else Lm) else Lm

/-- The residue written for the label of the dart `j`. -/
def kcnPhW (fl Lv : ℕ → ℕ) (Mo j : ℕ) : ℕ := if 0 < fl j then Lv j % Mo else 0

set_option maxHeartbeats 2000000 in
theorem kcnD_exec (hL : KNLay nD Lb Sb Rb Ob Wd) (hWd : Wd ≤ W) {Mo Lm : ℕ} (c : Config)
    (hc : WordsBounded W c) (hC : KNCtx nD Lb Sb Rb Ob nV k nF fl rb Lv c)
    (h26 : c.nreg 2126 = Mo) (h27 : c.nreg 2127 = Lm) :
    ∃ c' t, Exec P W kcnD c c' t ∧ t ≤ 20 * nD + 3 ∧
      ((∀ j < nD, c'.nmem (Ob + j) = kcnWtW fl rb Lv Mo Lm j ∧
          c'.nmem (Ob + nD + j) = kcnPhW fl Lv Mo j ∧ c'.nmem (Ob + 2 * nD + j) = 0) ∧
        (∀ a, a < Ob ∨ Ob + 3 * nD ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r ≤ 2110 ∨ r = 2114 ∨ 2120 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wR; have := hL.wL; have := hL.wO
  have := hL.dS; have := hL.dR; have := hL.dL
  unfold kcnD
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ j < i, c'.nmem (Ob + j) = kcnWtW fl rb Lv Mo Lm j ∧
        c'.nmem (Ob + nD + j) = kcnPhW fl Lv Mo j ∧ c'.nmem (Ob + 2 * nD + j) = 0) ∧
      (∀ a, a < Ob ∨ Ob + 3 * nD ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≤ 2110 ∨ r = 2114 ∨ 2120 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 2111) (bR := 2100) (body := kcnDBody) J (K := 18)
    (n := nD) _ ‹_› (by config_simp) (by config_simp; exact hC.r00) ?_
    (fun i c₁ hi hw ha hb ⟨g, gnm, gn, gr, grm, go⟩ => by
      have e00 : c₁.nreg 2100 = nD := (gn 2100 (by omega)).trans hC.r00
      have e01 : c₁.nreg 2101 = Lb := (gn 2101 (by omega)).trans hC.r01
      have e02 : c₁.nreg 2102 = Sb := (gn 2102 (by omega)).trans hC.r02
      have e03 : c₁.nreg 2103 = Rb := (gn 2103 (by omega)).trans hC.r03
      have e04 : c₁.nreg 2104 = Ob := (gn 2104 (by omega)).trans hC.r04
      have e10 : c₁.nreg 2110 = 1 := (gn 2110 (by omega)).trans hC.r10
      have e14 : c₁.nreg 2114 = 0 := (gn 2114 (by omega)).trans hC.r14
      have e26 : c₁.nreg 2126 = Mo := (gn 2126 (by omega)).trans h26
      have e27 : c₁.nreg 2127 = Lm := (gn 2127 (by omega)).trans h27
      have xf : c₁.nmem (Sb + i) = fl i := by rw [gnm _ (by omega)]; exact hC.fl i hi
      have xr : c₁.nmem (Rb + i) = rb i := by rw [gnm _ (by omega)]; exact hC.rb i hi
      have xl : c₁.nmem (Lb + i) = Lv i := by rw [gnm _ (by omega)]; exact hC.lv i hi
      unfold kcnDBody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e01, e02, e03, ha]); omega)
      -- the values read
      have hfv : ∀ c₂ : Config, c₂.nreg 2113 = fl i → c₂.nreg 2114 = 0 →
          (c₂.nreg 2114 < c₂.nreg 2113 ↔ 0 < fl i) := fun c₂ h1 h2 => by rw [h1, h2]
      refine spec_seq ?_
      by_cases hf : 0 < fl i
      · refine spec_ifLtN_true (by config_simp; rw [e14, e02, ha, xf]; exact hf) ?_
        refine spec_seq ?_
        exec_block
        by_cases hr : 0 < rb i
        · refine spec_ifLtN_true (by config_simp; rw [e14, e03, ha, xr]; exact hr) ?_
          exec_block
          all_goals try ((try config_simp); (try simp only [e00, e04, e10, ha]); omega)
          dsimp only [J]
          config_simp
          simp only [e00, e01, e02, e03, e04, e10, e14, e26, e27, ha, xf, xr, xl]
          refine ⟨by omega, trivial, trivial, fun j hj => ?_, fun a ha' => ?_, fun r hr' => ?_, gr, grm,
            go⟩
          · simp only [upd_apply]
            by_cases hji : j = i
            · subst hji
              simp only [show Ob + j ≠ Ob + j + nD + nD by omega,
                show Ob + j ≠ Ob + j + nD by omega, show Ob + j + nD ≠ Ob + j + nD + nD by omega,
                show Ob + nD + j = Ob + j + nD by omega, show Ob + 2 * nD + j = Ob + j + nD + nD by
                omega, ↓reduceIte, kcnWtW, kcnPhW, hf, hr, and_self]
            · simp only [show Ob + j ≠ Ob + i + nD + nD by omega, show Ob + j ≠ Ob + i + nD by omega,
                show Ob + j ≠ Ob + i by omega, show Ob + nD + j ≠ Ob + i + nD + nD by omega,
                show Ob + nD + j ≠ Ob + i + nD by omega, show Ob + nD + j ≠ Ob + i by omega,
                show Ob + 2 * nD + j ≠ Ob + i + nD + nD by omega,
                show Ob + 2 * nD + j ≠ Ob + i + nD by omega,
                show Ob + 2 * nD + j ≠ Ob + i by omega, ↓reduceIte]
              exact g j (by omega)
          · simp only [upd_apply, show a ≠ Ob + i + nD + nD by omega,
              show a ≠ Ob + i + nD by omega, show a ≠ Ob + i by omega, ↓reduceIte]
            exact gnm a ha'
          · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr'
        · refine spec_ifLtN_false (by config_simp; rw [e14, e03, ha, xr]; exact hr) ?_
          exec_block
          all_goals try ((try config_simp); (try simp only [e00, e04, e10, ha]); omega)
          dsimp only [J]
          config_simp
          simp only [e00, e01, e02, e03, e04, e10, e14, e26, e27, ha, xf, xr, xl]
          refine ⟨by omega, trivial, trivial, fun j hj => ?_, fun a ha' => ?_, fun r hr' => ?_, gr, grm,
            go⟩
          · simp only [upd_apply]
            by_cases hji : j = i
            · subst hji
              simp only [show Ob + j ≠ Ob + j + nD + nD by omega,
                show Ob + j ≠ Ob + j + nD by omega, show Ob + j + nD ≠ Ob + j + nD + nD by omega,
                show Ob + nD + j = Ob + j + nD by omega, show Ob + 2 * nD + j = Ob + j + nD + nD by
                omega, ↓reduceIte, kcnWtW, kcnPhW, hf, hr, and_self]
            · simp only [show Ob + j ≠ Ob + i + nD + nD by omega, show Ob + j ≠ Ob + i + nD by omega,
                show Ob + j ≠ Ob + i by omega, show Ob + nD + j ≠ Ob + i + nD + nD by omega,
                show Ob + nD + j ≠ Ob + i + nD by omega, show Ob + nD + j ≠ Ob + i by omega,
                show Ob + 2 * nD + j ≠ Ob + i + nD + nD by omega,
                show Ob + 2 * nD + j ≠ Ob + i + nD by omega,
                show Ob + 2 * nD + j ≠ Ob + i by omega, ↓reduceIte]
              exact g j (by omega)
          · simp only [upd_apply, show a ≠ Ob + i + nD + nD by omega,
              show a ≠ Ob + i + nD by omega, show a ≠ Ob + i by omega, ↓reduceIte]
            exact gnm a ha'
          · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr'
      · refine spec_ifLtN_false (by config_simp; rw [e14, e02, ha, xf]; exact hf) ?_
        exec_block
        all_goals try ((try config_simp); (try simp only [e00, e04, e10, ha]); omega)
        dsimp only [J]
        config_simp
        simp only [e00, e01, e02, e03, e04, e10, e14, e26, e27, ha, xf, xr, xl]
        refine ⟨by omega, trivial, trivial, fun j hj => ?_, fun a ha' => ?_, fun r hr' => ?_, gr, grm,
          go⟩
        · simp only [upd_apply]
          by_cases hji : j = i
          · subst hji
            simp only [show Ob + j ≠ Ob + j + nD + nD by omega,
              show Ob + j ≠ Ob + j + nD by omega, show Ob + j + nD ≠ Ob + j + nD + nD by omega,
              show Ob + nD + j = Ob + j + nD by omega, show Ob + 2 * nD + j = Ob + j + nD + nD by
              omega, ↓reduceIte, kcnWtW, kcnPhW, hf, and_self]
          · simp only [show Ob + j ≠ Ob + i + nD + nD by omega, show Ob + j ≠ Ob + i + nD by omega,
              show Ob + j ≠ Ob + i by omega, show Ob + nD + j ≠ Ob + i + nD + nD by omega,
              show Ob + nD + j ≠ Ob + i + nD by omega, show Ob + nD + j ≠ Ob + i by omega,
              show Ob + 2 * nD + j ≠ Ob + i + nD + nD by omega,
              show Ob + 2 * nD + j ≠ Ob + i + nD by omega,
              show Ob + 2 * nD + j ≠ Ob + i by omega, ↓reduceIte]
            exact g j (by omega)
        · simp only [upd_apply, show a ≠ Ob + i + nD + nD by omega,
            show a ≠ Ob + i + nD by omega, show a ≠ Ob + i by omega, ↓reduceIte]
          exact gnm a ha'
        · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr')) ?_
  · refine ⟨fun j hj => absurd hj (by omega), fun _ _ => rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, g, gnm, gn, gr, grm, go⟩ := hJ₂
  exact ⟨by omega, g, gnm, gn, gr, grm, go⟩

/-! ### The whole program -/

theorem kcnInit_exec (hL : KNLay nD Lb Sb Rb Ob Wd) (hWd : Wd ≤ W) (c : Config)
    (hc : WordsBounded W c)
    (h00 : c.nreg 2100 = nD) (h01 : c.nreg 2101 = Lb) (h02 : c.nreg 2102 = Sb)
    (h03 : c.nreg 2103 = Rb) (h04 : c.nreg 2104 = Ob) (h05 : c.nreg 2105 = nV)
    (h06 : c.nreg 2106 = k) (h07 : c.nreg 2107 = nF) (hfl : ∀ j < nD, c.nmem (Sb + j) = fl j)
    (hrb : ∀ j < nD, c.nmem (Rb + j) = rb j) (hlv : ∀ j < nD, c.nmem (Lb + j) = Lv j) :
    ∃ c' t, Exec P W kcnInit c c' t ∧ t ≤ 3 ∧
      (KNCtx nD Lb Sb Rb Ob nV k nF fl rb Lv c' ∧ c'.nreg 2112 = 0 ∧
        (∀ r, r < 2110 ∨ 2140 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO
  unfold kcnInit
  exec_block
  all_goals try omega
  refine ⟨by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hfl, hrb, hlv⟩, ?_, fun r hr => ?_,
    rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first | assumption | skip
  simp (disch := omega) only [upd_other]

/-- **The residues of the real constants, on index functions.** From the flags `fl` (at `Sb`),
the reach bits `rb` (at `Rb`) and the natural lengths `Lv` (at `Lb`) of the `nD` darts, with
`r2100 … r2107 = nD, Lb, Sb, Rb, Ob, nV, k, nF`, `kcnProg` ends within `33 nD + 45` steps with
`Hc = kcnHc nV nF Wv k` (`Wv = Σ_{fl j > 0} Lv j`) in `r2125`, `Mo = 2 Hc + 1` in `r2126`, the
residues modulo `Mo` of the weights (`kcnWtW`) at `Ob + j`, of the labels (`kcnPhW`) at
`Ob + nD + j`, `0` at `Ob + 2 nD + j`, and those of `kcnL`, `kcnTh`, `kcnH0` at `Ob + 3 nD`,
`+ 1`, `+ 2`; the rest of the natural memory, the natural registers outside `[2110, 2140)`, the
reals and the output are kept. -/
theorem kcnProg_exec (hL : KNLay nD Lb Sb Rb Ob Wd) (hWd : Wd ≤ W)
    (hH : 2 * kcnHc nV nF (kcnSum fl Lv nD) k + 1 ≤ W) (c : Config) (hc : WordsBounded W c)
    (h00 : c.nreg 2100 = nD) (h01 : c.nreg 2101 = Lb) (h02 : c.nreg 2102 = Sb)
    (h03 : c.nreg 2103 = Rb) (h04 : c.nreg 2104 = Ob) (h05 : c.nreg 2105 = nV)
    (h06 : c.nreg 2106 = k) (h07 : c.nreg 2107 = nF) (hfl : ∀ j < nD, c.nmem (Sb + j) = fl j)
    (hrb : ∀ j < nD, c.nmem (Rb + j) = rb j) (hlv : ∀ j < nD, c.nmem (Lb + j) = Lv j) :
    ∃ c' t, Exec P W kcnProg c c' t ∧ t ≤ 33 * nD + 45 ∧
      ((∀ j < nD, c'.nmem (Ob + j) = kcnWtW fl rb Lv (2 * kcnHc nV nF (kcnSum fl Lv nD) k + 1)
            (kcnL nV (kcnSum fl Lv nD) % (2 * kcnHc nV nF (kcnSum fl Lv nD) k + 1)) j ∧
          c'.nmem (Ob + nD + j) = kcnPhW fl Lv (2 * kcnHc nV nF (kcnSum fl Lv nD) k + 1) j ∧
          c'.nmem (Ob + 2 * nD + j) = 0) ∧
        c'.nmem (Ob + 3 * nD) =
          kcnL nV (kcnSum fl Lv nD) % (2 * kcnHc nV nF (kcnSum fl Lv nD) k + 1) ∧
        c'.nmem (Ob + 3 * nD + 1) =
          kcnTh nV (kcnSum fl Lv nD) % (2 * kcnHc nV nF (kcnSum fl Lv nD) k + 1) ∧
        c'.nmem (Ob + 3 * nD + 2) =
          kcnH0 nV (kcnSum fl Lv nD) k % (2 * kcnHc nV nF (kcnSum fl Lv nD) k + 1) ∧
        c'.nreg 2125 = kcnHc nV nF (kcnSum fl Lv nD) k ∧
        c'.nreg 2126 = 2 * kcnHc nV nF (kcnSum fl Lv nD) k + 1 ∧
        (∀ a, a < Ob ∨ Ob + 3 * nD + 3 ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 2110 ∨ 2140 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO
  have hS : kcnSum fl Lv nD ≤ W := by
    have := (kcn_bounds nV nF (kcnSum fl Lv nD) k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1; omega
  unfold kcnProg
  refine spec_seq ?_
  refine spec_use (kcnInit_exec (P := P) hL hWd c hc h00 h01 h02 h03 h04 h05 h06 h07 hfl hrb
    hlv) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hC₁, z12, zn, znm, zr, zrm, zo⟩
  refine spec_seq ?_
  refine spec_use (kcnA_exec (P := P) hL hS hWd c₁ hw₁ hC₁ z12) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨a12, an, anm, ar, arm, ao⟩
  have hC₂ := hC₁.frame (c' := c₂) hL (fun r hr => an r (by omega)) (fun a _ => by rw [anm])
  refine spec_seq ?_
  refine spec_use (kcnC_exec (P := P) hL hWd hH c₂ hw₂ hC₂ a12) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨b25, b26, b27, b1, b2, b3, bnm, bn, br, brm, bo⟩
  have hC₃ := hC₂.frame (c' := c₃) hL (fun r hr => bn r (by omega))
    (fun a ha => bnm a (by omega))
  refine spec_use (kcnD_exec (P := P) hL hWd c₃ hw₃ hC₃ b26 b27) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨d1, dnm, dn, dr, drm, d_o⟩
  refine ⟨by omega, d1, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [dnm _ (by omega), b1]
  · rw [dnm _ (by omega), b2]
  · rw [dnm _ (by omega), b3]
  · rw [dn _ (by omega), b25]
  · rw [dn _ (by omega), b26]
  · rw [dnm a (by omega), bnm a (by omega), anm, znm]
  · rw [dn _ (by omega), bn _ (by omega), an _ (by omega), zn _ hr]
  · rw [dr, br, ar, zr]
  · rw [drm, brm, arm, zrm]
  · rw [d_o, bo, ao, zo]

/-! ### The field `res` of the natural slot -/

section Slot

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

lemma kcnSum_eq_sum (fl Lv : ℕ → ℕ) (n : ℕ) :
    kcnSum fl Lv n = ∑ j ∈ range n, (if 0 < fl j then Lv j else 0) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_range_succ, ← ih]; rfl

/-- `tripW`, by dart number, for lengths `≥ 0` on the piece. -/
theorem kcnSum_tripW (S : Finset D) (ℓ : D → ℤ) (hnn : ∀ d ∈ S, 0 ≤ ℓ d)
    (σ : D ≃ Fin (Fintype.card D)) {fl Lv : ℕ → ℕ} (hfl : ∀ d, 0 < fl (σ d) ↔ d ∈ S)
    (hlv : ∀ d ∈ S, Lv (σ d) = (ℓ d).toNat) :
    kcnSum fl Lv (Fintype.card D) = (Klein.tripW S ℓ).toNat := by
  classical
  rw [kcnSum_eq_sum, ← Fin.sum_univ_eq_sum_range,
    ← Equiv.sum_comp σ (fun i : Fin (Fintype.card D) => if 0 < fl i then Lv i else 0)]
  have e : ∀ d, (if 0 < fl (σ d) then Lv (σ d) else 0) = if d ∈ S then (ℓ d).toNat else 0 :=
    fun d => by
      by_cases hd : d ∈ S
      · simp only [(hfl d).2 hd, hd, hlv d hd, ↓reduceIte]
      · have h : ¬ 0 < fl (σ d) := fun h => hd ((hfl d).1 h)
        simp only [h, hd, ↓reduceIte]
  simp only [e, sum_ite_mem, univ_inter]
  have hW : Klein.tripW S ℓ = ((∑ d ∈ S, (ℓ d).toNat : ℕ) : ℤ) := by
    unfold Klein.tripW
    push_cast
    exact sum_congr rfl fun d hd => by rw [abs_of_nonneg (hnn d hd), Int.toNat_of_nonneg (hnn d hd)]
  rw [hW, Int.toNat_natCast]

lemma resW_natCast (Mo x : ℕ) : Klein.resW Mo (((x : ℤ) : ℝ)) = x % Mo := by
  unfold Klein.resW
  rw [Int.floor_intCast, ← Int.natCast_mod, Int.toNat_natCast]

/-- **`Hc` bounds `kleinHI`** (`Klein.kleinHI_le`). -/
theorem kcnHc_ge (S : Finset D) (ℓ : D → ℤ) (k : ℕ) :
    Klein.kleinHI V F S ℓ k ≤
      (kcnHc (Fintype.card V) (Fintype.card F) (Klein.tripW S ℓ).toNat k : ℝ) := by
  have h := Klein.kleinHI_le (V := V) (F := F) (S := S) (ℓ := ℓ) (k := k)
  have hW : (((Klein.tripW S ℓ).toNat : ℕ) : ℝ) = (Klein.tripW S ℓ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg Klein.tripW_nonneg
  refine h.trans (le_of_eq ?_)
  simp only [kcnHc]
  push_cast
  rw [hW]
  ring

/-- The integer constants as natural numbers. -/
lemma tripL_eq (S : Finset D) (ℓ : D → ℤ) :
    Klein.tripL V S ℓ = (kcnL (Fintype.card V) (Klein.tripW S ℓ).toNat : ℤ) := by
  have hW := Int.toNat_of_nonneg (Klein.tripW_nonneg (S := S) (ℓ := ℓ))
  simp only [Klein.tripL, Klein.tripB, kcnL]
  push_cast
  rw [hW]

lemma tripTh_eq (S : Finset D) (ℓ : D → ℤ) :
    Klein.tripTh V S ℓ = (kcnTh (Fintype.card V) (Klein.tripW S ℓ).toNat : ℤ) := by
  have hW := Int.toNat_of_nonneg (Klein.tripW_nonneg (S := S) (ℓ := ℓ))
  simp only [Klein.tripTh, kcnTh, Klein.tripL, Klein.tripB, kcnL]
  rw [Nat.cast_sub (by omega)]
  push_cast
  rw [hW]

lemma tripK_eq (S : Finset D) (ℓ : D → ℤ) :
    Klein.tripK V S ℓ = (kcnK (Fintype.card V) (Klein.tripW S ℓ).toNat : ℤ) := by
  have hW := Int.toNat_of_nonneg (Klein.tripW_nonneg (S := S) (ℓ := ℓ))
  have hL := tripL_eq (V := V) S ℓ
  simp only [Klein.tripK, Klein.driftK, kcnK]
  rw [hL, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg Klein.tripW_nonneg,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) Klein.tripW_nonneg)]
  push_cast
  rw [hW]

lemma tripH0_eq (S : Finset D) (ℓ : D → ℤ) (k : ℕ) :
    Klein.tripH0 V S ℓ k = (kcnH0 (Fintype.card V) (Klein.tripW S ℓ).toNat k : ℤ) := by
  simp only [Klein.tripH0, kcnH0, tripTh_eq (V := V) S ℓ, tripK_eq (V := V) S ℓ]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
/-- **The output of `kcnProg` is the field `res` of `KSlotN`**: for a map `M`, `k`, `g`, a piece
`S`, lengths `ℓ ≥ 0` on `S` and a numbering `σ` of the darts, with the flags of `S` at
`Sb + σ d` (positive exactly on `S`), the reach bits at `Rb + σ d` (positive, on `S`, exactly
when `M.tail d` is reached from the target of the first move) and the natural lengths
`(ℓ d).toNat` at `Lb + σ d` (on `S`), `kcnProg` writes at `Ob + a` (`a < 3 #D + 3`) the residue
modulo `2 Hc + 1` of Klein's real constant `kConst … a`, for
`Hc = kcnHc #V #F (tripW S ℓ).toNat k ≥ kleinHI`, left in `r2125` (and `2 Hc + 1` in `r2126`),
within `33 #D + 45` steps. -/
theorem kcnProg_kslot {M : CombMap D V F} {kk : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
    (hnn : ∀ d ∈ S, 0 ≤ ℓ d) (σ : D ≃ Fin (Fintype.card D)) {Lb Sb Rb Ob : ℕ}
    (hL : KNLay (Fintype.card D) Lb Sb Rb Ob Wd) (hWd : Wd ≤ W)
    (hH : 2 * kcnHc (Fintype.card V) (Fintype.card F) (Klein.tripW S ℓ).toNat kk + 1 ≤ W)
    (c : Config) (hc : WordsBounded W c) (h00 : c.nreg 2100 = Fintype.card D)
    (h01 : c.nreg 2101 = Lb) (h02 : c.nreg 2102 = Sb) (h03 : c.nreg 2103 = Rb)
    (h04 : c.nreg 2104 = Ob) (h05 : c.nreg 2105 = Fintype.card V) (h06 : c.nreg 2106 = kk)
    (h07 : c.nreg 2107 = Fintype.card F)
    (hfl : ∀ d, 0 < c.nmem (Sb + σ d) ↔ d ∈ S)
    (hrb : ∀ d ∈ S, 0 < c.nmem (Rb + σ d) ↔
      MSSP.Reach (MSSP.pieceGraph M S ℓ) (Klein.tripDst M kk g 0) (M.tail d))
    (hlv : ∀ d ∈ S, c.nmem (Lb + σ d) = (ℓ d).toNat) :
    ∃ c' t, Exec P W kcnProg c c' t ∧ t ≤ 33 * Fintype.card D + 45 ∧
      (∀ a < 3 * Fintype.card D + 3, c'.nmem (Ob + a) =
        Klein.resW (2 * kcnHc (Fintype.card V) (Fintype.card F) (Klein.tripW S ℓ).toNat kk + 1)
          (Klein.kConst V M kk g S ℓ σ a : ℝ)) ∧
      c'.nreg 2125 = kcnHc (Fintype.card V) (Fintype.card F) (Klein.tripW S ℓ).toNat kk ∧
      c'.nreg 2126 = 2 * kcnHc (Fintype.card V) (Fintype.card F) (Klein.tripW S ℓ).toNat kk + 1 ∧
      Klein.kleinHI V F S ℓ kk ≤
        (kcnHc (Fintype.card V) (Fintype.card F) (Klein.tripW S ℓ).toNat kk : ℝ) ∧
      (∀ a, a < Ob ∨ Ob + 3 * Fintype.card D + 3 ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2110 ∨ 2140 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  have hsum := kcnSum_tripW S ℓ hnn σ (fl := fun j => c.nmem (Sb + j))
    (Lv := fun j => c.nmem (Lb + j)) hfl hlv
  rw [← hsum] at hH ⊢
  obtain ⟨c', t, ex, ht, hw, h1, h2, h3, h25, h26, hfr, hn, hr, hrm, ho⟩ :=
    kcnProg_exec (P := P) (fl := fun j => c.nmem (Sb + j)) (rb := fun j => c.nmem (Rb + j))
      (Lv := fun j => c.nmem (Lb + j)) hL hWd hH c hc h00 h01 h02 h03 h04 h05 h06 h07
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  rw [hsum] at hw h1 h2 h3 h25 h26 ⊢
  set Mo := 2 * kcnHc (Fintype.card V) (Fintype.card F) (Klein.tripW S ℓ).toNat kk + 1 with hMo
  refine ⟨c', t, ex, ht, fun a ha => ?_, h25, h26, kcnHc_ge S ℓ kk, hfr, hn, hr, hrm, ho⟩
  have hL' : (Klein.tripL V S ℓ : ℝ) = ((kcnL (Fintype.card V) (Klein.tripW S ℓ).toNat : ℤ) : ℝ) := by
    rw [tripL_eq]
  by_cases h1a : a < Fintype.card D
  · -- the weights
    set x := σ.symm ⟨a, h1a⟩ with hx
    have hxa : (σ x : ℕ) = a := by simp [hx]
    have e := Klein.kConst_wt (V := V) (M := M) (k := kk) (g := g) (S := S) (ℓ := ℓ) (σ := σ) x
    simp only [Klein.aWT, zero_add, hxa] at e
    rw [e, (hw a h1a).1]
    unfold kcnWtW Klein.tripWt
    have hfx := hfl x
    rw [hxa] at hfx
    by_cases hS : x ∈ S
    · have h := hfx.2 hS
      have hrx := hrb x hS
      rw [hxa] at hrx
      have hlx := hlv x hS
      rw [hxa] at hlx
      by_cases hR : MSSP.Reach (MSSP.pieceGraph M S ℓ) (Klein.tripDst M kk g 0) (M.tail x)
      · have h' := hrx.2 hR
        simp only [h, h', hS, hR, and_self, ↓reduceIte, hlx]
        rw [← resW_natCast, Int.toNat_of_nonneg (hnn x hS)]
      · have h' : ¬ 0 < c.nmem (Rb + a) := fun h' => hR (hrx.1 h')
        simp only [h, h', hS, hR, and_false, ↓reduceIte]
        rw [hL', resW_natCast]
    · have h : ¬ 0 < c.nmem (Sb + a) := fun h => hS (hfx.1 h)
      simp only [h, hS, false_and, ↓reduceIte]
      rw [hL', resW_natCast]
  by_cases h2a : a < 2 * Fintype.card D
  · -- the labels
    set x := σ.symm ⟨a - Fintype.card D, by omega⟩ with hx
    have hxa : (σ x : ℕ) = a - Fintype.card D := by simp [hx]
    have e := Klein.kConst_ph (V := V) (M := M) (k := kk) (g := g) (S := S) (ℓ := ℓ) (σ := σ) x
    simp only [Klein.aPH, hxa, show Fintype.card D + (a - Fintype.card D) = a by omega] at e
    rw [e, show Ob + a = Ob + Fintype.card D + (a - Fintype.card D) by omega, (hw (a - Fintype.card D) (by omega)).2.1]
    unfold kcnPhW Klein.tripφ
    have hfx := hfl x
    rw [hxa] at hfx
    by_cases hS : x ∈ S
    · have h := hfx.2 hS
      have hlx := hlv x hS
      rw [hxa] at hlx
      simp only [h, hS, ↓reduceIte, hlx]
      rw [← resW_natCast, Int.toNat_of_nonneg (hnn x hS)]
    · have h : ¬ 0 < c.nmem (Sb + (a - Fintype.card D)) := fun h => hS (hfx.1 h)
      simp only [h, hS, ↓reduceIte]
      rw [show ((0 : ℤ) : ℝ) = (((0 : ℕ) : ℤ) : ℝ) by simp, resW_natCast, Nat.zero_mod]
  by_cases h3a : a < 3 * Fintype.card D
  · -- the zeros
    have e : Klein.kConst V M kk g S ℓ σ a = 0 := by
      unfold Klein.kConst
      simp only [h1a, h2a, ↓reduceDIte, show a ≠ 3 * Fintype.card D by omega,
        show a ≠ 3 * Fintype.card D + 1 by omega, show a ≠ 3 * Fintype.card D + 2 by omega, ↓reduceIte]
    rw [e, show Ob + a = Ob + 2 * Fintype.card D + (a - 2 * Fintype.card D) by omega, (hw (a - 2 * Fintype.card D) (by omega)).2.2,
      show ((0 : ℤ) : ℝ) = (((0 : ℕ) : ℤ) : ℝ) by simp, resW_natCast, Nat.zero_mod]
  -- the three constants
  have : a = 3 * Fintype.card D ∨ a = 3 * Fintype.card D + 1 ∨ a = 3 * Fintype.card D + 2 := by omega
  rcases this with rfl | rfl | rfl
  · have e := Klein.kConst_tl (V := V) (M := M) (k := kk) (g := g) (S := S) (ℓ := ℓ) (σ := σ)
    simp only [Klein.aTL] at e
    rw [e, h1, hL', resW_natCast]
  · have e := Klein.kConst_th (V := V) (M := M) (k := kk) (g := g) (S := S) (ℓ := ℓ) (σ := σ)
    simp only [Klein.aTH] at e
    rw [e, ← Nat.add_assoc, h2, tripTh_eq, resW_natCast]
  · have e := Klein.kConst_h0 (V := V) (M := M) (k := kk) (g := g) (S := S) (ℓ := ℓ) (σ := σ)
    simp only [Klein.aH0] at e
    rw [e, ← Nat.add_assoc, h3, tripH0_eq, resW_natCast]

end Slot

end NegSSSP

end PlanarFlow
