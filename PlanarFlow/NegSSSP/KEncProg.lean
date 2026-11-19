module

public import PlanarFlow.NegSSSP.KEncConcrete

/-!
# The real constants of the one-face encoding, on the machine

The slot `NegSSSP.KSlot` of the encoding of a one-face instance holds, besides the input words,
the real constants of Klein's trip in the real memory at `Rk`: the weights
`Klein.tripWt M k g S ℓ 0` and the labels `Klein.tripφ S ℓ` by dart number, and the constants
`Klein.tripL`, `Klein.tripTh`, `Klein.tripH0`. Here a program writes them, from the lengths by
dart number (real memory, at `Lb`), the flags of the piece `S` (natural memory, at `Sb`) and the
reach bits from the target of the first move (natural memory, at `Rb`), with `nV = #V` and `k`:

* `sel_exec`: a real register chosen by a natural comparison.
* `cntLoop_exec`: `#V` and `k + 1` as reals (the machine has no conversion from naturals to
  reals: `n` additions of `1`).
* `kcA_exec`: `tripW = Σ_S |ℓ|` (by comparisons with `0`); `kcC_exec`: `tripB`, `tripL`,
  `tripTh`, `tripK`, `tripH0` and their stores; `kcD_exec`: the weights and labels by dart.
* `kcProg_exec`: **the whole program** (`kcProg`, within `36 nD + 4 nV + 4 k + 56` steps), on
  index functions; `kcProg_kslot`: **its output is the real part of `KSlot`** (`wt`, `ph`, `tl`,
  `th`, `h0` of `NegSSSP.KSlot` at `Rk = Ob`) for any map, piece, lengths and numbering `σ` of
  the darts read by the flags, reach bits and lengths.

The lengths are reals: for the perturbed lengths `MSSP.pertBy σ` of the encoding, of size
`2^|D|`, the program does `O(nD + nV + k)` real operations whatever their size.

Registers: natural `1300 … 1306` (inputs `nD`, `Lb`, `Sb`, `Rb`, `Ob`, `nV`, `k`), `1310 … 1315`
(scratch); real `1350 … 1364` (scratch). Natural memory is not written; real memory only in
`[Ob, Ob + 3 nD + 3)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### A choice between two real registers -/

/-- `rreg r := if nreg a < nreg b then rreg x else rreg y`. -/
def sel (a b r x y : ℕ) : Stmt := .ifLtN a b (.instr (.copyR r x)) (.instr (.copyR r y))

theorem sel_exec (a b r x y : ℕ) (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (sel a b r x y) c c' t ∧ t ≤ 3 ∧
      c' = { c with
        rreg := upd c.rreg r (if c.nreg a < c.nreg b then c.rreg x else c.rreg y) } := by
  unfold sel
  by_cases h : c.nreg a < c.nreg b
  · exact spec_ifLtN_true h (spec_instr (Exec.copyR hc r x) fun _ =>
      ⟨by omega, by simp only [h, ↓reduceIte]⟩)
  · exact spec_ifLtN_false h (spec_instr (Exec.copyR hc r y) fun _ =>
      ⟨by omega, by simp only [h, ↓reduceIte]⟩)

/-! ### The program -/

/-- The constants: `r1310 = 1`, `r1314 = 0`, the reals `r1350 = 0` (the sum), `r1351 = 0`,
`r1359 = 1`. -/
def kcInit : Stmt :=
  block [.constN 1310 1, .constN 1314 0, .constR 1350 0, .constR 1351 0, .constR 1359 1]

/-- The dart `j = r1311` of `tripW`: `r1350 += |S[j] > 0 ? L[j] : 0|`. -/
def kcABody : Stmt :=
  .seq (block [.addN 1312 1302 1311, .loadN 1313 1312, .addN 1312 1301 1311, .loadR 1352 1312]) <|
  .seq (sel 1314 1313 1360 1352 1351) <|
  .seq (absAdd 1350 1360 1353 1351) (block [.addN 1311 1311 1310])

/-- `tripW` into the real `1350`. -/
def kcA : Stmt := .seq (block [.constN 1311 0]) (.whileLtN 1311 1300 kcABody)

/-- `rreg rr += 1`, `nreg bR` times. -/
def cntLoop (bR rr : ℕ) : Stmt :=
  .seq (block [.constN 1311 0]) (.whileLtN 1311 bR (block [.addR rr rr 1359, .addN 1311 1311 1310]))

/-- `#V` into the real `1354`, `k + 1` into the real `1355`. -/
def kcB : Stmt :=
  .seq (block [.constR 1354 0]) (.seq (cntLoop 1305 1354)
    (.seq (block [.constR 1355 1]) (cntLoop 1306 1355)))

/-- The constants: `tripB` (`1361`), `tripL` (`1356`), `tripTh` (`1357`), `tripK` (`1362`),
`tripH0` (`1358`), stored at `Ob + 3 nD`, `+ 1`, `+ 2`. -/
def kcC : Stmt :=
  .seq (block [.mulR 1361 1354 1350, .constR 1364 4, .mulR 1356 1364 1361,
    .addR 1356 1356 1350, .addR 1356 1356 1359, .constR 1364 2, .mulR 1363 1364 1361,
    .subR 1357 1356 1363, .constR 1362 0]) <|
  .seq (absAdd 1362 1356 1353 1351) <| .seq (absAdd 1362 1350 1353 1351) <|
  .seq (absAdd 1362 1361 1353 1351) <| .seq (absAdd 1362 1361 1353 1351) <|
  block [.addR 1363 1354 1359, .mulR 1363 1363 1362, .mulR 1363 1355 1363,
    .addR 1358 1357 1363, .constN 1312 3, .mulN 1312 1312 1300, .addN 1312 1312 1304,
    .storeR 1312 1356, .addN 1312 1312 1310, .storeR 1312 1357, .addN 1312 1312 1310,
    .storeR 1312 1358]

/-- The dart `j = r1311`: `Ob[j] := S[j] > 0 ∧ R[j] > 0 ? L[j] : tripL` (the weight),
`Ob[nD + j] := S[j] > 0 ? L[j] : 0` (the label). -/
def kcDBody : Stmt :=
  .seq (block [.addN 1312 1302 1311, .loadN 1313 1312, .addN 1312 1303 1311, .loadN 1315 1312,
    .addN 1312 1301 1311, .loadR 1352 1312]) <|
  .seq (sel 1314 1313 1360 1352 1351) <|
  .seq (sel 1314 1315 1363 1352 1356) <|
  .seq (sel 1314 1313 1363 1363 1356) <|
  block [.addN 1312 1304 1311, .storeR 1312 1363, .addN 1312 1312 1300, .storeR 1312 1360,
    .addN 1311 1311 1310]

/-- The weights and the labels by dart. -/
def kcD : Stmt := .seq (block [.constN 1311 0]) (.whileLtN 1311 1300 kcDBody)

/-- **The real constants of the encoding.** -/
def kcProg : Stmt := .seq kcInit (.seq kcA (.seq kcB (.seq kcC kcD)))

/-! ### The data -/

/-- The layout of `kcProg`. -/
structure KCLay (nD Lb Sb Rb Ob nV k W : ℕ) : Prop where
  wS : Sb + nD ≤ W
  wR : Rb + nD ≤ W
  wL : Lb + nD ≤ W
  wO : Ob + 3 * nD + 3 ≤ W
  dj : Lb + nD ≤ Ob ∨ Ob + 3 * nD + 3 ≤ Lb
  wV : nV + 1 ≤ W
  wk : k + 1 ≤ W
  w3 : 3 ≤ W

/-- The inputs of `kcProg` and its constants, kept by every stage. -/
structure KCCtx (nD Lb Sb Rb Ob nV k : ℕ) (fl rb : ℕ → ℕ) (Lv : ℕ → ℝ) (c : Config) : Prop where
  r1300 : c.nreg 1300 = nD
  r1301 : c.nreg 1301 = Lb
  r1302 : c.nreg 1302 = Sb
  r1303 : c.nreg 1303 = Rb
  r1304 : c.nreg 1304 = Ob
  r1305 : c.nreg 1305 = nV
  r1306 : c.nreg 1306 = k
  r1310 : c.nreg 1310 = 1
  r1314 : c.nreg 1314 = 0
  z : c.rreg 1351 = 0
  one : c.rreg 1359 = 1
  fl : ∀ j < nD, c.nmem (Sb + j) = fl j
  rb : ∀ j < nD, c.nmem (Rb + j) = rb j
  lv : ∀ j < nD, c.rmem (Lb + j) = Lv j

variable {nD Lb Sb Rb Ob nV k : ℕ} {fl rb : ℕ → ℕ} {Lv : ℕ → ℝ}

theorem KCCtx.frame {c c' : Config} (h : KCCtx nD Lb Sb Rb Ob nV k fl rb Lv c)
    (hn : ∀ r, r < 1311 → c'.nreg r = c.nreg r) (h14 : c'.nreg 1314 = c.nreg 1314)
    (hz : c'.rreg 1351 = c.rreg 1351) (h1 : c'.rreg 1359 = c.rreg 1359) (hm : c'.nmem = c.nmem)
    (hl : ∀ j < nD, c'.rmem (Lb + j) = c.rmem (Lb + j)) :
    KCCtx nD Lb Sb Rb Ob nV k fl rb Lv c' :=
  ⟨(hn _ (by omega)).trans h.r1300, (hn _ (by omega)).trans h.r1301,
    (hn _ (by omega)).trans h.r1302, (hn _ (by omega)).trans h.r1303,
    (hn _ (by omega)).trans h.r1304, (hn _ (by omega)).trans h.r1305,
    (hn _ (by omega)).trans h.r1306, (hn _ (by omega)).trans h.r1310, h14.trans h.r1314,
    hz.trans h.z, h1.trans h.one, fun j hj => by rw [hm]; exact h.fl j hj,
    fun j hj => by rw [hm]; exact h.rb j hj, fun j hj => by rw [hl j hj]; exact h.lv j hj⟩


/-! ### `tripW` -/

/-- The term of the dart `j` in `tripW`. -/
def kcTerm (fl : ℕ → ℕ) (Lv : ℕ → ℝ) (j : ℕ) : ℝ := if 0 < fl j then |Lv j| else 0

theorem kcA_exec (hL : KCLay nD Lb Sb Rb Ob nV k W) (c : Config) (hc : WordsBounded W c)
    (hC : KCCtx nD Lb Sb Rb Ob nV k fl rb Lv c) :
    ∃ c' t, Exec P W kcA c c' t ∧ t ≤ 14 * nD + 3 ∧
      (c'.rreg 1350 = c.rreg 1350 + ∑ j ∈ range nD, kcTerm fl Lv j ∧
        (∀ r, r ≠ 1350 → r ≠ 1352 → r ≠ 1353 → r ≠ 1360 → c'.rreg r = c.rreg r) ∧
        (∀ r, r < 1311 ∨ 1315 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1314 = c.nreg 1314 ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wL; have := hL.w3
  unfold kcA
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    c'.rreg 1350 = c.rreg 1350 + ∑ j ∈ range i, kcTerm fl Lv j ∧
      (∀ r, r ≠ 1350 → r ≠ 1352 → r ≠ 1353 → r ≠ 1360 → c'.rreg r = c.rreg r) ∧
      (∀ r, r < 1311 ∨ 1315 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1314 = c.nreg 1314 ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1311) (bR := 1300) (body := kcABody) J (K := 12)
    (n := nD) _ ‹_› (by config_simp) (by config_simp; exact hC.r1300) ?_
    (fun i c₁ hi hw ha hb ⟨g50, gr, gn, g14, gnm, grm, go⟩ => by
      have e01 : c₁.nreg 1301 = Lb := (gn 1301 (by omega)).trans hC.r1301
      have e02 : c₁.nreg 1302 = Sb := (gn 1302 (by omega)).trans hC.r1302
      have e10 : c₁.nreg 1310 = 1 := (gn 1310 (by omega)).trans hC.r1310
      have e14 : c₁.nreg 1314 = 0 := g14.trans hC.r1314
      have z51 : c₁.rreg 1351 = 0 :=
        (gr 1351 (by decide) (by decide) (by decide) (by decide)).trans hC.z
      have xf : c₁.nmem (Sb + i) = fl i := by rw [gnm]; exact hC.fl i hi
      have xl : c₁.rmem (Lb + i) = Lv i := by rw [grm]; exact hC.lv i hi
      unfold kcABody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e01, e02, ha]); omega)
      refine spec_seq ?_
      refine spec_use (sel_exec (P := P) 1314 1313 1360 1352 1351 _ ‹_›) ?_
      intro c₂ k₂ hk₂ hw₂ hc₂
      have y60 : c₂.rreg 1360 = if 0 < fl i then Lv i else 0 := by
        rw [hc₂]; config_simp; simp only [e01, e02, e14, ha, xf, xl, z51]
      have q51 : c₂.rreg 1351 = 0 := by rw [hc₂]; config_simp; exact z51
      refine spec_seq ?_
      refine spec_use (absAdd_exec (P := P) (acc := 1350) (x := 1360) (t := 1353) (z := 1351)
        (by decide) (by decide) (by decide) (by decide) (by decide) c₂ hw₂ q51) ?_
      intro c₃ k₃ hk₃ hw₃ ⟨b50, br, bn, bnm, brm, bo⟩
      have q11 : c₃.nreg 1311 = i := by rw [bn, hc₂]; config_simp; exact ha
      have q10 : c₃.nreg 1310 = 1 := by rw [bn, hc₂]; config_simp; exact e10
      exec_block
      all_goals try ((try config_simp); (try simp only [q11, q10]); omega)
      dsimp only [J]
      config_simp
      simp only [q11, q10]
      refine ⟨by omega, trivial, by rw [bn, hc₂]; config_simp; exact hb, ?_,
        fun r h1 h2 h3 h4 => ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
      · rw [b50, y60, hc₂]
        config_simp
        rw [g50, sum_range_succ]
        unfold kcTerm
        split_ifs <;> simp [add_assoc]
      · rw [br r h1 h3, hc₂]; config_simp
        simp only [upd_apply, h4, h2, ↓reduceIte]
        exact gr r h1 h2 h3 h4
      · simp only [upd_apply]
        split_ifs
        · omega
        · rw [bn, hc₂]; config_simp; simp only [upd_apply]
          split_ifs <;> first | omega | exact gn r hr
      · rw [bn, hc₂]; config_simp; exact g14
      · rw [bnm, hc₂]; exact gnm
      · rw [brm, hc₂]; exact grm
      · rw [bo, hc₂]; exact go)) ?_
  · refine ⟨by simp, fun r _ _ _ _ => rfl, fun r hr => ?_, ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> omega
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, g50, gr, gn, g14, gnm, grm, go⟩ := hJ₂
  refine ⟨by omega, g50, gr, fun r hr => ?_, ?_, gnm, grm, go⟩
  · rw [gn r hr]
  · rw [g14]

/-! ### `#V` and `k + 1` as reals -/

theorem cntLoop_exec {bR rr n : ℕ} (hbR : bR < 1311 ∨ 1311 < bR) (hn : n + 1 ≤ W) (c : Config)
    (hc : WordsBounded W c) (hb : c.nreg bR = n) (h10 : c.nreg 1310 = 1)
    (h59 : c.rreg 1359 = 1) (hrr : rr ≠ 1359) :
    ∃ c' t, Exec P W (cntLoop bR rr) c c' t ∧ t ≤ 4 * n + 3 ∧
      (c'.rreg rr = c.rreg rr + n ∧ (∀ r, r ≠ rr → c'.rreg r = c.rreg r) ∧
        (∀ r, r ≠ 1311 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold cntLoop
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    c'.rreg rr = c.rreg rr + i ∧ (∀ r, r ≠ rr → c'.rreg r = c.rreg r) ∧
      (∀ r, r ≠ 1311 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1311) (bR := bR)
    (body := block [.addR rr rr 1359, .addN 1311 1311 1310]) J (K := 2)
    (n := n) _ ‹_› (by config_simp) (by config_simp; simp only [upd_apply]; split_ifs <;> omega)
    ?_
    (fun i c₁ hi hw ha hb' ⟨g, gr, gn, gnm, grm, go⟩ => by
      have e10 : c₁.nreg 1310 = 1 := (gn 1310 (by omega)).trans h10
      have e59 : c₁.rreg 1359 = 1 := (gr 1359 (Ne.symm hrr)).trans h59
      exec_block
      all_goals try ((try config_simp); (try simp only [ha, e10]); omega)
      dsimp only [J]
      config_simp
      simp only [ha, e10]
      refine ⟨by omega, trivial, ?_, ?_, fun r hr => ?_, fun r hr => ?_, gnm, grm, go⟩
      · simp only [upd_apply]; split_ifs <;> omega
      · simp only [e59, g]; push_cast; ring
      · simp only [upd_apply, hr, ↓reduceIte]; exact gr r hr
      · simp only [upd_apply, hr, ↓reduceIte]; exact gn r hr)) ?_
  · refine ⟨by simp, fun r _ => rfl, fun r hr => ?_, rfl, rfl, rfl⟩
    config_simp; simp only [upd_apply, hr, ↓reduceIte]
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, g, gr, gn, gnm, grm, go⟩ := hJ₂
  exact ⟨by omega, g, gr, gn, gnm, grm, go⟩

theorem kcB_exec (hL : KCLay nD Lb Sb Rb Ob nV k W) (c : Config) (hc : WordsBounded W c)
    (h05 : c.nreg 1305 = nV) (h06 : c.nreg 1306 = k) (h10 : c.nreg 1310 = 1)
    (h59 : c.rreg 1359 = 1) :
    ∃ c' t, Exec P W kcB c c' t ∧ t ≤ 4 * nV + 4 * k + 8 ∧
      (c'.rreg 1354 = nV ∧ c'.rreg 1355 = k + 1 ∧
        (∀ r, r ≠ 1354 → r ≠ 1355 → c'.rreg r = c.rreg r) ∧
        (∀ r, r ≠ 1311 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wV; have := hL.wk
  unfold kcB
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (cntLoop_exec (P := P) (bR := 1305) (rr := 1354) (n := nV) (by omega)
    (by omega) _ ‹_› (by config_simp; exact h05) (by config_simp; exact h10)
    (by config_simp; exact h59) (by decide)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨a54, ar, an, anm, arm, ao⟩
  refine spec_seq ?_
  exec_block
  refine spec_use (cntLoop_exec (P := P) (bR := 1306) (rr := 1355) (n := k) (by omega)
    (by omega) _ ‹_› (by config_simp; rw [an 1306 (by omega)]; config_simp; exact h06)
    (by config_simp; rw [an 1310 (by omega)]; config_simp; exact h10)
    (by config_simp; rw [ar 1359 (by decide)]; config_simp; exact h59) (by decide)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨b55, br, bn, bnm, brm, bo⟩
  refine ⟨by omega, ?_, ?_, fun r h1 h2 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [br 1354 (by decide)]; config_simp; rw [a54]; config_simp; simp
  · rw [b55]; config_simp; ring
  · rw [br r h2]; config_simp; simp only [upd_apply, h2, ↓reduceIte]
    rw [ar r h1]; config_simp; simp only [upd_apply, h1, ↓reduceIte]
  · rw [bn r hr]; config_simp; rw [an r hr]
  · rw [bnm]; config_simp; rw [anm]
  · rw [brm]; config_simp; rw [arm]
  · rw [bo]; config_simp; rw [ao]

/-! ### The constants -/

/-- `tripL` from `#V` and `tripW` (as reals). -/
def kcL (Vr Wv : ℝ) : ℝ := 4 * (Vr * Wv) + Wv + 1

/-- `tripTh`. -/
def kcTh (Vr Wv : ℝ) : ℝ := kcL Vr Wv - 2 * (Vr * Wv)

/-- `tripH0`. -/
def kcH0 (Vr Wv Kr : ℝ) : ℝ :=
  kcTh Vr Wv + Kr * ((Vr + 1) * (|kcL Vr Wv| + |Wv| + |Vr * Wv| + |Vr * Wv|))

theorem kcC_exec (hL : KCLay nD Lb Sb Rb Ob nV k W) (c : Config) (hc : WordsBounded W c)
    (hC : KCCtx nD Lb Sb Rb Ob nV k fl rb Lv c) {Wv Vr Kr : ℝ} (h50 : c.rreg 1350 = Wv)
    (h54 : c.rreg 1354 = Vr) (h55 : c.rreg 1355 = Kr) :
    ∃ c' t, Exec P W kcC c c' t ∧ t ≤ 37 ∧
      (c'.rmem (Ob + 3 * nD) = kcL Vr Wv ∧ c'.rmem (Ob + 3 * nD + 1) = kcTh Vr Wv ∧
        c'.rmem (Ob + 3 * nD + 2) = kcH0 Vr Wv Kr ∧
        (∀ a, a < Ob + 3 * nD ∨ Ob + 3 * nD + 3 ≤ a → c'.rmem a = c.rmem a) ∧
        c'.rreg 1356 = kcL Vr Wv ∧
        (∀ r, r < 1352 ∨ r = 1354 ∨ r = 1355 ∨ r = 1359 ∨ r = 1360 ∨ 1364 < r →
          c'.rreg r = c.rreg r) ∧
        (∀ r, r ≠ 1312 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
        c'.output = c.output) := by
  have := hL.wO; have := hL.w3
  have z51 := hC.z
  unfold kcC
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (absAdd_exec (P := P) (acc := 1362) (x := 1356) (t := 1353) (z := 1351)
    (by decide) (by decide) (by decide) (by decide) (by decide) _ ‹_›
    (by config_simp; exact z51)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨a62, ar, an, anm, arm, ao⟩
  refine spec_seq ?_
  refine spec_use (absAdd_exec (P := P) (acc := 1362) (x := 1350) (t := 1353) (z := 1351)
    (by decide) (by decide) (by decide) (by decide) (by decide) _ hw₂
    (by rw [ar 1351 (by decide) (by decide)]; config_simp; exact z51)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨b62, br, bn, bnm, brm, bo⟩
  refine spec_seq ?_
  refine spec_use (absAdd_exec (P := P) (acc := 1362) (x := 1361) (t := 1353) (z := 1351)
    (by decide) (by decide) (by decide) (by decide) (by decide) _ hw₃
    (by rw [br 1351 (by decide) (by decide), ar 1351 (by decide) (by decide)]; config_simp;
        exact z51)) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨d62, dr, dn, dnm, drm, d_o⟩
  refine spec_seq ?_
  refine spec_use (absAdd_exec (P := P) (acc := 1362) (x := 1361) (t := 1353) (z := 1351)
    (by decide) (by decide) (by decide) (by decide) (by decide) _ hw₄
    (by rw [dr 1351 (by decide) (by decide), br 1351 (by decide) (by decide),
          ar 1351 (by decide) (by decide)]; config_simp; exact z51)) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨e62, er, en, enm, erm, eo⟩
  -- the registers after the four sums
  have v61 : c₅.rreg 1361 = Vr * Wv := by
    rw [er 1361 (by decide) (by decide), dr 1361 (by decide) (by decide),
      br 1361 (by decide) (by decide), ar 1361 (by decide) (by decide)]; config_simp; rw [h54, h50]
  have v56 : c₅.rreg 1356 = kcL Vr Wv := by
    rw [er 1356 (by decide) (by decide), dr 1356 (by decide) (by decide),
      br 1356 (by decide) (by decide), ar 1356 (by decide) (by decide)]; config_simp
    rw [h54, h50, hC.one, kcL]; push_cast; ring
  have v57 : c₅.rreg 1357 = kcTh Vr Wv := by
    rw [er 1357 (by decide) (by decide), dr 1357 (by decide) (by decide),
      br 1357 (by decide) (by decide), ar 1357 (by decide) (by decide)]; config_simp
    rw [h54, h50, hC.one, kcTh, kcL]; push_cast; ring
  have v62 : c₅.rreg 1362 = |kcL Vr Wv| + |Wv| + |Vr * Wv| + |Vr * Wv| := by
    rw [e62, d62, b62, a62, dr 1361 (by decide) (by decide), br 1361 (by decide) (by decide),
      ar 1361 (by decide) (by decide), ar 1350 (by decide) (by decide)]
    config_simp
    rw [h54, h50, hC.one, kcL]; push_cast; ring
  have v54 : c₅.rreg 1354 = Vr := by
    rw [er 1354 (by decide) (by decide), dr 1354 (by decide) (by decide),
      br 1354 (by decide) (by decide), ar 1354 (by decide) (by decide)]; config_simp; exact h54
  have v55 : c₅.rreg 1355 = Kr := by
    rw [er 1355 (by decide) (by decide), dr 1355 (by decide) (by decide),
      br 1355 (by decide) (by decide), ar 1355 (by decide) (by decide)]; config_simp; exact h55
  have v59 : c₅.rreg 1359 = 1 := by
    rw [er 1359 (by decide) (by decide), dr 1359 (by decide) (by decide),
      br 1359 (by decide) (by decide), ar 1359 (by decide) (by decide)]; config_simp; exact hC.one
  have N : ∀ r, c₅.nreg r = c.nreg r := fun r => by rw [en, dn, bn, an]
  have n00 : c₅.nreg 1300 = nD := (N _).trans hC.r1300
  have n04 : c₅.nreg 1304 = Ob := (N _).trans hC.r1304
  have n10 : c₅.nreg 1310 = 1 := (N _).trans hC.r1310
  exec_block
  all_goals try ((try config_simp); (try simp only [n00, n04, n10]); omega)
  config_simp
  simp only [n00, n04, n10, v56, v57, v62, v54, v55, v59]
  refine ⟨by omega, ?_, ?_, ?_, fun a ha => ?_, ?_, fun r hr => ?_, fun r hr => ?_, ?_, ?_⟩
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  · simp only [upd_apply, kcH0]; split_ifs <;> first | omega | ring
  · simp only [upd_apply, show a ≠ 3 * nD + Ob + 1 + 1 by omega, show a ≠ 3 * nD + Ob + 1 by omega,
      show a ≠ 3 * nD + Ob by omega, ↓reduceIte]
    rw [erm, drm, brm, arm]
  · trivial
  · simp only [upd_apply, show r ≠ 1358 by omega, show r ≠ 1363 by omega, ↓reduceIte]
    rw [er r (by omega) (by omega), dr r (by omega) (by omega), br r (by omega) (by omega),
      ar r (by omega) (by omega)]
    config_simp
    simp only [upd_apply, show r ≠ 1361 by omega, show r ≠ 1364 by omega,
      show r ≠ 1356 by omega, show r ≠ 1363 by omega, show r ≠ 1357 by omega,
      show r ≠ 1362 by omega, ↓reduceIte]
  · simp only [upd_apply, hr, ↓reduceIte]; exact N r
  · rw [enm, dnm, bnm, anm]
  · rw [eo, d_o, bo, ao]

/-! ### The weights and the labels -/

/-- The weight written for the dart `j`. -/
def kcWt (fl rb : ℕ → ℕ) (Lv : ℕ → ℝ) (Lc : ℝ) (j : ℕ) : ℝ :=
  if 0 < fl j then (if 0 < rb j then Lv j else Lc) else Lc

/-- The label written for the dart `j`. -/
def kcPh (fl : ℕ → ℕ) (Lv : ℕ → ℝ) (j : ℕ) : ℝ := if 0 < fl j then Lv j else 0

set_option maxHeartbeats 1000000 in
theorem kcD_exec (hL : KCLay nD Lb Sb Rb Ob nV k W) (c : Config) (hc : WordsBounded W c)
    (hC : KCCtx nD Lb Sb Rb Ob nV k fl rb Lv c) {Lc : ℝ} (h56 : c.rreg 1356 = Lc) :
    ∃ c' t, Exec P W kcD c c' t ∧ t ≤ 22 * nD + 3 ∧
      ((∀ j < nD, c'.rmem (Ob + j) = kcWt fl rb Lv Lc j ∧
          c'.rmem (Ob + nD + j) = kcPh fl Lv j) ∧
        (∀ a, a < Ob ∨ Ob + 2 * nD ≤ a → c'.rmem a = c.rmem a) ∧
        c'.nmem = c.nmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wR; have := hL.wL; have := hL.wO; have := hL.dj; have := hL.w3
  unfold kcD
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ j < i, c'.rmem (Ob + j) = kcWt fl rb Lv Lc j ∧ c'.rmem (Ob + nD + j) = kcPh fl Lv j) ∧
      (∀ a, a < Ob ∨ Ob + 2 * nD ≤ a → c'.rmem a = c.rmem a) ∧
      (∀ r, r ≠ 1352 → r ≠ 1360 → r ≠ 1363 → c'.rreg r = c.rreg r) ∧
      (∀ r, r < 1311 ∨ 1315 < r → c'.nreg r = c.nreg r) ∧ c'.nreg 1314 = c.nreg 1314 ∧
      c'.nmem = c.nmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 1311) (bR := 1300) (body := kcDBody) J (K := 20)
    (n := nD) _ ‹_› (by config_simp) (by config_simp; exact hC.r1300) ?_
    (fun i c₁ hi hw ha hb ⟨g, grm, gr, gn, g14, gnm, go⟩ => by
      have e00 : c₁.nreg 1300 = nD := (gn 1300 (by omega)).trans hC.r1300
      have e01 : c₁.nreg 1301 = Lb := (gn 1301 (by omega)).trans hC.r1301
      have e02 : c₁.nreg 1302 = Sb := (gn 1302 (by omega)).trans hC.r1302
      have e03 : c₁.nreg 1303 = Rb := (gn 1303 (by omega)).trans hC.r1303
      have e04 : c₁.nreg 1304 = Ob := (gn 1304 (by omega)).trans hC.r1304
      have e10 : c₁.nreg 1310 = 1 := (gn 1310 (by omega)).trans hC.r1310
      have e14 : c₁.nreg 1314 = 0 := g14.trans hC.r1314
      have z51 : c₁.rreg 1351 = 0 := (gr 1351 (by decide) (by decide) (by decide)).trans hC.z
      have l56 : c₁.rreg 1356 = Lc := (gr 1356 (by decide) (by decide) (by decide)).trans h56
      have xf : c₁.nmem (Sb + i) = fl i := by rw [gnm]; exact hC.fl i hi
      have xr : c₁.nmem (Rb + i) = rb i := by rw [gnm]; exact hC.rb i hi
      have xl : c₁.rmem (Lb + i) = Lv i := by rw [grm _ (by omega)]; exact hC.lv i hi
      unfold kcDBody
      refine spec_seq ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e01, e02, e03, ha]); omega)
      refine spec_seq ?_
      refine spec_use (sel_exec (P := P) 1314 1313 1360 1352 1351 _ ‹_›) ?_
      intro c₂ k₂ hk₂ hw₂ hc₂
      subst hc₂
      refine spec_seq ?_
      refine spec_use (sel_exec (P := P) 1314 1315 1363 1352 1356 _ hw₂) ?_
      intro c₃ k₃ hk₃ hw₃ hc₃
      subst hc₃
      refine spec_seq ?_
      refine spec_use (sel_exec (P := P) 1314 1313 1363 1363 1356 _ hw₃) ?_
      intro c₄ k₄ hk₄ hw₄ hc₄
      subst hc₄
      exec_block
      all_goals try ((try config_simp); (try simp only [e00, e04, e10, ha]); omega)
      dsimp only [J]
      config_simp
      simp only [e00, e01, e02, e03, e04, e10, e14, ha, xf, xr, xl, z51, l56]
      refine ⟨by omega, trivial, trivial, fun j hj => ?_,
        fun a ha' => ?_, fun r h1 h2 h3 => ?_, fun r hr => ?_, ?_, gnm, go⟩
      · simp only [upd_apply]
        by_cases hji : j = i
        · subst hji
          simp only [show Ob + j ≠ Ob + j + nD by omega, show Ob + nD + j = Ob + j + nD by omega,
            ↓reduceIte, kcWt, kcPh, and_self]
        · simp only [show Ob + j ≠ Ob + i + nD by omega, show Ob + j ≠ Ob + i by omega,
            show Ob + nD + j ≠ Ob + i + nD by omega, show Ob + nD + j ≠ Ob + i by omega,
            ↓reduceIte]
          exact g j (by omega)
      · simp only [upd_apply, show a ≠ Ob + i + nD by omega, show a ≠ Ob + i by omega,
          ↓reduceIte]
        exact grm a ha'
      · simp only [upd_apply, h1, h2, h3, ↓reduceIte]; exact gr r h1 h2 h3
      · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r hr
      · exact hC.r1314.symm)) ?_
  · refine ⟨fun j hj => absurd hj (by omega), fun _ _ => rfl, fun _ _ _ _ => rfl, fun r hr => ?_,
      ?_, rfl, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> omega
  intro c₂ k₂ hk₂ _ hJ₂
  obtain ⟨_, g, grm, -, -, -, gnm, go⟩ := hJ₂
  exact ⟨by omega, g, grm, gnm, go⟩

/-! ### The whole program -/

theorem kcInit_exec (hL : KCLay nD Lb Sb Rb Ob nV k W) (c : Config) (hc : WordsBounded W c)
    (h00 : c.nreg 1300 = nD) (h01 : c.nreg 1301 = Lb) (h02 : c.nreg 1302 = Sb)
    (h03 : c.nreg 1303 = Rb) (h04 : c.nreg 1304 = Ob) (h05 : c.nreg 1305 = nV)
    (h06 : c.nreg 1306 = k) (hfl : ∀ j < nD, c.nmem (Sb + j) = fl j)
    (hrb : ∀ j < nD, c.nmem (Rb + j) = rb j) (hlv : ∀ j < nD, c.rmem (Lb + j) = Lv j) :
    ∃ c' t, Exec P W kcInit c c' t ∧ t ≤ 5 ∧
      (KCCtx nD Lb Sb Rb Ob nV k fl rb Lv c' ∧ c'.rreg 1350 = 0 ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.w3
  unfold kcInit
  exec_block
  all_goals try omega
  config_simp
  refine ⟨by omega, ⟨h00, h01, h02, h03, h04, h05, h06, rfl, rfl, by simp, by simp, hfl, hrb, hlv⟩,
    ?_⟩
  simp

set_option maxHeartbeats 1000000 in
/-- **The real constants, on index functions.** From the flags `fl` (at `Sb`), the reach bits
`rb` (at `Rb`), the lengths `Lv` (real, at `Lb`) of the `nD` darts, with `r1300 … r1306` =
`nD, Lb, Sb, Rb, Ob, nV, k`, `kcProg` ends within `36 nD + 4 nV + 4 k + 56` steps with the
weight `kcWt` of the dart `j` at `Ob + j`, its label `kcPh` at `Ob + nD + j`, and `kcL`,
`kcTh`, `kcH0` at `Ob + 3 nD`, `+ 1`, `+ 2`, for `Wv = Σ_j kcTerm fl Lv j`, `Vr = nV`,
`Kr = k + 1`; the rest of the real memory, the natural memory and the output are kept. -/
theorem kcProg_exec (hL : KCLay nD Lb Sb Rb Ob nV k W) (c : Config) (hc : WordsBounded W c)
    (h00 : c.nreg 1300 = nD) (h01 : c.nreg 1301 = Lb) (h02 : c.nreg 1302 = Sb)
    (h03 : c.nreg 1303 = Rb) (h04 : c.nreg 1304 = Ob) (h05 : c.nreg 1305 = nV)
    (h06 : c.nreg 1306 = k) (hfl : ∀ j < nD, c.nmem (Sb + j) = fl j)
    (hrb : ∀ j < nD, c.nmem (Rb + j) = rb j) (hlv : ∀ j < nD, c.rmem (Lb + j) = Lv j) :
    ∃ c' t, Exec P W kcProg c c' t ∧ t ≤ 36 * nD + 4 * nV + 4 * k + 56 ∧
      ((∀ j < nD, c'.rmem (Ob + j) =
          kcWt fl rb Lv (kcL nV (∑ i ∈ range nD, kcTerm fl Lv i)) j ∧
          c'.rmem (Ob + nD + j) = kcPh fl Lv j) ∧
        c'.rmem (Ob + 3 * nD) = kcL nV (∑ i ∈ range nD, kcTerm fl Lv i) ∧
        c'.rmem (Ob + 3 * nD + 1) = kcTh nV (∑ i ∈ range nD, kcTerm fl Lv i) ∧
        c'.rmem (Ob + 3 * nD + 2) = kcH0 nV (∑ i ∈ range nD, kcTerm fl Lv i) (k + 1) ∧
        (∀ a, a < Ob ∨ Ob + 3 * nD + 3 ≤ a → c'.rmem a = c.rmem a) ∧
        c'.nmem = c.nmem ∧ c'.output = c.output) := by
  have := hL.wO; have := hL.w3; have hdj := hL.dj
  unfold kcProg
  refine spec_seq ?_
  refine spec_use (kcInit_exec (P := P) hL c hc h00 h01 h02 h03 h04 h05 h06 hfl hrb hlv) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hC₁, z50, znm, zrm, zo⟩
  refine spec_seq ?_
  refine spec_use (kcA_exec (P := P) hL c₁ hw₁ hC₁) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨a50, ar, an, a14, anm, arm, ao⟩
  rw [z50, zero_add] at a50
  have hC₂ := hC₁.frame (c' := c₂) (fun r hr => an r (by omega)) a14
    (ar _ (by decide) (by decide) (by decide) (by decide))
    (ar _ (by decide) (by decide) (by decide) (by decide)) anm (fun j _ => by rw [arm])
  refine spec_seq ?_
  refine spec_use (kcB_exec (P := P) hL c₂ hw₂ hC₂.r1305 hC₂.r1306 hC₂.r1310 hC₂.one) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨b54, b55, br, bn, bnm, brm, bo⟩
  have hC₃ := hC₂.frame (c' := c₃) (fun r hr => bn r (by omega)) (bn _ (by omega))
    (br _ (by decide) (by decide)) (br _ (by decide) (by decide)) bnm (fun j _ => by rw [brm])
  have w50 : c₃.rreg 1350 = ∑ i ∈ range nD, kcTerm fl Lv i := by
    rw [br _ (by decide) (by decide), a50]
  refine spec_seq ?_
  refine spec_use (kcC_exec (P := P) hL c₃ hw₃ hC₃ w50 b54 b55) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨d1, d2, d3, drm, d56, dr, dn, dnm, d_o⟩
  have hC₄ := hC₃.frame (c' := c₄) (fun r hr => dn r (by omega)) (dn _ (by omega))
    (dr _ (by omega)) (dr _ (by omega)) dnm (fun j hj => drm _ (by omega))
  refine spec_use (kcD_exec (P := P) hL c₄ hw₄ hC₄ d56) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨eo1, erm, enm, eo⟩
  refine ⟨by omega, eo1, ?_, ?_, ?_, fun a ha => ?_, ?_, ?_⟩
  · rw [erm _ (Or.inr (by omega)), d1]
  · rw [erm _ (Or.inr (by omega)), d2]
  · rw [erm _ (Or.inr (by omega)), d3]
  · rw [erm _ (by omega), drm _ (by omega), brm, arm, zrm]
  · rw [enm, dnm, bnm, anm, znm]
  · rw [eo, d_o, bo, ao, zo]

/-! ### The real part of the slot -/

section Slot

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- `tripW`, by dart number. -/
theorem sum_kcTerm (S : Finset D) (ℓ : D → ℤ) (σ : D ≃ Fin (Fintype.card D)) {fl : ℕ → ℕ}
    {Lv : ℕ → ℝ} (hfl : ∀ d, 0 < fl (σ d) ↔ d ∈ S) (hlv : ∀ d ∈ S, Lv (σ d) = ℓ d) :
    ∑ i ∈ range (Fintype.card D), kcTerm fl Lv i = (Klein.tripW S ℓ : ℝ) := by
  classical
  rw [← Fin.sum_univ_eq_sum_range, ← Equiv.sum_comp σ (fun i => kcTerm fl Lv i)]
  have e : ∀ d, kcTerm fl Lv (σ d) = if d ∈ S then |(ℓ d : ℝ)| else 0 := fun d => by
    unfold kcTerm
    by_cases hd : d ∈ S
    · have h := (hfl d).2 hd
      simp only [h, hd, hlv d hd, ↓reduceIte]
    · have h : ¬ 0 < fl (σ d) := fun h => hd ((hfl d).1 h)
      simp only [h, hd, ↓reduceIte]
  simp only [e, sum_ite_mem, univ_inter, Klein.tripW]
  push_cast
  rfl

/-- **The output of `kcProg` is the real part of `KSlot`**: for a map `M`, `k`, `g`, a piece `S`,
lengths `ℓ` and a numbering `σ` of the darts, with the flags of `S` at `Sb + σ d` (positive
exactly on `S`), the reach bits at `Rb + σ d` (positive, on `S`, exactly when `M.tail d` is
reached from the target of the first move) and the lengths at `Lb + σ d` (on `S`), `kcProg`
writes at `Ob` the weights `tripWt M k g S ℓ 0`, the labels `tripφ S ℓ` and the constants
`tripL`, `tripTh`, `tripH0` (the fields `wt`, `ph`, `tl`, `th`, `h0` of `KSlot` at
`Rk = Ob`), within `36 |D| + 4 |V| + 4 k + 56` steps. -/
theorem kcProg_kslot {M : CombMap D V F} {kk : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
    (σ : D ≃ Fin (Fintype.card D)) {Lb Sb Rb Ob : ℕ}
    (hL : KCLay (Fintype.card D) Lb Sb Rb Ob (Fintype.card V) kk W) (c : Config)
    (hc : WordsBounded W c) (h00 : c.nreg 1300 = Fintype.card D) (h01 : c.nreg 1301 = Lb)
    (h02 : c.nreg 1302 = Sb) (h03 : c.nreg 1303 = Rb) (h04 : c.nreg 1304 = Ob)
    (h05 : c.nreg 1305 = Fintype.card V) (h06 : c.nreg 1306 = kk)
    (hfl : ∀ d, 0 < c.nmem (Sb + σ d) ↔ d ∈ S)
    (hrb : ∀ d ∈ S, 0 < c.nmem (Rb + σ d) ↔
      MSSP.Reach (MSSP.pieceGraph M S ℓ) (Klein.tripDst M kk g 0) (M.tail d))
    (hlv : ∀ d ∈ S, c.rmem (Lb + σ d) = ℓ d) :
    ∃ c' t, Exec P W kcProg c c' t ∧
      t ≤ 36 * Fintype.card D + 4 * Fintype.card V + 4 * kk + 56 ∧
      (∀ x, c'.rmem (Ob + (Klein.aWT + σ x)) = Klein.tripWt M kk g S ℓ 0 x) ∧
      (∀ x, c'.rmem (Ob + (Klein.aPH (Fintype.card D) + σ x)) = Klein.tripφ S ℓ x) ∧
      c'.rmem (Ob + Klein.aTL (Fintype.card D)) = Klein.tripL V S ℓ ∧
      c'.rmem (Ob + Klein.aTH (Fintype.card D)) = Klein.tripTh V S ℓ ∧
      c'.rmem (Ob + Klein.aH0 (Fintype.card D)) = Klein.tripH0 V S ℓ kk ∧
      (∀ a, a < Ob ∨ Ob + 3 * Fintype.card D + 3 ≤ a → c'.rmem a = c.rmem a) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  classical
  obtain ⟨c', t, ex, ht, hw, h1, h2, h3, hfr, hnm, ho⟩ :=
    kcProg_exec (P := P) (fl := fun j => c.nmem (Sb + j)) (rb := fun j => c.nmem (Rb + j))
      (Lv := fun j => c.rmem (Lb + j)) hL c hc h00 h01 h02 h03 h04 h05 h06 (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl)
  have hW := sum_kcTerm S ℓ σ (fl := fun j => c.nmem (Sb + j)) (Lv := fun j => c.rmem (Lb + j))
    hfl hlv
  rw [hW] at hw h1 h2 h3
  have eL : kcL (Fintype.card V) (Klein.tripW S ℓ : ℝ) = (Klein.tripL V S ℓ : ℝ) := by
    simp only [kcL, Klein.tripL, Klein.tripB]; push_cast; ring
  have eT : kcTh (Fintype.card V) (Klein.tripW S ℓ : ℝ) = (Klein.tripTh V S ℓ : ℝ) := by
    simp only [kcTh, kcL, Klein.tripTh, Klein.tripL, Klein.tripB]; push_cast; ring
  refine ⟨c', t, ex, ht, fun x => ?_, fun x => ?_, ?_, ?_, ?_, hfr, hnm, ho⟩
  · have hx := (hw (σ x) (σ x).2).1
    simp only [Klein.aWT, zero_add]
    rw [hx, eL]
    unfold kcWt Klein.tripWt
    by_cases hS : x ∈ S
    · have h := (hfl x).2 hS
      by_cases hR : MSSP.Reach (MSSP.pieceGraph M S ℓ) (Klein.tripDst M kk g 0) (M.tail x)
      · have h' := (hrb x hS).2 hR
        simp only [h, h', hS, hR, and_self, ↓reduceIte, hlv x hS]
      · have h' : ¬ 0 < c.nmem (Rb + σ x) := fun h' => hR ((hrb x hS).1 h')
        simp only [h, h', hS, hR, and_false, ↓reduceIte]
    · have h : ¬ 0 < c.nmem (Sb + σ x) := fun h => hS ((hfl x).1 h)
      simp only [h, hS, false_and, ↓reduceIte]
  · have hx := (hw (σ x) (σ x).2).2
    simp only [Klein.aPH, ← Nat.add_assoc]
    rw [hx]
    unfold kcPh Klein.tripφ
    by_cases hS : x ∈ S
    · have h := (hfl x).2 hS
      simp only [h, hS, ↓reduceIte, hlv x hS]
    · have h : ¬ 0 < c.nmem (Sb + σ x) := fun h => hS ((hfl x).1 h)
      simp only [h, hS, ↓reduceIte, Int.cast_zero]
  · simp only [Klein.aTL]; rw [h1, eL]
  · simp only [Klein.aTH, ← Nat.add_assoc]; rw [h2, eT]
  · simp only [Klein.aH0, ← Nat.add_assoc]
    rw [h3]
    simp only [kcH0, kcTh, kcL, Klein.tripH0, Klein.tripTh, Klein.tripL, Klein.tripB, Klein.tripK,
      Klein.driftK]
    push_cast
    ring

end Slot

end NegSSSP

end PlanarFlow
