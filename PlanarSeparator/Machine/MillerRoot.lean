module

public import PlanarSeparator.Machine.Front
public import PlanarSeparator.CycleWeight

/-!
# Miller's separator on the machine: root sums and depths

Part of step 8 of the plan in `PlanarSeparator/Machine/Miller.lean`. The tree `T₁` is held by
the parent darts at `bPr` (the dart from every vertex `v ≠ r₀` to its parent; see
`PlanarSeparator/Machine/MillerBFS.lean`, `PlanarSeparator/Machine/MillerInner.lean`), read in
the coded format (`A x` at `bR + x`, `V x` at `bV + x`): the parent of `v` is
`paN A V Pr v = V (A (Pr v))`. Given an order `ord` of the vertices in which every parent comes
before its children (`IsOrd`; a breadth-first order is one), one pass `rspass` over the order stores
for every vertex `v`

* its parent, the root being its own parent (`upN`, at `bU + v`; level `0` of the table of
  `PlanarSeparator/Machine/MillerLCA.lean`),
* its depth (at `bD + v`) and
* its root sum `rs v = ∑ u ∈ anc v, w u` (at `bS + v`),

within `28 n + 3` steps (`rspass_exec`, numeric: for any functions satisfying the recurrences
`RsRec`, `DpRec`). The bridge (`rspass_tree`): for a spanning tree `T` of a map coded by `cd`, with
its vertices numbered by `vi`, the numbers stored are `vi (T.parent v)`, `#(T.anc v) - 1` and
`∑ u ∈ T.anc v, w u` (`rsRec_anc`, `dpRec_anc`, `paN_tree`).

Registers: `r140 = 0`, `r141 = 1`, `r147 = bR`, `r161 = n`, `r162 = bV`, `r215 = bPr`, and
`r250 = bW` (weights), `r251 = bO` (order), `r252 = bS`, `r253 = bD`, `r254 = bU`, `r255 = r₀`;
the program writes `r256 … r265`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The numeric data -/

/-- The parent of a vertex: the vertex at the head of its parent dart. -/
def paN (A V Pr : ℕ → ℕ) (v : ℕ) : ℕ := V (A (Pr v))

/-- The parent, the root `r₀` being its own parent. -/
def upN (A V Pr : ℕ → ℕ) (r₀ v : ℕ) : ℕ := if v = r₀ then r₀ else paN A V Pr v

/-- An order of the vertices `< n` in which the parent of every vertex other than the root comes
first. -/
structure IsOrd (n r₀ : ℕ) (pa ord : ℕ → ℕ) : Prop where
  lt : ∀ i < n, ord i < n
  surj : ∀ v < n, ∃ i < n, ord i = v
  par_first : ∀ i < n, ord i ≠ r₀ → ∃ j < i, ord j = pa (ord i)

/-- The recurrence of the root sums. -/
def RsRec (n r₀ : ℕ) (pa w R : ℕ → ℕ) : Prop :=
  R r₀ = w r₀ ∧ ∀ v < n, v ≠ r₀ → R v = R (pa v) + w v

/-- The recurrence of the depths. -/
def DpRec (n r₀ : ℕ) (pa Dp : ℕ → ℕ) : Prop :=
  Dp r₀ = 0 ∧ ∀ v < n, v ≠ r₀ → Dp v = Dp (pa v) + 1

/-- The coded tree: the reversals and vertices of the darts, the parent darts. -/
structure RootIn (k n r₀ : ℕ) (A V Pr : ℕ → ℕ) : Prop where
  r₀_lt : r₀ < n
  A_lt : ∀ x < 3 * k, A x < 3 * k
  V_lt : ∀ x < 3 * k, V x < n
  Pr_lt : ∀ v < n, v ≠ r₀ → Pr v < 3 * k

theorem RootIn.pa_lt {k n r₀ : ℕ} {A V Pr : ℕ → ℕ} (h : RootIn k n r₀ A V Pr) {v : ℕ}
    (hv : v < n) (hr : v ≠ r₀) : paN A V Pr v < n :=
  h.V_lt _ (h.A_lt _ (h.Pr_lt v hv hr))

theorem RootIn.up_lt {k n r₀ : ℕ} {A V Pr : ℕ → ℕ} (h : RootIn k n r₀ A V Pr) {v : ℕ}
    (hv : v < n) : upN A V Pr r₀ v < n := by
  unfold upN
  split_ifs with e
  · exact h.r₀_lt
  · exact h.pa_lt hv e

/-! ### The program -/

/-- **A vertex `r258 = v` other than the root**: its parent `p`, then `U v := p`,
`D v := D p + 1`, `S v := S p + w v`. -/
def rsgen : Stmt :=
  block [.addN 259 215 258, .loadN 260 259, .addN 259 147 260, .loadN 261 259,
    .addN 259 162 261, .loadN 262 259, .addN 259 253 262, .loadN 263 259, .addN 263 263 141,
    .addN 259 252 262, .loadN 264 259, .addN 259 250 258, .loadN 265 259, .addN 264 264 265,
    .addN 259 254 258, .storeN 259 262, .addN 259 253 258, .storeN 259 263,
    .addN 259 252 258, .storeN 259 264]

/-- **The root `r258 = r₀`**: `U r₀ := r₀`, `D r₀ := 0`, `S r₀ := w r₀`. -/
def rsroot : Stmt :=
  block [.addN 259 250 258, .loadN 265 259, .addN 259 254 258, .storeN 259 258,
    .addN 259 253 258, .storeN 259 140, .addN 259 252 258, .storeN 259 265]

/-- **One position** `r256 = i` of the order. -/
def rsbody : Stmt :=
  .seq (block [.addN 257 251 256, .loadN 258 257])
    (.seq (.ifLtN 258 255 rsgen (.ifLtN 255 258 rsgen rsroot)) (.instr (.addN 256 256 141)))

/-- **The pass of the root sums.** -/
def rspass : Stmt := .seq (.instr (.copyN 256 140)) (.whileLtN 256 161 rsbody)

/-! ### Correctness -/

section proofs

variable {W : ℕ} {P : Input} {k n r₀ bR bV bPr bW bO bS bD bU : ℕ} {A V Pr w ord R Dp : ℕ → ℕ}

/-- The layout: the arrays read lie below `bS`; then `S`, `D`, `U`. -/
structure RLay (k n bR bV bPr bW bO bS bD bU W : ℕ) : Prop where
  hR : bR + 3 * k ≤ bS
  hV : bV + 3 * k ≤ bS
  hPr : bPr + n ≤ bS
  hW : bW + n ≤ bS
  hO : bO + n ≤ bS
  hS : bS + n ≤ bD
  hD : bD + n ≤ bU
  hU : bU + n ≤ W

/-- The written cells. -/
def ROut (n bS bD bU a : ℕ) : Prop :=
  (bS ≤ a ∧ a < bS + n) ∨ (bD ≤ a ∧ a < bD + n) ∨ (bU ≤ a ∧ a < bU + n)

/-- The registers and the memory read by the pass, in the starting configuration `c₀`. -/
structure RFix (k n r₀ bR bV bPr bW bO bS bD bU : ℕ) (A V Pr w ord : ℕ → ℕ) (c : Config) :
    Prop where
  r140 : c.nreg 140 = 0
  r141 : c.nreg 141 = 1
  r147 : c.nreg 147 = bR
  r161 : c.nreg 161 = n
  r162 : c.nreg 162 = bV
  r215 : c.nreg 215 = bPr
  r250 : c.nreg 250 = bW
  r251 : c.nreg 251 = bO
  r252 : c.nreg 252 = bS
  r253 : c.nreg 253 = bD
  r254 : c.nreg 254 = bU
  r255 : c.nreg 255 = r₀
  mA : ∀ x < 3 * k, c.nmem (bR + x) = A x
  mV : ∀ x < 3 * k, c.nmem (bV + x) = V x
  mP : ∀ v < n, v ≠ r₀ → c.nmem (bPr + v) = Pr v
  mW : ∀ v < n, c.nmem (bW + v) = w v
  mO : ∀ i < n, c.nmem (bO + i) = ord i

/-- The state of the pass after the positions `< i`. -/
structure RI (c₀ : Config) (i : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  r256 : c.nreg 256 = i
  le : i ≤ n
  regs : ∀ r, r < 256 ∨ 266 ≤ r → c.nreg r = c₀.nreg r
  mem : ∀ a, ¬ ROut n bS bD bU a → c.nmem a = c₀.nmem a
  out : c.output = c₀.output
  done : ∀ j < i, c.nmem (bU + ord j) = upN A V Pr r₀ (ord j) ∧ c.nmem (bD + ord j) = Dp (ord j) ∧
    c.nmem (bS + ord j) = R (ord j)

theorem RFix.of {c c' : Config} (h : RFix k n r₀ bR bV bPr bW bO bS bD bU A V Pr w ord c)
    (hl : RLay k n bR bV bPr bW bO bS bD bU W)
    (hr : ∀ r, r < 256 → c'.nreg r = c.nreg r) (hm : ∀ a, ¬ ROut n bS bD bU a → c'.nmem a = c.nmem a) :
    RFix k n r₀ bR bV bPr bW bO bS bD bU A V Pr w ord c' := by
  have hl' := hl
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := hl'
  refine ⟨(hr _ (by omega)).trans h.r140, (hr _ (by omega)).trans h.r141,
    (hr _ (by omega)).trans h.r147, (hr _ (by omega)).trans h.r161, (hr _ (by omega)).trans h.r162,
    (hr _ (by omega)).trans h.r215, (hr _ (by omega)).trans h.r250, (hr _ (by omega)).trans h.r251,
    (hr _ (by omega)).trans h.r252, (hr _ (by omega)).trans h.r253, (hr _ (by omega)).trans h.r254,
    (hr _ (by omega)).trans h.r255, fun x hx => ?_, fun x hx => ?_,
    fun v hv hr0 => ?_, fun v hv => ?_, fun i hi => ?_⟩
  · rw [hm _ (by unfold ROut; omega)]; exact h.mA x hx
  · rw [hm _ (by unfold ROut; omega)]; exact h.mV x hx
  · rw [hm _ (by unfold ROut; omega)]; exact h.mP v hv hr0
  · rw [hm _ (by unfold ROut; omega)]; exact h.mW v hv
  · rw [hm _ (by unfold ROut; omega)]; exact h.mO i hi

variable (hin : RootIn k n r₀ A V Pr) (hord : IsOrd n r₀ (paN A V Pr) ord)
  (hR : RsRec n r₀ (paN A V Pr) w R) (hDp : DpRec n r₀ (paN A V Pr) Dp)
  (hRW : ∀ v < n, R v ≤ W) (hDW : ∀ v < n, Dp v ≤ W)
  (hl : RLay k n bR bV bPr bW bO bS bD bU W)
include hin hord hR hDp hRW hDW hl

set_option maxHeartbeats 1000000 in
theorem rsbody_exec {c₀ : Config} (hF : RFix k n r₀ bR bV bPr bW bO bS bD bU A V Pr w ord c₀) (i : ℕ)
    (c : Config) (hI : RI (W := W) (n := n) (bS := bS) (bD := bD) (bU := bU) (r₀ := r₀) (A := A)
      (V := V) (Pr := Pr) (ord := ord) (R := R) (Dp := Dp) c₀ i c) (hi : i < n) :
    ∃ c' t, Exec P W rsbody c c' t ∧ RI (W := W) (n := n) (bS := bS) (bD := bD) (bU := bU)
      (r₀ := r₀) (A := A) (V := V) (Pr := Pr) (ord := ord) (R := R) (Dp := Dp) c₀ (i + 1) c' ∧
      t ≤ 26 := by
  have hc := hI.wb
  have hF' : RFix k n r₀ bR bV bPr bW bO bS bD bU A V Pr w ord c :=
    hF.of hl (fun r hr => hI.regs r (Or.inl hr)) hI.mem
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := hl
  have hv := hord.lt i hi
  generalize hvv : ord i = v at hv
  have mO : c.nmem (bO + i) = v := by rw [hF'.mO i hi, hvv]
  -- the stores of a vertex: the cells of `v` get the new values
  have hstore : ∀ (u d s : ℕ), u = upN A V Pr r₀ v → d = Dp v → s = R v →
      ∀ c' : Config, WordsBounded W c' → c'.nreg 256 = i + 1 →
      (∀ r, r < 256 ∨ 266 ≤ r → c'.nreg r = c₀.nreg r) → c'.output = c₀.output →
      c'.nmem = upd (upd (upd c.nmem (bU + v) u) (bD + v) d) (bS + v) s →
      RI (W := W) (n := n) (bS := bS) (bD := bD) (bU := bU) (r₀ := r₀) (A := A) (V := V)
        (Pr := Pr) (ord := ord) (R := R) (Dp := Dp) c₀ (i + 1) c' := by
    intro u d s hu hd hs c' hw' h256 hr' ho' hm'
    refine ⟨hw', h256, by omega, hr', fun a ha => ?_, ho', fun j hj => ?_⟩
    · rw [hm']
      unfold ROut at ha
      rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
      exact hI.mem a (by unfold ROut; omega)
    · have hjn := hord.lt j (by omega)
      rw [hm']
      by_cases e : ord j = v
      · rw [e]
        refine ⟨?_, ?_, ?_⟩
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_same, hu]
        · rw [upd_other _ _ _ (by omega), upd_same, hd]
        · rw [upd_same, hs]
      · have hj' : j < i := by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
          · exact h
          · exact absurd hvv e
        obtain ⟨d1, d2, d3⟩ := hI.done j hj'
        refine ⟨?_, ?_, ?_⟩
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), d1]
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), d2]
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), d3]
  unfold rsbody
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hF'.r251, hI.r256]; omega
  config_simp
  rename_i _ hw₁
  rw [hF'.r251, hI.r256, mO] at hw₁ ⊢
  -- the generic vertex
  have hgen : v ≠ r₀ → ∀ (c₁ : Config), WordsBounded W c₁ →
      (∀ r, r < 259 ∨ 266 ≤ r → c₁.nreg r = c.nreg r ∨ r = 257 ∨ r = 258) →
      c₁.nreg 258 = v → c₁.nmem = c.nmem → c₁.output = c.output →
      ∃ c' t, Exec P W rsgen c₁ c' t ∧ t ≤ 20 ∧ ((∀ r, r < 259 ∨ 266 ≤ r → c'.nreg r = c₁.nreg r) ∧
        c'.nmem = upd (upd (upd c.nmem (bU + v) (upN A V Pr r₀ v)) (bD + v) (Dp v)) (bS + v) (R v) ∧
        c'.output = c.output) := by
    intro hne c₁ hc₁ hr₁ h258 hm₁ ho₁
    have g : ∀ r, r ≠ 256 → r ≠ 257 → r ≠ 258 → r < 259 ∨ 266 ≤ r → c₁.nreg r = c.nreg r :=
      fun r a b d e => by rcases hr₁ r e with h | h | h <;> first | exact h | omega
    have g215 : c₁.nreg 215 = bPr := (g 215 (by omega) (by omega) (by omega) (by omega)).trans hF'.r215
    have g147 : c₁.nreg 147 = bR := (g 147 (by omega) (by omega) (by omega) (by omega)).trans hF'.r147
    have g162 : c₁.nreg 162 = bV := (g 162 (by omega) (by omega) (by omega) (by omega)).trans hF'.r162
    have g250 : c₁.nreg 250 = bW := (g 250 (by omega) (by omega) (by omega) (by omega)).trans hF'.r250
    have g252 : c₁.nreg 252 = bS := (g 252 (by omega) (by omega) (by omega) (by omega)).trans hF'.r252
    have g253 : c₁.nreg 253 = bD := (g 253 (by omega) (by omega) (by omega) (by omega)).trans hF'.r253
    have g254 : c₁.nreg 254 = bU := (g 254 (by omega) (by omega) (by omega) (by omega)).trans hF'.r254
    have g141 : c₁.nreg 141 = 1 := (g 141 (by omega) (by omega) (by omega) (by omega)).trans hF'.r141
    have hPr := hin.Pr_lt v hv hne
    have hAx := hin.A_lt _ hPr
    have hpa := hin.pa_lt hv hne
    -- the parent has been processed
    obtain ⟨j, hj, hjp⟩ := hord.par_first i hi (by rw [hvv]; exact hne)
    rw [hvv] at hjp
    obtain ⟨-, d2, d3⟩ := hI.done j hj
    rw [hjp] at d2 d3
    have mP : c₁.nmem (bPr + v) = Pr v := by rw [hm₁]; exact hF'.mP v hv hne
    have mA : c₁.nmem (bR + Pr v) = A (Pr v) := by rw [hm₁]; exact hF'.mA _ hPr
    have mV : c₁.nmem (bV + A (Pr v)) = paN A V Pr v := by rw [hm₁]; exact hF'.mV _ hAx
    have mD : c₁.nmem (bD + paN A V Pr v) = Dp (paN A V Pr v) := by rw [hm₁]; exact d2
    have mS : c₁.nmem (bS + paN A V Pr v) = R (paN A V Pr v) := by rw [hm₁]; exact d3
    have mW : c₁.nmem (bW + v) = w v := by rw [hm₁]; exact hF'.mW v hv
    have eD := hDp.2 v hv hne
    have eR := hR.2 v hv hne
    have hRv := hRW v hv
    have hDv := hDW v hv
    unfold rsgen
    exec_block
    all_goals try (config_simp; simp only [g215, h258, mP, g147, mA, g162, mV, g253, mD, g141,
      g252, mS, g250, mW, g254]; omega)
    refine ⟨le_rfl, fun r hr => ?_, ?_, ?_⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
    · simp only [g215, h258, mP, g147, mA, g162, mV, g253, mD, g141, g252, mS, g250, mW, g254, hm₁]
      rw [← eD, ← eR]
      simp only [upN, hne, ↓reduceIte]
    · exact ho₁
  have hroot : v = r₀ → ∀ (c₁ : Config), WordsBounded W c₁ →
      (∀ r, r < 259 ∨ 266 ≤ r → c₁.nreg r = c.nreg r ∨ r = 257 ∨ r = 258) →
      c₁.nreg 258 = v → c₁.nmem = c.nmem → c₁.output = c.output →
      ∃ c' t, Exec P W rsroot c₁ c' t ∧ t ≤ 8 ∧ ((∀ r, r < 259 ∨ 266 ≤ r → c'.nreg r = c₁.nreg r) ∧
        c'.nmem = upd (upd (upd c.nmem (bU + v) (upN A V Pr r₀ v)) (bD + v) (Dp v)) (bS + v) (R v) ∧
        c'.output = c.output) := by
    intro he c₁ hc₁ hr₁ h258 hm₁ ho₁
    subst he
    have g : ∀ r, r ≠ 256 → r ≠ 257 → r ≠ 258 → r < 259 ∨ 266 ≤ r → c₁.nreg r = c.nreg r :=
      fun r a b d e => by rcases hr₁ r e with h | h | h <;> first | exact h | omega
    have g140 : c₁.nreg 140 = 0 := (g 140 (by omega) (by omega) (by omega) (by omega)).trans hF'.r140
    have g250 : c₁.nreg 250 = bW := (g 250 (by omega) (by omega) (by omega) (by omega)).trans hF'.r250
    have g252 : c₁.nreg 252 = bS := (g 252 (by omega) (by omega) (by omega) (by omega)).trans hF'.r252
    have g253 : c₁.nreg 253 = bD := (g 253 (by omega) (by omega) (by omega) (by omega)).trans hF'.r253
    have g254 : c₁.nreg 254 = bU := (g 254 (by omega) (by omega) (by omega) (by omega)).trans hF'.r254
    have mW : c₁.nmem (bW + v) = w v := by rw [hm₁]; exact hF'.mW v hv
    unfold rsroot
    exec_block
    all_goals try (config_simp; simp only [h258, g250, g252, g253, g254]; omega)
    refine ⟨le_rfl, fun r hr => ?_, ?_, ?_⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
    · simp only [h258, g140, g250, g252, g253, g254, mW, hm₁]
      rw [hR.1, hDp.1]
      simp only [upN, ↓reduceIte]
    · exact ho₁
  have hfin : ∀ c₂ : Config, WordsBounded W c₂ → (∀ r, r < 256 ∨ 266 ≤ r → c₂.nreg r = c.nreg r) →
      c₂.nreg 256 = i →
      c₂.nmem = upd (upd (upd c.nmem (bU + v) (upN A V Pr r₀ v)) (bD + v) (Dp v)) (bS + v) (R v) →
      c₂.output = c.output → ∃ c' k', Exec P W (.instr (.addN 256 256 141)) c₂ c' k' ∧
        RI (W := W) (n := n) (bS := bS) (bD := bD) (bU := bU) (r₀ := r₀) (A := A) (V := V)
          (Pr := Pr) (ord := ord) (R := R) (Dp := Dp) c₀ (i + 1) c' ∧ k' = 1 := by
    intro c₂ hw₂ hr₂ h256 hm₂ ho₂
    have g141 : c₂.nreg 141 = 1 := (hr₂ 141 (by omega)).trans hF'.r141
    refine spec_instr (Exec.addN hw₂ 256 256 141 (by rw [h256, g141]; omega)) fun hw₃ => ?_
    refine ⟨hstore _ _ _ rfl rfl rfl _ hw₃ (by config_simp; rw [h256, g141]) (fun r hr => ?_)
      (by config_simp; rw [ho₂, hI.out]) (by config_simp; exact hm₂), rfl⟩
    config_simp
    rw [upd_other _ _ _ (by omega), hr₂ r hr]
    exact hI.regs r hr
  have hc₁r : ∀ r, r < 259 ∨ 266 ≤ r →
      upd (upd c.nreg 257 (bO + i)) 258 v r = c.nreg r ∨ r = 257 ∨ r = 258 := fun r _ => by
    simp only [upd_apply]; split_ifs <;> first | omega | (left; rfl)
  have hfr : ∀ c₂ : Config, (∀ r, r < 259 ∨ 266 ≤ r →
      c₂.nreg r = upd (upd c.nreg 257 (bO + i)) 258 v r) →
      ∀ r, r < 256 ∨ 266 ≤ r → c₂.nreg r = c.nreg r := fun c₂ h r hr => by
    rw [h r (by omega)]; simp only [upd_apply]; split_ifs <;> first | omega | rfl
  have hfr' : ∀ c₂ : Config, (∀ r, r < 259 ∨ 266 ≤ r →
      c₂.nreg r = upd (upd c.nreg 257 (bO + i)) 258 v r) → c₂.nreg 256 = i := fun c₂ h => by
    rw [h 256 (by omega)]; simp only [upd_apply]; split_ifs <;> first | omega | exact hI.r256
  have g255 := hF'.r255
  refine spec_seq ?_
  rcases Nat.lt_trichotomy v r₀ with hlt | heq | hgt
  · refine spec_ifLtN_true (by config_simp; rw [g255]; exact hlt) ?_
    refine spec_use (hgen (by omega) _ ?_ ?_ ?_ ?_ ?_) ?_
    · exact hw₁
    · exact hc₁r
    · config_simp
    · rfl
    · rfl
    rintro c₂ k₂ hk hw₂ ⟨hr₂, hm₂, ho₂⟩
    obtain ⟨c', k', e, hI', rfl⟩ := hfin c₂ hw₂ (hfr c₂ hr₂) (hfr' c₂ hr₂) hm₂ ho₂
    exact ⟨c', 1, e, hI', by omega⟩
  · refine spec_ifLtN_false (by config_simp; rw [g255]; omega) ?_
    refine spec_ifLtN_false (by config_simp; rw [g255]; omega) ?_
    refine spec_use (hroot heq _ ?_ ?_ ?_ ?_ ?_) ?_
    · exact hw₁
    · exact hc₁r
    · config_simp
    · rfl
    · rfl
    rintro c₂ k₂ hk hw₂ ⟨hr₂, hm₂, ho₂⟩
    obtain ⟨c', k', e, hI', rfl⟩ := hfin c₂ hw₂ (hfr c₂ hr₂) (hfr' c₂ hr₂) hm₂ ho₂
    exact ⟨c', 1, e, hI', by omega⟩
  · refine spec_ifLtN_false (by config_simp; rw [g255]; omega) ?_
    refine spec_ifLtN_true (by config_simp; rw [g255]; exact hgt) ?_
    refine spec_use (hgen (by omega) _ ?_ ?_ ?_ ?_ ?_) ?_
    · exact hw₁
    · exact hc₁r
    · config_simp
    · rfl
    · rfl
    rintro c₂ k₂ hk hw₂ ⟨hr₂, hm₂, ho₂⟩
    obtain ⟨c', k', e, hI', rfl⟩ := hfin c₂ hw₂ (hfr c₂ hr₂) (hfr' c₂ hr₂) hm₂ ho₂
    exact ⟨c', 1, e, hI', by omega⟩

/-- **The pass of the root sums.** From the parent darts of a tree with root `r₀` and an order of
its vertices in which parents come first, `rspass` stores for every vertex `v < n` its parent
(`upN`, the root fixed) at `bU + v`, its depth at `bD + v` and its root sum at `bS + v`, within
`28 n + 3` steps. -/
theorem rspass_exec (c : Config) (hc : WordsBounded W c)
    (hF : RFix k n r₀ bR bV bPr bW bO bS bD bU A V Pr w ord c) :
    ∃ c' t, Exec P W rspass c c' t ∧ t ≤ 28 * n + 3 ∧
      (∀ v < n, c'.nmem (bU + v) = upN A V Pr r₀ v ∧ c'.nmem (bD + v) = Dp v ∧
        c'.nmem (bS + v) = R v) ∧
      (∀ r, r < 256 ∨ 266 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, ¬ ROut n bS bD bU a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  let I : ℕ → Config → Prop := fun i c' =>
    RI (W := W) (n := n) (bS := bS) (bD := bD) (bU := bU) (r₀ := r₀) (A := A) (V := V)
      (Pr := Pr) (ord := ord) (R := R) (Dp := Dp) c i c'
  have e₁ := Exec.copyN (P := P) hc 256 140
  have hI₁ : I 0 { c with nreg := upd c.nreg 256 (c.nreg 140) } := by
    refine ⟨e₁.wb_right, by config_simp; exact hF.r140, by omega, fun r hr => ?_, fun a _ => rfl,
      rfl, fun j hj => absurd hj (by omega)⟩
    config_simp; rw [upd_other _ _ _ (by omega)]
  obtain ⟨c', t, e, hI', ht⟩ := Exec.forN (P := P) (W := W) (ri := 256) (rN := 161) (N := n)
    (lo := 0) (B := 26) (body := rsbody) I
    (fun i c' h => ⟨h.wb, h.r256, (h.regs 161 (by omega)).trans hF.r161⟩)
    (fun i c' h hi => rsbody_exec hin hord hR hDp hRW hDW hl hF i c' h hi) (by omega) hI₁
  refine ⟨c', 1 + t, .seq e₁ e, by omega, fun v hv => ?_, hI'.regs, hI'.mem, hI'.out⟩
  obtain ⟨i, hi, rfl⟩ := hord.surj v hv
  exact hI'.done i hi

end proofs

/-! ### The bridge to spanning trees -/

section Bridge

open Map

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}
  {k n : ℕ} (cd : D ≃ Fin (3 * k)) (vi : Q ≃ Fin n) (T : M.SpTree) {A V : ℕ → ℕ}

/-- A function on the vertices, read on their numbers (`0` beyond `n`). -/
def ofV (f : Q → ℕ) (u : ℕ) : ℕ := if h : u < n then f (vi.symm ⟨u, h⟩) else 0

omit [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] in
@[simp] theorem ofV_vi (f : Q → ℕ) (v : Q) : ofV vi f (vi v) = f v := by
  simp [ofV]

omit [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] in
theorem exists_vi {u : ℕ} (hu : u < n) : ∃ v, vi v = u := ⟨vi.symm ⟨u, hu⟩, by simp⟩

omit [Fintype D] [DecidableEq D] [Fintype Q] in
/-- The parent read through the coding is the parent in the tree. -/
theorem paN_tree (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hV : ∀ x, V (cd x) = vi (M.vert x))
    {Pr : ℕ → ℕ} (hPr : ∀ v (h : v ≠ T.root), Pr (vi v) = cd (T.par v h)) {v : Q}
    (h : v ≠ T.root) : paN A V Pr (vi v) = vi (T.parent v) := by
  rw [paN, hPr v h, hAcd, hV, T.parent_of_ne h]

omit [Fintype D] [DecidableEq D] [Fintype Q] in
theorem upN_tree (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hV : ∀ x, V (cd x) = vi (M.vert x))
    {Pr : ℕ → ℕ} (hPr : ∀ v (h : v ≠ T.root), Pr (vi v) = cd (T.par v h)) (v : Q) :
    upN A V Pr (vi T.root) (vi v) = vi (T.parent v) := by
  unfold upN
  by_cases h : v = T.root
  · subst h; simp [T.parent_root]
  · rw [ite_eq_right_iff.2 (fun e => absurd (vi.injective (Fin.ext e)) h), paN_tree cd vi T hAcd hV hPr h]

omit [Fintype D] [DecidableEq D] [Fintype Q] in
/-- The coded tree satisfies `RootIn`. -/
theorem rootIn_tree (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hV : ∀ x, V (cd x) = vi (M.vert x))
    {Pr : ℕ → ℕ} (hPr : ∀ v (h : v ≠ T.root), Pr (vi v) = cd (T.par v h)) :
    RootIn k n (vi T.root) A V Pr := by
  refine ⟨(vi _).2, fun x hx => ?_, fun x hx => ?_, fun u hu hr => ?_⟩
  · have e : x = cd (cd.symm ⟨x, hx⟩) := by simp
    rw [e, hAcd]; exact (cd _).2
  · have e : x = cd (cd.symm ⟨x, hx⟩) := by simp
    rw [e, hV]; exact (vi _).2
  · obtain ⟨v, rfl⟩ := exists_vi vi hu
    have h : v ≠ T.root := fun h' => hr (by rw [h'])
    rw [hPr v h]; exact (cd _).2

omit [Fintype D] [Fintype Q] in
/-- **The root sums satisfy the recurrence.** -/
theorem rsRec_anc (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hV : ∀ x, V (cd x) = vi (M.vert x))
    {Pr : ℕ → ℕ} (hPr : ∀ v (h : v ≠ T.root), Pr (vi v) = cd (T.par v h)) (w : Q → ℕ) :
    RsRec n (vi T.root) (paN A V Pr) (ofV vi w)
      (ofV vi fun v => ∑ u ∈ T.anc v, w u) := by
  refine ⟨by simp [T.anc_root], fun u hu hr => ?_⟩
  obtain ⟨v, rfl⟩ := exists_vi vi hu
  have h : v ≠ T.root := fun h' => hr (by rw [h'])
  rw [paN_tree cd vi T hAcd hV hPr h, ofV_vi, ofV_vi, ofV_vi, T.anc_of_ne h,
    sum_insert (SpTree.notMem_anc_parent (T := T) h), add_comm]

omit [Fintype D] [Fintype Q] in
/-- **The depths satisfy the recurrence.** -/
theorem dpRec_anc (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hV : ∀ x, V (cd x) = vi (M.vert x))
    {Pr : ℕ → ℕ} (hPr : ∀ v (h : v ≠ T.root), Pr (vi v) = cd (T.par v h)) :
    DpRec n (vi T.root) (paN A V Pr) (ofV vi fun v => #(T.anc v) - 1) := by
  refine ⟨by simp [T.anc_root], fun u hu hr => ?_⟩
  obtain ⟨v, rfl⟩ := exists_vi vi hu
  have h : v ≠ T.root := fun h' => hr (by rw [h'])
  rw [paN_tree cd vi T hAcd hV hPr h, ofV_vi, ofV_vi, T.anc_of_ne h,
    card_insert_of_notMem (SpTree.notMem_anc_parent (T := T) h)]
  have := card_pos.2 ⟨_, T.mem_anc_self (T.parent v)⟩
  omega

omit [Fintype D] [DecidableEq D] in
include vi in
theorem card_anc_le (v : Q) : #(T.anc v) ≤ n := by
  have := card_le_univ (T.anc v)
  rwa [Fintype.card_congr vi, Fintype.card_fin] at this

/-- **The root sums of a spanning tree on the machine.** For a map coded by `cd` (reversals `A`
at `bR`, vertices `V` at `bV`), with its vertices numbered by `vi`, the parent darts of a spanning
tree `T` at `bPr`, the weights `w` at `bW` and an order of the vertices with parents first at
`bO`, the pass `rspass` stores, for every vertex `v`, its parent, its depth `#(anc v) - 1` and its
root sum `∑ u ∈ anc v, w u`, within `28 n + 3` steps. -/
theorem rspass_tree {W : ℕ} {P' : Input} {bR bV bPr bW bO bS bD bU : ℕ} {ord : ℕ → ℕ}
    (hAcd : ∀ x, A (cd x) = cd (M.α x)) (hV : ∀ x, V (cd x) = vi (M.vert x)) (w : Q → ℕ)
    (hl : RLay k n bR bV bPr bW bO bS bD bU W) (hWt : ∑ v, w v ≤ W) (c : Config)
    (hc : WordsBounded W c)
    (hF : RFix k n (vi T.root) bR bV bPr bW bO bS bD bU A V (fun u => c.nmem (bPr + u))
      (ofV vi w) ord c)
    (hPr : ∀ v (h : v ≠ T.root), c.nmem (bPr + vi v) = cd (T.par v h))
    (hord : IsOrd n (vi T.root) (paN A V fun u => c.nmem (bPr + u)) ord) :
    ∃ c' t, Exec P' W rspass c c' t ∧ t ≤ 28 * n + 3 ∧
      (∀ v, c'.nmem (bU + vi v) = vi (T.parent v) ∧ c'.nmem (bD + vi v) = #(T.anc v) - 1 ∧
        c'.nmem (bS + vi v) = ∑ u ∈ T.anc v, w u) ∧
      (∀ r, r < 256 ∨ 266 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, ¬ ROut n bS bD bU a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  have hRW : ∀ u < n, (ofV vi fun v => ∑ u ∈ T.anc v, w u) u ≤ W := fun u hu => by
    obtain ⟨v, rfl⟩ := exists_vi vi hu
    rw [ofV_vi]
    exact (sum_le_sum_of_subset (subset_univ _)).trans hWt
  have hDW : ∀ u < n, (ofV vi fun v => #(T.anc v) - 1) u ≤ W := fun u hu => by
    obtain ⟨v, rfl⟩ := exists_vi vi hu
    rw [ofV_vi]
    have := card_anc_le vi T v
    have := hl.hU
    omega
  obtain ⟨c', t, e, ht, hd, hr, hm, ho⟩ := rspass_exec (P := P') (rootIn_tree cd vi T hAcd hV hPr)
    hord (rsRec_anc cd vi T hAcd hV hPr w) (dpRec_anc cd vi T hAcd hV hPr) hRW hDW hl c hc hF
  refine ⟨c', t, e, ht, fun v => ?_, hr, hm, ho⟩
  obtain ⟨d1, d2, d3⟩ := hd (vi v) (vi v).2
  rw [d1, d2, d3, upN_tree cd vi T hAcd hV hPr, ofV_vi, ofV_vi]
  exact ⟨rfl, rfl, rfl⟩

end Bridge

end MillerProg

end PlanarSeparator
