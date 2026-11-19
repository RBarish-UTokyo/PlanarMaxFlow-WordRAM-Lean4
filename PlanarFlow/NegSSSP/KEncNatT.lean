module

public import PlanarFlow.NegSSSP.KEncNatA

/-!
# The shortest-path tree of the first source from its distances, on natural words

The encoding of a one-face instance (`Klein.KVal`) asks for an initial spanning tree `T`
compatible with the shortest-path tree of the first source `u` (`Klein.Compat`: for every vertex
`x` with a parent `tpar G u x = some a`, `T.par x = a`). For the isolating lengths the tight
incoming arc of every vertex is unique (`MSSP.Hyp.uniq`, `MSSP.UniqTight`), so `tpar` is
determined by the distances. Here a pass over the darts, on **natural words only**, writes the
parent of every reached vertex from the distances from `u`:

* `tpProg`: for every dart `j` of the piece (`S[j] > 0`) whose tail node `t = NT[j]` is reached
  (`R[t] > 0`) and with `D[t] + L[j] = D[h]` (`h = NH[j]`, tested as `D[h] - D[t] = L[j]` and
  `D[t] ≤ D[h]`, so no addition can overflow), `PAR[h] := j`. `tpProg_natOnly`.
* `tpProg_exec`: on index functions, within `29 nD + 3` steps, the parents are `tpW … nD`, the
  last tight dart into each node (`tpW_of_tight`: the tight dart itself when tight darts into a
  node are unique; `tpW_of_none`: the old word when there is none).
* `tpProg_tpar`: **on a map**: with the flags of `S`, the nodes `ιv` (injective, `< n`) of the
  tails and heads, the lengths `(ℓ d).toNat` (`ℓ > 0` on `S`), the reach bits from `u` and the
  distances `(dist G u x).toNat` of the reached vertices (`G = pieceGraph M S ℓ`, any order of
  the darts `σ`), and unique tight arcs (`UniqTight G`): **`PAR[ιv x] = σ a` for every
  `tpar G u x = some a`** — the part of `Compat` fixed by the distances.

The distances are computed in memory by `bfProg` (`KEncNatB.lean`). Not done: the completion
of the parents into a spanning tree `T` of the whole map with its orders.

Registers: natural `2300 … 2307` (inputs `nD`, `Sb`, `NTb`, `NHb`, `Lb`, `Rb`, `Db`, `Pb`),
`2310 … 2321` (scratch). Natural memory is written only at `Pb + NH[j]`; no real register or
real memory is touched.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The loads of the dart `j = r2310`: `f = S[j]` (`2313`), `t = NT[j]` (`2314`),
`h = NH[j]` (`2315`), `R[t]` (`2316`), `D[t]` (`2317`), `L[j]` (`2318`), `D[h]` (`2319`),
`D[h] - D[t]` (`2321`), the address `Pb + h` (`2320`). -/
def tpLoad : Stmt :=
  block [.addN 2313 2301 2310, .loadN 2313 2313, .addN 2314 2302 2310, .loadN 2314 2314,
    .addN 2315 2303 2310, .loadN 2315 2315, .addN 2316 2305 2314, .loadN 2316 2316,
    .addN 2317 2306 2314, .loadN 2317 2317, .addN 2318 2304 2310, .loadN 2318 2318,
    .addN 2319 2306 2315, .loadN 2319 2319, .subN 2321 2319 2317, .addN 2320 2307 2315]

/-- The test of the dart and the store `PAR[h] := j`. -/
def tpTest : Stmt :=
  .ifLtN 2312 2313
    (.ifLtN 2312 2316
      (.ifLtN 2321 2318 .skip (.ifLtN 2318 2321 .skip (.ifLtN 2319 2317 .skip
        (.instr (.storeN 2320 2310)))))
      .skip)
    .skip

/-- The body of the pass. -/
def tpBody : Stmt := .seq tpLoad (.seq tpTest (block [.addN 2310 2310 2311]))

/-- **The parents of the shortest-path tree from the distances.** -/
def tpProg : Stmt :=
  .seq (block [.constN 2311 1, .constN 2312 0, .constN 2310 0]) (.whileLtN 2310 2300 tpBody)

/-- **`tpProg` has no real instruction** (checked by the kernel). -/
theorem tpProg_natOnly : Klein.natOnly tpProg = true := by kernel_rfl

/-! ### On index functions -/

/-- The dart `j` is tight. -/
def TightI (fl NT NH Lv rb Dv : ℕ → ℕ) (j : ℕ) : Prop :=
  0 < fl j ∧ 0 < rb (NT j) ∧ Dv (NT j) + Lv j = Dv (NH j)

instance (fl NT NH Lv rb Dv : ℕ → ℕ) (j : ℕ) : Decidable (TightI fl NT NH Lv rb Dv j) := by
  unfold TightI; infer_instance

/-- The parent word of the node `y` after the darts `< i`: the last tight dart into `y`. -/
def tpW (fl NT NH Lv rb Dv : ℕ → ℕ) (old : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, y => old y
  | i + 1, y => if TightI fl NT NH Lv rb Dv i ∧ NH i = y then i else tpW fl NT NH Lv rb Dv old i y

lemma tpW_of_tight {fl NT NH Lv rb Dv old : ℕ → ℕ} {n : ℕ}
    (hU : ∀ j j', j < n → j' < n → TightI fl NT NH Lv rb Dv j → TightI fl NT NH Lv rb Dv j' →
      NH j = NH j' → j = j') {j : ℕ} (hj : j < n) (ht : TightI fl NT NH Lv rb Dv j) :
    tpW fl NT NH Lv rb Dv old n (NH j) = j := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [tpW]
    split_ifs with h
    · exact (hU j n hj (by omega) ht h.1 h.2.symm).symm
    · have hjn : j ≠ n := fun e => h ⟨e ▸ ht, by rw [e]⟩
      exact ih (fun a b ha hb => hU a b (by omega) (by omega)) (by omega)

lemma tpW_of_none {fl NT NH Lv rb Dv old : ℕ → ℕ} {n y : ℕ}
    (h : ∀ j < n, TightI fl NT NH Lv rb Dv j → NH j ≠ y) :
    tpW fl NT NH Lv rb Dv old n y = old y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [tpW]
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h' => h n (by omega) h'.1 h'.2)]
    exact ih fun j hj => h j (by omega)

/-- The layout of `tpProg`: the arrays by darts (`nD` words) and by nodes (`n` words) below `W`,
the parents `[Pb, Pb + n)` apart from the inputs. -/
structure TPLay (nD n Sb NTb NHb Lb Rb Db Pb W : ℕ) : Prop where
  one : 1 ≤ W
  wS : Sb + nD ≤ W
  wT : NTb + nD ≤ W
  wH : NHb + nD ≤ W
  wL : Lb + nD ≤ W
  wR : Rb + n ≤ W
  wD : Db + n ≤ W
  wP : Pb + n ≤ W
  dS : Sb + nD ≤ Pb ∨ Pb + n ≤ Sb
  dT : NTb + nD ≤ Pb ∨ Pb + n ≤ NTb
  dH : NHb + nD ≤ Pb ∨ Pb + n ≤ NHb
  dL : Lb + nD ≤ Pb ∨ Pb + n ≤ Lb
  dR : Rb + n ≤ Pb ∨ Pb + n ≤ Rb
  dD : Db + n ≤ Pb ∨ Pb + n ≤ Db

theorem tpTest_exec (c : Config) (hc : WordsBounded W c) (h12 : c.nreg 2312 = 0)
    (h21 : c.nreg 2321 = c.nreg 2319 - c.nreg 2317) :
    ∃ c' t, Exec P W tpTest c c' t ∧ t ≤ 10 ∧
      c' = if 0 < c.nreg 2313 ∧ 0 < c.nreg 2316 ∧ c.nreg 2317 + c.nreg 2318 = c.nreg 2319 then
        { c with nmem := upd c.nmem (c.nreg 2320) (c.nreg 2310) } else c := by
  unfold tpTest
  by_cases h1 : 0 < c.nreg 2313
  · refine spec_ifLtN_true (by rw [h12]; exact h1) ?_
    by_cases h2 : 0 < c.nreg 2316
    · refine spec_ifLtN_true (by rw [h12]; exact h2) ?_
      by_cases h3 : c.nreg 2321 < c.nreg 2318
      · refine spec_ifLtN_true h3 (spec_skip hc ⟨by omega, ?_⟩)
        rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => by omega)]
      · refine spec_ifLtN_false h3 ?_
        by_cases h4 : c.nreg 2318 < c.nreg 2321
        · refine spec_ifLtN_true h4 (spec_skip hc ⟨by omega, ?_⟩)
          rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => by omega)]
        · refine spec_ifLtN_false h4 ?_
          by_cases h5 : c.nreg 2319 < c.nreg 2317
          · refine spec_ifLtN_true h5 (spec_skip hc ⟨by omega, ?_⟩)
            rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => by omega)]
          · refine spec_ifLtN_false h5 ?_
            refine spec_instr (Exec.storeN hc _ _) fun _ => ⟨by omega, ?_⟩
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨h1, h2, by omega⟩)]
    · refine spec_ifLtN_false (by rw [h12]; exact h2) (spec_skip hc ⟨by omega, ?_⟩)
      rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => h2 h.2.1)]
  · refine spec_ifLtN_false (by rw [h12]; exact h1) (spec_skip hc ⟨by omega, ?_⟩)
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => h1 h.1)]

set_option maxHeartbeats 2000000 in
/-- **The pass on index functions**: within `29 nD + 3` steps the word at `Pb + y` (`y < n`) is
`tpW … nD y`, the last tight dart into `y` (or the old word); the rest of the natural memory, the
registers outside `[2310, 2322)`, the reals and the output are kept. -/
theorem tpProg_exec {nD n Sb NTb NHb Lb Rb Db Pb : ℕ} (hL : TPLay nD n Sb NTb NHb Lb Rb Db Pb W)
    (c : Config) (hc : WordsBounded W c) (h00 : c.nreg 2300 = nD) (h01 : c.nreg 2301 = Sb)
    (h02 : c.nreg 2302 = NTb) (h03 : c.nreg 2303 = NHb) (h04 : c.nreg 2304 = Lb)
    (h05 : c.nreg 2305 = Rb) (h06 : c.nreg 2306 = Db) (h07 : c.nreg 2307 = Pb)
    (hNT : ∀ j < nD, c.nmem (NTb + j) < n) (hNH : ∀ j < nD, c.nmem (NHb + j) < n) :
    ∃ c' t, Exec P W tpProg c c' t ∧ t ≤ 29 * nD + 5 ∧
      ((∀ y < n, c'.nmem (Pb + y) = tpW (fun j => c.nmem (Sb + j)) (fun j => c.nmem (NTb + j))
          (fun j => c.nmem (NHb + j)) (fun j => c.nmem (Lb + j)) (fun y => c.nmem (Rb + y))
          (fun y => c.nmem (Db + y)) (fun y => c.nmem (Pb + y)) nD y) ∧
        (∀ a, a < Pb ∨ Pb + n ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 2310 ∨ 2322 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wT; have := hL.wH; have := hL.wL; have := hL.wR; have := hL.wD
  have := hL.wP; have := hL.dS; have := hL.dT; have := hL.dH; have := hL.dL; have := hL.dR
  have := hL.dD; have := hL.one
  obtain ⟨fl, hfl⟩ : ∃ f : ℕ → ℕ, f = fun j => c.nmem (Sb + j) := ⟨_, rfl⟩
  obtain ⟨NT, hNTd⟩ : ∃ f : ℕ → ℕ, f = fun j => c.nmem (NTb + j) := ⟨_, rfl⟩
  obtain ⟨NH, hNHd⟩ : ∃ f : ℕ → ℕ, f = fun j => c.nmem (NHb + j) := ⟨_, rfl⟩
  obtain ⟨Lv, hLv⟩ : ∃ f : ℕ → ℕ, f = fun j => c.nmem (Lb + j) := ⟨_, rfl⟩
  obtain ⟨rb, hrb⟩ : ∃ f : ℕ → ℕ, f = fun y => c.nmem (Rb + y) := ⟨_, rfl⟩
  obtain ⟨Dv, hDv⟩ : ∃ f : ℕ → ℕ, f = fun y => c.nmem (Db + y) := ⟨_, rfl⟩
  obtain ⟨old, hold⟩ : ∃ f : ℕ → ℕ, f = fun y => c.nmem (Pb + y) := ⟨_, rfl⟩
  rw [← hfl, ← hNTd, ← hNHd, ← hLv, ← hrb, ← hDv, ← hold]
  have hNT' : ∀ j < nD, NT j < n := fun j hj => by rw [hNTd]; exact hNT j hj
  have hNH' : ∀ j < nD, NH j < n := fun j hj => by rw [hNHd]; exact hNH j hj
  unfold tpProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ y < n, c'.nmem (Pb + y) = tpW fl NT NH Lv rb Dv old i y) ∧
      (∀ a, a < Pb ∨ Pb + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2310 ∨ 2322 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nreg 2311 = 1 ∧
      c'.nreg 2312 = 0 ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 2310) (bR := 2300) (body := tpBody) J (K := 27)
    (n := nD) _ ‹_› (by config_simp) (by config_simp; exact h00) ?_
    (fun i c₁ hi hw ha hb ⟨g, gnm, gn, g11, g12, gr, grm, go⟩ => by
      have e01 : c₁.nreg 2301 = Sb := (gn 2301 (by omega)).trans h01
      have e02 : c₁.nreg 2302 = NTb := (gn 2302 (by omega)).trans h02
      have e03 : c₁.nreg 2303 = NHb := (gn 2303 (by omega)).trans h03
      have e04 : c₁.nreg 2304 = Lb := (gn 2304 (by omega)).trans h04
      have e05 : c₁.nreg 2305 = Rb := (gn 2305 (by omega)).trans h05
      have e06 : c₁.nreg 2306 = Db := (gn 2306 (by omega)).trans h06
      have e07 : c₁.nreg 2307 = Pb := (gn 2307 (by omega)).trans h07
      have tlt := hNT' i hi
      have hlt := hNH' i hi
      have xf : c₁.nmem (Sb + i) = fl i := by rw [gnm _ (by omega), hfl]
      have xt : c₁.nmem (NTb + i) = NT i := by rw [gnm _ (by omega), hNTd]
      have xh : c₁.nmem (NHb + i) = NH i := by rw [gnm _ (by omega), hNHd]
      have xl : c₁.nmem (Lb + i) = Lv i := by rw [gnm _ (by omega), hLv]
      have xr : c₁.nmem (Rb + NT i) = rb (NT i) := by rw [gnm _ (by omega), hrb]
      have xdt : c₁.nmem (Db + NT i) = Dv (NT i) := by rw [gnm _ (by omega), hDv]
      have xdh : c₁.nmem (Db + NH i) = Dv (NH i) := by rw [gnm _ (by omega), hDv]
      -- the loads
      obtain ⟨c₂, k₂, e₂, hk₂, p13, p14, p15, p16, p17, p18, p19, p20, p21, p10, p11, p12, pn,
          pnm, pr, prm, po⟩ :
          ∃ c₂ k₂, Exec P W tpLoad c₁ c₂ k₂ ∧ k₂ ≤ 16 ∧
            c₂.nreg 2313 = fl i ∧ c₂.nreg 2314 = NT i ∧ c₂.nreg 2315 = NH i ∧
            c₂.nreg 2316 = rb (NT i) ∧ c₂.nreg 2317 = Dv (NT i) ∧ c₂.nreg 2318 = Lv i ∧
            c₂.nreg 2319 = Dv (NH i) ∧ c₂.nreg 2320 = Pb + NH i ∧
            c₂.nreg 2321 = c₂.nreg 2319 - c₂.nreg 2317 ∧ c₂.nreg 2310 = i ∧
            c₂.nreg 2311 = 1 ∧ c₂.nreg 2312 = 0 ∧
            (∀ r, r < 2313 ∨ 2322 ≤ r → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
            c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
        unfold tpLoad
        exec_block
        all_goals try ((try config_simp); (try simp only [e01, e02, e03, e04, e05, e06, e07, ha, xt, xh]); omega)
        refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl,
          rfl, rfl⟩
        all_goals config_simp
        all_goals try simp only [e01, e02, e03, e04, e05, e06, e07, ha, xf, xt, xh, xl, xr, xdt, xdh,
          g11, g12]
        · simp (disch := omega) only [upd_other]
      obtain ⟨c₃, k₃, e₃, hk₃, hc₃⟩ := tpTest_exec (P := P) c₂ e₂.wb_right p12 p21
      have q3 : c₃.nreg = c₂.nreg := by rw [hc₃]; split_ifs <;> rfl
      have qr : c₃.rreg = c₂.rreg := by rw [hc₃]; split_ifs <;> rfl
      have qrm : c₃.rmem = c₂.rmem := by rw [hc₃]; split_ifs <;> rfl
      have qo : c₃.output = c₂.output := by rw [hc₃]; split_ifs <;> rfl
      have qm : c₃.nmem = if TightI fl NT NH Lv rb Dv i then upd c₂.nmem (Pb + NH i) i
          else c₂.nmem := by
        rw [hc₃]
        unfold TightI
        rw [p13, p16, p17, p18, p19, p20, p10]
        split_ifs <;> rfl
      have hw₃ := e₃.wb_right
      have e₄ := Exec.addN (P := P) hw₃ 2310 2310 2311 (by rw [q3, p10, p11]; omega)
      refine ⟨_, _, Exec.seq e₂ (Exec.seq e₃ (Exec.block_cons e₄ (Exec.block_nil e₄.wb_right))),
        by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · config_simp; rw [q3, p10, p11]
      · config_simp; rw [q3, pn _ (by omega), hb]
      · intro y hy
        config_simp
        rw [qm, pnm]
        simp only [tpW]
        by_cases ht : TightI fl NT NH Lv rb Dv i
        · by_cases hy' : NH i = y
          · subst hy'
            simp only [ht, upd_same, and_self, ↓reduceIte]
          · rw [ite_eq_left_of_eq_true _ _ (eq_true ht), upd_other _ _ _ (by omega),
              ite_eq_right_of_eq_false _ _ (eq_false fun h => hy' h.2)]
            exact g y hy
        · rw [ite_eq_right_of_eq_false _ _ (eq_false ht),
            ite_eq_right_of_eq_false _ _ (eq_false fun h => ht h.1)]
          exact g y hy
      · intro a ha'
        config_simp
        rw [qm, pnm]
        split_ifs
        · rw [upd_other _ _ _ (by omega)]; exact gnm a ha'
        · exact gnm a ha'
      · intro r hr
        config_simp
        rw [upd_other _ _ _ (by omega), q3, pn _ (by omega)]
        exact gn r hr
      · config_simp; rw [q3, p11]
      · config_simp; rw [q3, p12]
      · config_simp; rw [qr, pr, gr]
      · config_simp; rw [qrm, prm, grm]
      · config_simp; rw [qo, po, go])) ?_
  · refine ⟨fun y _ => ?_, fun a _ => rfl, fun r hr => ?_, ?_, ?_, rfl, rfl, rfl⟩
    · config_simp; simp only [tpW]; rw [hold]
    · config_simp; simp (disch := omega) only [upd_other]
    · config_simp
    · config_simp
  rintro c₂ k₂ hk₂ _ ⟨_, g, gnm, gn, -, -, gr, grm, go⟩
  exact ⟨by omega, g, gnm, fun r hr => gn r hr, gr, grm, go⟩

/-! ### On a map -/

section Map

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ}

/-- A dart of the piece with its tail reached is tight exactly when the distances say so. -/
lemma tight_iff_toNat (hpos : ∀ d ∈ S, 0 < ℓ d) {u : V} {d : D} (hd : d ∈ S)
    (hr : MSSP.Reach (MSSP.pieceGraph M S ℓ) u (M.tail d)) :
    MSSP.Tight (MSSP.pieceGraph M S ℓ) u ⟨d, hd⟩ ↔
      (MSSP.dist (MSSP.pieceGraph M S ℓ) u (M.tail d)).toNat + (ℓ d).toNat =
        (MSSP.dist (MSSP.pieceGraph M S ℓ) u (M.head d)).toNat := by
  have hnn : ∀ a, 0 ≤ (MSSP.pieceGraph M S ℓ).len a := fun a => (hpos a.1 a.2).le
  have hr' : MSSP.Reach (MSSP.pieceGraph M S ℓ) u (M.head d) :=
    MSSP.Reach.arc (G := MSSP.pieceGraph M S ℓ) (a := ⟨d, hd⟩) hr
  have h1 : 0 ≤ MSSP.dist (MSSP.pieceGraph M S ℓ) u (M.tail d) := MSSP.dist_nonneg hnn hr
  have h2 : 0 ≤ MSSP.dist (MSSP.pieceGraph M S ℓ) u (M.head d) := MSSP.dist_nonneg hnn hr'
  have h3 := hpos d hd
  unfold MSSP.Tight
  change MSSP.Reach _ u (M.tail d) ∧ MSSP.dist _ u (M.tail d) + ℓ d = MSSP.dist _ u (M.head d) ↔ _
  constructor
  · rintro ⟨-, h⟩; omega
  · intro h; exact ⟨hr, by omega⟩

set_option maxHeartbeats 1000000 in
/-- **The parents written by `tpProg` are those of the shortest-path tree** (see the module
docstring): for every vertex `x` with `tpar G u x = some a`, `PAR[ιv x] = σ a`. -/
theorem tpProg_tpar {nD n Sb NTb NHb Lb Rb Db Pb : ℕ} (hpos : ∀ d ∈ S, 0 < ℓ d)
    (hU : MSSP.UniqTight (MSSP.pieceGraph M S ℓ)) (σ : D ≃ Fin nD) {ιv : V → ℕ}
    (hinj : Function.Injective ιv) (hιn : ∀ x, ιv x < n) (u : V)
    (hL : TPLay nD n Sb NTb NHb Lb Rb Db Pb W) (c : Config) (hc : WordsBounded W c)
    (h00 : c.nreg 2300 = nD) (h01 : c.nreg 2301 = Sb) (h02 : c.nreg 2302 = NTb)
    (h03 : c.nreg 2303 = NHb) (h04 : c.nreg 2304 = Lb) (h05 : c.nreg 2305 = Rb)
    (h06 : c.nreg 2306 = Db) (h07 : c.nreg 2307 = Pb)
    (hfl : ∀ d, 0 < c.nmem (Sb + σ d) ↔ d ∈ S)
    (hNT : ∀ d, c.nmem (NTb + σ d) = ιv (M.tail d))
    (hNH : ∀ d, c.nmem (NHb + σ d) = ιv (M.head d))
    (hLv : ∀ d ∈ S, c.nmem (Lb + σ d) = (ℓ d).toNat)
    (hrb : ∀ x, 0 < c.nmem (Rb + ιv x) ↔ MSSP.Reach (MSSP.pieceGraph M S ℓ) u x)
    (hDv : ∀ x, MSSP.Reach (MSSP.pieceGraph M S ℓ) u x →
      c.nmem (Db + ιv x) = (MSSP.dist (MSSP.pieceGraph M S ℓ) u x).toNat) :
    ∃ c' t, Exec P W tpProg c c' t ∧ t ≤ 29 * nD + 5 ∧
      (∀ x a, Klein.tpar (MSSP.pieceGraph M S ℓ) u x = some a → c'.nmem (Pb + ιv x) = σ a.1) ∧
      (∀ a, a < Pb ∨ Pb + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2310 ∨ 2322 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  have hσs : ∀ j < nD, ∃ d, (σ d : ℕ) = j := fun j hj =>
    ⟨σ.symm ⟨j, hj⟩, by simp⟩
  have hNT' : ∀ j < nD, c.nmem (NTb + j) < n := fun j hj => by
    obtain ⟨d, rfl⟩ := hσs j hj; rw [hNT]; exact hιn _
  have hNH' : ∀ j < nD, c.nmem (NHb + j) < n := fun j hj => by
    obtain ⟨d, rfl⟩ := hσs j hj; rw [hNH]; exact hιn _
  obtain ⟨c', t, ex, ht, hP, hm, hn, hr, hrm, ho⟩ :=
    tpProg_exec (P := P) hL c hc h00 h01 h02 h03 h04 h05 h06 h07 hNT' hNH'
  have hnn : ∀ a, 0 ≤ (MSSP.pieceGraph M S ℓ).len a := fun a => (hpos a.1 a.2).le
  -- a tight index is the number of a tight arc
  have hT : ∀ d, TightI (fun j => c.nmem (Sb + j)) (fun j => c.nmem (NTb + j))
      (fun j => c.nmem (NHb + j)) (fun j => c.nmem (Lb + j)) (fun y => c.nmem (Rb + y))
      (fun y => c.nmem (Db + y)) (σ d) ↔ ∃ hd : d ∈ S,
        MSSP.Tight (MSSP.pieceGraph M S ℓ) u ⟨d, hd⟩ := fun d => by
    unfold TightI
    simp only [hNT, hNH]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hd := (hfl d).1 h1
      have hr := (hrb _).1 h2
      have hr' : MSSP.Reach (MSSP.pieceGraph M S ℓ) u (M.head d) :=
        MSSP.Reach.arc (G := MSSP.pieceGraph M S ℓ) (a := ⟨d, hd⟩) hr
      refine ⟨hd, (tight_iff_toNat hpos hd hr).2 ?_⟩
      rw [← hDv _ hr, ← hLv d hd, ← hDv _ hr']
      exact h3
    · rintro ⟨hd, hT⟩
      have hr : MSSP.Reach (MSSP.pieceGraph M S ℓ) u (M.tail d) := hT.1
      have hr' : MSSP.Reach (MSSP.pieceGraph M S ℓ) u (M.head d) :=
        MSSP.Reach.arc (G := MSSP.pieceGraph M S ℓ) (a := ⟨d, hd⟩) hr
      refine ⟨(hfl d).2 hd, (hrb _).2 hr, ?_⟩
      rw [hDv _ hr, hLv d hd, hDv _ hr']
      exact (tight_iff_toNat hpos hd hr).1 hT
  -- no tight arc enters the source
  have hne : ∀ d (hd : d ∈ S), MSSP.Tight (MSSP.pieceGraph M S ℓ) u ⟨d, hd⟩ → M.head d ≠ u := by
    intro d hd hT e
    have h1 := MSSP.dist_nonneg hnn hT.1
    have h2 := hT.2
    change _ + ℓ d = MSSP.dist _ u (M.head d) at h2
    rw [e, MSSP.dist_self hnn] at h2
    have := hpos d hd
    omega
  refine ⟨c', t, ex, ht, fun x a ha => ?_, hm, hn, hr, hrm, ho⟩
  obtain ⟨hTa, hdst, -⟩ := Klein.tpar_spec ha
  obtain ⟨d, hd⟩ := a
  have hx : M.head d = x := hdst
  have hj : TightI (fun j => c.nmem (Sb + j)) (fun j => c.nmem (NTb + j))
      (fun j => c.nmem (NHb + j)) (fun j => c.nmem (Lb + j)) (fun y => c.nmem (Rb + y))
      (fun y => c.nmem (Db + y)) (σ d) := (hT d).2 ⟨hd, hTa⟩
  have e := tpW_of_tight (old := fun y => c.nmem (Pb + y)) (n := nD) (fun j j' hj hj' t1 t2 eh => by
    obtain ⟨d₁, rfl⟩ := hσs j hj
    obtain ⟨d₂, rfl⟩ := hσs j' hj'
    obtain ⟨h₁, T₁⟩ := (hT d₁).1 t1
    obtain ⟨h₂, T₂⟩ := (hT d₂).1 t2
    simp only [hNH] at eh
    have eh' : M.head d₁ = M.head d₂ := hinj eh
    have := hU u ⟨d₁, h₁⟩ ⟨d₂, h₂⟩ T₁ T₂ eh' (hne d₁ h₁ T₁)
    simp only [Subtype.mk.injEq] at this
    rw [this]) (σ d).2 hj
  simp only [hNH, hx] at e
  rw [hP _ (hιn x), e]

end Map

end NegSSSP

end PlanarFlow
