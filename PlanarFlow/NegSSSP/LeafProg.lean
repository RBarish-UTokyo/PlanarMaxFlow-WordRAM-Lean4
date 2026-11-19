module

public import PlanarFlow.NegSSSP.LeafSem

/-!
# Bellman–Ford for the leaves on the machine (natural words, negative lengths)

`lbProg` (registers `2400 … 2424`; inputs `r2400 = m` arcs, `r2401 = Tb`, `r2402 = Hb'`,
`r2403 = LLb` (the arrays of tails, heads and offset lengths `LL a = lam a + L`), `r2404 = L`,
`r2405 = Db` (the values, `w` words), `r2406 = w`, `r2407 = R` rounds, `r2408 = K`):
`D[v] := K` for `v < w`, then `R` rounds relaxing every arc (`lbRelax`), then a check pass
setting the flag `r2424 := 1` iff some arc is still relaxable. Natural words only
(`lbProg_natOnly`).

* `lbLoad_exec`, `lbTest_exec`, `lbBody_exec`, `lbRound_exec`, `lbInit_exec`, `lbCheck_exec`.
* **`lbProg_exec`**: within `lbCost m w R = 5w + 8 + R (19m + 6) + 18m + 4` steps, after `R`
  rounds the invariant `LBInv … R (R m)` holds, and the flag is `0` with no arc relaxable or `1`
  with one; memory written only in `[Db, Db + w)`, registers only `2410 … 2424`. Hypotheses:
  `K ≥ R m L`, `K + 2L ≤ W` and the layout below `W`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset MSSP WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {I : Input} {W : ℕ}

/-! ### The program -/

/-- `D[y] := K` (`y < w`), the constants `1`, `0` and the round counter. -/
def lbInit : Stmt :=
  .seq (block [.constN 2410 1, .constN 2411 0, .constN 2412 0])
    (.seq (.whileLtN 2412 2406 (block [.addN 2414 2405 2412, .storeN 2414 2408,
        .addN 2412 2412 2410]))
      (block [.constN 2413 0]))

/-- The loads of the arc `j = r2412`: the address `Db + H[j]` (`2420`), `D[T[j]] + LL[j]`
(`2421`), `D[H[j]] + L` (`2422`). -/
def lbLoad : Stmt :=
  block [.addN 2415 2401 2412, .loadN 2415 2415, .addN 2416 2402 2412, .loadN 2416 2416,
    .addN 2417 2405 2415, .loadN 2417 2417, .addN 2418 2405 2416, .loadN 2418 2418,
    .addN 2419 2403 2412, .loadN 2419 2419, .addN 2420 2405 2416, .addN 2421 2417 2419,
    .addN 2422 2418 2404]

/-- The relaxation of the arc. -/
def lbTest : Stmt :=
  .ifLtN 2421 2422 (block [.subN 2423 2421 2404, .storeN 2420 2423]) .skip

/-- The body of a round. -/
def lbBody : Stmt := .seq lbLoad (.seq lbTest (block [.addN 2412 2412 2410]))

/-- A round. -/
def lbRound : Stmt :=
  .seq (block [.constN 2412 0]) (.seq (.whileLtN 2412 2400 lbBody) (block [.addN 2413 2413 2410]))

/-- The body of the check pass. -/
def lbCkBody : Stmt :=
  .seq lbLoad (.seq (.ifLtN 2421 2422 (.instr (.constN 2424 1)) .skip)
    (block [.addN 2412 2412 2410]))

/-- The check pass: `r2424 := 1` iff some arc is relaxable. -/
def lbCheck : Stmt := .seq (block [.constN 2424 0, .constN 2412 0]) (.whileLtN 2412 2400 lbCkBody)

/-- **Bellman–Ford for the leaves.** -/
def lbProg : Stmt := .seq lbInit (.seq (.whileLtN 2413 2407 lbRound) lbCheck)

theorem lbProg_natOnly : Klein.natOnly lbProg = true := by decide +kernel

/-! ### The blocks -/

theorem lbLoad_exec (c : Config) (hc : WordsBounded W c) {i Tb Hb' LLb L Db : ℕ}
    (h01 : c.nreg 2401 = Tb) (h02 : c.nreg 2402 = Hb') (h03 : c.nreg 2403 = LLb)
    (h04 : c.nreg 2404 = L) (h05 : c.nreg 2405 = Db) (h12 : c.nreg 2412 = i)
    (wT : Tb + i ≤ W) (wH : Hb' + i ≤ W) (wL : LLb + i ≤ W) (wDt : Db + c.nmem (Tb + i) ≤ W)
    (wDh : Db + c.nmem (Hb' + i) ≤ W)
    (wx : c.nmem (Db + c.nmem (Tb + i)) + c.nmem (LLb + i) ≤ W)
    (wy : c.nmem (Db + c.nmem (Hb' + i)) + L ≤ W) :
    ∃ c' t, Exec I W lbLoad c c' t ∧ t = 13 ∧ c'.nreg 2420 = Db + c.nmem (Hb' + i) ∧
      c'.nreg 2421 = c.nmem (Db + c.nmem (Tb + i)) + c.nmem (LLb + i) ∧
      c'.nreg 2422 = c.nmem (Db + c.nmem (Hb' + i)) + L ∧
      (∀ q, q < 2415 ∨ 2423 ≤ q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lbLoad
  exec_block
  all_goals try ((try config_simp); (try simp only [h01, h02, h03, h04, h05, h12]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try simp only [h01, h02, h03, h04, h05, h12]
  simp (disch := omega) only [upd_other]

theorem lbTest_exec (c : Config) (hc : WordsBounded W c) {L : ℕ} (h04 : c.nreg 2404 = L) :
    ∃ c' t, Exec I W lbTest c c' t ∧ t ≤ 3 ∧
      c'.nmem = (if c.nreg 2421 < c.nreg 2422 then
        upd c.nmem (c.nreg 2420) (c.nreg 2421 - L) else c.nmem) ∧
      (∀ r, r ≠ 2423 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold lbTest
  by_cases h : c.nreg 2421 < c.nreg 2422
  · refine spec_ifLtN_true h ?_
    exec_block
    refine ⟨by omega, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
    · config_simp; rw [if_pos h, h04]
    · config_simp; rw [upd_other _ _ _ hr]
  · refine spec_ifLtN_false h (spec_skip hc ⟨by omega, ?_, fun r _ => rfl, rfl, rfl, rfl⟩)
    rw [if_neg h]

/-- The inputs of `lbProg` in memory. -/
structure LBIn (m : ℕ) (T H LL : ℕ → ℕ) (Tb Hb' LLb : ℕ) (mem : ℕ → ℕ) : Prop where
  t : ∀ a < m, mem (Tb + a) = T a
  h : ∀ a < m, mem (Hb' + a) = H a
  l : ∀ a < m, mem (LLb + a) = LL a

/-- The layout of `lbProg`. -/
structure LBLay (m w Tb Hb' LLb Db K L R W : ℕ) : Prop where
  one : 1 ≤ W
  wT : Tb + m ≤ W
  wH : Hb' + m ≤ W
  wL : LLb + m ≤ W
  wD : Db + w ≤ W
  wV : K + 2 * L ≤ W
  wR : R ≤ W
  dT : Tb + m ≤ Db ∨ Db + w ≤ Tb
  dH : Hb' + m ≤ Db ∨ Db + w ≤ Hb'
  dL : LLb + m ≤ Db ∨ Db + w ≤ LLb

lemma LBIn.frame {m Db w : ℕ} {T H LL : ℕ → ℕ} {Tb Hb' LLb K L R : ℕ}
    (hL : LBLay m w Tb Hb' LLb Db K L R W) {mem mem' : ℕ → ℕ}
    (h : LBIn m T H LL Tb Hb' LLb mem) (hm : ∀ a, a < Db ∨ Db + w ≤ a → mem' a = mem a) :
    LBIn m T H LL Tb Hb' LLb mem' := by
  have := hL.dT; have := hL.dH; have := hL.dL
  exact ⟨fun a ha => by rw [hm _ (by omega)]; exact h.t a ha,
    fun a ha => by rw [hm _ (by omega)]; exact h.h a ha,
    fun a ha => by rw [hm _ (by omega)]; exact h.l a ha⟩


/-! ### One arc, one round -/

theorem lbBody_exec {m w Tb Hb' LLb Db K L R i : ℕ} {T H LL : ℕ → ℕ}
    (hLay : LBLay m w Tb Hb' LLb Db K L R W) (hi : i < m)
    (hT : ∀ a < m, T a < w) (hH : ∀ a < m, H a < w) (hLL : ∀ a < m, LL a ≤ 2 * L)
    (c : Config) (hc : WordsBounded W c) (hIn : LBIn m T H LL Tb Hb' LLb c.nmem)
    (hK : ∀ v < w, c.nmem (Db + v) ≤ K)
    (h01 : c.nreg 2401 = Tb) (h02 : c.nreg 2402 = Hb') (h03 : c.nreg 2403 = LLb)
    (h04 : c.nreg 2404 = L) (h05 : c.nreg 2405 = Db) (h10 : c.nreg 2410 = 1)
    (h12 : c.nreg 2412 = i) :
    ∃ c' t, Exec I W lbBody c c' t ∧ t ≤ 17 ∧ c'.nmem = lbRelax T H LL Db L i c.nmem ∧
      c'.nreg 2412 = i + 1 ∧ (∀ q, q < 2412 ∨ (2412 < q ∧ q < 2415) ∨ 2424 ≤ q →
        c'.nreg q = c.nreg q) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hLay.wT; have := hLay.wH; have := hLay.wL; have := hLay.wD; have := hLay.wV
  have ti := hT i hi; have hi' := hH i hi; have li := hLL i hi
  have et := hIn.t i hi; have eh := hIn.h i hi; have el := hIn.l i hi
  have kt := hK _ ti; have kh := hK _ hi'
  obtain ⟨c₂, t₂, e₂, ht₂, p20, p21, p22, pn, pm, pr, prm, po⟩ :=
    lbLoad_exec (I := I) c hc h01 h02 h03 h04 h05 h12 (by omega) (by omega) (by omega)
      (by rw [et]; omega) (by rw [eh]; omega) (by rw [et, el]; omega) (by rw [eh]; omega)
  obtain ⟨c₃, t₃, e₃, ht₃, qm, qn, qr, qrm, qo⟩ :=
    lbTest_exec (I := I) c₂ e₂.wb_right (L := L) (by rw [pn _ (by omega)]; exact h04)
  have hw₃ := e₃.wb_right
  have e₄ := Exec.addN (P := I) hw₃ 2412 2412 2410
    (by rw [qn _ (by omega), qn _ (by omega), pn _ (by omega), pn _ (by omega), h10, h12]; omega)
  refine ⟨_, _, Exec.seq e₂ (Exec.seq e₃ (Exec.block_cons e₄ (Exec.block_nil e₄.wb_right))),
    by omega, ?_, ?_, fun q hq => ?_, ?_, ?_, ?_⟩
  · config_simp
    rw [qm, p20, p21, p22, pm, et, eh, el]
    rfl
  · config_simp
    rw [qn _ (by omega), qn _ (by omega), pn _ (by omega), pn _ (by omega), h10, h12]
  · config_simp
    rw [upd_other _ _ _ (by omega), qn _ (by omega), pn _ (by omega)]
  · config_simp; rw [qr, pr]
  · config_simp; rw [qrm, prm]
  · config_simp; rw [qo, po]

/-- The values of the invariant are at most `K`. -/
lemma LBInv.le_K {m w Db K r s : ℕ} {T H : ℕ → ℕ} {lam : ℕ → ℤ} {mem : ℕ → ℕ}
    (h : LBInv m T H lam w Db K r s mem) : ∀ v < w, mem (Db + v) ≤ K := fun v hv => by
  have := h.2 v hv v [] (.nil v) (by simp)
  simp only [wlen_nil] at this
  omega

set_option maxHeartbeats 1000000 in
/-- **One round on the machine.** -/
theorem lbRound_exec {m w Tb Hb' LLb Db K L R r : ℕ} {T H LL : ℕ → ℕ} {lam : ℕ → ℤ}
    (hLay : LBLay m w Tb Hb' LLb Db K L R W) (hrR : r < R) (hKm : R * m * L ≤ K)
    (hT : ∀ a < m, T a < w) (hH : ∀ a < m, H a < w)
    (hLLz : ∀ a < m, (LL a : ℤ) = lam a + L) (hlam : ∀ a < m, -(L : ℤ) ≤ lam a)
    (hlam2 : ∀ a < m, lam a ≤ L)
    (c : Config) (hc : WordsBounded W c) (hIn : LBIn m T H LL Tb Hb' LLb c.nmem)
    (hI : LBInv m T H lam w Db K r (r * m) c.nmem)
    (h00 : c.nreg 2400 = m) (h01 : c.nreg 2401 = Tb) (h02 : c.nreg 2402 = Hb')
    (h03 : c.nreg 2403 = LLb) (h04 : c.nreg 2404 = L) (h05 : c.nreg 2405 = Db)
    (h10 : c.nreg 2410 = 1) (h13 : c.nreg 2413 = r) :
    ∃ c' t, Exec I W lbRound c c' t ∧ t ≤ 19 * m + 6 ∧
      LBInv m T H lam w Db K (r + 1) ((r + 1) * m) c'.nmem ∧ c'.nreg 2413 = r + 1 ∧
      (∀ a, a < Db ∨ Db + w ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ q, q < 2412 ∨ (2413 < q ∧ q < 2415) ∨ 2424 ≤ q → c'.nreg q = c.nreg q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hLay.wR; have := hLay.wD
  have hLL2 : ∀ a < m, LL a ≤ 2 * L := fun a ha => by
    have := hLLz a ha; have := hlam2 a ha; omega
  obtain ⟨c₁, t₁, e₁, ht₁, s12, sn, sm, sr, srm, so⟩ : ∃ c₁ t₁,
      Exec I W (block [.constN 2412 0]) c c₁ t₁ ∧ t₁ = 1 ∧ c₁.nreg 2412 = 0 ∧
      (∀ q, q ≠ 2412 → c₁.nreg q = c.nreg q) ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧
      c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    rw [upd_other _ _ _ hq]
  let J : ℕ → Config → Prop := fun i c' =>
    LBInv m T H lam w Db K r (r * m + i) c'.nmem ∧ LBArc m T H lam Db K r i c'.nmem ∧
      (∀ a, a < Db ∨ Db + w ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ q, q < 2412 ∨ (2412 < q ∧ q < 2415) ∨ 2424 ≤ q → c'.nreg q = c₁.nreg q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, hw₂, gI, gA, gm, gn, gr, grm, go⟩ :=
    forLoop_exec (P := I) (a := 2412) (bR := 2400) (body := lbBody) J (K := 17) (n := m) c₁
      e₁.wb_right s12 (by rw [sn _ (by omega)]; exact h00)
      ⟨by rw [sm]; simpa using hI, fun a ha => absurd ha (by omega), fun a _ => by rw [sm],
        fun q _ => rfl, sr, srm, so⟩
      (fun i c' hi hw ha hb ⟨gI, gA, gm, gn, gr, grm, go⟩ => by
        have k : ∀ q, q < 2412 → c'.nreg q = c.nreg q := fun q hq => by
          rw [gn q (by omega), sn q (by omega)]
        obtain ⟨c₃, t₃, e₃, ht₃, qm, q12, qn, qr, qrm, qo⟩ :=
          lbBody_exec (I := I) hLay hi hT hH hLL2 c' hw (hIn.frame hLay gm) gI.le_K
            ((k _ (by omega)).trans h01) ((k _ (by omega)).trans h02)
            ((k _ (by omega)).trans h03) ((k _ (by omega)).trans h04)
            ((k _ (by omega)).trans h05) ((k _ (by omega)).trans h10) ha
        have hKs : (r * m + i + 1) * L ≤ K := by
          have : r * m + i + 1 ≤ R * m := by
            have : (r + 1) * m ≤ R * m := Nat.mul_le_mul_right _ hrR
            rw [Nat.add_mul, one_mul] at this; omega
          have := Nat.mul_le_mul_right L this
          omega
        obtain ⟨hI', hA'⟩ := lb_step (LL := LL) hi hT hH hLLz hlam hKs gI gA
        refine ⟨c₃, t₃, e₃, ht₃, q12, by rw [qn _ (by omega), hb], ?_, ?_, fun a ha' => ?_,
          fun q hq => (qn q hq).trans (gn q hq), qr.trans gr, qrm.trans grm, qo.trans go⟩
        · rw [qm]; exact hI'
        · rw [qm]; exact hA'
        · rw [qm, lbRelax_other (by have := hH i hi; omega)]; exact gm a ha')
  have hw₂' := e₂.wb_right
  have e₃ := Exec.addN (P := I) hw₂' 2413 2413 2410
    (by rw [gn _ (by omega), gn _ (by omega), sn _ (by omega), sn _ (by omega), h13, h10]
        omega)
  refine ⟨_, _, Exec.seq e₁ (Exec.seq e₂ (Exec.block_cons e₃ (Exec.block_nil e₃.wb_right))),
    by omega, ?_, ?_, fun a ha => ?_, fun q hq => ?_, ?_, ?_, ?_⟩
  · config_simp
    have := lbInv_succ hH gI gA
    rw [show (r + 1) * m = r * m + m by ring]
    obtain ⟨W1, W2⟩ := this
    exact ⟨W1, W2⟩
  · config_simp
    rw [gn _ (by omega), gn _ (by omega), sn _ (by omega), sn _ (by omega), h13, h10]
  · config_simp; exact gm a ha
  · config_simp
    rw [upd_other _ _ _ (by omega), gn _ (by omega), sn _ (by omega)]
  · config_simp; exact gr
  · config_simp; exact grm
  · config_simp; exact go


/-! ### The start and the check -/

theorem lbInit_exec {Db w K : ℕ} (hW : Db + w ≤ W) (h1 : 1 ≤ W) (hKW : K ≤ W)
    (c : Config) (hc : WordsBounded W c) (h05 : c.nreg 2405 = Db) (h06 : c.nreg 2406 = w)
    (h08 : c.nreg 2408 = K) :
    ∃ c' t, Exec I W lbInit c c' t ∧ t ≤ 5 * w + 6 ∧
      (∀ y < w, c'.nmem (Db + y) = K) ∧ (∀ a, a < Db ∨ Db + w ≤ a → c'.nmem a = c.nmem a) ∧
      c'.nreg 2410 = 1 ∧ c'.nreg 2411 = 0 ∧ c'.nreg 2413 = 0 ∧
      (∀ r, r < 2410 ∨ 2424 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, s10, s11, s12, sn, sm, sr, srm, so⟩ : ∃ c₁ t₁,
      Exec I W (block [.constN 2410 1, .constN 2411 0, .constN 2412 0]) c c₁ t₁ ∧ t₁ = 3 ∧
      c₁.nreg 2410 = 1 ∧ c₁.nreg 2411 = 0 ∧ c₁.nreg 2412 = 0 ∧
      (∀ q, q < 2410 ∨ 2412 < q → c₁.nreg q = c.nreg q) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp (disch := omega) only [upd_other]
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ y < i, c'.nmem (Db + y) = K) ∧ (∀ a, a < Db ∨ Db + i ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ q, q ≠ 2412 → q ≠ 2414 → c'.nreg q = c₁.nreg q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, hw₂, g, gm, gn, gr, grm, go⟩ :=
    forLoop_exec (P := I) (a := 2412) (bR := 2406)
      (body := block [.addN 2414 2405 2412, .storeN 2414 2408, .addN 2412 2412 2410]) J
      (K := 3) (n := w) c₁ e₁.wb_right s12 (by rw [sn _ (by omega)]; exact h06)
      ⟨fun y hy => absurd hy (by omega), fun a _ => by rw [sm], fun q _ _ => rfl, sr, srm, so⟩
      (fun i c' hi hw ha hb ⟨g, gm, gn, gr, grm, go⟩ => by
        have e05 : c'.nreg 2405 = Db := by rw [gn _ (by omega) (by omega), sn _ (by omega)]; exact h05
        have e08 : c'.nreg 2408 = K := by rw [gn _ (by omega) (by omega), sn _ (by omega)]; exact h08
        have e10 : c'.nreg 2410 = 1 := by rw [gn _ (by omega) (by omega)]; exact s10
        exec_block
        all_goals try ((try config_simp); (try simp only [e05, e08, e10, ha]); omega)
        refine ⟨by omega, by config_simp; rw [ha, e10], by config_simp; exact hb, fun y hy => ?_,
          fun a ha' => ?_, fun q h1 h2 => ?_, gr, grm, go⟩
        all_goals config_simp
        all_goals try simp only [e05, e08, e10, ha]
        · rw [upd_apply]; split_ifs with h
          · rfl
          · exact g y (by omega)
        · rw [upd_other _ _ _ (by omega)]; exact gm a (by omega)
        · rw [upd_other _ _ _ h1, upd_other _ _ _ h2]; exact gn q h1 h2)
  have hw₂' := e₂.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, s13, sn₃, sm₃, sr₃, srm₃, so₃⟩ : ∃ c₃ t₃,
      Exec I W (block [.constN 2413 0]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 2413 = 0 ∧
      (∀ q, q ≠ 2413 → c₃.nreg q = c₂.nreg q) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    rw [upd_other _ _ _ hq]
  refine ⟨c₃, t₁ + (t₂ + t₃), Exec.seq e₁ (Exec.seq e₂ e₃), by omega, fun y hy => ?_,
    fun a ha => ?_, ?_, ?_, s13, fun q hq => ?_, ?_, ?_, ?_⟩
  · rw [sm₃]; exact g y hy
  · rw [sm₃]; exact gm a ha
  · rw [sn₃ _ (by omega), gn _ (by omega) (by omega)]; exact s10
  · rw [sn₃ _ (by omega), gn _ (by omega) (by omega)]; exact s11
  · rw [sn₃ _ (by omega), gn _ (by omega) (by omega), sn _ (by omega)]
  · rw [sr₃, gr]
  · rw [srm₃, grm]
  · rw [so₃, go]

/-- An arc relaxable in the memory `mem`. -/
abbrev LBViol (T H LL : ℕ → ℕ) (Db L : ℕ) (mem : ℕ → ℕ) (j : ℕ) : Prop :=
  mem (Db + T j) + LL j < mem (Db + H j) + L

theorem lbCkBody_exec {m w Tb Hb' LLb Db K L R i : ℕ} {T H LL : ℕ → ℕ}
    (hLay : LBLay m w Tb Hb' LLb Db K L R W) (hi : i < m)
    (hT : ∀ a < m, T a < w) (hH : ∀ a < m, H a < w) (hLL : ∀ a < m, LL a ≤ 2 * L)
    (c : Config) (hc : WordsBounded W c) (hIn : LBIn m T H LL Tb Hb' LLb c.nmem)
    (hK : ∀ v < w, c.nmem (Db + v) ≤ K)
    (h01 : c.nreg 2401 = Tb) (h02 : c.nreg 2402 = Hb') (h03 : c.nreg 2403 = LLb)
    (h04 : c.nreg 2404 = L) (h05 : c.nreg 2405 = Db) (h10 : c.nreg 2410 = 1)
    (h12 : c.nreg 2412 = i) :
    ∃ c' t, Exec I W lbCkBody c c' t ∧ t ≤ 16 ∧ c'.nmem = c.nmem ∧
      c'.nreg 2412 = i + 1 ∧
      c'.nreg 2424 = (if LBViol T H LL Db L c.nmem i then 1 else c.nreg 2424) ∧
      (∀ q, q < 2412 ∨ (2412 < q ∧ q < 2415) ∨ 2424 < q → c'.nreg q = c.nreg q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hLay.wT; have := hLay.wH; have := hLay.wL; have := hLay.wD; have := hLay.wV
  have := hLay.one
  have ti := hT i hi; have hi' := hH i hi; have li := hLL i hi
  have et := hIn.t i hi; have eh := hIn.h i hi; have el := hIn.l i hi
  have kt := hK _ ti; have kh := hK _ hi'
  obtain ⟨c₂, t₂, e₂, ht₂, p20, p21, p22, pn, pm, pr, prm, po⟩ :=
    lbLoad_exec (I := I) c hc h01 h02 h03 h04 h05 h12 (by omega) (by omega) (by omega)
      (by rw [et]; omega) (by rw [eh]; omega) (by rw [et, el]; omega) (by rw [eh]; omega)
  have hw₂ := e₂.wb_right
  have hv : LBViol T H LL Db L c.nmem i ↔ c₂.nreg 2421 < c₂.nreg 2422 := by
    rw [p21, p22, et, eh, el]
  obtain ⟨c₃, t₃, e₃, ht₃, q24, qn, qm, qr, qrm, qo⟩ : ∃ c₃ t₃,
      Exec I W (.ifLtN 2421 2422 (.instr (.constN 2424 1)) .skip) c₂ c₃ t₃ ∧ t₃ ≤ 2 ∧
      c₃.nreg 2424 = (if LBViol T H LL Db L c.nmem i then 1 else c₂.nreg 2424) ∧
      (∀ q, q ≠ 2424 → c₃.nreg q = c₂.nreg q) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    by_cases h : c₂.nreg 2421 < c₂.nreg 2422
    · have e := Exec.constN (P := I) hw₂ 2424 1 (by omega)
      refine ⟨_, _, Exec.ifLtN_true h e, by omega, ?_, fun q hq => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [if_pos (hv.2 h)]
      · config_simp; rw [upd_other _ _ _ hq]
    · refine ⟨_, _, Exec.ifLtN_false h (Exec.skip hw₂), by omega, ?_, fun q _ => rfl, rfl, rfl,
        rfl, rfl⟩
      rw [if_neg (fun h' => h (hv.1 h'))]
  have hw₃ := e₃.wb_right
  have e₄ := Exec.addN (P := I) hw₃ 2412 2412 2410
    (by rw [qn _ (by omega), qn _ (by omega), pn _ (by omega), pn _ (by omega), h10, h12]; omega)
  refine ⟨_, _, Exec.seq e₂ (Exec.seq e₃ (Exec.block_cons e₄ (Exec.block_nil e₄.wb_right))),
    by omega, ?_, ?_, ?_, fun q hq => ?_, ?_, ?_, ?_⟩
  · config_simp; rw [qm, pm]
  · config_simp
    rw [qn _ (by omega), qn _ (by omega), pn _ (by omega), pn _ (by omega), h10, h12]
  · config_simp
    rw [q24, pn _ (by omega)]
  · config_simp
    rw [upd_other _ _ _ (by omega), qn _ (by omega), pn _ (by omega)]
  · config_simp; rw [qr, pr]
  · config_simp; rw [qrm, prm]
  · config_simp; rw [qo, po]


set_option maxHeartbeats 1000000 in
theorem lbCheck_exec {m w Tb Hb' LLb Db K L R : ℕ} {T H LL : ℕ → ℕ}
    (hLay : LBLay m w Tb Hb' LLb Db K L R W)
    (hT : ∀ a < m, T a < w) (hH : ∀ a < m, H a < w) (hLL : ∀ a < m, LL a ≤ 2 * L)
    (c : Config) (hc : WordsBounded W c) (hIn : LBIn m T H LL Tb Hb' LLb c.nmem)
    (hK : ∀ v < w, c.nmem (Db + v) ≤ K) (h00 : c.nreg 2400 = m)
    (h01 : c.nreg 2401 = Tb) (h02 : c.nreg 2402 = Hb') (h03 : c.nreg 2403 = LLb)
    (h04 : c.nreg 2404 = L) (h05 : c.nreg 2405 = Db) (h10 : c.nreg 2410 = 1) :
    ∃ c' t, Exec I W lbCheck c c' t ∧ t ≤ 18 * m + 4 ∧ c'.nmem = c.nmem ∧
      ((c'.nreg 2424 = 0 ∧ ∀ j < m, ¬ LBViol T H LL Db L c.nmem j) ∨
        (c'.nreg 2424 = 1 ∧ ∃ j < m, LBViol T H LL Db L c.nmem j)) ∧
      (∀ q, q < 2412 ∨ (2412 < q ∧ q < 2415) ∨ 2424 < q → c'.nreg q = c.nreg q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hLay.one
  obtain ⟨c₁, t₁, e₁, ht₁, s24, s12, sn, sm, sr, srm, so⟩ : ∃ c₁ t₁,
      Exec I W (block [.constN 2424 0, .constN 2412 0]) c c₁ t₁ ∧ t₁ = 2 ∧
      c₁.nreg 2424 = 0 ∧ c₁.nreg 2412 = 0 ∧
      (∀ q, q ≠ 2412 → q ≠ 2424 → c₁.nreg q = c.nreg q) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, fun q h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    rw [upd_other _ _ _ h1, upd_other _ _ _ h2]
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nmem = c.nmem ∧
      ((c'.nreg 2424 = 0 ∧ ∀ j < i, ¬ LBViol T H LL Db L c.nmem j) ∨
        (c'.nreg 2424 = 1 ∧ ∃ j < i, LBViol T H LL Db L c.nmem j)) ∧
      (∀ q, q < 2412 ∨ (2412 < q ∧ q < 2415) ∨ 2424 < q → c'.nreg q = c₁.nreg q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, hw₂, gm, gf, gn, gr, grm, go⟩ :=
    forLoop_exec (P := I) (a := 2412) (bR := 2400) (body := lbCkBody) J (K := 16) (n := m) c₁
      e₁.wb_right s12 (by rw [sn _ (by omega) (by omega)]; exact h00)
      ⟨sm, Or.inl ⟨s24, fun j hj => absurd hj (by omega)⟩, fun q _ => rfl, sr, srm, so⟩
      (fun i c' hi hw ha hb ⟨gm, gf, gn, gr, grm, go⟩ => by
        have k : ∀ q, q < 2412 → c'.nreg q = c.nreg q := fun q hq => by
          rw [gn q (by omega), sn q (by omega) (by omega)]
        obtain ⟨c₃, t₃, e₃, ht₃, qm, q12, q24, qn, qr, qrm, qo⟩ :=
          lbCkBody_exec (I := I) hLay hi hT hH hLL c' hw (by rw [gm]; exact hIn)
            (by rw [gm]; exact hK)
            ((k _ (by omega)).trans h01) ((k _ (by omega)).trans h02)
            ((k _ (by omega)).trans h03) ((k _ (by omega)).trans h04)
            ((k _ (by omega)).trans h05) ((k _ (by omega)).trans h10) ha
        rw [gm] at q24
        refine ⟨c₃, t₃, e₃, ht₃, q12, by rw [qn _ (by omega), hb], qm.trans gm, ?_,
          fun q hq => (qn q hq).trans (gn q hq), qr.trans gr, qrm.trans grm, qo.trans go⟩
        by_cases hv : LBViol T H LL Db L c.nmem i
        · rw [if_pos hv] at q24
          exact Or.inr ⟨q24, i, by omega, hv⟩
        · rw [if_neg hv] at q24
          rcases gf with ⟨h0, hn⟩ | ⟨h1, j, hj, hvj⟩
          · exact Or.inl ⟨q24.trans h0, fun j hj => by
              rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
              · exact hn j hj
              · exact hv⟩
          · exact Or.inr ⟨q24.trans h1, j, by omega, hvj⟩)
  refine ⟨c₂, t₁ + t₂, Exec.seq e₁ e₂, by omega, gm, gf, fun q hq => ?_, gr, grm, go⟩
  rw [gn q hq, sn q (by omega) (by omega)]

/-- The cost of `lbProg`. -/
def lbCost (m w R : ℕ) : ℕ := 5 * w + 8 + R * (19 * m + 8) + 18 * m + 4

set_option maxHeartbeats 1000000 in
/-- **Bellman–Ford for the leaves on the machine** (see the module docstring). -/
theorem lbProg_exec {m w Tb Hb' LLb Db K L R : ℕ} {T H LL : ℕ → ℕ} {lam : ℕ → ℤ}
    (hLay : LBLay m w Tb Hb' LLb Db K L R W) (hKm : R * m * L ≤ K)
    (hT : ∀ a < m, T a < w) (hH : ∀ a < m, H a < w)
    (hLLz : ∀ a < m, (LL a : ℤ) = lam a + L) (hlam : ∀ a < m, -(L : ℤ) ≤ lam a)
    (hlam2 : ∀ a < m, lam a ≤ L)
    (c : Config) (hc : WordsBounded W c) (hIn : LBIn m T H LL Tb Hb' LLb c.nmem)
    (h00 : c.nreg 2400 = m) (h01 : c.nreg 2401 = Tb) (h02 : c.nreg 2402 = Hb')
    (h03 : c.nreg 2403 = LLb) (h04 : c.nreg 2404 = L) (h05 : c.nreg 2405 = Db)
    (h06 : c.nreg 2406 = w) (h07 : c.nreg 2407 = R) (h08 : c.nreg 2408 = K) :
    ∃ c' t, Exec I W lbProg c c' t ∧ t ≤ lbCost m w R ∧
      LBInv m T H lam w Db K R (R * m) c'.nmem ∧
      ((c'.nreg 2424 = 0 ∧ ∀ j < m, ¬ LBViol T H LL Db L c'.nmem j) ∨
        (c'.nreg 2424 = 1 ∧ ∃ j < m, LBViol T H LL Db L c'.nmem j)) ∧
      (∀ a, a < Db ∨ Db + w ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ q, q < 2410 ∨ 2424 < q → c'.nreg q = c.nreg q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hLay.one; have := hLay.wD; have := hLay.wV; have := hLay.wR
  have hLL2 : ∀ a < m, LL a ≤ 2 * L := fun a ha => by
    have := hLLz a ha; have := hlam2 a ha; omega
  obtain ⟨c₁, t₁, e₁, ht₁, hD₁, hm₁, a10, a11, a13, an₁, ar₁, arm₁, ao₁⟩ :=
    lbInit_exec (I := I) hLay.wD hLay.one (by omega) c hc h05 h06 h08
  have hI₀ : LBInv m T H lam w Db K 0 (0 * m) c₁.nmem := by
    refine ⟨fun v hv => ⟨v, [], .nil v, by simp, by rw [hD₁ v hv]; simp⟩,
      fun v hv x l hl hlen => ?_⟩
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [hD₁ v hv]; simp
  let J : ℕ → Config → Prop := fun r c' =>
    LBInv m T H lam w Db K r (r * m) c'.nmem ∧
      (∀ a, a < Db ∨ Db + w ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ q, q < 2412 ∨ (2413 < q ∧ q < 2415) ∨ 2424 ≤ q → c'.nreg q = c₁.nreg q) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, hw₂, gI, gm, gn, gr, grm, go⟩ :=
    forLoop_exec (P := I) (a := 2413) (bR := 2407) (body := lbRound) J (K := 19 * m + 6)
      (n := R) c₁ e₁.wb_right a13 (by rw [an₁ _ (by omega), h07])
      ⟨hI₀, hm₁, fun _ _ => rfl, ar₁, arm₁, ao₁⟩
      (fun r c₃ hr hw ha hb ⟨gI, gm, gn, gr, grm, go⟩ => by
        have k : ∀ q, q < 2410 → c₃.nreg q = c.nreg q := fun q hq => by
          rw [gn q (by omega), an₁ q (by omega)]
        obtain ⟨c₄, t₄, e₄, ht₄, hI₄, h13, hm₄, hn₄, hr₄, hrm₄, ho₄⟩ :=
          lbRound_exec (I := I) hLay hr hKm hT hH hLLz hlam hlam2 c₃ hw (hIn.frame hLay gm) gI
            ((k _ (by omega)).trans h00) ((k _ (by omega)).trans h01)
            ((k _ (by omega)).trans h02) ((k _ (by omega)).trans h03)
            ((k _ (by omega)).trans h04) ((k _ (by omega)).trans h05)
            ((gn _ (by omega)).trans a10) ha
        refine ⟨c₄, t₄, e₄, ht₄, h13, by rw [hn₄ _ (by omega), hb], hI₄,
          fun a ha' => (hm₄ a ha').trans (gm a ha'), fun q hq => (hn₄ q (by omega)).trans
            (gn q hq), hr₄.trans gr, hrm₄.trans grm, ho₄.trans go⟩)
  have k : ∀ q, q < 2410 → c₂.nreg q = c.nreg q := fun q hq => by
    rw [gn q (by omega), an₁ q (by omega)]
  obtain ⟨c₅, t₅, e₅, ht₅, hm₅, hf₅, hn₅, hr₅, hrm₅, ho₅⟩ :=
    lbCheck_exec (I := I) hLay hT hH hLL2 c₂ hw₂ (hIn.frame hLay gm) gI.le_K
      ((k _ (by omega)).trans h00) ((k _ (by omega)).trans h01)
      ((k _ (by omega)).trans h02) ((k _ (by omega)).trans h03)
      ((k _ (by omega)).trans h04) ((k _ (by omega)).trans h05)
      ((gn _ (by omega)).trans a10)
  refine ⟨c₅, t₁ + (t₂ + t₅), Exec.seq e₁ (Exec.seq e₂ e₅), ?_, by rw [hm₅]; exact gI,
    by rw [hm₅]; exact hf₅, fun a ha => by rw [hm₅]; exact gm a ha,
    fun q hq => by rw [hn₅ q (by omega), gn q (by omega), an₁ q (by omega)], ?_, ?_, ?_⟩
  · unfold lbCost
    have : (19 * m + 6 + 2) * R = R * (19 * m + 8) := by ring
    omega
  · rw [hr₅, gr]
  · rw [hrm₅, grm]
  · rw [ho₅, go]

end NegSSSP

end PlanarFlow
