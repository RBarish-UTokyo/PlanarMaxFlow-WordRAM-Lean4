module

public import PlanarFlow.BKMNW.ExistOracleD
public import PlanarFlow.BKMNW.TwoGroupsProg

/-!
# The darts attached to a certificate on the machine

`PlanarFlow.BKMNW.pcNf M Q P Hs` (the darts of the piece `P` but those inside a hole that no
dart of the piece map of the core touches) computed by a natural-word program in two linear
scans with branch-free arithmetic (`x / x` is the test `x ≠ 0`):

1. for every dart of the piece map of the core (`d ∈ P`, ends off `Q`, not inside a hole), mark
   the class of its tail: `MK[TC[j]] := 1`;
2. `OUT[j] := 1` iff `d ∈ P` and (`d` not inside a hole, or the class of its tail is marked).

Layout (an enumeration `e j`, `j < n`, of darts, the vertex classes of the holes numbered by
`cid`, `cid u = cid v ↔ HRel Hs u v`): `PF[j]` (`0 <` iff in `P`), `TQ[j]`, `HQ[j]` (ends in `Q`),
`TC[j] = cid (tail)`, `HC[j] = cid (head)`, `TH[j]` (`0 <` iff the tail is in a hole), the table
`MK[t]`, `t < nc` (zero at the start), the output `OUT[j]`.
Registers `4200 = n`, `4201 … 4208` the bases `PF TQ HQ TC HC TH MK OUT`; written `4209 = 1`,
`4210 = 0`, index `4211`, scratch `4212 … 4221`.

* `nzF`, `innerF`, `c1F`, `orF`, `outF` and their meaning;
* `pnLoad`, `pnBody1`, `pnBody2`, **`pnProg`**, **`pnProg_exec`** (within `69 n + 8` steps);
* **`pnProg_pcNf`**: for the arrays of an enumeration covering `P`, `OUT[j] = 1 ↔ e j ∈ pcNf M Q P Hs`
  and `OUT[j] ≤ 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### Branch-free tests -/

/-- `x ≠ 0` as a word. -/
def nzF (x : ℕ) : ℕ := x / x

lemma nzF_eq (x : ℕ) : nzF x = if x = 0 then 0 else 1 := by
  unfold nzF; split_ifs with h
  · simp [h]
  · exact Nat.div_self (Nat.pos_of_ne_zero h)

lemma nzF_le (x : ℕ) : nzF x ≤ 1 := by rw [nzF_eq]; split_ifs <;> omega

/-- Inside a hole: the tail in a hole (`th ≠ 0`) and the same class at both ends. -/
def innerF (th tc hc : ℕ) : ℕ := nzF th * (1 - nzF (tc - hc + (hc - tc)))

lemma innerF_eq (th tc hc : ℕ) : innerF th tc hc = if 0 < th ∧ tc = hc then 1 else 0 := by
  unfold innerF; rw [nzF_eq, nzF_eq]
  by_cases h1 : th = 0
  · simp [h1]
  · by_cases h2 : tc = hc
    · subst h2; simp [h1, Nat.pos_of_ne_zero h1]
    · have : tc - hc + (hc - tc) ≠ 0 := by omega
      rw [tgIteF this]; simp [h1, h2]

/-- A dart of the piece map of the core: in `P`, ends off `Q`, not inside a hole. -/
def c1F (pf tq hq th tc hc : ℕ) : ℕ :=
  (1 - innerF th tc hc) * nzF pf * (1 - nzF tq) * (1 - nzF hq)

lemma c1F_eq (pf tq hq th tc hc : ℕ) : c1F pf tq hq th tc hc =
    if 0 < pf ∧ tq = 0 ∧ hq = 0 ∧ ¬ (0 < th ∧ tc = hc) then 1 else 0 := by
  unfold c1F; rw [innerF_eq, nzF_eq, nzF_eq, nzF_eq]
  by_cases h1 : 0 < th ∧ tc = hc <;> by_cases h2 : pf = 0 <;> by_cases h3 : tq = 0 <;>
    by_cases h4 : hq = 0 <;> simp [h1, h2, h3, h4] <;> omega

lemma c1F_le (pf tq hq th tc hc : ℕ) : c1F pf tq hq th tc hc ≤ 1 := by
  rw [c1F_eq]; split_ifs <;> omega

/-- The or of two flags. -/
def orF (a b : ℕ) : ℕ := a + b - a * b

lemma orF_eq {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : orF a b = if a = 1 ∨ b = 1 then 1 else 0 := by
  unfold orF
  interval_cases a <;> interval_cases b <;> simp

/-- The output flag: in `P` and (not inside a hole, or the class marked). -/
def outF (pf th tc hc mk : ℕ) : ℕ := (1 - innerF th tc hc * (1 - nzF mk)) * nzF pf

lemma outF_eq (pf th tc hc mk : ℕ) : outF pf th tc hc mk =
    if 0 < pf ∧ (¬ (0 < th ∧ tc = hc) ∨ 0 < mk) then 1 else 0 := by
  unfold outF; rw [innerF_eq, nzF_eq, nzF_eq]
  by_cases h1 : 0 < th ∧ tc = hc <;> by_cases h2 : pf = 0 <;> by_cases h3 : mk = 0 <;>
    simp [h1, h2, h3] <;> omega

/-! ### The programs -/

/-- The loads at the dart `j = r4211`: `r4212 = PF`, `r4213 = TQ`, `r4214 = HQ`, `r4215 = TC`,
`r4216 = HC`, `r4217 = TH`, `r4221 = MKb + TC`, `r4218 = MK[TC]`; then `r4219 := innerF`. -/
def pnLoad : List Instr :=
  [.addN 4212 4201 4211, .loadN 4212 4212, .addN 4213 4202 4211, .loadN 4213 4213,
    .addN 4214 4203 4211, .loadN 4214 4214, .addN 4215 4204 4211, .loadN 4215 4215,
    .addN 4216 4205 4211, .loadN 4216 4216, .addN 4217 4206 4211, .loadN 4217 4217,
    .addN 4221 4207 4215, .loadN 4218 4221,
    .divN 4212 4212 4212, .divN 4217 4217 4217,
    .subN 4219 4215 4216, .subN 4220 4216 4215, .addN 4219 4219 4220, .divN 4219 4219 4219,
    .subN 4219 4209 4219, .mulN 4219 4217 4219]

/-- Pass 1 at a dart: `MK[TC] := MK[TC] or c1F`. -/
def pnBody1 : Stmt :=
  block (pnLoad ++ [.divN 4213 4213 4213, .divN 4214 4214 4214, .subN 4219 4209 4219,
    .mulN 4219 4219 4212, .subN 4213 4209 4213, .subN 4214 4209 4214, .mulN 4219 4219 4213,
    .mulN 4219 4219 4214, .mulN 4220 4218 4219, .addN 4218 4218 4219, .subN 4218 4218 4220,
    .storeN 4221 4218, .addN 4211 4211 4209])

/-- Pass 2 at a dart: `OUT[j] := outF`. -/
def pnBody2 : Stmt :=
  block (pnLoad ++ [.divN 4218 4218 4218, .subN 4218 4209 4218, .mulN 4219 4219 4218,
    .subN 4219 4209 4219, .mulN 4219 4219 4212, .addN 4220 4208 4211, .storeN 4220 4219,
    .addN 4211 4211 4209])

/-- **The attached darts on the machine.** -/
def pnProg : Stmt :=
  .seq (block [.constN 4209 1, .constN 4210 0, .constN 4211 0])
    (.seq (.whileLtN 4211 4200 pnBody1)
      (.seq (block [.constN 4211 0]) (.whileLtN 4211 4200 pnBody2)))

section Exec

variable {P : Input} {W : ℕ}

lemma pn_dsl (x : ℕ) : x / x ≤ 1 := by
  have := nzF_le x; unfold nzF at this; exact this

lemma pn_m1 {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  interval_cases a <;> interval_cases b <;> simp

/-- Bounds `≤ 1` of the flags computed by the bodies. -/
macro "pn_a" : tactic => `(tactic| first | assumption | exact Nat.sub_le _ _)
macro "pn_step1" : tactic => `(tactic| first | pn_a | exact pn_dsl _ | refine pn_m1 ?_ ?_)
macro "pn_le1" : tactic => `(tactic| (repeat' pn_step1))

/-- The side conditions of the bodies: sums of addresses, products and sums of flags. -/
macro "pn_side" : tactic => `(tactic| first | omega |
  exact le_trans (pn_m1 (by pn_le1) (by pn_le1)) (by omega) |
  exact le_trans (Nat.add_le_add (by pn_le1) (by pn_le1)) (by omega))

/-- The frame of a body: the registers outside `4211 … 4221` are not written. -/
macro "pn_frame" x:ident : tactic => `(tactic| (
  have e11 : $x ≠ 4211 := by omega
  have e12 : $x ≠ 4212 := by omega
  have e13 : $x ≠ 4213 := by omega
  have e14 : $x ≠ 4214 := by omega
  have e15 : $x ≠ 4215 := by omega
  have e16 : $x ≠ 4216 := by omega
  have e17 : $x ≠ 4217 := by omega
  have e18 : $x ≠ 4218 := by omega
  have e19 : $x ≠ 4219 := by omega
  have e20 : $x ≠ 4220 := by omega
  have e21 : $x ≠ 4221 := by omega
  simp only [Config.nreg_mk, upd_other _ _ _ e11, upd_other _ _ _ e12, upd_other _ _ _ e13,
    upd_other _ _ _ e14, upd_other _ _ _ e15, upd_other _ _ _ e16, upd_other _ _ _ e17,
    upd_other _ _ _ e18, upd_other _ _ _ e19, upd_other _ _ _ e20, upd_other _ _ _ e21]))

/-- The registers of the bases. -/
structure PnRegs (c : Config) (PFb TQb HQb TCb HCb THb MKb OUTb : ℕ) : Prop where
  r1 : c.nreg 4201 = PFb
  r2 : c.nreg 4202 = TQb
  r3 : c.nreg 4203 = HQb
  r4 : c.nreg 4204 = TCb
  r5 : c.nreg 4205 = HCb
  r6 : c.nreg 4206 = THb
  r7 : c.nreg 4207 = MKb
  r8 : c.nreg 4208 = OUTb
  r9 : c.nreg 4209 = 1

lemma PnRegs.congr {c c' : Config} {PFb TQb HQb TCb HCb THb MKb OUTb : ℕ}
    (h : PnRegs c PFb TQb HQb TCb HCb THb MKb OUTb)
    (hc : ∀ x, (x < 4211 ∨ 4221 < x) → c'.nreg x = c.nreg x) :
    PnRegs c' PFb TQb HQb TCb HCb THb MKb OUTb :=
  ⟨by rw [hc _ (by omega), h.r1], by rw [hc _ (by omega), h.r2], by rw [hc _ (by omega), h.r3],
    by rw [hc _ (by omega), h.r4], by rw [hc _ (by omega), h.r5], by rw [hc _ (by omega), h.r6],
    by rw [hc _ (by omega), h.r7], by rw [hc _ (by omega), h.r8], by rw [hc _ (by omega), h.r9]⟩

/-- **Pass 1 at the dart `j`.** -/
theorem pnBody1_exec (c : Config) (hc : WordsBounded W c) {PFb TQb HQb TCb HCb THb MKb OUTb j : ℕ}
    (hR : PnRegs c PFb TQb HQb TCb HCb THb MKb OUTb) (r11 : c.nreg 4211 = j)
    (w1 : THb + j + 1 ≤ W) (w2 : MKb + c.nmem (TCb + j) ≤ W) (w3 : 2 ≤ W)
    (hPT : PFb ≤ THb ∧ TQb ≤ THb ∧ HQb ≤ THb ∧ TCb ≤ THb ∧ HCb ≤ THb)
    (hmk : c.nmem (MKb + c.nmem (TCb + j)) ≤ 1) :
    ∃ c' k, Exec P W pnBody1 c c' k ∧ k = 35 ∧ c'.nreg 4211 = j + 1 ∧
      c'.nmem = upd c.nmem (MKb + c.nmem (TCb + j)) (orF (c.nmem (MKb + c.nmem (TCb + j)))
        (c1F (c.nmem (PFb + j)) (c.nmem (TQb + j)) (c.nmem (HQb + j)) (c.nmem (THb + j))
          (c.nmem (TCb + j)) (c.nmem (HCb + j)))) ∧
      (∀ x, (x < 4211 ∨ 4221 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hR
  have b5 := hc.2 (TCb + j)
  have b6 := hc.2 (HCb + j)
  simp only [pnBody1, pnLoad, List.cons_append, List.nil_append]
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6, r7, r9, r11]; pn_side)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r9, r11]
  · config_simp; simp only [r1, r2, r3, r4, r5, r6, r7, r9, r11, orF, c1F, innerF, nzF]
  · pn_frame x

/-- **Pass 2 at the dart `j`.** -/
theorem pnBody2_exec (c : Config) (hc : WordsBounded W c) {PFb TQb HQb TCb HCb THb MKb OUTb j : ℕ}
    (hR : PnRegs c PFb TQb HQb TCb HCb THb MKb OUTb) (r11 : c.nreg 4211 = j)
    (w1 : THb + j + 1 ≤ W) (w2 : MKb + c.nmem (TCb + j) ≤ W) (w3 : OUTb + j + 1 ≤ W)
    (hPT : PFb ≤ THb ∧ TQb ≤ THb ∧ HQb ≤ THb ∧ TCb ≤ THb ∧ HCb ≤ THb) :
    ∃ c' k, Exec P W pnBody2 c c' k ∧ k = 30 ∧ c'.nreg 4211 = j + 1 ∧
      c'.nmem = upd c.nmem (OUTb + j) (outF (c.nmem (PFb + j)) (c.nmem (THb + j))
          (c.nmem (TCb + j)) (c.nmem (HCb + j)) (c.nmem (MKb + c.nmem (TCb + j)))) ∧
      (∀ x, (x < 4211 ∨ 4221 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩ := hR
  have b5 := hc.2 (TCb + j)
  have b6 := hc.2 (HCb + j)
  simp only [pnBody2, pnLoad, List.cons_append, List.nil_append]
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r6, r7, r8, r9, r11]; pn_side)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r9, r11]
  · config_simp; simp only [r1, r2, r3, r4, r5, r6, r7, r8, r9, r11, outF, innerF, nzF]
  · pn_frame x

/-- The layout of the arrays: `PF | TQ | HQ | TC | HC | TH (+1) | MK | OUT (+1)` below `W`. -/
structure PnLay (n nc PFb TQb HQb TCb HCb THb MKb OUTb W : ℕ) : Prop where
  l1 : PFb + n ≤ TQb
  l2 : TQb + n ≤ HQb
  l3 : HQb + n ≤ TCb
  l4 : TCb + n ≤ HCb
  l5 : HCb + n ≤ THb
  l6 : THb + n + 1 ≤ MKb
  l7 : MKb + nc ≤ OUTb
  l8 : OUTb + n + 1 ≤ W
  l9 : 2 ≤ W

/-- The marked classes after the darts `[0, i)`. -/
def pnMark (m : ℕ → ℕ) (PFb TQb HQb TCb HCb THb i t : ℕ) : ℕ :=
  if ∃ j < i, c1F (m (PFb + j)) (m (TQb + j)) (m (HQb + j)) (m (THb + j)) (m (TCb + j))
    (m (HCb + j)) = 1 ∧ m (TCb + j) = t then 1 else 0

lemma pnMark_le (m : ℕ → ℕ) (PFb TQb HQb TCb HCb THb i t : ℕ) :
    pnMark m PFb TQb HQb TCb HCb THb i t ≤ 1 := by
  unfold pnMark; split_ifs <;> omega

lemma pnMark_succ (m : ℕ → ℕ) (PFb TQb HQb TCb HCb THb i t : ℕ) :
    pnMark m PFb TQb HQb TCb HCb THb (i + 1) t =
      if pnMark m PFb TQb HQb TCb HCb THb i t = 1 ∨
        (c1F (m (PFb + i)) (m (TQb + i)) (m (HQb + i)) (m (THb + i)) (m (TCb + i))
          (m (HCb + i)) = 1 ∧ m (TCb + i) = t) then 1 else 0 := by
  unfold pnMark
  by_cases h : ∃ j < i, c1F (m (PFb + j)) (m (TQb + j)) (m (HQb + j)) (m (THb + j))
      (m (TCb + j)) (m (HCb + j)) = 1 ∧ m (TCb + j) = t
  · have h1 : ∃ j < i + 1, c1F (m (PFb + j)) (m (TQb + j)) (m (HQb + j)) (m (THb + j))
        (m (TCb + j)) (m (HCb + j)) = 1 ∧ m (TCb + j) = t := by
      obtain ⟨j, hj, hj'⟩ := h; exact ⟨j, by omega, hj'⟩
    rw [tgIteT h1, tgIteT h]; simp
  · rw [tgIteF h]
    simp only [zero_ne_one, false_or]
    congr 1
    apply propext
    constructor
    · rintro ⟨j, hj, hj'⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact absurd ⟨j, hj, hj'⟩ h
      · exact hj'
    · intro h'; exact ⟨i, by omega, h'⟩

/-- **The attached darts on the machine**: under the layout `PnLay`, the classes `TC[j] < nc`
and the table `MK` zero, within `69 n + 8` steps, `OUT[j] = outF PF[j] TH[j] TC[j] HC[j]
(pnMark … n TC[j])` for every `j < n`; the memory outside `MK` and `OUT`, the registers outside
`4209 … 4221`, the reals and the output kept. -/
theorem pnProg_exec (c : Config) (hc : WordsBounded W c)
    {n nc PFb TQb HQb TCb HCb THb MKb OUTb : ℕ}
    (hL : PnLay n nc PFb TQb HQb TCb HCb THb MKb OUTb W) (r0 : c.nreg 4200 = n)
    (r1 : c.nreg 4201 = PFb) (r2 : c.nreg 4202 = TQb) (r3 : c.nreg 4203 = HQb)
    (r4 : c.nreg 4204 = TCb) (r5 : c.nreg 4205 = HCb) (r6 : c.nreg 4206 = THb)
    (r7 : c.nreg 4207 = MKb) (r8 : c.nreg 4208 = OUTb)
    (hTC : ∀ j < n, c.nmem (TCb + j) < nc) (hMK : ∀ t < nc, c.nmem (MKb + t) = 0) :
    ∃ c' k, Exec P W pnProg c c' k ∧ k ≤ 69 * n + 8 ∧
      (∀ j < n, c'.nmem (OUTb + j) = outF (c.nmem (PFb + j)) (c.nmem (THb + j))
        (c.nmem (TCb + j)) (c.nmem (HCb + j))
        (pnMark c.nmem PFb TQb HQb TCb HCb THb n (c.nmem (TCb + j)))) ∧
      (∀ a, (a < MKb ∨ OUTb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4209 ∨ 4221 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := hL
  unfold pnProg
  obtain ⟨c₁, k₁, e₁, hk₁, g9, g11, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4209 1, .constN 4210 0, .constN 4211 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 4209 = 1 ∧ c₁.nreg 4211 = 0 ∧
      (∀ x, (x < 4209 ∨ 4211 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have hR₁ : PnRegs c₁ PFb TQb HQb TCb HCb THb MKb OUTb :=
    ⟨by rw [gn₁ _ (by omega), r1], by rw [gn₁ _ (by omega), r2], by rw [gn₁ _ (by omega), r3],
      by rw [gn₁ _ (by omega), r4], by rw [gn₁ _ (by omega), r5], by rw [gn₁ _ (by omega), r6],
      by rw [gn₁ _ (by omega), r7], by rw [gn₁ _ (by omega), r8], g9⟩
  have q0 : c₁.nreg 4200 = n := by rw [gn₁ _ (by omega), r0]
  set m := c.nmem with hm
  have hPT : PFb ≤ THb ∧ TQb ≤ THb ∧ HQb ≤ THb ∧ TCb ≤ THb ∧ HCb ≤ THb := by omega
  -- pass 1
  let J1 : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4211 ∨ 4221 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ a, (a < MKb ∨ MKb + nc ≤ a) → c'.nmem a = m a) ∧
    (∀ t < nc, c'.nmem (MKb + t) = pnMark m PFb TQb HQb TCb HCb THb i t) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h11₂, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P) (a := 4211)
    (b := 4200) (body := pnBody1) J1 (B := 35) c₁ hw₁ g11 q0 (Nat.zero_le n)
    ⟨fun _ _ => rfl, fun a _ => by rw [gm₁], fun t ht => by
      rw [gm₁, hMK t ht]; unfold pnMark; rw [tgIteF]; push Not; intro j hj; omega, rfl, rfl,
      rfl⟩
    (fun i c' hlo hhi hw h11 h0 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have hR := hR₁.congr j1
      have hti := hTC i hhi
      have e1 : c'.nmem (PFb + i) = m (PFb + i) := j2 _ (Or.inl (by omega))
      have e2 : c'.nmem (TQb + i) = m (TQb + i) := j2 _ (Or.inl (by omega))
      have e3 : c'.nmem (HQb + i) = m (HQb + i) := j2 _ (Or.inl (by omega))
      have e4 : c'.nmem (TCb + i) = m (TCb + i) := j2 _ (Or.inl (by omega))
      have e5 : c'.nmem (HCb + i) = m (HCb + i) := j2 _ (Or.inl (by omega))
      have e6 : c'.nmem (THb + i) = m (THb + i) := j2 _ (Or.inl (by omega))
      have hmk : c'.nmem (MKb + c'.nmem (TCb + i)) ≤ 1 := by
        rw [e4, j3 _ hti]; unfold pnMark; split_ifs <;> omega
      obtain ⟨c'', t, ex, ht, h11', hm', hfr, hr', hrm', ho'⟩ := pnBody1_exec (P := P) c' hw hR
        h11 (by omega) (by rw [e4]; omega) l9 hPT hmk
      rw [e1, e2, e3, e4, e5, e6] at hm'
      refine ⟨c'', t, ex, ht.le, h11', by rw [hfr _ (by omega)]; exact h0,
        fun x hx => by rw [hfr x hx]; exact j1 x hx, fun a ha => ?_, fun u hu => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm', upd_other _ _ _ (by omega)]; exact j2 a ha
      · rw [hm']
        have hmk' := hmk
        rw [e4, j3 _ hti] at hmk'
        rw [pnMark_succ]
        by_cases hut : u = m (TCb + i)
        · subst hut
          rw [upd_apply, tgIteT rfl, j3 _ hti, orF_eq hmk' (c1F_le _ _ _ _ _ _)]
          simp only [and_true]
        · rw [upd_other _ _ _ (by omega), j3 u hu]
          have h2 : ¬ (c1F (m (PFb + i)) (m (TQb + i)) (m (HQb + i)) (m (THb + i)) (m (TCb + i))
              (m (HCb + i)) = 1 ∧ m (TCb + i) = u) := fun h => hut h.2.symm
          simp only [h2, or_false]
          have := pnMark_le m PFb TQb HQb TCb HCb THb i u
          split_ifs <;> omega)
  have hw₂' := e₂.wb_right
  obtain ⟨c₃, k₃, e₃, hk₃, g11', gn₃, gm₃, gr₃, grm₃, go₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.constN 4211 0]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg 4211 = 0 ∧
      (∀ x, x ≠ 4211 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₃ := e₃.wb_right
  have hR₃ : PnRegs c₃ PFb TQb HQb TCb HCb THb MKb OUTb :=
    hR₁.congr fun x hx => by rw [gn₃ x (by omega), j1 x hx]
  have q0₃ : c₃.nreg 4200 = n := by rw [gn₃ _ (by omega), j1 _ (by omega), q0]
  -- pass 2
  let J2 : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4211 ∨ 4221 < x) → c'.nreg x = c₃.nreg x) ∧
    (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + i) → c'.nmem a = c₂.nmem a) ∧
    (∀ j < i, c'.nmem (OUTb + j) = outF (m (PFb + j)) (m (THb + j)) (m (TCb + j)) (m (HCb + j))
      (pnMark m PFb TQb HQb TCb HCb THb n (m (TCb + j)))) ∧
    c'.rreg = c₃.rreg ∧ c'.rmem = c₃.rmem ∧ c'.output = c₃.output
  obtain ⟨c₄, k₄, e₄, hk₄, hw₄, h11₄, i1, i2, i3, i4, i5, i6⟩ := tgRange (P := P) (a := 4211)
    (b := 4200) (body := pnBody2) J2 (B := 30) c₃ hw₃ g11' q0₃ (Nat.zero_le n)
    ⟨fun _ _ => rfl, fun a _ => by rw [gm₃], fun j hj => absurd hj (by omega), rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h11 h0 ⟨i1, i2, i3, i4, i5, i6⟩ => by
      have hR := hR₃.congr i1
      have hti := hTC i hhi
      have f : ∀ a, a < MKb → c'.nmem a = m a := fun a ha => by
        rw [i2 a (by omega), j2 a (Or.inl ha)]
      have e1 := f (PFb + i) (by omega)
      have e4 := f (TCb + i) (by omega)
      have e5 := f (HCb + i) (by omega)
      have e6 := f (THb + i) (by omega)
      have e7 : c'.nmem (MKb + m (TCb + i)) = pnMark m PFb TQb HQb TCb HCb THb n (m (TCb + i)) := by
        rw [i2 _ (by omega), j3 _ hti]
      obtain ⟨c'', t, ex, ht, h11', hm', hfr, hr', hrm', ho'⟩ := pnBody2_exec (P := P) c' hw hR
        h11 (by omega) (by rw [e4]; omega) (by omega) hPT
      rw [e1, e4, e5, e6, e7] at hm'
      refine ⟨c'', t, ex, ht.le, h11', by rw [hfr _ (by omega)]; exact h0,
        fun x hx => by rw [hfr x hx]; exact i1 x hx, fun a ha => ?_, fun j hj => ?_,
        by rw [hr', i4], by rw [hrm', i5], by rw [ho', i6]⟩
      · rw [hm', upd_other _ _ _ (by omega)]; exact i2 a (by omega)
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact i3 j hj
        · rw [upd_apply, tgIteT rfl])
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, i3, fun a ha => ?_,
    fun x hx => ?_, by rw [i4, gr₃, j4, gr₁], by rw [i5, grm₃, j5, grm₁],
    by rw [i6, go₃, j6, go₁]⟩
  · simp only [Nat.sub_zero] at hk₂ hk₄
    have : (37 : ℕ) * n + 2 + (32 * n + 2) = 69 * n + 4 := by ring
    omega
  · rw [i2 a (by omega), j2 a (by omega)]
  · rw [i1 x (by omega), gn₃ x (by omega), j1 x (by omega), gn₁ x (by omega)]

end Exec

section Link

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

lemma inner_iff_hRel {Hs : List (Finset V)} {d : D} :
    Inner M Hs d ↔ M.tail d ∈ hunion Hs ∧ HRel Hs (M.tail d) (M.head d) := by
  constructor
  · rintro ⟨H, hH, h1, h2⟩; exact ⟨mem_hunion.2 ⟨H, hH, h1⟩, Or.inr ⟨H, hH, h1, h2⟩⟩
  · rintro ⟨h1, h | ⟨H, hH, h2, h3⟩⟩
    · obtain ⟨H, hH, h2⟩ := mem_hunion.1 h1
      exact ⟨H, hH, h2, h ▸ h2⟩
    · exact ⟨H, hH, h2, h3⟩

lemma mem_pcNf {Q : Finset V} {B : Finset D} {Hs : List (Finset V)} {d : D} :
    d ∈ pcNf M Q B Hs ↔ d ∈ B ∧
      (¬ Inner M Hs d ∨ ∃ b ∈ pdarts M (core M Q B) Hs, HRel Hs (M.tail b) (M.tail d)) := by
  classical
  simp only [pcNf, mem_sdiff, mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra h
    push Not at h
    exact h2 ⟨h1, h.1, h.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun ⟨_, h3, h4⟩ => ?_⟩
    rcases h2 with h2 | ⟨b, hb, hb'⟩
    · exact h2 h3
    · exact h4 b hb hb'

end Link

section ExecLink

variable {P : Input} {W : ℕ}

/-- **The attached darts `pcNf` on the machine**: for the arrays of an enumeration `e` of darts
covering the piece `B` (in `B`, tail/head in `Q`, classes `cid` of the ends with
`cid u = cid v ↔ HRel Hs u v`, tail in a hole), within `69 n + 8` steps,
`OUT[j] = 1 ↔ e j ∈ pcNf M Q B Hs` and `OUT[j] ≤ 1` for every `j < n`. -/
theorem pnProg_pcNf {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (Q : Finset V) (B : Finset D)
    (Hs : List (Finset V)) (e : ℕ → D) (cid : V → ℕ) (c : Config) (hc : WordsBounded W c)
    {n nc PFb TQb HQb TCb HCb THb MKb OUTb : ℕ}
    (hL : PnLay n nc PFb TQb HQb TCb HCb THb MKb OUTb W) (r0 : c.nreg 4200 = n)
    (r1 : c.nreg 4201 = PFb) (r2 : c.nreg 4202 = TQb) (r3 : c.nreg 4203 = HQb)
    (r4 : c.nreg 4204 = TCb) (r5 : c.nreg 4205 = HCb) (r6 : c.nreg 4206 = THb)
    (r7 : c.nreg 4207 = MKb) (r8 : c.nreg 4208 = OUTb)
    (hcid : ∀ u v, cid u = cid v ↔ HRel Hs u v) (hcov : ∀ d ∈ B, ∃ j < n, e j = d)
    (hPF : ∀ j < n, (0 < c.nmem (PFb + j) ↔ e j ∈ B))
    (hTQ : ∀ j < n, (c.nmem (TQb + j) = 0 ↔ M.tail (e j) ∉ Q))
    (hHQ : ∀ j < n, (c.nmem (HQb + j) = 0 ↔ M.head (e j) ∉ Q))
    (hTC : ∀ j < n, c.nmem (TCb + j) = cid (M.tail (e j)))
    (hHC : ∀ j < n, c.nmem (HCb + j) = cid (M.head (e j)))
    (hTH : ∀ j < n, (0 < c.nmem (THb + j) ↔ M.tail (e j) ∈ hunion Hs))
    (hnc : ∀ j < n, cid (M.tail (e j)) < nc) (hMK : ∀ t < nc, c.nmem (MKb + t) = 0) :
    ∃ c' k, Exec P W pnProg c c' k ∧ k ≤ 69 * n + 8 ∧
      (∀ j < n, (c'.nmem (OUTb + j) = 1 ↔ e j ∈ pcNf M Q B Hs) ∧ c'.nmem (OUTb + j) ≤ 1) ∧
      (∀ a, (a < MKb ∨ OUTb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4209 ∨ 4221 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c', k, ex, hk, hout, rest⟩ := pnProg_exec (P := P) c hc hL r0 r1 r2 r3 r4 r5 r6 r7 r8
    (fun j hj => by rw [hTC j hj]; exact hnc j hj) hMK
  refine ⟨c', k, ex, hk, fun j hj => ?_, rest⟩
  rw [hout j hj, outF_eq]
  -- the inner test
  have hin : (0 < c.nmem (THb + j) ∧ c.nmem (TCb + j) = c.nmem (HCb + j)) ↔ Inner M Hs (e j) := by
    rw [inner_iff_hRel, hTH j hj, hTC j hj, hHC j hj, hcid]
  -- the c1 test
  have hc1 : ∀ i < n, (c1F (c.nmem (PFb + i)) (c.nmem (TQb + i)) (c.nmem (HQb + i))
      (c.nmem (THb + i)) (c.nmem (TCb + i)) (c.nmem (HCb + i)) = 1 ↔
        e i ∈ pdarts M (core M Q B) Hs) := fun i hi => by
    rw [c1F_eq, mem_pdarts, mem_core, inner_iff_hRel, ← hTH i hi, ← hPF i hi, ← hTQ i hi,
      ← hHQ i hi, hTC i hi, hHC i hi, ← hcid]
    constructor
    · intro h
      split_ifs at h with h'
      exact ⟨⟨h'.1, h'.2.1, h'.2.2.1⟩, h'.2.2.2⟩
    · intro h
      have h' : 0 < c.nmem (PFb + i) ∧ c.nmem (TQb + i) = 0 ∧ c.nmem (HQb + i) = 0 ∧
          ¬ (0 < c.nmem (THb + i) ∧ cid (M.tail (e i)) = cid (M.head (e i))) :=
        ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩
      rw [tgIteT h']
  -- the mark test
  have hmk : 0 < pnMark c.nmem PFb TQb HQb TCb HCb THb n (c.nmem (TCb + j)) ↔
      ∃ b ∈ pdarts M (core M Q B) Hs, HRel Hs (M.tail b) (M.tail (e j)) := by
    unfold pnMark
    constructor
    · intro h
      by_contra hno
      have hex : ¬ ∃ i < n, c1F (c.nmem (PFb + i)) (c.nmem (TQb + i)) (c.nmem (HQb + i))
          (c.nmem (THb + i)) (c.nmem (TCb + i)) (c.nmem (HCb + i)) = 1 ∧
            c.nmem (TCb + i) = c.nmem (TCb + j) := by
        rintro ⟨i, hi, h1, h2⟩
        refine hno ⟨e i, (hc1 i hi).1 h1, ?_⟩
        rw [← hcid, ← hTC i hi, ← hTC j hj, h2]
      rw [tgIteF hex] at h; exact absurd h (lt_irrefl 0)
    · rintro ⟨b, hb, hbr⟩
      obtain ⟨i, hi, rfl⟩ := hcov b ((mem_core.1 (mem_pdarts.1 hb).1).1)
      have hex : ∃ i < n, c1F (c.nmem (PFb + i)) (c.nmem (TQb + i)) (c.nmem (HQb + i))
          (c.nmem (THb + i)) (c.nmem (TCb + i)) (c.nmem (HCb + i)) = 1 ∧
            c.nmem (TCb + i) = c.nmem (TCb + j) :=
        ⟨i, hi, (hc1 i hi).2 hb, by rw [hTC i hi, hTC j hj, hcid]; exact hbr⟩
      rw [tgIteT hex]; exact one_pos
  rw [mem_pcNf, ← hPF j hj, ← hin, ← hmk]
  constructor
  · constructor
    · intro h
      by_contra h'
      rw [tgIteF h'] at h; exact zero_ne_one h
    · intro h; rw [tgIteT h]
  · split_ifs <;> omega

end ExecLink

end BKMNW

end PlanarFlow
