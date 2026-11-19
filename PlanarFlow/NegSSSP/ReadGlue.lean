module

public import PlanarFlow.NegSSSP.LinGlue
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Reading the answers of Klein's program on the machine

Klein's program (`PlanarFlow.Klein.kleinProg`) leaves its answers on the perturbed lengths in
memory: a reach flag (natural memory) and a real value per pair of a source and a target, and an
answer is read back as the integer part of the value divided by `2 ^ M` (`Klein.outNN`), cut off
at a bound `W` (`Klein.cutW`). The machine has no real-to-integer rounding; this file recovers the
integer part by a **binary search on the real side**: with `0 ≤ y < 2 ^ L`, the `L` comparisons
`y < acc + p` (`p = 2 ^ (L - 1), …, 1`, halved by an exact real division) leave `acc = ⌊y⌋` as a
real (`sLoop_exec`).

`rdProg` reads the `b²` answers at the pairs of sources `σ s`, `σ t` (`s, t < b`) of an
instance with `k` targets into the row-major layout of `NegSSSP.bfStartP`: the flag
`[f = 1 ∧ r / 2 ^ M < W]` at `Fb + s b + t` (natural memory) and the value
`⌊r / 2 ^ M⌋ + δ (ν t) - δ (ν s)` (or `0` without an arc) at `Lb + s b + t` (real memory), `f`
and `r` the flag and the value of the pair, `δ` a real array indexed by the numbers `ν`
(`rdProg_exec`, within `rdCost b L M = 4 M + 4 L + 14 + 14 b + (8 L + 31) b²` steps). The scale
`2 ^ M` is computed by `M` doublings, the top `2 ^ L / 2` by `L` doublings.

Registers: natural `r300 … r310` the data (`RdIn`), `r311 … r340` scratch; real `r301` the bound
`W`, `r300`, `r302 … r309` scratch.
-/

@[expose] public section

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge

variable {P : Input} {W : ℕ}

/-! ### The binary search -/

/-- One step of the search: `tmp := acc + p`; `acc := tmp` unless `y < tmp`; `p := p / 2`
(real registers `306 = y`, `307 = acc`, `308 = p`, `309 = tmp`, `303 = 2`; `r313` the counter,
`r320 = 1`). -/
def sStep : Stmt :=
  .seq (.instr (.addR 309 307 308)) <|
  .seq (.ifLtR 306 309 .skip (.instr (.copyR 307 309)))
    (block [.divR 308 308 303, .addN 313 313 320])

/-- **The binary search**: `acc := 0`, `p := r302`, then `r309` steps. -/
def sLoop : Stmt :=
  .seq (block [.constR 307 0, .copyR 308 302, .constN 313 0]) (.whileLtN 313 309 sStep)

theorem sStep_exec (c : Config) (hc : WordsBounded W c) (h303 : c.rreg 303 = 2)
    (h320 : c.nreg 320 = 1) (h313 : c.nreg 313 + 1 ≤ W) :
    ∃ c' k, Exec P W sStep c c' k ∧ k ≤ 6 ∧
      (c'.rreg 307 = (if c.rreg 306 < c.rreg 307 + c.rreg 308 then c.rreg 307
          else c.rreg 307 + c.rreg 308) ∧ c'.rreg 308 = c.rreg 308 / 2 ∧
        (∀ r, r ≠ 307 → r ≠ 308 → r ≠ 309 → c'.rreg r = c.rreg r) ∧
        c'.nreg 313 = c.nreg 313 + 1 ∧ (∀ r, r ≠ 313 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold sStep
  refine spec_seq ?_
  refine spec_instr (Exec.addR hc 309 307 308) fun hw₁ => ?_
  refine spec_seq ?_
  by_cases hlt : c.rreg 306 < c.rreg 307 + c.rreg 308
  · refine spec_ifLtR_true (by config_simp; exact hlt) ?_
    refine spec_skip hw₁ ?_
    exec_block
    · config_simp; rw [h303]; norm_num
    · config_simp; omega
    · config_simp
      simp only [hlt, ↓reduceIte, h320, h303]
      and_intros
      all_goals first
        | trivial
        | omega
        | rfl
        | (intro r h1 h2 h3; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
        | (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
  · refine spec_ifLtR_false (by config_simp; exact hlt) ?_
    refine spec_instr (Exec.copyR hw₁ 307 309) fun hw₂ => ?_
    exec_block
    · config_simp; rw [h303]; norm_num
    · config_simp; omega
    · config_simp
      simp only [hlt, ↓reduceIte, h320, h303]
      and_intros
      all_goals first
        | trivial
        | omega
        | rfl
        | (intro r h1 h2 h3; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
        | (intro r hr; simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-- One step of the search on the reals: from `z ≤ y < z + 2 p` with `p = 2 ^ n`, the new
accumulator is an integer `z'` with `z' ≤ y < z' + 2 (p / 2)`. -/
lemma bs_step {y a p : ℝ} {z : ℤ} (n : ℕ) (hp : p = (2 : ℝ) ^ n) (ha : a = z)
    (h1 : (z : ℝ) ≤ y) (h2 : y < z + 2 * p) :
    ∃ z' : ℤ, (if y < a + p then a else a + p) = z' ∧ (z' : ℝ) ≤ y ∧ y < z' + 2 * (p / 2) := by
  split_ifs with h
  · exact ⟨z, ha, h1, by rw [ha] at h; linarith⟩
  · refine ⟨z + 2 ^ n, by push_cast; rw [ha, hp], ?_, ?_⟩
    · push_cast; rw [← hp, ← ha]; linarith
    · push_cast; rw [← hp]; linarith

/-- **The binary search on the machine.** With `r302 = 2 ^ L / 2`, `r309 = L`, `r303 = 2`,
`r320 = 1` and `y = r306 < 2 ^ L`, `sLoop` leaves `⌊y⌋` (as a real) in `r307` when `0 ≤ y`,
within `8 L + 5` steps. -/
theorem sLoop_exec {L : ℕ} (c : Config) (hc : WordsBounded W c) (h303 : c.rreg 303 = 2)
    (h320 : c.nreg 320 = 1) (h309 : c.nreg 309 = L) (h302 : c.rreg 302 = (2 : ℝ) ^ L / 2)
    (hy : c.rreg 306 < (2 : ℝ) ^ L) :
    ∃ c' k, Exec P W sLoop c c' k ∧ k ≤ 8 * L + 5 ∧
      ((0 ≤ c.rreg 306 → c'.rreg 307 = (⌊c.rreg 306⌋ : ℝ)) ∧
        (∀ r, r ≠ 307 → r ≠ 308 → r ≠ 309 → c'.rreg r = c.rreg r) ∧
        (∀ r, r ≠ 313 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧
        c'.output = c.output) := by
  have hLW : L ≤ W := h309 ▸ hc.1 309
  unfold sLoop
  refine spec_seq ?_
  exec_block
  · omega
  set y := c.rreg 306 with hyd
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ r, r ≠ 307 → r ≠ 308 → r ≠ 309 → c'.rreg r = c.rreg r) ∧
    (∀ r, r ≠ 313 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧
    c'.output = c.output ∧ c'.rreg 308 = (2 : ℝ) ^ L / 2 ^ (i + 1) ∧
    (0 ≤ y → ∃ z : ℤ, c'.rreg 307 = z ∧ (z : ℝ) ≤ y ∧ y < z + 2 * c'.rreg 308)
  refine spec_use (forLoop_exec (P := P) (a := 313) (bR := 309) (body := sStep) J (K := 6)
    (n := L) _ ‹_› (by config_simp) (by config_simp; exact h309) ?_
    (fun i c₁ hi hw ha hb ⟨fr, fn, fnm, frm, fo, fp, fz⟩ => by
      have e303 : c₁.rreg 303 = 2 := (fr 303 (by omega) (by omega) (by omega)).trans h303
      have e320 : c₁.nreg 320 = 1 := (fn 320 (by omega)).trans h320
      have e306 : c₁.rreg 306 = y := fr 306 (by omega) (by omega) (by omega)
      refine spec_use (sStep_exec (P := P) c₁ hw e303 e320 (by omega)) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨g7, g8, gr, g313, gn, gnm, grm, go⟩
      have hpn : c₁.rreg 308 = (2 : ℝ) ^ (L - (i + 1)) := by
        rw [fp, pow_sub₀ _ two_ne_zero (by omega), div_eq_mul_inv]
      refine ⟨hk₂, by rw [g313, ha], by rw [gn 309 (by omega), hb], fun r h1 h2 h3 => ?_,
        fun r hr => ?_, by rw [gnm, fnm], by rw [grm, frm], by rw [go, fo], ?_, fun h0 => ?_⟩
      · rw [gr r h1 h2 h3, fr r h1 h2 h3]
      · rw [gn r hr, fn r hr]
      · rw [g8, fp, pow_succ _ (i + 1), div_div]
      · obtain ⟨z, hz, hz1, hz2⟩ := fz h0
        obtain ⟨z', hz', h1', h2'⟩ := bs_step (y := y) (L - (i + 1)) hpn hz hz1 hz2
        refine ⟨z', ?_, h1', ?_⟩
        · rw [g7, e306, hz']
        · rw [g8]; exact h2')) ?_
  · refine ⟨fun r h1 h2 h3 => ?_, fun r hr => ?_, rfl, rfl, rfl, ?_, fun _ => ⟨0, ?_, ?_, ?_⟩⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
    · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
    · config_simp; rw [h302, pow_one]
    · config_simp
    · simpa using ‹0 ≤ y›
    · config_simp; rw [h302]; push_cast; linarith
  intro c₂ k₂ hk₂ _ ⟨_, fr, fn, fnm, frm, fo, fp, fz⟩
  refine ⟨by omega, fun h0 => ?_, fr, fn, fnm, frm, fo⟩
  obtain ⟨z, hz, hz1, hz2⟩ := fz h0
  have : c₂.rreg 308 = 1 / 2 := by
    rw [fp, pow_succ, div_mul_eq_div_div, div_self (pow_ne_zero _ two_ne_zero)]
  rw [this] at hz2
  rw [hz, Int.floor_eq_iff.2 ⟨hz1, by linarith⟩]

/-! ### One answer -/

/-- No arc: flag `0` at `r307 + r337`, value `0` at `r308 + r337`. -/
def eNo : Stmt := block [.addN 330 307 337, .constN 340 0, .storeN 330 340, .constR 307 0,
  .addN 330 308 337, .storeR 330 307]

/-- An arc: the search, then flag `1` and value `⌊y⌋ + r305 - r304`. -/
def eYes : Stmt := .seq sLoop (block [.addR 307 307 305, .subR 307 307 304, .addN 330 307 337,
  .storeN 330 320, .addN 330 308 337, .storeR 330 307])

/-- The choice on the flag `r338` and the value `r306`: an arc iff the flag is `1` and
`r306 / r300 < r301`. -/
def eSel : Stmt := .ifLtN 338 320 eNo (.ifLtN 320 338 eNo
  (.seq (.instr (.divR 306 306 300)) (.ifLtR 306 301 eYes eNo)))

theorem eNo_exec (c : Config) (hc : WordsBounded W c) (h1 : c.nreg 307 + c.nreg 337 ≤ W)
    (h2 : c.nreg 308 + c.nreg 337 ≤ W) :
    ∃ c' k, Exec P W eNo c c' k ∧ k ≤ 6 ∧
      (c'.nmem = upd c.nmem (c.nreg 307 + c.nreg 337) 0 ∧
        c'.rmem = upd c.rmem (c.nreg 308 + c.nreg 337) 0 ∧
        (∀ r, r ≠ 330 → r ≠ 340 → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 307 → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  have h0 : 0 ≤ W := Nat.zero_le _
  unfold eNo
  exec_block
  all_goals try ((try config_simp); omega)
  config_simp
  and_intros
  all_goals first
    | trivial
    | omega
    | rfl
    | (intro r h1 h2; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
    | (intro r h1; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
    | simp

theorem eYes_exec {L : ℕ} (c : Config) (hc : WordsBounded W c) (h303 : c.rreg 303 = 2)
    (h320 : c.nreg 320 = 1) (h309 : c.nreg 309 = L) (h302 : c.rreg 302 = (2 : ℝ) ^ L / 2)
    (hy : c.rreg 306 < (2 : ℝ) ^ L) (h1 : c.nreg 307 + c.nreg 337 ≤ W)
    (h2 : c.nreg 308 + c.nreg 337 ≤ W) :
    ∃ c' k, Exec P W eYes c c' k ∧ k ≤ 8 * L + 11 ∧
      ∃ v : ℝ, (0 ≤ c.rreg 306 → v = ⌊c.rreg 306⌋ + c.rreg 305 - c.rreg 304) ∧
        c'.nmem = upd c.nmem (c.nreg 307 + c.nreg 337) 1 ∧
        c'.rmem = upd c.rmem (c.nreg 308 + c.nreg 337) v ∧
        (∀ r, r ≠ 330 → r ≠ 313 → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 307 → r ≠ 308 → r ≠ 309 → c'.rreg r = c.rreg r) ∧ c'.output = c.output := by
  unfold eYes
  refine spec_seq ?_
  refine spec_use (sLoop_exec (P := P) c hc h303 h320 h309 h302 hy) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨g7, gr, gn, gnm, grm, go⟩
  have e307 := gn 307 (by omega)
  have e308 := gn 308 (by omega)
  have e337 := gn 337 (by omega)
  have e320 := gn 320 (by omega)
  have e305 := gr 305 (by omega) (by omega) (by omega)
  have e304 := gr 304 (by omega) (by omega) (by omega)
  exec_block
  all_goals try ((try config_simp); (try simp only [e307, e308, e337]); omega)
  config_simp
  refine ⟨by omega, c₁.rreg 307 + c₁.rreg 305 - c₁.rreg 304, fun h0 => by rw [g7 h0, e305, e304],
    ?_, ?_, fun r h1 h2 => ?_, fun r h1 h2 h3 => ?_, go⟩
  · rw [e307, e337, e320, gnm, h320]
  · rw [e308, e337, grm]
  · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r (by omega)
  · simp only [upd_apply]; split_ifs <;> first | omega | exact gr r h1 h2 h3

theorem eSel_exec {L M : ℕ} {Wr : ℝ} (c : Config) (hc : WordsBounded W c)
    (h303 : c.rreg 303 = 2) (h320 : c.nreg 320 = 1) (h309 : c.nreg 309 = L)
    (h302 : c.rreg 302 = (2 : ℝ) ^ L / 2) (h300 : c.rreg 300 = (2 : ℝ) ^ M)
    (h301 : c.rreg 301 = Wr) (hWL : Wr ≤ (2 : ℝ) ^ L) (h1 : c.nreg 307 + c.nreg 337 ≤ W)
    (h2 : c.nreg 308 + c.nreg 337 ≤ W) :
    ∃ c' k, Exec P W eSel c c' k ∧ k ≤ 8 * L + 17 ∧
      ∃ v : ℝ, (¬ (c.nreg 338 = 1 ∧ c.rreg 306 / 2 ^ M < Wr) → v = 0) ∧
        ((c.nreg 338 = 1 ∧ c.rreg 306 / 2 ^ M < Wr) → 0 ≤ c.rreg 306 →
          v = ⌊c.rreg 306 / 2 ^ M⌋ + c.rreg 305 - c.rreg 304) ∧
        c'.nmem = upd c.nmem (c.nreg 307 + c.nreg 337)
          (if c.nreg 338 = 1 ∧ c.rreg 306 / 2 ^ M < Wr then 1 else 0) ∧
        c'.rmem = upd c.rmem (c.nreg 308 + c.nreg 337) v ∧
        (∀ r, r ≠ 330 → r ≠ 340 → r ≠ 313 → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 306 → r ≠ 307 → r ≠ 308 → r ≠ 309 → c'.rreg r = c.rreg r) ∧
        c'.output = c.output := by
  unfold eSel
  by_cases f0 : c.nreg 338 < c.nreg 320
  · refine spec_ifLtN_true f0 ?_
    refine spec_use (eNo_exec (P := P) c hc h1 h2) ?_
    intro c₁ k₁ hk₁ _ ⟨gnm, grm, gn, gr, go⟩
    have hA : ¬ (c.nreg 338 = 1 ∧ c.rreg 306 / 2 ^ M < Wr) := fun h => by omega
    refine ⟨by omega, 0, fun _ => rfl, fun h => absurd h hA,
      by rw [gnm, ite_eq_right_of_eq_false _ _ (eq_false hA)], grm,
      fun r h1 h2 _ => gn r h1 h2, fun r _ h2 _ _ => gr r h2, go⟩
  refine spec_ifLtN_false f0 ?_
  by_cases f1 : c.nreg 320 < c.nreg 338
  · refine spec_ifLtN_true f1 ?_
    refine spec_use (eNo_exec (P := P) c hc h1 h2) ?_
    intro c₁ k₁ hk₁ _ ⟨gnm, grm, gn, gr, go⟩
    have hA : ¬ (c.nreg 338 = 1 ∧ c.rreg 306 / 2 ^ M < Wr) := fun h => by omega
    refine ⟨by omega, 0, fun _ => rfl, fun h => absurd h hA,
      by rw [gnm, ite_eq_right_of_eq_false _ _ (eq_false hA)], grm,
      fun r h1 h2 _ => gn r h1 h2, fun r _ h2 _ _ => gr r h2, go⟩
  refine spec_ifLtN_false f1 ?_
  have hf : c.nreg 338 = 1 := by omega
  refine spec_seq ?_
  refine spec_instr (Exec.divR hc 306 306 300 (by rw [h300]; positivity)) fun hw₁ => ?_
  by_cases hlt : c.rreg 306 / 2 ^ M < Wr
  · have hA : c.nreg 338 = 1 ∧ c.rreg 306 / 2 ^ M < Wr := ⟨hf, hlt⟩
    refine spec_ifLtR_true (by config_simp; rw [h300, h301]; exact hlt) ?_
    refine spec_use (eYes_exec (P := P) (L := L) _ hw₁ (by config_simp; exact h303)
      (by config_simp; exact h320) (by config_simp; exact h309) (by config_simp; exact h302)
      (by config_simp; rw [h300]; linarith) (by config_simp; exact h1)
      (by config_simp; exact h2)) ?_
    intro c₁ k₁ hk₁ _ ⟨v, hv, gnm, grm, gn, gr, go⟩
    config_simp at hv
    config_simp at gnm
    config_simp at grm
    refine ⟨by omega, v, fun h => absurd hA h, fun _ h0 => ?_,
      by rw [gnm, ite_eq_left_of_eq_true _ _ (eq_true hA)], grm,
      fun r h1 h2 h3 => ?_, fun r h1 h2 h3 h4 => ?_, go⟩
    · rw [hv (by rw [h300]; positivity), h300]
    · rw [gn r h1 h3]
    · rw [gr r h2 h3 h4]; config_simp; simp only [upd_apply, h1, ↓reduceIte]
  · have hA : ¬ (c.nreg 338 = 1 ∧ c.rreg 306 / 2 ^ M < Wr) := fun h => hlt h.2
    refine spec_ifLtR_false (by config_simp; rw [h300, h301]; exact hlt) ?_
    refine spec_use (eNo_exec (P := P) _ hw₁ (by config_simp; exact h1)
      (by config_simp; exact h2)) ?_
    intro c₁ k₁ hk₁ _ ⟨gnm, grm, gn, gr, go⟩
    config_simp at gnm
    config_simp at grm
    refine ⟨by omega, 0, fun _ => rfl, fun h => absurd h hA,
      by rw [gnm, ite_eq_right_of_eq_false _ _ (eq_false hA)], grm,
      fun r h1 h2 _ => by rw [gn r h1 h2], fun r h1 h2 _ _ => ?_, go⟩
    rw [gr r h2]; config_simp; simp only [upd_apply, h1, ↓reduceIte]

/-! ### The data of the reading -/

/-- **The data of `rdProg`**: `b` pairs per row; `k` the targets of Klein's program (the stride
of its answers); `w` the vertex numbers; the bases `Sg` of the source indices `σ` and `Nb` of
the vertex numbers `ν` (natural memory), `δb` of the potentials (real memory, by vertex number),
`RBb` of Klein's flags (natural) and `OUTb` of its values (real), `Fb` of the output flags
(natural) and `Lb` of the output values (real); the bits `L` of the search, the exponent `M` of
the scale; the cut `Wr`. -/
structure Rd where
  b : ℕ
  k : ℕ
  w : ℕ
  Sg : ℕ
  Nb : ℕ
  δb : ℕ
  RBb : ℕ
  OUTb : ℕ
  Fb : ℕ
  Lb : ℕ
  L : ℕ
  M : ℕ
  σ : ℕ → ℕ
  ν : ℕ → ℕ
  Wr : ℝ

/-- The registers and arrays of `rdProg`. -/
structure RdIn (R : Rd) (c : Config) : Prop where
  r300 : c.nreg 300 = R.b
  r301 : c.nreg 301 = R.Sg
  r302 : c.nreg 302 = R.Nb
  r303 : c.nreg 303 = R.δb
  r304 : c.nreg 304 = R.RBb
  r305 : c.nreg 305 = R.OUTb
  r306 : c.nreg 306 = R.k
  r307 : c.nreg 307 = R.Fb
  r308 : c.nreg 308 = R.Lb
  r309 : c.nreg 309 = R.L
  r310 : c.nreg 310 = R.M
  w301 : c.rreg 301 = R.Wr
  sg : ∀ s < R.b, c.nmem (R.Sg + s) = R.σ s
  nb : ∀ s < R.b, c.nmem (R.Nb + s) = R.ν s

/-- The layout of `rdProg`: the indices in range, the outputs apart from the arrays read, the
addresses below the word bound. -/
structure RdLay (R : Rd) (W : ℕ) : Prop where
  σlt : ∀ s < R.b, R.σ s < R.k
  νlt : ∀ s < R.b, R.ν s < R.w
  fS : R.Fb + R.b * R.b ≤ R.Sg ∨ R.Sg + R.b ≤ R.Fb
  fN : R.Fb + R.b * R.b ≤ R.Nb ∨ R.Nb + R.b ≤ R.Fb
  fR : R.Fb + R.b * R.b ≤ R.RBb ∨ R.RBb + R.k * R.k ≤ R.Fb
  lD : R.Lb + R.b * R.b ≤ R.δb ∨ R.δb + R.w ≤ R.Lb
  lO : R.Lb + R.b * R.b ≤ R.OUTb ∨ R.OUTb + R.k * R.k ≤ R.Lb
  wS : R.Sg + R.b ≤ W
  wN : R.Nb + R.b ≤ W
  wD : R.δb + R.w ≤ W
  wR : R.RBb + R.k * R.k ≤ W
  wO : R.OUTb + R.k * R.k ≤ W
  wF : R.Fb + R.b * R.b ≤ W
  wL : R.Lb + R.b * R.b ≤ W
  wb : R.b * R.b + 1 ≤ W
  wM : R.M + 1 ≤ W
  wLL : R.L + 1 ≤ W

/-- The address of the answer of the pair `(s, t)` in Klein's arrays. -/
def Rd.ad (R : Rd) (s t : ℕ) : ℕ := R.σ s * R.k + R.σ t

/-- The pair `(s, t)` has an arc: Klein's flag is `1` and the value, scaled, is below the cut
(in the memory of `c`). -/
def Rd.A (R : Rd) (c : Config) (s t : ℕ) : Prop :=
  c.nmem (R.RBb + R.ad s t) = 1 ∧ c.rmem (R.OUTb + R.ad s t) / 2 ^ R.M < R.Wr

/-- **The output of the pair `(s, t)`** in `c'`, from the answers in `c`: the flag of an arc at
`Fb + s b + t`, and at `Lb + s b + t` the value `0` without an arc, and with an arc (and a
nonnegative answer) the integer part of the scaled answer plus `δ (ν t) - δ (ν s)`. -/
def Rd.Out (R : Rd) (c c' : Config) (s t : ℕ) : Prop :=
  c'.nmem (R.Fb + (s * R.b + t)) = (if R.A c s t then 1 else 0) ∧
    (¬ R.A c s t → c'.rmem (R.Lb + (s * R.b + t)) = 0) ∧
    (R.A c s t → 0 ≤ c.rmem (R.OUTb + R.ad s t) →
      c'.rmem (R.Lb + (s * R.b + t)) = ⌊c.rmem (R.OUTb + R.ad s t) / 2 ^ R.M⌋ +
        c.rmem (R.δb + R.ν t) - c.rmem (R.δb + R.ν s))

lemma rm_lt {b s t : ℕ} (hs : s < b) (ht : t < b) : s * b + t < b * b := by nlinarith

lemma rm_inj {b s t s' t' : ℕ} (ht : t < b) (ht' : t' < b) (h : s * b + t = s' * b + t') :
    s = s' ∧ t = t' := by
  have hb : 0 < b := by omega
  have h1 : (s * b + t) / b = s := by
    rw [add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt ht, zero_add]
  have h2 : (s' * b + t') / b = s' := by
    rw [add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt ht', zero_add]
  have : s = s' := by rw [← h1, ← h2, h]
  subst this; omega

/-! ### One answer, read -/

/-- The reads of the pair `(s, r312)`: `r335 = σ s k + σ t` (from `r331 = σ s k`),
`r337 = s b + t` (from `r333 = s b`), the flag into `r338`, `δ (ν t)` into the real `r305`, the
answer into the real `r306`. -/
def eRead : Stmt := block [.addN 330 301 312, .loadN 334 330, .addN 335 331 334,
  .addN 330 302 312, .loadN 336 330, .addN 330 303 336, .loadR 305 330, .addN 337 333 312,
  .addN 330 304 335, .loadN 338 330, .addN 339 305 335, .loadR 306 339]

/-- The pair `(s, r312)`, and the next `t`. -/
def eBody : Stmt := .seq eRead (.seq eSel (block [.addN 312 312 320]))

theorem eRead_exec {R : Rd} (hL : RdLay R W) (c : Config) (hc : WordsBounded W c)
    (hI : RdIn R c) {s t : ℕ} (hs : s < R.b) (ht : t < R.b) (h312 : c.nreg 312 = t)
    (h331 : c.nreg 331 = R.σ s * R.k) (h333 : c.nreg 333 = s * R.b) :
    ∃ c' k, Exec P W eRead c c' k ∧ k ≤ 12 ∧
      (c'.nreg 337 = s * R.b + t ∧ c'.nreg 338 = c.nmem (R.RBb + R.ad s t) ∧
        c'.rreg 305 = c.rmem (R.δb + R.ν t) ∧ c'.rreg 306 = c.rmem (R.OUTb + R.ad s t) ∧
        (∀ r, r ≠ 330 → (r < 334 ∨ 339 < r) → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 305 → r ≠ 306 → c'.rreg r = c.rreg r) ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wS; have := hL.wN; have := hL.wD; have := hL.wR; have := hL.wO; have := hL.wb
  have hσs := hL.σlt s hs
  have hσt := hL.σlt t ht
  have hνt := hL.νlt t ht
  have hσ := hI.sg t ht
  have hν := hI.nb t ht
  have hadk : R.σ s * R.k + R.σ t < R.k * R.k := rm_lt hσs hσt
  have hbb : s * R.b + t < R.b * R.b := rm_lt hs ht
  unfold eRead
  exec_block
  all_goals try ((try config_simp); (try simp only [hI.r301, hI.r302, hI.r303, hI.r304,
    hI.r305, h312, h331, h333, hσ, hν]); omega)
  config_simp
  simp only [hI.r301, hI.r302, hI.r303, hI.r304, hI.r305, h312, h331, h333, hσ, hν, Rd.ad]
  and_intros
  all_goals first
    | trivial
    | omega
    | rfl
    | (intro r h1 h2; simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem eBody_exec {R : Rd} (hL : RdLay R W) (hWL : R.Wr ≤ (2 : ℝ) ^ R.L) (c : Config)
    (hc : WordsBounded W c)
    (hI : RdIn R c) {s t : ℕ} (hs : s < R.b) (ht : t < R.b) (h312 : c.nreg 312 = t)
    (h331 : c.nreg 331 = R.σ s * R.k) (h333 : c.nreg 333 = s * R.b) (h320 : c.nreg 320 = 1)
    (h300 : c.rreg 300 = (2 : ℝ) ^ R.M) (h302 : c.rreg 302 = (2 : ℝ) ^ R.L / 2)
    (h303 : c.rreg 303 = 2) :
    ∃ c' k, Exec P W eBody c c' k ∧ k ≤ 8 * R.L + 30 ∧
      (c'.nreg 312 = t + 1 ∧
        c'.nmem = upd c.nmem (R.Fb + (s * R.b + t)) (if R.A c s t then 1 else 0) ∧
        (∃ v : ℝ, c'.rmem = upd c.rmem (R.Lb + (s * R.b + t)) v ∧ (¬ R.A c s t → v = 0) ∧
          (R.A c s t → 0 ≤ c.rmem (R.OUTb + R.ad s t) →
            v = ⌊c.rmem (R.OUTb + R.ad s t) / 2 ^ R.M⌋ + c.rmem (R.δb + R.ν t) - c.rreg 304)) ∧
        (∀ r, r ≠ 312 → r ≠ 313 → r ≠ 330 → (r < 334 ∨ 340 < r) → c'.nreg r = c.nreg r) ∧
        (∀ r, (r < 305 ∨ 309 < r) → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  have := hL.wF; have := hL.wL; have := hL.wb
  have hbb : s * R.b + t < R.b * R.b := rm_lt hs ht
  unfold eBody
  refine spec_seq ?_
  refine spec_use (eRead_exec (P := P) hL c hc hI hs ht h312 h331 h333) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨g337, g338, g305, g306, gn, gr, gnm, grm, go⟩
  refine spec_seq ?_
  refine spec_use (eSel_exec (P := P) (L := R.L) (M := R.M) (Wr := R.Wr) c₁ hw₁
    (by rw [gr 303 (by omega) (by omega), h303]) (by rw [gn 320 (by omega) (by omega), h320])
    (by rw [gn 309 (by omega) (by omega), hI.r309]) (by rw [gr 302 (by omega) (by omega), h302])
    (by rw [gr 300 (by omega) (by omega), h300]) (by rw [gr 301 (by omega) (by omega), hI.w301])
    hWL (by rw [gn 307 (by omega) (by omega), hI.r307, g337]; omega)
    (by rw [gn 308 (by omega) (by omega), hI.r308, g337]; omega)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨v, hv0, hv1, hnm, hrm, gn₂, gr₂, go₂⟩
  have e312 : c₂.nreg 312 = t := by
    rw [gn₂ 312 (by omega) (by omega) (by omega), gn 312 (by omega) (by omega), h312]
  have e320 : c₂.nreg 320 = 1 := by
    rw [gn₂ 320 (by omega) (by omega) (by omega), gn 320 (by omega) (by omega), h320]
  have e307 : c₁.nreg 307 = R.Fb := by rw [gn 307 (by omega) (by omega), hI.r307]
  have e308 : c₁.nreg 308 = R.Lb := by rw [gn 308 (by omega) (by omega), hI.r308]
  have e304 : c₁.rreg 304 = c.rreg 304 := gr 304 (by omega) (by omega)
  simp only [g338, g306, g305, e304, gnm, grm, e307, e308, g337] at hnm hrm hv0 hv1
  exec_block
  all_goals try ((try config_simp); (try simp only [e312, e320]); omega)
  config_simp
  simp only [e312, e320]
  refine ⟨by omega, by trivial, by rw [hnm]; exact congrArg _ (if_congr Iff.rfl rfl rfl),
    ⟨v, hrm, hv0, hv1⟩, fun r h1 h2 h3 h4 => ?_, fun r hr => ?_,
    ?_⟩
  · simp only [upd_apply]
    rw [ite_eq_right_of_eq_false _ _ (eq_false h1), gn₂ r h3 (by omega) h2, gn r h3 (by omega)]
  · rw [gr₂ r (by omega) (by omega) (by omega) (by omega), gr r (by omega) (by omega)]
  · rw [go₂, go]

/-! ### The rows -/

/-- **The invariant of the reading**, after the pairs `s b + t < q`: the data registers and the
constants kept, the memory changed only in the output regions, the outputs of those pairs
written (`Rd.Out`, from the answers in `c₀`). -/
def RdInv (R : Rd) (c₀ c : Config) (q : ℕ) : Prop :=
  (∀ r, r < 311 → c.nreg r = c₀.nreg r) ∧ c.nreg 320 = 1 ∧ c.rreg 300 = (2 : ℝ) ^ R.M ∧
    c.rreg 301 = c₀.rreg 301 ∧ c.rreg 302 = (2 : ℝ) ^ R.L / 2 ∧ c.rreg 303 = 2 ∧
    (∀ a, (a < R.Fb ∨ R.Fb + R.b * R.b ≤ a) → c.nmem a = c₀.nmem a) ∧
    (∀ a, (a < R.Lb ∨ R.Lb + R.b * R.b ≤ a) → c.rmem a = c₀.rmem a) ∧
    (∀ s < R.b, ∀ t < R.b, s * R.b + t < q → R.Out c₀ c s t) ∧ c.output = c₀.output

section Inv

variable {R : Rd} {c₀ c : Config} {q : ℕ}

lemma RdInv.rdIn (hL : RdLay R W) (hI : RdIn R c₀) (h : RdInv R c₀ c q) : RdIn R c := by
  obtain ⟨hr, -, -, h301, -, -, hn, -, -, -⟩ := h
  have := hL.fS; have := hL.fN
  exact ⟨(hr 300 (by omega)).trans hI.r300, (hr 301 (by omega)).trans hI.r301,
    (hr 302 (by omega)).trans hI.r302, (hr 303 (by omega)).trans hI.r303,
    (hr 304 (by omega)).trans hI.r304, (hr 305 (by omega)).trans hI.r305,
    (hr 306 (by omega)).trans hI.r306, (hr 307 (by omega)).trans hI.r307,
    (hr 308 (by omega)).trans hI.r308, (hr 309 (by omega)).trans hI.r309,
    (hr 310 (by omega)).trans hI.r310, h301.trans hI.w301,
    fun s hs => by rw [hn _ (by omega)]; exact hI.sg s hs,
    fun s hs => by rw [hn _ (by omega)]; exact hI.nb s hs⟩

lemma RdInv.reads (hL : RdLay R W) (h : RdInv R c₀ c q) {s t : ℕ} (hs : s < R.b)
    (ht : t < R.b) :
    c.nmem (R.RBb + R.ad s t) = c₀.nmem (R.RBb + R.ad s t) ∧
      c.rmem (R.OUTb + R.ad s t) = c₀.rmem (R.OUTb + R.ad s t) ∧
      c.rmem (R.δb + R.ν t) = c₀.rmem (R.δb + R.ν t) ∧
      c.rmem (R.δb + R.ν s) = c₀.rmem (R.δb + R.ν s) := by
  obtain ⟨-, -, -, -, -, -, hn, hr, -, -⟩ := h
  have hadk : R.ad s t < R.k * R.k := rm_lt (hL.σlt s hs) (hL.σlt t ht)
  have := hL.fR; have := hL.lO; have := hL.lD
  have := hL.νlt s hs; have := hL.νlt t ht
  exact ⟨hn _ (by omega), hr _ (by omega), hr _ (by omega), hr _ (by omega)⟩

lemma RdInv.A_eq (hL : RdLay R W) (h : RdInv R c₀ c q) {s t : ℕ} (hs : s < R.b)
    (ht : t < R.b) : R.A c s t = R.A c₀ s t := by
  obtain ⟨e1, e2, -, -⟩ := h.reads hL hs ht
  unfold Rd.A; rw [e1, e2]

end Inv

/-- The row `s = r311`: `r331 = σ s k`, `δ (ν s)` into the real `r304`, `r333 = s b`, the
pairs `(s, t)`, `t < b`, and the next row. -/
def rRow : Stmt := .seq (block [.addN 330 301 311, .loadN 331 330, .mulN 331 331 306,
  .addN 330 302 311, .loadN 332 330, .addN 330 303 332, .loadR 304 330, .mulN 333 311 300,
  .constN 312 0]) (.seq (.whileLtN 312 300 eBody) (block [.addN 311 311 320]))

theorem eBody_inv {R : Rd} (hL : RdLay R W) (hWL : R.Wr ≤ (2 : ℝ) ^ R.L) {c₀ : Config}
    (hI₀ : RdIn R c₀) (c : Config)
    (hc : WordsBounded W c) {s t : ℕ} (hs : s < R.b) (ht : t < R.b)
    (hJ : RdInv R c₀ c (s * R.b + t)) (h312 : c.nreg 312 = t) (h311 : c.nreg 311 = s)
    (h331 : c.nreg 331 = R.σ s * R.k) (h333 : c.nreg 333 = s * R.b)
    (h304 : c.rreg 304 = c₀.rmem (R.δb + R.ν s)) :
    ∃ c' k, Exec P W eBody c c' k ∧ k ≤ 8 * R.L + 30 ∧ c'.nreg 312 = t + 1 ∧
      RdInv R c₀ c' (s * R.b + (t + 1)) ∧ c'.nreg 311 = s ∧ c'.nreg 331 = R.σ s * R.k ∧
      c'.nreg 333 = s * R.b ∧ c'.rreg 304 = c₀.rmem (R.δb + R.ν s) := by
  have hI := hJ.rdIn hL hI₀
  have hbb : s * R.b + t < R.b * R.b := rm_lt hs ht
  obtain ⟨hr, h320, h300, h301, h302, h303, hn, hrm, hout, ho⟩ := hJ
  refine spec_use (eBody_exec (P := P) hL hWL c hc hI hs ht h312 h331 h333 h320 h300 h302 h303) ?_
  intro c' k hk hw ⟨g312, gnm, ⟨v, grm, hv0, hv1⟩, gn, gr, go⟩
  obtain ⟨e1, e2, e3, -⟩ := RdInv.reads hL ⟨hr, h320, h300, h301, h302, h303, hn, hrm, hout, ho⟩
    hs ht
  have hA := RdInv.A_eq (q := s * R.b + t) hL ⟨hr, h320, h300, h301, h302, h303, hn, hrm, hout,
    ho⟩ hs ht
  have := hL.wF; have := hL.wL
  refine ⟨hk, g312, ⟨fun r hr' => ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun a ha => ?_, ?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [gn r (by omega) (by omega) (by omega) (by omega), hr r hr']
  · rw [gn 320 (by omega) (by omega) (by omega) (by omega), h320]
  · rw [gr 300 (by omega), h300]
  · rw [gr 301 (by omega), h301]
  · rw [gr 302 (by omega), h302]
  · rw [gr 303 (by omega), h303]
  · rw [gnm, upd_other _ _ _ (by omega), hn a ha]
  · rw [grm, upd_other _ _ _ (by omega), hrm a ha]
  · intro s' hs' t' ht' hq
    rcases Nat.lt_succ_iff_lt_or_eq.1 (show s' * R.b + t' < s * R.b + t + 1 by omega) with h | h
    · obtain ⟨o1, o2, o3⟩ := hout s' hs' t' ht' h
      refine ⟨?_, fun hA' => ?_, fun hA' h0 => ?_⟩
      · rw [gnm, upd_other _ _ _ (by omega), o1]
      · rw [grm, upd_other _ _ _ (by omega), o2 hA']
      · rw [grm, upd_other _ _ _ (by omega), o3 hA' h0]
    · obtain ⟨rfl, rfl⟩ := rm_inj ht' ht h
      refine ⟨?_, fun hA' => ?_, fun hA' h0 => ?_⟩
      · rw [gnm, upd_same, hA]
      · rw [grm, upd_same]; exact hv0 (by rw [hA]; exact hA')
      · rw [grm, upd_same, hv1 (by rw [hA]; exact hA') (by rw [e2]; exact h0), e2, e3, h304]
  · rw [go, ho]
  · rw [gn 311 (by omega) (by omega) (by omega) (by omega), h311]
  · rw [gn 331 (by omega) (by omega) (by omega) (by omega), h331]
  · rw [gn 333 (by omega) (by omega) (by omega) (by omega), h333]
  · rw [gr 304 (by omega), h304]

theorem rRow_exec {R : Rd} (hL : RdLay R W) (hWL : R.Wr ≤ (2 : ℝ) ^ R.L) {c₀ : Config}
    (hI₀ : RdIn R c₀) (c : Config)
    (hc : WordsBounded W c) {s : ℕ} (hs : s < R.b) (hJ : RdInv R c₀ c (s * R.b))
    (h311 : c.nreg 311 = s) :
    ∃ c' k, Exec P W rRow c c' k ∧ k ≤ (8 * R.L + 32) * R.b + 12 ∧ c'.nreg 311 = s + 1 ∧
      RdInv R c₀ c' ((s + 1) * R.b) := by
  have hI := hJ.rdIn hL hI₀
  have := hL.wS; have := hL.wN; have := hL.wD; have := hL.wb; have := hL.wR
  have hσs := hL.σlt s hs
  have hνs := hL.νlt s hs
  have hσk : R.σ s * R.k ≤ R.k * R.k := Nat.mul_le_mul_right _ hσs.le
  have hsb : s * R.b ≤ R.b * R.b := Nat.mul_le_mul_right _ hs.le
  have hσ := hI.sg s hs
  have hν := hI.nb s hs
  obtain ⟨-, -, -, e4⟩ := hJ.reads hL hs hs
  unfold rRow
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [hI.r301, hI.r302, hI.r303, hI.r306,
    hI.r300, h311, hσ, hν]); omega)
  refine spec_seq ?_
  obtain ⟨hr, h320, h300, h301, h302, h303, hn, hrm, hout, ho⟩ := hJ
  let J : ℕ → Config → Prop := fun t c' =>
    RdInv R c₀ c' (s * R.b + t) ∧ c'.nreg 311 = s ∧ c'.nreg 331 = R.σ s * R.k ∧
      c'.nreg 333 = s * R.b ∧ c'.rreg 304 = c₀.rmem (R.δb + R.ν s)
  refine spec_use (forLoop_exec (P := P) (a := 312) (bR := 300) (body := eBody) J
    (K := 8 * R.L + 30) (n := R.b) _ ‹_› (by config_simp) (by config_simp; exact hI.r300) ?_
    (fun t c₁ ht hw ha hb ⟨hJ₁, g311, g331, g333, g304⟩ => by
      obtain ⟨c', k, e, hk, h1, hJ', h2, h3, h4, h5⟩ :=
        eBody_inv (P := P) hL hWL hI₀ c₁ hw hs ht hJ₁ ha g311 g331 g333 g304
      exact ⟨c', k, e, hk, h1, (hJ'.1 300 (by omega)).trans hI₀.r300, hJ', h2, h3, h4, h5⟩)) ?_
  · refine ⟨⟨fun r hr' => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
    all_goals config_simp
    all_goals try simp only [hI.r301, hI.r302, hI.r303, hI.r306, hI.r300, h311, hσ, hν]
    all_goals try assumption
    all_goals first
      | (simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr')
      | (intro s' hs' t' ht' hq; exact hout s' hs' t' ht' (by omega))
  intro c₂ k₂ hk₂ hw₂ hJ₂
  obtain ⟨_, ⟨hr₂, h320₂, h300₂, h301₂, h302₂, h303₂, hn₂, hrm₂, hout₂, ho₂⟩, g311, -, -, -⟩ :=
    hJ₂
  exec_block
  all_goals try ((try config_simp); (try simp only [g311, h320₂]); omega)
  config_simp
  simp only [g311, h320₂]
  refine ⟨by nlinarith, trivial, ⟨fun r hr' => ?_, h320₂, h300₂, h301₂, h302₂, h303₂, hn₂, hrm₂,
    fun s' hs' t' ht' hq => hout₂ s' hs' t' ht' (by nlinarith), ho₂⟩⟩
  simp only [upd_apply]; split_ifs <;> first | omega | exact hr₂ r hr'

/-! ### The program -/

/-- The constants: `r320 = 1`, the scale `2 ^ M` (`M = r310` doublings) in the real `r300`, the
top `2 ^ L / 2` (`L = r309`) in the real `r302`, `2` in the real `r303`. -/
def rdInit : Stmt :=
  .seq (block [.constN 320 1, .constR 300 1, .constR 302 1, .constR 303 2, .constN 321 0]) <|
  .seq (.whileLtN 321 310 (block [.addR 300 300 300, .addN 321 321 320])) <|
  .seq (.instr (.constN 321 0)) <|
  .seq (.whileLtN 321 309 (block [.addR 302 302 302, .addN 321 321 320]))
    (.instr (.divR 302 302 303))

theorem rdInit_exec {L M : ℕ} (c : Config) (hc : WordsBounded W c) (h310 : c.nreg 310 = M)
    (h309 : c.nreg 309 = L) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W rdInit c c' k ∧ k ≤ 4 * M + 4 * L + 11 ∧
      (c'.nreg 320 = 1 ∧ c'.rreg 300 = (2 : ℝ) ^ M ∧ c'.rreg 302 = (2 : ℝ) ^ L / 2 ∧
        c'.rreg 303 = 2 ∧ (∀ r, r ≠ 320 → r ≠ 321 → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 300 → r ≠ 302 → r ≠ 303 → c'.rreg r = c.rreg r) ∧ c'.nmem = c.nmem ∧
        c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hM : M ≤ W := h310 ▸ hc.1 310
  have hL : L ≤ W := h309 ▸ hc.1 309
  unfold rdInit
  refine spec_seq ?_
  exec_block
  all_goals try omega
  refine spec_seq ?_
  let J : ℕ → Config → Prop := fun i c' =>
    c'.rreg 300 = (2 : ℝ) ^ i ∧ c'.nreg 320 = 1 ∧ c'.rreg 302 = 1 ∧ c'.rreg 303 = 2 ∧
      (∀ r, r ≠ 320 → r ≠ 321 → c'.nreg r = c.nreg r) ∧
      (∀ r, r ≠ 300 → r ≠ 302 → r ≠ 303 → c'.rreg r = c.rreg r) ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 321) (bR := 310)
    (body := block [.addR 300 300 300, .addN 321 321 320]) J (K := 2) (n := M) _ ‹_›
    (by config_simp) (by config_simp; exact h310) ?_
    (fun i c₁ hi hw ha hb ⟨g300, g320, g302, g303, gn, gr, gnm, grm, go⟩ => by
      exec_block
      all_goals try ((try config_simp); (try simp only [ha, g320]); omega)
      dsimp only [J]
      config_simp
      simp only [ha, g320, g300, g302, g303]
      and_intros
      all_goals first
        | trivial
        | omega
        | assumption
        | (rw [pow_succ]; ring)
        | (intro r h1 h2; simp only [upd_apply]; split_ifs <;> first | omega | exact gn r h1 h2)
        | (intro r h1 h2 h3; simp only [upd_apply]; split_ifs <;> first | omega |
            exact gr r h1 h2 h3))) ?_
  · refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 => ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try simp
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
    · simp only [upd_apply]; split_ifs <;> first | omega | rfl
  intro c₂ k₂ hk₂ hw₂ ⟨_, g300, g320, g302, g303, gn, gr, gnm, grm, go⟩
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₂ 321 0 (by omega)) fun hw₃ => ?_
  refine spec_seq ?_
  let J' : ℕ → Config → Prop := fun i c' =>
    c'.rreg 300 = (2 : ℝ) ^ M ∧ c'.nreg 320 = 1 ∧ c'.rreg 302 = (2 : ℝ) ^ i ∧ c'.rreg 303 = 2 ∧
      (∀ r, r ≠ 320 → r ≠ 321 → c'.nreg r = c.nreg r) ∧
      (∀ r, r ≠ 300 → r ≠ 302 → r ≠ 303 → c'.rreg r = c.rreg r) ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 321) (bR := 309)
    (body := block [.addR 302 302 302, .addN 321 321 320]) J' (K := 2) (n := L) _ hw₃
    (by config_simp) (by config_simp; rw [gn 309 (by omega) (by omega), h309]) ?_
    (fun i c₁ hi hw ha hb ⟨g300, g320, g302, g303, gn, gr, gnm, grm, go⟩ => by
      exec_block
      all_goals try ((try config_simp); (try simp only [ha, g320]); omega)
      dsimp only [J']
      config_simp
      simp only [ha, g320, g300, g302, g303]
      and_intros
      all_goals first
        | trivial
        | omega
        | assumption
        | (rw [pow_succ]; ring)
        | (intro r h1 h2; simp only [upd_apply]; split_ifs <;> first | omega | exact gn r h1 h2)
        | (intro r h1 h2 h3; simp only [upd_apply]; split_ifs <;> first | omega |
            exact gr r h1 h2 h3))) ?_
  · refine ⟨?_, ?_, ?_, ?_, fun r h1 h2 => ?_, fun r h1 h2 h3 => ?_, gnm, grm, go⟩
    all_goals config_simp
    all_goals try simp only [g300, g320, g302, g303, pow_zero]
    · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r h1 h2
    · exact gr r h1 h2 h3
  intro c₄ k₄ hk₄ hw₄ ⟨_, g300', g320', g302', g303', gn', gr', gnm', grm', go'⟩
  refine spec_instr (Exec.divR hw₄ 302 302 303 (by rw [g303']; norm_num)) fun _ => ?_
  config_simp
  refine ⟨by omega, g320', g300', by rw [g302', g303'], g303', gn', fun r h1 h2 h3 => ?_, gnm',
    grm', go'⟩
  simp only [upd_apply]; split_ifs <;> first | omega | exact gr' r h1 h2 h3

/-- The cost bound of `rdProg`. -/
def rdCost (b L M : ℕ) : ℕ := 4 * M + 4 * L + 14 + 14 * b + (8 * L + 32) * (b * b)

/-- **The reading of Klein's answers.** -/
def rdProg : Stmt :=
  .seq rdInit (.seq (.instr (.constN 311 0)) (.whileLtN 311 300 rRow))

/-- **The reading of Klein's answers on the machine.** From `RdIn` (with `RdLay`, and the cut
below `2 ^ L`), `rdProg`
writes the output `Rd.Out` of every pair `(s, t)`, `s, t < b`, read from the answers in `c`, within
`rdCost b L M` steps, changing the memory only in the output regions `[Fb, Fb + b²)` (natural) and
`[Lb, Lb + b²)` (real), and keeping the data registers `r0 … r310` and the output. -/
theorem rdProg_exec {R : Rd} (hL : RdLay R W) (hWL : R.Wr ≤ (2 : ℝ) ^ R.L) (c : Config)
    (hc : WordsBounded W c)
    (hI : RdIn R c) :
    ∃ c' k, Exec P W rdProg c c' k ∧ k ≤ rdCost R.b R.L R.M ∧
      ((∀ s < R.b, ∀ t < R.b, R.Out c c' s t) ∧
        (∀ a, (a < R.Fb ∨ R.Fb + R.b * R.b ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ a, (a < R.Lb ∨ R.Lb + R.b * R.b ≤ a) → c'.rmem a = c.rmem a) ∧
        (∀ r, r < 311 → c'.nreg r = c.nreg r) ∧ c'.output = c.output) := by
  have := hL.wb
  unfold rdProg
  refine spec_seq ?_
  refine spec_use (rdInit_exec (P := P) c hc hI.r310 hI.r309 (by omega)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨g320, g300, g302, g303, gn, gr, gnm, grm, go⟩
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₁ 311 0 (by omega)) fun hw₂ => ?_
  let J : ℕ → Config → Prop := fun s c' => RdInv R c c' (s * R.b)
  have hb : R.b ≤ W := by nlinarith
  refine spec_use (forLoop_exec (P := P) (a := 311) (bR := 300) (body := rRow) J
    (K := (8 * R.L + 32) * R.b + 12) (n := R.b) _ hw₂ (by config_simp)
    (by config_simp; rw [gn 300 (by omega) (by omega), hI.r300]) ?_
    (fun s c₂ hs hw ha _ hJ => by
      obtain ⟨c', k, e, hk, h1, hJ'⟩ := rRow_exec (P := P) hL hWL hI c₂ hw hs hJ ha
      exact ⟨c', k, e, hk, h1, (hJ'.1 300 (by omega)).trans hI.r300, hJ'⟩)) ?_
  · refine ⟨fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, fun a _ => ?_, fun a _ => ?_, ?_, ?_⟩
    all_goals config_simp
    all_goals try assumption
    · simp only [upd_apply]; split_ifs <;> first | omega | exact gn r (by omega) (by omega)
    · exact gr 301 (by omega) (by omega) (by omega)
    · rw [gnm]
    · rw [grm]
    · intro s hs t ht hq; simp at hq
  intro c₃ k₃ hk₃ _ hJ₃
  obtain ⟨_, hr, -, -, -, -, -, hn, hrm, hout, ho⟩ := hJ₃
  refine ⟨?_, fun s hs t ht => hout s hs t ht (rm_lt hs ht), hn, hrm, hr, ho⟩
  unfold rdCost
  have : ((8 * R.L + 32) * R.b + 12 + 2) * R.b = (8 * R.L + 32) * (R.b * R.b) + 14 * R.b := by
    ring
  omega

end NegSSSP

end PlanarFlow
