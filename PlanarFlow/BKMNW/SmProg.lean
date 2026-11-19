module

public import PlanarFlow.BKMNW.SmSem
public import PlanarFlow.BKMNW.MbLab

/-!
# One step of `smD` on the machine: the classification scan

The per-dart arrays of a piece (an enumeration of `[0, n)`, see `SmStep.lean`): `PF` (the flags
of the piece), `RV` (the index of the reverse), `TH` (the hole label `hlab` of the tail), `KR`
(the rank `lrk` of the tail), `VT` (a vertex number of the tail). One scan `smA` over `i < n`
loads the eight words of `i` and of its reverse (`smA1`), computes the bits (`smA2a`, `smA2b`:
all by truncated subtraction, so `omega` decides them) of

* `p` (dart of the piece), `X` (`smX`: from a vertex off the terminals and the holes into a
  hole), `Y` (`smY`: leaving a hole), `B` (`smB`: from a vertex off the terminals and the holes),
  `I` (inside a hole),

counts `p` and `I`, and keeps, for each of `X`, `Y`, `B`, the first index with the bit set and
the words of the split it would make (`smTX`, `smTY`, `smTB`).

Registers (band `5300 … 5353`): `5300 = n`, `5301 = PFb`, `5302 = RVb`, `5303 = THb`,
`5304 = KRb`, `5305 = VTb`, `5310 = 1`, `5311 = 2`, `5313 = 0`, counter `5314`; written
`5315 … 5353`.

* the arithmetic `smSg`, `smEq`, `smAnd`, `smInn`, `smHst` and the per-index values `smPv`,
  `smXv`, `smYv`, `smBv`, `smIv`;
* `FstT` (the first index with a bit set, kept by a scan), `fstT_zero`, `fstT_step`;
* the blocks and **`smABody_exec`**, **`smA_exec`** (`(91 + 2) n + 2` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The arithmetic -/

/-- The sign. -/
abbrev smSg (x : ℕ) : ℕ := x - (x - 1)

/-- Equality as a bit. -/
abbrev smEq (x y : ℕ) : ℕ := 1 - ((x - y) + (y - x))

/-- The conjunction of a bit `x` and a bit `y`. -/
abbrev smAnd (x y : ℕ) : ℕ := x - (1 - y)

/-- A dart inside a hole, from the hole labels `t`, `h` of its ends. -/
abbrev smInn (t h : ℕ) : ℕ := smAnd (smSg t) (smEq t h)

/-- The head is a terminal, from its rank (`0` or `2`). -/
abbrev smHst (kh : ℕ) : ℕ := (1 - kh) + smEq kh 2

/-- The bit of a dart of the piece. -/
abbrev smPv (m : ℕ → ℕ) (PFb i : ℕ) : ℕ := smSg (m (PFb + i))

/-- The bit `X` (`smX`). -/
abbrev smXv (m : ℕ → ℕ) (PFb RVb THb KRb i : ℕ) : ℕ :=
  smAnd (smAnd (smSg (m (PFb + i))) (m (KRb + i) - 2)) (smSg (m (THb + m (RVb + i))))

/-- The bit `Y` (`smY`). -/
abbrev smYv (m : ℕ → ℕ) (PFb THb i : ℕ) : ℕ := smAnd (smSg (m (PFb + i))) (smSg (m (THb + i)))

/-- The bit `B` (`smB`). -/
abbrev smBv (m : ℕ → ℕ) (PFb KRb i : ℕ) : ℕ := smAnd (smSg (m (PFb + i))) (m (KRb + i) - 2)

/-- The bit `I` (a dart of the piece inside a hole). -/
abbrev smIv (m : ℕ → ℕ) (PFb RVb THb i : ℕ) : ℕ :=
  smAnd (smSg (m (PFb + i))) (smInn (m (THb + i)) (m (THb + m (RVb + i))))

lemma smSg_le (x : ℕ) : smSg x ≤ 1 := by unfold smSg; omega
lemma smAnd_le (x y : ℕ) : smAnd x y ≤ x := by unfold smAnd; omega

/-! ### The first index with a bit set -/

/-- **The first index `a < i` with `Q a = 1`**, kept with the flag `g`. -/
def FstT (Q : ℕ → ℕ) (i g a : ℕ) : Prop :=
  g ≤ 1 ∧ (g = 1 ↔ ∃ j < i, Q j = 1) ∧ (g = 1 → a < i ∧ Q a = 1 ∧ ∀ j < a, Q j ≠ 1)

lemma fstT_zero (Q : ℕ → ℕ) (a : ℕ) : FstT Q 0 0 a :=
  ⟨by omega, ⟨fun h => absurd h (by omega), fun ⟨j, hj, _⟩ => absurd hj (by omega)⟩,
    fun h => absurd h (by omega)⟩

lemma fstT_step {Q : ℕ → ℕ} {i g a a' : ℕ} (h : FstT Q i g a) (hq : Q i ≤ 1)
    (ha : a' = if Q i - g = 0 then a else i) : FstT Q (i + 1) (g + (Q i - g)) a' := by
  obtain ⟨h1, h2, h3⟩ := h
  rcases Nat.lt_or_ge g 1 with hg | hg
  · have hg0 : g = 0 := by omega
    subst hg0
    have hn : ∀ j < i, Q j ≠ 1 := fun j hj e => absurd (h2.2 ⟨j, hj, e⟩) (by omega)
    rcases Nat.lt_or_ge (Q i) 1 with hq0 | hq1
    · have : Q i = 0 := by omega
      rw [ha, this]
      simp only [Nat.sub_self, ↓reduceIte, add_zero]
      refine ⟨by omega, ⟨fun h => absurd h (by omega), fun ⟨j, hj, e⟩ => ?_⟩,
        fun h => absurd h (by omega)⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact (hn j hj e).elim
      · omega
    · have : Q i = 1 := by omega
      rw [ha, this]
      simp only [Nat.sub_zero, one_ne_zero, ↓reduceIte, zero_add]
      exact ⟨le_rfl, ⟨fun _ => ⟨i, by omega, this⟩, fun _ => rfl⟩,
        fun _ => ⟨by omega, this, hn⟩⟩
  · have hg1 : g = 1 := by omega
    subst hg1
    have hz : Q i - 1 = 0 := by omega
    rw [ha, hz]
    simp only [↓reduceIte, add_zero]
    obtain ⟨j, hj, e⟩ := h2.1 rfl
    obtain ⟨a1, a2, a3⟩ := h3 rfl
    exact ⟨le_rfl, ⟨fun _ => ⟨j, by omega, e⟩, fun _ => rfl⟩, fun _ => ⟨by omega, a2, a3⟩⟩

/-! ### The program -/

/-- The loads of the index `i = r5314` and its reverse `ri`: `5335 = PF[i]`, `5336 = ri`,
`5337 = TH[i]`, `5338 = TH[ri]`, `5339 = KR[i]`, `5340 = KR[ri]`, `5341 = VT[i]`,
`5342 = VT[ri]`. -/
def smA1 : Stmt :=
  block [.addN 5334 5301 5314, .loadN 5335 5334, .addN 5334 5302 5314, .loadN 5336 5334,
    .addN 5334 5303 5314, .loadN 5337 5334, .addN 5334 5303 5336, .loadN 5338 5334,
    .addN 5334 5304 5314, .loadN 5339 5334, .addN 5334 5304 5336, .loadN 5340 5334,
    .addN 5334 5305 5314, .loadN 5341 5334, .addN 5334 5305 5336, .loadN 5342 5334]

/-- The bits of the index: `5335 = p`, `5343 = [t ≠ 0]`, `5344 = [h ≠ 0]`, `5345` inside a hole,
`5346 = [KR = 3]`, `5347` the head a terminal. -/
def smA2a : Stmt :=
  block [.subN 5353 5335 5310, .subN 5335 5335 5353,
    .subN 5353 5337 5310, .subN 5343 5337 5353,
    .subN 5353 5338 5310, .subN 5344 5338 5353,
    .subN 5353 5337 5338, .subN 5345 5338 5337, .addN 5353 5353 5345, .subN 5345 5310 5353,
    .subN 5353 5310 5345, .subN 5345 5343 5353,
    .subN 5346 5339 5311,
    .subN 5347 5310 5340, .subN 5353 5340 5311, .subN 5348 5311 5340, .addN 5353 5353 5348,
    .subN 5348 5310 5353, .addN 5347 5347 5348]

/-- The bits `5350 = B`, `5348 = X`, `5349 = Y`, `5351 = I`. -/
def smA2b : Stmt :=
  block [.subN 5353 5310 5346, .subN 5350 5335 5353,
    .subN 5353 5310 5344, .subN 5348 5350 5353,
    .subN 5353 5310 5343, .subN 5349 5335 5353,
    .subN 5353 5310 5345, .subN 5351 5335 5353]

/-- The first `X`: flag `5317`, index `5318`, `5319 = ri`, `5320 = VT[i]`, `5321 = VT[ri]`,
`5322 = TH[ri]`. -/
def smTX : Stmt :=
  .seq (block [.subN 5352 5348 5317])
    (.seq (.ifLtN 5313 5352 (block [.copyN 5318 5314, .copyN 5319 5336, .copyN 5320 5341,
      .copyN 5321 5342, .copyN 5322 5338]) .skip) (block [.addN 5317 5317 5352]))

/-- The first `Y`: flag `5323`, index `5324`, `5325 = VT[i]`, `5326 = TH[i]`. -/
def smTY : Stmt :=
  .seq (block [.subN 5352 5349 5323])
    (.seq (.ifLtN 5313 5352 (block [.copyN 5324 5314, .copyN 5325 5341, .copyN 5326 5337])
      .skip) (block [.addN 5323 5323 5352]))

/-- The first `B`: flag `5327`, index `5328`, `5329 = ri`, `5330 = VT[i]`, `5331 = VT[ri]`,
`5332` the head a terminal, `5333 = TH[ri]`. -/
def smTB : Stmt :=
  .seq (block [.subN 5352 5350 5327])
    (.seq (.ifLtN 5313 5352 (block [.copyN 5328 5314, .copyN 5329 5336, .copyN 5330 5341,
      .copyN 5331 5342, .copyN 5332 5347, .copyN 5333 5338]) .skip)
      (block [.addN 5327 5327 5352]))

/-- The counts `5315 += p`, `5316 += I`, and the next index. -/
def smA3 : Stmt := block [.addN 5315 5315 5335, .addN 5316 5316 5351, .addN 5314 5314 5310]

/-- One index of the classification scan. -/
def smABody : Stmt :=
  .seq smA1 (.seq smA2a (.seq smA2b (.seq smTX (.seq smTY (.seq smTB smA3)))))

/-- **The classification scan.** -/
def smA : Stmt :=
  .seq (block [.constN 5310 1, .constN 5311 2, .constN 5313 0, .constN 5314 0, .constN 5315 0,
    .constN 5316 0, .constN 5317 0, .constN 5323 0, .constN 5327 0]) (.whileLtN 5314 5300 smABody)

section A

variable {P : Input} {W : ℕ}

theorem smA1_exec (c : Config) (hc : WordsBounded W c) {PFb RVb THb KRb VTb i : ℕ}
    (r1 : c.nreg 5301 = PFb) (r2 : c.nreg 5302 = RVb) (r3 : c.nreg 5303 = THb)
    (r4 : c.nreg 5304 = KRb) (r5 : c.nreg 5305 = VTb) (r14 : c.nreg 5314 = i)
    (w1 : PFb + i ≤ W) (w2 : RVb + i ≤ W) (w3 : THb + i ≤ W) (w4 : KRb + i ≤ W)
    (w5 : VTb + i ≤ W) (w6 : THb + c.nmem (RVb + i) ≤ W) (w7 : KRb + c.nmem (RVb + i) ≤ W)
    (w8 : VTb + c.nmem (RVb + i) ≤ W) :
    ∃ c' t, Exec P W smA1 c c' t ∧ t = 16 ∧ c'.nreg 5335 = c.nmem (PFb + i) ∧
      c'.nreg 5336 = c.nmem (RVb + i) ∧ c'.nreg 5337 = c.nmem (THb + i) ∧
      c'.nreg 5338 = c.nmem (THb + c.nmem (RVb + i)) ∧ c'.nreg 5339 = c.nmem (KRb + i) ∧
      c'.nreg 5340 = c.nmem (KRb + c.nmem (RVb + i)) ∧ c'.nreg 5341 = c.nmem (VTb + i) ∧
      c'.nreg 5342 = c.nmem (VTb + c.nmem (RVb + i)) ∧
      (∀ x, (x < 5334 ∨ 5342 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smA1
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r14]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5, r14]; done)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem smA2a_exec (c : Config) (hc : WordsBounded W c) {p0 t h kr kh : ℕ} (hW : 2 ≤ W)
    (r10 : c.nreg 5310 = 1) (r11 : c.nreg 5311 = 2) (r35 : c.nreg 5335 = p0)
    (r37 : c.nreg 5337 = t) (r38 : c.nreg 5338 = h) (r39 : c.nreg 5339 = kr)
    (r40 : c.nreg 5340 = kh) :
    ∃ c' t', Exec P W smA2a c c' t' ∧ t' = 19 ∧ c'.nreg 5335 = smSg p0 ∧
      c'.nreg 5343 = smSg t ∧ c'.nreg 5344 = smSg h ∧ c'.nreg 5345 = smInn t h ∧
      c'.nreg 5346 = kr - 2 ∧ c'.nreg 5347 = smHst kh ∧
      (∀ x, (x < 5335 ∨ (5335 < x ∧ x < 5343) ∨ (5348 < x ∧ x < 5353) ∨ 5353 < x) →
        c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b1 := hc.1 5337
  have b2 := hc.1 5338
  have b3 := hc.1 5340
  rw [r37] at b1; rw [r38] at b2; rw [r40] at b3
  unfold smA2a
  exec_block
  all_goals try (config_simp; simp only [r10, r11, r35, r37, r38, r39, r40]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; simp only [r10, r11, r35, r37, r38, r39, r40]; done)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem smA2b_exec (c : Config) (hc : WordsBounded W c) {p tz hz inn bad : ℕ}
    (r10 : c.nreg 5310 = 1) (r35 : c.nreg 5335 = p) (r43 : c.nreg 5343 = tz)
    (r44 : c.nreg 5344 = hz) (r45 : c.nreg 5345 = inn) (r46 : c.nreg 5346 = bad) :
    ∃ c' t', Exec P W smA2b c c' t' ∧ t' = 8 ∧ c'.nreg 5350 = smAnd p bad ∧
      c'.nreg 5348 = smAnd (smAnd p bad) hz ∧ c'.nreg 5349 = smAnd p tz ∧
      c'.nreg 5351 = smAnd p inn ∧
      (∀ x, (x < 5348 ∨ (5351 < x ∧ x < 5353) ∨ 5353 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have b1 := hc.1 5335
  rw [r35] at b1
  unfold smA2b
  exec_block
  all_goals try (config_simp; simp only [r10, r35, r43, r44, r45, r46]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; simp only [r10, r35, r43, r44, r45, r46]; done)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem smTX_exec (c : Config) (hc : WordsBounded W c) {X g : ℕ}
    (r13 : c.nreg 5313 = 0) (rq : c.nreg 5348 = X) (rg : c.nreg 5317 = g) (hW : 2 ≤ W)
    (hq : X ≤ 1) (hg : g ≤ 1) :
    ∃ c' t, Exec P W smTX c c' t ∧ t ≤ 8 ∧ c'.nreg 5317 = g + (X - g) ∧
      c'.nreg 5318 = (if X - g = 0 then c.nreg 5318 else c.nreg 5314) ∧
      c'.nreg 5319 = (if X - g = 0 then c.nreg 5319 else c.nreg 5336) ∧
      c'.nreg 5320 = (if X - g = 0 then c.nreg 5320 else c.nreg 5341) ∧
      c'.nreg 5321 = (if X - g = 0 then c.nreg 5321 else c.nreg 5342) ∧
      c'.nreg 5322 = (if X - g = 0 then c.nreg 5322 else c.nreg 5338) ∧
      (∀ x, (x < 5317 ∨ (5317 < x ∧ x < 5318) ∨ (5322 < x ∧ x < 5352) ∨ 5352 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smTX
  obtain ⟨c₁, t₁, e₁, ht₁, a52, an₁, am₁, ar₁, arm₁, ao₁⟩ : ∃ c₁ t₁,
      Exec P W (block [.subN 5352 5348 5317]) c c₁ t₁ ∧ t₁ = 1 ∧ c₁.nreg 5352 = X - g ∧
      (∀ x, x ≠ 5352 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧
      c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have b := hc.1 5348
    exec_block
    all_goals try (config_simp; simp only [rq, rg]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [rq, rg]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, t₂, e₂, ht₂, b5318, b5319, b5320, b5321, b5322, bn₂, bm₂, br₂, brm₂, bo₂⟩ : ∃ c₂ t₂,
      Exec P W (.ifLtN 5313 5352 (block [.copyN 5318 5314, .copyN 5319 5336, .copyN 5320 5341, .copyN 5321 5342, .copyN 5322 5338]) .skip) c₁ c₂ t₂ ∧ t₂ ≤ 6 ∧
      c₂.nreg 5318 = (if X - g = 0 then c.nreg 5318 else c.nreg 5314) ∧
      c₂.nreg 5319 = (if X - g = 0 then c.nreg 5319 else c.nreg 5336) ∧
      c₂.nreg 5320 = (if X - g = 0 then c.nreg 5320 else c.nreg 5341) ∧
      c₂.nreg 5321 = (if X - g = 0 then c.nreg 5321 else c.nreg 5342) ∧
      c₂.nreg 5322 = (if X - g = 0 then c.nreg 5322 else c.nreg 5338) ∧
      (∀ x, (x < 5318 ∨ 5322 < x) → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases hu : X - g = 0
    · have hlt : ¬ c₁.nreg 5313 < c₁.nreg 5352 := by rw [a52, an₁ _ (by omega), r13]; omega
      refine ⟨c₁, 2, .ifLtN_false hlt (.skip hw₁), by omega, ?_, ?_, ?_, ?_, ?_,
        fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      all_goals rw [iteT hu, an₁ _ (by omega)]
    · have hlt : c₁.nreg 5313 < c₁.nreg 5352 := by rw [a52, an₁ _ (by omega), r13]; omega
      obtain ⟨c₂, t₂, e₂, ht₂, d5318, d5319, d5320, d5321, d5322, dn₂, dm₂, dr₂, drm₂, do₂⟩ : ∃ c₂ t₂,
          Exec P W (block [.copyN 5318 5314, .copyN 5319 5336, .copyN 5320 5341, .copyN 5321 5342, .copyN 5322 5338]) c₁ c₂ t₂ ∧ t₂ = 5 ∧
          c₂.nreg 5318 = c₁.nreg 5314 ∧
          c₂.nreg 5319 = c₁.nreg 5336 ∧
          c₂.nreg 5320 = c₁.nreg 5341 ∧
          c₂.nreg 5321 = c₁.nreg 5342 ∧
          c₂.nreg 5322 = c₁.nreg 5338 ∧
          (∀ x, (x < 5318 ∨ 5322 < x) → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
          c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
        exec_block
        all_goals try (config_simp; omega)
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        all_goals try (config_simp; done)
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c₂, t₂ + 1, .ifLtN_true hlt e₂, by omega, ?_, ?_, ?_, ?_, ?_, dn₂, dm₂, dr₂, drm₂, do₂⟩
      · rw [iteF hu, d5318, an₁ _ (by omega)]
      · rw [iteF hu, d5319, an₁ _ (by omega)]
      · rw [iteF hu, d5320, an₁ _ (by omega)]
      · rw [iteF hu, d5321, an₁ _ (by omega)]
      · rw [iteF hu, d5322, an₁ _ (by omega)]
  have hw₂ := e₂.wb_right
  have k52 : c₂.nreg 5352 = X - g := by rw [bn₂ _ (by omega), a52]
  have kg : c₂.nreg 5317 = g := by rw [bn₂ _ (by omega), an₁ _ (by omega), rg]
  obtain ⟨c₃, t₃, e₃, ht₃, f1, fn₃, fm₃, fr₃, frm₃, fo₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 5317 5317 5352]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 5317 = g + (X - g) ∧
      (∀ x, x ≠ 5317 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try (config_simp; simp only [k52, kg]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [k52, kg]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, f1, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_,
    by rw [fm₃, bm₂, am₁], by rw [fr₃, br₂, ar₁], by rw [frm₃, brm₂, arm₁], by rw [fo₃, bo₂, ao₁]⟩
  · rw [fn₃ _ (by omega), b5318]
  · rw [fn₃ _ (by omega), b5319]
  · rw [fn₃ _ (by omega), b5320]
  · rw [fn₃ _ (by omega), b5321]
  · rw [fn₃ _ (by omega), b5322]
  · rw [fn₃ _ (by omega), bn₂ _ (by omega), an₁ _ (by omega)]

theorem smTY_exec (c : Config) (hc : WordsBounded W c) {Y g : ℕ}
    (r13 : c.nreg 5313 = 0) (rq : c.nreg 5349 = Y) (rg : c.nreg 5323 = g) (hW : 2 ≤ W)
    (hq : Y ≤ 1) (hg : g ≤ 1) :
    ∃ c' t, Exec P W smTY c c' t ∧ t ≤ 6 ∧ c'.nreg 5323 = g + (Y - g) ∧
      c'.nreg 5324 = (if Y - g = 0 then c.nreg 5324 else c.nreg 5314) ∧
      c'.nreg 5325 = (if Y - g = 0 then c.nreg 5325 else c.nreg 5341) ∧
      c'.nreg 5326 = (if Y - g = 0 then c.nreg 5326 else c.nreg 5337) ∧
      (∀ x, (x < 5323 ∨ (5323 < x ∧ x < 5324) ∨ (5326 < x ∧ x < 5352) ∨ 5352 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smTY
  obtain ⟨c₁, t₁, e₁, ht₁, a52, an₁, am₁, ar₁, arm₁, ao₁⟩ : ∃ c₁ t₁,
      Exec P W (block [.subN 5352 5349 5323]) c c₁ t₁ ∧ t₁ = 1 ∧ c₁.nreg 5352 = Y - g ∧
      (∀ x, x ≠ 5352 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧
      c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have b := hc.1 5349
    exec_block
    all_goals try (config_simp; simp only [rq, rg]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [rq, rg]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, t₂, e₂, ht₂, b5324, b5325, b5326, bn₂, bm₂, br₂, brm₂, bo₂⟩ : ∃ c₂ t₂,
      Exec P W (.ifLtN 5313 5352 (block [.copyN 5324 5314, .copyN 5325 5341, .copyN 5326 5337]) .skip) c₁ c₂ t₂ ∧ t₂ ≤ 4 ∧
      c₂.nreg 5324 = (if Y - g = 0 then c.nreg 5324 else c.nreg 5314) ∧
      c₂.nreg 5325 = (if Y - g = 0 then c.nreg 5325 else c.nreg 5341) ∧
      c₂.nreg 5326 = (if Y - g = 0 then c.nreg 5326 else c.nreg 5337) ∧
      (∀ x, (x < 5324 ∨ 5326 < x) → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases hu : Y - g = 0
    · have hlt : ¬ c₁.nreg 5313 < c₁.nreg 5352 := by rw [a52, an₁ _ (by omega), r13]; omega
      refine ⟨c₁, 2, .ifLtN_false hlt (.skip hw₁), by omega, ?_, ?_, ?_,
        fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      all_goals rw [iteT hu, an₁ _ (by omega)]
    · have hlt : c₁.nreg 5313 < c₁.nreg 5352 := by rw [a52, an₁ _ (by omega), r13]; omega
      obtain ⟨c₂, t₂, e₂, ht₂, d5324, d5325, d5326, dn₂, dm₂, dr₂, drm₂, do₂⟩ : ∃ c₂ t₂,
          Exec P W (block [.copyN 5324 5314, .copyN 5325 5341, .copyN 5326 5337]) c₁ c₂ t₂ ∧ t₂ = 3 ∧
          c₂.nreg 5324 = c₁.nreg 5314 ∧
          c₂.nreg 5325 = c₁.nreg 5341 ∧
          c₂.nreg 5326 = c₁.nreg 5337 ∧
          (∀ x, (x < 5324 ∨ 5326 < x) → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
          c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
        exec_block
        all_goals try (config_simp; omega)
        refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        all_goals try (config_simp; done)
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c₂, t₂ + 1, .ifLtN_true hlt e₂, by omega, ?_, ?_, ?_, dn₂, dm₂, dr₂, drm₂, do₂⟩
      · rw [iteF hu, d5324, an₁ _ (by omega)]
      · rw [iteF hu, d5325, an₁ _ (by omega)]
      · rw [iteF hu, d5326, an₁ _ (by omega)]
  have hw₂ := e₂.wb_right
  have k52 : c₂.nreg 5352 = Y - g := by rw [bn₂ _ (by omega), a52]
  have kg : c₂.nreg 5323 = g := by rw [bn₂ _ (by omega), an₁ _ (by omega), rg]
  obtain ⟨c₃, t₃, e₃, ht₃, f1, fn₃, fm₃, fr₃, frm₃, fo₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 5323 5323 5352]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 5323 = g + (Y - g) ∧
      (∀ x, x ≠ 5323 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try (config_simp; simp only [k52, kg]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [k52, kg]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, f1, ?_, ?_, ?_, fun x hx => ?_,
    by rw [fm₃, bm₂, am₁], by rw [fr₃, br₂, ar₁], by rw [frm₃, brm₂, arm₁], by rw [fo₃, bo₂, ao₁]⟩
  · rw [fn₃ _ (by omega), b5324]
  · rw [fn₃ _ (by omega), b5325]
  · rw [fn₃ _ (by omega), b5326]
  · rw [fn₃ _ (by omega), bn₂ _ (by omega), an₁ _ (by omega)]

theorem smTB_exec (c : Config) (hc : WordsBounded W c) {B g : ℕ}
    (r13 : c.nreg 5313 = 0) (rq : c.nreg 5350 = B) (rg : c.nreg 5327 = g) (hW : 2 ≤ W)
    (hq : B ≤ 1) (hg : g ≤ 1) :
    ∃ c' t, Exec P W smTB c c' t ∧ t ≤ 9 ∧ c'.nreg 5327 = g + (B - g) ∧
      c'.nreg 5328 = (if B - g = 0 then c.nreg 5328 else c.nreg 5314) ∧
      c'.nreg 5329 = (if B - g = 0 then c.nreg 5329 else c.nreg 5336) ∧
      c'.nreg 5330 = (if B - g = 0 then c.nreg 5330 else c.nreg 5341) ∧
      c'.nreg 5331 = (if B - g = 0 then c.nreg 5331 else c.nreg 5342) ∧
      c'.nreg 5332 = (if B - g = 0 then c.nreg 5332 else c.nreg 5347) ∧
      c'.nreg 5333 = (if B - g = 0 then c.nreg 5333 else c.nreg 5338) ∧
      (∀ x, (x < 5327 ∨ (5327 < x ∧ x < 5328) ∨ (5333 < x ∧ x < 5352) ∨ 5352 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smTB
  obtain ⟨c₁, t₁, e₁, ht₁, a52, an₁, am₁, ar₁, arm₁, ao₁⟩ : ∃ c₁ t₁,
      Exec P W (block [.subN 5352 5350 5327]) c c₁ t₁ ∧ t₁ = 1 ∧ c₁.nreg 5352 = B - g ∧
      (∀ x, x ≠ 5352 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧
      c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have b := hc.1 5350
    exec_block
    all_goals try (config_simp; simp only [rq, rg]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [rq, rg]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, t₂, e₂, ht₂, b5328, b5329, b5330, b5331, b5332, b5333, bn₂, bm₂, br₂, brm₂, bo₂⟩ : ∃ c₂ t₂,
      Exec P W (.ifLtN 5313 5352 (block [.copyN 5328 5314, .copyN 5329 5336, .copyN 5330 5341, .copyN 5331 5342, .copyN 5332 5347, .copyN 5333 5338]) .skip) c₁ c₂ t₂ ∧ t₂ ≤ 7 ∧
      c₂.nreg 5328 = (if B - g = 0 then c.nreg 5328 else c.nreg 5314) ∧
      c₂.nreg 5329 = (if B - g = 0 then c.nreg 5329 else c.nreg 5336) ∧
      c₂.nreg 5330 = (if B - g = 0 then c.nreg 5330 else c.nreg 5341) ∧
      c₂.nreg 5331 = (if B - g = 0 then c.nreg 5331 else c.nreg 5342) ∧
      c₂.nreg 5332 = (if B - g = 0 then c.nreg 5332 else c.nreg 5347) ∧
      c₂.nreg 5333 = (if B - g = 0 then c.nreg 5333 else c.nreg 5338) ∧
      (∀ x, (x < 5328 ∨ 5333 < x) → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases hu : B - g = 0
    · have hlt : ¬ c₁.nreg 5313 < c₁.nreg 5352 := by rw [a52, an₁ _ (by omega), r13]; omega
      refine ⟨c₁, 2, .ifLtN_false hlt (.skip hw₁), by omega, ?_, ?_, ?_, ?_, ?_, ?_,
        fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
      all_goals rw [iteT hu, an₁ _ (by omega)]
    · have hlt : c₁.nreg 5313 < c₁.nreg 5352 := by rw [a52, an₁ _ (by omega), r13]; omega
      obtain ⟨c₂, t₂, e₂, ht₂, d5328, d5329, d5330, d5331, d5332, d5333, dn₂, dm₂, dr₂, drm₂, do₂⟩ : ∃ c₂ t₂,
          Exec P W (block [.copyN 5328 5314, .copyN 5329 5336, .copyN 5330 5341, .copyN 5331 5342, .copyN 5332 5347, .copyN 5333 5338]) c₁ c₂ t₂ ∧ t₂ = 6 ∧
          c₂.nreg 5328 = c₁.nreg 5314 ∧
          c₂.nreg 5329 = c₁.nreg 5336 ∧
          c₂.nreg 5330 = c₁.nreg 5341 ∧
          c₂.nreg 5331 = c₁.nreg 5342 ∧
          c₂.nreg 5332 = c₁.nreg 5347 ∧
          c₂.nreg 5333 = c₁.nreg 5338 ∧
          (∀ x, (x < 5328 ∨ 5333 < x) → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
          c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
        exec_block
        all_goals try (config_simp; omega)
        refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        all_goals try (config_simp; done)
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c₂, t₂ + 1, .ifLtN_true hlt e₂, by omega, ?_, ?_, ?_, ?_, ?_, ?_, dn₂, dm₂, dr₂, drm₂, do₂⟩
      · rw [iteF hu, d5328, an₁ _ (by omega)]
      · rw [iteF hu, d5329, an₁ _ (by omega)]
      · rw [iteF hu, d5330, an₁ _ (by omega)]
      · rw [iteF hu, d5331, an₁ _ (by omega)]
      · rw [iteF hu, d5332, an₁ _ (by omega)]
      · rw [iteF hu, d5333, an₁ _ (by omega)]
  have hw₂ := e₂.wb_right
  have k52 : c₂.nreg 5352 = B - g := by rw [bn₂ _ (by omega), a52]
  have kg : c₂.nreg 5327 = g := by rw [bn₂ _ (by omega), an₁ _ (by omega), rg]
  obtain ⟨c₃, t₃, e₃, ht₃, f1, fn₃, fm₃, fr₃, frm₃, fo₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 5327 5327 5352]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 5327 = g + (B - g) ∧
      (∀ x, x ≠ 5327 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try (config_simp; simp only [k52, kg]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [k52, kg]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, f1, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_,
    by rw [fm₃, bm₂, am₁], by rw [fr₃, br₂, ar₁], by rw [frm₃, brm₂, arm₁], by rw [fo₃, bo₂, ao₁]⟩
  · rw [fn₃ _ (by omega), b5328]
  · rw [fn₃ _ (by omega), b5329]
  · rw [fn₃ _ (by omega), b5330]
  · rw [fn₃ _ (by omega), b5331]
  · rw [fn₃ _ (by omega), b5332]
  · rw [fn₃ _ (by omega), b5333]
  · rw [fn₃ _ (by omega), bn₂ _ (by omega), an₁ _ (by omega)]


theorem smA3_exec (c : Config) (hc : WordsBounded W c) {cP cI p I i : ℕ}
    (r10 : c.nreg 5310 = 1) (r14 : c.nreg 5314 = i) (r15 : c.nreg 5315 = cP)
    (r16 : c.nreg 5316 = cI) (r35 : c.nreg 5335 = p) (r51 : c.nreg 5351 = I)
    (w1 : cP + p ≤ W) (w2 : cI + I ≤ W) (w3 : i + 1 ≤ W) :
    ∃ c' t, Exec P W smA3 c c' t ∧ t = 3 ∧ c'.nreg 5314 = i + 1 ∧ c'.nreg 5315 = cP + p ∧
      c'.nreg 5316 = cI + I ∧ (∀ x, (x < 5314 ∨ 5316 < x) → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smA3
  exec_block
  all_goals try (config_simp; simp only [r10, r14, r15, r16, r35, r51]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; simp only [r10, r14, r15, r16, r35, r51]; done)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

set_option maxHeartbeats 1600000 in
/-- **One index of the classification scan.** -/
theorem smABody_exec (c : Config) (hc : WordsBounded W c) {PFb RVb THb KRb VTb i cP cI : ℕ}
    (r1 : c.nreg 5301 = PFb) (r2 : c.nreg 5302 = RVb) (r3 : c.nreg 5303 = THb)
    (r4 : c.nreg 5304 = KRb) (r5 : c.nreg 5305 = VTb) (r10 : c.nreg 5310 = 1)
    (r11 : c.nreg 5311 = 2) (r13 : c.nreg 5313 = 0) (r14 : c.nreg 5314 = i)
    (r15 : c.nreg 5315 = cP) (r16 : c.nreg 5316 = cI) (g1 : c.nreg 5317 ≤ 1)
    (g2 : c.nreg 5323 ≤ 1) (g3 : c.nreg 5327 ≤ 1) (hW : 2 ≤ W)
    (w1 : PFb + i ≤ W) (w2 : RVb + i ≤ W) (w3 : THb + i ≤ W) (w4 : KRb + i ≤ W)
    (w5 : VTb + i ≤ W) (w6 : THb + c.nmem (RVb + i) ≤ W) (w7 : KRb + c.nmem (RVb + i) ≤ W)
    (w8 : VTb + c.nmem (RVb + i) ≤ W) (w9 : cP + 1 ≤ W) (w10 : cI + 1 ≤ W) (w11 : i + 1 ≤ W) :
    ∃ c' t, Exec P W smABody c c' t ∧ t ≤ 91 ∧ c'.nreg 5314 = i + 1 ∧
      c'.nreg 5315 = cP + smPv c.nmem PFb i ∧ c'.nreg 5316 = cI + smIv c.nmem PFb RVb THb i ∧
      c'.nreg 5317 = c.nreg 5317 + (smXv c.nmem PFb RVb THb KRb i - c.nreg 5317) ∧
      c'.nreg 5318 = (if smXv c.nmem PFb RVb THb KRb i - c.nreg 5317 = 0 then c.nreg 5318
        else i) ∧
      c'.nreg 5319 = (if smXv c.nmem PFb RVb THb KRb i - c.nreg 5317 = 0 then c.nreg 5319
        else c.nmem (RVb + i)) ∧
      c'.nreg 5320 = (if smXv c.nmem PFb RVb THb KRb i - c.nreg 5317 = 0 then c.nreg 5320
        else c.nmem (VTb + i)) ∧
      c'.nreg 5321 = (if smXv c.nmem PFb RVb THb KRb i - c.nreg 5317 = 0 then c.nreg 5321
        else c.nmem (VTb + c.nmem (RVb + i))) ∧
      c'.nreg 5322 = (if smXv c.nmem PFb RVb THb KRb i - c.nreg 5317 = 0 then c.nreg 5322
        else c.nmem (THb + c.nmem (RVb + i))) ∧
      c'.nreg 5323 = c.nreg 5323 + (smYv c.nmem PFb THb i - c.nreg 5323) ∧
      c'.nreg 5324 = (if smYv c.nmem PFb THb i - c.nreg 5323 = 0 then c.nreg 5324 else i) ∧
      c'.nreg 5325 = (if smYv c.nmem PFb THb i - c.nreg 5323 = 0 then c.nreg 5325
        else c.nmem (VTb + i)) ∧
      c'.nreg 5326 = (if smYv c.nmem PFb THb i - c.nreg 5323 = 0 then c.nreg 5326
        else c.nmem (THb + i)) ∧
      c'.nreg 5327 = c.nreg 5327 + (smBv c.nmem PFb KRb i - c.nreg 5327) ∧
      c'.nreg 5328 = (if smBv c.nmem PFb KRb i - c.nreg 5327 = 0 then c.nreg 5328 else i) ∧
      c'.nreg 5329 = (if smBv c.nmem PFb KRb i - c.nreg 5327 = 0 then c.nreg 5329
        else c.nmem (RVb + i)) ∧
      c'.nreg 5330 = (if smBv c.nmem PFb KRb i - c.nreg 5327 = 0 then c.nreg 5330
        else c.nmem (VTb + i)) ∧
      c'.nreg 5331 = (if smBv c.nmem PFb KRb i - c.nreg 5327 = 0 then c.nreg 5331
        else c.nmem (VTb + c.nmem (RVb + i))) ∧
      c'.nreg 5332 = (if smBv c.nmem PFb KRb i - c.nreg 5327 = 0 then c.nreg 5332
        else smHst (c.nmem (KRb + c.nmem (RVb + i)))) ∧
      c'.nreg 5333 = (if smBv c.nmem PFb KRb i - c.nreg 5327 = 0 then c.nreg 5333
        else c.nmem (THb + c.nmem (RVb + i))) ∧
      (∀ x, (x < 5314 ∨ 5353 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, l35, l36, l37, l38, l39, l40, l41, l42, n₁, m₁, rr₁, rm₁, o₁⟩ :=
    smA1_exec (P := P) c hc r1 r2 r3 r4 r5 r14 w1 w2 w3 w4 w5 w6 w7 w8
  have hw₁ := e₁.wb_right
  have q₁ : ∀ x, (x < 5334 ∨ 5342 < x) → c₁.nreg x = c.nreg x := n₁
  obtain ⟨c₂, t₂, e₂, ht₂, f35, f43, f44, f45, f46, f47, n₂, m₂, rr₂, rm₂, o₂⟩ :=
    smA2a_exec (P := P) c₁ hw₁ hW (by rw [q₁ _ (by omega), r10]) (by rw [q₁ _ (by omega), r11])
      l35 l37 l38 l39 l40
  have hw₂ := e₂.wb_right
  have q₂ : ∀ x, (x < 5335 ∨ (5335 < x ∧ x < 5343) ∨ (5348 < x ∧ x < 5353) ∨ 5353 < x) →
      c₂.nreg x = c₁.nreg x := n₂
  obtain ⟨c₃, t₃, e₃, ht₃, h50, h48, h49, h51, n₃, m₃, rr₃, rm₃, o₃⟩ :=
    smA2b_exec (P := P) c₂ hw₂ (by rw [q₂ _ (by omega), q₁ _ (by omega), r10]) f35 f43 f44 f45 f46
  have hw₃ := e₃.wb_right
  have q₃ : ∀ x, (x < 5348 ∨ (5351 < x ∧ x < 5353) ∨ 5353 < x) → c₃.nreg x = c₂.nreg x := n₃
  -- registers of `c` seen at `c₃`
  have s₃ : ∀ x, (x < 5334 ∨ 5353 < x) → c₃.nreg x = c.nreg x := fun x hx => by
    rw [q₃ _ (by omega), q₂ _ (by omega), q₁ _ (by omega)]
  have hX1 : smAnd (smAnd (smSg (c.nmem (PFb + i))) (c.nmem (KRb + i) - 2))
      (smSg (c.nmem (THb + c.nmem (RVb + i)))) ≤ 1 := by unfold smAnd smSg; omega
  obtain ⟨c₄, t₄, e₄, ht₄, x17, x18, x19, x20, x21, x22, n₄, m₄, rr₄, rm₄, o₄⟩ :=
    smTX_exec (P := P) c₃ hw₃ (by rw [s₃ _ (by omega), r13]) h48 (s₃ _ (by omega)) hW hX1
      g1
  have hw₄ := e₄.wb_right
  have q₄ : ∀ x, (x < 5317 ∨ (5322 < x ∧ x < 5352) ∨ 5352 < x) → c₄.nreg x = c₃.nreg x := fun x hx => n₄ x (by omega)
  have hY1 : smAnd (smSg (c.nmem (PFb + i))) (smSg (c.nmem (THb + i))) ≤ 1 := by unfold smAnd smSg; omega
  obtain ⟨c₅, t₅, e₅, ht₅, y23, y24, y25, y26, n₅, m₅, rr₅, rm₅, o₅⟩ :=
    smTY_exec (P := P) c₄ hw₄ (by rw [q₄ _ (by omega), s₃ _ (by omega), r13])
      (by rw [q₄ _ (by omega)]; exact h49) (by rw [q₄ _ (by omega), s₃ _ (by omega)]) hW hY1
      g2
  have hw₅ := e₅.wb_right
  have q₅ : ∀ x, (x < 5323 ∨ (5326 < x ∧ x < 5352) ∨ 5352 < x) → c₅.nreg x = c₄.nreg x := fun x hx => n₅ x (by omega)
  have hB1 : smAnd (smSg (c.nmem (PFb + i))) (c.nmem (KRb + i) - 2) ≤ 1 := by unfold smAnd smSg; omega
  obtain ⟨c₆, t₆, e₆, ht₆, z27, z28, z29, z30, z31, z32, z33, n₆, m₆, rr₆, rm₆, o₆⟩ :=
    smTB_exec (P := P) c₅ hw₅ (by rw [q₅ _ (by omega), q₄ _ (by omega), s₃ _ (by omega), r13])
      (by rw [q₅ _ (by omega), q₄ _ (by omega)]; exact h50)
      (by rw [q₅ _ (by omega), q₄ _ (by omega), s₃ _ (by omega)]) hW hB1
      g3
  have hw₆ := e₆.wb_right
  have q₆ : ∀ x, (x < 5327 ∨ (5333 < x ∧ x < 5352) ∨ 5352 < x) → c₆.nreg x = c₅.nreg x := fun x hx => n₆ x (by omega)
  have hP1 : smSg (c.nmem (PFb + i)) ≤ 1 := by unfold smSg; omega
  have hI1 : smAnd (smSg (c.nmem (PFb + i))) (smInn (c.nmem (THb + i)) (c.nmem (THb + c.nmem (RVb + i)))) ≤ 1 := by
    unfold smAnd smSg; omega
  obtain ⟨c₇, t₇, e₇, ht₇, a14, a15, a16, n₇, m₇, rr₇, rm₇, o₇⟩ :=
    smA3_exec (P := P) c₆ hw₆ (cP := cP) (cI := cI) (i := i)
      (p := smSg (c.nmem (PFb + i)))
      (I := smAnd (smSg (c.nmem (PFb + i))) (smInn (c.nmem (THb + i)) (c.nmem (THb + c.nmem (RVb + i)))))
      (by rw [q₆ _ (by omega), q₅ _ (by omega), q₄ _ (by omega), s₃ _ (by omega), r10])
      (by rw [q₆ _ (by omega), q₅ _ (by omega), q₄ _ (by omega), s₃ _ (by omega), r14])
      (by rw [q₆ _ (by omega), q₅ _ (by omega), q₄ _ (by omega), s₃ _ (by omega), r15])
      (by rw [q₆ _ (by omega), q₅ _ (by omega), q₄ _ (by omega), s₃ _ (by omega), r16])
      (by rw [q₆ _ (by omega), q₅ _ (by omega), q₄ _ (by omega), q₃ _ (by omega)]; exact f35)
      (by rw [q₆ _ (by omega), q₅ _ (by omega), q₄ _ (by omega)]; exact h51)
      (by omega) (by omega) w11
  have q₇ : ∀ x, (x < 5314 ∨ 5316 < x) → c₇.nreg x = c₆.nreg x := n₇
  -- the values seen by the trackers
  have v14 : c₃.nreg 5314 = i := by rw [s₃ _ (by omega), r14]
  have v36 : c₃.nreg 5336 = c.nmem (RVb + i) := by rw [q₃ _ (by omega), q₂ _ (by omega)]; exact l36
  have v37 : c₃.nreg 5337 = c.nmem (THb + i) := by rw [q₃ _ (by omega), q₂ _ (by omega)]; exact l37
  have v38 : c₃.nreg 5338 = c.nmem (THb + c.nmem (RVb + i)) := by
    rw [q₃ _ (by omega), q₂ _ (by omega)]; exact l38
  have v41 : c₃.nreg 5341 = c.nmem (VTb + i) := by rw [q₃ _ (by omega), q₂ _ (by omega)]; exact l41
  have v42 : c₃.nreg 5342 = c.nmem (VTb + c.nmem (RVb + i)) := by
    rw [q₃ _ (by omega), q₂ _ (by omega)]; exact l42
  have v47 : c₃.nreg 5347 = smHst (c.nmem (KRb + c.nmem (RVb + i))) := by
    rw [q₃ _ (by omega)]; exact f47
  refine ⟨c₇, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), by omega, a14, a15, a16,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_,
    by rw [m₇, m₆, m₅, m₄, m₃, m₂, m₁], by rw [rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁], by rw [o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  all_goals simp (disch := omega) only [q₇, q₆, q₅, q₄, x17, x18, x19, x20, x21, x22, y23, y24,
    y25, y26, z27, z28, z29, z30, z31, z32, z33, s₃, v14, v36, v37, v38, v41, v42, v47, r14]

/-- **The output of the classification scan up to the index `i`.** -/
structure SmAOut (m : ℕ → ℕ) (PFb RVb THb KRb VTb i : ℕ) (c : Config) : Prop where
  cp : c.nreg 5315 = ∑ j ∈ range i, smPv m PFb j
  ci : c.nreg 5316 = ∑ j ∈ range i, smIv m PFb RVb THb j
  cp_le : c.nreg 5315 ≤ i
  ci_le : c.nreg 5316 ≤ i
  fx : FstT (smXv m PFb RVb THb KRb) i (c.nreg 5317) (c.nreg 5318)
  vx : c.nreg 5317 = 1 → c.nreg 5319 = m (RVb + c.nreg 5318) ∧
    c.nreg 5320 = m (VTb + c.nreg 5318) ∧ c.nreg 5321 = m (VTb + m (RVb + c.nreg 5318)) ∧
    c.nreg 5322 = m (THb + m (RVb + c.nreg 5318))
  fy : FstT (smYv m PFb THb) i (c.nreg 5323) (c.nreg 5324)
  vy : c.nreg 5323 = 1 → c.nreg 5325 = m (VTb + c.nreg 5324) ∧
    c.nreg 5326 = m (THb + c.nreg 5324)
  fb : FstT (smBv m PFb KRb) i (c.nreg 5327) (c.nreg 5328)
  vb : c.nreg 5327 = 1 → c.nreg 5329 = m (RVb + c.nreg 5328) ∧
    c.nreg 5330 = m (VTb + c.nreg 5328) ∧ c.nreg 5331 = m (VTb + m (RVb + c.nreg 5328)) ∧
    c.nreg 5332 = smHst (m (KRb + m (RVb + c.nreg 5328))) ∧
    c.nreg 5333 = m (THb + m (RVb + c.nreg 5328))

lemma smAOut_zero (m : ℕ → ℕ) (PFb RVb THb KRb VTb : ℕ) (c : Config) (h15 : c.nreg 5315 = 0)
    (h16 : c.nreg 5316 = 0) (h17 : c.nreg 5317 = 0) (h23 : c.nreg 5323 = 0)
    (h27 : c.nreg 5327 = 0) : SmAOut m PFb RVb THb KRb VTb 0 c where
  cp := by rw [h15]; rfl
  ci := by rw [h16]; rfl
  cp_le := by omega
  ci_le := by omega
  fx := by rw [h17]; exact fstT_zero _ _
  vx := fun h => absurd h (by omega)
  fy := by rw [h23]; exact fstT_zero _ _
  vy := fun h => absurd h (by omega)
  fb := by rw [h27]; exact fstT_zero _ _
  vb := fun h => absurd h (by omega)

set_option maxHeartbeats 1600000 in
/-- **The classification scan**: within `93 n + 11` steps, `SmAOut` up to `n`. -/
theorem smA_exec (c : Config) (hc : WordsBounded W c) {n PFb RVb THb KRb VTb : ℕ}
    (r0 : c.nreg 5300 = n) (r1 : c.nreg 5301 = PFb) (r2 : c.nreg 5302 = RVb)
    (r3 : c.nreg 5303 = THb) (r4 : c.nreg 5304 = KRb) (r5 : c.nreg 5305 = VTb) (hW : 2 ≤ W)
    (w1 : PFb + n ≤ W) (w2 : RVb + n ≤ W) (w3 : THb + n ≤ W) (w4 : KRb + n ≤ W)
    (w5 : VTb + n ≤ W) (w6 : n + 1 ≤ W) (hrv : ∀ i < n, c.nmem (RVb + i) < n) :
    ∃ c' t, Exec P W smA c c' t ∧ t ≤ 93 * n + 11 ∧ SmAOut c.nmem PFb RVb THb KRb VTb n c' ∧
      c'.nreg 5310 = 1 ∧ c'.nreg 5311 = 2 ∧ c'.nreg 5313 = 0 ∧ c'.nreg 5314 = n ∧
      (∀ x, (x < 5310 ∨ 5353 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smA
  obtain ⟨c₁, k₁, e₁, hk₁, g10, g11, g13, g14, g15, g16, g17, g23, g27, gn₁, gm₁, gr₁, grm₁,
      go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 5310 1, .constN 5311 2, .constN 5313 0, .constN 5314 0,
        .constN 5315 0, .constN 5316 0, .constN 5317 0, .constN 5323 0, .constN 5327 0])
        c c₁ k₁ ∧ k₁ = 9 ∧ c₁.nreg 5310 = 1 ∧ c₁.nreg 5311 = 2 ∧ c₁.nreg 5313 = 0 ∧
      c₁.nreg 5314 = 0 ∧ c₁.nreg 5315 = 0 ∧ c₁.nreg 5316 = 0 ∧ c₁.nreg 5317 = 0 ∧
      c₁.nreg 5323 = 0 ∧ c₁.nreg 5327 = 0 ∧
      (∀ x, (x < 5310 ∨ 5327 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 5310 ∨ 5327 < x) → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 5314 ∨ 5353 < x) → c'.nreg x = c₁.nreg x) ∧ c'.nmem = m₀ ∧
    SmAOut m₀ PFb RVb THb KRb VTb i c' ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h14, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 5314) (b := 5300) (body := smABody) J (B := 91) c₁ hw₁ g14
    (by rw [q _ (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, by rw [gm₁], smAOut_zero _ _ _ _ _ _ _ g15 g16 g17 g23 g27, rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h14 h00 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 5314 ∨ 5353 < x) → c'.nreg x = c₁.nreg x := j1
      have hrvi := hrv i hhi
      obtain ⟨c'', t, ex, ht, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26,
          b27, b28, b29, b30, b31, b32, b33, bn, bm, br, brm, bo⟩ :=
        smABody_exec (P := P) c' hw (PFb := PFb) (RVb := RVb) (THb := THb) (KRb := KRb)
          (VTb := VTb) (i := i) (cP := c'.nreg 5315) (cI := c'.nreg 5316)
          (by rw [f _ (by omega), q _ (by omega), r1]) (by rw [f _ (by omega), q _ (by omega), r2])
          (by rw [f _ (by omega), q _ (by omega), r3]) (by rw [f _ (by omega), q _ (by omega), r4])
          (by rw [f _ (by omega), q _ (by omega), r5]) (by rw [f _ (by omega), g10])
          (by rw [f _ (by omega), g11]) (by rw [f _ (by omega), g13]) h14 rfl rfl
          j3.fx.1 j3.fy.1 j3.fb.1 hW (by omega) (by omega) (by omega) (by omega) (by omega)
          (by rw [j2]; omega) (by rw [j2]; omega) (by rw [j2]; omega)
          (by have := j3.cp_le; omega) (by have := j3.ci_le; omega) (by omega)
      rw [j2] at b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32 b33
      have hX1 : smXv m₀ PFb RVb THb KRb i ≤ 1 := by unfold smXv smAnd smSg; omega
      have hY1 : smYv m₀ PFb THb i ≤ 1 := by unfold smYv smAnd smSg; omega
      have hB1 : smBv m₀ PFb KRb i ≤ 1 := by unfold smBv smAnd smSg; omega
      have hP1 : smPv m₀ PFb i ≤ 1 := by unfold smPv smSg; omega
      have hI1 : smIv m₀ PFb RVb THb i ≤ 1 := by unfold smIv smAnd smSg; omega
      have hm'' : c''.nmem = m₀ := by rw [bm, j2]
      refine ⟨c'', t, ex, by omega, b14, by rw [bn _ (by omega)]; exact h00,
        fun x hx => by rw [bn x hx, f x hx], hm'', ?_, by rw [br, j4], by rw [brm, j5],
        by rw [bo, j6]⟩
      refine ⟨by rw [b15, j3.cp, sum_range_succ], by rw [b16, j3.ci, sum_range_succ],
        by rw [b15]; have := j3.cp_le; omega, by rw [b16]; have := j3.ci_le; omega,
        by rw [b17, b18]; exact fstT_step j3.fx hX1 rfl, fun hg => ?_,
        by rw [b23, b24]; exact fstT_step j3.fy hY1 rfl, fun hg => ?_,
        by rw [b27, b28]; exact fstT_step j3.fb hB1 rfl, fun hg => ?_⟩
      · by_cases hu : smXv m₀ PFb RVb THb KRb i - c'.nreg 5317 = 0
        · rw [b18, iteT hu, b19, iteT hu, b20, iteT hu, b21, iteT hu, b22, iteT hu]
          exact j3.vx (by rw [b17] at hg; omega)
        · rw [b18, iteF hu, b19, iteF hu, b20, iteF hu, b21, iteF hu, b22, iteF hu]
          exact ⟨rfl, rfl, rfl, rfl⟩
      · by_cases hu : smYv m₀ PFb THb i - c'.nreg 5323 = 0
        · rw [b24, iteT hu, b25, iteT hu, b26, iteT hu]
          exact j3.vy (by rw [b23] at hg; omega)
        · rw [b24, iteF hu, b25, iteF hu, b26, iteF hu]
          exact ⟨rfl, rfl⟩
      · by_cases hu : smBv m₀ PFb KRb i - c'.nreg 5327 = 0
        · rw [b28, iteT hu, b29, iteT hu, b30, iteT hu, b31, iteT hu, b32, iteT hu, b33, iteT hu]
          exact j3.vb (by rw [b27] at hg; omega)
        · rw [b28, iteF hu, b29, iteF hu, b30, iteF hu, b31, iteF hu, b32, iteF hu, b33, iteF hu]
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j3, by rw [j1 _ (by omega), g10],
    by rw [j1 _ (by omega), g11], by rw [j1 _ (by omega), g13], h14,
    fun x hx => by rw [j1 x (by omega), q x (by omega)], by rw [j2], by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩


end A

end BKMNW

end PlanarFlow
