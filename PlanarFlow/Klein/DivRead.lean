module

public import PlanarFlow.Klein.ExecNatK
public import PlanarFlow.Klein.Sources

/-!
# Reading the true distances back on natural words: a loop of `divN`

The natural-word programs `kleinProgMN` and `kleinProgN` (`PlanarFlow/Klein/ExecNat.lean`,
`PlanarFlow/Klein/ExecNatK.lean`) end with the natural words holding the distances for the
**isolating** lengths, whose quotients by `N₁` are the true distances. This file adds the
read-back **executed by the machine**: a loop of natural divisions.

* `divLoop base L N`: the constants `base`, `base + L`, `N`, `1` into the natural registers
  `0, 1, 2, 4`, then for every address `a ∈ [base, base + L)`: `nmem a := nmem a / N`
  (`loadN`, `divN`, `storeN`, `addN`). `divLoop_natOnly`: no real instruction.
* `divLoop_exec`: from any configuration with words `≤ W`, `base + L + 1 ≤ W`, `N ≤ W`, it runs
  within `6 L + 6` steps and divides exactly the cells of `[base, base + L)` by `N`, keeping the
  other cells, the reals and the output.
* `kleinProgMND`, `kleinProgND`: Klein's (masked, unmasked) programs on natural words followed by
  `divLoop` over the answer words (`β + aOUT nD`, `β = W + 1`); both have no real instruction.
* `kleinM_exec_exists_natD`, `klein_exec_exists_natD`: **the true answers in machine words**:
  the statements of `kleinM_exec_exists_nat`, `klein_exec_exists_nat` for these programs, with
  word bound `kleinWN B n Hc + N` and `6 (#answers) + 6` more steps, the answer words read
  (`kOutN`, `kOutNK`) being the distances divided by `N` (`Option.map (· / N)`): with
  `N = N₁` and the isolating lengths, the true distances (`isoLen_dist_div`).
* `divCutLoop base rb L N Wc`, `divCutLoop_exec`: the read-back with a cut-off: the answer word
  at `base + p` divided by `N`, and the reach word at `rb + p` multiplied by `[quotient < Wc]`
  (computed by truncated subtractions, `ind_sub`), within `14 L + 9` steps (`cutMem`).
  `kleinProgNDC`, `klein_exec_exists_natDC`: Klein's program on natural words followed by it;
  the answers read at the end (`kOutNK`) are the distances divided by `N` and cut off at `Wc`
  (`Klein.cutW`), as the copies of the sources ask (`PlanarFlow/NegSSSP/ReadMachNat.lean`).
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-! ### The loop -/

/-- **The read-back loop**: `nmem a := nmem a / N` for `base ≤ a < base + L`, with the pointer
in the natural register `0`, the end in `1`, the divisor `N` in `2`, the word in `3` and the
constant `1` in `4`. -/
def divLoop (base L N : ℕ) : Stmt :=
  .seq (block [.constN 0 base, .constN 1 (base + L), .constN 2 N, .constN 4 1])
    (.whileLtN 0 1 (block [.loadN 3 0, .divN 3 3 2, .storeN 0 3, .addN 0 0 4]))

/-- `divLoop` has no real instruction. -/
theorem divLoop_natOnly (base L N : ℕ) : natOnly (divLoop base L N) = true := rfl

/-- The invariant of the loop: `j` cells divided so far. -/
def DivInv (W base L N : ℕ) (c d : Config) : Prop :=
  WordsBounded W d ∧ ∃ j ≤ L, d.nreg 0 = base + j ∧ d.nreg 1 = base + L ∧ d.nreg 2 = N ∧
    d.nreg 4 = 1 ∧
    (∀ a, d.nmem a = if base ≤ a ∧ a < base + j then c.nmem a / N else c.nmem a) ∧
    d.output = c.output ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem

/-- **The read-back loop runs**: from a configuration with words `≤ W`, `base + L + 1 ≤ W`,
`N ≤ W`, `divLoop base L N` runs within `6 L + 6` steps and ends with the cells of
`[base, base + L)` divided by `N`, every other cell, the reals and the output kept. -/
theorem divLoop_exec {P : Input} {W base L N : ℕ} {c : Config} (hc : WordsBounded W c)
    (hW : base + L + 1 ≤ W) (hN : N ≤ W) :
    ∃ c' k, Exec P W (divLoop base L N) c c' k ∧ k ≤ 6 * L + 6 ∧
      (∀ a, c'.nmem a = if base ≤ a ∧ a < base + L then c.nmem a / N else c.nmem a) ∧
      c'.output = c.output ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem := by
  -- the constants
  have e1 := Exec.constN (P := P) hc 0 base (by omega)
  have e2 := Exec.constN (P := P) e1.wb_right 1 (base + L) (by omega)
  have e3 := Exec.constN (P := P) e2.wb_right 2 N hN
  have e4 := Exec.constN (P := P) e3.wb_right 4 1 (by omega)
  set c₁ : Config := { c with nreg := upd (upd (upd (upd c.nreg 0 base) 1 (base + L)) 2 N) 4 1 }
    with hc₁
  have eb : Exec P W (block [.constN 0 base, .constN 1 (base + L), .constN 2 N, .constN 4 1])
      c c₁ (0 + 1 + 1 + 1 + 1) :=
    Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_cons e3 (Exec.block_cons e4
      (Exec.block_nil e4.wb_right))))
  have hw₁ : WordsBounded W c₁ := e4.wb_right
  have hI : DivInv W base L N c c₁ := by
    refine ⟨hw₁, 0, Nat.zero_le _, ?_, ?_, ?_, ?_, fun a => ?_, rfl, rfl, rfl⟩
    · simp [hc₁, upd]
    · simp [hc₁, upd]
    · simp [hc₁, upd]
    · simp [hc₁, upd]
    · have : ¬ (base ≤ a ∧ a < base + 0) := by omega
      simp only [this, ↓reduceIte]
      rfl
  obtain ⟨c', k, el, hI', ht, hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 0) (b := 1)
    (body := block [.loadN 3 0, .divN 3 3 2, .storeN 0 3, .addN 0 0 4]) (DivInv W base L N c)
    (fun d => 6 * (d.nreg 1 - d.nreg 0)) (fun d h => h.1) (fun d hd hlt => by
      obtain ⟨hw, j, hj, h0, h1, h2, h4, hm, ho, hr, hrm⟩ := hd
      have hjL : j < L := by omega
      have f1 := Exec.loadN (P := P) hw 3 0
      have f2 := Exec.divN (P := P) f1.wb_right 3 3 2
      have f3 := Exec.storeN (P := P) f2.wb_right 0 3
      have f4 := Exec.addN (P := P) f3.wb_right 0 0 4 (by simp [upd, h0, h4]; omega)
      have fb := Exec.block_cons f1 (Exec.block_cons f2 (Exec.block_cons f3 (Exec.block_cons f4
        (Exec.block_nil f4.wb_right))))
      refine ⟨_, _, fb, ⟨f4.wb_right, j + 1, hjL, ?_, ?_, ?_, ?_, fun a => ?_, ho, hr, hrm⟩, ?_⟩
      · simp [upd, h0, h4]; omega
      · simp [upd, h1]
      · simp [upd, h2]
      · simp [upd, h4]
      · show (if a = d.nreg 0 then d.nmem (d.nreg 0) / d.nreg 2 else d.nmem a) = _
        rw [h0, h2]
        by_cases ha : a = base + j
        · subst ha
          have hn : ¬ (base ≤ base + j ∧ base + j < base + j) := by omega
          have hy : base ≤ base + j ∧ base + j < base + (j + 1) := by omega
          rw [hm (base + j), ite_eq_right_of_eq_false _ _ (eq_false hn), ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true hy)]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false ha), hm a]
          by_cases hr1 : base ≤ a ∧ a < base + j
          · have hr2 : base ≤ a ∧ a < base + (j + 1) := by omega
            rw [ite_eq_left_of_eq_true _ _ (eq_true hr1), ite_eq_left_of_eq_true _ _ (eq_true hr2)]
          · have hr2 : ¬ (base ≤ a ∧ a < base + (j + 1)) := by omega
            rw [ite_eq_right_of_eq_false _ _ (eq_false hr1), ite_eq_right_of_eq_false _ _ (eq_false hr2)]
      · simp [upd, h0, h1, h4]; omega) hI
  obtain ⟨-, j, hj, h0, h1, -, -, hm, ho, hr, hrm⟩ := hI'
  have hjL : j = L := by rw [h0, h1] at ht; omega
  rw [hjL] at hm
  refine ⟨c', _, Exec.seq eb el, ?_, hm, ho, hr, hrm⟩
  have : c₁.nreg 1 - c₁.nreg 0 = L := by simp [hc₁, upd]
  rw [this] at hk
  omega

/-! ### Klein's programs followed by the read-back -/

/-- **Klein's masked program on natural words, with the read-back**: `kleinProgMN`, then the
`L` answer words at `β + aOUT nD` (`β = W + 1`, `W = B + 16 (n + 1)`) divided by `N`. -/
def kleinProgMND (B nD n k t Hc L N : ℕ) : Stmt :=
  .seq (kleinProgMN B nD n k t Hc) (divLoop (B + 16 * (n + 1) + 1 + aOUT nD) L N)

/-- **Klein's program on natural words, with the read-back**. -/
def kleinProgND (B nD n k t Hc L N : ℕ) : Stmt :=
  .seq (kleinProgN B nD n k t Hc) (divLoop (B + 16 * (n + 1) + 1 + aOUT nD) L N)

/-- `kleinProgMND` has no real instruction and no real test. -/
theorem kleinProgMND_natOnly (B nD n k t Hc L N : ℕ) :
    natOnly (kleinProgMND B nD n k t Hc L N) = true := by
  show (natOnly (kleinProgMN B nD n k t Hc) && natOnly (divLoop _ L N)) = true
  rw [kleinProgMN_natOnly, divLoop_natOnly]; rfl

/-- `kleinProgND` has no real instruction and no real test. -/
theorem kleinProgND_natOnly (B nD n k t Hc L N : ℕ) :
    natOnly (kleinProgND B nD n k t Hc L N) = true := by
  show (natOnly (kleinProgN B nD n k t Hc) && natOnly (divLoop _ L N)) = true
  rw [kleinProgN_natOnly, divLoop_natOnly]; rfl

/-- The compiled `kleinProgMND` has no real instruction. -/
theorem kleinProgMND_compile_noReal (B nD n k t Hc L N base : ℕ) :
    ∀ j ∈ compile (kleinProgMND B nD n k t Hc L N) base, j.isReal = false :=
  compile_natOnly _ (kleinProgMND_natOnly B nD n k t Hc L N) base

/-- The compiled `kleinProgND` has no real instruction. -/
theorem kleinProgND_compile_noReal (B nD n k t Hc L N base : ℕ) :
    ∀ j ∈ compile (kleinProgND B nD n k t Hc L N) base, j.isReal = false :=
  compile_natOnly _ (kleinProgND_natOnly B nD n k t Hc L N) base

lemma map_div_natCast (z : ℕ) (N : ℕ) :
    (some (z : ℤ)).map (· / (N : ℤ)) = some ((z / N : ℕ) : ℤ) := by
  simp

/-- The answer read after the loop is the answer read before it, divided by `N`. -/
lemma kOutN_divLoop {nD n k t β N L q i : ℕ} {d d' : Config}
    (hm : ∀ a, d'.nmem a = if β + aOUT nD ≤ a ∧ a < β + aOUT nD + L then d.nmem a / N
      else d.nmem a)
    (hq : q * t + i < L) (hRB : aRBM n k + q * t + i < β + aOUT nD) :
    kOutN nD n k t β d' q i = (kOutN nD n k t β d q i).map (· / (N : ℤ)) := by
  unfold kOutN
  have h1 : ¬ (β + aOUT nD ≤ aRBM n k + q * t + i ∧
      aRBM n k + q * t + i < β + aOUT nD + L) := by omega
  have h2 : β + aOUT nD ≤ β + (aOUT nD + q * t + i) ∧
      β + (aOUT nD + q * t + i) < β + aOUT nD + L := by omega
  rw [hm, hm, ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
  split_ifs
  · exact (map_div_natCast _ _).symm
  · rfl

/-- The answer of `kleinProg` read after the loop is the one read before it, divided by `N`. -/
lemma kOutNK_divLoop {nD n t β N L j i : ℕ} {d d' : Config}
    (hm : ∀ a, d'.nmem a = if β + aOUT nD ≤ a ∧ a < β + aOUT nD + L then d.nmem a / N
      else d.nmem a)
    (hq : j * t + i < L) (hRB : aRB n + j * t + i < β + aOUT nD) :
    kOutNK nD n t β d' j i = (kOutNK nD n t β d j i).map (· / (N : ℤ)) := by
  unfold kOutNK
  have h1 : ¬ (β + aOUT nD ≤ aRB n + j * t + i ∧ aRB n + j * t + i < β + aOUT nD + L) := by
    omega
  have h2 : β + aOUT nD ≤ β + (aOUT nD + j * t + i) ∧
      β + (aOUT nD + j * t + i) < β + aOUT nD + L := by omega
  rw [hm, hm, ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2)]
  split_ifs
  · exact (map_div_natCast _ _).symm
  · rfl

/-! ### The read-back with the cut-off -/

/-- `1` if `v < Wc`, else `0`, by truncated subtractions. -/
lemma ind_sub (Wc v : ℕ) : Wc - v - (Wc - v - 1) = if v < Wc then 1 else 0 := by
  split_ifs <;> omega

/-- The body of the read-back with the cut-off, at offset `p` (register `0`): the answer word
at `base + p` divided by `N` (`divN`), and the reach word at `rb + p` multiplied by
`[quotient < Wc]` (computed by truncated subtractions). -/
def dcBody : Stmt :=
  block [.addN 8 5 0, .loadN 3 8, .divN 3 3 2, .storeN 8 3, .subN 10 7 3, .subN 11 10 4,
    .subN 10 10 11, .addN 8 6 0, .loadN 11 8, .mulN 11 11 10, .storeN 8 11, .addN 0 0 4]

/-- **The read-back loop with the cut-off**: for every offset `p < L`, the answer word at
`base + p` divided by `N`, and the reach word at `rb + p` cleared when the quotient is not
below `Wc`. Registers: `0` offset, `1` end, `2` divisor, `4` one, `5` `base`, `6` `rb`, `7` `Wc`,
`3, 8, 10, 11` scratch. -/
def divCutLoop (base rb L N Wc : ℕ) : Stmt :=
  .seq (block [.constN 0 0, .constN 1 L, .constN 2 N, .constN 4 1, .constN 5 base,
      .constN 6 rb, .constN 7 Wc])
    (.whileLtN 0 1 dcBody)

/-- `divCutLoop` has no real instruction. -/
theorem divCutLoop_natOnly (base rb L N Wc : ℕ) : natOnly (divCutLoop base rb L N Wc) = true :=
  rfl

/-- The memory after `j` steps of the read-back with the cut-off. -/
def cutMem (c : Config) (base rb j N Wc a : ℕ) : ℕ :=
  if base ≤ a ∧ a < base + j then c.nmem a / N
  else if rb ≤ a ∧ a < rb + j then
    c.nmem a * (if c.nmem (base + (a - rb)) / N < Wc then 1 else 0)
  else c.nmem a

lemma dcBody_exec {P : Input} {W base rb N Wc j : ℕ} {d : Config} (hw : WordsBounded W d)
    (h0 : d.nreg 0 = j) (h2 : d.nreg 2 = N) (h4 : d.nreg 4 = 1) (h5 : d.nreg 5 = base)
    (h6 : d.nreg 6 = rb) (h7 : d.nreg 7 = Wc) (hb : base + j ≤ W) (hr : rb + j ≤ W)
    (hj : j + 1 ≤ W) (hne : rb + j ≠ base + j) :
    ∃ d', Exec P W dcBody d d' (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) ∧
      d'.nreg 0 = j + 1 ∧ d'.nreg 1 = d.nreg 1 ∧ d'.nreg 2 = N ∧ d'.nreg 4 = 1 ∧
      d'.nreg 5 = base ∧ d'.nreg 6 = rb ∧ d'.nreg 7 = Wc ∧
      (∀ a, d'.nmem a = if a = rb + j then
          d.nmem (rb + j) * (if d.nmem (base + j) / N < Wc then 1 else 0)
        else if a = base + j then d.nmem (base + j) / N else d.nmem a) ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem := by
  have f1 := Exec.addN (P := P) hw 8 5 0 (by rw [h5, h0]; exact hb)
  have f2 := Exec.loadN (P := P) f1.wb_right 3 8
  have f3 := Exec.divN (P := P) f2.wb_right 3 3 2
  have f4 := Exec.storeN (P := P) f3.wb_right 8 3
  have f5 := Exec.subN (P := P) f4.wb_right 10 7 3
  have f6 := Exec.subN (P := P) f5.wb_right 11 10 4
  have f7 := Exec.subN (P := P) f6.wb_right 10 10 11
  have f8 := Exec.addN (P := P) f7.wb_right 8 6 0 (by simp [upd, h6, h0]; exact hr)
  have f9 := Exec.loadN (P := P) f8.wb_right 11 8
  have hw9 := f9.wb_right
  have f10 := Exec.mulN (P := P) hw9 11 11 10
    (le_trans (Nat.mul_le_mul_left _ (show _ ≤ 1 by simp [upd]; omega))
      (by rw [mul_one]; exact hw9.1 11))
  have f11 := Exec.storeN (P := P) f10.wb_right 8 11
  have f12 := Exec.addN (P := P) f11.wb_right 0 0 4 (by simp [upd, h0, h4]; exact hj)
  refine ⟨_, Exec.block_cons f1 (Exec.block_cons f2 (Exec.block_cons f3 (Exec.block_cons f4
    (Exec.block_cons f5 (Exec.block_cons f6 (Exec.block_cons f7 (Exec.block_cons f8
    (Exec.block_cons f9 (Exec.block_cons f10 (Exec.block_cons f11 (Exec.block_cons f12
    (Exec.block_nil f12.wb_right)))))))))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a => ?_, rfl, rfl,
    rfl⟩
  · simp [upd, h0, h4]
  · simp [upd]
  · simp [upd, h2]
  · simp [upd, h4]
  · simp [upd, h5]
  · simp [upd, h6]
  · simp [upd, h7]
  · simp only [upd, h0, h2, h4, h5, h6, h7]
    simp only [Nat.reduceEqDiff, ↓reduceIte, hne]
    split_ifs <;> simp_all [ind_sub]

/-- The invariant of the read-back with the cut-off: `j` offsets done. -/
def DCInv (W base rb L N Wc : ℕ) (c d : Config) : Prop :=
  WordsBounded W d ∧ ∃ j ≤ L, d.nreg 0 = j ∧ d.nreg 1 = L ∧ d.nreg 2 = N ∧ d.nreg 4 = 1 ∧
    d.nreg 5 = base ∧ d.nreg 6 = rb ∧ d.nreg 7 = Wc ∧
    (∀ a, d.nmem a = cutMem c base rb j N Wc a) ∧
    d.output = c.output ∧ d.rreg = c.rreg ∧ d.rmem = c.rmem

/-- **The read-back loop with the cut-off runs**: from a configuration with words `≤ W`,
`base + L + 1 ≤ W`, `rb + L ≤ base`, `N, Wc ≤ W`, `divCutLoop base rb L N Wc` runs within
`14 L + 9` steps and ends with the memory `cutMem c base rb L N Wc`: the answer words of
`[base, base + L)` divided by `N`, the reach words of `[rb, rb + L)` cleared where the quotient
is not below `Wc`, every other cell, the reals and the output kept. -/
theorem divCutLoop_exec {P : Input} {W base rb L N Wc : ℕ} {c : Config} (hc : WordsBounded W c)
    (hW : base + L + 1 ≤ W) (hrb : rb + L ≤ base) (hN : N ≤ W) (hWc : Wc ≤ W) :
    ∃ c' k, Exec P W (divCutLoop base rb L N Wc) c c' k ∧ k ≤ 14 * L + 9 ∧
      (∀ a, c'.nmem a = cutMem c base rb L N Wc a) ∧
      c'.output = c.output ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem := by
  have e1 := Exec.constN (P := P) hc 0 0 (by omega)
  have e2 := Exec.constN (P := P) e1.wb_right 1 L (by omega)
  have e3 := Exec.constN (P := P) e2.wb_right 2 N hN
  have e4 := Exec.constN (P := P) e3.wb_right 4 1 (by omega)
  have e5 := Exec.constN (P := P) e4.wb_right 5 base (by omega)
  have e6 := Exec.constN (P := P) e5.wb_right 6 rb (by omega)
  have e7 := Exec.constN (P := P) e6.wb_right 7 Wc hWc
  set u := upd (upd (upd c.nreg 0 0) 1 L) 2 N with hu
  set c₁ : Config := { c with nreg := upd (upd (upd (upd u 4 1) 5 base) 6 rb) 7 Wc } with hc₁
  have eb : Exec P W (block [.constN 0 0, .constN 1 L, .constN 2 N, .constN 4 1, .constN 5 base,
      .constN 6 rb, .constN 7 Wc]) c c₁ (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) :=
    Exec.block_cons e1 (Exec.block_cons e2 (Exec.block_cons e3 (Exec.block_cons e4
      (Exec.block_cons e5 (Exec.block_cons e6 (Exec.block_cons e7
      (Exec.block_nil e7.wb_right)))))))
  have hw₁ : WordsBounded W c₁ := e7.wb_right
  have hI : DCInv W base rb L N Wc c c₁ := by
    refine ⟨hw₁, 0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a => ?_, rfl, rfl, rfl⟩
    · simp [hc₁, hu, upd]
    · simp [hc₁, hu, upd]
    · simp [hc₁, hu, upd]
    · simp [hc₁, hu, upd]
    · simp [hc₁, hu, upd]
    · simp [hc₁, hu, upd]
    · simp [hc₁, hu, upd]
    · unfold cutMem
      have h1 : ¬ (base ≤ a ∧ a < base + 0) := by omega
      have h2 : ¬ (rb ≤ a ∧ a < rb + 0) := by omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2)]
  obtain ⟨c', k, el, hI', ht, hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 0) (b := 1)
    (body := dcBody) (DCInv W base rb L N Wc c)
    (fun d => 14 * (d.nreg 1 - d.nreg 0)) (fun d h => h.1) (fun d hd hlt => by
      obtain ⟨hw, j, hj, h0, h1, h2, h4, h5, h6, h7, hm, ho, hr, hrm⟩ := hd
      have hjL : j < L := by omega
      obtain ⟨d', fb, g0, g1, g2, g4, g5, g6, g7, gm, go, gr, grm⟩ := dcBody_exec (P := P) hw h0
        h2 h4 h5 h6 h7 (by omega) (by omega) (by omega) (by omega)
      refine ⟨d', _, fb, ⟨fb.wb_right, j + 1, hjL, g0, by rw [g1, h1], g2, g4, g5, g6, g7,
        fun a => ?_, go.trans ho, gr.trans hr, grm.trans hrm⟩, ?_⟩
      · rw [gm a, hm (rb + j), hm (base + j), hm a]
        unfold cutMem
        have n1 : ¬ (base ≤ rb + j ∧ rb + j < base + j) := by omega
        have n2 : ¬ (rb ≤ rb + j ∧ rb + j < rb + j) := by omega
        have n3 : ¬ (base ≤ base + j ∧ base + j < base + j) := by omega
        have n4 : ¬ (rb ≤ base + j ∧ base + j < rb + j) := by omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false n1), ite_eq_right_of_eq_false _ _ (eq_false n2),
          ite_eq_right_of_eq_false _ _ (eq_false n3), ite_eq_right_of_eq_false _ _ (eq_false n4)]
        by_cases ha : a = rb + j
        · subst ha
          have y1 : ¬ (base ≤ rb + j ∧ rb + j < base + (j + 1)) := by omega
          have y2 : rb ≤ rb + j ∧ rb + j < rb + (j + 1) := by omega
          rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_right_of_eq_false _ _ (eq_false y1),
            ite_eq_left_of_eq_true _ _ (eq_true y2), Nat.add_sub_cancel_left]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false ha)]
          by_cases hb : a = base + j
          · subst hb
            have y1 : base ≤ base + j ∧ base + j < base + (j + 1) := by omega
            rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), ite_eq_left_of_eq_true _ _ (eq_true y1)]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false hb)]
            by_cases z1 : base ≤ a ∧ a < base + j
            · have z2 : base ≤ a ∧ a < base + (j + 1) := by omega
              rw [ite_eq_left_of_eq_true _ _ (eq_true z1), ite_eq_left_of_eq_true _ _ (eq_true z2)]
            · have z2 : ¬ (base ≤ a ∧ a < base + (j + 1)) := by omega
              rw [ite_eq_right_of_eq_false _ _ (eq_false z1),
                ite_eq_right_of_eq_false _ _ (eq_false z2)]
              by_cases z3 : rb ≤ a ∧ a < rb + j
              · have z4 : rb ≤ a ∧ a < rb + (j + 1) := by omega
                rw [ite_eq_left_of_eq_true _ _ (eq_true z3),
                  ite_eq_left_of_eq_true _ _ (eq_true z4)]
              · have z4 : ¬ (rb ≤ a ∧ a < rb + (j + 1)) := by omega
                rw [ite_eq_right_of_eq_false _ _ (eq_false z3),
                  ite_eq_right_of_eq_false _ _ (eq_false z4)]
      · rw [g1, g0, h1]; omega) hI
  obtain ⟨-, j, hj, h0, h1, -, -, -, -, -, hm, ho, hr, hrm⟩ := hI'
  have hjL : j = L := by rw [h0, h1] at ht; omega
  rw [hjL] at hm
  refine ⟨c', _, Exec.seq eb el, ?_, hm, ho, hr, hrm⟩
  have : c₁.nreg 1 - c₁.nreg 0 = L := by simp [hc₁, hu, upd]
  rw [this] at hk
  omega

/-- **The answer of `kleinProg` read after the loop with the cut-off** is the one read before
it, divided by `N` and cut off at `Wc`. -/
lemma kOutNK_divCutLoop {nD n t β N L Wc j i : ℕ} {d d' : Config}
    (hm : ∀ a, d'.nmem a = cutMem d (β + aOUT nD) (aRB n) L N Wc a)
    (hq : j * t + i < L) (hrb : aRB n + L ≤ β + aOUT nD) :
    kOutNK nD n t β d' j i =
      ((kOutNK nD n t β d j i).map (· / (N : ℤ))).bind (cutW (Wc : ℤ)) := by
  unfold kOutNK
  rw [hm, hm]
  unfold cutMem
  have h1 : ¬ (β + aOUT nD ≤ aRB n + j * t + i ∧ aRB n + j * t + i < β + aOUT nD + L) := by
    omega
  have h2 : aRB n ≤ aRB n + j * t + i ∧ aRB n + j * t + i < aRB n + L := by omega
  have h3 : β + aOUT nD ≤ β + (aOUT nD + j * t + i) ∧
      β + (aOUT nD + j * t + i) < β + aOUT nD + L := by omega
  have e1 : β + aOUT nD + (aRB n + j * t + i - aRB n) = β + (aOUT nD + j * t + i) := by omega
  rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2),
    ite_eq_left_of_eq_true _ _ (eq_true h3), e1]
  set v := d.nmem (β + (aOUT nD + j * t + i)) / N
  set r := d.nmem (aRB n + j * t + i)
  by_cases hv : v < Wc
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hv), mul_one]
    split_ifs with hr
    · rw [map_div_natCast, Option.bind_some]
      unfold cutW
      have : ((v : ℕ) : ℤ) < (Wc : ℤ) := by exact_mod_cast hv
      rw [ite_eq_left_of_eq_true _ _ (eq_true this)]
    · rfl
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hv), mul_zero]
    have h0 : ¬ (0 = 1) := by omega
    rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
    split_ifs with hr
    · rw [map_div_natCast, Option.bind_some]
      unfold cutW
      have : ¬ ((v : ℕ) : ℤ) < (Wc : ℤ) := by exact_mod_cast hv
      rw [ite_eq_right_of_eq_false _ _ (eq_false this)]
    · rfl

lemma le_kleinWN (B n Hc : ℕ) : 2 * (B + 16 * (n + 1)) + 2 ≤ kleinWN B n Hc := by
  unfold kleinWN
  have := Nat.zero_le ((2 * Hc + 1) * (2 * Hc + 1))
  omega

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

local notation "𝒢" => pieceGraph M S ℓ

/-- **Klein's masked program on natural words, with the answers divided by `N` in machine
words** (`kleinM_exec_exists_nat` followed by `divLoop` over the `kRank fl k · t` answer
words): the program `kleinProgMND` (no real instruction) runs from `natCfg c₀` with words at
most `kleinWN B n Hc + N` within `4 · 36500000 (N lg N + f t lg N) + 6 f t + 9` steps
(`f = kRank fl k` the flagged moves), and the natural answer words read at the end
(`kOutN`) are **the distances divided by `N`**, computed by the machine (`divN`). -/
theorem kleinM_exec_exists_natD (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (t : ℕ)
    (X : ℕ → V) (hX : ∀ i < t, ¬ IsRoot M k g (X i)) (fl : ℕ → Bool) (N : ℕ) :
    ∃ (n B Hc : ℕ) (P : Input) (c₀ d' : Config) (steps : ℕ),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      kleinHI V F S ℓ k ≤ Hc ∧ (Hc : ℝ) < kleinHI V F S ℓ k + 1 ∧
      Exec P (kleinWN B n Hc + N)
        (kleinProgMND B (Fintype.card D) n k t Hc (kRank fl k * t) N)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) d' steps ∧
      steps ≤ 4 * (36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        kRank fl k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) +
          6 * (kRank fl k * t) + 9 ∧
      (∀ j < k, fl j = true → ∀ i < t,
        kOutN (Fintype.card D) n k t (B + 16 * (n + 1) + 1) d' (kRank fl j) i =
          (odist 𝒢 (tripSrc M k g j) (X i)).map (· / (N : ℤ))) ∧
      d'.output = c₀.output := by
  obtain ⟨n, B, Hc, P, c₀, d₁, s₁, hn, hHc, hHc', e, hs, hd, hout, hOUT, hRB⟩ :=
    kleinM_exec_exists_nat' H hR t X hX fl
  have e' := e.mono_W (Nat.le_add_right _ N)
  have hfk : kRank fl k * t ≤ k * t := Nat.mul_le_mul_right t (kRank_le fl k)
  have hWN := le_kleinWN B n Hc
  obtain ⟨d', s₂, el, hs₂, hm, ho, -, -⟩ := divLoop_exec (P := P)
    (base := B + 16 * (n + 1) + 1 + aOUT (Fintype.card D)) (L := kRank fl k * t) (N := N)
    e'.wb_right (by omega) (by omega)
  refine ⟨n, B, Hc, P, c₀, d', s₁ + s₂, hn, hHc, hHc', Exec.seq e' el, by omega,
    fun j hj hfj i hi => ?_, by rw [ho, hout]⟩
  have hq : kRank fl j * t + t ≤ kRank fl k * t := by
    have := Nat.mul_le_mul_right t (kRank_succ_le fl hj hfj)
    rw [Nat.add_mul, one_mul] at this
    exact this
  rw [kOutN_divLoop hm (by omega) (by omega), hd j hj hfj i hi]

/-- **Klein's program on natural words, with the answers divided by `N` in machine words**
(`klein_exec_exists_nat` followed by `divLoop` over the `k t` answer words): the program
`kleinProgND` (no real instruction) runs from `natCfg c₀` with words at most
`kleinWN B n Hc + N` within `4 · 36500000 (N lg N + k t lg N) + 6 k t + 9` steps, and the
natural answer words read at the end (`kOutNK`) are **the distances divided by `N`**. -/
theorem klein_exec_exists_natD (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (t : ℕ)
    (X : ℕ → V) (hX : ∀ i < t, ¬ IsRoot M k g (X i)) (N : ℕ) :
    ∃ (n B Hc : ℕ) (P : Input) (c₀ d' : Config) (steps : ℕ),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      kleinHI V F S ℓ k ≤ Hc ∧ (Hc : ℝ) < kleinHI V F S ℓ k + 1 ∧
      Exec P (kleinWN B n Hc + N) (kleinProgND B (Fintype.card D) n k t Hc (k * t) N)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) d' steps ∧
      steps ≤ 4 * (36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) +
          6 * (k * t) + 9 ∧
      (∀ j < k, ∀ i < t,
        kOutNK (Fintype.card D) n t (B + 16 * (n + 1) + 1) d' j i =
          (odist 𝒢 (tripSrc M k g j) (X i)).map (· / (N : ℤ))) ∧
      d'.output = c₀.output := by
  obtain ⟨n, B, Hc, P, c₀, d₁, s₁, hn, hHc, hHc', e, hs, hd, hout, hOUT, hRB⟩ :=
    klein_exec_exists_nat' H hR t X hX
  have e' := e.mono_W (Nat.le_add_right _ N)
  have hWN := le_kleinWN B n Hc
  obtain ⟨d', s₂, el, hs₂, hm, ho, -, -⟩ := divLoop_exec (P := P)
    (base := B + 16 * (n + 1) + 1 + aOUT (Fintype.card D)) (L := k * t) (N := N)
    e'.wb_right (by omega) (by omega)
  refine ⟨n, B, Hc, P, c₀, d', s₁ + s₂, hn, hHc, hHc', Exec.seq e' el, by omega,
    fun j hj i hi => ?_, by rw [ho, hout]⟩
  have hq : j * t + t ≤ k * t := by
    have := Nat.mul_le_mul_right t (show j + 1 ≤ k by omega)
    rw [Nat.add_mul, one_mul] at this
    exact this
  rw [kOutNK_divLoop hm (by omega) (by unfold aRB at hRB ⊢; omega), hd j hj i hi]

/-- **Klein's program on natural words, with the read-back and the cut-off**: `kleinProgN`, then
the `L` answer words at `β + aOUT nD` divided by `N`, the reach words at `aRB n` cleared where
the quotient is not below `Wc` (`divCutLoop`). -/
def kleinProgNDC (B nD n k t Hc L N Wc : ℕ) : Stmt :=
  .seq (kleinProgN B nD n k t Hc) (divCutLoop (B + 16 * (n + 1) + 1 + aOUT nD) (aRB n) L N Wc)

/-- `kleinProgNDC` has no real instruction and no real test. -/
theorem kleinProgNDC_natOnly (B nD n k t Hc L N Wc : ℕ) :
    natOnly (kleinProgNDC B nD n k t Hc L N Wc) = true := by
  show (natOnly (kleinProgN B nD n k t Hc) && natOnly (divCutLoop _ _ L N Wc)) = true
  rw [kleinProgN_natOnly, divCutLoop_natOnly]; rfl

/-- The compiled `kleinProgNDC` has no real instruction. -/
theorem kleinProgNDC_compile_noReal (B nD n k t Hc L N Wc base : ℕ) :
    ∀ j ∈ compile (kleinProgNDC B nD n k t Hc L N Wc) base, j.isReal = false :=
  compile_natOnly _ (kleinProgNDC_natOnly B nD n k t Hc L N Wc) base

/-- **Klein's program on natural words, with the answers divided by `N` and cut off at `Wc` in
machine words** (`klein_exec_exists_nat` followed by `divCutLoop` over the `k t` answers): the
program `kleinProgNDC` (no real instruction) runs from `natCfg c₀` with words at most
`kleinWN B n Hc + N + Wc` within `4 · 36500000 (N lg N + k t lg N) + 14 k t + 12` steps, and
the natural answers read at the end (`kOutNK`) are the distances divided by `N`, cut off at
`Wc`. -/
theorem klein_exec_exists_natDC (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (t : ℕ)
    (X : ℕ → V) (hX : ∀ i < t, ¬ IsRoot M k g (X i)) (N Wc : ℕ) :
    ∃ (n B Hc : ℕ) (P : Input) (c₀ d' : Config) (steps : ℕ),
      n = 2 * (Fintype.card V + Fintype.card F + Fintype.card D) ∧
      kleinHI V F S ℓ k ≤ Hc ∧ (Hc : ℝ) < kleinHI V F S ℓ k + 1 ∧
      Exec P (kleinWN B n Hc + N + Wc)
        (kleinProgNDC B (Fintype.card D) n k t Hc (k * t) N Wc)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) d' steps ∧
      steps ≤ 4 * (36500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        k * t * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) +
          14 * (k * t) + 12 ∧
      (∀ j < k, ∀ i < t,
        kOutNK (Fintype.card D) n t (B + 16 * (n + 1) + 1) d' j i =
          ((odist 𝒢 (tripSrc M k g j) (X i)).map (· / (N : ℤ))).bind (cutW (Wc : ℤ))) ∧
      d'.output = c₀.output := by
  obtain ⟨n, B, Hc, P, c₀, d₁, s₁, hn, hHc, hHc', e, hs, hd, hout, hOUT, hRB⟩ :=
    klein_exec_exists_nat' H hR t X hX
  have e' := e.mono_W (show kleinWN B n Hc ≤ kleinWN B n Hc + N + Wc by omega)
  have hWN := le_kleinWN B n Hc
  have hRB' : aRB n + k * t ≤ B + 16 * (n + 1) + 1 + aOUT (Fintype.card D) := by omega
  obtain ⟨d', s₂, el, hs₂, hm, ho, -, -⟩ := divCutLoop_exec (P := P)
    (base := B + 16 * (n + 1) + 1 + aOUT (Fintype.card D)) (rb := aRB n) (L := k * t) (N := N)
    (Wc := Wc) e'.wb_right (by omega) hRB' (by omega) (by omega)
  refine ⟨n, B, Hc, P, c₀, d', s₁ + s₂, hn, hHc, hHc', Exec.seq e' el, by omega,
    fun j hj i hi => ?_, by rw [ho, hout]⟩
  have hq : j * t + t ≤ k * t := by
    have := Nat.mul_le_mul_right t (show j + 1 ≤ k by omega)
    rw [Nat.add_mul, one_mul] at this
    exact this
  rw [kOutNK_divCutLoop hm (by omega) hRB', hd j hj i hi]

end Klein

end PlanarFlow
