module

public import NestedDissection.DetModMath
public import WordRAM

/-!
# Determinants modulo a prime on the random-access machine

Gaussian elimination with row exchanges modulo a prime `p`, on the machine of `WordRAM`. The
input is `[n, p, a₀₀, a₀₁, …, a_{n-1,n-1}]`; the program `DetMod.detMod` prints
`det A mod p` within `O(n³ + n log p)` steps (`DetMod.detMod_runsWithin`).

Memory: the matrix row by row at `0 … n² - 1`. Registers: `r0 = 0`, `r1 = 1`, `r2 = n`,
`r3 = p`, `r4 = n²`, `r5 = 2`, `r12 = p - 1`, `r13 = p - 2`; `r6` the column `k`, `r24 = k n`,
`r11` the accumulated determinant; scratch registers otherwise.
-/

@[expose] public section

namespace NestedDissection

namespace DetMod

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The input

`inp`, `dim`, `prm`, `ent`, `DEnc`, `mat` and `inMat` are defined in
`NestedDissection/DetModSpec.lean`. -/

/-! ### The program -/

/-- Set up the constants. -/
def setup : Stmt := block [.constN 1 1, .readIn 2 0, .readIn 3 1, .mulN 4 2 2, .constN 5 2,
  .subN 12 3 1, .subN 13 3 5, .constN 11 1, .copyN 6 0, .copyN 7 0]

/-- Copy one entry, reduced modulo `p`. -/
def copyStep : Stmt := block [.addN 10 7 5, .readIn 9 10, .modN 9 9 3, .storeN 7 9, .addN 7 7 1]

/-- One row `r7` of the pivot search in column `k = r6`: stop at the first nonzero entry. -/
def scanStep : Stmt :=
  .seq (block [.mulN 25 7 2, .addN 10 25 6, .loadN 9 10])
    (.ifLtN 0 9 (block [.copyN 8 7, .copyN 7 2]) (.instr (.addN 7 7 1)))

/-- One column `r16` of the exchange of rows `k` (at `r24`) and `r8` (at `r25`). -/
def swapStep : Stmt := block [.addN 10 24 16, .loadN 9 10, .addN 23 25 16, .loadN 22 23,
  .storeN 10 22, .storeN 23 9, .addN 16 16 1]

/-- One step of the power `r21 · r19 ^ r20` modulo `p`. -/
def powStep : Stmt :=
  .seq (block [.modN 22 20 5])
    (.seq (.ifLtN 0 22 (block [.mulN 21 21 19, .modN 21 21 3]) .skip)
      (block [.mulN 19 19 19, .modN 19 19 3, .divN 20 20 5]))

/-- One entry `r16` of the row operation on row `i` (at `r25`) with factor `p - f = r18`. -/
def entStep : Stmt := block [.addN 10 25 16, .loadN 9 10, .addN 23 24 16, .loadN 22 23,
  .mulN 22 22 18, .addN 9 9 22, .modN 9 9 3, .storeN 10 9, .addN 16 16 1]

/-- The row operation on row `i = r15`: subtract `f = a_ik / a_kk` times row `k`. -/
def rowStep : Stmt :=
  .seq (block [.mulN 25 15 2, .addN 10 25 6, .loadN 9 10, .mulN 17 9 14, .modN 17 17 3,
      .subN 18 3 17, .copyN 16 6])
    (.seq (.whileLtN 16 2 entStep) (.instr (.addN 15 15 1)))

/-- Eliminate below a nonzero pivot `r9`: its inverse by Fermat, then the rows below. -/
def elim : Stmt :=
  .seq (block [.copyN 19 9, .copyN 20 13, .copyN 21 1]) <|
  .seq (.whileLtN 0 20 powStep) <|
  .seq (block [.copyN 14 21, .addN 15 6 1]) (.whileLtN 15 2 rowStep)

/-- One column `k = r6`. -/
def colStep : Stmt :=
  .seq (.seq (block [.mulN 24 6 2, .copyN 7 6, .copyN 8 2]) <|
    .seq (.whileLtN 7 2 scanStep) (.ifLtN 6 8 (.ifLtN 8 2 (.seq (block [.mulN 25 8 2, .copyN 16 0,
      .mulN 11 11 12, .modN 11 11 3]) (.whileLtN 16 2 swapStep)) .skip) .skip)) <|
  .seq (block [.addN 10 24 6, .loadN 9 10, .mulN 11 11 9, .modN 11 11 3]) <|
  .seq (.ifLtN 0 9 elim .skip) (.instr (.addN 6 6 1))

/-- **The determinant modulo `p`.** -/
def detMod : Stmt :=
  .seq setup <| .seq (.whileLtN 7 4 copyStep) <| .seq (.whileLtN 6 2 colStep) (.instr (.outN 11))

/-! ### The constant registers -/

/-- The constant registers. -/
def Regs (d : List ℕ) (c : Config) : Prop :=
  c.nreg 0 = 0 ∧ c.nreg 1 = 1 ∧ c.nreg 2 = dim d ∧ c.nreg 3 = prm d ∧
    c.nreg 4 = dim d * dim d ∧ c.nreg 5 = 2 ∧ c.nreg 12 = prm d - 1 ∧ c.nreg 13 = prm d - 2

/-- The constant registers are unchanged. -/
def KeepsR (c c' : Config) : Prop :=
  ∀ r, r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 12 ∨ r = 13 → c'.nreg r = c.nreg r

theorem regs_of_keepsR {d : List ℕ} {c c' : Config} (hR : Regs d c) (h : KeepsR c c') :
    Regs d c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ := hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [h _ (by omega)] <;> assumption

/-! ### The pivot search -/

/-- The state of the pivot search in column `k`, from `c₀`. -/
structure ISc (d : List ℕ) (W : ℕ) (k : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 25 → c.nreg r = c₀.nreg r
  mem : c.nmem = c₀.nmem
  out : c.output = c₀.output
  r7_ge : k ≤ c.nreg 7
  r7_le : c.nreg 7 ≤ dim d
  found : (c.nreg 8 = dim d ∧ ∀ r, k ≤ r → r < c.nreg 7 → c.nmem (r * dim d + k) = 0) ∨
    (k ≤ c.nreg 8 ∧ c.nreg 8 < dim d ∧ c.nmem (c.nreg 8 * dim d + k) ≠ 0 ∧ c.nreg 7 = dim d)

section scan
variable {d : List ℕ} {W : ℕ}

theorem scanStep_exec (he : DEnc d W) {k : ℕ} {c₀ : Config} (hR : Regs d c₀) (h6 : c₀.nreg 6 = k)
    (hk : k < dim d) (c : Config) (hI : ISc d W k c₀ c) (hlt : c.nreg 7 < dim d) :
    ∃ c' k', Exec (inp d) W scanStep c c' k' ∧ ISc d W k c₀ c' ∧
      (dim d - c'.nreg 7) * 8 + k' + 2 ≤ (dim d - c.nreg 7) * 8 := by
  have hc := hI.wb
  have hW := he.dim_sq
  obtain ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ := regs_of_keepsR hR fun r hr => hI.regs r
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have e6 : c.nreg 6 = k := by rw [hI.regs 6 (by omega) (by omega) (by omega) (by omega) (by omega), h6]
  have hidx : c.nreg 7 * dim d + k < dim d * dim d := DetMod.idx_lt hlt hk
  have hnW : dim d + 2 ≤ W := by nlinarith
  have hval : c.nmem (c.nreg 7 * c.nreg 2 + c.nreg 6) = c.nmem (c.nreg 7 * dim d + k) := by
    rw [h2, e6]
  have hK : ∀ c' : Config, (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 25 → c'.nreg r = c.nreg r) →
      ∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 25 → c'.nreg r = c₀.nreg r :=
    fun c' h r a b e f g => (h r a b e f g).trans (hI.regs r a b e f g)
  unfold scanStep
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h2]; have := hc.1 7; nlinarith
  · config_simp; rw [h2, e6]; omega
  config_simp
  by_cases hz : c.nmem (c.nreg 7 * dim d + k) = 0
  · refine spec_ifLtN_false (by config_simp; rw [h0, hval]; omega) ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
    refine ⟨⟨hw, hK _ fun r a b e f g => ?_, by config_simp; exact hI.mem, by config_simp; exact hI.out,
      by config_simp; have := hI.r7_ge; omega, by config_simp; rw [h1]; omega, ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply, a, e, f, g, ↓reduceIte]
    · config_simp
      rcases hI.found with ⟨h8, hr⟩ | ⟨-, -, -, h7⟩
      · left; refine ⟨h8, fun r hr1 hr2 => ?_⟩
        rw [h1] at hr2
        rcases Nat.lt_succ_iff_lt_or_eq.1 hr2 with hr2 | rfl
        · exact hI.mem ▸ hr r hr1 hr2
        · exact hz
      · omega
    · config_simp; rw [h1]; omega
  · refine spec_ifLtN_true (by config_simp; rw [h0, hval]; omega) ?_
    exec_block
    refine ⟨⟨‹_›, hK _ fun r a b e f g => ?_, by config_simp; exact hI.mem, by config_simp; exact hI.out,
      by config_simp; rw [h2]; omega, by config_simp; rw [h2], ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply, a, b, e, f, g, ↓reduceIte]
    · config_simp
      right; exact ⟨hI.r7_ge, hlt, hz, h2⟩
    · config_simp; rw [h2]; omega

end scan

/-! ### The row exchange -/

/-- The state of the exchange of rows `k` and `r`, from `c₀`. -/
structure ISw (d : List ℕ) (W : ℕ) (k r : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 16 → x ≠ 22 → x ≠ 23 → c.nreg x = c₀.nreg x
  r16 : c.nreg 16 ≤ dim d
  rowk : ∀ j < dim d, c.nmem (k * dim d + j) =
    if j < c.nreg 16 then c₀.nmem (r * dim d + j) else c₀.nmem (k * dim d + j)
  rowr : ∀ j < dim d, c.nmem (r * dim d + j) =
    if j < c.nreg 16 then c₀.nmem (k * dim d + j) else c₀.nmem (r * dim d + j)
  oth : ∀ a, (∀ j < dim d, a ≠ k * dim d + j ∧ a ≠ r * dim d + j) → c.nmem a = c₀.nmem a
  out : c.output = c₀.output

section swap
variable {d : List ℕ} {W : ℕ}

theorem swapStep_exec (he : DEnc d W) {k r : ℕ} {c₀ : Config} (hR : Regs d c₀)
    (hk : k < dim d) (hr : r < dim d) (hkr : k ≠ r)
    (h24 : c₀.nreg 24 = k * dim d) (h25 : c₀.nreg 25 = r * dim d)
    (c : Config) (hI : ISw d W k r c₀ c) (hlt : c.nreg 16 < dim d) :
    ∃ c' k', Exec (inp d) W swapStep c c' k' ∧ ISw d W k r c₀ c' ∧
      (dim d - c'.nreg 16) * 9 + k' + 2 ≤ (dim d - c.nreg 16) * 9 := by
  have hc := hI.wb
  have hW := he.dim_sq
  have hnW : dim d + 2 ≤ W := by nlinarith
  obtain ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ := regs_of_keepsR hR fun x hx => hI.regs x
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have e24 : c.nreg 24 = k * dim d := by
    rw [hI.regs 24 (by omega) (by omega) (by omega) (by omega) (by omega), h24]
  have e25 : c.nreg 25 = r * dim d := by
    rw [hI.regs 25 (by omega) (by omega) (by omega) (by omega) (by omega), h25]
  have hik := DetMod.idx_lt hk hlt
  have hir := DetMod.idx_lt hr hlt
  have hne : ∀ j' j'', j' < dim d → j'' < dim d → k * dim d + j' ≠ r * dim d + j'' := by
    intro j' j'' h1 h2 e; exact hkr (DetMod.idx_inj h1 h2 e).1
  have hmk : c.nmem (k * dim d + c.nreg 16) = c₀.nmem (k * dim d + c.nreg 16) := by
    rw [hI.rowk _ hlt]; simp
  have hmr : c.nmem (r * dim d + c.nreg 16) = c₀.nmem (r * dim d + c.nreg 16) := by
    rw [hI.rowr _ hlt]; simp
  unfold swapStep
  exec_block
  · config_simp; rw [e24]; omega
  · config_simp; rw [e25]; omega
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, fun x a b e f g => ?_, ?_, fun j' hj' => ?_, fun j' hj' => ?_, fun a ha => ?_,
    by config_simp; exact hI.out⟩, ?_⟩
  · config_simp; simp only [upd_apply, a, b, e, f, g, ↓reduceIte]; exact hI.regs x a b e f g
  · config_simp; rw [h1]; omega
  · config_simp; rw [e24, e25, h1]
    rcases lt_trichotomy j' (c.nreg 16) with h | rfl | h
    · rw [upd_other _ _ _ (hne _ _ hj' hlt), upd_other _ _ _ (by omega), hI.rowk j' hj']
      simp [h, show j' < c.nreg 16 + 1 by omega]
    · rw [upd_other _ _ _ (hne _ _ hlt hlt), upd_same, hmr]; simp
    · rw [upd_other _ _ _ (hne _ _ hj' hlt), upd_other _ _ _ (by omega), hI.rowk j' hj']
      simp [show ¬ j' < c.nreg 16 by omega, show ¬ j' < c.nreg 16 + 1 by omega]
  · config_simp; rw [e24, e25, h1]
    rcases lt_trichotomy j' (c.nreg 16) with h | rfl | h
    · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (fun e => hne _ _ hlt hj' e.symm),
        hI.rowr j' hj']
      simp [h, show j' < c.nreg 16 + 1 by omega]
    · rw [upd_same, hmk]; simp
    · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (fun e => hne _ _ hlt hj' e.symm),
        hI.rowr j' hj']
      simp [show ¬ j' < c.nreg 16 by omega, show ¬ j' < c.nreg 16 + 1 by omega]
  · config_simp; rw [e24, e25]
    rw [upd_other _ _ _ (ha _ hlt).2, upd_other _ _ _ (ha _ hlt).1, hI.oth a ha]
  · config_simp; rw [h1]; omega

end swap

/-! ### The inverse of the pivot -/

/-- The potential of the power loop: the number of binary digits of the exponent. -/
def powPot (e : ℕ) : ℕ := if e = 0 then 0 else 12 * (Nat.log 2 e + 1)

/-- The state of the power loop, from `c₀`, computing `a ^ (p - 2)`. -/
structure IPw (d : List ℕ) (W : ℕ) (a : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ x, x ≠ 19 → x ≠ 20 → x ≠ 21 → x ≠ 22 → c.nreg x = c₀.nreg x
  mem : c.nmem = c₀.nmem
  out : c.output = c₀.output
  base_lt : c.nreg 19 < prm d
  res_lt : c.nreg 21 < prm d
  inv : (c.nreg 21 : ZMod (prm d)) * (c.nreg 19 : ZMod (prm d)) ^ c.nreg 20 =
    (a : ZMod (prm d)) ^ (prm d - 2)

section pow
variable {d : List ℕ} {W : ℕ}

theorem powStep_exec (he : DEnc d W) {a : ℕ} {c₀ : Config} (hR : Regs d c₀)
    (c : Config) (hI : IPw d W a c₀ c) (hlt : c.nreg 0 < c.nreg 20) :
    ∃ c' k', Exec (inp d) W powStep c c' k' ∧ IPw d W a c₀ c' ∧
      powPot (c'.nreg 20) + k' + 2 ≤ powPot (c.nreg 20) := by
  have hc := hI.wb
  have hW := he.sq
  have hp := he.prime.two_le
  obtain ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ := regs_of_keepsR hR fun x hx => hI.regs x
    (by omega) (by omega) (by omega) (by omega)
  have hb := hI.base_lt; have hr := hI.res_lt
  have hbb : c.nreg 19 * c.nreg 19 ≤ W := by nlinarith
  have hrb : c.nreg 21 * c.nreg 19 ≤ W := by nlinarith
  rw [h0] at hlt
  have hpot : ∀ e', e' = c.nreg 20 / 2 → ∀ k', k' ≤ 7 → powPot e' + k' + 2 ≤ powPot (c.nreg 20) := by
    rintro e' rfl k' hk'
    unfold powPot
    rcases Nat.lt_or_ge (c.nreg 20) 2 with h | h
    · have e1 : c.nreg 20 = 1 := by omega
      rw [e1]; simp <;> omega
    · rw [Nat.log_div_base]
      have := Nat.log_pos (b := 2) (by omega) h
      simp only [show c.nreg 20 / 2 ≠ 0 by omega, show c.nreg 20 ≠ 0 by omega, ↓reduceIte]
      omega
  have hpm : ∀ x, x % prm d < prm d := fun x => Nat.mod_lt _ (by omega)
  have key : ∀ e : ℕ, (c.nreg 21 : ZMod (prm d)) * (c.nreg 19 : ZMod (prm d)) ^ e =
      ((if e % 2 = 1 then c.nreg 21 * c.nreg 19 % prm d else c.nreg 21 : ℕ) : ZMod (prm d)) *
        (((c.nreg 19 * c.nreg 19) % prm d : ℕ) : ZMod (prm d)) ^ (e / 2) := by
    intro e
    rw [cast_mulmod, ← sq, ← pow_mul]
    conv_lhs => rw [← Nat.div_add_mod e 2]
    rcases Nat.mod_two_eq_zero_or_one e with h | h
    · simp [h] <;> ring
    · simp only [h, ↓reduceIte, cast_mulmod]; rw [pow_add]; ring
  unfold powStep
  refine spec_seq ?_
  exec_block
  try config_simp
  refine spec_seq ?_
  rcases Nat.mod_two_eq_zero_or_one (c.nreg 20) with hpar | hpar
  · refine spec_ifLtN_false (by config_simp; rw [h0, h5]; omega) ?_
    refine spec_skip ‹_› ?_
    exec_block
    · config_simp; exact hbb
    refine ⟨⟨‹_›, fun x a b e f => ?_, by config_simp; exact hI.mem, by config_simp; exact hI.out,
      by config_simp; rw [h3]; exact hpm _, by config_simp; exact hr, ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply, a, b, f, ↓reduceIte]; exact hI.regs x a b e f
    · config_simp; rw [h3, h5, ← hI.inv, key (c.nreg 20)]; simp [hpar]
    · config_simp; rw [h5]; exact hpot _ rfl _ (by omega)
  · refine spec_ifLtN_true (by config_simp; rw [h0, h5]; omega) ?_
    exec_block
    · config_simp; exact hrb
    · config_simp; exact hbb
    refine ⟨⟨‹_›, fun x a b e f => ?_, by config_simp; exact hI.mem, by config_simp; exact hI.out,
      by config_simp; rw [h3]; exact hpm _, by config_simp; rw [h3]; exact hpm _, ?_⟩, ?_⟩
    · config_simp; simp only [upd_apply, a, b, e, f, ↓reduceIte]; exact hI.regs x a b e f
    · config_simp; rw [h3, h5, ← hI.inv, key (c.nreg 20)]; simp [hpar]
    · config_simp; rw [h5]; exact hpot _ rfl _ (by omega)

end pow

/-! ### The row operation -/

/-- The state of the row operation on row `i`, with factor `f`, from `c₀`. -/
structure IEn (d : List ℕ) (W : ℕ) (i k f : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 16 → x ≠ 22 → x ≠ 23 → c.nreg x = c₀.nreg x
  r16_ge : k ≤ c.nreg 16
  r16_le : c.nreg 16 ≤ dim d
  new : ∀ j, k ≤ j → j < c.nreg 16 → c.nmem (i * dim d + j) =
    (c₀.nmem (i * dim d + j) + (prm d - f) * c₀.nmem (k * dim d + j)) % prm d
  oth : ∀ a, (∀ j, k ≤ j → j < c.nreg 16 → a ≠ i * dim d + j) → c.nmem a = c₀.nmem a
  out : c.output = c₀.output

section ent
variable {d : List ℕ} {W : ℕ}

theorem entStep_exec (he : DEnc d W) {i k f : ℕ} {c₀ : Config} (hR : Regs d c₀)
    (hi : i < dim d) (hk : k < dim d) (hik : i ≠ k) (hf : f ≤ prm d)
    (h24 : c₀.nreg 24 = k * dim d) (h25 : c₀.nreg 25 = i * dim d)
    (h18 : c₀.nreg 18 = prm d - f) (hent : ∀ a < dim d * dim d, c₀.nmem a < prm d)
    (c : Config) (hI : IEn d W i k f c₀ c) (hlt : c.nreg 16 < dim d) :
    ∃ c' k', Exec (inp d) W entStep c c' k' ∧ IEn d W i k f c₀ c' ∧
      (dim d - c'.nreg 16) * 11 + k' + 2 ≤ (dim d - c.nreg 16) * 11 := by
  have hc := hI.wb
  have hW := he.dim_sq; have hWp := he.sq
  have hnW : dim d + 2 ≤ W := by nlinarith
  obtain ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ := regs_of_keepsR hR fun x hx => hI.regs x
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have e24 : c.nreg 24 = k * dim d := by
    rw [hI.regs 24 (by omega) (by omega) (by omega) (by omega) (by omega), h24]
  have e25 : c.nreg 25 = i * dim d := by
    rw [hI.regs 25 (by omega) (by omega) (by omega) (by omega) (by omega), h25]
  have e18 : c.nreg 18 = prm d - f := by
    rw [hI.regs 18 (by omega) (by omega) (by omega) (by omega) (by omega), h18]
  have hii := DetMod.idx_lt hi hlt
  have hkk := DetMod.idx_lt hk hlt
  have hne : ∀ j j', j < dim d → j' < dim d → k * dim d + j ≠ i * dim d + j' := by
    intro j j' h1 h2 e; exact hik (DetMod.idx_inj h2 h1 e.symm).1
  have hmi : c.nmem (c.nreg 25 + c.nreg 16) = c₀.nmem (i * dim d + c.nreg 16) := by
    rw [e25]; exact hI.oth _ fun j _ hj e => by
      have := (DetMod.idx_inj hlt (by omega) e).2; omega
  have hmk : c.nmem (c.nreg 24 + c.nreg 16) = c₀.nmem (k * dim d + c.nreg 16) := by
    rw [e24]; exact hI.oth _ fun j _ hj e => hne _ _ hlt (by omega) e
  have ha := hent _ hii; have hb := hent _ hkk
  have hprod : c₀.nmem (k * dim d + c.nreg 16) * (prm d - f) ≤ prm d * prm d := by
    have := Nat.mul_le_mul hb.le (Nat.sub_le (prm d) f); omega
  unfold entStep
  exec_block
  · config_simp; rw [e25]; omega
  · config_simp; rw [e24]; omega
  · config_simp; rw [e18, hmk]; omega
  · config_simp; rw [hmi, e18, hmk]; omega
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, fun x a b e f g => ?_, by config_simp; rw [h1]; have := hI.r16_ge; omega,
    by config_simp; rw [h1]; omega, fun j hj1 hj2 => ?_, fun a ha' => ?_,
    by config_simp; exact hI.out⟩, ?_⟩
  · config_simp; simp only [upd_apply, a, b, e, f, g, ↓reduceIte]; exact hI.regs x a b e f g
  · config_simp
    rw [h1] at hj2
    rw [hmi, hmk, e18, h3, e25]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj2 with hj2 | rfl
    · rw [upd_other _ _ _ (by omega)]; exact hI.new j hj1 hj2
    · rw [upd_same, Nat.mul_comm (c₀.nmem _)]
  · config_simp
    config_simp at ha'
    rw [e25, upd_other _ _ _ (ha' _ hI.r16_ge (by rw [h1]; omega))]
    exact hI.oth a fun j hj1 hj2 => ha' j hj1 (by rw [h1]; omega)
  · config_simp; rw [h1]; omega

end ent

/-- The state of the row operations below the pivot `(k, k)`, from `c₀`. -/
structure IRw (d : List ℕ) (W : ℕ) (k : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → x ≠ 22 → x ≠ 23 → x ≠ 25 →
    c.nreg x = c₀.nreg x
  r15_gt : k < c.nreg 15
  r15_le : c.nreg 15 ≤ dim d
  keep : ∀ i < dim d, ∀ j < dim d, (i ≤ k ∨ c.nreg 15 ≤ i) →
    c.nmem (i * dim d + j) = c₀.nmem (i * dim d + j)
  lt : ∀ a < dim d * dim d, c.nmem a < prm d
  det : (mat (dim d) (prm d) c.nmem).det = (mat (dim d) (prm d) c₀.nmem).det
  col : ∀ i, k < i → i < c.nreg 15 → c.nmem (i * dim d + k) = 0
  tri : ∀ j < k, ∀ i < dim d, j < i → c.nmem (i * dim d + j) = 0
  out : c.output = c₀.output

section rows
variable {d : List ℕ} {W : ℕ}

theorem zero_of_cast {p a : ℕ} (ha : a < p) (h : (a : ZMod p) = 0) : a = 0 := by
  rw [ZMod.natCast_eq_zero_iff] at h
  exact Nat.eq_zero_of_dvd_of_lt h ha

theorem rowStep_exec (he : DEnc d W) {k : ℕ} {c₀ : Config} (hR : Regs d c₀) (hk : k < dim d)
    (h6 : c₀.nreg 6 = k) (h24 : c₀.nreg 24 = k * dim d) (h14 : c₀.nreg 14 < prm d)
    (hinv : (c₀.nreg 14 : ZMod (prm d)) * (c₀.nmem (k * dim d + k) : ZMod (prm d)) = 1)
    (c : Config) (hI : IRw d W k c₀ c) (hlt : c.nreg 15 < dim d) :
    ∃ c' k', Exec (inp d) W rowStep c c' k' ∧ IRw d W k c₀ c' ∧
      (dim d - c'.nreg 15) * (11 * dim d + 12) + k' + 2 ≤
        (dim d - c.nreg 15) * (11 * dim d + 12) := by
  have hc := hI.wb
  have hW := he.dim_sq; have hWp := he.sq
  have hp2 := he.prime.two_le
  have hnW : dim d + 2 ≤ W := by nlinarith
  have hR' : Regs d c := regs_of_keepsR hR fun x hx => hI.regs x (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ := hR'
  have e6 : c.nreg 6 = k := by
    rw [hI.regs 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), h6]
  have e14 : c.nreg 14 = c₀.nreg 14 := hI.regs 14 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have e24 : c.nreg 24 = k * dim d := by
    rw [hI.regs 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), h24]
  have hki := hI.r15_gt
  generalize hi_def : c.nreg 15 = i at hlt hki
  have hiik := DetMod.idx_lt hlt hk
  have hmik : c.nmem (i * dim d + k) < prm d := hI.lt _ hiik
  have hmkk : c.nmem (k * dim d + k) = c₀.nmem (k * dim d + k) := hI.keep k hk k hk (Or.inl le_rfl)
  have hprod : c.nmem (i * dim d + k) * c₀.nreg 14 ≤ W :=
    (Nat.mul_le_mul hmik.le h14.le).trans (by omega)
  have hin : i * dim d ≤ W := (Nat.mul_le_mul_right (dim d) hlt.le).trans (by omega)
  generalize hf_def : c.nmem (i * dim d + k) * c₀.nreg 14 % prm d = f
  have hflt : f < prm d := by rw [← hf_def]; exact Nat.mod_lt _ (by omega)
  have key : ∀ c₁ : Config, WordsBounded W c₁ →
      (∀ x, x ≠ 9 → x ≠ 10 → x ≠ 16 → x ≠ 17 → x ≠ 18 → x ≠ 25 → c₁.nreg x = c.nreg x) →
      c₁.nreg 25 = i * dim d → c₁.nreg 16 = k → c₁.nreg 18 = prm d - f → c₁.nmem = c.nmem →
      c₁.output = c.output → ∀ K, K ≤ 7 →
      ∃ c' k₂, Exec (inp d) W (.seq (.whileLtN 16 2 entStep) (.instr (.addN 15 15 1))) c₁ c' k₂ ∧
        IRw d W k c₀ c' ∧ (dim d - c'.nreg 15) * (11 * dim d + 12) + (K + k₂) + 2 ≤
          (dim d - i) * (11 * dim d + 12) := by
    intro c₁ hw₁ hr₁ h25₁ h16₁ h18₁ hm₁ ho₁ K hK
    have hR₁ : Regs d c₁ := regs_of_keepsR ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ fun x hx =>
      hr₁ x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have h24₁ : c₁.nreg 24 = k * dim d := by
      rw [hr₁ 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), e24]
    have hent₁ : ∀ a < dim d * dim d, c₁.nmem a < prm d := fun a ha => by rw [hm₁]; exact hI.lt a ha
    have hIE : IEn d W i k f c₁ c₁ := ⟨hw₁, fun _ _ _ _ _ _ => rfl, by rw [h16₁], by rw [h16₁]; omega,
      fun j hj1 hj2 => by rw [h16₁] at hj2; omega, fun _ _ => rfl, rfl⟩
    obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 16)
      (b := 2) (body := entStep) (IEn d W i k f c₁) (fun c => (dim d - c.nreg 16) * 11)
      (fun c h => h.wb) (fun c' hc' hlt' => entStep_exec he hR₁ hlt hk (by omega) hflt.le h24₁
        h25₁ h18₁ hent₁ c' hc' (by
          rw [hc'.regs 2 (by omega) (by omega) (by omega) (by omega) (by omega), hR₁.2.2.1] at hlt'
          exact hlt')) hIE
    have h16₂ : c₂.nreg 16 = dim d := by
      have := hI₂.r16_le
      rw [hI₂.regs 2 (by omega) (by omega) (by omega) (by omega) (by omega), hR₁.2.2.1] at hn₂
      omega
    have hr₂ : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 16 → x ≠ 17 → x ≠ 18 → x ≠ 22 → x ≠ 23 → x ≠ 25 →
        c₂.nreg x = c.nreg x := fun x a b e f' g h l m =>
      (hI₂.regs x a b e h l).trans (hr₁ x a b e f' g m)
    have e15₂ : c₂.nreg 15 = i := (hr₂ 15 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)).trans hi_def
    have e1₂ : c₂.nreg 1 = 1 := by
      rw [hr₂ 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), h1]
    -- the memory after the row operation
    have hrowi : ∀ j < dim d, c₂.nmem (i * dim d + j) = if k ≤ j then
        (c.nmem (i * dim d + j) + (prm d - f) * c.nmem (k * dim d + j)) % prm d
        else c.nmem (i * dim d + j) := fun j hj => by
      split_ifs with hkj
      · rw [hI₂.new j hkj (by omega), hm₁]
      · rw [hI₂.oth _ fun j' hj1 hj2 e => by
          have := (DetMod.idx_inj hj (by omega) e).2; omega, hm₁]
    have hoth : ∀ i' < dim d, i' ≠ i → ∀ j < dim d, c₂.nmem (i' * dim d + j) = c.nmem (i' * dim d + j) :=
      fun i' hi' hne j hj => by
        rw [hI₂.oth _ fun j' hj1 hj2 e => hne (DetMod.idx_inj hj (by omega) e).1, hm₁]
    have e2 := Exec.addN (P := inp d) hI₂.wb 15 15 1 (by rw [e15₂, e1₂]; omega)
    refine ⟨_, _, .seq e₂ e2, ⟨e2.wb_right, fun x a b e f' g h l m n' => ?_, ?_, ?_,
      fun i' hi' j hj hor => ?_, fun a ha => ?_, ?_, fun i' hi1 hi2 => ?_, fun j hj i' hi' hji => ?_,
      ?_⟩, ?_⟩
    · config_simp; rw [upd_other _ _ _ e, hr₂ x a b f' g h l m n']
      exact hI.regs x a b e f' g h l m n'
    · config_simp; rw [e15₂, e1₂]; omega
    · config_simp; rw [e15₂, e1₂]; omega
    · config_simp
      config_simp at hor
      rw [hoth i' hi' (by omega) j hj]
      exact hI.keep i' hi' j hj (by rw [hi_def]; omega)
    · config_simp
      by_cases hrow : ∃ j < dim d, k ≤ j ∧ a = i * dim d + j
      · obtain ⟨j, hj, hkj, rfl⟩ := hrow
        rw [hrowi j hj, DetMod.iteP hkj]; exact Nat.mod_lt _ (by omega)
      · push Not at hrow
        have hai : ∀ j, k ≤ j → j < c₂.nreg 16 → a ≠ i * dim d + j := fun j h1 h2 =>
          hrow j (by omega) h1
        rw [hI₂.oth a hai, hm₁]; exact hI.lt a ha
    · config_simp
      rw [DetMod.det_rowop (m := c.nmem) hlt hk (by omega) (f : ZMod (prm d)) (fun j hj => ?_)
        (fun i' hi' hne j hj => hoth i' hi' hne j hj), hI.det]
      rw [hrowi j hj]
      split_ifs with hkj
      · exact DetMod.cast_combo hflt.le
      · have h1' : c.nmem (i * dim d + j) = 0 := hI.tri j (by omega) i hlt (by omega)
        have h2' : c.nmem (k * dim d + j) = 0 := hI.tri j (by omega) k hk (by omega)
        rw [h1', h2']; simp
    · config_simp
      rw [e15₂, e1₂] at hi2
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi2 with hi2 | rfl
      · rw [hoth i' (by omega) (by omega) k hk]; exact hI.col i' hi1 (by rw [hi_def]; exact hi2)
      · rw [hrowi k hk, DetMod.iteP le_rfl]
        refine zero_of_cast (Nat.mod_lt _ (by omega)) ?_
        rw [DetMod.cast_combo hflt.le, ← hf_def, DetMod.cast_mulmod, hmkk]
        rw [mul_assoc, hinv]; ring
    · config_simp
      by_cases hii : i' = i
      · subst hii; rw [hrowi j (by omega), DetMod.iteN (by omega)]; exact hI.tri j hj _ hi' hji
      · rw [hoth i' hi' hii j (by omega)]; exact hI.tri j hj i' hi' hji
    · config_simp; rw [hI₂.out, ho₁]; exact hI.out
    · config_simp; rw [e15₂, e1₂]
      have := Nat.sub_le (dim d) (c₁.nreg 16)
      rw [h16₁] at hk₂
      have : (dim d - i) * (11 * dim d + 12) = (dim d - (i + 1)) * (11 * dim d + 12) +
          (11 * dim d + 12) := by
        rw [← Nat.add_one_mul]; congr 1; omega
      omega
  rw [← hi_def] at key ⊢
  unfold rowStep
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h2, hi_def]; exact hin
  · config_simp; rw [h2, e6, hi_def]; omega
  · config_simp; rw [e14, h2, e6, hi_def]; exact hprod
  refine key _ ‹_› (fun x a b e f' g h => ?_) (by config_simp; rw [h2, hi_def])
    (by config_simp; exact e6) ?_ (by config_simp) (by config_simp) _ (by omega)
  · config_simp; simp only [upd_apply, a, b, e, f', g, h, ↓reduceIte]
  · config_simp; rw [h3, h2, e6, e14, hi_def, hf_def]

end rows

/-! ### Elimination below a pivot -/

/-- What the elimination below the pivot `(k, k)` achieves, from `c₀`. -/
structure ElimPost (d : List ℕ) (k : ℕ) (c₀ c : Config) : Prop where
  regs : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 14 → x ≠ 15 → x ≠ 16 → x ≠ 17 → x ≠ 18 → x ≠ 19 → x ≠ 20 →
    x ≠ 21 → x ≠ 22 → x ≠ 23 → x ≠ 25 → c.nreg x = c₀.nreg x
  keep : ∀ i < dim d, ∀ j < dim d, i ≤ k → c.nmem (i * dim d + j) = c₀.nmem (i * dim d + j)
  lt : ∀ a < dim d * dim d, c.nmem a < prm d
  det : (mat (dim d) (prm d) c.nmem).det = (mat (dim d) (prm d) c₀.nmem).det
  col : ∀ i, k < i → i < dim d → c.nmem (i * dim d + k) = 0
  tri : ∀ j < k, ∀ i < dim d, j < i → c.nmem (i * dim d + j) = 0
  out : c.output = c₀.output

section elimination
variable {d : List ℕ} {W : ℕ}

theorem powPot_le (e : ℕ) : powPot e ≤ 12 * e := by
  unfold powPot
  split_ifs with h
  · omega
  · have := Nat.log_lt_self 2 h; omega

theorem elim_exec (he : DEnc d W) {k : ℕ} (c : Config) (hw : WordsBounded W c) (hR : Regs d c)
    (hk : k < dim d) (h6 : c.nreg 6 = k) (h24 : c.nreg 24 = k * dim d)
    (h9 : c.nreg 9 = c.nmem (k * dim d + k))
    (hpiv : (c.nmem (k * dim d + k) : ZMod (prm d)) ≠ 0)
    (hlt : ∀ a < dim d * dim d, c.nmem a < prm d)
    (htri : ∀ j < k, ∀ i < dim d, j < i → c.nmem (i * dim d + j) = 0) :
    ∃ c' k', Exec (inp d) W elim c c' k' ∧ WordsBounded W c' ∧ ElimPost d k c c' ∧
      k' ≤ dim d * (11 * dim d + 12) + powPot (prm d - 2) + 12 := by
  haveI := Fact.mk he.prime
  have hp2 := he.prime.two_le
  obtain ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ := hR
  have hkk := DetMod.idx_lt hk hk
  have hpivlt := hlt _ hkk
  -- the power
  have e₁ : ∃ c₁ k₁, Exec (inp d) W (block [.copyN 19 9, .copyN 20 13, .copyN 21 1]) c c₁ k₁ ∧
      IPw d W (c.nmem (k * dim d + k)) c₁ c₁ ∧ k₁ = 3 ∧ c₁.nreg 20 = prm d - 2 ∧
      (∀ x, x ≠ 19 → x ≠ 20 → x ≠ 21 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output := by
    exec_block
    refine ⟨⟨‹_›, fun _ _ _ _ _ => rfl, rfl, rfl, by config_simp; rw [h9]; exact hpivlt,
      by config_simp; rw [h1]; omega, ?_⟩, rfl, by config_simp; exact h13,
      fun x a b e => by config_simp; simp only [upd_apply, a, b, e, ↓reduceIte], rfl, rfl⟩
    config_simp; rw [h1, h9, h13]; simp
  obtain ⟨c₁, k₁, e₁, hP₁, rfl, h20₁, hr₁, hm₁, ho₁⟩ := e₁
  have hR₁ : Regs d c₁ := regs_of_keepsR ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ fun x hx =>
    hr₁ x (by omega) (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, hP₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 0)
    (b := 20) (body := powStep) (IPw d W (c.nmem (k * dim d + k)) c₁) (fun c => powPot (c.nreg 20))
    (fun c h => h.wb) (fun c' hc' hlt' => powStep_exec he hR₁ c' hc' hlt') hP₁
  have hr₂ : ∀ x, x ≠ 19 → x ≠ 20 → x ≠ 21 → x ≠ 22 → c₂.nreg x = c.nreg x := fun x a b e f =>
    (hP₂.regs x a b e f).trans (hr₁ x a b e)
  have h20₂ : c₂.nreg 20 = 0 := by
    rw [hr₂ 0 (by omega) (by omega) (by omega) (by omega), h0] at hn₂; omega
  have hinv : (c₂.nreg 21 : ZMod (prm d)) * (c.nmem (k * dim d + k) : ZMod (prm d)) = 1 := by
    have := hP₂.inv; rw [h20₂, pow_zero, mul_one] at this
    rw [this]; exact DetMod.fermat hpiv
  -- the rows
  have hw₂ := hP₂.wb
  have e₃ : ∃ c₃ k₃, Exec (inp d) W (block [.copyN 14 21, .addN 15 6 1]) c₂ c₃ k₃ ∧
      WordsBounded W c₃ ∧ k₃ = 2 ∧ c₃.nreg 14 = c₂.nreg 21 ∧ c₃.nreg 15 = k + 1 ∧
      (∀ x, x ≠ 14 → x ≠ 15 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.output = c₂.output := by
    have e6 : c₂.nreg 6 = k := by rw [hr₂ 6 (by omega) (by omega) (by omega) (by omega), h6]
    have e1 : c₂.nreg 1 = 1 := by rw [hr₂ 1 (by omega) (by omega) (by omega) (by omega), h1]
    exec_block
    · config_simp; rw [e6, e1]; have := he.dim_sq; nlinarith
    refine ⟨‹_›, rfl, by config_simp, by config_simp; rw [e6, e1], fun x a b => by
      config_simp; simp only [upd_apply, a, b, ↓reduceIte], rfl, rfl⟩
  obtain ⟨c₃, k₃, e₃, hw₃, rfl, h14₃, h15₃, hr₃, hm₃, ho₃⟩ := e₃
  have hm₂ : c₂.nmem = c.nmem := hP₂.mem.trans hm₁
  have hR₃ : Regs d c₃ := regs_of_keepsR ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ fun x hx => by
    rw [hr₃ x (by omega) (by omega), hr₂ x (by omega) (by omega) (by omega) (by omega)]
  have hI₃ : IRw d W k c₃ c₃ := ⟨hw₃, fun _ _ _ _ _ _ _ _ _ _ => rfl, by omega, by omega,
    fun _ _ _ _ _ => rfl, fun a ha => by rw [hm₃, hm₂]; exact hlt a ha, rfl,
    fun i h1' h2' => by omega, fun j hj i hi hji => by rw [hm₃, hm₂]; exact htri j hj i hi hji, rfl⟩
  have e6₃ : c₃.nreg 6 = k := by
    rw [hr₃ 6 (by omega) (by omega), hr₂ 6 (by omega) (by omega) (by omega) (by omega), h6]
  have e24₃ : c₃.nreg 24 = k * dim d := by
    rw [hr₃ 24 (by omega) (by omega), hr₂ 24 (by omega) (by omega) (by omega) (by omega), h24]
  have hmkk : c₃.nmem (k * dim d + k) = c.nmem (k * dim d + k) := by rw [hm₃, hm₂]
  obtain ⟨c₄, k₄, e₄, hI₄, hn₄, hk₄⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 15)
    (b := 2) (body := rowStep) (IRw d W k c₃) (fun c => (dim d - c.nreg 15) * (11 * dim d + 12))
    (fun c h => h.wb) (fun c' hc' hlt' => rowStep_exec he hR₃ hk e6₃ e24₃
      (by rw [h14₃]; exact hP₂.res_lt) (by rw [h14₃, hmkk]; exact hinv) c' hc' (by
        rw [hc'.regs 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega), hR₃.2.2.1] at hlt'
        exact hlt')) hI₃
  have h15₄ : c₄.nreg 15 = dim d := by
    have := hI₄.r15_le
    rw [hI₄.regs 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), hR₃.2.2.1] at hn₄
    omega
  refine ⟨c₄, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), hI₄.wb, ⟨fun x a b e f g h l m n' o q r s' => ?_,
    fun i hi j hj hik => ?_, hI₄.lt, ?_, fun i h1' h2' => hI₄.col i h1' (by omega), hI₄.tri, ?_⟩, ?_⟩
  · rw [hI₄.regs x a b f g h l q r s', hr₃ x e f, hr₂ x m n' o q]
  · rw [hI₄.keep i hi j hj (Or.inl hik), hm₃, hm₂]
  · rw [hI₄.det, hm₃, hm₂]
  · rw [hI₄.out, ho₃, hP₂.out, ho₁]
  · rw [h20₁] at hk₂
    rw [h15₃] at hk₄
    have := Nat.sub_le (dim d) (k + 1)
    have : (dim d - (k + 1)) * (11 * dim d + 12) ≤ dim d * (11 * dim d + 12) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

end elimination

/-! ### One column -/

/-- The state between columns. -/
structure IK (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  k_le : c.nreg 6 ≤ dim d
  lt : ∀ a < dim d * dim d, c.nmem a < prm d
  tri : ∀ j < c.nreg 6, ∀ i < dim d, j < i → c.nmem (i * dim d + j) = 0
  acc_lt : c.nreg 11 < prm d
  sgn : ∃ s : ZMod (prm d), (s = 1 ∨ s = -1) ∧
    (mat (dim d) (prm d) c.nmem).det = s * (inMat d).det ∧
    (c.nreg 11 : ZMod (prm d)) = s * diag (dim d) (prm d) c.nmem (c.nreg 6)
  out : c.output = []

section column
variable {d : List ℕ} {W : ℕ}

/-- After the pivot search and the exchange. -/
structure AfterSwap (d : List ℕ) (W : ℕ) (k : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  regs : ∀ x, x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 16 → x ≠ 22 → x ≠ 23 → x ≠ 24 →
    x ≠ 25 → c.nreg x = c₀.nreg x
  r24 : c.nreg 24 = k * dim d
  lt : ∀ a < dim d * dim d, c.nmem a < prm d
  tri : ∀ j < k, ∀ i < dim d, j < i → c.nmem (i * dim d + j) = 0
  low : ∀ i < k, ∀ j < dim d, c.nmem (i * dim d + j) = c₀.nmem (i * dim d + j)
  zero : c.nmem (k * dim d + k) = 0 → ∀ i, k ≤ i → i < dim d → c.nmem (i * dim d + k) = 0
  acc_lt : c.nreg 11 < prm d
  sgn : ∃ s : ZMod (prm d), (s = 1 ∨ s = -1) ∧
    (mat (dim d) (prm d) c.nmem).det = s * (mat (dim d) (prm d) c₀.nmem).det ∧
    (c.nreg 11 : ZMod (prm d)) = s * c₀.nreg 11
  out : c.output = c₀.output

theorem searchSwap_exec (he : DEnc d W) (c : Config) (hI : IK d W c) (hk : c.nreg 6 < dim d) :
    ∃ c' k', Exec (inp d) W (.seq (block [.mulN 24 6 2, .copyN 7 6, .copyN 8 2]) <|
      .seq (.whileLtN 7 2 scanStep) (.ifLtN 6 8 (.ifLtN 8 2 (.seq (block [.mulN 25 8 2, .copyN 16 0,
        .mulN 11 11 12, .modN 11 11 3]) (.whileLtN 16 2 swapStep)) .skip) .skip)) c c' k' ∧
      AfterSwap d W (c.nreg 6) c c' ∧ k' ≤ 17 * dim d + 16 := by
  have hc := hI.wb
  have hW := he.dim_sq; have hWp := he.sq
  have hp2 := he.prime.two_le
  have hnW : dim d + 2 ≤ W := by nlinarith
  obtain ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ := hI.regs
  set k := c.nreg 6 with hk_def
  -- the head
  have eA : ∃ c₁ k₁, Exec (inp d) W (block [.mulN 24 6 2, .copyN 7 6, .copyN 8 2]) c c₁ k₁ ∧
      ISc d W k c₁ c₁ ∧ k₁ = 3 ∧ c₁.nreg 24 = k * dim d ∧
      (∀ x, x ≠ 7 → x ≠ 8 → x ≠ 24 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output := by
    exec_block
    · rw [h2]; exact (Nat.mul_le_mul_right _ hk.le).trans (by omega)
    refine ⟨⟨‹_›, fun _ _ _ _ _ _ => rfl, rfl, rfl, by config_simp; rw [← hk_def],
      by config_simp; omega, Or.inl ⟨by config_simp; exact h2, fun r h1' h2' => by
        config_simp at h2'; omega⟩⟩, rfl, by config_simp; rw [h2], fun x a b e => by
          config_simp; simp only [upd_apply, a, b, e, ↓reduceIte], rfl, rfl⟩
  obtain ⟨c₁, k₁, eA, hS₁, rfl, h24₁, hr₁, hm₁, ho₁⟩ := eA
  have hR₁ : Regs d c₁ := regs_of_keepsR hI.regs fun x hx => hr₁ x (by omega) (by omega) (by omega)
  have e6₁ : c₁.nreg 6 = k := by rw [hr₁ 6 (by omega) (by omega) (by omega)]
  obtain ⟨c₂, k₂, eB, hS₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 7)
    (b := 2) (body := scanStep) (ISc d W k c₁) (fun c => (dim d - c.nreg 7) * 8) (fun c h => h.wb)
    (fun c' hc' hlt' => scanStep_exec he hR₁ e6₁ hk c' hc' (by
      rw [hc'.regs 2 (by omega) (by omega) (by omega) (by omega) (by omega), hR₁.2.2.1] at hlt'
      exact hlt')) hS₁
  have hr₂ : ∀ x, x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → x ≠ 24 → x ≠ 25 → c₂.nreg x = c.nreg x :=
    fun x a b e f g l => (hS₂.regs x a b e f l).trans (hr₁ x a b g)
  have hm₂ : c₂.nmem = c.nmem := hS₂.mem.trans hm₁
  have e2₂ : c₂.nreg 2 = dim d := by
    rw [hr₂ 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h2]
  have e6₂ : c₂.nreg 6 = k := by
    rw [hr₂ 6 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have e24₂ : c₂.nreg 24 = k * dim d := by
    rw [hS₂.regs 24 (by omega) (by omega) (by omega) (by omega) (by omega), h24₁]
  have h7₂ : c₂.nreg 7 = dim d := by have := hS₂.r7_le; rw [e2₂] at hn₂; omega
  have hk₂' : k₂ ≤ 8 * dim d + 2 := by
    beta_reduce at hk₂
    have := Nat.sub_le (dim d) (c₁.nreg 7)
    have : (dim d - c₁.nreg 7) * 8 ≤ dim d * 8 := Nat.mul_le_mul_right _ this
    omega
  have hlow_id : ∀ c' : Config, c'.nmem = c.nmem → ∀ i < k, ∀ j < dim d,
      c'.nmem (i * dim d + j) = c.nmem (i * dim d + j) := fun c' h _ _ _ _ => by rw [h]
  have hpost : ∀ c' : Config, WordsBounded W c' →
      (∀ x, x ≠ 7 → x ≠ 8 → x ≠ 9 → x ≠ 10 → c'.nreg x = c₂.nreg x) →
      c'.nmem = c₂.nmem → c'.output = c₂.output →
      (c.nmem (k * dim d + k) = 0 → ∀ i, k ≤ i → i < dim d → c.nmem (i * dim d + k) = 0) →
      AfterSwap d W k c c' := by
    intro c' hw hr hm ho hz
    refine ⟨hw, fun x a b e f g h l m n' o => ?_, ?_, fun a ha => ?_, fun j hj i hi hji => ?_,
      fun i hi j hj => by rw [hm, hm₂], fun h i h1' h2' => ?_, ?_, ⟨1, Or.inl rfl, ?_, ?_⟩, ?_⟩
    · rw [hr x a b e f, hr₂ x a b e f n' o]
    · rw [hr 24 (by omega) (by omega) (by omega) (by omega)]; exact e24₂
    · rw [hm, hm₂]; exact hI.lt a ha
    · rw [hm, hm₂]; exact hI.tri j hj i hi hji
    · rw [hm, hm₂] at h ⊢; exact hz h i h1' h2'
    · rw [hr 11 (by omega) (by omega) (by omega) (by omega),
        hr₂ 11 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hI.acc_lt
    · rw [hm, hm₂, one_mul]
    · rw [hr 11 (by omega) (by omega) (by omega) (by omega),
        hr₂ 11 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), one_mul]
    · rw [ho, hS₂.out, ho₁]
  rcases hS₂.found with ⟨h8, hz⟩ | ⟨hk8, h8n, hnz, -⟩
  · -- no nonzero entry: no exchange
    refine ⟨c₂, _, .seq eA (.seq eB (.ifLtN_true (by rw [e6₂, h8]; exact hk)
      (.ifLtN_false (by rw [h8, e2₂]; omega) (.skip hS₂.wb)))), hpost c₂ hS₂.wb (fun _ _ _ _ _ => rfl)
      rfl rfl (fun _ i h1' h2' => by rw [← hm₂]; exact hz i h1' (by omega)), by omega⟩
  by_cases hkr : c₂.nreg 8 = k
  · -- the pivot is in place
    refine ⟨c₂, _, .seq eA (.seq eB (.ifLtN_false (by rw [e6₂, hkr]; omega) (.skip hS₂.wb))),
      hpost c₂ hS₂.wb (fun _ _ _ _ _ => rfl) rfl rfl (fun h => by
        rw [← hm₂] at h; rw [hkr] at hnz; exact absurd h hnz), by omega⟩
  -- the exchange
  set r := c₂.nreg 8 with hr_def
  have hkr' : k < r := by omega
  have eS : ∃ c₃ k₃, Exec (inp d) W (block [.mulN 25 8 2, .copyN 16 0, .mulN 11 11 12,
      .modN 11 11 3]) c₂ c₃ k₃ ∧ ISw d W k r c₃ c₃ ∧ k₃ = 4 ∧ c₃.nreg 25 = r * dim d ∧
      c₃.nreg 11 = c.nreg 11 * (prm d - 1) % prm d ∧
      (∀ x, x ≠ 11 → x ≠ 16 → x ≠ 25 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.output = c₂.output := by
    have e11 : c₂.nreg 11 = c.nreg 11 := hr₂ 11 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
    have e12 : c₂.nreg 12 = prm d - 1 := by
      rw [hr₂ 12 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h12]
    have e0 : c₂.nreg 0 = 0 := by
      rw [hr₂ 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h0]
    have e3 : c₂.nreg 3 = prm d := by
      rw [hr₂ 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h3]
    have hacc := hI.acc_lt
    have hw₂ := hS₂.wb
    clear eA eB
    exec_block
    · rw [e2₂]; exact (Nat.mul_le_mul_right _ h8n.le).trans (by omega)
    · config_simp; rw [e11, e12]
      exact (Nat.mul_le_mul hacc.le (Nat.sub_le _ _)).trans (by omega)
    refine ⟨⟨‹_›, fun _ _ _ _ _ _ => rfl, by config_simp; rw [e0]; omega, fun j hj => ?_,
      fun j hj => ?_, fun _ _ => rfl, rfl⟩, rfl, by config_simp; rw [e2₂], by
        config_simp; rw [e11, e12, e3], fun x a b e => by
          config_simp; simp only [upd_apply, a, b, e, ↓reduceIte], rfl, rfl⟩
    · config_simp; rw [e0]; simp
    · config_simp; rw [e0]; simp
  obtain ⟨c₃, k₃, eS, hW₃, rfl, h25₃, h11₃, hr₃, hm₃, ho₃⟩ := eS
  have hR₃ : Regs d c₃ := regs_of_keepsR hI.regs fun x hx => by
    rw [hr₃ x (by omega) (by omega) (by omega), hr₂ x (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)]
  obtain ⟨c₄, k₄, eL, hW₄, hn₄, hk₄⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 16)
    (b := 2) (body := swapStep) (ISw d W k r c₃) (fun c => (dim d - c.nreg 16) * 9)
    (fun c h => h.wb) (fun c' hc' hlt' => swapStep_exec he hR₃ hk h8n (by omega)
      (by rw [hr₃ 24 (by omega) (by omega) (by omega)]; exact e24₂) h25₃ c' hc' (by
        rw [hc'.regs 2 (by omega) (by omega) (by omega) (by omega) (by omega), hR₃.2.2.1] at hlt'
        exact hlt')) hW₃
  have h16₄ : c₄.nreg 16 = dim d := by
    have := hW₄.r16; rw [hW₄.regs 2 (by omega) (by omega) (by omega) (by omega) (by omega),
      hR₃.2.2.1] at hn₄; omega
  have hm₃' : c₃.nmem = c.nmem := hm₃.trans hm₂
  -- the rows after the exchange
  have hsw : ∀ i < dim d, ∀ j < dim d, c₄.nmem (i * dim d + j) =
      c.nmem ((if i = k then r else if i = r then k else i) * dim d + j) := by
    intro i hi j hj
    by_cases hik : i = k
    · subst hik; rw [hW₄.rowk j hj, h16₄, DetMod.iteP hj, hm₃']; simp
    · by_cases hir : i = r
      · subst hir; rw [hW₄.rowr j hj, h16₄, DetMod.iteP hj, hm₃']; simp [hik]
      · rw [hW₄.oth _ fun j' hj' => ⟨fun e => hik (DetMod.idx_inj hj hj' e).1,
          fun e => hir (DetMod.idx_inj hj hj' e).1⟩, hm₃']
        simp [hik, hir]
  have hrk : ∀ x, x ≠ 9 → x ≠ 10 → x ≠ 11 → x ≠ 16 → x ≠ 22 → x ≠ 23 → x ≠ 25 →
      c₄.nreg x = c₂.nreg x := fun x a b e f g h l =>
    (hW₄.regs x a b f g h).trans (hr₃ x e f l)
  refine ⟨c₄, _, .seq eA (.seq eB (.ifLtN_true (by rw [e6₂]; exact hkr')
    (.ifLtN_true (by rw [e2₂]; exact h8n) (.seq eS eL)))), ⟨hW₄.wb, fun x a b e f g h l m n' o => ?_,
      ?_, fun a ha => ?_, fun j hj i hi hji => ?_, fun i hi j hj => ?_, fun h => ?_, ?_, ⟨-1,
      Or.inr rfl, ?_, ?_⟩, ?_⟩, ?_⟩
  · rw [hrk x e f g h l m o, hr₂ x a b e f n' o]
  · rw [hrk 24 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact e24₂
  · -- entries stay residues
    by_cases hrow : ∃ i < dim d, ∃ j < dim d, a = i * dim d + j
    · obtain ⟨i, hi, j, hj, rfl⟩ := hrow
      rw [hsw i hi j hj]
      exact hI.lt _ (DetMod.idx_lt (by split_ifs <;> omega) hj)
    · push Not at hrow
      have : a = (a / dim d) * dim d + a % dim d := by rw [Nat.mul_comm]; exact (Nat.div_add_mod a _).symm
      exact absurd this (hrow _ (by
        have hn : 0 < dim d := by omega
        exact (Nat.div_lt_iff_lt_mul hn).2 ha) _ (Nat.mod_lt _ (by omega)))
  · rw [hsw i hi j (by omega)]
    split_ifs with h1' h2'
    · exact hI.tri j hj r h8n (by omega)
    · exact hI.tri j hj k hk (by omega)
    · exact hI.tri j hj i hi hji
  · rw [hsw i (by omega) j hj]; simp [show i ≠ k by omega, show i ≠ r by omega]
  · rw [hsw k hk k hk] at h; simp at h; rw [hm₂] at hnz; exact absurd h hnz
  · rw [hW₄.regs 11 (by omega) (by omega) (by omega) (by omega) (by omega), h11₃]
    exact Nat.mod_lt _ (by omega)
  · rw [DetMod.det_swap (m := c.nmem) hk h8n (by omega) hsw]; ring
  · rw [hW₄.regs 11 (by omega) (by omega) (by omega) (by omega) (by omega), h11₃,
      DetMod.cast_mulmod, Nat.cast_sub (by omega), ZMod.natCast_self]; simp
  · rw [hW₄.out, ho₃, hS₂.out, ho₁]
  · omega

/-- The step bound of one column. -/
def colCost (d : List ℕ) : ℕ := 11 * dim d * dim d + 30 * dim d + powPot (prm d - 2) + 50

theorem colStep_exec (he : DEnc d W) (c : Config) (hI : IK d W c) (hk : c.nreg 6 < dim d) :
    ∃ c' k', Exec (inp d) W colStep c c' k' ∧ IK d W c' ∧
      (dim d - c'.nreg 6) * colCost d + k' + 2 ≤ (dim d - c.nreg 6) * colCost d := by
  have hW := he.dim_sq; have hWp := he.sq
  have hp2 := he.prime.two_le
  obtain ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ := hI.regs
  obtain ⟨sc, hsc, hdetc, hacc⟩ := hI.sgn
  obtain ⟨c₃, k₃, e₃, hA, hk₃⟩ := searchSwap_exec he c hI hk
  generalize hk_def : c.nreg 6 = k at hk hA hacc ⊢
  have hkk := DetMod.idx_lt hk hk
  have hr3 : ∀ x, x ≤ 6 ∨ x = 12 ∨ x = 13 → x ≠ 7 → c₃.nreg x = c.nreg x := fun x hx h7 =>
    hA.regs x h7 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)
  have hR₃ : Regs d c₃ := regs_of_keepsR hI.regs fun x hx => hr3 x (by omega) (by omega)
  have e6₃ : c₃.nreg 6 = k := (hr3 6 (by omega) (by omega)).trans hk_def
  have hpivlt : c₃.nmem (k * dim d + k) < prm d := hA.lt _ hkk
  have hacc₃ := hA.acc_lt
  -- the pivot
  have eD : ∃ c₄ k₄, Exec (inp d) W (block [.addN 10 24 6, .loadN 9 10, .mulN 11 11 9,
      .modN 11 11 3]) c₃ c₄ k₄ ∧ WordsBounded W c₄ ∧ k₄ = 4 ∧
      c₄.nreg 9 = c₃.nmem (k * dim d + k) ∧
      c₄.nreg 11 = c₃.nreg 11 * c₃.nmem (k * dim d + k) % prm d ∧
      (∀ x, x ≠ 9 → x ≠ 10 → x ≠ 11 → c₄.nreg x = c₃.nreg x) ∧ c₄.nmem = c₃.nmem ∧
      c₄.output = c₃.output := by
    have hw₃ := hA.wb
    clear e₃
    exec_block
    · rw [hA.r24, e6₃]; omega
    · config_simp; rw [hA.r24, e6₃]
      exact (Nat.mul_le_mul hacc₃.le hpivlt.le).trans (by omega)
    refine ⟨‹_›, rfl, by config_simp; rw [hA.r24, e6₃], by config_simp; rw [hA.r24, e6₃, hR₃.2.2.2.1],
      fun x a b e => by config_simp; simp only [upd_apply, a, b, e, ↓reduceIte], rfl, rfl⟩
  obtain ⟨c₄, k₄, eD, hw₄, rfl, h9₄, h11₄, hr₄, hm₄, ho₄⟩ := eD
  have hR₄ : Regs d c₄ := regs_of_keepsR hR₃ fun x hx => hr₄ x (by omega) (by omega) (by omega)
  -- the common conclusion
  obtain ⟨s3, hs3, hdet3, hacc3⟩ := hA.sgn
  have hdiag : diag (dim d) (prm d) c₃.nmem k = diag (dim d) (prm d) c.nmem k :=
    DetMod.diag_congr fun i hi => hA.low i hi i (by omega)
  have hfin : ∀ (c₅ : Config) (k₅ : ℕ), WordsBounded W c₅ →
      (∀ x, x ≤ 6 ∨ x = 11 ∨ x = 12 ∨ x = 13 → c₅.nreg x = c₄.nreg x) →
      (∀ i < dim d, ∀ j < dim d, i ≤ k → c₅.nmem (i * dim d + j) = c₃.nmem (i * dim d + j)) →
      (∀ a < dim d * dim d, c₅.nmem a < prm d) →
      (mat (dim d) (prm d) c₅.nmem).det = (mat (dim d) (prm d) c₃.nmem).det →
      (∀ i, k < i → i < dim d → c₅.nmem (i * dim d + k) = 0) →
      (∀ j < k, ∀ i < dim d, j < i → c₅.nmem (i * dim d + j) = 0) →
      c₅.output = c₄.output → k₅ ≤ dim d * (11 * dim d + 12) + powPot (prm d - 2) + 14 →
      ∃ c' k', Exec (inp d) W (.instr (.addN 6 6 1)) c₅ c' k' ∧ IK d W c' ∧
        (dim d - c'.nreg 6) * colCost d + (k₃ + (4 + (k₅ + k'))) + 2 ≤
          (dim d - k) * colCost d := by
    intro c₅ k₅ hw₅ hr₅ hkeep hlt5 hdet5 hcol5 htri5 ho5 hk5
    have e6₅ : c₅.nreg 6 = k := by rw [hr₅ 6 (by omega), hr₄ 6 (by omega) (by omega) (by omega), e6₃]
    have e1₅ : c₅.nreg 1 = 1 := by rw [hr₅ 1 (by omega), hr₄ 1 (by omega) (by omega) (by omega),
      hR₃.2.1]
    have eF := Exec.addN (P := inp d) hw₅ 6 6 1 (by rw [e6₅, e1₅]; omega)
    refine ⟨_, 1, eF, ⟨eF.wb_right, regs_of_keepsR hR₄ fun x hx => ?_, ?_, hlt5, ?_, ?_, ?_, ?_⟩, ?_⟩
    · config_simp; rw [upd_other _ _ _ (by omega)]; exact hr₅ x (by omega)
    · config_simp; rw [e6₅, e1₅]; omega
    · config_simp; rw [e6₅, e1₅]
      intro j hj i hi hji
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact htri5 j hj i hi hji
      · exact hcol5 i hji hi
    · config_simp; rw [hr₅ 11 (by omega), h11₄]; exact Nat.mod_lt _ (by omega)
    · config_simp; rw [e6₅, e1₅]
      refine ⟨s3 * sc, by rcases hs3 with rfl | rfl <;> rcases hsc with rfl | rfl <;> simp, ?_, ?_⟩
      · rw [hdet5, hdet3, hdetc]; ring
      · rw [hr₅ 11 (by omega), h11₄, DetMod.cast_mulmod, hacc3, hacc, DetMod.diag_succ,
          DetMod.diag_congr (m := c₃.nmem) fun i hi => hkeep i (by omega) i (by omega) (by omega),
          hkeep k hk k hk le_rfl, hdiag]
        ring
    · config_simp; rw [ho5, ho₄, hA.out]; exact hI.out
    · have : (dim d - k) * colCost d = (dim d - (k + 1)) * colCost d + colCost d := by
        rw [← Nat.add_one_mul]; congr 1; omega
      config_simp; rw [e6₅, e1₅, this]
      unfold colCost
      have : 11 * dim d * dim d = dim d * (11 * dim d) := by ring
      nlinarith
  by_cases hz : c₃.nmem (k * dim d + k) = 0
  · -- no pivot: nothing to eliminate
    obtain ⟨c', k', eF, hI', hp⟩ := hfin c₄ 2 hw₄ (fun _ _ => rfl)
      (fun i hi j hj _ => by rw [hm₄]) (fun a ha => by rw [hm₄]; exact hA.lt a ha) (by rw [hm₄])
      (fun i hi1 hi2 => by rw [hm₄]; exact hA.zero hz i hi1.le hi2)
      (fun j hj i hi hji => by rw [hm₄]; exact hA.tri j hj i hi hji) rfl (by omega)
    exact ⟨c', _, .seq e₃ (.seq eD (.seq (.ifLtN_false (by rw [h9₄, hR₄.1]; omega) (.skip hw₄)) eF)),
      hI', hp⟩
  · -- eliminate below the pivot
    have hpiv : (c₃.nmem (k * dim d + k) : ZMod (prm d)) ≠ 0 := fun h =>
      hz (zero_of_cast hpivlt h)
    obtain ⟨c₅, k₅, e₅, hw₅, hE, hk₅⟩ := elim_exec he c₄ hw₄ hR₄ hk
      (by rw [hr₄ 6 (by omega) (by omega) (by omega), e6₃])
      (by rw [hr₄ 24 (by omega) (by omega) (by omega)]; exact hA.r24)
      (by rw [h9₄, hm₄]) (by rw [hm₄]; exact hpiv) (fun a ha => by rw [hm₄]; exact hA.lt a ha)
      (fun j hj i hi hji => by rw [hm₄]; exact hA.tri j hj i hi hji)
    obtain ⟨c', k', eF, hI', hp⟩ := hfin c₅ (k₅ + 1) hw₅
      (fun x hx => hE.regs x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
      (fun i hi j hj hik => by rw [hE.keep i hi j hj hik, hm₄]) hE.lt (by rw [hE.det, hm₄])
      hE.col (fun j hj i hi hji => hE.tri j hj i hi hji) hE.out (by omega)
    exact ⟨c', _, .seq e₃ (.seq eD (.seq (.ifLtN_true (by rw [h9₄, hR₄.1]; omega) e₅) eF)),
      hI', hp⟩

end column

/-! ### The whole program -/

/-- The state of the copy loop. -/
structure ICp (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  r6 : c.nreg 6 = 0
  r11 : c.nreg 11 = 1
  r7 : c.nreg 7 ≤ dim d * dim d
  mem : ∀ t < c.nreg 7, c.nmem t = ent d t % prm d
  out : c.output = []

section main
variable {d : List ℕ} {W : ℕ}

theorem copyStep_exec (he : DEnc d W) (c : Config) (hI : ICp d W c)
    (hlt : c.nreg 7 < dim d * dim d) :
    ∃ c' k', Exec (inp d) W copyStep c c' k' ∧ ICp d W c' ∧
      (dim d * dim d - c'.nreg 7) * 7 + k' + 2 ≤ (dim d * dim d - c.nreg 7) * 7 := by
  have hc := hI.wb
  have hW := he.dim_sq
  obtain ⟨h0, h1, h2, h3, h4, h5, h12, h13⟩ := hI.regs
  have hent : (inp d).data.getD (c.nreg 7 + c.nreg 5) 0 = ent d (c.nreg 7) := by
    simp only [inp, ent, h5]
  unfold copyStep
  exec_block
  · rw [h5]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [h1]; omega
  simp only [hent] at *
  refine ⟨⟨‹_›, regs_of_keepsR hI.regs fun x hx => ?_, ?_, ?_, ?_, fun t ht => ?_, ?_⟩, ?_⟩
  · config_simp; rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · config_simp; exact hI.r6
  · config_simp; exact hI.r11
  · config_simp; rw [h1]; omega
  · config_simp at ht; config_simp; rw [h1] at ht
    rw [h3]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · rw [upd_other _ _ _ (by omega)]; exact hI.mem t ht
    · rw [upd_same]
  · config_simp; exact hI.out
  · config_simp; rw [h1]; omega

theorem ICp.toIK {c : Config} (hI : ICp d W c) (h7 : c.nreg 7 = dim d * dim d) (hp : 2 ≤ prm d) :
    IK d W c := by
  have hm : ∀ i < dim d, ∀ j < dim d, (c.nmem (i * dim d + j) : ZMod (prm d)) = ent d (i * dim d + j) :=
    fun i hi j hj => by
      rw [hI.mem _ (by rw [h7]; exact DetMod.idx_lt hi hj), ZMod.natCast_mod]
  refine ⟨hI.wb, hI.regs, by rw [hI.r6]; omega, fun a ha => by
    rw [hI.mem a (by omega)]; exact Nat.mod_lt _ (by omega), fun j hj => by rw [hI.r6] at hj; omega,
    by rw [hI.r11]; omega, ⟨1, Or.inl rfl, ?_, ?_⟩, hI.out⟩
  · rw [one_mul]; congr 1; ext i j; exact hm i i.2 j j.2
  · rw [hI.r11, hI.r6]; simp [diag]

/-- The step bound of the program. -/
def detCost (d : List ℕ) : ℕ := 7 * dim d * dim d + dim d * colCost d + 16

/-- **The determinant modulo `p` on the machine.** -/
theorem detMod_exec (he : DEnc d W) :
    ∃ c' k, Exec (inp d) W detMod initConfig c' k ∧ c'.output = [(inMat d).det.val] ∧
      k ≤ detCost d := by
  have hW := he.dim_sq; have hWp := he.sq
  have hp2 := he.prime.two_le
  have hw0 : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  have e₁ : ∃ c₁ k₁, Exec (inp d) W setup initConfig c₁ k₁ ∧ ICp d W c₁ ∧ k₁ = 10 := by
    unfold setup
    exec_block
    · omega
    · exact he.word_le _
    · exact he.word_le _
    · exact (Nat.le_add_right _ 2).trans hW
    · omega
    · omega
    refine ⟨⟨‹_›, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, fun t ht => ?_, ?_⟩, rfl⟩
    all_goals config_simp
    all_goals try rfl
    all_goals first | exact Nat.zero_le _ | exact absurd ht (Nat.not_lt_zero _)
  obtain ⟨c₁, k₁, e₁, hC₁, rfl⟩ := e₁
  obtain ⟨c₂, k₂, e₂, hC₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 7)
    (b := 4) (body := copyStep) (ICp d W) (fun c => (dim d * dim d - c.nreg 7) * 7)
    (fun c h => h.wb) (fun c hc hlt => copyStep_exec he c hc (by rw [hc.regs.2.2.2.2.1] at hlt; exact hlt))
    hC₁
  have h7₂ : c₂.nreg 7 = dim d * dim d := by
    have := hC₂.r7; rw [hC₂.regs.2.2.2.2.1] at hn₂; omega
  have hK₂ := hC₂.toIK h7₂ hp2
  obtain ⟨c₃, k₃, e₃, hK₃, hn₃, hk₃⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 6)
    (b := 2) (body := colStep) (IK d W) (fun c => (dim d - c.nreg 6) * colCost d)
    (fun c h => h.wb) (fun c hc hlt => colStep_exec he c hc (by rw [hc.regs.2.2.1] at hlt; exact hlt))
    hK₂
  have h6₃ : c₃.nreg 6 = dim d := by
    have := hK₃.k_le; rw [hK₃.regs.2.2.1] at hn₃; omega
  have e₄ := Exec.outN (P := inp d) hK₃.wb 11
  refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_, ?_⟩
  · rw [hK₃.out]
    obtain ⟨s, hs, hdet, hacc⟩ := hK₃.sgn
    rw [h6₃] at hacc
    have htri : (mat (dim d) (prm d) c₃.nmem).det = diag (dim d) (prm d) c₃.nmem (dim d) :=
      DetMod.det_triangular fun i hi j hji => by
        rw [hK₃.tri j (by rw [h6₃]; omega) i hi hji]; simp
    have hval : ((c₃.nreg 11 : ℕ) : ZMod (prm d)) = (inMat d).det := by
      rw [hacc, ← htri, hdet, ← mul_assoc]
      rcases hs with rfl | rfl <;> simp
    simp only [List.nil_append, List.cons.injEq, and_true]
    haveI : NeZero (prm d) := ⟨by omega⟩
    rw [← hval, ZMod.val_natCast_of_lt hK₃.acc_lt]
  · unfold detCost
    beta_reduce at hk₂ hk₃
    have a1 : (dim d * dim d - c₁.nreg 7) * 7 ≤ dim d * dim d * 7 :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have a2 : (dim d - c₂.nreg 6) * colCost d ≤ dim d * colCost d :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    have : 7 * dim d * dim d = dim d * dim d * 7 := by ring
    omega

/-- **The determinant modulo a prime on the machine.** On an input `[n, p, entries]` with `p`
prime and words of at least `p² + p` and `n² + 2` values, the compiled program halts within
`7 n² + n (11 n² + 30 n + 12 ⌊log₂ p⌋ + 62) + 17` steps and prints `det A mod p`. -/
theorem detMod_runsWithin (he : DEnc d W) :
    RunsWithin (compile detMod 0 ++ [Instr.halt]) (inp d) W (detCost d + 1)
      [(inMat d).det.val] := by
  obtain ⟨c', k, e, hout, hk⟩ := detMod_exec he
  obtain ⟨k', hk', h1, h2⟩ := runsWithin_of_exec_output e hout
  exact ⟨k', by omega, h1, h2⟩

theorem colCost_le (d : List ℕ) :
    colCost d ≤ 11 * dim d * dim d + 30 * dim d + 12 * Nat.log 2 (prm d) + 62 := by
  unfold colCost powPot
  split_ifs with h
  · omega
  · have := Nat.log_mono_right (b := 2) (Nat.sub_le (prm d) 2); omega

end main

end DetMod

end NestedDissection
