module

public import PlanarFlow.Monge.RangeMin
public import PlanarFlow.Monge.FRExec

/-!
# Range minima in an anti-Monge matrix on the machine: layout, entries, counting

The parameters of the structure (`RMP`): the height `T` of the tree (`s = 2 ^ T` leaves, the rows
`ρ < s`), the number `nr ≤ s` of true rows (the rows `≥ nr` repeat the row `nr - 1`), the number
`nc` of sources, the base `B` of the structure in the natural memory, the matrix in the real
memory (`rmF`: the entry `(ρ, σ)` is `rmem (Ab + σ * Ls + ρ) - rmem (Pb + ρ)`, the row clamped to
`nr - 1`; for a half block of FR, `Ab + σ * Ls + ρ` is the length from the source to the target
and `Pb + ρ` the price of the target), and the word bound `W`.

**Memory layout** (`cell`): the natural memory cell `B + (4 j + f) s + i` holds the entry `i` of
the array `f` of the level `j` (`j ≤ T`, `f < 4`, `i < s`); the node of height `j` at the offset
`o` owns the entries `[o, o + 2 ^ j)` of the four arrays of its level: `f = 0` the sorted
thresholds with their sentinel, `f = 1`, `f = 2` the gaps at the children, `f = 3` the rows
(`NodeOK`). The structure occupies `[B, B + 4 (T + 1) s)`.

**Registers.** The parameters are in `r300 … r307` (`RCtx`: `B`, `s`, `nc`, `Ab`, `Ls`, `Pb`,
`nr - 1`, `T`), the constants `1`, `2`, `nc + 1`, `4 s` in `r308 … r311` (set by the programs);
the programs write only the natural registers `r308 … r369` and the real registers
`r300 … r309`.

* `rmEv_exec`: an entry of the matrix, within `10` steps.
* `rmCnt_exec`: the number of entries at most a key in a sorted array (a binary search), within
  `9 lg n + 4` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace RM

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs FR Heap

/-- The parameters of the structure. -/
structure RMP where
  /-- The base of the structure (natural memory). -/
  B : ℕ
  /-- The height of the tree: `2 ^ T` leaves. -/
  T : ℕ
  /-- The number of rows. -/
  nr : ℕ
  /-- The number of sources. -/
  nc : ℕ
  /-- The base of the lengths (real memory). -/
  Ab : ℕ
  /-- The stride of the lengths: one source per stride. -/
  Ls : ℕ
  /-- The base of the prices of the rows (real memory). -/
  Pb : ℕ
  /-- The word bound. -/
  W : ℕ

/-- The number of leaves. -/
def RMP.s (p : RMP) : ℕ := 2 ^ p.T

/-- The sizes and the word bound. -/
structure RMLay (p : RMP) : Prop where
  nr_pos : 1 ≤ p.nr
  nr_le : p.nr ≤ p.s
  wB : p.B + 4 * (p.T + 2) * p.s ≤ p.W
  wA : p.Ab + p.nc * p.Ls + p.nr ≤ p.W
  wP : p.Pb + p.nr ≤ p.W
  wnc : 2 * p.nc + 2 ≤ p.W

/-- **The matrix**, read in the real memory `rm`: the length from the source `σ` to the row `ρ`
minus the price of `ρ`, the row clamped to `nr - 1`. -/
def rmF (rm : ℕ → ℝ) (p : RMP) (ρ σ : ℕ) : ℝ :=
  rm (p.Ab + σ * p.Ls + min ρ (p.nr - 1)) - rm (p.Pb + min ρ (p.nr - 1))

/-- The cell of the entry `i` of the array `f` of the level `j`. -/
def cell (p : RMP) (j f i : ℕ) : ℕ := p.B + (4 * j + f) * p.s + i

/-- The array `f` of the node of height `j` at the offset `o`. -/
def Arr (nm : ℕ → ℕ) (p : RMP) (j f o : ℕ) (e : ℕ) : ℕ := nm (cell p j f (o + e))

/-- The gap of the source `σ` at the node of height `j` at the offset `o`. -/
def gapAt (nm : ℕ → ℕ) (p : RMP) (j o σ : ℕ) : ℕ := cntP (Arr nm p j 0 o) (2 ^ j - 1) σ

/-- **A correct node**: its thresholds are sorted with the sentinel, the row of the gap of a
source minimises the matrix over the rows of the node, and the gaps at the children are those of
the source. -/
def NodeOK (F : ℕ → ℕ → ℝ) (p : RMP) (nm : ℕ → ℕ) (j o : ℕ) : Prop :=
  LOK (Arr nm p j 0 o) (2 ^ j - 1) p.nc ∧ ∀ σ < p.nc,
    IsArgmin F σ o (o + 2 ^ j) (Arr nm p j 3 o (gapAt nm p j o σ)) ∧
    ∀ j', j = j' + 1 → Arr nm p j 1 o (gapAt nm p j o σ) = gapAt nm p j' o σ ∧
      Arr nm p j 2 o (gapAt nm p j o σ) = gapAt nm p j' (o + 2 ^ j') σ

/-- The fixed registers. -/
structure RCtx (p : RMP) (c : Config) : Prop where
  r300 : c.nreg 300 = p.B
  r301 : c.nreg 301 = p.s
  r302 : c.nreg 302 = p.nc
  r303 : c.nreg 303 = p.Ab
  r304 : c.nreg 304 = p.Ls
  r305 : c.nreg 305 = p.Pb
  r306 : c.nreg 306 = p.nr - 1
  r307 : c.nreg 307 = p.T
  r308 : c.nreg 308 = 1
  r309 : c.nreg 309 = 2
  r310 : c.nreg 310 = p.nc + 1
  r311 : c.nreg 311 = 4 * p.s

theorem RCtx.of {p : RMP} {c c' : Config} (h : RCtx p c)
    (hr : ∀ r, 300 ≤ r → r < 312 → c'.nreg r = c.nreg r) : RCtx p c' :=
  ⟨(hr 300 (by omega) (by omega)).trans h.r300, (hr 301 (by omega) (by omega)).trans h.r301,
    (hr 302 (by omega) (by omega)).trans h.r302, (hr 303 (by omega) (by omega)).trans h.r303,
    (hr 304 (by omega) (by omega)).trans h.r304, (hr 305 (by omega) (by omega)).trans h.r305,
    (hr 306 (by omega) (by omega)).trans h.r306, (hr 307 (by omega) (by omega)).trans h.r307,
    (hr 308 (by omega) (by omega)).trans h.r308, (hr 309 (by omega) (by omega)).trans h.r309,
    (hr 310 (by omega) (by omega)).trans h.r310, (hr 311 (by omega) (by omega)).trans h.r311⟩

lemma RMLay.s_pos {p : RMP} (_ : RMLay p) : 1 ≤ p.s := Nat.one_le_two_pow

lemma RMLay.T_lt {p : RMP} (_ : RMLay p) : p.T < p.s := Nat.lt_two_pow_self

/-! ### The programs -/

/-- `r301 := F r316 r317`, the row `r316` clamped to `nr - 1`. -/
def rmEv : Stmt :=
  .seq (.instr (.copyN 318 316)) <|
  .seq (.ifLtN 306 318 (.instr (.copyN 318 306)) .skip) <|
  block [.mulN 319 317 304, .addN 319 319 303, .addN 319 319 318, .loadR 301 319,
    .addN 319 305 318, .loadR 302 319, .subR 301 301 302]

/-- One probe of the binary search of `rmCnt`. -/
def cntBody : Stmt :=
  .seq (block [.addN 325 323 324, .divN 325 325 309, .addN 326 320 325, .loadN 326 326]) <|
  .ifLtN 322 326 (.instr (.copyN 324 325)) (.instr (.addN 323 325 308))

/-- `r323 :=` the number of the entries `nmem (r320 + e)`, `e < r321`, at most `r322` (a sorted
array). -/
def rmCnt : Stmt := .seq (block [.constN 323 0, .copyN 324 321]) (.whileLtN 323 324 cntBody)

variable {p : RMP} {I : Input}

/-- **An entry of the matrix.** -/
theorem rmEv_exec (hL : RMLay p) (c : Config) (hc : WordsBounded p.W c) (hR : RCtx p c)
    (hσ : c.nreg 317 < p.nc) :
    ∃ c' k, Exec I p.W rmEv c c' k ∧ k ≤ 10 ∧
      (c'.rreg 301 = rmF c.rmem p (c.nreg 316) (c.nreg 317) ∧ KN 318 320 c c' ∧
        KR 301 303 c c' ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hA := hL.wA; have hP := hL.wP; have hnr := hL.nr_pos
  obtain ⟨-, -, -, g203, g204, g205, g206, -, -, -, -, -⟩ := hR
  generalize hρ' : c.nreg 316 = ρ
  generalize hσ' : c.nreg 317 = σ at hσ
  generalize ht : min ρ (p.nr - 1) = t
  unfold rmEv
  refine spec_seq ?_
  refine spec_instr (Exec.copyN hc 318 316) fun hw₁ => ?_
  refine spec_seq ?_
  have hcl : ∃ c₂ k₂, Exec I p.W (.ifLtN 306 318 (.instr (.copyN 318 306)) .skip)
      { c with nreg := upd c.nreg 318 (c.nreg 316) } c₂ k₂ ∧ k₂ = 2 ∧
      c₂ = { c with nreg := upd c.nreg 318 t } := by
    by_cases hlt : p.nr - 1 < ρ
    · refine spec_ifLtN_true (by config_simp; rw [g206, hρ']; exact hlt) ?_
      refine spec_instr (Exec.copyN hw₁ 318 306) fun _ => ⟨rfl, ?_⟩
      config_simp; rw [g206, ← ht]; congr 1; funext r; simp only [upd_apply]
      split_ifs <;> first | rfl | omega
    · refine spec_ifLtN_false (by config_simp; rw [g206, hρ']; exact hlt) ?_
      refine spec_skip hw₁ ⟨rfl, ?_⟩
      rw [hρ', ← ht]; congr 2; omega
  obtain ⟨c₂, k₂, e₂, hk₂, rfl⟩ := hcl
  refine ⟨_, k₂, e₂, ?_⟩
  have hw₂ := e₂.wb_right
  have hσL : σ * p.Ls ≤ p.nc * p.Ls := Nat.mul_le_mul_right _ hσ.le
  have htn : t < p.nr := by omega
  exec_block
  · config_simp; rw [hσ', g204]; omega
  · config_simp; rw [hσ', g204, g203]; omega
  · config_simp; rw [hσ', g204, g203]; omega
  · config_simp; rw [g205]; omega
  refine ⟨by omega, ?_, fun r hr => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · config_simp
    rw [hσ', g204, g203, g205]
    unfold rmF; rw [ht]; congr 2; ring
  · config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
  · config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega

/-! ### Counting in a sorted array -/

lemma lg_half' {a b : ℕ} (hb : 1 ≤ b) (h : a ≤ b / 2) : lg a + 1 ≤ lg b := by
  have := lg_mono h
  rw [lg_pos hb]; omega

/-- The state of the binary search of `rmCnt`. -/
structure ICnt (W n σ : ℕ) (f : ℕ → ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  keep : KN 323 327 c₀ c
  rr : c.rreg = c₀.rreg
  nm : c.nmem = c₀.nmem
  rm : c.rmem = c₀.rmem
  out : c.output = c₀.output
  lohi : c.nreg 323 ≤ c.nreg 324
  hin : c.nreg 324 ≤ n
  lo : ∀ e < c.nreg 323, f e ≤ σ
  hi : ∀ e, c.nreg 324 ≤ e → e < n → σ < f e

theorem cntBody_exec {W n σ : ℕ} {f : ℕ → ℕ} {c₀ : Config} (hR : RCtx p c₀)
    (hsort : SortedTo f n) (hf : ∀ e < n, c₀.nmem (c₀.nreg 320 + e) = f e)
    (h220 : c₀.nreg 320 + 2 * n ≤ W) (h222 : c₀.nreg 322 = σ)
    (c : Config) (hI : ICnt W n σ f c₀ c) (hlt : c.nreg 323 < c.nreg 324) :
    ∃ c' k, Exec I W cntBody c c' k ∧ ICnt W n σ f c₀ c' ∧
      9 * lg (c'.nreg 324 - c'.nreg 323) + k + 2 ≤ 9 * lg (c.nreg 324 - c.nreg 323) := by
  have hc := hI.wb
  have g : ∀ r, (r < 323 ∨ 327 ≤ r) → c.nreg r = c₀.nreg r := hI.keep
  have g208 : c.nreg 308 = 1 := (g 308 (by omega)).trans hR.r308
  have g209 : c.nreg 309 = 2 := (g 309 (by omega)).trans hR.r309
  have g220 : c.nreg 320 = c₀.nreg 320 := g 320 (by omega)
  have g222 : c.nreg 322 = σ := (g 322 (by omega)).trans h222
  have hhin := hI.hin
  generalize hp : c.nreg 323 = lo at hlt
  generalize hq : c.nreg 324 = hi at hlt hhin
  generalize hm : (lo + hi) / 2 = m
  have hm1 : lo ≤ m := by omega
  have hm2 : m < hi := by omega
  have hsz : ∀ x, x ≤ (hi - lo) / 2 → lg x + 1 ≤ lg (hi - lo) := fun x hx => lg_half' (by omega) hx
  have hfm : c.nmem (c₀.nreg 320 + m) = f m := by rw [hI.nm]; exact hf m (by omega)
  unfold cntBody
  refine spec_seq ?_
  exec_block
  · rw [hp, hq]; omega
  · config_simp; rw [g209, hp, hq, g220, hm]; omega
  have hfin : ∀ c' : Config, WordsBounded W c' → KN 323 327 c c' → c'.rreg = c.rreg →
      c'.nmem = c.nmem → c'.rmem = c.rmem → c'.output = c.output →
      c'.nreg 323 ≤ c'.nreg 324 → c'.nreg 324 ≤ n → (∀ e < c'.nreg 323, f e ≤ σ) →
      (∀ e, c'.nreg 324 ≤ e → e < n → σ < f e) → ICnt W n σ f c₀ c' :=
    fun c' hw hK hr hn hrm ho a1 a2 a3 a4 => ⟨hw, fun r hr' => (hK r hr').trans (g r hr'),
      hr.trans hI.rr, hn.trans hI.nm, hrm.trans hI.rm, ho.trans hI.out, a1, a2, a3, a4⟩
  by_cases hb : σ < f m
  · refine spec_ifLtN_true (by config_simp; rw [g222, g220, g209, hp, hq, hm, hfm]; exact hb) ?_
    refine spec_instr (Exec.copyN ‹_› 324 325) fun hw' => ?_
    refine ⟨hfin _ hw' (fun r hr => by config_simp; upd_tac) rfl rfl rfl rfl
      (by config_simp; rw [g209, hp, hq, hm]; omega) (by config_simp; rw [g209, hp, hq, hm]; omega)
      (by config_simp; exact hI.lo) (fun e h1 h2 => ?_), ?_⟩
    · config_simp at h1; rw [g209, hp, hq, hm] at h1
      exact lt_of_lt_of_le hb (hsort.le h1 h2)
    · config_simp; rw [g209, hp, hq, hm]
      have := hsz (m - lo) (by omega)
      omega
  · refine spec_ifLtN_false (by config_simp; rw [g222, g220, g209, hp, hq, hm, hfm]; exact hb) ?_
    have hadd : m + 1 ≤ W := by omega
    refine spec_instr (Exec.addN ‹_› 323 325 308 (by
      config_simp; rw [g208, g209, hp, hq, hm]; exact hadd)) fun hw' => ?_
    refine ⟨hfin _ hw' (fun r hr => by config_simp; upd_tac) rfl rfl rfl rfl
      (by config_simp; rw [g208, g209, hp, hq, hm]; omega) (by config_simp; rw [hq]; omega)
      (fun e he => ?_) (by config_simp; exact fun e h1 h2 => hI.hi e (by omega) h2), ?_⟩
    · config_simp at he; rw [g208, g209, hp, hq, hm] at he
      exact (hsort.le (show e ≤ m by omega) (lt_of_lt_of_le hm2 hhin)).trans (not_lt.1 hb)
    · config_simp; rw [g208, g209, hp, hq, hm]
      have := hsz (hi - (m + 1)) (by omega)
      omega

/-- **Counting in a sorted array** by a binary search: `r323` becomes the number of the entries
`e < n` of the array at `r320` at most the key `r322`. -/
theorem rmCnt_exec {n : ℕ} {f : ℕ → ℕ} (c : Config) (hc : WordsBounded p.W c) (hR : RCtx p c)
    (hsort : SortedTo f n) (hf : ∀ e < n, c.nmem (c.nreg 320 + e) = f e)
    (h221 : c.nreg 321 = n) (h220 : c.nreg 320 + 2 * n ≤ p.W) :
    ∃ c' k, Exec I p.W rmCnt c c' k ∧ k ≤ 9 * lg n + 4 ∧
      (c'.nreg 323 = cntP f n (c.nreg 322) ∧ KN 323 327 c c' ∧ c'.rreg = c.rreg ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold rmCnt
  refine spec_seq ?_
  exec_block
  · omega
  config_simp
  have hw₁ : WordsBounded p.W { c with nreg := upd (upd c.nreg 323 0) 324 (c.nreg 321) } :=
    ⟨upd_le (upd_le hc.1 (Nat.zero_le _)) (hc.1 321), hc.2⟩
  have hI₀ : ICnt p.W n (c.nreg 322) f c
      { c with nreg := upd (upd c.nreg 323 0) 324 (c.nreg 321) } :=
    ⟨hw₁, fun r hr => by config_simp; upd_tac, rfl, rfl, rfl, rfl,
      by config_simp; omega, by config_simp; omega, fun e he => by config_simp at he; omega,
      fun e h1 h2 => by config_simp at h1; omega⟩
  obtain ⟨c', k, e, hI, hn, hk⟩ := Exec.whileLtN_potential (P := I) (W := p.W) (a := 323)
    (b := 324) (body := cntBody) (fun c' => ICnt p.W n (c.nreg 322) f c c')
    (fun c' => 9 * lg (c'.nreg 324 - c'.nreg 323)) (fun _ h => h.wb)
    (fun c' hI' hlt => cntBody_exec hR hsort hf h220 rfl c' hI' hlt) hI₀
  refine ⟨c', k, e, ?_, ?_, hI.keep, hI.rr, hI.nm, hI.rm, hI.out⟩
  · config_simp at hk
    have : lg (n - 0) ≤ lg n := le_of_eq (by rw [Nat.sub_zero])
    rw [h221] at hk; omega
  · have h1 := hI.lohi
    exact (cntP_eq_of (by have := hI.hin; omega) hI.lo (fun e a b => hI.hi e (by omega) b)).symm

end RM

end Monge

end PlanarFlow
