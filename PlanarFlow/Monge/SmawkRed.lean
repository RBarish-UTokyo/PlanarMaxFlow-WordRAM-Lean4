module

public import PlanarFlow.Monge.Smawk
public import PlanarFlow.Monge.RowMin

/-!
# SMAWK on the machine: the reduction of one level

The program `reduce ent` runs the reduction of `PlanarFlow.Monge.RedInv` on the machine. The
input list of columns is read from the natural memory at `inB + i · inS` (`i = 0, 1, …`, ended
by the sentinel `n`), the stack is written at `outB + u · outS`; the `k`-th row of the level is
the row `(k + 1) s - 1` of the matrix, whose entries are produced by the entry oracle `ent`.

**`PlanarFlow.Monge.reduce_exec`.** From an input list of `N` columns containing the leftmost
minima of the `p` rows of the level, the run ends with a list of at most `p` columns, ended by
the sentinel `n`, containing them, within `(4E + 45) N + 12` steps (`E` bounds the cost of an
entry): every column is pushed and popped at most once.

The entry oracle may now use a scratch region larger than the output: `EntSpecK … pb K c₀`
is `PlanarFlow.Monge.EntSpec` with the frame `Agree pb K` (`EntSpec = EntSpecK` with `K = m`).

Registers: `r60 = m`, `r61 = n`, `r62 = pb`, `r63 = 1`, `r64 = 2`, `r65 = s`, `r66 = m + 1`,
`r67 = inB`, `r68 = inS`, `r69 = outB`, `r72 = outS`, `r74 = p` (fixed), `r73 = t` the height of
the stack, `r75 = i` the input position, `r76` the input column, `r77` the flag of the pop loop,
`r70, r71` the arguments of the oracle, `r78, r79` addresses; the real `r71` holds an entry.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The entry oracle with the frame `Agree pb K`. -/
def EntSpecK (P : Input) (W : ℕ) (ent : Stmt) (A : ℕ → ℕ → ℝ) (E m n pb K : ℕ) (c₀ : Config) :
    Prop :=
  ∀ c, WordsBounded W c → Agree pb K c₀ c → c.nreg 70 < m → c.nreg 71 < n →
    ∃ c' k, Exec P W ent c c' k ∧ k ≤ E ∧ c'.rreg 70 = A (c.nreg 70) (c.nreg 71) ∧
      (∀ r < 80, c'.nreg r = c.nreg r) ∧ (∀ r < 80, r ≠ 70 → c'.rreg r = c.rreg r) ∧
      c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output

theorem entSpec_iff {P : Input} {W : ℕ} {ent : Stmt} {A : ℕ → ℕ → ℝ} {E m n pb : ℕ}
    {c₀ : Config} : EntSpec P W ent A E m n pb c₀ ↔ EntSpecK P W ent A E m n pb m c₀ := Iff.rfl

/-- A loop with a potential, keeping the final potential in the bound. -/
theorem whileLtN_potential' {P : Input} {W : ℕ} {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (Φ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k + Φ c' ≤ Φ c + 2 := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hΦ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂⟩ := ih (Φ c₁) (by omega) hI₁ rfl
      exact ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega⟩
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht, by omega⟩

/-! ### The program -/

/-- One step of the pop loop: stop (`r77 := 1`) if the stack is empty or its top is not beaten
by the input column in the row of the top, pop otherwise. -/
def redPop (ent : Stmt) : Stmt :=
  .ifLtN 73 63 (.instr (.constN 77 1)) <|
  .seq (block [.mulN 70 73 65, .subN 70 70 63, .subN 79 73 63, .mulN 79 79 72, .addN 79 79 69,
      .loadN 71 79]) <|
  .seq ent <| .seq (block [.copyR 71 70, .copyN 71 76]) <| .seq ent <|
  .ifLtR 70 71 (.instr (.subN 73 73 63)) (.instr (.constN 77 1))

/-- One input column: the pops, the push if the stack is not full, the next input column. -/
def redCol (ent : Stmt) : Stmt :=
  .seq (.instr (.constN 77 0)) <| .seq (.whileLtN 77 63 (redPop ent)) <|
  .ifLtN 73 74 (block [.mulN 79 73 72, .addN 79 79 69, .storeN 79 76, .addN 73 73 63,
      .addN 75 75 63, .mulN 78 75 68, .addN 78 78 67, .loadN 76 78])
    (block [.addN 75 75 63, .mulN 78 75 68, .addN 78 78 67, .loadN 76 78])

/-- **The reduction of one level.** -/
def reduce (ent : Stmt) : Stmt :=
  .seq (block [.constN 73 0, .constN 75 0, .copyN 78 67, .loadN 76 78]) <|
  .seq (.whileLtN 76 61 (redCol ent)) <|
  block [.mulN 79 73 72, .addN 79 79 69, .storeN 79 61]

/-! ### The state -/

/-- The data of a reduction: the input list, the geometry of the lists and the fixed
registers of the starting configuration `c₁`. -/
structure RedData (W : ℕ) (n pb K s p inB inS outB outS N : ℕ) (In : ℕ → ℕ) (c₁ : Config) :
    Prop where
  r61 : c₁.nreg 61 = n
  r63 : c₁.nreg 63 = 1
  r65 : c₁.nreg 65 = s
  r67 : c₁.nreg 67 = inB
  r68 : c₁.nreg 68 = inS
  r69 : c₁.nreg 69 = outB
  r72 : c₁.nreg 72 = outS
  r74 : c₁.nreg 74 = p
  input : ∀ k ≤ N, c₁.nmem (inB + k * inS) = In k
  cols : IsCols n In N
  disj : ∀ u ≤ p, ∀ k ≤ N, outB + u * outS ≠ inB + k * inS
  region : ∀ u ≤ p, pb < outB + u * outS ∧ outB + u * outS ≤ pb + K
  wout : outB + p * outS ≤ W
  win : inB + N * inS ≤ W
  wps : p * s ≤ W
  spos : 0 < outS
  inpos : 0 < inS

lemma RedData.w1 {W n pb K s p inB inS outB outS N : ℕ} {In : ℕ → ℕ} {c₁ : Config}
    (hD : RedData W n pb K s p inB inS outB outS N In c₁) : 1 ≤ W := by
  have := hD.wout; have := (hD.region 0 (Nat.zero_le _)).1; omega

/-- The state of a reduction. -/
structure IRd (W : ℕ) (A : ℕ → ℕ → ℝ) (n pb K s p outB outS : ℕ) (In : ℕ → ℕ) (c₀ c₁ c : Config) :
    Prop where
  wb : WordsBounded W c
  agree : Agree pb K c₀ c
  nreg : ∀ r < 80, r ≠ 70 → r ≠ 71 → r ≠ 73 → r ≠ 75 → r ≠ 76 → r ≠ 77 → r ≠ 78 → r ≠ 79 →
    c.nreg r = c₁.nreg r
  rreg : ∀ r < 80, r ≠ 70 → r ≠ 71 → c.rreg r = c₁.rreg r
  nmem : ∀ a, (∀ u ≤ p, a ≠ outB + u * outS) → c.nmem a = c₁.nmem a
  rmem : c.rmem = c₁.rmem
  out : c.output = c₁.output
  j : c.nreg 76 = In (c.nreg 75)
  inv : RedInv n A s p In (fun u => c.nmem (outB + u * outS)) (c.nreg 75) (c.nreg 73)

variable {P : Input} {W : ℕ} {ent : Stmt} {A : ℕ → ℕ → ℝ} {E m n pb K : ℕ} {c₀ : Config}
variable {s p inB inS outB outS N : ℕ} {In : ℕ → ℕ} {c₁ c : Config}

/-- The frame of a step changing only some registers and no memory. -/
theorem IRd.of_regs (h : IRd W A n pb K s p outB outS In c₀ c₁ c) {c' : Config}
    (hw : WordsBounded W c')
    (hn : ∀ r < 80, r ≠ 70 → r ≠ 71 → r ≠ 73 → r ≠ 75 → r ≠ 76 → r ≠ 77 → r ≠ 78 → r ≠ 79 →
      c'.nreg r = c.nreg r)
    (hr : ∀ r < 80, r ≠ 70 → r ≠ 71 → c'.rreg r = c.rreg r) (hnm : c'.nmem = c.nmem)
    (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) (h73 : c'.nreg 73 = c.nreg 73)
    (h75 : c'.nreg 75 = c.nreg 75) (h76 : c'.nreg 76 = c.nreg 76) :
    IRd W A n pb K s p outB outS In c₀ c₁ c' := by
  refine ⟨hw, h.agree.of_eq (fun r hr => hn r (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega))
    (fun r hr' => hr r (by omega) (by omega) (by omega)) hnm hrm ho,
    fun r hr' a b d e f g i j => (hn r hr' a b d e f g i j).trans (h.nreg r hr' a b d e f g i j),
    fun r hr' a b => (hr r hr' a b).trans (h.rreg r hr' a b), fun a ha => by rw [hnm]; exact h.nmem a ha,
    by rw [hrm]; exact h.rmem, by rw [ho]; exact h.out, by rw [h76, h75]; exact h.j, ?_⟩
  rw [h73, h75, hnm]; exact h.inv

lemma IRd.input (h : IRd W A n pb K s p outB outS In c₀ c₁ c)
    (hD : RedData W n pb K s p inB inS outB outS N In c₁) {k : ℕ} (hk : k ≤ N) :
    c.nmem (inB + k * inS) = In k := by
  rw [h.nmem _ (fun u hu => (hD.disj u hu k hk).symm)]; exact hD.input k hk

lemma IRd.reg (h : IRd W A n pb K s p outB outS In c₀ c₁ c) {r : ℕ} (hr : r < 70) :
    c.nreg r = c₁.nreg r :=
  h.nreg r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)

/-! ### The pop loop -/

/-- The stop condition of the pop loop. -/
def PopStop (A : ℕ → ℕ → ℝ) (s : ℕ) (In : ℕ → ℕ) (c : Config) (outB outS : ℕ) : Prop :=
  c.nreg 73 = 0 ∨ A (rowL s (c.nreg 73 - 1)) (c.nmem (outB + (c.nreg 73 - 1) * outS)) ≤
    A (rowL s (c.nreg 73 - 1)) (In (c.nreg 75))

/-- The state of the pop loop. -/
def IPop (W : ℕ) (A : ℕ → ℕ → ℝ) (n pb K s p outB outS N : ℕ) (In : ℕ → ℕ) (i₀ : ℕ)
    (c₀ c₁ c : Config) : Prop :=
  IRd W A n pb K s p outB outS In c₀ c₁ c ∧ c.nreg 75 = i₀ ∧ i₀ < N ∧
    (c.nreg 77 = 0 ∨ (c.nreg 77 = 1 ∧ PopStop A s In c outB outS))

theorem redPop_exec (hent : EntSpecK P W ent A E m n pb K c₀) (hA : IsTotMono m n A)
    (hs : 0 < s) (hps : p * s ≤ m) (hD : RedData W n pb K s p inB inS outB outS N In c₁)
    {i₀ : ℕ} (c : Config) (hI : IPop W A n pb K s p outB outS N In i₀ c₀ c₁ c)
    (hlt : c.nreg 77 < c.nreg 63) :
    ∃ c' k, Exec P W (redPop ent) c c' k ∧ IPop W A n pb K s p outB outS N In i₀ c₀ c₁ c' ∧
      (2 * E + 15) * (c'.nreg 73 + 1 - c'.nreg 77) + k + 2 ≤
        (2 * E + 15) * (c.nreg 73 + 1 - c.nreg 77) := by
  obtain ⟨hR, h75, hiN, hfl⟩ := hI
  subst h75
  have hc := hR.wb
  have g63 : c.nreg 63 = 1 := (hR.reg (by omega)).trans hD.r63
  have g65 : c.nreg 65 = s := (hR.reg (by omega)).trans hD.r65
  have g69 : c.nreg 69 = outB := (hR.reg (by omega)).trans hD.r69
  have g72 : c.nreg 72 = outS := (hR.nreg 72 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)).trans hD.r72
  rw [g63] at hlt
  have h77 : c.nreg 77 = 0 := by omega
  have htp := hR.inv.tle
  have hjn : In (c.nreg 75) < n := hD.cols.lt hiN
  unfold redPop
  by_cases ht0 : c.nreg 73 < 1
  · -- the stack is empty: stop
    refine spec_ifLtN_true (by rw [g63]; exact ht0) ?_
    refine spec_instr (Exec.constN hc 77 1 hD.w1) fun hw => ?_
    refine ⟨⟨hR.of_regs hw (fun r _ _ _ _ _ _ h _ _ => by config_simp; rw [upd_other _ _ _ h])
      (fun _ _ _ _ => rfl) rfl rfl rfl (by config_simp) (by config_simp) (by config_simp),
      by config_simp, hiN, Or.inr ⟨by config_simp, Or.inl (by config_simp; omega)⟩⟩, ?_⟩
    config_simp; rw [h77]
    have : c.nreg 73 = 0 := by omega
    rw [this]; omega
  -- the top of the stack and the input column, in the row of the top
  refine spec_ifLtN_false (by rw [g63]; exact ht0) ?_
  generalize ht : c.nreg 73 = t at ht0 htp
  have ht1 : 1 ≤ t := by omega
  have hrow : rowL s (t - 1) < m := rowL_lt hs hps (by omega)
  have hrowe : t * s - 1 = rowL s (t - 1) := by unfold rowL; rw [Nat.sub_add_cancel ht1]
  have hts : t * s ≤ W := le_trans (Nat.mul_le_mul_right s htp) hD.wps
  have hreg1 := hD.region (t - 1) (by omega)
  refine spec_seq ?_
  exec_block
  · config_simp; rw [ht, g65]; exact hts
  · config_simp; rw [ht, g63, g72]
    have := Nat.mul_le_mul_right outS (show t - 1 ≤ p by omega); have := hD.wout; omega
  · config_simp; rw [ht, g63, g72, g69]; have := hD.wout
    have := Nat.mul_le_mul_right outS (show t - 1 ≤ p by omega); omega
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded W c₂ := hc₂ ▸ ‹_›
  have e₂ : ∀ r < 80, r ≠ 70 → r ≠ 71 → r ≠ 79 → c₂.nreg r = c.nreg r := fun r _ a b d => by
    rw [← hc₂]; config_simp; rw [upd_other _ _ _ b, upd_other _ _ _ d, upd_other _ _ _ a]
  have g70₂ : c₂.nreg 70 = rowL s (t - 1) := by rw [← hc₂]; config_simp; rw [ht, g65, g63, hrowe]
  have g71₂ : c₂.nreg 71 = c.nmem (outB + (t - 1) * outS) := by
    rw [← hc₂]; config_simp; rw [ht, g63, g72, g69, Nat.add_comm]
  have R₂ : IRd W A n pb K s p outB outS In c₀ c₁ c₂ :=
    hR.of_regs hw₂ (fun r hr a b _ _ _ _ _ i => e₂ r hr a b i) (fun _ _ _ _ => by rw [← hc₂])
      (by rw [← hc₂]) (by rw [← hc₂]) (by rw [← hc₂]) (e₂ 73 (by omega) (by omega) (by omega)
      (by omega)) (e₂ 75 (by omega) (by omega) (by omega) (by omega))
      (e₂ 76 (by omega) (by omega) (by omega) (by omega))
  -- the top is a column `< n`
  have htop : c.nmem (outB + (t - 1) * outS) < In (c.nreg 75) := by
    obtain ⟨i', hi', e⟩ := hR.inv.sub (t - 1) (by omega)
    beta_reduce at e
    rw [e]; exact hD.cols.1 i' _ hi' hiN.le
  refine spec_seq ?_
  refine spec_use (hent c₂ hw₂ R₂.agree (by rw [g70₂]; exact hrow)
    (by rw [g71₂]; omega)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hv₃, hn₃, hr₃, hnm₃, hrm₃, ho₃⟩
  rw [g70₂, g71₂] at hv₃
  refine spec_seq ?_
  exec_block
  generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
  have hw₄ : WordsBounded W c₄ := hc₄ ▸ ‹_›
  have e₄ : ∀ r < 80, r ≠ 71 → c₄.nreg r = c₂.nreg r := fun r hr a => by
    rw [← hc₄]; config_simp; rw [upd_other _ _ _ a, hn₃ r hr]
  have g71₄ : c₄.nreg 71 = In (c.nreg 75) := by
    rw [← hc₄]; config_simp; rw [hn₃ 76 (by omega), e₂ 76 (by omega) (by omega) (by omega)
      (by omega), hR.j]
  have v₄ : c₄.rreg 71 = A (rowL s (t - 1)) (c.nmem (outB + (t - 1) * outS)) := by
    rw [← hc₄]; config_simp; exact hv₃
  have R₄ : IRd W A n pb K s p outB outS In c₀ c₁ c₄ :=
    R₂.of_regs hw₄ (fun r hr a b _ _ _ _ _ _ => by rw [e₄ r hr b])
      (fun r hr a b => by rw [← hc₄]; config_simp; rw [upd_other _ _ _ b, hr₃ r hr a])
      (by rw [← hc₄]; exact hnm₃) (by rw [← hc₄]; exact hrm₃) (by rw [← hc₄]; exact ho₃)
      (e₄ 73 (by omega) (by omega)) (e₄ 75 (by omega) (by omega)) (e₄ 76 (by omega) (by omega))
  refine spec_seq ?_
  refine spec_use (hent c₄ hw₄ R₄.agree (by rw [e₄ 70 (by omega) (by omega), g70₂]; exact hrow)
    (by rw [g71₄]; exact hjn)) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨hv₅, hn₅, hr₅, hnm₅, hrm₅, ho₅⟩
  rw [e₄ 70 (by omega) (by omega), g70₂, g71₄] at hv₅
  have v₅ : c₅.rreg 71 = A (rowL s (t - 1)) (c.nmem (outB + (t - 1) * outS)) := by
    rw [hr₅ 71 (by omega) (by omega)]; exact v₄
  have R₅ : IRd W A n pb K s p outB outS In c₀ c₁ c₅ :=
    R₄.of_regs hw₅ (fun r hr _ _ _ _ _ _ _ _ => hn₅ r hr) (fun r hr a _ => hr₅ r hr a)
      hnm₅ hrm₅ ho₅ (hn₅ 73 (by omega)) (hn₅ 75 (by omega)) (hn₅ 76 (by omega))
  have g73₅ : c₅.nreg 73 = t := by
    rw [hn₅ 73 (by omega), e₄ 73 (by omega) (by omega), e₂ 73 (by omega) (by omega) (by omega)
      (by omega), ht]
  have g75₅ : c₅.nreg 75 = c.nreg 75 := by
    rw [hn₅ 75 (by omega), e₄ 75 (by omega) (by omega), e₂ 75 (by omega) (by omega) (by omega)
      (by omega)]
  have g77₅ : c₅.nreg 77 = 0 := by
    rw [hn₅ 77 (by omega), e₄ 77 (by omega) (by omega), e₂ 77 (by omega) (by omega) (by omega)
      (by omega), h77]
  have g63₅ : c₅.nreg 63 = 1 := (R₅.reg (by omega)).trans hD.r63
  have hm₅ : c₅.nmem = c.nmem := by
    rw [hnm₅, ← hc₄]; config_simp; rw [hnm₃, ← hc₂]
  by_cases hcmp : A (rowL s (t - 1)) (In (c.nreg 75)) <
      A (rowL s (t - 1)) (c.nmem (outB + (t - 1) * outS))
  · -- pop
    refine spec_ifLtR_true (by rw [hv₅, v₅]; exact hcmp) ?_
    refine spec_instr (Exec.subN hw₅ 73 73 63) fun hw₆ => ?_
    have hpop := hR.inv.pop hA hs hps hD.cols hiN (by omega) (by rw [ht]; beta_reduce; exact hcmp)
    refine ⟨⟨?_, by config_simp; exact g75₅, hiN, Or.inl (by config_simp; exact g77₅)⟩, ?_⟩
    · refine ⟨hw₆, R₅.agree.of_eq (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)])
        (fun _ _ => rfl) rfl rfl rfl, fun r hr a b d e f g i j => ?_, R₅.rreg, R₅.nmem, R₅.rmem,
        R₅.out, by config_simp; exact R₅.j, ?_⟩
      · config_simp; rw [upd_other _ _ _ d]; exact R₅.nreg r hr a b d e f g i j
      · config_simp; rw [g73₅, g63₅, g75₅, hm₅, ← ht]; exact hpop
    · config_simp
      rw [g73₅, g63₅, g77₅, h77, show t - 1 + 1 - 0 = t by omega, show t + 1 - 0 = t + 1 by omega, Nat.mul_add,
        Nat.mul_one]
      omega
  · -- stop
    refine spec_ifLtR_false (by rw [hv₅, v₅]; exact hcmp) ?_
    refine spec_instr (Exec.constN hw₅ 77 1 hD.w1) fun hw₆ => ?_
    refine ⟨⟨R₅.of_regs hw₆ (fun r _ _ _ _ _ _ h _ _ => by config_simp; rw [upd_other _ _ _ h])
      (fun _ _ _ _ => rfl) rfl rfl rfl (by config_simp) (by config_simp) (by config_simp),
      by config_simp; exact g75₅, hiN, Or.inr ⟨by config_simp, Or.inr ?_⟩⟩, ?_⟩
    · config_simp; rw [g73₅, g75₅, hm₅, ← ht]; rw [not_lt] at hcmp; rw [ht]; exact hcmp
    · config_simp
      rw [g73₅, h77, show t + 1 - 1 = t by omega, show t + 1 - 0 = t + 1 by omega, Nat.mul_add,
        Nat.mul_one]
      omega

/-! ### One input column -/

/-- The state of the loop over the input columns. -/
def ICol (W : ℕ) (A : ℕ → ℕ → ℝ) (n pb K s p outB outS N : ℕ) (In : ℕ → ℕ) (c₀ c₁ c : Config) :
    Prop :=
  IRd W A n pb K s p outB outS In c₀ c₁ c ∧ c.nreg 75 ≤ N

/-- Writing the stack cell at position `u ≤ p`. -/
lemma Agree.store_stack {pb K : ℕ} {c₀ c : Config} (h : Agree pb K c₀ c) {a : ℕ}
    (ha : pb < a ∧ a ≤ pb + K) (v : ℕ) :
    Agree pb K c₀ { c with nmem := upd c.nmem a v } := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, fun b hb => by config_simp; rw [upd_other _ _ _ (by omega)]; exact h3 b hb, h4, h5⟩

theorem redCol_exec (hent : EntSpecK P W ent A E m n pb K c₀) (hA : IsTotMono m n A)
    (hs : 0 < s) (hps : p * s ≤ m) (hp : 0 < p) (hD : RedData W n pb K s p inB inS outB outS N In c₁)
    (c : Config) (hI : ICol W A n pb K s p outB outS N In c₀ c₁ c) (hlt : c.nreg 76 < c.nreg 61) :
    ∃ c' k, Exec P W (redCol ent) c c' k ∧ ICol W A n pb K s p outB outS N In c₀ c₁ c' ∧
      (2 * E + 15) * c'.nreg 73 + (4 * E + 45) * (N - c'.nreg 75) + k + 2 ≤
        (2 * E + 15) * c.nreg 73 + (4 * E + 45) * (N - c.nreg 75) := by
  obtain ⟨hR, hiN⟩ := hI
  have hc := hR.wb
  have g61 : c.nreg 61 = n := (hR.reg (by omega)).trans hD.r61
  rw [g61, hR.j] at hlt
  have hiN' : c.nreg 75 < N := by
    rcases Nat.eq_or_lt_of_le hiN with e | h
    · rw [e, hD.cols.2] at hlt; omega
    · exact h
  unfold redCol
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 77 0 (Nat.zero_le _)) fun hw₁ => ?_
  have R₁ : IRd W A n pb K s p outB outS In c₀ c₁ { c with nreg := upd c.nreg 77 0 } :=
    hR.of_regs hw₁ (fun r _ _ _ _ _ _ h _ _ => by config_simp; rw [upd_other _ _ _ h])
      (fun _ _ _ _ => rfl) rfl rfl rfl (by config_simp) (by config_simp) (by config_simp)
  refine spec_seq ?_
  obtain ⟨c₂, k₂, e₂, ⟨R₂, g75₂, -, hfl₂⟩, hn₂, hk₂⟩ := whileLtN_potential' (P := P) (W := W)
    (a := 77) (b := 63) (body := redPop ent) (IPop W A n pb K s p outB outS N In (c.nreg 75) c₀ c₁)
    (fun c => (2 * E + 15) * (c.nreg 73 + 1 - c.nreg 77)) (fun c h => h.1.wb)
    (fun c' hc' hlt' => redPop_exec hent hA hs hps hD c' hc' hlt')
    (c := { c with nreg := upd c.nreg 77 0 })
    ⟨R₁, by config_simp, hiN', Or.inl (by config_simp)⟩
  refine ⟨c₂, k₂, e₂, ?_⟩
  have hw₂ := R₂.wb
  have g63₂ : c₂.nreg 63 = 1 := (R₂.reg (by omega)).trans hD.r63
  have h77 : c₂.nreg 77 = 1 := by
    rw [g63₂] at hn₂
    rcases hfl₂ with h | ⟨h, -⟩ <;> omega
  have hstop : PopStop A s In c₂ outB outS := by
    rcases hfl₂ with h | ⟨-, h⟩
    · omega
    · exact h
  rw [h77] at hk₂
  config_simp at hk₂
  generalize hi : c.nreg 75 = i at hiN' g75₂
  generalize ht₀ : c.nreg 73 = t₀ at hk₂
  generalize ht₂ : c₂.nreg 73 = t₂ at hk₂ hstop
  have htp : t₂ ≤ p := ht₂ ▸ R₂.inv.tle
  have hj₂ : c₂.nreg 76 = In i := by rw [R₂.j, g75₂]
  have g74 : c₂.nreg 74 = p := (R₂.nreg 74 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)).trans hD.r74
  have g72 : c₂.nreg 72 = outS := (R₂.nreg 72 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)).trans hD.r72
  have g69 : c₂.nreg 69 = outB := (R₂.reg (by omega)).trans hD.r69
  have g67 : c₂.nreg 67 = inB := (R₂.reg (by omega)).trans hD.r67
  have g68 : c₂.nreg 68 = inS := (R₂.reg (by omega)).trans hD.r68
  have hwin := hD.win
  have hwout := hD.wout
  have hinS : (i + 1) * inS ≤ N * inS := Nat.mul_le_mul_right _ (by omega)
  have hNW : N ≤ N * inS := Nat.le_mul_of_pos_right _ hD.inpos
  have hpN : p ≤ W := by
    have : p ≤ p * outS := Nat.le_mul_of_pos_right _ hD.spos
    omega
  have hstop' : t₂ = 0 ∨ A (rowL s (t₂ - 1)) (c₂.nmem (outB + (t₂ - 1) * outS)) ≤
      A (rowL s (t₂ - 1)) (In i) := by
    unfold PopStop at hstop; rw [ht₂, g75₂] at hstop; exact hstop
  have hinv := R₂.inv
  rw [ht₂, g75₂] at hinv
  by_cases hpush : t₂ < p
  · refine spec_ifLtN_true (by rw [g74, ht₂]; exact hpush) ?_
    have hst : t₂ * outS ≤ p * outS := Nat.mul_le_mul_right _ hpush.le
    have hreg := hD.region t₂ hpush.le
    exec_block
    · config_simp; rw [ht₂, g72]; omega
    · config_simp; rw [ht₂, g72, g69]; omega
    · config_simp; rw [ht₂, g63₂]; omega
    · config_simp; rw [g75₂, g63₂]; omega
    · config_simp; rw [g75₂, g63₂, g68]; omega
    · config_simp; rw [g75₂, g63₂, g68, g67]; omega
    generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
    have hw₃ : WordsBounded W c₃ := hc₃ ▸ ‹_›
    have hm₃ : c₃.nmem = upd c₂.nmem (outB + t₂ * outS) (In i) := by
      rw [← hc₃]; config_simp; rw [ht₂, g72, g69, hj₂, Nat.add_comm]
    have e₃ : ∀ r, r ≠ 73 → r ≠ 75 → r ≠ 76 → r ≠ 78 → r ≠ 79 → c₃.nreg r = c₂.nreg r :=
      fun r a b d e f => by
        rw [← hc₃]; config_simp
        rw [upd_other _ _ _ d, upd_other _ _ _ e, upd_other _ _ _ b, upd_other _ _ _ a,
          upd_other _ _ _ f]
    have g73₃ : c₃.nreg 73 = t₂ + 1 := by rw [← hc₃]; config_simp; rw [ht₂, g63₂]
    have g75₃ : c₃.nreg 75 = i + 1 := by rw [← hc₃]; config_simp; rw [g75₂, g63₂]
    have g76₃ : c₃.nreg 76 = In (i + 1) := by
      rw [← hc₃]; config_simp
      rw [g75₂, g63₂, g68, g67, ht₂, g72, g69, upd_other _ _ _ (by
        have := hD.disj t₂ hpush.le (i + 1) (by omega); omega), Nat.add_comm]
      exact R₂.input hD (by omega)
    have hdiff : ∀ u, u ≠ t₂ → outB + u * outS ≠ outB + t₂ * outS := fun u hu h =>
      hu (Nat.eq_of_mul_eq_mul_right hD.spos (by omega))
    refine ⟨⟨⟨hw₃, ?_, fun r hr a b d e f g h' j => ?_, fun r hr a b => ?_, fun a ha => ?_, ?_, ?_,
      ?_, ?_⟩, by rw [g75₃]; omega⟩, ?_⟩
    · refine (R₂.agree.store_stack hreg (In i)).of_eq (fun r hr => ?_) (fun r _ => ?_) hm₃ ?_ ?_
      · rw [e₃ r (by omega) (by omega) (by omega) (by omega) (by omega)]
      · rw [← hc₃]
      · rw [← hc₃]
      · rw [← hc₃]
    · rw [e₃ r d e f h' j]; exact R₂.nreg r hr a b d e f g h' j
    · rw [← hc₃]; exact R₂.rreg r hr a b
    · rw [hm₃, upd_other _ _ _ (ha t₂ hpush.le)]; exact R₂.nmem a ha
    · rw [← hc₃]; exact R₂.rmem
    · rw [← hc₃]; exact R₂.out
    · rw [g76₃, g75₃]
    · rw [g73₃, g75₃]
      refine hinv.push hA hs hps hD.cols hiN' hpush hstop' (fun u hu => ?_) ?_
      · beta_reduce; rw [hm₃, upd_other _ _ _ (hdiff u (by omega))]
      · beta_reduce; rw [hm₃, upd_same]
    · rw [g73₃, g75₃, show N - i = N - (i + 1) + 1 by omega, Nat.mul_add, Nat.mul_one,
        Nat.mul_add, Nat.mul_one]
      rw [show t₂ + 1 - 1 = t₂ by omega, show t₀ + 1 - 0 = t₀ + 1 by omega, Nat.mul_add,
        Nat.mul_one] at hk₂
      omega
  · refine spec_ifLtN_false (by rw [g74, ht₂]; exact hpush) ?_
    have htp' : t₂ = p := by omega
    exec_block
    · config_simp; rw [g75₂, g63₂]; omega
    · config_simp; rw [g75₂, g63₂, g68]; omega
    · config_simp; rw [g75₂, g63₂, g68, g67]; omega
    generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
    have hw₃ : WordsBounded W c₃ := hc₃ ▸ ‹_›
    have e₃ : ∀ r, r ≠ 75 → r ≠ 76 → r ≠ 78 → c₃.nreg r = c₂.nreg r := fun r a b d => by
      rw [← hc₃]; config_simp; rw [upd_other _ _ _ b, upd_other _ _ _ d, upd_other _ _ _ a]
    have g75₃ : c₃.nreg 75 = i + 1 := by rw [← hc₃]; config_simp; rw [g75₂, g63₂]
    have g76₃ : c₃.nreg 76 = In (i + 1) := by
      rw [← hc₃]; config_simp
      rw [g75₂, g63₂, g68, g67, Nat.add_comm]
      exact R₂.input hD (by omega)
    have R₃ : IRd W A n pb K s p outB outS In c₀ c₁ c₃ := by
      refine ⟨hw₃, R₂.agree.of_eq (fun r hr => e₃ r (by omega) (by omega) (by omega))
        (fun r _ => by rw [← hc₃]) (by rw [← hc₃]) (by rw [← hc₃]) (by rw [← hc₃]),
        fun r hr a b d e f g h' j => by rw [e₃ r e f h']; exact R₂.nreg r hr a b d e f g h' j,
        fun r hr a b => by rw [← hc₃]; exact R₂.rreg r hr a b,
        fun a ha => by rw [← hc₃]; exact R₂.nmem a ha, by rw [← hc₃]; exact R₂.rmem,
        by rw [← hc₃]; exact R₂.out, by rw [g76₃, g75₃], ?_⟩
      rw [e₃ 73 (by omega) (by omega) (by omega), ht₂, g75₃,
        show c₃.nmem = c₂.nmem by rw [← hc₃]]
      refine hinv.discard hA hs hps hD.cols hiN' htp' hp ?_
      rcases hstop' with h | h
      · omega
      · exact h
    refine ⟨⟨R₃, by rw [g75₃]; omega⟩, ?_⟩
    rw [e₃ 73 (by omega) (by omega) (by omega), ht₂, g75₃, show N - i = N - (i + 1) + 1 by omega,
      Nat.mul_add, Nat.mul_one]
    rw [show t₂ + 1 - 1 = t₂ by omega, show t₀ + 1 - 0 = t₀ + 1 by omega, Nat.mul_add,
      Nat.mul_one] at hk₂
    omega

/-! ### The whole reduction -/

/-- **The reduction of one level on the machine.** From an input list of `N` columns containing
the leftmost minima of the `p` rows `ρ s k` of the level, `reduce ent` writes a list of
`t ≤ p` columns, ended by the sentinel `n`, containing them, within `(4E + 45) N + 9` steps. -/
theorem reduce_exec (hent : EntSpecK P W ent A E m n pb K c₀) (hA : IsTotMono m n A)
    (hs : 0 < s) (hps : p * s ≤ m) (hp : 0 < p) (hD : RedData W n pb K s p inB inS outB outS N In c₁)
    (hall : ∀ k < p, ∃ i' < N, In i' = lmin n A (rowL s k)) (hc : WordsBounded W c₁)
    (hA₁ : Agree pb K c₀ c₁) :
    ∃ c' k, Exec P W (reduce ent) c₁ c' k ∧ k ≤ (4 * E + 45) * N + 9 ∧
      (Agree pb K c₀ c' ∧
        (∀ r < 80, r ≠ 70 → r ≠ 71 → r ≠ 73 → r ≠ 75 → r ≠ 76 → r ≠ 77 → r ≠ 78 → r ≠ 79 →
          c'.nreg r = c₁.nreg r) ∧
        (∀ r < 80, r ≠ 70 → r ≠ 71 → c'.rreg r = c₁.rreg r) ∧
        (∀ a, (∀ u ≤ p, a ≠ outB + u * outS) → c'.nmem a = c₁.nmem a) ∧
        c'.rmem = c₁.rmem ∧ c'.output = c₁.output ∧
        ∃ t ≤ p, IsCols n (fun u => c'.nmem (outB + u * outS)) t ∧
          ∀ k < p, ∃ u < t, c'.nmem (outB + u * outS) = lmin n A (rowL s k)) := by
  have hwin := hD.win
  have hwout := hD.wout
  unfold reduce
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded W c₂ := hc₂ ▸ ‹_›
  have R₂ : ICol W A n pb K s p outB outS N In c₀ c₁ c₂ := by
    refine ⟨⟨hw₂, hA₁.of_eq (fun r hr => by rw [← hc₂]; config_simp; upd_tac)
      (fun r _ => by rw [← hc₂]) (by rw [← hc₂]) (by rw [← hc₂]) (by rw [← hc₂]),
      fun r _ _ _ a b c d e f => by rw [← hc₂]; config_simp; upd_tac,
      fun _ _ _ _ => by rw [← hc₂], fun _ _ => by rw [← hc₂], by rw [← hc₂], by rw [← hc₂], ?_,
      ?_⟩, by rw [← hc₂]; config_simp; omega⟩
    · rw [← hc₂]; config_simp; rw [hD.r67, ← hD.input 0 (Nat.zero_le _), Nat.zero_mul,
        Nat.add_zero]
    · rw [← hc₂]; config_simp; exact RedInv.init _
  refine spec_seq ?_
  refine spec_while (ICol W A n pb K s p outB outS N In c₀ c₁)
    (fun c => (2 * E + 15) * c.nreg 73 + (4 * E + 45) * (N - c.nreg 75)) (fun c h => h.1.wb)
    (fun c' hc' hlt' => redCol_exec hent hA hs hps hp hD c' hc' hlt') R₂ ?_
  intro c₃ k₃ ⟨R₃, hiN₃⟩ hn₃ hk₃
  have hw₃ := R₃.wb
  have hi₃ : c₃.nreg 75 = N := by
    rw [(R₃.reg (by omega)).trans hD.r61, R₃.j, not_lt] at hn₃
    by_contra hne
    have := hD.cols.lt (show c₃.nreg 75 < N by omega)
    omega
  have hinv := R₃.inv
  rw [hi₃] at hinv
  generalize ht : c₃.nreg 73 = t at hinv
  have htp : t ≤ p := hinv.tle
  have g72 : c₃.nreg 72 = outS := (R₃.nreg 72 (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)).trans hD.r72
  have g69 : c₃.nreg 69 = outB := (R₃.reg (by omega)).trans hD.r69
  have g61 : c₃.nreg 61 = n := (R₃.reg (by omega)).trans hD.r61
  have hst : t * outS ≤ p * outS := Nat.mul_le_mul_right _ htp
  have hreg := hD.region t htp
  exec_block
  · config_simp; rw [ht, g72]; omega
  · config_simp; rw [ht, g72, g69]; omega
  generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
  have hm₄ : c₄.nmem = upd c₃.nmem (outB + t * outS) n := by
    rw [← hc₄]; config_simp; rw [ht, g72, g69, g61, Nat.add_comm]
  have e₄ : ∀ r, r ≠ 79 → c₄.nreg r = c₃.nreg r := fun r h => by
    rw [← hc₄]; config_simp; rw [upd_other _ _ _ h]
  have hdiff : ∀ u, u ≠ t → outB + u * outS ≠ outB + t * outS := fun u hu h =>
    hu (Nat.eq_of_mul_eq_mul_right hD.spos (by omega))
  obtain ⟨hcols, hmin⟩ := hinv.final hD.cols hall (St' := fun u => c₄.nmem (outB + u * outS))
    (fun u hu => by beta_reduce; rw [hm₄, upd_other _ _ _ (hdiff u (by omega))])
    (by beta_reduce; rw [hm₄, upd_same])
  refine ⟨?_, ⟨(R₃.agree.store_stack hreg n).of_eq (fun r hr => ?_) (fun r _ => by rw [← hc₄])
    hm₄ (by rw [← hc₄]) (by rw [← hc₄]), fun r hr a b d e f g h j => ?_,
    fun r hr a b => by rw [← hc₄]; exact R₃.rreg r hr a b, fun a ha => ?_,
    by rw [← hc₄]; exact R₃.rmem, by rw [← hc₄]; exact R₃.out, t, htp, hcols, hmin⟩⟩
  · have h73 : c₂.nreg 73 = 0 := by rw [← hc₂]; config_simp
    have h75 : c₂.nreg 75 = 0 := by rw [← hc₂]; config_simp
    beta_reduce at hk₃
    rw [h73, h75, Nat.mul_zero, Nat.zero_add, Nat.sub_zero] at hk₃
    omega
  · rw [e₄ r (by omega)]
  · rw [e₄ r j]; exact R₃.nreg r hr a b d e f g h j
  · rw [hm₄, upd_other _ _ _ (ha t htp)]; exact R₃.nmem a ha

end Monge

end PlanarFlow
