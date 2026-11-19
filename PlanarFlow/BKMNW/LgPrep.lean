module

public import PlanarFlow.BKMNW.LgCore
public import PlanarFlow.BKMNW.SmXC

/-!
# The large-piece separator, stage 2: the piece map of the core in the layout of `scProg`

From the record of a call (enumeration `g` of the piece `P`, arrays `RP HP VP SP`), **`lgPrep`**
computes the arrays of the piece map of the core `B = pdarts M (core M Q P) Hs` that the
certificate program `scProg` (`LvIn`) and its rotation array (`scProg_exec_sepC`)
read, enumerated by `e j = g IX[j]` (`j < n' = #B`, increasing in `gid`):

* `cfScan` (stage 1): the flags `CF[i] = bf (g i ∈ B)`;
* `lkProg` (compaction): `CI[i]` (the rank of a flagged `i`), `IX[k]` (the `k`-th flagged index),
  `n' = r6306`;
* the ones `NF` at `b`, the hole labels `TH[j] = HP[IX[j]]` at `b + n'` (`ggProg`), the reverse
  `RV0[CI[i]] = CI[RP[i]]` at `b + 2 n'` and the rotation `SG[CI[i]] = CI[SP[i]]` at `SGb`
  (`lrProg`).

* `lgP2 … lgP7`, **`lgPrep`**; `cmp_pos`, `cmp_ci` (the compaction as an enumeration);
* **`lgPrep_exec`** (within `100 n + 60` steps): the fields `mem`, `surj`, `inj`, `rv0`, `nf`,
  `th` of `LvIn` for `(e, B, N = B)`, `e` increasing in `gid`, `n' = #B`, and the rotation array
  `SG[j] < n' ∧ e SG[j] = st (e j)` for any `st` stable on `B` given by `SP` on `B`.

Registers (inputs) `5800 = n`, `5801 = RPb`, `5802 = HPb`, `5803 = VPb`, `5804 = CFb`,
`5805 = SPb`, `5806 = 1`, `5807 = 2`, `5808 = CIb`, `5809 = IXb`, `5810 = b`, `5814 = SGb`,
`6521 = 1`; written `5811 = n'`, `5812 = b + n'`, `5813 = b + 2 n'`, and the loops' own
(`6210 … 6217`, `6300 … 6319`, `6520 … 6529`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### The compaction as an enumeration -/

/-- Every position of a compaction is a flagged index of that rank. -/
lemma cmp_pos {F : ℕ → ℕ} {n : ℕ} {IX : ℕ → ℕ} (hix : ∀ i < n, 0 < F i → IX (cnt F i) = i) :
    ∀ k < cnt F n, IX k < n ∧ 0 < F (IX k) ∧ cnt F (IX k) = k := fun k hk => by
  obtain ⟨i, hi, hfi, rfl⟩ := cnt_surj F n k hk
  rw [hix i hi hfi]; exact ⟨hi, hfi, rfl⟩

/-- The rank of a flagged index is a position of the compaction pointing back to it. -/
lemma cmp_ci {F : ℕ → ℕ} {n : ℕ} {CI IX : ℕ → ℕ}
    (hci : ∀ i < n, 0 < F i → CI i = cnt F i ∧ IX (cnt F i) = i) :
    ∀ i < n, 0 < F i → CI i < cnt F n ∧ IX (CI i) = i := fun i hi hf => by
  obtain ⟨h1, h2⟩ := hci i hi hf
  rw [h1]; exact ⟨cnt_lt_of F hi hf, h2⟩

/-! ### The programs -/

/-- The compaction of the flags. -/
def lgP2 : Stmt :=
  .seq (block [.copyN 6300 5800, .copyN 6301 5804, .copyN 6302 5808, .copyN 6303 5809]) lkProg

/-- `n'`, `b + n'`, `b + 2 n'`. -/
def lgP3 : Stmt := block [.copyN 5811 6306, .addN 5812 5810 5811, .addN 5813 5812 5811]

/-- The ones at `b`. -/
def lgP4 : Stmt := mapRunS (block [.constN 6523 1]) 5811 5810

/-- The hole labels at `b + n'`. -/
def lgP5 : Stmt := ggProg 5811 5809 5802 5812

/-- The reverse at `b + 2 n'`. -/
def lgP6 : Stmt :=
  .seq (block [.copyN 6310 5800, .copyN 6311 5804, .copyN 6312 5808, .copyN 6313 5801,
    .copyN 6314 5813]) lrProg

/-- The rotation at `SGb`. -/
def lgP7 : Stmt := .seq (block [.copyN 6313 5805, .copyN 6314 5814]) lrProg

/-- **Stage 2 of the large-piece separator**: the arrays of the piece map of the core. -/
def lgPrep : Stmt :=
  .seq cfScan (.seq lgP2 (.seq lgP3 (.seq lgP4 (.seq lgP5 (.seq lgP6 lgP7)))))

/-- The registers written by `lgPrep`. -/
def lgPw (x : ℕ) : Prop :=
  (5811 ≤ x ∧ x ≤ 5813) ∨ (6210 ≤ x ∧ x ≤ 6217) ∨ (6300 ≤ x ∧ x ≤ 6319) ∨
    (6520 ≤ x ∧ x ≤ 6529)

section Exec

variable {P : Input} {W : ℕ}

theorem lgP2_exec (c : Config) (hc : WordsBounded W c) {n CFb CIb IXb : ℕ}
    (r00 : c.nreg 5800 = n) (r04 : c.nreg 5804 = CFb) (r08 : c.nreg 5808 = CIb)
    (r09 : c.nreg 5809 = IXb) (l1 : CFb + n ≤ CIb) (l2 : CIb + n ≤ IXb) (l3 : IXb + n ≤ W)
    (w4 : n + 1 ≤ W) :
    ∃ c' t, Exec P W lgP2 c c' t ∧ t ≤ 11 * n + 10 ∧
      c'.nreg 6306 = cnt (fun j => c.nmem (CFb + j)) n ∧
      (∀ i < n, 0 < c.nmem (CFb + i) →
        c'.nmem (CIb + i) = cnt (fun j => c.nmem (CFb + j)) i ∧
        c'.nmem (IXb + cnt (fun j => c.nmem (CFb + j)) i) = i) ∧
      (∀ a, ¬ (CIb ≤ a ∧ a < IXb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6300 ∨ 6309 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, g3, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 6300 5800, .copyN 6301 5804, .copyN 6302 5808, .copyN 6303 5809])
        c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg 6300 = n ∧ c₁.nreg 6301 = CFb ∧ c₁.nreg 6302 = CIb ∧ c₁.nreg 6303 = IXb ∧
      (∀ x, (x < 6300 ∨ 6303 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r00, r04, r08, r09])
      try omega
  obtain ⟨c₂, k₂, e₂, hk₂, h6, hci, hm, hr, rr, rm, oo⟩ := lkProg_exec (P := P) c₁ e₁.wb_right
    g0 g1 g2 g3 l1 l2 l3 w4
  rw [gm₁] at h6 hci hm
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, h6, hci, hm, fun x hx => ?_, by rw [rr, gr₁],
    by rw [rm, grm₁], by rw [oo, go₁]⟩
  rw [hr x (by omega), gn₁ x (by omega)]

theorem lgP3_exec (c : Config) (hc : WordsBounded W c) {b n' : ℕ}
    (r10 : c.nreg 5810 = b) (r06 : c.nreg 6306 = n') (w : b + 2 * n' ≤ W) :
    ∃ c' t, Exec P W lgP3 c c' t ∧ t = 3 ∧ c'.nreg 5811 = n' ∧ c'.nreg 5812 = b + n' ∧
      c'.nreg 5813 = b + 2 * n' ∧
      (∀ x, (x < 5811 ∨ 5813 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lgP3
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r10, r06]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r10, r06])
    try omega

theorem lgP4_exec (c : Config) (hc : WordsBounded W c) {n' b : ℕ}
    (r11 : c.nreg 5811 = n') (r10 : c.nreg 5810 = b) (r21 : c.nreg 6521 = 1)
    (w : b + n' + 1 ≤ W) :
    ∃ c' t, Exec P W lgP4 c c' t ∧ t ≤ 6 * n' + 3 ∧ (∀ i < n', c'.nmem (b + i) = 1) ∧
      (∀ a, ¬ (b ≤ a ∧ a < b + n') → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h1 : (1 : ℕ) ≤ W := by omega
  obtain ⟨c₄, t₄, e₄, ht₄, f4, mm4, nn4, rr4, rm4, o4⟩ := mapRun_exec (P := P) c hc
    (vb := block [.constN 6523 1]) (bnd := 5811) (ob := 5810) (m := n') (Ob := b) (B := 1)
    (fun _ => 1) r11 r21 r10 (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm' => by
      obtain ⟨c'', k', e', hk'', v, nn, mm, rr, rm, oo⟩ := cst_exec (P := P) (r := 6523) (v := 1)
        c' hw h1
      exact ⟨c'', k', e', by omega, v, fun x hx => nn x (by unfold vscr at hx; omega), mm, rr,
        rm, oo⟩)
  exact ⟨c₄, t₄, e₄, by omega, f4, mm4, nn4, rr4, rm4, o4⟩

theorem lgP6_exec (c : Config) (hc : WordsBounded W c) {n CFb CIb RPb OUTb : ℕ}
    (r00 : c.nreg 5800 = n) (r04 : c.nreg 5804 = CFb) (r08 : c.nreg 5808 = CIb)
    (r01 : c.nreg 5801 = RPb) (r13 : c.nreg 5813 = OUTb)
    (l1 : CFb + n ≤ OUTb) (l2 : CIb + n ≤ OUTb) (l3 : RPb + n ≤ OUTb) (l4 : OUTb + n ≤ W)
    (w4 : n + 1 ≤ W)
    (hA : ∀ i < n, 0 < c.nmem (CFb + i) → c.nmem (RPb + i) < n)
    (hCI : ∀ i < n, 0 < c.nmem (CFb + i) → c.nmem (CIb + i) < n)
    (hinj : ∀ i < n, ∀ j < n, 0 < c.nmem (CFb + i) → 0 < c.nmem (CFb + j) →
      c.nmem (CIb + i) = c.nmem (CIb + j) → i = j) :
    ∃ c' t, Exec P W lgP6 c c' t ∧ t ≤ 14 * n + 10 ∧
      (∀ i < n, 0 < c.nmem (CFb + i) →
        c'.nmem (OUTb + c.nmem (CIb + i)) = c.nmem (CIb + c.nmem (RPb + i))) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + n) → c'.nmem a = c.nmem a) ∧
      c'.nreg 6310 = n ∧ c'.nreg 6311 = CFb ∧ c'.nreg 6312 = CIb ∧
      (∀ x, (x < 6310 ∨ 6319 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g0, g1, g2, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 6310 5800, .copyN 6311 5804, .copyN 6312 5808, .copyN 6313 5801,
        .copyN 6314 5813]) c c₁ k₁ ∧ k₁ = 5 ∧
      c₁.nreg 6310 = n ∧ c₁.nreg 6311 = CFb ∧ c₁.nreg 6312 = CIb ∧ c₁.nreg 6313 = RPb ∧
      c₁.nreg 6314 = OUTb ∧
      (∀ x, (x < 6310 ∨ 6314 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r00, r04, r08, r01, r13])
      try omega
  rw [← gm₁] at hA hCI hinj
  obtain ⟨c₂, k₂, e₂, hk₂, h1, h2, hr, rr, rm, oo⟩ := lrProg_exec (P := P) c₁ e₁.wb_right
    g0 g1 g2 g3 g4 l1 l2 l3 l4 w4 hA hCI hinj
  rw [gm₁] at h1 h2
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, h1, h2, by rw [hr _ (by omega), g0],
    by rw [hr _ (by omega), g1], by rw [hr _ (by omega), g2], fun x hx => ?_, by rw [rr, gr₁],
    by rw [rm, grm₁], by rw [oo, go₁]⟩
  rw [hr x (by omega), gn₁ x (by omega)]

theorem lgP7_exec (c : Config) (hc : WordsBounded W c) {n CFb CIb SPb OUTb : ℕ}
    (r10 : c.nreg 6310 = n) (r11 : c.nreg 6311 = CFb) (r12 : c.nreg 6312 = CIb)
    (r05 : c.nreg 5805 = SPb) (r14 : c.nreg 5814 = OUTb)
    (l1 : CFb + n ≤ OUTb) (l2 : CIb + n ≤ OUTb) (l3 : SPb + n ≤ OUTb) (l4 : OUTb + n ≤ W)
    (w4 : n + 1 ≤ W)
    (hA : ∀ i < n, 0 < c.nmem (CFb + i) → c.nmem (SPb + i) < n)
    (hCI : ∀ i < n, 0 < c.nmem (CFb + i) → c.nmem (CIb + i) < n)
    (hinj : ∀ i < n, ∀ j < n, 0 < c.nmem (CFb + i) → 0 < c.nmem (CFb + j) →
      c.nmem (CIb + i) = c.nmem (CIb + j) → i = j) :
    ∃ c' t, Exec P W lgP7 c c' t ∧ t ≤ 14 * n + 7 ∧
      (∀ i < n, 0 < c.nmem (CFb + i) →
        c'.nmem (OUTb + c.nmem (CIb + i)) = c.nmem (CIb + c.nmem (SPb + i))) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6313 ∨ 6319 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, g3, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 6313 5805, .copyN 6314 5814]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6313 = SPb ∧ c₁.nreg 6314 = OUTb ∧
      (∀ x, (x < 6313 ∨ 6314 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
    refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals
      try config_simp
      try (simp (disch := omega) only [upd_other, upd_same, r05, r14])
      try omega
  rw [← gm₁] at hA hCI hinj
  obtain ⟨c₂, k₂, e₂, hk₂, h1, h2, hr, rr, rm, oo⟩ := lrProg_exec (P := P) c₁ e₁.wb_right
    (by rw [gn₁ _ (by omega), r10]) (by rw [gn₁ _ (by omega), r11])
    (by rw [gn₁ _ (by omega), r12]) g3 g4 l1 l2 l3 l4 w4 hA hCI hinj
  rw [gm₁] at h1 h2
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, h1, h2, fun x hx => ?_, by rw [rr, gr₁],
    by rw [rm, grm₁], by rw [oo, go₁]⟩
  rw [hr x (by omega), gn₁ x (by omega)]


/-- The piece map of the core of a piece with reversal-closed darts is reversal-closed. -/
lemma rev_mem_pdarts_core {Q : Finset V} {P : Finset D} {Hs : List (Finset V)} {d : D}
    (hd : d ∈ pdarts M (core M Q P) Hs) (hr : M.rev d ∈ P) :
    M.rev d ∈ pdarts M (core M Q P) Hs := by
  rw [mem_pdarts, mem_core] at hd ⊢
  refine ⟨⟨hr, ?_, ?_⟩, ?_⟩
  · rw [CombMap.tail_rev]; exact hd.1.2.2
  · rw [CombMap.head_rev]; exact hd.1.2.1
  · rw [inner_rev]; exact hd.2

set_option maxHeartbeats 4000000 in
/-- **Stage 2 of the large-piece separator** (see the module docstring): from a record with
`QPar Q ν`, pairwise disjoint holes and the state `st` given by `SP` on the piece map of the core
`B` (stable on `B`), within `100 n + 60` steps: `n' = #B` in `5811`, the enumeration
`e j = g IX[j]` of `B` increasing in `gid`, the ones at `b`, the hole labels at `b + n'`, the
reverse at `b + 2 n'`, the rotation at `SGb`. -/
theorem lgPrep_exec {gid : D → ℕ} {ν : V → ℕ} {S T Q : Finset V} {x : MCall M} {m n R : ℕ}
    {g : ℕ → D} (hQ : QPar Q ν) (hd : x.2.1.Pairwise Disjoint) {st : Perm D}
    (hst : ∀ d ∈ pdarts M (core M Q x.1.piece) x.2.1, st d ∈ pdarts M (core M Q x.1.piece) x.2.1)
    (c : Config) (hc : WordsBounded W c) (hA : RArr M gid ν S T x m n R g c.nmem)
    (hSP : ∀ i < n, g i ∈ pdarts M (core M Q x.1.piece) x.2.1 →
      c.nmem (R + 3 + 5 * n + i) < n ∧ g (c.nmem (R + 3 + 5 * n + i)) = st (g i))
    {CFb CIb IXb SGb b : ℕ}
    (r00 : c.nreg 5800 = n) (r01 : c.nreg 5801 = R + 3 + n) (r02 : c.nreg 5802 = R + 3 + 2 * n)
    (r03 : c.nreg 5803 = R + 3 + 4 * n) (r04 : c.nreg 5804 = CFb)
    (r05 : c.nreg 5805 = R + 3 + 5 * n) (r06 : c.nreg 5806 = 1) (r07 : c.nreg 5807 = 2)
    (r08 : c.nreg 5808 = CIb) (r09 : c.nreg 5809 = IXb) (r10 : c.nreg 5810 = b)
    (r14 : c.nreg 5814 = SGb) (r21 : c.nreg 6521 = 1)
    (l0 : R + 3 + 6 * n + m ≤ CFb) (l1 : CFb + n ≤ CIb) (l2 : CIb + n ≤ IXb) (l3 : IXb + n ≤ SGb)
    (l4 : SGb + n ≤ b) (w : b + 3 * n + 1 ≤ W) :
    ∃ c' t, Exec P W lgPrep c c' t ∧ t ≤ 100 * n + 60 ∧
      c'.nreg 5811 = (pdarts M (core M Q x.1.piece) x.2.1).card ∧
      (∀ j < (pdarts M (core M Q x.1.piece) x.2.1).card, c'.nmem (IXb + j) < n ∧
        g (c'.nmem (IXb + j)) ∈ pdarts M (core M Q x.1.piece) x.2.1) ∧
      (∀ y ∈ pdarts M (core M Q x.1.piece) x.2.1,
        ∃ j < (pdarts M (core M Q x.1.piece) x.2.1).card, g (c'.nmem (IXb + j)) = y) ∧
      (∀ i j, i < j → j < (pdarts M (core M Q x.1.piece) x.2.1).card →
        gid (g (c'.nmem (IXb + i))) < gid (g (c'.nmem (IXb + j)))) ∧
      (∀ j < (pdarts M (core M Q x.1.piece) x.2.1).card, c'.nmem (b + j) = 1) ∧
      (∀ j < (pdarts M (core M Q x.1.piece) x.2.1).card,
        c'.nmem (b + (pdarts M (core M Q x.1.piece) x.2.1).card + j) =
          hlab x.2.1 (M.tail (g (c'.nmem (IXb + j))))) ∧
      (∀ j < (pdarts M (core M Q x.1.piece) x.2.1).card,
        c'.nmem (b + 2 * (pdarts M (core M Q x.1.piece) x.2.1).card + j) <
          (pdarts M (core M Q x.1.piece) x.2.1).card ∧
        g (c'.nmem (IXb + c'.nmem (b + 2 * (pdarts M (core M Q x.1.piece) x.2.1).card + j))) =
          M.rev (g (c'.nmem (IXb + j)))) ∧
      (∀ j < (pdarts M (core M Q x.1.piece) x.2.1).card,
        c'.nmem (SGb + j) < (pdarts M (core M Q x.1.piece) x.2.1).card ∧
        g (c'.nmem (IXb + c'.nmem (SGb + j))) = st (g (c'.nmem (IXb + j)))) ∧
      (∀ a, ¬ (CFb ≤ a ∧ a < b + 3 * n) → c'.nmem a = c.nmem a) ∧
      (∀ y, ¬ lgPw y → c'.nreg y = c.nreg y) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set B := pdarts M (core M Q x.1.piece) x.2.1 with hB
  have hBP : ∀ y ∈ B, y ∈ x.1.piece := fun y hy => (mem_core.1 (mem_pdarts.1 hy).1).1
  -- stage 1: the flags
  obtain ⟨c₁, t₁, e₁, ht₁, f1, m1, n1, rr1, rm1, o1⟩ := cfScan_rec (P := P) hQ hd c hA hc
    (OUTb := CFb) r00 r01 r02 r03 r04 r06 r07 r21 (by omega) (by omega) l0
  have q1 : ∀ y, ¬ lgPw y → c₁.nreg y = c.nreg y := fun y hy => by
    unfold lgPw at hy; exact n1 y (by unfold vscr; omega) (by omega) (by omega)
  set F : ℕ → ℕ := fun j => c₁.nmem (CFb + j) with hF
  have hFv : ∀ i < n, F i = bf (g i ∈ B) := fun i hi => f1 i hi
  have hFp : ∀ i < n, (0 < F i ↔ g i ∈ B) := fun i hi => by rw [hFv i hi]; exact bf_pos
  -- the size
  have hcntB : cnt F n = B.card := by
    rw [cnt_congr (G := fun j => bf (g j ∈ B)) hFv]
    exact cnt_bf_card (fun i hi j hj e => hA.g_inj hi hj e)
      (fun y hy => hA.g_surj y (hBP y hy))
  -- stage 2: the compaction
  obtain ⟨c₂, t₂, e₂, ht₂, h6, hci, m2, n2, rr2, rm2, o2⟩ := lgP2_exec (P := P) c₁ e₁.wb_right
    (by rw [q1 _ (by unfold lgPw; omega), r00]) (by rw [q1 _ (by unfold lgPw; omega), r04])
    (by rw [q1 _ (by unfold lgPw; omega), r08]) (by rw [q1 _ (by unfold lgPw; omega), r09])
    l1 l2 (by omega) (by omega)
  have q2 : ∀ y, ¬ lgPw y → c₂.nreg y = c.nreg y := fun y hy => by
    unfold lgPw at hy; rw [n2 y (by omega), q1 y (by unfold lgPw; omega)]
  set n' := cnt F n with hn'
  have hn'n : n' ≤ n := cnt_le F n
  -- the compaction as functions
  set CI : ℕ → ℕ := fun i => c₂.nmem (CIb + i) with hCI
  set IX : ℕ → ℕ := fun k => c₂.nmem (IXb + k) with hIX
  have hci' : ∀ i < n, 0 < F i → CI i = cnt F i ∧ IX (cnt F i) = i := hci
  have hpos := cmp_pos (fun i hi hf => (hci' i hi hf).2)
  have hcix := cmp_ci hci'
  -- the frame of the flags through the compaction
  have m2F : ∀ i < n, c₂.nmem (CFb + i) = F i := fun i hi => m2 _ (by omega)
  -- stage 3: the registers
  obtain ⟨c₃, t₃, e₃, ht₃, s11, s12, s13, n3, m3, rr3, rm3, o3⟩ := lgP3_exec (P := P) c₂
    e₂.wb_right (by rw [q2 _ (by unfold lgPw; omega), r10]) h6 (by omega)
  have q3 : ∀ y, ¬ lgPw y → c₃.nreg y = c.nreg y := fun y hy => by
    unfold lgPw at hy; rw [n3 y (by omega), q2 y (by unfold lgPw; omega)]
  -- stage 4: the ones
  obtain ⟨c₄, t₄, e₄, ht₄, f4, m4, n4, rr4, rm4, o4⟩ := lgP4_exec (P := P) c₃ e₃.wb_right s11
    (by rw [q3 _ (by unfold lgPw; omega), r10])
    (by rw [n3 _ (by omega), n2 _ (by omega), n1 _ (by unfold vscr; omega) (by omega) (by omega),
      r21])
    (by omega)
  have q4 : ∀ y, ¬ lgPw y → c₄.nreg y = c.nreg y := fun y hy => by
    unfold lgPw at hy; rw [n4 y (by unfold vscr; omega) (by omega) (by omega),
      q3 y (by unfold lgPw; omega)]
  have m4' : ∀ a, a < b → c₄.nmem a = c₂.nmem a := fun a ha => by
    rw [m4 a (by omega), m3]
  -- stage 5: the hole labels
  have hIX4 : ∀ j < n', c₄.nmem (IXb + j) = IX j := fun j hj => m4' _ (by omega)
  obtain ⟨c₅, t₅, e₅, ht₅, f5, m5, n5, rr5, rm5, o5⟩ := ggProg_exec (P := P) c₄ e₄.wb_right
    (a := 5811) (b := 5809) (cc := 5802) (dd := 5812) (m := n') (IXb := IXb)
    (Ab := R + 3 + 2 * n) (OUTb := b + n') (by omega) (by omega) (by omega) (by omega)
    (by rw [n4 _ (by unfold vscr; omega) (by omega) (by omega), s11])
    (by rw [q4 _ (by unfold lgPw; omega), r09]) (by rw [q4 _ (by unfold lgPw; omega), r02])
    (by rw [n4 _ (by unfold vscr; omega) (by omega) (by omega), s12]) (by omega) (by omega)
    (by omega) (fun j hj => by rw [hIX4 j hj]; have := (hpos j hj).1; omega)
    (fun j hj => by omega) (fun j hj => by rw [hIX4 j hj]; have := (hpos j hj).1; omega)
  have q5 : ∀ y, ¬ lgPw y → c₅.nreg y = c.nreg y := fun y hy => by
    unfold lgPw at hy; rw [n5 y (by omega), q4 y (by unfold lgPw; omega)]
  have m5' : ∀ a, a < b → c₅.nmem a = c₂.nmem a := fun a ha => by
    rw [m5 a (by omega), m4' a ha]
  -- stage 6: the reverse
  have hRP5 : ∀ i < n, c₅.nmem (R + 3 + n + i) = c.nmem (R + 3 + n + i) := fun i hi => by
    rw [m5' _ (by omega), m2 _ (by omega), m1 _ (by omega)]
  have hSP5 : ∀ i < n, c₅.nmem (R + 3 + 5 * n + i) = c.nmem (R + 3 + 5 * n + i) := fun i hi => by
    rw [m5' _ (by omega), m2 _ (by omega), m1 _ (by omega)]
  have hCF5 : ∀ i < n, c₅.nmem (CFb + i) = F i := fun i hi => by
    rw [m5' _ (by omega), m2F i hi]
  have hCI5 : ∀ i < n, c₅.nmem (CIb + i) = CI i := fun i hi => m5' _ (by omega)
  have hCIlt : ∀ i < n, 0 < F i → CI i < n := fun i hi hf => by
    have := (hcix i hi hf).1; omega
  have hCIinj : ∀ i < n, ∀ j < n, 0 < F i → 0 < F j → CI i = CI j → i = j :=
    fun i hi j hj hfi hfj he => by
      rw [(hci' i hi hfi).1, (hci' j hj hfj).1] at he
      exact cnt_inj F hfi hfj he
  obtain ⟨c₆, t₆, e₆, ht₆, f6, m6, r610, r611, r612, n6, rr6, rm6, o6⟩ := lgP6_exec (P := P) c₅
    e₅.wb_right (by rw [q5 _ (by unfold lgPw; omega), r00])
    (by rw [q5 _ (by unfold lgPw; omega), r04]) (by rw [q5 _ (by unfold lgPw; omega), r08])
    (by rw [q5 _ (by unfold lgPw; omega), r01])
    (by rw [n5 _ (by omega), n4 _ (by unfold vscr; omega) (by omega) (by omega), s13])
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi hf => by rw [hRP5 i hi]; exact (hA.rp i hi).1)
    (fun i hi hf => by rw [hCF5 i hi] at hf; rw [hCI5 i hi]; exact hCIlt i hi hf)
    (fun i hi j hj hfi hfj he => by
      rw [hCF5 i hi] at hfi; rw [hCF5 j hj] at hfj; rw [hCI5 i hi, hCI5 j hj] at he
      exact hCIinj i hi j hj hfi hfj he)
  have q6 : ∀ y, ¬ lgPw y → c₆.nreg y = c.nreg y := fun y hy => by
    unfold lgPw at hy; rw [n6 y (by omega), q5 y (by unfold lgPw; omega)]
  have m6' : ∀ a, a < b → c₆.nmem a = c₂.nmem a := fun a ha => by
    rw [m6 a (by omega), m5' a ha]
  -- stage 7: the rotation
  have hCF6 : ∀ i < n, c₆.nmem (CFb + i) = F i := fun i hi => by
    rw [m6' _ (by omega), m2F i hi]
  have hCI6 : ∀ i < n, c₆.nmem (CIb + i) = CI i := fun i hi => m6' _ (by omega)
  have hSP6 : ∀ i < n, c₆.nmem (R + 3 + 5 * n + i) = c.nmem (R + 3 + 5 * n + i) := fun i hi => by
    rw [m6' _ (by omega), m2 _ (by omega), m1 _ (by omega)]
  obtain ⟨c₇, t₇, e₇, ht₇, f7, m7, n7, rr7, rm7, o7⟩ := lgP7_exec (P := P) c₆ e₆.wb_right
    r610 r611 r612 (by rw [q6 _ (by unfold lgPw; omega), r05])
    (by rw [q6 _ (by unfold lgPw; omega), r14]) (by omega) (by omega) (by omega) (by omega)
    (by omega)
    (fun i hi hf => by
      rw [hCF6 i hi] at hf; rw [hSP6 i hi]; exact (hSP i hi ((hFp i hi).1 hf)).1)
    (fun i hi hf => by rw [hCF6 i hi] at hf; rw [hCI6 i hi]; exact hCIlt i hi hf)
    (fun i hi j hj hfi hfj he => by
      rw [hCF6 i hi] at hfi; rw [hCF6 j hj] at hfj; rw [hCI6 i hi, hCI6 j hj] at he
      exact hCIinj i hi j hj hfi hfj he)
  have q7 : ∀ y, ¬ lgPw y → c₇.nreg y = c.nreg y := fun y hy => by
    unfold lgPw at hy; rw [n7 y (by omega), q6 y (by unfold lgPw; omega)]
  have m7' : ∀ a, a < SGb → c₇.nmem a = c₂.nmem a := fun a ha => by
    rw [m7 a (by omega), m6' a (by omega)]
  have hIX7 : ∀ k, k < n' → c₇.nmem (IXb + k) = IX k := fun k hk => m7' _ (by omega)
  -- the enumeration
  have pe : ∀ j < n', IX j < n ∧ g (IX j) ∈ B ∧ CI (IX j) = j := fun j hj => by
    obtain ⟨a1, a2, a3⟩ := hpos j hj
    exact ⟨a1, (hFp _ a1).1 a2, by rw [(hci' _ a1 a2).1, a3]⟩
  -- the relabelling of a dart of `B`
  have rel : ∀ i < n, g i ∈ B → CI i < n' ∧ g (IX (CI i)) = g i := fun i hi hb => by
    obtain ⟨a1, a2⟩ := hcix i hi ((hFp i hi).2 hb); exact ⟨a1, by rw [a2]⟩
  refine ⟨c₇, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), by omega, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, q7, by rw [rr7, rr6, rr5, rr4, rr3, rr2, rr1],
    by rw [rm7, rm6, rm5, rm4, rm3, rm2, rm1], by rw [o7, o6, o5, o4, o3, o2, o1]⟩
  · rw [n7 _ (by omega), n6 _ (by omega), n5 _ (by omega),
      n4 _ (by unfold vscr; omega) (by omega) (by omega), s11]
    exact hcntB
  · intro j hj
    rw [← hcntB] at hj
    rw [hIX7 j hj]; exact ⟨(pe j hj).1, (pe j hj).2.1⟩
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := hA.g_surj y (hBP y hy)
    obtain ⟨a1, a2⟩ := rel i hi hy
    refine ⟨CI i, by rw [← hcntB]; exact a1, ?_⟩
    rw [hIX7 _ a1, a2]
  · intro i j hij hj
    rw [← hcntB] at hj
    rw [hIX7 i (by omega), hIX7 j hj]
    obtain ⟨a1, a2, -⟩ := cnt_ix_mono (fun i hi hf => (hci' i hi hf).2) hij hj
    exact hA.g_mono _ _ a1 a2
  · intro j hj
    rw [← hcntB] at hj
    rw [m7 _ (by omega), m6 _ (by omega), m5 _ (by omega)]; exact f4 j hj
  · intro j hj
    rw [← hcntB] at hj ⊢
    have hpj := (pe j hj).1
    rw [hIX7 j hj]
    rw [m7 _ (by omega), m6 _ (by omega), f5 j hj, hIX4 j hj, m4 _ (by omega), m3,
      m2 _ (by omega), m1 _ (by omega)]
    exact hA.hp _ (pe j hj).1
  · intro j hj
    rw [← hcntB] at hj ⊢
    obtain ⟨p1, p2, p3⟩ := pe j hj
    rw [hIX7 j hj]
    have hf : 0 < F (IX j) := (hFp _ p1).2 p2
    have e6 := f6 _ p1 (by rw [hCF5 _ p1]; exact hf)
    rw [hCI5 _ p1, p3, hRP5 _ p1] at e6
    obtain ⟨r1, r2⟩ := hA.rp _ p1
    have hrB : g (c.nmem (R + 3 + n + IX j)) ∈ B := by
      rw [r2]; exact rev_mem_pdarts_core p2 (by rw [← r2]; exact hA.g_mem _ r1)
    rw [hCI5 _ r1] at e6
    rw [m7 _ (by omega), e6]
    obtain ⟨a1, a2⟩ := rel _ r1 hrB
    refine ⟨a1, ?_⟩
    rw [hIX7 _ a1, a2, r2]
  · intro j hj
    rw [← hcntB] at hj ⊢
    obtain ⟨p1, p2, p3⟩ := pe j hj
    rw [hIX7 j hj]
    have hf : 0 < F (IX j) := (hFp _ p1).2 p2
    have e7 := f7 _ p1 (by rw [hCF6 _ p1]; exact hf)
    rw [hCI6 _ p1, p3, hSP6 _ p1] at e7
    obtain ⟨s1, s2⟩ := hSP _ p1 p2
    have hsB : g (c.nmem (R + 3 + 5 * n + IX j)) ∈ B := by rw [s2]; exact hst _ p2
    rw [hCI6 _ s1] at e7
    rw [e7]
    obtain ⟨a1, a2⟩ := rel _ s1 hsB
    refine ⟨a1, ?_⟩
    rw [hIX7 _ a1, a2, s2]
  · intro a ha
    rw [m7 a (by omega), m6 a (by omega), m5 a (by omega), m4 a (by omega), m3,
      m2 a (by omega), m1 a (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
