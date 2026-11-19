module

public import PlanarFlow.NegSSSP.Enc.NodeFixP2
public import PlanarFlow.NegSSSP.Enc.NodeOne

/-!
# The fixed node with its registers below `2920`

The census of `nodeFullP2` (computed): 1279 natural registers; `[0, 2004)`, `[2600, 2920)`, and
seventeen blocks at `≥ 3000` (the renamed encoders `[3300, 3338)`, `[3400, 3418)`,
`[3500, 3600)`, `[3650, 3659)`, `[3700, 3748)`; the parameters `[10000, 10110)`,
`[10200, 10310)`, `[10400, 10521)`; the primaries and their programs `[10530, 10564)`,
`[10600, 10602)`, `[10610, 10624)`, `[10630, 10636)`, `[10640, 10646)`, `[10650, 10662)`,
`[10670, 10675)`, `[10680, 10685)`, `[10690, 10698)`: 646 registers counting the small gaps).
`[2004, 2600)` holds only 596 registers, so the blocks go to `[2004, 2549)` (avoiding `sdProg`'s
`[2550, 2594)`), `[2623, 2700)` and `[2720, 2744)` (free gaps of the low part of the encoders).

* `rbF l`: the piecewise-affine map exchanging each block `[a, a + n)` with `[b, b + n)`;
  `rbTbl` (the 17 blocks); **`rbF_inv`** (involutive: a kernel check below `10698`, the identity
  above); `rbSwap` (the permutation), `rbSwap_symm`, `rb_low` (identity below `2004`).
* `nfV` (the census as a predicate), `nodeFullP2_V` (kernel: `nodeFullP2` names only `nfV`),
  `rn_regsOK` (generic: renaming a natural-only statement), **`nodeFullR = rnS rbSwap
  nodeFullP2`**, **`nodeFullR_ok`**: it names only registers `< 2920`, reads no input, uses no
  randomness (so by `exec_nreg_keep` it keeps every register `≥ 2920`, in particular the driver's
  `2997 … 3012`: `RegKeep`).
* `PnInR` (the 14 sizes at their renamed registers `2657 … 2670`), **`node_exec_fixedR`**: the
  statement of `node_exec_fixedP'` for `nodeFullR`, with `PnInR` and the register bound
  `d₀.nreg r ≤ W'` for `r ≥ 2004` outside the sizes; conclusion: also
  `∀ r ≥ 2920, d'.nreg r = d₀.nreg r`.

**The heap of the driver.** Nothing to change in the node: its run is on
words `≤ WN`, so every address it touches (the residues of the real memory at `W' + 1 + a`
included) is `≤ WN`. Run with `Exec.lift_trunc` (`U = (· < 2920)`, `Ws = WN`) from the driver's
configuration, it keeps the registers `≥ 2920` and the memory above `WN` (`regKeep_of_keep`,
`heapKeep_of_keep`); **what the driver must provide**: a heap base `Hb > WN` (the work area
`[0, Hb)` holds the node's natural data, the plain arrays, the encoders' slots and the residues of
its real memory), the node's data copied into the work area (and the result `W' + 1 + (Z + 20 M₀
+ ν x)` copied back to the frame), the registers `[2004, 2920)` bounded by `W'` (e.g. zeroed).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge
  Monge.FR CmpAbs ModNat

/-! ### A block involution -/

/-- Exchange each block `[a, a + n)` with `[b, b + n)` (first match). -/
def rbF : List (ℕ × ℕ × ℕ) → ℕ → ℕ
  | [], r => r
  | (a, b, n) :: l, r =>
    if a ≤ r ∧ r < a + n then b + (r - a) else if b ≤ r ∧ r < b + n then a + (r - b) else rbF l r

theorem rbF_out {l : List (ℕ × ℕ × ℕ)} {r : ℕ}
    (h : ∀ e ∈ l, ¬ (e.1 ≤ r ∧ r < e.1 + e.2.2) ∧ ¬ (e.2.1 ≤ r ∧ r < e.2.1 + e.2.2)) :
    rbF l r = r := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨a, b, n⟩ := e
    have h0 := h (a, b, n) (by simp)
    simp only [rbF]
    rw [ite_eq_right_of_eq_false _ _ (eq_false h0.1), ite_eq_right_of_eq_false _ _ (eq_false h0.2)]
    exact ih fun e he => h e (by simp [he])

/-- The 17 blocks of registers `≥ 3000` of `nodeFullP2` and their places below `2744`. -/
def rbTbl : List (ℕ × ℕ × ℕ) :=
  [(10000, 2004, 110), (10200, 2114, 110), (10400, 2224, 121), (3500, 2345, 100),
    (3700, 2445, 48), (3300, 2493, 38), (3400, 2531, 18), (10530, 2623, 34), (10610, 2657, 14),
    (10650, 2671, 12), (3650, 2683, 9), (10690, 2692, 8), (10600, 2720, 2), (10630, 2722, 6),
    (10640, 2728, 6), (10670, 2734, 5), (10680, 2739, 5)]

theorem rb_out {r : ℕ} (h : r < 2004 ∨ 10698 ≤ r) : rbF rbTbl r = r := by
  apply rbF_out
  intro e he
  simp only [rbTbl, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;> (dsimp only; omega)

/-- `r` lies in one of the blocks of `l`. -/
def RbIn (l : List (ℕ × ℕ × ℕ)) (r : ℕ) : Prop :=
  ∃ e ∈ l, (e.1 ≤ r ∧ r < e.1 + e.2.2) ∨ (e.2.1 ≤ r ∧ r < e.2.1 + e.2.2)

theorem rbF_mem {l : List (ℕ × ℕ × ℕ)} {r : ℕ} (h : RbIn l r) : RbIn l (rbF l r) := by
  induction l with
  | nil => obtain ⟨e, he, -⟩ := h; simp at he
  | cons e l ih =>
    obtain ⟨a, b, n⟩ := e
    simp only [rbF]
    split_ifs with h1 h2
    · refine ⟨(a, b, n), by simp, Or.inr ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
    · refine ⟨(a, b, n), by simp, Or.inl ⟨?_, ?_⟩⟩ <;> dsimp only <;> omega
    · obtain ⟨f, hf, hf'⟩ := h
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · exfalso; rcases hf' with hf' | hf'
        · exact h1 hf'
        · exact h2 hf'
      · obtain ⟨g, hg, hg'⟩ := ih ⟨f, hf, hf'⟩
        exact ⟨g, by simp [hg], hg'⟩

theorem rbF_notMem {l : List (ℕ × ℕ × ℕ)} {r : ℕ} (h : ¬ RbIn l r) : rbF l r = r :=
  rbF_out fun e he => ⟨fun h' => h ⟨e, he, Or.inl h'⟩, fun h' => h ⟨e, he, Or.inr h'⟩⟩

/-- The intervals of a block. -/
def rbIv (e : ℕ × ℕ × ℕ) : List (ℕ × ℕ) := [(e.1, e.1 + e.2.2), (e.2.1, e.2.1 + e.2.2)]

/-- **Pairwise disjoint blocks** (Boolean). -/
def rbDisj : List (ℕ × ℕ × ℕ) → Bool
  | [] => true
  | e :: l => (decide (e.1 + e.2.2 ≤ e.2.1) || decide (e.2.1 + e.2.2 ≤ e.1)) &&
      l.all (fun f => (rbIv f).all fun J => (rbIv e).all fun I =>
        decide (I.2 ≤ J.1) || decide (J.2 ≤ I.1)) && rbDisj l

theorem rbF_c1 {a b n r : ℕ} {l : List (ℕ × ℕ × ℕ)} (h : a ≤ r ∧ r < a + n) :
    rbF ((a, b, n) :: l) r = b + (r - a) := by
  simp only [rbF]; rw [ite_eq_left_of_eq_true _ _ (eq_true h)]

theorem rbF_c2 {a b n r : ℕ} {l : List (ℕ × ℕ × ℕ)} (h : ¬ (a ≤ r ∧ r < a + n))
    (h' : b ≤ r ∧ r < b + n) : rbF ((a, b, n) :: l) r = a + (r - b) := by
  simp only [rbF]; rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_left_of_eq_true _ _ (eq_true h')]

theorem rbF_c3 {a b n r : ℕ} {l : List (ℕ × ℕ × ℕ)} (h : ¬ (a ≤ r ∧ r < a + n))
    (h' : ¬ (b ≤ r ∧ r < b + n)) : rbF ((a, b, n) :: l) r = rbF l r := by
  simp only [rbF]; rw [ite_eq_right_of_eq_false _ _ (eq_false h), ite_eq_right_of_eq_false _ _ (eq_false h')]

/-- **Disjoint blocks give an involution.** -/
theorem rbF_inv_of {l : List (ℕ × ℕ × ℕ)} (h : rbDisj l = true) : Function.Involutive (rbF l) := by
  induction l with
  | nil => intro r; rfl
  | cons e l ih =>
    obtain ⟨a, b, n⟩ := e
    simp only [rbDisj, rbIv, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      List.all_eq_true, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at h
    obtain ⟨⟨h0, hl⟩, h3⟩ := h
    intro r
    have hout : ∀ s, RbIn l s → ¬ (a ≤ s ∧ s < a + n) ∧ ¬ (b ≤ s ∧ s < b + n) := by
      intro s ⟨f, hf, hs⟩
      obtain ⟨⟨x1, x2⟩, x3, x4⟩ := hl f hf
      constructor <;> rintro ⟨y1, y2⟩ <;> rcases hs with ⟨z1, z2⟩ | ⟨z1, z2⟩ <;> omega
    show rbF _ (rbF _ r) = r
    by_cases r1 : a ≤ r ∧ r < a + n
    · rw [rbF_c1 r1, rbF_c2 (by omega) (by omega)]; omega
    · by_cases r2 : b ≤ r ∧ r < b + n
      · rw [rbF_c2 r1 r2, rbF_c1 (by omega)]; omega
      · rw [rbF_c3 r1 r2]
        by_cases hr : RbIn l r
        · obtain ⟨s1, s2⟩ := hout _ (rbF_mem hr)
          rw [rbF_c3 s1 s2]; exact ih h3 r
        · rw [rbF_notMem hr, rbF_c3 r1 r2]; exact rbF_notMem hr

theorem rb_disj : rbDisj rbTbl = true := by decide

/-- **The block map is an involution.** -/
theorem rbF_inv : Function.Involutive (rbF rbTbl) := rbF_inv_of rb_disj

/-- The block involution as a permutation. -/
def rbSwap : Equiv.Perm ℕ := Function.Involutive.toPerm _ rbF_inv

theorem rbSwap_apply (r : ℕ) : rbSwap r = rbF rbTbl r := rfl

theorem rbSwap_symm : rbSwap.symm = rbSwap := Function.Involutive.toPerm_symm rbF_inv

theorem rb_low (r : ℕ) (h : r < 2004) : rbSwap r = r := rb_out (Or.inl h)

theorem rb_ge (r : ℕ) (h : 2004 ≤ r) : 2004 ≤ rbSwap r := by
  rw [rbSwap_apply]
  by_cases hr : RbIn rbTbl r
  · obtain ⟨e, he, h'⟩ := rbF_mem hr
    simp only [rbTbl, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> (dsimp only at h'; omega)
  · rw [rbF_notMem hr]; exact h

theorem rb_sizes_check : (List.range' 2657 14).all (fun x => decide (10610 ≤ rbF rbTbl x)) =
    true := by decide

theorem rb_mid (r : ℕ) (h1 : 2600 ≤ r) (h2 : r < 3748) :
    2004 ≤ rbSwap r ∧ (rbSwap r < 2657 ∨ 2671 ≤ rbSwap r) := by
  refine ⟨rb_ge r (by omega), ?_⟩
  by_contra hc
  have hx : 2657 ≤ rbSwap r ∧ rbSwap r < 2657 + 14 := by omega
  have := rb_sizes_check
  simp only [List.all_eq_true, List.mem_range', decide_eq_true_eq] at this
  obtain ⟨i, hi, hi'⟩ : ∃ i, i < 14 ∧ rbSwap r = 2657 + i := ⟨rbSwap r - 2657, by omega, by omega⟩
  have h3 := this (2657 + i) ⟨i, hi, by ring⟩
  rw [← hi', ← rbSwap_apply, ← Equiv.Perm.mul_apply] at h3
  have : (rbSwap * rbSwap) r = r := by
    show rbSwap (rbSwap r) = r
    rw [rbSwap_apply, rbSwap_apply]; exact rbF_inv r
  omega

/-! ### The registers of the renamed node -/

/-- The registers named by `nodeFullP2` (the census). -/
def nfV (r : ℕ) : Bool :=
  decide (r < 2004) || decide (2600 ≤ r ∧ r < 2623) || decide (2700 ≤ r ∧ r < 2720) ||
  decide (2800 ≤ r ∧ r < 2835) || decide (2900 ≤ r ∧ r < 2920) || decide (3300 ≤ r ∧ r < 3338) ||
  decide (3400 ≤ r ∧ r < 3418) || decide (3500 ≤ r ∧ r < 3600) ||
  decide (3650 ≤ r ∧ r < 3659) || decide (3700 ≤ r ∧ r < 3748) ||
  decide (10000 ≤ r ∧ r < 10110) || decide (10200 ≤ r ∧ r < 10310) ||
  decide (10400 ≤ r ∧ r < 10521) || decide (10530 ≤ r ∧ r < 10564) ||
  decide (10600 ≤ r ∧ r < 10602) || decide (10610 ≤ r ∧ r < 10624) ||
  decide (10630 ≤ r ∧ r < 10636) || decide (10640 ≤ r ∧ r < 10646) ||
  decide (10650 ≤ r ∧ r < 10662) || decide (10670 ≤ r ∧ r < 10675) ||
  decide (10680 ≤ r ∧ r < 10685) || decide (10690 ≤ r ∧ r < 10698)

set_option maxRecDepth 100000 in
theorem nodeFullP2_V : nodeFullP2.regsOK nfV = true := by kernel_rfl

set_option maxRecDepth 100000 in
theorem nodeFullP2_natOnly : Klein.natOnly nodeFullP2 = true := by kernel_rfl

set_option maxRecDepth 100000 in
theorem nodeFullP2_noInp : nodeFullP2.noInp = true := by kernel_rfl

set_option maxRecDepth 100000 in
theorem nodeFullP2_noRand : nodeFullP2.noRand = true := by kernel_rfl

/-- The registers of the moved blocks. -/
def rbSrc : List ℕ := (rbTbl.map fun e => List.range' e.1 e.2.2).flatten

set_option maxRecDepth 100000 in
theorem rb_src_check : rbSrc.all (fun r => decide (rbF rbTbl r < 2920)) = true := by
  decide +kernel

theorem rb_V (r : ℕ) (h : nfV r = true) : rbSwap r < 2920 := by
  rw [rbSwap_apply]
  have hsrc : (∃ e ∈ rbTbl, e.1 ≤ r ∧ r < e.1 + e.2.2) → rbF rbTbl r < 2920 := by
    rintro ⟨e, he, h1, h2⟩
    have := rb_src_check
    simp only [List.all_eq_true, decide_eq_true_eq] at this
    exact this r (by
      simp only [rbSrc, List.mem_flatten, List.mem_map]
      exact ⟨_, ⟨e, he, rfl⟩, List.mem_range'.2 ⟨r - e.1, by omega, by omega⟩⟩)
  simp only [nfV, Bool.or_eq_true, decide_eq_true_eq] at h
  by_cases hr : RbIn rbTbl r
  · obtain ⟨e, he, h'⟩ := hr
    rcases h' with h' | h'
    · exact hsrc ⟨e, he, h'⟩
    · exfalso
      simp only [rbTbl, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl <;> (dsimp only at h'; omega)
  · rw [rbF_notMem hr]
    by_contra hc
    apply hr
    have hh : r ∈ rbSrc := by
      simp only [rbSrc, rbTbl, List.map_cons, List.map_nil, List.flatten_cons,
        List.flatten_nil, List.mem_append, List.mem_range'_1, List.not_mem_nil, or_false]
      omega
    simp only [rbSrc, List.mem_flatten, List.mem_map] at hh
    obtain ⟨_, ⟨e, he, rfl⟩, hm⟩ := hh
    rw [List.mem_range'_1] at hm
    exact ⟨e, he, Or.inl hm⟩

/-- Renaming a natural-only statement: the registers named are the images. -/
theorem rn_regsOK (π : Equiv.Perm ℕ) {V U : ℕ → Bool} (hVU : ∀ r, V r = true → U (π r) = true) :
    ∀ s : Stmt, Klein.natOnly s = true → s.regsOK V = true → (rnS π s).regsOK U = true := by
  intro s
  induction s with
  | skip => intro _ _; rfl
  | instr i =>
    intro hn hs
    simp only [Klein.natOnly, Bool.not_eq_true'] at hn
    simp only [regsOK, Instr.regsOK, rnS, List.all_eq_true] at hs ⊢
    cases i <;> simp_all [rnI, Instr.regs, Instr.isReal]
  | seq s t ih₁ ih₂ =>
    intro hn hs
    simp only [Klein.natOnly, regsOK, rnS, Bool.and_eq_true] at hn hs ⊢
    exact ⟨ih₁ hn.1 hs.1, ih₂ hn.2 hs.2⟩
  | ifLtN a b s t ih₁ ih₂ =>
    intro hn hs
    simp only [Klein.natOnly, regsOK, rnS, Bool.and_eq_true] at hn hs ⊢
    exact ⟨⟨⟨hVU a hs.1.1.1, hVU b hs.1.1.2⟩, ih₁ hn.1 hs.1.2⟩, ih₂ hn.2 hs.2⟩
  | ifLtR a b s t _ _ => intro hn; simp [Klein.natOnly] at hn
  | whileLtN a b s ih =>
    intro hn hs
    simp only [Klein.natOnly, regsOK, rnS, Bool.and_eq_true] at hn hs ⊢
    exact ⟨⟨hVU a hs.1.1, hVU b hs.1.2⟩, ih hn hs.2⟩
  | whileLtR a b s _ => intro hn; simp [Klein.natOnly] at hn

theorem rn_noInp (π : Equiv.Perm ℕ) : ∀ s : Stmt, (rnS π s).noInp = s.noInp := by
  intro s
  induction s with
  | skip => rfl
  | instr i => cases i <;> rfl
  | seq s t ih₁ ih₂ => simp only [rnS, noInp, ih₁, ih₂]
  | ifLtN a b s t ih₁ ih₂ => simp only [rnS, noInp, ih₁, ih₂]
  | ifLtR a b s t ih₁ ih₂ => simp only [rnS, noInp, ih₁, ih₂]
  | whileLtN a b s ih => simp only [rnS, noInp, ih]
  | whileLtR a b s ih => simp only [rnS, noInp, ih]

theorem rn_noRand (π : Equiv.Perm ℕ) : ∀ s : Stmt, (rnS π s).noRand = s.noRand := by
  intro s
  induction s with
  | skip => rfl
  | instr i => cases i <;> rfl
  | seq s t ih₁ ih₂ => simp only [rnS, noRand, ih₁, ih₂]
  | ifLtN a b s t ih₁ ih₂ => simp only [rnS, noRand, ih₁, ih₂]
  | ifLtR a b s t ih₁ ih₂ => simp only [rnS, noRand, ih₁, ih₂]
  | whileLtN a b s ih => simp only [rnS, noRand, ih]
  | whileLtR a b s ih => simp only [rnS, noRand, ih]

/-- **The fixed node with its registers below `2920`.** -/
def nodeFullR : Stmt := rnS rbSwap nodeFullP2

/-- **`nodeFullR` names only registers `< 2920`**, reads no input, uses no randomness. -/
theorem nodeFullR_ok : nodeFullR.regsOK (fun r => decide (r < 2920)) = true ∧
    nodeFullR.noInp = true ∧ nodeFullR.noRand = true :=
  ⟨rn_regsOK rbSwap (fun r h => by simpa using rb_V r h) _ nodeFullP2_natOnly nodeFullP2_V,
    by rw [nodeFullR, rn_noInp]; exact nodeFullP2_noInp,
    by rw [nodeFullR, rn_noRand]; exact nodeFullP2_noRand⟩

/-- The 14 sizes at their renamed registers. -/
structure PnInR (f : ℕ → ℕ) (p₀ p₁ : FeP) (m w b B Y S : ℕ) : Prop where
  a0 : f 2657 = p₀.nD
  a1 : f 2658 = p₀.k
  a2 : f 2659 = p₀.nV
  a3 : f 2660 = p₀.nF
  b0 : f 2661 = p₁.nD
  b1 : f 2662 = p₁.k
  b2 : f 2663 = p₁.nV
  b3 : f 2664 = p₁.nF
  m : f 2665 = m
  w : f 2666 = w
  b : f 2667 = b
  B : f 2668 = B
  Y : f 2669 = Y
  S : f 2670 = S

theorem pnInR_ren {f : ℕ → ℕ} {p₀ p₁ : FeP} {m w b B Y S : ℕ}
    (h : PnInR f p₀ p₁ m w b B Y S) : PnIn (fun r => f (rbSwap r)) p₀ p₁ m w b B Y S := by
  obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, hm, hw, hb, hB, hY, hS⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [rbSwap_apply] <;>
    first
    | (rw [show rbF rbTbl 10610 = 2657 by decide]; exact a0)
    | (rw [show rbF rbTbl 10611 = 2658 by decide]; exact a1)
    | (rw [show rbF rbTbl 10612 = 2659 by decide]; exact a2)
    | (rw [show rbF rbTbl 10613 = 2660 by decide]; exact a3)
    | (rw [show rbF rbTbl 10614 = 2661 by decide]; exact b0)
    | (rw [show rbF rbTbl 10615 = 2662 by decide]; exact b1)
    | (rw [show rbF rbTbl 10616 = 2663 by decide]; exact b2)
    | (rw [show rbF rbTbl 10617 = 2664 by decide]; exact b3)
    | (rw [show rbF rbTbl 10618 = 2665 by decide]; exact hm)
    | (rw [show rbF rbTbl 10619 = 2666 by decide]; exact hw)
    | (rw [show rbF rbTbl 10620 = 2667 by decide]; exact hb)
    | (rw [show rbF rbTbl 10621 = 2668 by decide]; exact hB)
    | (rw [show rbF rbTbl 10622 = 2669 by decide]; exact hY)
    | (rw [show rbF rbTbl 10623 = 2670 by decide]; exact hS)

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
open Classical in
/-- **The node of the recursion as one run of one fixed program naming only registers `< 2920`**
(see the module docstring). -/
theorem node_exec_fixedR (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {P P₀ P₁ : Finset D} (hS : SplitF N P P₀ P₁) (hB : (bdry N P₀ P₁).Nonempty) (ℓ : D → ℤ)
    (δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    (fd₀ : FaceData N P₀ (bdry N P₀ P₁)) (hq₀ : fd₀.q ≤ 18 * P.card)
    (hk₀ : fd₀.k ^ 2 ≤ 1200 * P.card)
    (fd₁ : FaceData N P₁ (bdry N P₀ P₁)) (hq₁ : fd₁.q ≤ 18 * P.card)
    (hk₁ : fd₁.k ^ 2 ≤ 1200 * P.card)
    -- the plain numberings and the constants of the two encoders
    (σ₀ : fd₀.DQ ≃ Fin (Fintype.card fd₀.DQ)) (νv₀ : fd₀.VQ ≃ Fin (Fintype.card fd₀.VQ))
    (τ₀ : fd₀.FQ ≃ Fin (Fintype.card fd₀.FQ))
    (σ₁ : fd₁.DQ ≃ Fin (Fintype.card fd₁.DQ)) (νv₁ : fd₁.VQ ≃ Fin (Fintype.card fd₁.VQ))
    (τ₁ : fd₁.FQ ≃ Fin (Fintype.card fd₁.FQ)) (p₀ p₁ : FeP)
    (hpD₀ : p₀.nD = Fintype.card fd₀.DQ) (hpk₀ : p₀.k = fd₀.k)
    (hpV₀ : p₀.nV = Fintype.card fd₀.VQ) (hpF₀ : p₀.nF = Fintype.card fd₀.FQ)
    (hpD₁ : p₁.nD = Fintype.card fd₁.DQ) (hpk₁ : p₁.k = fd₁.k)
    (hpV₁ : p₁.nV = Fintype.card fd₁.VQ) (hpF₁ : p₁.nF = Fintype.card fd₁.FQ)
    {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (hN : NodeEnc N P₀ P₁ m w e ν ι)
    (hb : b = (bdry N P₀ P₁).card)
    (Pb₀ Pb₁ Z M₀ Y S W' B M WN : ℕ) (I : Input) (c : Config)
    (hM₀ : M₀ = m + w + 1) (hZ : loB m w ≤ Z) (hbZ : bfWP b < Z)
    (hK₀ : 2 * p₀.Kw + 1 < Z) (hK₁ : 2 * p₁.Kw + 1 < Z)
    (hkk₀ : p₀.NN + fd₀.k * fd₀.k ≤ Z) (hkk₁ : p₁.NN + fd₁.k * fd₁.k ≤ Z)
    (hY : Z + 22 * M₀ ≤ Y)
    (hSz : w ≤ S ∧ b * b ≤ S ∧ fd₀.k ≤ S ∧ fd₁.k ≤ S)
    -- the layout: the node's data, the positions, then the two encoders
    (hPb₀ : Pb₀ = Y + 16 * S) (hPb₁ : Pb₁ = Y + 16 * S + w)
    (hI0₀ : p₀.I0 = Y + 16 * S + 2 * w) (hI0₁ : p₁.I0 = p₀.END)
    -- the word bounds of the encoders
    (hL₀ : p₀.Lmax = feIsoB p₀.A p₀.N p₀.FN
      (srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat)
    (hL₁ : p₁.Lmax = feIsoB p₁.A p₁.N p₁.FN
      (srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat)
    (hW' : W' = pnW p₀ p₁)
    -- the word bounds of the node
    (hWN : 2 * W' + 1 + M * M + M ≤ WN ∧
      2 * W' + 2 + (2 * p₀.Kw + 1) +
          (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) *
            (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) +
          (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) ≤ WN ∧
      2 * W' + 2 + (2 * p₁.Kw + 1) +
          (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1) *
            (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1) +
          (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1) ≤ WN ∧
      2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1 + 2 * M ≤ WN ∧
      2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1 + 2 * M ≤ WN ∧
      Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k ≤ WN ∧ Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k ≤ WN ∧
      (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat ≤ WN ∧
      (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat ≤ WN)
    (hMd : M = 2 * nodeHN m b w B + 1)
    (hc : WordsBounded W' c) (hctx : NCtx m w b Z M₀ c) (hx : XCtx Y S c)
    (hTm : ∀ d < m, c.nmem (Z + 0 * M₀ + d) = encT N e ν d)
    (hHm : ∀ d < m, c.nmem (Z + 1 * M₀ + d) = encH N e ν d)
    (hSm : ∀ d < m, c.nmem (Z + 2 * M₀ + d) = encS P₀ e d)
    (hLm : ∀ d < m, c.rmem (Z + 3 * M₀ + d) = ℓ (e d))
    (hD₀ : ∀ v < w, c.rmem (Z + 4 * M₀ + v) = δ₀ (ι v))
    (hD₁ : ∀ v < w, c.rmem (Z + 5 * M₀ + v) = δ₁ (ι v))
    (hz : ∀ a < Z, c.nmem a = 0)
    (hpos₀ : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₀ + ν x) < fd₀.k ∧
      fd₀.Q.tail (fd₀.g (c.nmem (Pb₀ + ν x))) = fd₀.j x)
    (hpos₁ : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₁ + ν x) < fd₁.k ∧
      fd₁.Q.tail (fd₁.g (c.nmem (Pb₁ + ν x))) = fd₁.j x)
    -- the plain arrays of the two maps
    (hQRV₀ : ∀ d, c.nmem (p₀.I0 + σ₀ d) = σ₀ (fd₀.Q.rev d))
    (hQNT₀ : ∀ d, c.nmem (p₀.I0 + p₀.nD + σ₀ d) = νv₀ (fd₀.Q.tail d))
    (hQNF₀ : ∀ d, c.nmem (p₀.I0 + 2 * p₀.nD + σ₀ d) = τ₀ (fd₀.Q.face d))
    (hQIS₀ : ∀ d, c.nmem (p₀.I0 + 3 * p₀.nD + σ₀ d) = if d ∈ fd₀.P'.image fd₀.e then 1 else 0)
    (hQLN₀ : ∀ d, c.nmem (p₀.I0 + 4 * p₀.nD + σ₀ d) =
      (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀) d).toNat)
    (hQG₀ : ∀ i < fd₀.k, c.nmem (p₀.I0 + 5 * p₀.nD + i) = σ₀ (fd₀.g i))
    (hQRV₁ : ∀ d, c.nmem (p₁.I0 + σ₁ d) = σ₁ (fd₁.Q.rev d))
    (hQNT₁ : ∀ d, c.nmem (p₁.I0 + p₁.nD + σ₁ d) = νv₁ (fd₁.Q.tail d))
    (hQNF₁ : ∀ d, c.nmem (p₁.I0 + 2 * p₁.nD + σ₁ d) = τ₁ (fd₁.Q.face d))
    (hQIS₁ : ∀ d, c.nmem (p₁.I0 + 3 * p₁.nD + σ₁ d) = if d ∈ fd₁.P'.image fd₁.e then 1 else 0)
    (hQLN₁ : ∀ d, c.nmem (p₁.I0 + 4 * p₁.nD + σ₁ d) =
      (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁) d).toNat)
    (hQG₁ : ∀ i < fd₁.k, c.nmem (p₁.I0 + 5 * p₁.nD + i) = σ₁ (fd₁.g i))
    (hI : NInv W' B c) (hZi : IntAll c)
    (d₀ : Config) (hS₀ : Sim 1000 W' M (W' + 1) c d₀) (hd₀ : WordsBounded WN d₀)
    (hR0 : ∀ r, 2004 ≤ r → (r < 2657 ∨ 2671 ≤ r) → d₀.nreg r ≤ W') 
    -- the primary values of the parameter program and its word bounds
    (h9600 : 9600 ≤ WN) (hin : PnInR d₀.nreg p₀ p₁ m w b B Y S)
    (hBN : hnB p₀ p₁ Pb₀ Pb₁ W' M (nodeHN m b w B)
      (Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k) (Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k)
      (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat
      (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat ≤ WN) :
    ∃ (Hc₀ Hc₁ : ℕ), 4800 ≤ Hc₀ ∧ Hc₀ ≤ kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k ∧
      4800 ≤ Hc₁ ∧ Hc₁ ≤ kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k ∧
      ∃ d' t₀ t₁ t', ∃ o : Option (V → ℤ),
        Exec I WN nodeFullR d₀ d'
          (t₀ + (hpCost (hfPrmL 0) + hpCost (hfPrmL 0) + hpCost hnPrmL + (t₁ + t'))) ∧
        t₀ ≤ pnCost p₀.nD p₁.nD ∧
        t₁ ≤ feCostDk p₀ + feCostDk p₁ + 8 ∧
        t' ≤ 4 * (8 + (61 * m + 12)) + 3 +
          (partNCost P.card fd₀.k b p₀.Kw p₀.N + partNCost P.card fd₁.k b p₁.Kw p₁.N + 14) +
          4 * (bfCostP b + 4 * bfWP b + 22 * (b * b) + 2 * (cNegMach C).dij (w + 1) (m + w) +
            232 * m + 450 * w + 92 * b + 2917) + 2 ∧
        PotOut ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).join
          (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁))) o ∧
        (∀ bf : DDG V → DDG V → Option (V → ℤ),
          bf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) =
            o →
          (step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = none ∧ d'.nreg 990 ≠ 0) ∨
          (∃ f, step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = some f ∧ d'.nreg 990 = 0 ∧
            ∀ x ∈ verts N (P₀ ∪ P₁),
              (f x : ℝ) = sgnD (nodeHN m b w B) M (d'.nmem (W' + 1 + (Z + 20 * M₀ + ν x))))) ∧
        (∀ r, 2920 ≤ r → d'.nreg r = d₀.nreg r) ∧ d'.output = c.output := by
  classical
  have hsy : rbSwap.symm = rbSwap := rbSwap_symm
  -- the configuration of the unrenamed program
  set e₀ := rnC rbSwap d₀ with he₀
  have hE : ∀ r, e₀.nreg r = d₀.nreg (rbSwap r) := fun r => by
    rw [he₀]; show d₀.nreg (rbSwap.symm r) = _; rw [hsy]
  have hS₁ : Sim 1000 W' M (W' + 1) c e₀ :=
    ⟨fun r hr => by rw [hE, rb_low r (by omega)]; exact hS₀.nreg r hr,
      fun r hr => by rw [hE, rb_low _ (by omega)]; exact hS₀.rreg r hr,
      fun a ha => hS₀.nmem a ha, fun a ha => hS₀.rmem a ha, hS₀.output⟩
  have hR₁ : ∀ r, 2600 ≤ r → r < 3748 → e₀.nreg r ≤ W' := fun r h1 h2 => by
    rw [hE]
    obtain ⟨a1, a2⟩ := rb_mid r h1 h2
    exact hR0 _ a1 a2
  obtain ⟨Hc₀, Hc₁, g1, g2, g3, g4, d', t₀, t₁, t', o, ex, ht₀, ht₁, ht', hpot, hstep, hout⟩ :=
    node_exec_fixedP' C hfr hmssp hS hB ℓ δ₀ δ₁ hδ₀ hδ₁ fd₀ hq₀ hk₀ fd₁ hq₁ hk₁ σ₀ νv₀ τ₀ σ₁ νv₁
      τ₁ p₀ p₁ hpD₀ hpk₀ hpV₀ hpF₀ hpD₁ hpk₁ hpV₁ hpF₁ hN hb Pb₀ Pb₁ Z M₀ Y S W' B M WN I c
      hM₀ hZ hbZ hK₀ hK₁ hkk₀ hkk₁ hY hSz hPb₀ hPb₁ hI0₀ hI0₁ hL₀ hL₁ hW' hWN hMd hc hctx hx
      hTm hHm hSm hLm hD₀ hD₁ hz hpos₀ hpos₁ hQRV₀ hQNT₀ hQNF₀ hQIS₀ hQLN₀ hQG₀ hQRV₁ hQNT₁
      hQNF₁ hQIS₁ hQLN₁ hQG₁ hI hZi e₀ hS₁ (rn_wb hd₀) hR₁ h9600
      (by rw [show e₀.nreg = fun r => d₀.nreg (rbSwap r) from funext hE]; exact pnInR_ren hin)
      hBN
  -- renamed back
  have ex' := rn_exec rbSwap ex
  have hback : rnC rbSwap e₀ = d₀ := by
    rw [he₀]; have := nb_rnC_back rbSwap d₀; rwa [hsy] at this
  rw [hback] at ex'
  have h990 : (rnC rbSwap d').nreg 990 = d'.nreg 990 := by
    show d'.nreg (rbSwap.symm 990) = _; rw [hsy, rb_low 990 (by omega)]
  obtain ⟨ok1, ok2, ok3⟩ := nodeFullR_ok
  refine ⟨Hc₀, Hc₁, g1, g2, g3, g4, rnC rbSwap d', t₀, t₁, t', o, ex', ht₀, ht₁, ht', hpot,
    fun bf hbf => ?_, fun r hr => exec_nreg_keep ex' ok1 ok2 ok3 r (by simp; omega), hout⟩
  rcases hstep bf hbf with ⟨h1, h2⟩ | ⟨f, h1, h2, h3⟩
  · exact Or.inl ⟨h1, by rw [h990]; exact h2⟩
  · exact Or.inr ⟨f, h1, by rw [h990]; exact h2, h3⟩

end NegSSSP

end PlanarFlow
