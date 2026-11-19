module

public import PlanarSeparator.Machine.MillerStep8

/-!
# Miller's separator on the machine: the tree marks from the parent darts

The cycle search of Lipton and Tarjan, which step 8 of `PlanarSeparator/Machine/Miller.lean`
reuses, reads the coded map in its own layout (`PlanarSeparator/Machine/Search.lean`): the
reversals `A x` at `x` (so the base of the reversals of the Miller programs is `bR = 0`), the tree
marks at `3 k + x`, the face weights at `6 k + F`, and it needs the marks of the faces at `7 k + F`
clear; it writes `[7 k, 11 k)`, so the arrays of the Miller programs lie above `11 k`.

The program `tmpass` clears the tree marks and the face marks and then marks, for every vertex
`v ≠ r₀`, its parent dart `Pr v` (at `bPr + v`) and the reversal `A (Pr v)`: within
`20 k + 13 n + 9` steps the tree marks are `tmark` (`tmpass_exec`). For a spanning tree `T` whose
parent darts are at `bPr` (as left by `bprog_tree` or `iprog_inner`), the marks are those of the
tree darts, and the coding is `CycleSearch.Coded` (`coded_of_tmark`).

Registers: `r0 … r10` (`CycleSearch.CRegs`), `r161 = n`, `r215 = bPr`, `r255 = r₀`; the program
writes `r370 … r373`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset CycleSearch

open Classical in
/-- The mark of the dart `x`: `1` if it is the parent dart of a vertex `v < i` other than `r₀` or
its reversal. -/
noncomputable def tmark (A Pr : ℕ → ℕ) (r₀ i x : ℕ) : ℕ :=
  if ∃ v < i, v ≠ r₀ ∧ (x = Pr v ∨ x = A (Pr v)) then 1 else 0

/-- Clear the tree mark of the dart `r370`. -/
def tclr : Stmt := block [.addN 371 5 370, .storeN 371 0, .addN 370 370 1]

/-- Clear the mark of the face `r370`. -/
def fclr : Stmt := block [.addN 371 7 370, .storeN 371 0, .addN 370 370 1]

/-- Mark the parent dart of `r370` and its reversal. -/
def tsetM : Stmt :=
  block [.addN 371 215 370, .loadN 372 371, .loadN 373 372, .addN 371 5 372, .storeN 371 1,
    .addN 371 5 373, .storeN 371 1]

/-- The vertex `r370`: marks unless it is the root. -/
def tset : Stmt :=
  .seq (.ifLtN 370 255 tsetM (.ifLtN 255 370 tsetM .skip)) (.instr (.addN 370 370 1))

/-- **The tree marks.** -/
def tmpass : Stmt :=
  .seq (.instr (.copyN 370 0)) <| .seq (.whileLtN 370 5 tclr) <| .seq (.instr (.copyN 370 0)) <|
  .seq (.whileLtN 370 4 fclr) <| .seq (.instr (.copyN 370 0)) (.whileLtN 370 161 tset)

section proofs

variable {W : ℕ} {P : Input} {k n r₀ bPr : ℕ} {A Pr : ℕ → ℕ}

theorem tmark_zero (x : ℕ) : tmark A Pr r₀ 0 x = 0 := by
  unfold tmark; rw [ite_eq_right_iff.2]; rintro ⟨v, hv, -⟩; omega

theorem tmark_succ (i x : ℕ) : tmark A Pr r₀ (i + 1) x =
    if i ≠ r₀ ∧ (x = Pr i ∨ x = A (Pr i)) then 1 else tmark A Pr r₀ i x := by
  classical
  unfold tmark
  by_cases h : i ≠ r₀ ∧ (x = Pr i ∨ x = A (Pr i))
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h), ite_eq_left_of_eq_true _ _ (eq_true ⟨i, by omega, h⟩)]
  · rw [ite_eq_right_iff.2 (fun h' => absurd h' h)]
    congr 1
    apply propext
    constructor
    · rintro ⟨v, hv, h'⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
      · exact ⟨v, hv, h'⟩
      · exact absurd h' h
    · rintro ⟨v, hv, h'⟩; exact ⟨v, by omega, h'⟩

theorem tmark_le (i x : ℕ) : tmark A Pr r₀ i x ≤ 1 := by unfold tmark; split_ifs <;> omega

/-- The configuration the pass reads. -/
structure TFix (k n r₀ bPr W : ℕ) (A Pr : ℕ → ℕ) (c : Config) : Prop where
  regs : CRegs k c
  r161 : c.nreg 161 = n
  r215 : c.nreg 215 = bPr
  r255 : c.nreg 255 = r₀
  mA : ∀ x < 3 * k, c.nmem x = A x
  A_lt : ∀ x < 3 * k, A x < 3 * k
  mP : ∀ v < n, v ≠ r₀ → c.nmem (bPr + v) = Pr v
  P_lt : ∀ v < n, v ≠ r₀ → Pr v < 3 * k
  lP : 8 * k ≤ bPr
  hW : bPr + n ≤ W
  hk : 8 * k ≤ W

/-- The cells written. -/
def TOut (k a : ℕ) : Prop := (3 * k ≤ a ∧ a < 6 * k) ∨ (7 * k ≤ a ∧ a < 8 * k)

variable {c₀ : Config} (hF : TFix k n r₀ bPr W A Pr c₀)
include hF

/-- A clearing loop over `[b, b + N)` with base register `rb` and bound register `rN`. -/
theorem clr_exec {rb rN b N : ℕ} (hrb : rb ≤ 10) (hrN : rN ≤ 10) (hb : c₀.nreg rb = b)
    (hN : c₀.nreg rN = N) (hbN : b + N ≤ W) (_hout : ∀ a, b ≤ a → a < b + N → TOut k a)
    (c : Config) (hc : WordsBounded W c) (hr : ∀ r, r ≠ 370 → r ≠ 371 → c.nreg r = c₀.nreg r)
    (h370 : c.nreg 370 = 0) (body : Stmt)
    (hbody : body = block [.addN 371 rb 370, .storeN 371 0, .addN 370 370 1]) :
    ∃ c' t, Exec P W (.whileLtN 370 rN body) c c' t ∧ t ≤ 5 * N + 2 ∧
      (∀ r, r ≠ 370 → r ≠ 371 → c'.nreg r = c₀.nreg r) ∧
      (∀ a, b ≤ a → a < b + N → c'.nmem a = 0) ∧
      (∀ a, ¬ (b ≤ a ∧ a < b + N) → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨h0, h1, -⟩ := hF.regs
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 370 = i ∧
    c'.nreg rN = N ∧ i ≤ N ∧ (∀ r, r ≠ 370 → r ≠ 371 → c'.nreg r = c₀.nreg r) ∧
    (∀ a, b ≤ a → a < b + i → c'.nmem a = 0) ∧
    (∀ a, ¬ (b ≤ a ∧ a < b + i) → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 370) (rN := rN) (N := N)
    (lo := 0) (B := 3) (body := body) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw, h370', hN', hi, hr', hz, hm', ho⟩ hlt => by
      have hc := hw
      have g0 := (hr' 0 (by omega) (by omega)).trans h0
      have g1 := (hr' 1 (by omega) (by omega)).trans h1
      have gb := (hr' rb (by omega) (by omega)).trans hb
      subst hbody
      exec_block
      all_goals try (config_simp; simp only [gb, h370', g1]; omega)
      refine ⟨⟨‹_›, ?_, ?_, by omega, fun r a b' => ?_, fun a ha1 ha2 => ?_, fun a ha => ?_, ho⟩,
        le_rfl⟩
      all_goals config_simp
      · rw [h370', g1]
      · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hN'
      · simp only [upd_apply]; split_ifs <;> first | omega | exact hr' r a b'
      · simp only [gb, h370', g0]
        by_cases e : a = b + i
        · rw [e, upd_same]
        · rw [upd_other _ _ _ e]; exact hz a ha1 (by omega)
      · simp only [gb, h370', g0]
        rw [upd_other _ _ _ (by omega)]; exact hm' a (by omega))
    (by omega) ⟨hc, h370, by rw [hr rN (by omega) (by omega)]; exact hN, by omega, hr,
      fun a h1 h2 => absurd h2 (by omega), fun a _ => rfl, rfl⟩
  exact ⟨c', t, e, by omega, hI.2.2.2.2.1, hI.2.2.2.2.2.1, hI.2.2.2.2.2.2.1, hI.2.2.2.2.2.2.2⟩

set_option maxHeartbeats 2000000 in
/-- **The tree marks.** Within `20 k + 13 n + 9` steps the tree marks at `3 k + x` are
`tmark A Pr r₀ n x` and the face marks at `7 k + F` are clear; the rest of the memory is kept. -/
theorem tmpass_exec (hc₀ : WordsBounded W c₀) :
    ∃ c' t, Exec P W tmpass c₀ c' t ∧ t ≤ 20 * k + 13 * n + 9 ∧
      (∀ x < 3 * k, c'.nmem (3 * k + x) = tmark A Pr r₀ n x) ∧
      (∀ f < k, mark k c'.nmem f = 0) ∧ (∀ a, ¬ TOut k a → c'.nmem a = c₀.nmem a) ∧
      (∀ r, r ≠ 370 → r ≠ 371 → r ≠ 372 → r ≠ 373 → c'.nreg r = c₀.nreg r) ∧
      c'.output = c₀.output := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hF.regs
  have hk := hF.hk
  -- clear the tree marks
  have e₁ := Exec.copyN (P := P) hc₀ 370 0
  obtain ⟨c₂, t₂, e₂, ht₂, hr₂, hz₂, hm₂, ho₂⟩ := clr_exec (P := P) hF (rb := 5) (rN := 5)
    (b := 3 * k) (N := 3 * k) (by omega) (by omega) h5 h5 (by omega)
    (fun a h1 h2 => Or.inl ⟨h1, by omega⟩) _ e₁.wb_right
    (fun r a _ => by config_simp; rw [upd_other _ _ _ a]) (by config_simp; exact h0) tclr rfl
  have hw₂ := e₂.wb_right
  -- clear the face marks
  have e₃ := Exec.copyN (P := P) hw₂ 370 0
  obtain ⟨c₄, t₄, e₄, ht₄, hr₄, hz₄, hm₄, ho₄⟩ := clr_exec (P := P) hF (rb := 7) (rN := 4)
    (b := 7 * k) (N := k) (by omega) (by omega) h7 h4 (by omega)
    (fun a h1 h2 => Or.inr ⟨h1, by omega⟩) _ e₃.wb_right
    (fun r a b => by config_simp; rw [upd_other _ _ _ a]; exact hr₂ r a b)
    (by config_simp; rw [hr₂ 0 (by omega) (by omega)]; exact h0) fclr rfl
  have hw₄ := e₄.wb_right
  -- the marks
  have e₅ := Exec.copyN (P := P) hw₄ 370 0
  have hm4 : ∀ a, c₄.nmem a = if 3 * k ≤ a ∧ a < 6 * k then 0 else
      if 7 * k ≤ a ∧ a < 8 * k then 0 else c₀.nmem a := fun a => by
    split_ifs with h h'
    · rw [hm₄ a (by omega)]; exact hz₂ a h.1 (by omega)
    · exact hz₄ a h'.1 (by omega)
    · rw [hm₄ a (by omega), hm₂ a (by omega)]
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 370 = i ∧
    c'.nreg 161 = n ∧ i ≤ n ∧
    (∀ r, r ≠ 370 → r ≠ 371 → r ≠ 372 → r ≠ 373 → c'.nreg r = c₀.nreg r) ∧
    (∀ x < 3 * k, c'.nmem (3 * k + x) = tmark A Pr r₀ i x) ∧
    (∀ a, ¬ (3 * k ≤ a ∧ a < 6 * k) → c'.nmem a = c₄.nmem a) ∧ c'.output = c₀.output
  have hI₅ : I 0 { c₄ with nreg := upd c₄.nreg 370 (c₄.nreg 0) } := by
    refine ⟨e₅.wb_right, ?_, ?_, by omega, fun r a b _ _ => ?_, fun x hx => ?_, fun a _ => rfl, ?_⟩
    all_goals config_simp
    · rw [hr₄ 0 (by omega) (by omega)]; exact h0
    · rw [hr₄ 161 (by omega) (by omega)]; exact hF.r161
    · rw [upd_other _ _ _ a, hr₄ r a b]
    · rw [tmark_zero, hm4]; simp only [show 3 * k ≤ 3 * k + x ∧ 3 * k + x < 6 * k from
        ⟨by omega, by omega⟩, and_self, ↓reduceIte]
    · rw [ho₄]; config_simp; rw [ho₂]
  obtain ⟨c', t, e, hI', ht⟩ := Exec.forN (P := P) (W := W) (ri := 370) (rN := 161) (N := n)
    (lo := 0) (B := 11) (body := tset) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw, h370, h161, hi, hr', hT', hm', ho⟩ hlt => by
      have hc := hw
      have g1 := (hr' 1 (by omega) (by omega) (by omega) (by omega)).trans h1
      have g5 := (hr' 5 (by omega) (by omega) (by omega) (by omega)).trans h5
      have g215 := (hr' 215 (by omega) (by omega) (by omega) (by omega)).trans hF.r215
      have g255 := (hr' 255 (by omega) (by omega) (by omega) (by omega)).trans hF.r255
      have hlP := hF.lP
      have hWP := hF.hW
      -- the step after the marks (or none)
      have fin : ∀ c₂ : Config, WordsBounded W c₂ →
          (∀ r, r ≠ 371 → r ≠ 372 → r ≠ 373 → c₂.nreg r = c₁.nreg r) →
          (∀ x < 3 * k, c₂.nmem (3 * k + x) = tmark A Pr r₀ (i + 1) x) →
          (∀ a, ¬ (3 * k ≤ a ∧ a < 6 * k) → c₂.nmem a = c₁.nmem a) → c₂.output = c₁.output →
          ∃ c' t', Exec P W (.instr (.addN 370 370 1)) c₂ c' t' ∧ I (i + 1) c' ∧ t' = 1 := by
        intro c₂ hw₂ hr₂ hT₂ hm₂ ho₂
        have k370 := (hr₂ 370 (by omega) (by omega) (by omega)).trans h370
        have k1 := (hr₂ 1 (by omega) (by omega) (by omega)).trans g1
        refine ⟨_, 1, Exec.addN hw₂ 370 370 1 (by rw [k370, k1]; omega), ⟨(Exec.addN (P := P) hw₂ 370
          370 1 (by rw [k370, k1]; omega)).wb_right, ?_, ?_, by omega, fun r a b c d => ?_, hT₂,
          fun a ha => ?_, ?_⟩, rfl⟩
        all_goals config_simp
        · rw [k370, k1]
        · rw [hr₂ 161 (by omega) (by omega) (by omega)]; exact h161
        · rw [upd_other _ _ _ a, hr₂ r b c d]; exact hr' r a b c d
        · rw [hm₂ a ha]; exact hm' a ha
        · rw [ho₂]; exact ho
      have hTm : ∀ x < 3 * k, i = r₀ → tmark A Pr r₀ (i + 1) x = tmark A Pr r₀ i x := fun x _ he => by
        rw [tmark_succ, ite_eq_right_iff.2 (fun h => absurd he h.1)]
      have hgen : i ≠ r₀ → ∃ c₂ t₂, Exec P W tsetM c₁ c₂ t₂ ∧ t₂ = 7 ∧ WordsBounded W c₂ ∧
          (∀ r, r ≠ 371 → r ≠ 372 → r ≠ 373 → c₂.nreg r = c₁.nreg r) ∧
          (∀ x < 3 * k, c₂.nmem (3 * k + x) = tmark A Pr r₀ (i + 1) x) ∧
          (∀ a, ¬ (3 * k ≤ a ∧ a < 6 * k) → c₂.nmem a = c₁.nmem a) ∧ c₂.output = c₁.output := by
        intro hne
        have hPl := hF.P_lt i hlt hne
        have hAl := hF.A_lt _ hPl
        have mP : c₁.nmem (bPr + i) = Pr i := by
          rw [hm' _ (by omega), hm4]
          simp only [show ¬ (3 * k ≤ bPr + i ∧ bPr + i < 6 * k) by omega,
            show ¬ (7 * k ≤ bPr + i ∧ bPr + i < 8 * k) by omega, ↓reduceIte]
          exact hF.mP i hlt hne
        have mA : ∀ c₂ : Config, (∀ a, ¬ (3 * k ≤ a ∧ a < 6 * k) → c₂.nmem a = c₁.nmem a) →
            c₂.nmem (Pr i) = A (Pr i) := fun c₂ h => by
          rw [h _ (by omega), hm' _ (by omega), hm4]
          simp only [show ¬ (3 * k ≤ Pr i ∧ Pr i < 6 * k) by omega,
            show ¬ (7 * k ≤ Pr i ∧ Pr i < 8 * k) by omega, ↓reduceIte]
          exact hF.mA _ hPl
        have mA₁ := mA c₁ (fun _ _ => rfl)
        unfold tsetM
        exec_block
        all_goals try (config_simp; simp only [g215, h370, mP, g5, mA₁]; omega)
        refine ⟨rfl, ‹_›, fun r a b c' => ?_, fun x hx => ?_, fun a ha => ?_, rfl⟩
        all_goals config_simp
        · simp only [upd_apply]; split_ifs <;> first | omega | rfl
        · simp only [g215, h370, mP, g5, mA₁, g1]
          rw [tmark_succ, ← hT' x hx]
          by_cases e1 : x = Pr i
          · subst e1
            rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hne, Or.inl rfl⟩)]
            simp only [upd_apply]; split_ifs <;> first | rfl | omega
          · by_cases e2 : x = A (Pr i)
            · subst e2
              rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hne, Or.inr rfl⟩)]
              simp only [upd_apply]; split_ifs <;> first | rfl | omega
            · simp [upd_apply, e1, e2]
        · simp only [g215, h370, mP, g5, mA₁]
          rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
      unfold tset
      refine spec_seq ?_
      rcases Nat.lt_trichotomy i r₀ with hlt' | heq | hgt
      · refine spec_ifLtN_true (by rw [h370, g255]; exact hlt') ?_
        obtain ⟨c₂, t₂, e₂', rfl, hw₂', hr₂, hT₂, hm₂, ho₂⟩ := hgen (by omega)
        obtain ⟨c', t', e', hI', rfl⟩ := fin c₂ hw₂' hr₂ hT₂ hm₂ ho₂
        exact ⟨c₂, 7, e₂', c', 1, e', hI', by omega⟩
      · refine spec_ifLtN_false (by rw [h370, g255]; omega) ?_
        refine spec_ifLtN_false (by rw [h370, g255]; omega) ?_
        refine spec_skip hw ?_
        obtain ⟨c', t', e', hI', rfl⟩ := fin c₁ hw (fun _ _ _ _ => rfl)
          (fun x hx => by rw [hTm x hx heq]; exact hT' x hx) (fun _ _ => rfl) rfl
        exact ⟨c', 1, e', hI', by omega⟩
      · refine spec_ifLtN_false (by rw [h370, g255]; omega) ?_
        refine spec_ifLtN_true (by rw [h370, g255]; exact hgt) ?_
        obtain ⟨c₂, t₂, e₂', rfl, hw₂', hr₂, hT₂, hm₂, ho₂⟩ := hgen (by omega)
        obtain ⟨c', t', e', hI', rfl⟩ := fin c₂ hw₂' hr₂ hT₂ hm₂ ho₂
        exact ⟨c₂, 7, e₂', c', 1, e', hI', by omega⟩)
    (by omega) hI₅
  obtain ⟨-, -, -, -, hr', hT', hm', ho'⟩ := hI'
  refine ⟨c', 1 + (t₂ + (1 + (t₄ + (1 + t)))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e)))),
    by omega, hT', fun f hf => ?_, fun a ha => ?_, fun r a b c d => ?_, ho'⟩
  · unfold mark
    rw [hm' _ (by omega), hm4]
    split_ifs <;> first | rfl | omega
  · unfold TOut at ha
    rw [hm' a (by omega), hm4]
    split_ifs <;> first | rfl | omega
  · exact hr' r a b c d

end proofs

/-! ### The bridge -/

section Bridge

open Map

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}
  {T : M.SpTree} {k n : ℕ} {cd : D ≃ Fin (3 * k)} {vi : Q ≃ Fin n} {A Pr : ℕ → ℕ}

omit [Fintype D] [Fintype Q] in
/-- **The marks of `tmpass` are the marks of the tree darts**: with the parent darts of `T` (other
than the root) at `bPr`, the coding with the marks `tmark` is `CycleSearch.Coded`. -/
theorem coded_of_tmark (hAcd : ∀ x, A (cd x) = cd (M.α x))
    (hφ : ∀ x, (cd (M.φ x) : ℕ) = phi3 (cd x))
    (hPr : ∀ v (h : v ≠ T.root), Pr (vi v) = cd (T.par v h)) :
    Coded M T k cd A (tmark A Pr (vi T.root) n) := by
  have key : ∀ x, tmark A Pr (vi T.root) n (cd x) = 1 ↔ T.IsTree x := fun x => by
    classical
    unfold tmark
    constructor
    · intro h
      by_contra hn
      rw [ite_eq_right_iff.2] at h
      · omega
      · rintro ⟨u, hu, hr, h'⟩
        obtain ⟨v, rfl⟩ := exists_vi vi hu
        have hv : v ≠ T.root := fun e => hr (by rw [e])
        rw [hPr v hv, hAcd] at h'
        rcases h' with h' | h'
        · exact (hn ⟨v, hv, Or.inl (cd.injective (Fin.ext h'))⟩).elim
        · exact (hn ⟨v, hv, Or.inr (cd.injective (Fin.ext h'))⟩).elim
    · rintro ⟨v, hv, h' | h'⟩
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨vi v, (vi v).2,
          fun e => hv (vi.injective (Fin.ext e)), Or.inl (by rw [hPr v hv, h'])⟩)]
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨vi v, (vi v).2,
          fun e => hv (vi.injective (Fin.ext e)), Or.inr (by rw [hPr v hv, hAcd, h'])⟩)]
  refine ⟨hAcd, hφ, fun x => ?_, fun x => tmark_le _ _⟩
  have h1 := tmark_le (A := A) (Pr := Pr) (r₀ := vi T.root) n (cd x)
  rw [← key x]
  omega

end Bridge

end MillerProg

end PlanarSeparator
