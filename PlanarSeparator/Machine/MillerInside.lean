module

public import PlanarSeparator.Machine.MillerFcyc
public import PlanarSeparator.Machine.Bridge

/-!
# Miller's separator on the machine: the inside marks of a fundamental cycle

For the output `Z` of steps 9 and 10 (`PlanarSeparator.Map.bandSep`: the inside of the dart `δ`
in `T₁`, or of the last dart of an arc in the redirected tree, or its complement), the faces
inside a dart `a` off a tree `T`, after the search of the dual tree of
`PlanarSeparator/Machine/Search.lean` for `T` (the state `SB`, as step 8 leaves it for `T₁`; for
a redirected tree the search is rerun on its tree marks). As `PlanarSeparator.SepProg.inLoop`,
but with the registers `r530 …` and the search arrays of the Miller layout (order of the search
at `9 k + i`, darts `pd` at `8 k + f`, reversals at `bA + x`):

* `fsel`: the face `F` of the search whose dart `pd F` is `a` or `α a` (`r532`), and the flag
  (`r539`: `0` if `pd F = a`, `1` otherwise) (`fsel_exec`, `16` steps);
* `imLoop`: the marks `im` at `bIm`: `0` at the root face `0`, `1` at `F`, and the mark of the
  parent elsewhere, in the order of the search (`imLoop_exec`, within `21 k + 5` steps).

**`imLoop_inside`**: through the coding, a face `G` lies in `T.inside a` if and only if its mark
differs from the flag (from `PlanarSeparator.SepProg.inside_marks`).

Registers: inputs `r530 = k`, `r531 = bIm`, `r533 = 1`, `r534 = 0`, `r535 = 3`, `r536 = 9 k`,
`r537 = 8 k`, `r538 = bA`, `r547 = a` (`IR`); written: `r532`, `r539`, `r540 … r546`, `r548`,
`r549`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-- The alternative of `fsel`: the face of `α a`, flag `1`. -/
def fselAlt : List Instr := [.addN 541 538 547, .loadN 549 541, .divN 532 549 535, .copyN 539 533]

/-- **The face of the search for the dart `a`** (`r532`) and the flag (`r539`). -/
def fsel : Stmt :=
  .seq (block [.divN 532 547 535, .addN 541 537 532, .loadN 549 541, .subN 546 549 547,
      .subN 541 547 549, .addN 546 546 541, .copyN 539 534])
    (.ifLtN 534 532 (.ifLtN 546 533 .skip (block fselAlt)) (block fselAlt))

/-- **The face `r540`-th in the search**: its mark is `1` if it is `F = r532`, the mark of its
parent otherwise. -/
def imBody : Stmt :=
  .seq (block [.addN 541 536 540, .loadN 542 541, .addN 541 537 542, .loadN 543 541,
      .addN 541 538 543, .loadN 544 541, .divN 544 544 535, .addN 541 531 544, .loadN 545 541,
      .subN 546 542 532, .subN 541 532 542, .addN 546 546 541])
    (.seq (.ifLtN 546 533 (.instr (.copyN 545 533)) .skip)
      (block [.addN 541 531 542, .storeN 541 545, .addN 540 540 533]))

/-- **The marks of the subtree of `F`.** -/
def imLoop : Stmt :=
  .seq (block [.addN 541 531 534, .storeN 541 534, .copyN 540 533]) (.whileLtN 540 530 imBody)

/-- The input registers of `fsel` and `imLoop`. -/
structure IR (k bIm bA a : ℕ) (c : Config) : Prop where
  r530 : c.nreg 530 = k
  r531 : c.nreg 531 = bIm
  r533 : c.nreg 533 = 1
  r534 : c.nreg 534 = 0
  r535 : c.nreg 535 = 3
  r536 : c.nreg 536 = 9 * k
  r537 : c.nreg 537 = 8 * k
  r538 : c.nreg 538 = bA
  r547 : c.nreg 547 = a

theorem IR.of {k bIm bA a : ℕ} {c c' : Config} (h : IR k bIm bA a c)
    (e : ∀ r, r ≠ 532 → r ≠ 539 → (r < 540 ∨ 550 ≤ r ∨ r = 547) → c'.nreg r = c.nreg r) :
    IR k bIm bA a c' :=
  ⟨(e 530 (by omega) (by omega) (by omega)).trans h.r530,
    (e 531 (by omega) (by omega) (by omega)).trans h.r531,
    (e 533 (by omega) (by omega) (by omega)).trans h.r533,
    (e 534 (by omega) (by omega) (by omega)).trans h.r534,
    (e 535 (by omega) (by omega) (by omega)).trans h.r535,
    (e 536 (by omega) (by omega) (by omega)).trans h.r536,
    (e 537 (by omega) (by omega) (by omega)).trans h.r537,
    (e 538 (by omega) (by omega) (by omega)).trans h.r538,
    (e 547 (by omega) (by omega) (by omega)).trans h.r547⟩

/-- The face of the search for the dart `a`: `a / 3` if `pd (a / 3) = a`, `A a / 3` otherwise. -/
def fselF (pdF A : ℕ → ℕ) (a : ℕ) : ℕ := if 0 < a / 3 ∧ pdF (a / 3) = a then a / 3 else A a / 3

/-- The flag: `0` if `pd (a / 3) = a`, `1` otherwise. -/
def fselB (pdF : ℕ → ℕ) (a : ℕ) : ℕ := if 0 < a / 3 ∧ pdF (a / 3) = a then 0 else 1

section proofs

variable {k : ℕ} {W : ℕ} {P : Input} {bIm bA a : ℕ}

set_option maxHeartbeats 2000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The face and the flag of a dart.** -/
theorem fsel_exec {pdF AF : ℕ → ℕ} (hW : 9 * k ≤ W ∧ bA + 3 * k ≤ W) (c : Config)
    (hc : WordsBounded W c) (hI : IR k bIm bA a c) (ha : a < 3 * k)
    (hpm : ∀ G < k, c.nmem (8 * k + G) = pdF G) (hAm : ∀ x < 3 * k, c.nmem (bA + x) = AF x) :
    ∃ c' t, Exec P W fsel c c' t ∧ t ≤ 16 ∧ c'.nreg 532 = fselF pdF AF a ∧
      c'.nreg 539 = fselB pdF a ∧
      (∀ r, r ≠ 532 → r ≠ 539 → (r < 540 ∨ 550 ≤ r ∨ r = 547) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.output = c.output := by
  obtain ⟨r530, r531, r533, r534, r535, r536, r537, r538, r547⟩ := hI
  have m1 : c.nmem (8 * k + a / 3) = pdF (a / 3) := hpm _ (by omega)
  have m2 : c.nmem (bA + a) = AF a := hAm _ ha
  have hb1 := hc.2 (8 * k + a / 3)
  have hb2 := hc.1 547
  rw [m1] at hb1
  rw [r547] at hb2
  unfold fsel
  refine spec_seq ?_
  exec_block
  all_goals try (config_simp; (try simp only [r547, r535, r537, m1]); omega)
  rename_i hwa
  simp only [r547, r535, r537, m1, r534] at hwa ⊢
  have hfin : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 547 = a → c₂.nreg 538 = bA →
      c₂.nreg 533 = 1 → c₂.nreg 535 = 3 → c₂.nmem = c.nmem →
      ¬ (0 < a / 3 ∧ pdF (a / 3) = a) →
      (∀ r, r ≠ 532 → r ≠ 539 → (r < 540 ∨ 550 ≤ r ∨ r = 547) → c₂.nreg r = c.nreg r) →
      c₂.output = c.output →
      ∃ c' t, Exec P W (block fselAlt) c₂ c' t ∧ t ≤ 4 ∧ c'.nreg 532 = fselF pdF AF a ∧
        c'.nreg 539 = fselB pdF a ∧
        (∀ r, r ≠ 532 → r ≠ 539 → (r < 540 ∨ 550 ≤ r ∨ r = 547) → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.output = c.output := by
    intro c₂ hw₂ f547 f538 f533 f535 fm hnp fr fo
    have m2' : c₂.nmem (bA + a) = AF a := by rw [fm]; exact m2
    unfold fselAlt
    exec_block
    all_goals try (config_simp; (try simp only [f538, f547, m2', f535, f533]); omega)
    rename_i hwb
    simp only [f538, f547, m2', f535, f533] at hwb ⊢
    refine ⟨by omega, by config_simp; unfold fselF; rw [ite_eq_right_of_eq_false _ _ (eq_false hnp)],
      by config_simp; unfold fselB; rw [ite_eq_right_of_eq_false _ _ (eq_false hnp)],
      fun r h1 h2 h3 => ?_, by config_simp; exact fm, by config_simp; exact fo⟩
    config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact fr r h1 h2 h3
  have fr0 : ∀ r, r ≠ 532 → r ≠ 539 → (r < 540 ∨ 550 ≤ r ∨ r = 547) →
      ({ c with nreg := upd (upd (upd (upd (upd (upd (upd c.nreg 532 (a / 3)) 541 (8 * k + a / 3))
        549 (pdF (a / 3))) 546 (pdF (a / 3) - a)) 541 (a - pdF (a / 3))) 546
        (pdF (a / 3) - a + (a - pdF (a / 3)))) 539 0 } : Config).nreg r = c.nreg r := by
    intro r h1 h2 h3
    simp only [upd_apply]; split_ifs <;> omega
  by_cases hpos : 0 < a / 3
  · refine spec_ifLtN_true (by config_simp; omega) ?_
    by_cases heq : pdF (a / 3) = a
    · refine spec_ifLtN_true (by config_simp; omega) ?_
      refine spec_skip hwa ⟨by omega, ?_, ?_, fun r h1 h2 h3 => fr0 r h1 h2 h3, rfl, rfl⟩
      · config_simp; unfold fselF; rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hpos, heq⟩)]
      · config_simp; unfold fselB; rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨hpos, heq⟩)]
    · refine spec_ifLtN_false (by config_simp; omega) ?_
      obtain ⟨c', t, e, ht, h1, h2, h3, h4, h5⟩ := hfin _ hwa (by config_simp <;> exact r547)
        (by config_simp <;> exact r538) (by config_simp <;> exact r533)
        (by config_simp <;> exact r535) rfl (fun h => heq h.2)
        (fun r h1 h2 h3 => fr0 r h1 h2 h3) rfl
      exact ⟨c', t, e, by omega, h1, h2, h3, h4, h5⟩
  · refine spec_ifLtN_false (by config_simp; omega) ?_
    obtain ⟨c', t, e, ht, h1, h2, h3, h4, h5⟩ := hfin _ hwa (by config_simp <;> exact r547)
      (by config_simp <;> exact r538) (by config_simp <;> exact r533)
      (by config_simp <;> exact r535) rfl (fun h => hpos h.1)
      (fun r h1 h2 h3 => fr0 r h1 h2 h3) rfl
    exact ⟨c', t, e, by omega, h1, h2, h3, h4, h5⟩

set_option maxHeartbeats 4000000 in
set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **The marks of the subtree of `F = r532`**, in the order `quF` of the search (every face once,
the face `0` first, the parent `AF (pdF G) / 3` of every other face before it). -/
theorem imLoop_exec (hk1 : 1 ≤ k) (hlay : bA + 3 * k ≤ bIm ∧ 10 * k ≤ bIm) (hW : bIm + k ≤ W)
    (quF pdF AF : ℕ → ℕ) (F : ℕ)
    (hq : ∀ i < k, quF i < k) (hqi : ∀ i < k, ∀ j < k, quF i = quF j → i = j)
    (hq0 : quF 0 = 0) (hall : ∀ G < k, ∃ i < k, quF i = G)
    (hpar : ∀ i, 1 ≤ i → i < k → pdF (quF i) < 3 * k ∧ AF (pdF (quF i)) < 3 * k ∧
      ∃ i' < i, quF i' = AF (pdF (quF i)) / 3)
    (c : Config) (hc : WordsBounded W c) (hI : IR k bIm bA a c) (h532 : c.nreg 532 = F)
    (hqm : ∀ i < k, c.nmem (9 * k + i) = quF i) (hpm : ∀ G < k, c.nmem (8 * k + G) = pdF G)
    (hAm : ∀ x < 3 * k, c.nmem (bA + x) = AF x) :
    ∃ c' t, Exec P W imLoop c c' t ∧ t ≤ 21 * k + 5 ∧ c'.nmem bIm = 0 ∧
      (∀ G < k, G ≠ 0 → c'.nmem (bIm + G) =
        if G = F then 1 else c'.nmem (bIm + AF (pdF G) / 3)) ∧
      (∀ a, ¬ (bIm ≤ a ∧ a < bIm + k) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 540 ∨ 547 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output := by
  classical
  obtain ⟨r530, r531, r533, r534, r535, r536, r537, r538, r547⟩ := hI
  have hqne : ∀ i, 1 ≤ i → i < k → quF i ≠ 0 := fun i h1 h2 e =>
    absurd (hqi i h2 0 hk1 (by rw [e, hq0])) (by omega)
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 540 = i ∧
    c'.nreg 530 = k ∧ 1 ≤ i ∧ c'.nmem bIm = 0 ∧
    (∀ i' < i, 1 ≤ i' → c'.nmem (bIm + quF i') =
      if quF i' = F then 1 else c'.nmem (bIm + AF (pdF (quF i')) / 3)) ∧
    (∀ a, ¬ (bIm ≤ a ∧ a < bIm + k) → c'.nmem a = c.nmem a) ∧
    (∀ r, r < 540 ∨ 547 ≤ r → c'.nreg r = c.nreg r) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.addN 541 531 534, .storeN 541 534,
      .copyN 540 533]) c c₁ k₁ ∧ I 1 c₁ ∧ k₁ = 3 := by
    exec_block
    · rw [r531, r534]; omega
    refine ⟨⟨‹_›, by config_simp; exact r533, by config_simp; exact r530, le_rfl,
      by config_simp; rw [r531, r534, Nat.add_zero, upd_same],
      fun i' h1 h2 => absurd h2 (by omega),
      fun a ha => by config_simp; rw [r531, r534, Nat.add_zero, upd_other _ _ _ (by omega)],
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl⟩, rfl⟩
  obtain ⟨c₂, t, e, hI', ht⟩ := Exec.forN (P := P) (W := W) (ri := 540) (rN := 530)
    (N := k) (lo := 1) (B := 17) (body := imBody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h540, h530, hi1, h0, hI1, hf, hr, ho⟩ hi => by
      have g : ∀ r, r < 540 → c₁.nreg r = c.nreg r := fun r hr' => hr r (Or.inl hr')
      have g531 : c₁.nreg 531 = bIm := by rw [g 531 (by omega)]; exact r531
      have g532 : c₁.nreg 532 = F := by rw [g 532 (by omega)]; exact h532
      have g533 : c₁.nreg 533 = 1 := by rw [g 533 (by omega)]; exact r533
      have g535 : c₁.nreg 535 = 3 := by rw [g 535 (by omega)]; exact r535
      have g536 : c₁.nreg 536 = 9 * k := by rw [g 536 (by omega)]; exact r536
      have g537 : c₁.nreg 537 = 8 * k := by rw [g 537 (by omega)]; exact r537
      have g538 : c₁.nreg 538 = bA := by rw [g 538 (by omega)]; exact r538
      obtain ⟨hpd, hA, i'', hi'', hpar'⟩ := hpar i hi1 hi
      have hparne : ∀ j, 1 ≤ j → j < i → AF (pdF (quF j)) / 3 ≠ quF i := by
        intro j hj1 hj2 e'
        obtain ⟨-, -, j', hj', hpj⟩ := hpar j hj1 (by omega)
        rw [← hpj] at e'
        have := hqi j' (by omega) i hi e'
        omega
      obtain ⟨G, hG⟩ : ∃ G, G = quF i := ⟨_, rfl⟩
      rw [← hG] at hpd hA hpar' hparne
      have hGk : G < k := hG ▸ hq i hi
      have hG0 : G ≠ 0 := hG ▸ hqne i hi1 hi
      obtain ⟨Pf, hPf⟩ : ∃ Pf, Pf = AF (pdF G) / 3 := ⟨_, rfl⟩
      rw [← hPf] at hpar'
      have hPk : Pf < k := by omega
      have m1 : c₁.nmem (9 * k + i) = G := by rw [hf _ (by omega), hG]; exact hqm i hi
      have m2 : c₁.nmem (8 * k + G) = pdF G := by rw [hf _ (by omega)]; exact hpm G hGk
      have m3 : c₁.nmem (bA + pdF G) = AF (pdF G) := by rw [hf _ (by omega)]; exact hAm _ hpd
      have hPG : Pf ≠ G := fun e' => by
        have := hqi i'' (by omega) i hi (hpar'.trans (e'.trans hG)); omega
      have hfin : ∀ c₃ : Config, WordsBounded W c₃ →
          c₃.nreg 545 = (if G = F then 1 else c₁.nmem (bIm + Pf)) → c₃.nreg 542 = G →
          c₃.nreg 540 = i → (∀ r, r < 540 ∨ 547 ≤ r → c₃.nreg r = c₁.nreg r) →
          c₃.nmem = c₁.nmem → c₃.output = c₁.output →
          ∃ c' k, Exec P W (block [.addN 541 531 542, .storeN 541 545, .addN 540 540 533]) c₃ c'
            k ∧ I (i + 1) c' ∧ k ≤ 3 := by
        intro c₃ hw₃ f545 f542 f540 fr fm fo
        have f531 : c₃.nreg 531 = bIm := (fr 531 (by omega)).trans g531
        have f533 : c₃.nreg 533 = 1 := (fr 533 (by omega)).trans g533
        have f530 : c₃.nreg 530 = k := (fr 530 (by omega)).trans h530
        exec_block
        all_goals try (config_simp; (try simp only [f531, f542, f540, f533]); omega)
        rename_i hwb
        simp only [f531, f542, f540, f533, f545] at hwb ⊢
        refine ⟨⟨hwb, by config_simp, by config_simp; exact f530, by omega, ?_, fun i' hi' h1 => ?_,
          fun a ha => ?_, fun r hr' => ?_, by config_simp; rw [fo, ho]⟩, by omega⟩
        · config_simp; rw [upd_other _ _ _ (by omega), fm]; exact h0
        · config_simp
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
          · have hne : quF i' ≠ G := fun e' => by have := hqi i' (by omega) i hi (e'.trans hG); omega
            have e1 : bIm + quF i' ≠ bIm + G := by omega
            have e2 : bIm + AF (pdF (quF i')) / 3 ≠ bIm + G := fun e' =>
              hparne i' h1 hi' (Nat.add_left_cancel e')
            simp only [upd_apply, e1, e2, Ne.symm e1, Ne.symm e2, ↓reduceIte, fm]
            exact hI1 i' hi' h1
          · rw [← hG, upd_same, ← hPf, upd_other _ _ _ (by omega), fm]
        · config_simp; rw [upd_other _ _ _ (by omega), fm]; exact hf a ha
        · config_simp; simp only [upd_apply]
          split_ifs <;> first | omega | (rw [fr r hr']; exact hr r hr')
      have hb532 := hw₁.1 532
      rw [g532] at hb532
      unfold imBody
      refine spec_seq ?_
      exec_block
      all_goals try (config_simp; (try simp only [g536, h540, m1, g537, m2, g538, m3, g535, g531, g532]); omega)
      rename_i hwa
      simp only [g536, h540, m1, g537, m2, g538, m3, g535, g531, g532] at hwa ⊢
      refine spec_seq ?_
      by_cases hGF : G = F
      · refine spec_ifLtN_true (by config_simp; rw [g533]; omega) ?_
        refine spec_instr (Exec.copyN hwa 545 533) fun hw₃ => ?_
        obtain ⟨c', k', e', hI'', hk'⟩ := hfin _ hw₃
          (by config_simp; rw [g533, ite_eq_left_of_eq_true _ _ (eq_true hGF)])
          (by config_simp) (by config_simp <;> exact h540)
          (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
          (by config_simp) (by config_simp)
        exact ⟨c', k', e', hI'', by omega⟩
      · refine spec_ifLtN_false (by config_simp; rw [g533]; omega) ?_
        refine spec_skip hwa ?_
        obtain ⟨c', k', e', hI'', hk'⟩ := hfin _ hwa
          (by config_simp; rw [ite_eq_right_of_eq_false _ _ (eq_false hGF), hPf])
          (by config_simp) (by config_simp <;> exact h540)
          (fun r hr' => by config_simp; simp only [upd_apply]; split_ifs <;> omega)
          (by config_simp) (by config_simp)
        exact ⟨c', k', e', hI'', by omega⟩)
    hk1 hI₁
  obtain ⟨-, -, -, -, h0', hI1', hf', hr', ho'⟩ := hI'
  refine ⟨c₂, 3 + t, .seq e₁ e, by omega, h0', fun G hG hG0 => ?_, hf', hr', ho'⟩
  obtain ⟨i, hi, rfl⟩ := hall G hG
  have hi1 : 1 ≤ i := by
    by_contra h; obtain rfl : i = 0 := by omega
    exact hG0 hq0
  exact hI1' i hi hi1

end proofs

/-! ### Through the coding -/

section Bridge

open Map CycleSearch CycleSearch.Coded

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}
  {T : M.SpTree} {k : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm : ℕ → ℕ}

set_option maxHeartbeats 2000000 in
/-- **The inside of a dart off the tree, on the machine.** After the search of the dual tree of
`T` (the state `SB`, every face found), `fsel ; imLoop` marks the faces so that a face `G` lies in
`T.inside a` exactly when its mark at `bIm + fi cd G` differs from the flag in `r539`, within
`21 k + 21` steps. -/
theorem imLoop_inside (hC : Coded M T k cd A Tm) (hM : M.IsPlane) (hk : 0 < k) {Fw : ℕ → ℕ}
    {W : ℕ} {o : List ℕ} {P : Input} {c : Config} (hS : SB k A Tm Fw W o c)
    (hall : c.nreg 11 = k) (a : D) (hTa : Tm (cd a) = 0) {bIm bA : ℕ}
    (hlay : bA + 3 * k ≤ bIm ∧ 10 * k ≤ bIm) (hW : bIm + k ≤ W)
    (hI : IR k bIm bA (cd a) c) (mA : ∀ x < 3 * k, c.nmem (bA + x) = A x) :
    ∃ c' t, Exec P W (.seq fsel imLoop) c c' t ∧ t ≤ 21 * k + 21 ∧
      (∀ G : M.Face, c'.nmem (bIm + fi cd G) ≠ c'.nreg 539 ↔ G ∈ T.inside a) ∧
      (∀ x, ¬ (bIm ≤ x ∧ x < bIm + k) → c'.nmem x = c.nmem x) ∧
      (∀ r, r ≠ 532 → r ≠ 539 → (r < 540 ∨ 550 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  classical
  have hAlt : ∀ y < 3 * k, A y < 3 * k := fun y hy => by
    have e : y = cd (cd.symm ⟨y, hy⟩) := by simp
    rw [e, hC.A_cd]; exact (cd _).2
  set pdF : ℕ → ℕ := fun G => c.nmem (8 * k + G) with hpdF
  obtain ⟨c₁, t₁, e₁, ht₁, h532, h539, hr₁, hm₁, ho₁⟩ := fsel_exec (P := P) (pdF := pdF) (AF := A)
    ⟨by omega, by omega⟩ c hS.wb hI (cd a).2 (fun G _ => rfl) mA
  have hI₁ := hI.of hr₁
  obtain ⟨c₂, t₂, e₂, ht₂, h0, hrec, hf₂, hr₂, ho₂⟩ := imLoop_exec (P := P) (by omega) hlay hW
    (qu k c.nmem) pdF A (fselF pdF A (cd a))
    (fun i hi => hS.q_lt i (by omega)) (fun i hi j hj e => hS.q_inj i (by omega) j (by omega) e)
    hS.q0.2 (fun G hG => hS.exists_pos hall hG)
    (fun i h1 hi => by
      obtain ⟨b1, b2, b3, i', hi', e⟩ := hS.pd_ok i h1 (by omega)
      exact ⟨b2, hAlt _ b2, i', hi', e⟩)
    c₁ e₁.wb_right hI₁ h532 (fun i _ => by rw [hm₁]; rfl) (fun G _ => by rw [hm₁])
    (fun x hx => by rw [hm₁]; exact mA x hx)
  have h539' : c₂.nreg 539 = fselB pdF (cd a) := by
    rw [hr₂ 539 (Or.inl (by omega))]; exact h539
  have hpd : ∀ G, pd k c.nmem G = pdF G := fun G => rfl
  have hisPd : (0 < (cd a : ℕ) / 3 ∧ pdF ((cd a : ℕ) / 3) = cd a) ↔ SepProg.IsPd c.nmem k (cd a) :=
    Iff.rfl
  have key := SepProg.inside_marks hC hM hk hS hall (fun f => c₂.nmem (bIm + f)) a
    (by simpa using h0)
    (fun G hG hG0 => by
      rw [hrec G hG hG0, hpd]
      simp only [hTa, ne_eq, not_true_eq_false, ↓reduceIte]
      unfold fselF
      by_cases hp : SepProg.IsPd c.nmem k (cd a)
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (hisPd.2 hp)),
          ite_eq_left_of_eq_true _ _ (eq_true hp)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hp (hisPd.1 h))),
          ite_eq_right_of_eq_false _ _ (eq_false hp)])
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, fun G => ?_, fun x hx => ?_, fun r h1 h2 h3 => ?_,
    by rw [ho₂, ho₁]⟩
  · rw [h539', ← key G]
    simp only [hTa, ne_eq, not_true_eq_false, ↓reduceIte]
    unfold fselB
    by_cases hp : SepProg.IsPd c.nmem k (cd a)
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (hisPd.2 hp)),
        ite_eq_left_of_eq_true _ _ (eq_true hp)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hp (hisPd.1 h))),
        ite_eq_right_of_eq_false _ _ (eq_false hp)]
  · rw [hf₂ x hx, hm₁]
  · rw [hr₂ r (by omega), hr₁ r h1 h2 (by omega)]

end Bridge

end MillerProg

end PlanarSeparator
