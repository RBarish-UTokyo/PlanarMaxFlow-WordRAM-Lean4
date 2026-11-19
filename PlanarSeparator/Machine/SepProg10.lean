module

public import PlanarSeparator.Machine.SepOut
public import PlanarSeparator.Machine.MillerFullAll

/-!
# Steps 1–10 of the separator of the recursion on the machine

`MillerProg.Spec10` (`PlanarSeparator/Machine/SepOut.lean`) is the specification of a program of
steps 1–10 run by `sepRun` after `sepIn`. Here it is met by Miller's whole program:

* `MillerProg.setup10` (`MillerProg.setup10_exec`): the registers `S9Regs`, `S10Regs`,
  `S11Regs` of steps 9–10 with their arrays laid out from `bS₂ + n` (above the arrays of `millerA`,
  `aBase`) to `bS₂ + 10 k + 21 n + 4 ≤ aEnd10 k n`, cleared by `zrclear`; `k` and the registers
  `r390`, `r393` of `sepRun` saved in `r680`, `r690`, `r691`.
* `MillerProg.millerFull` (`MillerProg.millerFull_spec`): the separator `bandSep` with `SepOK`,
  its face marks at `r642` (with flag `r643` and polarity `r644`).
* `MillerProg.marks01` (`MillerProg.marks01_exec`): the face marks turned in place into `0`/`1`
  (`1` on the faces of the separator), `r394` their base, `r390`, `r393` restored.
* **`MillerProg.prog10_spec10`**: `prog10 = setup10 ; millerFull ; marks01` meets `Spec10` within
  `T10 m n = (693 m + 60 n + 152) log₂ n + 5500 m + 850 n + 1700` steps (`n = nV + nF + m`), for
  `aEnd10 (3 m) n ≤ B₀ ≤ W`; the separator has at most `6 ⌊√n⌋ + 2` darts.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace PlanarSeparator

open Finset StDart

namespace Map

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P] (M : Map D P)

/-- The faces of the stellar subdivision are the triples of `phi3` for `stCode`. -/
lemma stCode_phi3 {m : ℕ} (c : D ≃ Fin m) (x : StDart D) :
    (M.stCode c (M.stellar.φ x) : ℕ) = CycleSearch.phi3 (M.stCode c x) := by
  rw [stCode_val, stCode_val]
  cases x with
  | old d =>
    show M.stNum c (up (M.φ d)) = CycleSearch.phi3 (M.stNum c (old d))
    simp only [stNum, Equiv.symm_apply_apply, phi3_0]
  | up e =>
    show M.stNum c (down (M.φ.symm e)) = CycleSearch.phi3 (M.stNum c (up e))
    simp only [stNum, phi3_1]
  | down d =>
    show M.stNum c (old d) = CycleSearch.phi3 (M.stNum c (down d))
    simp only [stNum, phi3_2]

end Map

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Map CycleSearch

variable {W : ℕ} {P : Input}

/-! ### The programs -/

/-- The bases of the arrays of steps 9–10 from `s = bS₂ + n` (`r382 = bS₂`, `r143 = k`,
`r161 = n`, `r141 = 1`, `r142 = 3`): `bIm = s`, `bMk`, `bTmp`, `bFc` (`s9band`), `bNx`, `bA'`,
`bL'`, `bS'`, `bSum'`, `bCy`, `bPos`, `bCv`, the two arc options `bP1 … bF1`, `bP2 … bF2`, and
the end `r687`. -/
def s10A : Stmt := block [.addN 531 382 161, .copyN 608 531, .copyN 631 531, .addN 506 531 143,
  .addN 509 506 161, .addN 508 509 161, .copyN 630 508, .addN 438 508 161, .addN 438 438 161,
  .addN 438 438 141, .addN 591 438 161, .addN 592 591 143, .copyN 435 592, .addN 593 592 143,
  .addN 594 593 143, .addN 439 594 143, .addN 439 439 141, .mulN 436 142 143, .addN 440 439 436,
  .constN 684 4, .mulN 685 684 143, .mulN 686 684 161, .addN 632 594 685, .addN 632 632 686,
  .addN 632 632 141, .addN 611 632 161, .addN 612 611 161, .addN 615 612 143, .addN 613 615 161,
  .addN 614 613 161, .addN 616 614 161, .addN 616 616 161, .addN 616 616 141, .addN 617 616 161,
  .addN 620 617 143, .addN 618 620 161, .addN 619 618 161, .addN 687 619 161, .addN 687 687 161,
  .addN 687 687 141]

/-- The constant registers of steps 9–10, `k` in `r680`, `r390`, `r393` saved in `r690`, `r691`,
and the registers of `zrclear` (`r307 = 1`, `r322 = s`, `r321 = r687 - s`). -/
def s10B : Stmt := block [.constN 501 0, .copyN 502 162, .copyN 503 215, .constN 504 0,
  .copyN 505 161, .constN 507 1, .constN 510 0, .constN 511 1, .copyN 530 143, .constN 533 1,
  .constN 534 0, .constN 535 3, .mulN 536 436 142, .subN 537 536 143, .constN 538 0, .copyN 567 163, .copyN 595 164, .copyN 596 165,
  .constN 430 0, .constN 431 1, .constN 432 3, .constN 433 0, .copyN 434 162, .copyN 441 161,
  .copyN 442 163, .copyN 443 215, .copyN 605 143, .copyN 606 536, .copyN 607 537,
  .copyN 633 190, .copyN 634 189, .copyN 680 143, .copyN 690 390, .copyN 691 393,
  .constN 307 1, .copyN 322 531, .subN 321 687 531]

/-- **The setup of steps 9–10**: the bases, the constants, and the arrays cleared. -/
def setup10 : Stmt := .seq s10A (.seq s10B zrclear)

/-- One face: `mem[r642 + i] := ([mem[r642 + i] = r643] + r694) % 2` (`r692 = i`, `r693 = 2`,
`r695 = 1`). -/
def mkbody : Stmt :=
  .seq (block [.addN 696 642 692, .loadN 697 696]) (.seq (eqb 698 697 643)
    (block [.addN 699 698 694, .modN 699 699 693, .storeN 696 699, .addN 692 692 695]))

/-- **The `0`/`1` marks** of the faces of the separator, in place at `r642` (`r694 = [r644 = 1]`,
`k` faces in `r680`), with `r394 = r642` and `r390`, `r393` restored. -/
def marks01 : Stmt :=
  .seq (block [.copyN 394 642, .constN 692 0, .constN 693 2, .constN 695 1])
    (.seq (eqb 694 644 695)
      (.seq (.whileLtN 692 680 mkbody) (block [.copyN 390 690, .copyN 393 691])))

/-- **Steps 1–10 of the separator of the recursion**: the setup, Miller's whole program and the
`0`/`1` marks. -/
def prog10 : Stmt := .seq setup10 (.seq millerFull marks01)

/-- The end of the arrays of `prog10` for `k` triangles and `n` vertices. -/
def aEnd10 (k n : ℕ) : ℕ := aEnd k n + 7 * k + 17 * n

/-- The time bound of `prog10` (`m` darts of the piece map, `n = nV + nF + m`). -/
def T10 (m n : ℕ) : ℕ := (693 * m + 60 * n + 152) * Nat.log 2 n + 5500 * m + 850 * n + 1700

/-- Miller's whole program writes no register from `680` on (kernel evaluation). -/
theorem millerFull_wmax : millerFull.wmax < 680 := by decide +kernel

/-! ### The setup -/

theorem s10A_wr {r : ℕ} (hr : r < 430) : s10A.wr r = false := by
  simp only [s10A, block, Stmt.wr, Instr.wr, Bool.or_false, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq]
  omega

theorem s10B_wr {r : ℕ} (hr : r < 300 ∨ (325 ≤ r ∧ r < 430)) : s10B.wr r = false := by
  simp only [s10B, block, Stmt.wr, Instr.wr, Bool.or_false, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne, ne_eq]
  omega

set_option maxHeartbeats 4000000 in
/-- The bases of the arrays of steps 9–10 (`s10A`). -/
theorem s10A_exec {k n S : ℕ} (c : Config) (hc : WordsBounded W c) (h141 : c.nreg 141 = 1)
    (h142 : c.nreg 142 = 3) (h143 : c.nreg 143 = k) (h161 : c.nreg 161 = n)
    (h382 : c.nreg 382 = S) (hS : 11 * k ≤ S) (hW : S + 10 * k + 21 * n + 4 ≤ W) :
    ∃ c₁ t₁, Exec P W s10A c c₁ t₁ ∧ t₁ = 40 ∧
      c₁.nreg 531 = S + n ∧ c₁.nreg 608 = S + n ∧ c₁.nreg 631 = S + n ∧
      c₁.nreg 506 = S + k + n ∧ c₁.nreg 509 = S + k + 2 * n ∧ c₁.nreg 508 = S + k + 3 * n ∧
      c₁.nreg 630 = S + k + 3 * n ∧ c₁.nreg 438 = S + k + 5 * n + 1 ∧
      c₁.nreg 591 = S + k + 6 * n + 1 ∧ c₁.nreg 592 = S + 2 * k + 6 * n + 1 ∧
      c₁.nreg 435 = S + 2 * k + 6 * n + 1 ∧ c₁.nreg 593 = S + 3 * k + 6 * n + 1 ∧
      c₁.nreg 594 = S + 4 * k + 6 * n + 1 ∧ c₁.nreg 439 = S + 5 * k + 6 * n + 2 ∧
      c₁.nreg 436 = 3 * k ∧ c₁.nreg 440 = S + 8 * k + 6 * n + 2 ∧
      c₁.nreg 632 = S + 8 * k + 10 * n + 2 ∧ c₁.nreg 611 = S + 8 * k + 11 * n + 2 ∧
      c₁.nreg 612 = S + 8 * k + 12 * n + 2 ∧ c₁.nreg 615 = S + 9 * k + 12 * n + 2 ∧
      c₁.nreg 613 = S + 9 * k + 13 * n + 2 ∧ c₁.nreg 614 = S + 9 * k + 14 * n + 2 ∧
      c₁.nreg 616 = S + 9 * k + 16 * n + 3 ∧ c₁.nreg 617 = S + 9 * k + 17 * n + 3 ∧
      c₁.nreg 620 = S + 10 * k + 17 * n + 3 ∧ c₁.nreg 618 = S + 10 * k + 18 * n + 3 ∧
      c₁.nreg 619 = S + 10 * k + 19 * n + 3 ∧ c₁.nreg 687 = S + 10 * k + 21 * n + 4 ∧
      c₁.nmem = c.nmem ∧ c₁.output = c.output := by
  unfold s10A
  exec_block
  all_goals try (show _ ≤ W; config_simp; (try simp only [h141, h142, h143, h161, h382]); omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  all_goals (config_simp <;> (try simp only [h141, h142, h143, h161, h382]) <;> omega)

set_option maxHeartbeats 4000000 in
/-- The constants of steps 9–10 (`s10B`). -/
theorem s10B_exec {k n S bV bLv bF bw bCN bWC bPr : ℕ} (c₁ : Config) (hc : WordsBounded W c₁)
    (g142 : c₁.nreg 142 = 3) (g143 : c₁.nreg 143 = k) (g161 : c₁.nreg 161 = n)
    (g162 : c₁.nreg 162 = bV) (g163 : c₁.nreg 163 = bLv) (g164 : c₁.nreg 164 = bF)
    (g165 : c₁.nreg 165 = bw) (g189 : c₁.nreg 189 = bCN) (g190 : c₁.nreg 190 = bWC)
    (g215 : c₁.nreg 215 = bPr) (q531 : c₁.nreg 531 = S + n)
    (q687 : c₁.nreg 687 = S + 10 * k + 21 * n + 4) (q436 : c₁.nreg 436 = 3 * k)
    (hW : S + 10 * k + 21 * n + 4 ≤ W) :
    ∃ c₂ t₂, Exec P W s10B c₁ c₂ t₂ ∧ t₂ = 37 ∧
      c₂.nreg 501 = 0 ∧ c₂.nreg 502 = bV ∧ c₂.nreg 503 = bPr ∧ c₂.nreg 504 = 0 ∧
      c₂.nreg 505 = n ∧ c₂.nreg 507 = 1 ∧ c₂.nreg 510 = 0 ∧ c₂.nreg 511 = 1 ∧
      c₂.nreg 530 = k ∧ c₂.nreg 533 = 1 ∧ c₂.nreg 534 = 0 ∧ c₂.nreg 535 = 3 ∧
      c₂.nreg 536 = 9 * k ∧ c₂.nreg 537 = 8 * k ∧ c₂.nreg 538 = 0 ∧ c₂.nreg 567 = bLv ∧
      c₂.nreg 595 = bF ∧ c₂.nreg 596 = bw ∧ c₂.nreg 430 = 0 ∧ c₂.nreg 431 = 1 ∧
      c₂.nreg 432 = 3 ∧ c₂.nreg 433 = 0 ∧ c₂.nreg 434 = bV ∧ c₂.nreg 441 = n ∧
      c₂.nreg 442 = bLv ∧ c₂.nreg 443 = bPr ∧ c₂.nreg 605 = k ∧ c₂.nreg 606 = 9 * k ∧
      c₂.nreg 607 = 8 * k ∧ c₂.nreg 633 = bWC ∧ c₂.nreg 634 = bCN ∧ c₂.nreg 680 = k ∧
      c₂.nreg 690 = c₁.nreg 390 ∧ c₂.nreg 691 = c₁.nreg 393 ∧ c₂.nreg 307 = 1 ∧
      c₂.nreg 322 = S + n ∧ c₂.nreg 321 = 10 * k + 20 * n + 4 ∧
      c₂.nmem = c₁.nmem ∧ c₂.output = c₁.output := by
  have hbnd := hc.1
  unfold s10B
  exec_block
  all_goals try (show _ ≤ W; config_simp; first | exact hbnd _ |
    (simp only [g142, g143, g161, q531, q687, q436]; omega) | omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  all_goals (config_simp <;> (try simp only [g142, g143, g161, g162, g163, g164, g165, g189,
    g190, g215, q531, q687, q436]) <;> omega)

set_option maxHeartbeats 4000000 in
/-- **The setup of steps 9–10 on the machine.** -/
theorem setup10_exec {b : ABase} {k n : ℕ} (c : Config) (hc : WordsBounded W c)
    (hR : ARegs b k n c) (hS : 11 * k ≤ b.bS₂) (hW : b.bS₂ + 10 * k + 21 * n + 4 ≤ W) :
    ∃ c' t, Exec P W setup10 c c' t ∧ t ≤ 50 * k + 100 * n + 101 ∧
      (∀ r, r < 300 ∨ r = 381 ∨ r = 382 → c'.nreg r = c.nreg r) ∧
      S9Regs k n b.bV b.bPr b.bLv (b.bS₂ + n) (b.bS₂ + k + n) (b.bS₂ + k + 2 * n)
        (b.bS₂ + k + 3 * n) c' ∧
      S10Regs k n b.bV b.bLv b.bPr b.bF b.bw (b.bS₂ + k + 6 * n + 1) (b.bS₂ + 2 * k + 6 * n + 1)
        (b.bS₂ + 3 * k + 6 * n + 1) (b.bS₂ + 4 * k + 6 * n + 1) (b.bS₂ + k + 5 * n + 1)
        (b.bS₂ + 5 * k + 6 * n + 2) (b.bS₂ + 8 * k + 6 * n + 2) c' ∧
      S11Regs k (b.bS₂ + n) (b.bS₂ + k + 3 * n) (b.bS₂ + 8 * k + 10 * n + 2) b.bWC b.bCN
        (b.bS₂ + 8 * k + 11 * n + 2) (b.bS₂ + 8 * k + 12 * n + 2) (b.bS₂ + 9 * k + 13 * n + 2)
        (b.bS₂ + 9 * k + 14 * n + 2) (b.bS₂ + 9 * k + 12 * n + 2) (b.bS₂ + 9 * k + 16 * n + 3)
        (b.bS₂ + 9 * k + 17 * n + 3) (b.bS₂ + 10 * k + 18 * n + 3)
        (b.bS₂ + 10 * k + 19 * n + 3) (b.bS₂ + 10 * k + 17 * n + 3) c' ∧
      c'.nreg 680 = k ∧ c'.nreg 690 = c.nreg 390 ∧ c'.nreg 691 = c.nreg 393 ∧
      (∀ x < 10 * k + 20 * n + 4, c'.nmem (b.bS₂ + n + x) = 0) ∧
      (∀ a, a < b.bS₂ + n ∨ b.bS₂ + 10 * k + 21 * n + 4 ≤ a → c'.nmem a = c.nmem a) ∧
      c'.output = c.output := by
  have hz : b.bS₂ + n + (10 * k + 20 * n + 4) ≤ W := by omega
  have hr0 : ∀ r, r < 300 ∨ r = 381 ∨ r = 382 →
      r ≠ 320 ∧ r ≠ 323 ∧ r ≠ 324 ∧ (r < 300 ∨ (325 ≤ r ∧ r < 430)) ∧ r < 430 := by
    intro r hr; omega
  have hm0 : ∀ a, a < b.bS₂ + n ∨ b.bS₂ + 10 * k + 21 * n + 4 ≤ a →
      a < b.bS₂ + n ∨ b.bS₂ + n + (10 * k + 20 * n + 4) ≤ a := by
    intro a ha; omega
  -- 1. the bases
  obtain ⟨c₁, t₁, e₁, ht₁, q531, q608, q631, q506, q509, q508, q630, q438, q591, q592, q435,
      q593, q594, q439, q436, q440, q632, q611, q612, q615, q613, q614, q616, q617, q620, q618,
      q619, q687, m₁, o₁⟩ :=
    s10A_exec (P := P) c hc hR.r141 hR.r142 hR.r143 hR.r161 hR.r382 hS hW
  have f₁ : ∀ r, r < 430 → c₁.nreg r = c.nreg r := fun r h => e₁.nreg_of_wr (s10A_wr h)
  -- 2. the constants
  obtain ⟨c₂, t₂, e₂, ht₂, p501, p502, p503, p504, p505, p507, p510, p511, p530, p533, p534,
      p535, p536, p537, p538, p567, p595, p596, p430, p431, p432, p433, p434, p441, p442, p443,
      p605, p606, p607, p633, p634, p680, p690, p691, p307, p322, p321, m₂, o₂⟩ :=
    s10B_exec (P := P) c₁ e₁.wb_right ((f₁ 142 (by decide)).trans hR.r142)
      ((f₁ 143 (by decide)).trans hR.r143) ((f₁ 161 (by decide)).trans hR.r161)
      ((f₁ 162 (by decide)).trans hR.r162) ((f₁ 163 (by decide)).trans hR.r163)
      ((f₁ 164 (by decide)).trans hR.r164) ((f₁ 165 (by decide)).trans hR.r165)
      ((f₁ 189 (by decide)).trans hR.r189) ((f₁ 190 (by decide)).trans hR.r190)
      ((f₁ 215 (by decide)).trans hR.r215) q531 q687 q436 hW
  -- 3. the clear arrays
  obtain ⟨c₃, t₃, e₃, ht₃, hz₃, hr₃, hm₃, ho₃⟩ := zrclear_exec (P := P) (W := W)
    (N := 10 * k + 20 * n + 4) (b := b.bS₂ + n) hz c₂ e₂.wb_right p307 p321 p322
  have Z : ∀ r, r ≠ 320 → r ≠ 323 → r ≠ 324 → c₃.nreg r = c₂.nreg r := hr₃
  have F : ∀ r, r ≠ 320 → r ≠ 323 → r ≠ 324 → s10B.wr r = false → c₃.nreg r = c₁.nreg r :=
    fun r a b' d h => (hr₃ r a b' d).trans (e₂.nreg_of_wr h)
  have hfr : ∀ r, r < 300 ∨ r = 381 ∨ r = 382 → c₃.nreg r = c.nreg r := fun r hr => by
    have h1 := hr0 r hr
    rw [hr₃ r h1.1 h1.2.1 h1.2.2.1, e₂.nreg_of_wr (s10B_wr h1.2.2.2.1), f₁ r h1.2.2.2.2]
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by clear * - ht₁ ht₂ ht₃; omega, hfr, ?_, ?_, ?_,
    by rw [Z 680 (by decide) (by decide) (by decide)]; exact p680,
    by rw [Z 690 (by decide) (by decide) (by decide), p690]; exact f₁ 390 (by decide),
    by rw [Z 691 (by decide) (by decide) (by decide), p691]; exact f₁ 393 (by decide), hz₃,
    fun a ha => by rw [hm₃ a (hm0 a ha), m₂, m₁], by rw [ho₃, o₂, o₁]⟩
  · exact ⟨(Z 501 (by decide) (by decide) (by decide)).trans p501,
      (Z 502 (by decide) (by decide) (by decide)).trans p502,
      (Z 503 (by decide) (by decide) (by decide)).trans p503,
      (Z 504 (by decide) (by decide) (by decide)).trans p504,
      (Z 505 (by decide) (by decide) (by decide)).trans p505,
      (F 506 (by decide) (by decide) (by decide) (by decide)).trans q506,
      (Z 507 (by decide) (by decide) (by decide)).trans p507,
      (F 508 (by decide) (by decide) (by decide) (by decide)).trans q508,
      (F 509 (by decide) (by decide) (by decide) (by decide)).trans q509,
      (Z 510 (by decide) (by decide) (by decide)).trans p510,
      (Z 511 (by decide) (by decide) (by decide)).trans p511,
      (Z 530 (by decide) (by decide) (by decide)).trans p530,
      (F 531 (by decide) (by decide) (by decide) (by decide)).trans q531,
      (Z 533 (by decide) (by decide) (by decide)).trans p533,
      (Z 534 (by decide) (by decide) (by decide)).trans p534,
      (Z 535 (by decide) (by decide) (by decide)).trans p535,
      (Z 536 (by decide) (by decide) (by decide)).trans p536,
      (Z 537 (by decide) (by decide) (by decide)).trans p537,
      (Z 538 (by decide) (by decide) (by decide)).trans p538,
      (Z 567 (by decide) (by decide) (by decide)).trans p567⟩
  · exact ⟨(F 591 (by decide) (by decide) (by decide) (by decide)).trans q591,
      (F 592 (by decide) (by decide) (by decide) (by decide)).trans q592,
      (F 593 (by decide) (by decide) (by decide) (by decide)).trans q593,
      (F 594 (by decide) (by decide) (by decide) (by decide)).trans q594,
      (Z 595 (by decide) (by decide) (by decide)).trans p595,
      (Z 596 (by decide) (by decide) (by decide)).trans p596,
      (Z 430 (by decide) (by decide) (by decide)).trans p430,
      (Z 431 (by decide) (by decide) (by decide)).trans p431,
      (Z 432 (by decide) (by decide) (by decide)).trans p432,
      (Z 433 (by decide) (by decide) (by decide)).trans p433,
      (Z 434 (by decide) (by decide) (by decide)).trans p434,
      (F 435 (by decide) (by decide) (by decide) (by decide)).trans q435,
      (F 436 (by decide) (by decide) (by decide) (by decide)).trans q436,
      (F 438 (by decide) (by decide) (by decide) (by decide)).trans q438,
      (F 439 (by decide) (by decide) (by decide) (by decide)).trans q439,
      (F 440 (by decide) (by decide) (by decide) (by decide)).trans q440,
      (Z 441 (by decide) (by decide) (by decide)).trans p441,
      (Z 442 (by decide) (by decide) (by decide)).trans p442,
      (Z 443 (by decide) (by decide) (by decide)).trans p443⟩
  · exact ⟨(Z 605 (by decide) (by decide) (by decide)).trans p605,
      (Z 606 (by decide) (by decide) (by decide)).trans p606,
      (Z 607 (by decide) (by decide) (by decide)).trans p607,
      (F 608 (by decide) (by decide) (by decide) (by decide)).trans q608,
      (F 611 (by decide) (by decide) (by decide) (by decide)).trans q611,
      (F 612 (by decide) (by decide) (by decide) (by decide)).trans q612,
      (F 613 (by decide) (by decide) (by decide) (by decide)).trans q613,
      (F 614 (by decide) (by decide) (by decide) (by decide)).trans q614,
      (F 615 (by decide) (by decide) (by decide) (by decide)).trans q615,
      (F 616 (by decide) (by decide) (by decide) (by decide)).trans q616,
      (F 617 (by decide) (by decide) (by decide) (by decide)).trans q617,
      (F 618 (by decide) (by decide) (by decide) (by decide)).trans q618,
      (F 619 (by decide) (by decide) (by decide) (by decide)).trans q619,
      (F 620 (by decide) (by decide) (by decide) (by decide)).trans q620,
      (F 630 (by decide) (by decide) (by decide) (by decide)).trans q630,
      (F 631 (by decide) (by decide) (by decide) (by decide)).trans q631,
      (F 632 (by decide) (by decide) (by decide) (by decide)).trans q632,
      (Z 633 (by decide) (by decide) (by decide)).trans p633,
      (Z 634 (by decide) (by decide) (by decide)).trans p634⟩

/-- The registers of `millerA` are kept by a program that writes none of them. -/
theorem ARegs.of_nreg {b : ABase} {k n : ℕ} {c c' : Config} (h : ARegs b k n c)
    (hr : ∀ r, r < 300 ∨ r = 381 ∨ r = 382 → c'.nreg r = c.nreg r) : ARegs b k n c' :=
  ⟨cregs_of h.cregs (fun r h' => hr r (by omega)), (hr 140 (by omega)).trans h.r140,
    (hr 141 (by omega)).trans h.r141, (hr 142 (by omega)).trans h.r142,
    (hr 143 (by omega)).trans h.r143, (hr 144 (by omega)).trans h.r144,
    (hr 145 (by omega)).trans h.r145, (hr 146 (by omega)).trans h.r146,
    (hr 147 (by omega)).trans h.r147, (hr 161 (by omega)).trans h.r161,
    (hr 162 (by omega)).trans h.r162, (hr 163 (by omega)).trans h.r163,
    (hr 164 (by omega)).trans h.r164, (hr 165 (by omega)).trans h.r165,
    (hr 166 (by omega)).trans h.r166, (hr 188 (by omega)).trans h.r188,
    (hr 189 (by omega)).trans h.r189, (hr 190 (by omega)).trans h.r190,
    (hr 200 (by omega)).trans h.r200, (hr 215 (by omega)).trans h.r215,
    (hr 216 (by omega)).trans h.r216, (hr 217 (by omega)).trans h.r217,
    (hr 218 (by omega)).trans h.r218, (hr 219 (by omega)).trans h.r219,
    (hr 252 (by omega)).trans h.r252, (hr 253 (by omega)).trans h.r253,
    (hr 254 (by omega)).trans h.r254, (hr 381 (by omega)).trans h.r381,
    (hr 382 (by omega)).trans h.r382⟩

/-! ### The `0`/`1` marks -/

/-- The mark of one face: `[x = f] + [p = 1]` is odd iff `x ≠ f ↔ p = 1`. -/
lemma bit_eq {e₁ e₂ x f p : ℕ} (h1 : e₁ ≤ 1) (h1' : e₁ = 1 ↔ x = f) (h2 : e₂ ≤ 1)
    (h2' : e₂ = 1 ↔ p = 1) : (e₁ + e₂) % 2 = if (x ≠ f ↔ p = 1) then 1 else 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with rfl | rfl <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h2 with rfl | rfl <;> simp_all

set_option maxHeartbeats 4000000 in
/-- **The `0`/`1` marks on the machine**: the `k = r680` marks at `r642` become `1` exactly
where `mark ≠ r643 ↔ r644 = 1`, within `13 k + 15` steps; `r394 = r642`, `r390 = r690`,
`r393 = r691`, and the rest of the memory is kept. -/
theorem marks01_exec {k : ℕ} (hW2 : 2 ≤ W) (c : Config) (hc : WordsBounded W c)
    (h680 : c.nreg 680 = k) (hb : c.nreg 642 + k ≤ W) :
    ∃ c' t, Exec P W marks01 c c' t ∧ t ≤ 13 * k + 15 ∧ c'.nreg 394 = c.nreg 642 ∧
      c'.nreg 390 = c.nreg 690 ∧ c'.nreg 393 = c.nreg 691 ∧
      (∀ i < k, c'.nmem (c.nreg 642 + i) =
        if (c.nmem (c.nreg 642 + i) ≠ c.nreg 643 ↔ c.nreg 644 = 1) then 1 else 0) ∧
      (∀ a, a < c.nreg 642 ∨ c.nreg 642 + k ≤ a → c'.nmem a = c.nmem a) := by
  set B := c.nreg 642 with hB
  -- 1. the constants
  obtain ⟨c₁, t₁, e₁, ht₁, q394, q692, q693, q695, m₁⟩ : ∃ c₁ t₁, Exec P W
      (block [.copyN 394 642, .constN 692 0, .constN 693 2, .constN 695 1]) c c₁ t₁ ∧ t₁ = 4 ∧
      c₁.nreg 394 = B ∧ c₁.nreg 692 = 0 ∧ c₁.nreg 693 = 2 ∧ c₁.nreg 695 = 1 ∧
      c₁.nmem = c.nmem := by
    exec_block
    all_goals try (show _ ≤ W; config_simp; first | exact hc.1 _ | omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, rfl⟩
    all_goals (config_simp <;> (try simp only [← hB]) <;> omega)
  have k₁ : ∀ r, r ≠ 394 → r ≠ 692 → r ≠ 693 → r ≠ 695 → c₁.nreg r = c.nreg r :=
    fun r a b d e => e₁.nreg_of_wr (by
      simp only [block, Stmt.wr, Instr.wr, Bool.or_false, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq]; omega)
  -- 2. the polarity bit
  obtain ⟨c₂, t₂, e₂, ht₂, b₂, i₂, k₂, m₂, -⟩ :=
    eqb_exec (P := P) (by omega) 694 644 695 c₁ e₁.wb_right
  have r₂ : ∀ r, r ≠ 394 → r ≠ 692 → r ≠ 693 → r ≠ 694 → r ≠ 695 → c₂.nreg r = c.nreg r :=
    fun r a b d e f => by rw [k₂ r e, k₁ r a b d f]
  have v642 : c₂.nreg 642 = B := r₂ 642 (by omega) (by omega) (by omega) (by omega) (by omega)
  have v643 : c₂.nreg 643 = c.nreg 643 :=
    r₂ 643 (by omega) (by omega) (by omega) (by omega) (by omega)
  have v680 : c₂.nreg 680 = k :=
    (r₂ 680 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h680
  have v693 : c₂.nreg 693 = 2 := (k₂ 693 (by omega)).trans q693
  have v695 : c₂.nreg 695 = 1 := (k₂ 695 (by omega)).trans q695
  have v692 : c₂.nreg 692 = 0 := (k₂ 692 (by omega)).trans q692
  have i₂' : c₂.nreg 694 = 1 ↔ c.nreg 644 = 1 := by
    rw [i₂, q695, k₁ 644 (by omega) (by omega) (by omega) (by omega)]
  have M₂ : c₂.nmem = c.nmem := by rw [m₂, m₁]
  -- 3. the loop
  let bit : ℕ → ℕ := fun x => if (x ≠ c.nreg 643 ↔ c.nreg 644 = 1) then 1 else 0
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 692 = i ∧ i ≤ k ∧
    (∀ r, r ≠ 692 → r ≠ 696 → r ≠ 697 → r ≠ 698 → r ≠ 699 → c'.nreg r = c₂.nreg r) ∧
    (∀ x < i, c'.nmem (B + x) = bit (c.nmem (B + x))) ∧
    (∀ a, ¬ (B ≤ a ∧ a < B + i) → c'.nmem a = c.nmem a)
  obtain ⟨c₃, t₃, e₃, ⟨-, -, -, hr₃, hd₃, hm₃⟩, ht₃⟩ := Exec.forN (P := P) (W := W) (ri := 692)
    (rN := 680) (N := k) (lo := 0) (B := 11) (body := mkbody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.1 680 (by omega) (by omega) (by omega) (by omega)
      (by omega)).trans v680⟩)
    (fun i c' ⟨hw, h692, hi, hr, hd, hm⟩ hlt => by
      have g642 : c'.nreg 642 = B :=
        (hr 642 (by omega) (by omega) (by omega) (by omega) (by omega)).trans v642
      -- the address and the mark
      obtain ⟨ca, ta, ea, hta, a696, a697, ka, ma⟩ : ∃ ca ta, Exec P W
          (block [.addN 696 642 692, .loadN 697 696]) c' ca ta ∧ ta = 2 ∧
          ca.nreg 696 = B + i ∧ ca.nreg 697 = c.nmem (B + i) ∧
          (∀ r, r ≠ 696 → r ≠ 697 → ca.nreg r = c'.nreg r) ∧ ca.nmem = c'.nmem := by
        have hc := hw
        exec_block
        all_goals try (show _ ≤ W; config_simp; first | exact hw.2 _ |
          (simp only [g642, h692]; omega))
        refine ⟨rfl, ?_, ?_, fun r a b => ?_, rfl⟩
        · config_simp; simp only [g642, h692]
        · config_simp; simp only [g642, h692]; exact hm _ (by omega)
        · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
      have hwa := ea.wb_right
      -- the comparison
      obtain ⟨cb, tb, eb, htb, bb, ib, kb, mb, -⟩ :=
        eqb_exec (P := P) (by omega) 698 697 643 ca hwa
      have hwb := eb.wb_right
      have b694 : cb.nreg 694 = c₂.nreg 694 := by
        rw [kb 694 (by omega), ka 694 (by omega) (by omega)]
        exact hr 694 (by omega) (by omega) (by omega) (by omega) (by omega)
      have b696 : cb.nreg 696 = B + i := by rw [kb 696 (by omega), a696]
      have b693 : cb.nreg 693 = 2 := by
        rw [kb 693 (by omega), ka 693 (by omega) (by omega),
          hr 693 (by omega) (by omega) (by omega) (by omega) (by omega), v693]
      have b695 : cb.nreg 695 = 1 := by
        rw [kb 695 (by omega), ka 695 (by omega) (by omega),
          hr 695 (by omega) (by omega) (by omega) (by omega) (by omega), v695]
      have b692 : cb.nreg 692 = i := by
        rw [kb 692 (by omega), ka 692 (by omega) (by omega), h692]
      have ib' : cb.nreg 698 = 1 ↔ c.nmem (B + i) = c.nreg 643 := by
        rw [ib, a697, ka 643 (by omega) (by omega),
          hr 643 (by omega) (by omega) (by omega) (by omega) (by omega), v643]
      have hbit : (cb.nreg 698 + cb.nreg 694) % 2 = bit (c.nmem (B + i)) := by
        rw [b694]; exact bit_eq bb ib' b₂ i₂'
      -- the new mark
      obtain ⟨cc, tc, ec, htc, c699, c692, kc, mc⟩ : ∃ cc tc, Exec P W
          (block [.addN 699 698 694, .modN 699 699 693, .storeN 696 699, .addN 692 692 695])
          cb cc tc ∧ tc = 4 ∧ cc.nreg 699 = bit (c.nmem (B + i)) ∧ cc.nreg 692 = i + 1 ∧
          (∀ r, r ≠ 692 → r ≠ 699 → cc.nreg r = cb.nreg r) ∧
          cc.nmem = upd cb.nmem (B + i) (bit (c.nmem (B + i))) := by
        have hc := hwb
        have hbit1 : bit (c.nmem (B + i)) ≤ 1 := by
          show (if _ then 1 else 0) ≤ 1; split_ifs <;> omega
        exec_block
        all_goals try (show _ ≤ W; config_simp; first | exact hwb.1 _ |
          (simp only [b693, b694, b695, b692, b696]; omega) |
          (simp only [b693, b694, b695, b692, b696, hbit]; omega))
        refine ⟨rfl, ?_, ?_, fun r a b => ?_, ?_⟩
        · config_simp; simp only [b693, hbit]
        · config_simp; simp only [b692, b695]
        · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | rfl
        · config_simp; simp only [b696, b693, hbit]
      refine ⟨cc, ta + (tb + tc), .seq ea (.seq eb ec), ⟨ec.wb_right, c692, by omega,
        fun r a b d e f => ?_, fun x hx => ?_, fun a ha => ?_⟩, by omega⟩
      · rw [kc r a f, kb r e, ka r b d]; exact hr r a b d e f
      · rw [mc, mb, ma]
        simp only [upd_apply]
        split_ifs with h
        · have : x = i := by omega
          subst this; rfl
        · exact hd x (by omega)
      · rw [mc, mb, ma]
        simp only [upd_apply]
        split_ifs with h
        · exact absurd ⟨by omega, by omega⟩ ha
        · exact hm a (fun h' => ha ⟨h'.1, by omega⟩))
    (Nat.zero_le _)
    ⟨e₂.wb_right, v692, Nat.zero_le _, fun r _ _ _ _ _ => rfl, fun x hx => absurd hx (by omega),
      fun a _ => by rw [M₂]⟩
  have hw₃ := e₃.wb_right
  -- 4. the registers restored
  obtain ⟨c₄, t₄, e₄, ht₄, q390, q393, m₄⟩ : ∃ c₄ t₄, Exec P W
      (block [.copyN 390 690, .copyN 393 691]) c₃ c₄ t₄ ∧ t₄ = 2 ∧
      c₄.nreg 390 = c₃.nreg 690 ∧ c₄.nreg 393 = c₃.nreg 691 ∧ c₄.nmem = c₃.nmem := by
    have hc := hw₃
    exec_block
    all_goals try (show _ ≤ W; config_simp; exact hw₃.1 _)
    refine ⟨rfl, ?_, ?_, rfl⟩ <;> config_simp
  have k₄ : ∀ r, r ≠ 390 → r ≠ 393 → c₄.nreg r = c₃.nreg r :=
    fun r a b => e₄.nreg_of_wr (by
      simp only [block, Stmt.wr, Instr.wr, Bool.or_false, Bool.or_eq_false_iff,
        beq_eq_false_iff_ne, ne_eq]; omega)
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, ?_, ?_, ?_,
    fun i hi => by rw [m₄]; exact hd₃ i hi, fun a ha => by rw [m₄]; exact hm₃ a (by omega)⟩
  · rw [k₄ 394 (by omega) (by omega), hr₃ 394 (by omega) (by omega) (by omega) (by omega)
      (by omega), k₂ 394 (by omega), q394]
  · rw [q390, hr₃ 690 (by omega) (by omega) (by omega) (by omega) (by omega),
      r₂ 690 (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [q393, hr₃ 691 (by omega) (by omega) (by omega) (by omega) (by omega),
      r₂ 691 (by omega) (by omega) (by omega) (by omega) (by omega)]

/-! ### Steps 1–10 -/

section Spec

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]

set_option maxHeartbeats 16000000 in
open Classical in
/-- **Steps 1–10 of the separator of the recursion on the machine.** For a plane map `M` without
loops with `m ≥ 1` darts, `0/1` flags `fl` not all `0`, and `aEnd10 (3 m) n ≤ B₀ ≤ W`
(`n = nV + nF + m`), `prog10 = setup10 ; millerFull ; marks01` meets `Spec10` within
`T10 m n = (693 m + 60 n + 152) log₂ n + 5500 m + 850 n + 1700` steps: the separator is the
explicit separator `bandSep` of Miller's program, with at most
`2 (l₂ - l₀) + #K₀ + #(T.lvl l₂) ≤ 6 ⌊√n⌋ + 2` darts. -/
theorem prog10_spec10 (M : Map D Q) {m nV nF : ℕ} (c : D ≃ Fin m) (vn : Q ≃ Fin nV)
    (fn : M.Face ≃ Fin nF) (fl : D → ℕ) {B₀ : ℕ} (hm1 : 1 ≤ m) (hM : M.IsPlane)
    (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (hfl1 : ∀ d, fl d ≤ 1) {d₀ : D} (hd₀ : 0 < fl d₀)
    (hB : aEnd10 (3 * m) (nV + nF + m) ≤ B₀) (hBW : B₀ ≤ W) :
    Spec10 M c vn fn fl B₀ (T10 m (nV + nF + m)) prog10 P W := by
  intro c₁ L hc₁ hL1 hL2 hAR hA hV hw
  set k := 3 * m with hk
  set n := nV + nF + m with hn
  set b := aBase k n L with hb
  set S := b.bS₂ with hSdef
  -- the layout
  have hSv : S = 22 * k + 14 * n + 3 + (L + 1) * n := rfl
  have hLn : (L + 1) * n ≤ (Nat.log 2 n + 2) * n := Nat.mul_le_mul_right _ (by omega)
  have hE : S + 10 * k + 21 * n + 4 ≤ B₀ := by
    have h := hB; unfold aEnd10 aEnd at h; omega
  have hEW : S + 10 * k + 21 * n + 4 ≤ W := hE.trans hBW
  have hS22 : 22 * k + 14 * n + 3 ≤ S := by omega
  have hlay : ALay b k n W := aLay_of hL1 hL2 (by have h := hB; unfold aEnd10 at h; omega)
  have hbV : b.bV = 11 * k := rfl
  have hbLv : b.bLv = 14 * k := rfl
  have hbPr : b.bPr = 14 * k + n := rfl
  have hbw : b.bw = 17 * k + 6 * n := rfl
  have hsum := sum_wSt_le M c hfl1
  have hWt : 11 * k + 3 * ∑ v, wSt M c fl v + 4 ≤ W := by omega
  have hlay9 : b.bS₂ + n ≤ S + n ∧ S + n + k ≤ S + k + n ∧ S + k + n + n ≤ S + k + 2 * n ∧
      S + k + 2 * n + n ≤ S + k + 3 * n ∧ S + k + 3 * n + 2 * n + 1 ≤ W := by omega
  have hlay10 : S + k + 3 * n + 2 * n + 1 ≤ S + k + 5 * n + 1 ∧
      S + k + 5 * n + 1 + n ≤ S + k + 6 * n + 1 ∧
      S + k + 6 * n + 1 + k ≤ S + 2 * k + 6 * n + 1 ∧
      S + 2 * k + 6 * n + 1 + k ≤ S + 3 * k + 6 * n + 1 ∧
      S + 3 * k + 6 * n + 1 + k ≤ S + 4 * k + 6 * n + 1 ∧
      S + 4 * k + 6 * n + 1 + k + 1 ≤ S + 5 * k + 6 * n + 2 ∧
      S + 5 * k + 6 * n + 2 + 3 * k ≤ S + 8 * k + 6 * n + 2 ∧
      S + 8 * k + 6 * n + 2 + n ≤ W ∧ S + 4 * k + 6 * n + 1 + 3 * k + 4 * n + 1 ≤ W := by
    omega
  have hlay11 : S + 8 * k + 6 * n + 2 + n ≤ S + 8 * k + 10 * n + 2 ∧
      S + 4 * k + 6 * n + 1 + 3 * k + 4 * n + 1 ≤ S + 8 * k + 10 * n + 2 ∧
      S + 8 * k + 10 * n + 2 + n ≤ S + 8 * k + 11 * n + 2 ∧
      S9Lay k n b.bV (S + 8 * k + 11 * n + 2) b.bLv (S + 8 * k + 12 * n + 2)
        (S + 9 * k + 12 * n + 2) (S + 9 * k + 13 * n + 2) (S + 9 * k + 14 * n + 2) W ∧
      S + 9 * k + 14 * n + 2 + 2 * n + 1 ≤ S + 9 * k + 16 * n + 3 ∧
      S9Lay k n b.bV (S + 9 * k + 16 * n + 3) b.bLv (S + 9 * k + 17 * n + 3)
        (S + 10 * k + 17 * n + 3) (S + 10 * k + 18 * n + 3) (S + 10 * k + 19 * n + 3) W := by
    refine ⟨by omega, by omega, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega,
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> omega
  -- 1. the setup
  obtain ⟨c₂, t₂, e₂, ht₂, hfr₂, hR9, hR10, hR11, g680, g690, g691, hz₂, hm₂, -⟩ :=
    setup10_exec (P := P) c₁ hc₁ hAR (by omega) hEW
  have hAR₂ : ARegs b k n c₂ := hAR.of_nreg hfr₂
  have Zr : ∀ a, S + n ≤ a → a < S + 10 * k + 21 * n + 4 → c₂.nmem a = 0 := fun a h1 h2 => by
    have := hz₂ (a - (S + n)) (by omega)
    rwa [show S + n + (a - (S + n)) = a by omega] at this
  have Lo : ∀ a, a < S + n → c₂.nmem a = c₁.nmem a := fun a h => hm₂ a (Or.inl h)
  -- 2. Miller's program
  obtain ⟨c₃, t₃, e₃, ht₃, T, T₁, l₀, l₂, K₀, cn, δ, x₀, xg, hl02, hl2s, h3, hK, -, -, -, -,
      hmk, hsep, h642, hm₃⟩ :=
    millerFull_spec (M := M.stellar.stellar) (cd := M.stellar.stCode (M.stCode c))
      (vi := M.stellar.stVi (M.stVi vn fn) (M.stFn c)) (A := fun x => c₁.nmem x)
      (V := fun x => c₁.nmem (11 * k + x)) (wSt M c fl) (P := P) (W := W) (c := c₂) (b := b)
      (bIm := S + n) (bMk := S + k + n) (bTmp := S + k + 2 * n) (bFc := S + k + 3 * n)
      (bA' := S + k + 6 * n + 1) (bL' := S + 2 * k + 6 * n + 1) (bS' := S + 3 * k + 6 * n + 1)
      (bSum' := S + 4 * k + 6 * n + 1) (bNx := S + k + 5 * n + 1)
      (bCy := S + 5 * k + 6 * n + 2) (bPos := S + 8 * k + 6 * n + 2)
      (bCv := S + 8 * k + 10 * n + 2) (bP1 := S + 8 * k + 11 * n + 2)
      (bI1 := S + 8 * k + 12 * n + 2) (bT1 := S + 9 * k + 13 * n + 2)
      (bF1 := S + 9 * k + 14 * n + 2) (bM1 := S + 9 * k + 12 * n + 2)
      (bP2 := S + 9 * k + 16 * n + 3) (bI2 := S + 9 * k + 17 * n + 3)
      (bT2 := S + 10 * k + 18 * n + 3) (bF2 := S + 10 * k + 19 * n + 3)
      (bM2 := S + 10 * k + 17 * n + 3)
      (isPlane_stellar (isPlane_stellar hM)) (M.stellar.isTriangle_stellar (stellar_loopless hl))
      (by omega) hA (M.stellar.stCode_phi3 (M.stCode c)) hV (sum_wSt_pos M c hd₀) hlay hWt hlay9
      hlay10 hlay11 e₂.wb_right hAR₂ hR9 hR10 hR11
      (fun x hx => Lo x (by omega))
      (fun x hx => by rw [hbV]; exact Lo _ (by omega))
      (fun v => by
        have := (M.stellar.stVi (M.stVi vn fn) (M.stFn c) v).2
        rw [Lo _ (by omega)]; exact hw v)
      (fun v hv => Zr _ (by omega) (by omega)) (fun x hx => Zr _ (by omega) (by omega))
      (fun v hv => Zr _ (by omega) (by omega)) (fun v hv => Zr _ (by omega) (by omega))
      (fun v hv => Zr _ (by omega) (by omega)) (fun v hv => Zr _ (by omega) (by omega))
  have hw₃ := e₃.wb_right
  have f₃ : ∀ r, 680 ≤ r → c₃.nreg r = c₂.nreg r := fun r hr =>
    e₃.nreg_of_wr (Stmt.wr_of_wmax (by have := millerFull_wmax; omega))
  -- 3. the `0`/`1` marks
  obtain ⟨c₄, t₄, e₄, ht₄, q394, q390, q393, hbit, hm₄⟩ :=
    marks01_exec (P := P) (k := k) (by omega) c₃ hw₃ ((f₃ 680 le_rfl).trans g680)
      (by omega)
  set R := bandSep T T₁ l₂ cn (wR (wSt M c fl)) δ x₀ (M.stellar.stellar.face xg)
  refine ⟨c₄, t₂ + (t₃ + t₄), .seq e₂ (.seq e₃ e₄), ?_, ?_, ?_, ?_, ?_, R.1, R.2, ?_,
    hsep.2.1, hsep.2.2.1, hsep.2.2.2, ?_⟩
  · -- the time
    have ht₂' : t₂ ≤ 50 * (3 * m) + 100 * (nV + nF + m) + 101 := ht₂
    have ht₄' : t₄ ≤ 13 * (3 * m) + 15 := ht₄
    have ht₃' : t₃ ≤ (231 * Nat.log 2 (nV + nF + m) + 1134) * (3 * m) +
        (60 * (nV + nF + m) + 152) * Nat.log 2 (nV + nF + m) + 278 * (nV + nF + m) + 637 +
        (113 * (3 * m) + 90 * (nV + nF + m) + 145) + (281 * (3 * m) + 51 * (nV + nF + m) + 69) +
        (226 * (3 * m) + 291 * (nV + nF + m) + 620) := ht₃
    have hX : (231 * Nat.log 2 (nV + nF + m) + 1134) * (3 * m) +
        (60 * (nV + nF + m) + 152) * Nat.log 2 (nV + nF + m) + 278 * (nV + nF + m) + 637 +
        (113 * (3 * m) + 90 * (nV + nF + m) + 145) + (281 * (3 * m) + 51 * (nV + nF + m) + 69) +
        (226 * (3 * m) + 291 * (nV + nF + m) + 620) =
        (693 * m + 60 * (nV + nF + m) + 152) * Nat.log 2 (nV + nF + m) + 5262 * m +
          710 * (nV + nF + m) + 1471 := by ring
    show t₂ + (t₃ + t₄) ≤ T10 m (nV + nF + m)
    unfold T10
    clear * - ht₂' ht₃' ht₄' hX
    omega
  · rw [q390, f₃ 690 (by omega), g690]
  · rw [q393, f₃ 691 (by omega), g691]
  · rw [q394]; omega
  · intro a ha
    rw [hm₄ a (Or.inr (by omega)), hm₃ a (by omega), hm₂ a (Or.inr (by omega))]
  · -- the number of darts
    have hk' : R.1.k ≤ 2 * (l₂ - l₀) + #K₀ + #(T.lvl l₂) := hsep.1
    have h3n : (Nat.sqrt (nV + nF + m) + 1) * #(T.lvl l₂) ≤ nV + nF + m := h3
    have hl2n : l₂ ≤ l₀ + 2 * Nat.sqrt (nV + nF + m) + 1 := hl2s
    show R.1.k ≤ 6 * Nat.sqrt (nV + nF + m) + 4
    have h3' := Map.le_sqrt_of_mul_le' h3n
    rcases hK with ⟨rfl, rfl⟩ | ⟨-, hK, hK'⟩
    · rw [card_singleton] at hk'; clear * - hk' h3' hl2n; omega
    · have hK'' : (Nat.sqrt (nV + nF + m) + 1) * #(T.lvl l₀) ≤ nV + nF + m := hK'
      have := (card_le_card hK).trans (Map.le_sqrt_of_mul_le' hK'')
      clear * - hk' h3' hl2n this; omega
  · -- the marks
    intro G
    have hfi : fi (M.stellar.stCode (M.stCode c)) G = M.stellar.stFn (M.stCode c) G := by
      unfold fi
      rw [← Map.stFn_face, (M.stellar.stellar.face_surjective G).choose_spec]
    have hlt : fi (M.stellar.stCode (M.stCode c)) G < k := by
      unfold fi
      have := (M.stellar.stCode (M.stCode c) (M.stellar.stellar.face_surjective G).choose).2
      omega
    rw [q394, ← hfi, hbit _ hlt]
    have key := hmk G
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (key.2 h1) h2
    · exact absurd (key.1 h2) h1
    · rfl

end Spec

end MillerProg

end PlanarSeparator
