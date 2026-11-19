module

public import PlanarFlow.BKMNW.NcSrtM
public import PlanarFlow.BKMNW.LinLoops

/-!
# The hole-flag program `hfP` of `c2sP`: the program and its blocks

From the hole labels `HL[t]` (`t < m`) of a frame and a hole index `i`, **`hfP`** writes
`F[t] = [HL[t] = v]` where `v` is the `i`-th smallest distinct positive label (`NcSrtM.lean`):

1. `hfCopy`: `A[t] := HL[t]`;
2. `hfSort`: a bottom-up merge sort between the buffers `A` and `B` (`r9760` the source,
   `r9761` the target, swapped after every pass; widths `w = 1, 2, 4, …` while `w < m`); one pass
   `hfPass` merges the blocks `[lo, mid)` and `[mid, hi)` (`mid = min (lo + w) m`,
   `hi = min (lo + 2w) m`) into the target, one word per step `mstep` (`List.merge`);
3. `hfScan`: the scan `dscan i` of the sorted buffer (`prev`, `cnt`, `v`);
4. `hfFlag`: `F[t] := 1 ∸ ((HL[t] ∸ v) + (v ∸ HL[t]))`.

Registers (natural words): inputs `9757` `m`, `9758` `HL` base, `9759` `i`, `9760` `A`,
`9761` `B`, `9762` `F` base; output `9763` `v`; scratch `9764 … 9782` (`9764 = 1`, `9766 = w`,
`9767 = lo`, `9768 = mid`, `9769 = hi`, `9770 = p`, `9771 = q`, `9772 = o`, `9773`, `9774` the
compared words, `9775` addresses, `9776` temporary, `9777 = 2w`, `9778 = t`, `9779 = prev`,
`9780 = cnt`, `9781`, `9782` temporaries).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### The program -/

/-- `A[t] := HL[t]`, `t := t + 1`. -/
def hfCopyB : Stmt :=
  block [.addN 9775 9758 9778, .loadN 9781 9775, .addN 9775 9760 9778, .storeN 9775 9781,
    .addN 9778 9778 9764]

/-- `1`, `t := 0`. -/
def hfCopyI : Stmt := block [.constN 9764 1, .constN 9778 0]

/-- The copy of the labels into the first buffer. -/
def hfCopy : Stmt := .seq hfCopyI (.whileLtN 9778 9757 hfCopyB)

/-- Take the word `p` of the left block: `T[o] := S[p]`. -/
def mTakeP : Stmt :=
  block [.addN 9775 9760 9770, .loadN 9773 9775, .addN 9775 9761 9772, .storeN 9775 9773,
    .addN 9770 9770 9764, .addN 9772 9772 9764]

/-- Take the word `q` of the right block: `T[o] := S[q]`. -/
def mTakeQ : Stmt :=
  block [.addN 9775 9760 9771, .loadN 9774 9775, .addN 9775 9761 9772, .storeN 9775 9774,
    .addN 9771 9771 9764, .addN 9772 9772 9764]

/-- Load the two heads. -/
def mLoad : Stmt :=
  block [.addN 9775 9760 9770, .loadN 9773 9775, .addN 9775 9760 9771, .loadN 9774 9775]

/-- **One step of the merge.** -/
def mstep : Stmt :=
  .ifLtN 9770 9768 (.ifLtN 9771 9769 (.seq mLoad (.ifLtN 9774 9773 mTakeQ mTakeP)) mTakeP) mTakeQ

/-- The bounds of a block: `mid = min (lo + w) m`, `hi = min (lo + 2w) m`, `p = lo`,
`q = mid`, `o = lo`. -/
def hfBlkA : Stmt :=
  block [.addN 9768 9767 9766, .subN 9776 9768 9757, .subN 9768 9768 9776,
    .addN 9769 9767 9777, .subN 9776 9769 9757, .subN 9769 9769 9776,
    .copyN 9770 9767, .copyN 9771 9768, .copyN 9772 9767]

/-- `lo := lo + 2w`. -/
def hfBlkB : Stmt := block [.addN 9767 9767 9777]

/-- One block of a pass. -/
def hfBlk : Stmt := .seq hfBlkA (.seq (.whileLtN 9772 9769 mstep) hfBlkB)

/-- `lo := 0`, `2w`. -/
def hfPassI : Stmt := block [.constN 9767 0, .addN 9777 9766 9766]

/-- **One pass** of the merge sort. -/
def hfPass : Stmt := .seq hfPassI (.whileLtN 9767 9757 hfBlk)

/-- Swap the buffers, `w := 2w`. -/
def hfSwap : Stmt := block [.copyN 9776 9760, .copyN 9760 9761, .copyN 9761 9776,
  .addN 9766 9766 9766]

/-- **The merge sort.** -/
def hfSort : Stmt := .seq (block [.constN 9766 1]) (.whileLtN 9766 9757 (.seq hfPass hfSwap))

/-- The update of the scan on a new value. -/
def hfScU : Stmt :=
  .seq (.ifLtN 9780 9759 .skip (.ifLtN 9759 9780 .skip (block [.copyN 9763 9781])))
    (block [.addN 9780 9780 9764, .copyN 9779 9781])

/-- `x := S[t]`. -/
def hfScL : Stmt := block [.addN 9775 9760 9778, .loadN 9781 9775]

/-- One step of the scan. -/
def hfScB : Stmt := .seq hfScL (.seq (.ifLtN 9779 9781 hfScU .skip) (block [.addN 9778 9778 9764]))

/-- `t := 0`, `prev := 0`, `cnt := 0`, `v := 0`. -/
def hfScI : Stmt := block [.constN 9778 0, .constN 9779 0, .constN 9780 0, .constN 9763 0]

/-- **The scan.** -/
def hfScan : Stmt := .seq hfScI (.whileLtN 9778 9757 hfScB)

/-- `F[t] := [HL[t] = v]`, `t := t + 1`. -/
def hfFlB : Stmt :=
  block [.addN 9775 9758 9778, .loadN 9781 9775, .subN 9782 9781 9763, .subN 9776 9763 9781,
    .addN 9782 9782 9776, .subN 9782 9764 9782, .addN 9775 9762 9778, .storeN 9775 9782,
    .addN 9778 9778 9764]

/-- **The flags.** -/
def hfFlag : Stmt := .seq (block [.constN 9778 0]) (.whileLtN 9778 9757 hfFlB)

/-- **The hole-flag program.** -/
def hfP : Stmt := .seq hfCopy (.seq hfSort (.seq hfScan hfFlag))

/-- The scratch registers of `hfP` (with the buffer registers and the output). -/
def HfScr (r : ℕ) : Prop := (r = 9760 ∨ r = 9761) ∨ (9763 ≤ r ∧ r ≤ 9782)

/-! ### The blocks of the merge -/

theorem mTakeP_exec (c : Config) (hc : WordsBounded W c) {S T p o : ℕ}
    (r60 : c.nreg 9760 = S) (r61 : c.nreg 9761 = T) (r64 : c.nreg 9764 = 1)
    (r70 : c.nreg 9770 = p) (r72 : c.nreg 9772 = o)
    (w1 : S + p ≤ W) (w2 : T + o ≤ W) (w3 : p + 1 ≤ W) (w4 : o + 1 ≤ W) :
    ∃ c' k, Exec P W mTakeP c c' k ∧ k = 6 ∧ c'.nmem = upd c.nmem (T + o) (c.nmem (S + p)) ∧
      c'.nreg 9770 = p + 1 ∧ c'.nreg 9772 = o + 1 ∧
      (∀ r, r ≠ 9770 → r ≠ 9772 → r ≠ 9773 → r ≠ 9775 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mTakeP
  exec_block
  all_goals try ((try config_simp); (try simp only [r60, r61, r64, r70, r72]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r60, r61, r70, r72]
  · config_simp; simp only [r64, r70]
  · config_simp; simp only [r64, r72]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem mTakeQ_exec (c : Config) (hc : WordsBounded W c) {S T q o : ℕ}
    (r60 : c.nreg 9760 = S) (r61 : c.nreg 9761 = T) (r64 : c.nreg 9764 = 1)
    (r71 : c.nreg 9771 = q) (r72 : c.nreg 9772 = o)
    (w1 : S + q ≤ W) (w2 : T + o ≤ W) (w3 : q + 1 ≤ W) (w4 : o + 1 ≤ W) :
    ∃ c' k, Exec P W mTakeQ c c' k ∧ k = 6 ∧ c'.nmem = upd c.nmem (T + o) (c.nmem (S + q)) ∧
      c'.nreg 9771 = q + 1 ∧ c'.nreg 9772 = o + 1 ∧
      (∀ r, r ≠ 9771 → r ≠ 9772 → r ≠ 9774 → r ≠ 9775 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mTakeQ
  exec_block
  all_goals try ((try config_simp); (try simp only [r60, r61, r64, r71, r72]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r60, r61, r71, r72]
  · config_simp; simp only [r64, r71]
  · config_simp; simp only [r64, r72]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem mLoad_exec (c : Config) (hc : WordsBounded W c) {S p q : ℕ}
    (r60 : c.nreg 9760 = S) (r70 : c.nreg 9770 = p) (r71 : c.nreg 9771 = q)
    (w1 : S + p ≤ W) (w2 : S + q ≤ W) :
    ∃ c' k, Exec P W mLoad c c' k ∧ k = 4 ∧ c'.nmem = c.nmem ∧
      c'.nreg 9773 = c.nmem (S + p) ∧ c'.nreg 9774 = c.nmem (S + q) ∧
      (∀ r, r ≠ 9773 → r ≠ 9774 → r ≠ 9775 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mLoad
  exec_block
  all_goals try ((try config_simp); (try simp only [r60, r70, r71]); omega)
  refine ⟨rfl, rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r60, r70]
  · config_simp; simp only [r60, r71]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- The choice of the merge: the left head when it exists and is at most the right one. -/
def mTakesP (mem : ℕ → ℕ) (S p q mid hi : ℕ) : Prop :=
  p < mid ∧ (hi ≤ q ∨ mem (S + p) ≤ mem (S + q))

/-- **One step of the merge.** -/
theorem mstep_exec (c : Config) (hc : WordsBounded W c) {S T p q o mid hi : ℕ}
    (r60 : c.nreg 9760 = S) (r61 : c.nreg 9761 = T) (r64 : c.nreg 9764 = 1)
    (r68 : c.nreg 9768 = mid) (r69 : c.nreg 9769 = hi)
    (r70 : c.nreg 9770 = p) (r71 : c.nreg 9771 = q) (r72 : c.nreg 9772 = o)
    (hpq : p < mid ∨ q < hi) (w1 : S + mid ≤ W) (w2 : S + hi ≤ W) (w3 : T + o ≤ W)
    (w4 : mid + 1 ≤ W) (w5 : hi + 1 ≤ W) (w6 : o + 1 ≤ W) :
    ∃ c' k, Exec P W mstep c c' k ∧ k ≤ 14 ∧ c'.nreg 9772 = o + 1 ∧
      (∀ r, r ≠ 9770 → r ≠ 9771 → r ≠ 9772 → r ≠ 9773 → r ≠ 9774 → r ≠ 9775 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      (mTakesP c.nmem S p q mid hi →
        c'.nmem = upd c.nmem (T + o) (c.nmem (S + p)) ∧ c'.nreg 9770 = p + 1 ∧
          c'.nreg 9771 = q) ∧
      (¬ mTakesP c.nmem S p q mid hi →
        c'.nmem = upd c.nmem (T + o) (c.nmem (S + q)) ∧ c'.nreg 9770 = p ∧
          c'.nreg 9771 = q + 1) := by
  unfold mstep
  by_cases hp : p < mid
  · by_cases hq : q < hi
    · obtain ⟨c₁, k₁, e₁, hk₁, m₁, a₁, b₁, g₁, rr₁, rm₁, o₁⟩ :=
        mLoad_exec (P := P) c hc r60 r70 r71 (by omega) (by omega)
      have q60 : c₁.nreg 9760 = S := by rw [g₁ _ (by omega) (by omega) (by omega), r60]
      have q61 : c₁.nreg 9761 = T := by rw [g₁ _ (by omega) (by omega) (by omega), r61]
      have q64 : c₁.nreg 9764 = 1 := by rw [g₁ _ (by omega) (by omega) (by omega), r64]
      have q70 : c₁.nreg 9770 = p := by rw [g₁ _ (by omega) (by omega) (by omega), r70]
      have q71 : c₁.nreg 9771 = q := by rw [g₁ _ (by omega) (by omega) (by omega), r71]
      have q72 : c₁.nreg 9772 = o := by rw [g₁ _ (by omega) (by omega) (by omega), r72]
      have hw₁ := e₁.wb_right
      by_cases hba : c.nmem (S + q) < c.nmem (S + p)
      · obtain ⟨c₂, k₂, e₂, hk₂, m₂, a₂, b₂, g₂, rr₂, rm₂, o₂⟩ :=
          mTakeQ_exec (P := P) c₁ hw₁ q60 q61 q64 q71 q72 (by omega) (by omega) (by omega)
            (by omega)
        have ht : ¬ mTakesP c.nmem S p q mid hi := by unfold mTakesP; omega
        refine ⟨c₂, _, .ifLtN_true (show c.nreg 9770 < c.nreg 9768 by rw [r70, r68]; exact hp)
          (.ifLtN_true (show c.nreg 9771 < c.nreg 9769 by rw [r71, r69]; exact hq) (.seq e₁ (.ifLtN_true (show c₁.nreg 9774 < c₁.nreg 9773 by rw [a₁, b₁]; exact hba)
            e₂))), by omega, b₂, fun r h1 h2 h3 h4 h5 h6 => ?_, by rw [rr₂, rr₁],
          by rw [rm₂, rm₁], by rw [o₂, o₁], fun h => absurd h ht, fun _ => ⟨?_, ?_, a₂⟩⟩
        · rw [g₂ r h2 h3 h5 h6, g₁ r h4 h5 h6]
        · rw [m₂, m₁]
        · rw [g₂ _ (by omega) (by omega) (by omega) (by omega), q70]
      · obtain ⟨c₂, k₂, e₂, hk₂, m₂, a₂, b₂, g₂, rr₂, rm₂, o₂⟩ :=
          mTakeP_exec (P := P) c₁ hw₁ q60 q61 q64 q70 q72 (by omega) (by omega) (by omega)
            (by omega)
        have ht : mTakesP c.nmem S p q mid hi := by unfold mTakesP; omega
        refine ⟨c₂, _, .ifLtN_true (show c.nreg 9770 < c.nreg 9768 by rw [r70, r68]; exact hp)
          (.ifLtN_true (show c.nreg 9771 < c.nreg 9769 by rw [r71, r69]; exact hq) (.seq e₁ (.ifLtN_false (show ¬ c₁.nreg 9774 < c₁.nreg 9773 by rw [a₁, b₁]; exact hba)
            e₂))), by omega, b₂, fun r h1 h2 h3 h4 h5 h6 => ?_, by rw [rr₂, rr₁],
          by rw [rm₂, rm₁], by rw [o₂, o₁], fun _ => ⟨?_, a₂, ?_⟩, fun h => absurd ht h⟩
        · rw [g₂ r h1 h3 h4 h6, g₁ r h4 h5 h6]
        · rw [m₂, m₁]
        · rw [g₂ _ (by omega) (by omega) (by omega) (by omega), q71]
    · obtain ⟨c₂, k₂, e₂, hk₂, m₂, a₂, b₂, g₂, rr₂, rm₂, o₂⟩ :=
        mTakeP_exec (P := P) c hc r60 r61 r64 r70 r72 (by omega) (by omega) (by omega)
          (by omega)
      have ht : mTakesP c.nmem S p q mid hi := by unfold mTakesP; omega
      refine ⟨c₂, _, .ifLtN_true (show c.nreg 9770 < c.nreg 9768 by rw [r70, r68]; exact hp)
        (.ifLtN_false (show ¬ c.nreg 9771 < c.nreg 9769 by rw [r71, r69]; exact hq) e₂), by omega, b₂,
        fun r h1 h2 h3 h4 h5 h6 => g₂ r h1 h3 h4 h6, rr₂, rm₂, o₂,
        fun _ => ⟨m₂, a₂, by rw [g₂ _ (by omega) (by omega) (by omega) (by omega), r71]⟩,
        fun h => absurd ht h⟩
  · obtain ⟨c₂, k₂, e₂, hk₂, m₂, a₂, b₂, g₂, rr₂, rm₂, o₂⟩ :=
      mTakeQ_exec (P := P) c hc r60 r61 r64 r71 r72 (by omega) (by omega) (by omega)
        (by omega)
    have ht : ¬ mTakesP c.nmem S p q mid hi := by unfold mTakesP; omega
    refine ⟨c₂, _, .ifLtN_false (show ¬ c.nreg 9770 < c.nreg 9768 by rw [r70, r68]; exact hp) e₂, by omega, b₂,
      fun r h1 h2 h3 h4 h5 h6 => g₂ r h2 h3 h5 h6, rr₂, rm₂, o₂, fun h => absurd h ht,
      fun _ => ⟨m₂, by rw [g₂ _ (by omega) (by omega) (by omega) (by omega), r70], a₂⟩⟩

/-! ### The other blocks -/

theorem hfBlkA_exec (c : Config) (hc : WordsBounded W c) {m lo w : ℕ}
    (r57 : c.nreg 9757 = m) (r66 : c.nreg 9766 = w) (r67 : c.nreg 9767 = lo)
    (r77 : c.nreg 9777 = 2 * w) (w1 : lo + 2 * w ≤ W) :
    ∃ c' k, Exec P W hfBlkA c c' k ∧ k = 9 ∧ c'.nreg 9768 = min (lo + w) m ∧
      c'.nreg 9769 = min (lo + 2 * w) m ∧ c'.nreg 9770 = lo ∧ c'.nreg 9771 = min (lo + w) m ∧
      c'.nreg 9772 = lo ∧
      (∀ r, r ≠ 9768 → r ≠ 9769 → r ≠ 9770 → r ≠ 9771 → r ≠ 9772 → r ≠ 9776 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hfBlkA
  exec_block
  all_goals try ((try config_simp); (try simp only [r57, r66, r67, r77]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r57, r66, r67, r77]; omega)
  all_goals (try simp only [upd_apply]) <;> (try split_ifs) <;> omega

theorem hfBlkB_exec (c : Config) (hc : WordsBounded W c) {lo w : ℕ}
    (r67 : c.nreg 9767 = lo) (r77 : c.nreg 9777 = 2 * w) (w1 : lo + 2 * w ≤ W) :
    ∃ c' k, Exec P W hfBlkB c c' k ∧ k = 1 ∧ c'.nreg 9767 = lo + 2 * w ∧
      (∀ r, r ≠ 9767 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hfBlkB
  exec_block
  all_goals try ((try config_simp); (try simp only [r67, r77]); omega)
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r67, r77]
  · simp only [upd_apply]; split_ifs <;> omega

theorem hfPassI_exec (c : Config) (hc : WordsBounded W c) {w : ℕ}
    (r66 : c.nreg 9766 = w) (w1 : 2 * w ≤ W) :
    ∃ c' k, Exec P W hfPassI c c' k ∧ k = 2 ∧ c'.nreg 9767 = 0 ∧ c'.nreg 9777 = 2 * w ∧
      (∀ r, r ≠ 9767 → r ≠ 9777 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hfPassI
  exec_block
  all_goals try ((try config_simp); (try simp only [r66]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r66]; omega
  · simp only [upd_apply]; split_ifs <;> omega

theorem hfSwap_exec (c : Config) (hc : WordsBounded W c) {S T w : ℕ}
    (r60 : c.nreg 9760 = S) (r61 : c.nreg 9761 = T) (r66 : c.nreg 9766 = w) (w1 : 2 * w ≤ W) :
    ∃ c' k, Exec P W hfSwap c c' k ∧ k = 4 ∧ c'.nreg 9760 = T ∧ c'.nreg 9761 = S ∧
      c'.nreg 9766 = 2 * w ∧
      (∀ r, r ≠ 9760 → r ≠ 9761 → r ≠ 9766 → r ≠ 9776 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hfSwap
  exec_block
  all_goals try ((try config_simp); (try simp only [r60, r61, r66]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r61]
  · simp only [r60]
  · simp only [r66]; omega
  · simp only [upd_apply]; split_ifs <;> omega

theorem hfCopyI_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' k, Exec P W hfCopyI c c' k ∧ k = 2 ∧ c'.nreg 9764 = 1 ∧ c'.nreg 9778 = 0 ∧
      (∀ r, r ≠ 9764 → r ≠ 9778 → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hfCopyI
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem hfCopyB_exec (c : Config) (hc : WordsBounded W c) {HLb S t : ℕ}
    (r58 : c.nreg 9758 = HLb) (r60 : c.nreg 9760 = S) (r64 : c.nreg 9764 = 1)
    (r78 : c.nreg 9778 = t) (w1 : HLb + t ≤ W) (w2 : S + t ≤ W) (w3 : t + 1 ≤ W) :
    ∃ c' k, Exec P W hfCopyB c c' k ∧ k = 5 ∧ c'.nmem = upd c.nmem (S + t) (c.nmem (HLb + t)) ∧
      c'.nreg 9778 = t + 1 ∧
      (∀ r, r ≠ 9775 → r ≠ 9778 → r ≠ 9781 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold hfCopyB
  exec_block
  all_goals try ((try config_simp); (try simp only [r58, r60, r64, r78]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r58, r60, r78]
  · simp only [r64, r78]
  · simp only [upd_apply]; split_ifs <;> omega

/-- The flag word. -/
def hfFlagW (x v : ℕ) : ℕ := 1 - ((x - v) + (v - x))

lemma hfFlagW_eq (x v : ℕ) : hfFlagW x v = if x = v then 1 else 0 := by
  unfold hfFlagW; split_ifs <;> omega

theorem hfFlB_exec (c : Config) (hc : WordsBounded W c) {HLb Fb v t : ℕ}
    (r58 : c.nreg 9758 = HLb) (r62 : c.nreg 9762 = Fb) (r63 : c.nreg 9763 = v)
    (r64 : c.nreg 9764 = 1) (r78 : c.nreg 9778 = t) (w1 : HLb + t ≤ W) (w2 : Fb + t ≤ W)
    (w3 : t + 1 ≤ W) :
    ∃ c' k, Exec P W hfFlB c c' k ∧ k = 9 ∧
      c'.nmem = upd c.nmem (Fb + t) (hfFlagW (c.nmem (HLb + t)) v) ∧
      c'.nreg 9778 = t + 1 ∧
      (∀ r, r ≠ 9775 → r ≠ 9776 → r ≠ 9778 → r ≠ 9781 → r ≠ 9782 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hv : v ≤ W := by rw [← r63]; exact hc.1 _
  have hx : c.nmem (HLb + t) ≤ W := hc.2 _
  unfold hfFlB
  exec_block
  all_goals try ((try config_simp); (try simp only [r58, r62, r63, r64, r78]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 h4 h5 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r58, r62, r63, r64, r78, hfFlagW]
  · simp only [r64, r78]
  · simp only [upd_apply]; split_ifs <;> omega

end NcStep

end BKMNW

end PlanarFlow
