module

public import PlanarFlow.BKMNW.FrImA
public import PlanarFlow.BKMNW.StDkRun

/-!
# The FR image, part B: the memory phases

With the parameters of `FrImA.lean` in the registers (`r8112 = 1`, `r8113 = pb`, `r8114 = ob`,
`r8116 = sb`, `r8124 = M`, `r8125 = M - K mod M`, `r8126 = A + sb`), natural words only:

* `fiZ`: zero the image `[A, A + 2 sb)` (`mzFill`);
* `fiO`: the keep flags `1` at `[S, S + mE)` (`onesProg`);
* `fiS`: the counting sort of the arcs by tail (`osProg`, scratch from `S + mE`): the offsets
  `OB` at `r8141 = OBb` and the sorted arc indices `SI` at `r8142 = SIb`;
* `fiOff`: the offsets `OB[x]` to `A + ob + x` (`x < b`), and `mE` to `A + ob + b` (`cpArr`);
* `fiDst`: the heads `EH[SI[e]]` to `A + ob + b + 1 + e` (`e < mE`);
* `fiMat`: the matrix `DM` to `A + sb` (`cpArr`, `b²` words);
* `fiPr`: the residues `(PR[x] + K') mod M` to `A + sb + pb + x` (`x < b`);
* `fiLn`: the residues `(EL[SI[e]] + K') mod M` to `A + sb + lb + e` (`e < mE`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Monge.FR NegSSSP

/-! ### The programs -/

/-- Zero the image `[A, A + 2 sb)`. -/
def fiZ : Stmt := .seq (block [.addN 5030 8116 8116, .copyN 5031 8110]) mzFill

/-- The keep flags `1` at `[S, S + mE)`. -/
def fiO : Stmt := .seq (block [.copyN 7861 8104, .copyN 7865 8111]) onesProg

/-- The counting sort of the arcs by tail. -/
def fiS : Stmt := .seq (block [.copyN 1500 8104, .copyN 1501 8100, .copyN 1502 8105,
  .copyN 1504 8111, .addN 1505 8111 8104, .addN 1506 1505 8100, .addN 1506 1506 8112,
  .addN 1507 1506 8100, .addN 1508 1507 8100, .addN 1509 1508 8100, .copyN 8141 1507,
  .copyN 8142 1509]) osProg

/-- The offsets. -/
def fiOff : Stmt := .seq (block [.copyN 4910 8100, .copyN 4911 8141, .addN 4912 8110 8114])
  (.seq cpArr (block [.addN 8143 8110 8114, .addN 8143 8143 8100, .storeN 8143 8104]))

/-- The body of `fiDst`. -/
def fiDstBody : Stmt := block [.addN 8145 8142 8140, .loadN 8146 8145, .addN 8145 8106 8146,
  .loadN 8147 8145, .addN 8145 8144 8140, .storeN 8145 8147, .addN 8140 8140 8112]

/-- The heads of the sorted arcs. -/
def fiDst : Stmt := .seq (block [.addN 8144 8110 8114, .addN 8144 8144 8100,
  .addN 8144 8144 8112, .constN 8140 0]) (.whileLtN 8140 8104 fiDstBody)

/-- The matrix. -/
def fiMat : Stmt := .seq (block [.copyN 4910 8113, .copyN 4911 8101, .copyN 4912 8126]) cpArr

/-- The body of `fiPr`. -/
def fiPrBody : Stmt := block [.addN 8145 8102 8140, .loadN 8146 8145, .addN 8146 8146 8125,
  .modN 8146 8146 8124, .addN 8145 8148 8140, .storeN 8145 8146, .addN 8140 8140 8112]

/-- The residues of the prices. -/
def fiPr : Stmt := .seq (block [.addN 8148 8126 8113, .constN 8140 0])
  (.whileLtN 8140 8100 fiPrBody)

/-- The body of `fiLn`. -/
def fiLnBody : Stmt := block [.addN 8145 8142 8140, .loadN 8146 8145, .addN 8145 8107 8146,
  .loadN 8147 8145, .addN 8147 8147 8125, .modN 8147 8147 8124, .addN 8145 8149 8140,
  .storeN 8145 8147, .addN 8140 8140 8112]

/-- The residues of the lengths of the sorted arcs. -/
def fiLn : Stmt := .seq (block [.addN 8149 8126 8115, .constN 8140 0])
  (.whileLtN 8140 8104 fiLnBody)

/-! ### The phases -/

section Phases

variable {P : Input} {W : ℕ}

theorem fiZ_exec (c : Config) (hc : WordsBounded W c) {A sb : ℕ} (r16 : c.nreg 8116 = sb)
    (r10 : c.nreg 8110 = A) (hW : A + (sb + sb) + 1 ≤ W) :
    ∃ c' t, Exec P W fiZ c c' t ∧ t ≤ 10 * sb + 7 ∧
      (∀ i < sb + sb, c'.nmem (A + i) = 0) ∧
      (∀ a, (a < A ∨ A + (sb + sb) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 5030 ∨ 5035 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a30, a31, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.addN 5030 8116 8116, .copyN 5031 8110]) c c₁ t₁ ∧ t₁ = 2 ∧
        c₁.nreg 5030 = sb + sb ∧ c₁.nreg 5031 = A ∧
        (∀ r, r ≠ 5030 → r ≠ 5031 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r16, r10]); omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r16, r10])
    repeat rw [upd_other _ _ _ (by omega)]
  obtain ⟨c₂, t₂, e₂, ht₂, bz, bk, bn, br, brm, bo⟩ :=
    mzFill_exec (P := P) c₁ e₁.wb_right a30 a31 (by omega) (by omega)
  refine ⟨c₂, _, e₁.seq e₂, by omega, bz, fun a ha => by rw [bk a ha, am], fun r hr => ?_,
    by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
  rw [bn r (by omega), ak r (by omega) (by omega)]

theorem fiO_exec (c : Config) (hc : WordsBounded W c) {S mE : ℕ} (r04 : c.nreg 8104 = mE)
    (r11 : c.nreg 8111 = S) (hW : S + mE + 1 ≤ W) :
    ∃ c' t, Exec P W fiO c c' t ∧ t ≤ 5 * mE + 6 ∧
      (∀ y < mE, c'.nmem (S + y) = 1) ∧ (∀ a, a < S ∨ S + mE ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 7861 → r ≠ 7865 → (r < 7873 ∨ 7876 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a61, a65, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.copyN 7861 8104, .copyN 7865 8111]) c c₁ t₁ ∧ t₁ = 2 ∧
        c₁.nreg 7861 = mE ∧ c₁.nreg 7865 = S ∧
        (∀ r, r ≠ 7861 → r ≠ 7865 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r04, r11])
    repeat rw [upd_other _ _ _ (by omega)]
  obtain ⟨c₂, t₂, e₂, ht₂, b1, bk, bn, br, brm, bo⟩ :=
    onesProg_exec (P := P) (n := mE) (Ab := S) (by omega) (by omega) c₁ e₁.wb_right a61 a65
  refine ⟨c₂, _, e₁.seq e₂, by omega, b1, fun a ha => by rw [bk a ha, am], fun r h1 h2 h3 => ?_,
    by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
  rw [bn r h3, ak r h1 h2]

/-- The keys of the sorted arcs: `csList ET id 1 0 mE` (`osProg` sorts the indices). -/
noncomputable abbrev fiL (ET : ℕ → ℕ) (mE : ℕ) : List (ℕ × ℕ × ℤ) :=
  csList ET id (fun _ => 1) (fun _ => 0) mE

theorem fiS_exec (c : Config) (hc : WordsBounded W c) {b mE ETb S : ℕ} {ET : ℕ → ℕ}
    (r00 : c.nreg 8100 = b) (r04 : c.nreg 8104 = mE) (r05 : c.nreg 8105 = ETb)
    (r11 : c.nreg 8111 = S) (r12 : c.nreg 8112 = 1)
    (het : ∀ a < mE, c.nmem (ETb + a) = ET a) (hone : ∀ a < mE, c.nmem (S + a) = 1)
    (hlt : ∀ a < mE, ET a < b) (hET : ETb + mE ≤ S) (hW : S + mE + mE + 4 * b + 2 ≤ W) :
    ∃ c' t, Exec P W fiS c c' t ∧ t ≤ osCost mE b + 12 ∧
      c'.nreg 8141 = S + mE + b + 1 + b ∧ c'.nreg 8142 = S + mE + b + 1 + b + b + b ∧
      (∀ x < b, c'.nmem (S + mE + b + 1 + b + x) = (pre (fiL ET mE) x).length) ∧
      (∀ e < (pre (fiL ET mE) b).length,
        c'.nmem (S + mE + b + 1 + b + b + b + e) = ((pre (fiL ET mE) b).getD e (0, 0, 0)).2.1) ∧
      (∀ a, (a < S + mE ∨ S + mE + mE + 4 * b + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 1500 ∨ 1520 < r) → r ≠ 8141 → r ≠ 8142 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a01, a02, a04, a05, a06, a07, a08, a09, a41, a42, ak, am, ar,
      arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.copyN 1500 8104, .copyN 1501 8100, .copyN 1502 8105,
        .copyN 1504 8111, .addN 1505 8111 8104, .addN 1506 1505 8100, .addN 1506 1506 8112,
        .addN 1507 1506 8100, .addN 1508 1507 8100, .addN 1509 1508 8100, .copyN 8141 1507,
        .copyN 8142 1509]) c c₁ t₁ ∧ t₁ = 12 ∧
        c₁.nreg 1500 = mE ∧ c₁.nreg 1501 = b ∧ c₁.nreg 1502 = ETb ∧ c₁.nreg 1504 = S ∧
        c₁.nreg 1505 = S + mE ∧ c₁.nreg 1506 = S + mE + b + 1 ∧
        c₁.nreg 1507 = S + mE + b + 1 + b ∧ c₁.nreg 1508 = S + mE + b + 1 + b + b ∧
        c₁.nreg 1509 = S + mE + b + 1 + b + b + b ∧
        c₁.nreg 8141 = S + mE + b + 1 + b ∧ c₁.nreg 8142 = S + mE + b + 1 + b + b + b ∧
        (∀ r, (r < 1500 ∨ 1509 < r) → r ≠ 8141 → r ≠ 8142 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r00, r04, r05, r11, r12]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl,
      rfl⟩
    all_goals config_simp
    all_goals try (simp only [r00, r04, r05, r11, r12] <;> omega)
    repeat rw [upd_other _ _ _ (by omega)]
  have hL : OsLay mE b ETb S (S + mE) (S + mE + b + 1) (S + mE + b + 1 + b)
      (S + mE + b + 1 + b + b) (S + mE + b + 1 + b + b + b) W ET (fun _ => 1) :=
    { tlt := fun i hi _ => hlt i hi, cb := rfl, sT := Or.inr (by omega),
      sK := Or.inr (by omega), sO := Or.inl (by omega), bE := le_rfl, eD := le_rfl,
      dT := Or.inr (by omega), dK := Or.inr (by omega), wT := by omega, wK := by omega,
      wD := by omega, wS := by omega, wM := by omega, wN := by omega }
  have hI : OsIn mE b ETb S (S + mE) (S + mE + b + 1) (S + mE + b + 1 + b)
      (S + mE + b + 1 + b + b) (S + mE + b + 1 + b + b + b) ET (fun _ => 1) c₁ :=
    ⟨a00, a01, a02, a04, a05, a06, a07, a08, a09, fun i hi => by rw [am]; exact het i hi,
      fun i hi => by rw [am]; exact hone i hi⟩
  obtain ⟨c₂, t₂, e₂, ht₂, bOB, bSI, bk, bn, br, brm, bo⟩ :=
    osProg_exec (P := P) hL c₁ e₁.wb_right hI
  refine ⟨c₂, _, e₁.seq e₂, by omega, by rw [bn _ (by omega), a41],
    by rw [bn _ (by omega), a42], fun x hx => (bOB x hx).1, bSI, fun a ha => ?_,
    fun r h1 h2 h3 => ?_, by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
  · rw [bk a (by omega) (by omega), am]
  · rw [bn r (by omega), ak r (by omega) h2 h3]

theorem fiOff_exec (c : Config) (hc : WordsBounded W c) {b mE A ob OBb : ℕ}
    (r00 : c.nreg 8100 = b) (r04 : c.nreg 8104 = mE) (r10 : c.nreg 8110 = A)
    (r14 : c.nreg 8114 = ob) (r41 : c.nreg 8141 = OBb)
    (hsep : OBb + b ≤ A ∨ A + ob + b + 1 ≤ OBb) (hW1 : OBb + b ≤ W) (hW2 : A + ob + b + 1 ≤ W)
    (hW3 : mE ≤ W) :
    ∃ c' t, Exec P W fiOff c c' t ∧ t ≤ 7 * b + 10 ∧
      (∀ x < b, c'.nmem (A + ob + x) = c.nmem (OBb + x)) ∧ c'.nmem (A + ob + b) = mE ∧
      (∀ a, (a < A + ob ∨ A + ob + b + 1 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 4910 ∨ 4916 < r) → r ≠ 8143 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a10, a11, a12, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.copyN 4910 8100, .copyN 4911 8141, .addN 4912 8110 8114]) c c₁ t₁ ∧
        t₁ = 3 ∧ c₁.nreg 4910 = b ∧ c₁.nreg 4911 = OBb ∧ c₁.nreg 4912 = A + ob ∧
        (∀ r, (r < 4910 ∨ 4912 < r) → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r00, r41, r10, r14]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r00, r41, r10, r14])
    repeat rw [upd_other _ _ _ (by omega)]
  obtain ⟨c₂, t₂, e₂, ht₂, bcp, bk, bn, br, brm, bo⟩ :=
    cpArr_exec (P := P) (n := b) (Sb := OBb) (Db := A + ob) c₁ e₁.wb_right a10 a11 a12
      ⟨by omega, by omega, by omega, by omega⟩
  have k2 : ∀ r, (r < 4910 ∨ 4916 < r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [bn r (by omega), ak r (by omega)]
  have hw₂ := e₂.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, dm, dk, dr, drm, do'⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 8143 8110 8114, .addN 8143 8143 8100, .storeN 8143 8104]) c₂ c₃ t₃ ∧
        t₃ = 3 ∧ c₃.nmem = upd c₂.nmem (A + ob + b) mE ∧
        (∀ r, r ≠ 8143 → c₃.nreg r = c₂.nreg r) ∧
        c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [k2 8110 (by omega), k2 8114 (by omega),
      k2 8100 (by omega), r00, r10, r14]); omega)
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    · simp only [k2 8110 (by omega), k2 8114 (by omega), k2 8100 (by omega), k2 8104 (by omega),
        r00, r10, r14, r04]
    · repeat rw [upd_other _ _ _ (by omega)]
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), by omega, fun x hx => ?_, ?_, fun a ha => ?_,
    fun r h1 h2 => ?_, by rw [dr, br, ar], by rw [drm, brm, arm], by rw [do', bo, ao]⟩
  · rw [dm, upd_other _ _ _ (by omega), bcp x hx, am]
  · rw [dm, upd_same]
  · rw [dm, upd_other _ _ _ (by omega), bk a (by omega), am]
  · rw [dk r h2, k2 r h1]

theorem fiDstBody_exec (c : Config) (hc : WordsBounded W c) {e SIb EHb Bb : ℕ}
    (r40 : c.nreg 8140 = e) (r42 : c.nreg 8142 = SIb) (r06 : c.nreg 8106 = EHb)
    (r44 : c.nreg 8144 = Bb) (r12 : c.nreg 8112 = 1) (w1 : SIb + e ≤ W)
    (w2 : EHb + c.nmem (SIb + e) ≤ W) (w3 : Bb + e ≤ W) (w4 : e + 1 ≤ W) :
    ∃ c' t, Exec P W fiDstBody c c' t ∧ t = 7 ∧ c'.nreg 8140 = e + 1 ∧
      c'.nmem = upd c.nmem (Bb + e) (c.nmem (EHb + c.nmem (SIb + e))) ∧
      (∀ r, (r < 8145 ∨ 8147 < r) → r ≠ 8140 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fiDstBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r40, r42, r06, r44, r12]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r40, r12]
  · simp only [r40, r42, r06, r44]
  · repeat rw [upd_other _ _ _ (by omega)]

/-- **The heads of the sorted arcs**: `Bb + e ↦ EH[SI[e]]`, `Bb = A + ob + b + 1`. -/
theorem fiDst_exec (c : Config) (hc : WordsBounded W c) {b mE A ob SIb EHb : ℕ}
    (r00 : c.nreg 8100 = b) (r04 : c.nreg 8104 = mE) (r10 : c.nreg 8110 = A)
    (r14 : c.nreg 8114 = ob) (r42 : c.nreg 8142 = SIb) (r06 : c.nreg 8106 = EHb)
    (r12 : c.nreg 8112 = 1)
    (hSI : SIb + mE ≤ A + ob + b + 1 ∨ A + ob + b + 1 + mE ≤ SIb)
    (hEH : ∀ e < mE, EHb + c.nmem (SIb + e) ≤ W ∧
      (EHb + c.nmem (SIb + e) < A + ob + b + 1 ∨ A + ob + b + 1 + mE ≤ EHb + c.nmem (SIb + e)))
    (hW1 : A + ob + b + 1 + mE + 1 ≤ W) (hW2 : SIb + mE ≤ W) :
    ∃ c' t, Exec P W fiDst c c' t ∧ t ≤ 9 * mE + 6 ∧
      (∀ e < mE, c'.nmem (A + ob + b + 1 + e) = c.nmem (EHb + c.nmem (SIb + e))) ∧
      (∀ a, (a < A + ob + b + 1 ∨ A + ob + b + 1 + mE ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 8140 ∨ 8147 < r) → c'.nreg r = c.nreg r) ∧ c'.nreg 8142 = SIb ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a44, a40, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.addN 8144 8110 8114, .addN 8144 8144 8100, .addN 8144 8144 8112,
        .constN 8140 0]) c c₁ t₁ ∧ t₁ = 4 ∧ c₁.nreg 8144 = A + ob + b + 1 ∧ c₁.nreg 8140 = 0 ∧
        (∀ r, r ≠ 8144 → r ≠ 8140 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r00, r10, r14, r12]); omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r00, r10, r14, r12])
    repeat rw [upd_other _ _ _ (by omega)]
  set Bb := A + ob + b + 1 with hBb
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Bb + e) = c.nmem (EHb + c.nmem (SIb + e))) ∧
      (∀ a, (a < Bb ∨ Bb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 8140 ∨ 8147 < r) → c'.nreg r = c.nreg r) ∧ c'.nreg 8144 = Bb ∧
      c'.nreg 8142 = SIb ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, -, g1, g2, g3, -, g42f, g5, g6, g7⟩ :=
    forLoop_exec (P := P) (a := 8140) (bR := 8104) (body := fiDstBody) J (K := 7) (n := mE) c₁
      e₁.wb_right a40 (by rw [ak _ (by omega) (by omega), r04])
      ⟨fun e he => absurd he (by omega), fun a _ => by rw [am], fun r hr => ak r (by omega)
        (by omega), a44, by rw [ak _ (by omega) (by omega), r42], ar, arm, ao⟩
      (fun i c' hi hw ha hb hJ => by
        obtain ⟨g1, g2, g3, g4, g42, g5, g6, g7⟩ := hJ
        have hSIe : c'.nmem (SIb + i) = c.nmem (SIb + i) := g2 _ (by omega)
        obtain ⟨c'', t, e, ht, b40, bm, bk, br, brm, bo⟩ :=
          fiDstBody_exec (P := P) c' hw ha g42
            (by rw [g3 _ (by omega), r06]) g4 (by rw [g3 _ (by omega), r12]) (by omega)
            (by rw [hSIe]; exact (hEH i hi).1) (by omega) (by omega)
        refine ⟨c'', t, e, by omega, b40, by rw [bk _ (by omega) (by omega), hb],
          fun e' he' => ?_, fun a ha' => ?_, fun r hr => ?_, by rw [bk _ (by omega) (by omega), g4],
          by rw [bk _ (by omega) (by omega), g42], by rw [br, g5], by rw [brm, g6], by rw [bo, g7]⟩
        · rw [bm]
          by_cases h : e' = i
          · subst h
            rw [upd_same, hSIe, g2 _ ((hEH e' hi).2.imp_right (fun h => by omega))]
          · rw [upd_other _ _ _ (by omega), g1 e' (by omega)]
        · rw [bm, upd_other _ _ _ (by omega), g2 a (by omega)]
        · rw [bk r (by omega) (by omega), g3 r hr])
  exact ⟨c₂, _, e₁.seq e₂, by omega, g1, fun a ha => g2 a ha, g3, g42f, g5, g6, g7⟩

theorem fiMat_exec (c : Config) (hc : WordsBounded W c) {b DMb As : ℕ}
    (r13 : c.nreg 8113 = b * b) (r01 : c.nreg 8101 = DMb) (r26 : c.nreg 8126 = As)
    (hsep : DMb + b * b ≤ As ∨ As + b * b ≤ DMb) (hW1 : DMb + b * b ≤ W) (hW2 : As + b * b ≤ W)
    (hW3 : b * b + 1 ≤ W) :
    ∃ c' t, Exec P W fiMat c c' t ∧ t ≤ 7 * (b * b) + 7 ∧
      (∀ i < b * b, c'.nmem (As + i) = c.nmem (DMb + i)) ∧
      (∀ a, (a < As ∨ As + b * b ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 4910 ∨ 4916 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a10, a11, a12, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.copyN 4910 8113, .copyN 4911 8101, .copyN 4912 8126]) c c₁ t₁ ∧
        t₁ = 3 ∧ c₁.nreg 4910 = b * b ∧ c₁.nreg 4911 = DMb ∧ c₁.nreg 4912 = As ∧
        (∀ r, (r < 4910 ∨ 4912 < r) → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r13, r01, r26])
    repeat rw [upd_other _ _ _ (by omega)]
  obtain ⟨c₂, t₂, e₂, ht₂, bcp, bk, bn, br, brm, bo⟩ :=
    cpArr_exec (P := P) (n := b * b) (Sb := DMb) (Db := As) c₁ e₁.wb_right a10 a11 a12
      ⟨hsep, by omega, by omega, by omega⟩
  refine ⟨c₂, _, e₁.seq e₂, by omega, fun i hi => by rw [bcp i hi, am], fun a ha => by
    rw [bk a ha, am], fun r hr => by rw [bn r (by omega), ak r (by omega)], by rw [br, ar],
    by rw [brm, arm], by rw [bo, ao]⟩

theorem fiPrBody_exec (c : Config) (hc : WordsBounded W c) {x PRb Bb Kp Mo : ℕ}
    (r40 : c.nreg 8140 = x) (r02 : c.nreg 8102 = PRb) (r48 : c.nreg 8148 = Bb)
    (r25 : c.nreg 8125 = Kp) (r24 : c.nreg 8124 = Mo) (r12 : c.nreg 8112 = 1)
    (w1 : PRb + x ≤ W) (w2 : c.nmem (PRb + x) + Kp ≤ W) (w3 : Bb + x ≤ W) (w4 : x + 1 ≤ W) :
    ∃ c' t, Exec P W fiPrBody c c' t ∧ t = 7 ∧ c'.nreg 8140 = x + 1 ∧
      c'.nmem = upd c.nmem (Bb + x) ((c.nmem (PRb + x) + Kp) % Mo) ∧
      (∀ r, (r < 8145 ∨ 8146 < r) → r ≠ 8140 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fiPrBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r40, r02, r48, r25, r24, r12]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r40, r12]
  · simp only [r40, r02, r48, r25, r24]
  · repeat rw [upd_other _ _ _ (by omega)]

/-- **The residues of the prices**: `Bb + x ↦ (PR[x] + K') mod M`, `Bb = A + sb + pb`. -/
theorem fiPr_exec (c : Config) (hc : WordsBounded W c) {b As pb PRb Kp Mo : ℕ}
    (r00 : c.nreg 8100 = b) (r26 : c.nreg 8126 = As) (r13 : c.nreg 8113 = pb)
    (r02 : c.nreg 8102 = PRb) (r25 : c.nreg 8125 = Kp) (r24 : c.nreg 8124 = Mo)
    (r12 : c.nreg 8112 = 1)
    (hsep : PRb + b ≤ As + pb ∨ As + pb + b ≤ PRb)
    (hPR : ∀ x < b, c.nmem (PRb + x) + Kp ≤ W) (hW1 : As + pb + b ≤ W) (hW2 : PRb + b ≤ W)
    (hW3 : b + 1 ≤ W) :
    ∃ c' t, Exec P W fiPr c c' t ∧ t ≤ 9 * b + 4 ∧
      (∀ x < b, c'.nmem (As + pb + x) = (c.nmem (PRb + x) + Kp) % Mo) ∧
      (∀ a, (a < As + pb ∨ As + pb + b ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 8140 → r ≠ 8145 → r ≠ 8146 → r ≠ 8148 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a48, a40, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.addN 8148 8126 8113, .constN 8140 0]) c c₁ t₁ ∧ t₁ = 2 ∧
        c₁.nreg 8148 = As + pb ∧ c₁.nreg 8140 = 0 ∧
        (∀ r, r ≠ 8148 → r ≠ 8140 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r26, r13]); omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r26, r13])
    repeat rw [upd_other _ _ _ (by omega)]
  set Bb := As + pb with hBb
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x < i, c'.nmem (Bb + x) = (c.nmem (PRb + x) + Kp) % Mo) ∧
      (∀ a, (a < Bb ∨ Bb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 8140 → r ≠ 8145 → r ≠ 8146 → r ≠ 8148 → c'.nreg r = c.nreg r) ∧
      c'.nreg 8148 = Bb ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, -, g1, g2, g3, -, g5, g6, g7⟩ :=
    forLoop_exec (P := P) (a := 8140) (bR := 8100) (body := fiPrBody) J (K := 7) (n := b) c₁
      e₁.wb_right a40 (by rw [ak _ (by omega) (by omega), r00])
      ⟨fun e he => absurd he (by omega), fun a _ => by rw [am], fun r h1 h2 h3 h4 => ak r h4 h1,
        a48, ar, arm, ao⟩
      (fun i c' hi hw ha hb hJ => by
        obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := hJ
        have hPe : c'.nmem (PRb + i) = c.nmem (PRb + i) := g2 _ (by omega)
        obtain ⟨c'', t, e, ht, b40, bm, bk, br, brm, bo⟩ :=
          fiPrBody_exec (P := P) c' hw ha (by rw [g3 _ (by omega) (by omega) (by omega) (by omega),
            r02]) g4
            (by rw [g3 _ (by omega) (by omega) (by omega) (by omega), r25])
            (by rw [g3 _ (by omega) (by omega) (by omega) (by omega), r24])
            (by rw [g3 _ (by omega) (by omega) (by omega) (by omega), r12]) (by omega) (by rw [hPe]; exact hPR i hi) (by omega)
            (by omega)
        refine ⟨c'', t, e, by omega, b40, by rw [bk _ (by omega) (by omega), hb],
          fun e' he' => ?_, fun a ha' => ?_, fun r h1 h2 h3 h4 => ?_,
          by rw [bk _ (by omega) (by omega), g4],
          by rw [br, g5], by rw [brm, g6], by rw [bo, g7]⟩
        · rw [bm]
          by_cases h : e' = i
          · subst h; rw [upd_same, hPe]
          · rw [upd_other _ _ _ (by omega), g1 e' (by omega)]
        · rw [bm, upd_other _ _ _ (by omega), g2 a (by omega)]
        · rw [bk r (by omega) (by omega), g3 r h1 h2 h3 h4])
  exact ⟨c₂, _, e₁.seq e₂, by omega, g1, fun a ha => g2 a ha, g3, g5, g6, g7⟩

theorem fiLnBody_exec (c : Config) (hc : WordsBounded W c) {e SIb ELb Bb Kp Mo : ℕ}
    (r40 : c.nreg 8140 = e) (r42 : c.nreg 8142 = SIb) (r07 : c.nreg 8107 = ELb)
    (r49 : c.nreg 8149 = Bb) (r25 : c.nreg 8125 = Kp) (r24 : c.nreg 8124 = Mo)
    (r12 : c.nreg 8112 = 1) (w1 : SIb + e ≤ W) (w2 : ELb + c.nmem (SIb + e) ≤ W)
    (w3 : c.nmem (ELb + c.nmem (SIb + e)) + Kp ≤ W) (w4 : Bb + e ≤ W) (w5 : e + 1 ≤ W) :
    ∃ c' t, Exec P W fiLnBody c c' t ∧ t = 9 ∧ c'.nreg 8140 = e + 1 ∧
      c'.nmem = upd c.nmem (Bb + e) ((c.nmem (ELb + c.nmem (SIb + e)) + Kp) % Mo) ∧
      (∀ r, (r < 8145 ∨ 8147 < r) → r ≠ 8140 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fiLnBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r40, r42, r07, r49, r25, r24, r12]); omega)
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r40, r12]
  · simp only [r40, r42, r07, r49, r25, r24]
  · repeat rw [upd_other _ _ _ (by omega)]

/-- **The residues of the lengths of the sorted arcs**: `Bb + e ↦ (EL[SI[e]] + K') mod M`,
`Bb = A + sb + lb`. -/
theorem fiLn_exec (c : Config) (hc : WordsBounded W c) {mE As lb SIb ELb Kp Mo : ℕ}
    (r04 : c.nreg 8104 = mE) (r26 : c.nreg 8126 = As) (r15 : c.nreg 8115 = lb)
    (r42 : c.nreg 8142 = SIb) (r07 : c.nreg 8107 = ELb) (r25 : c.nreg 8125 = Kp)
    (r24 : c.nreg 8124 = Mo) (r12 : c.nreg 8112 = 1)
    (hSI : SIb + mE ≤ As + lb ∨ As + lb + mE ≤ SIb)
    (hEL : ∀ e < mE, ELb + c.nmem (SIb + e) ≤ W ∧
      c.nmem (ELb + c.nmem (SIb + e)) + Kp ≤ W ∧
      (ELb + c.nmem (SIb + e) < As + lb ∨ As + lb + mE ≤ ELb + c.nmem (SIb + e)))
    (hW1 : As + lb + mE ≤ W) (hW2 : SIb + mE ≤ W) (hW3 : mE + 1 ≤ W) :
    ∃ c' t, Exec P W fiLn c c' t ∧ t ≤ 11 * mE + 4 ∧
      (∀ e < mE, c'.nmem (As + lb + e) = (c.nmem (ELb + c.nmem (SIb + e)) + Kp) % Mo) ∧
      (∀ a, (a < As + lb ∨ As + lb + mE ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 8140 ∨ 8149 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a49, a40, ak, am, ar, arm, ao⟩ : ∃ c₁ t₁,
      Exec P W (block [.addN 8149 8126 8115, .constN 8140 0]) c c₁ t₁ ∧ t₁ = 2 ∧
        c₁.nreg 8149 = As + lb ∧ c₁.nreg 8140 = 0 ∧
        (∀ r, r ≠ 8149 → r ≠ 8140 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r26, r15]); omega)
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r26, r15])
    repeat rw [upd_other _ _ _ (by omega)]
  set Bb := As + lb with hBb
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Bb + e) = (c.nmem (ELb + c.nmem (SIb + e)) + Kp) % Mo) ∧
      (∀ a, (a < Bb ∨ Bb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 8140 ∨ 8149 < r) → c'.nreg r = c.nreg r) ∧ c'.nreg 8149 = Bb ∧
      c'.nreg 8142 = SIb ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, t₂, e₂, ht₂, -, g1, g2, g3, -, -, g5, g6, g7⟩ :=
    forLoop_exec (P := P) (a := 8140) (bR := 8104) (body := fiLnBody) J (K := 9) (n := mE) c₁
      e₁.wb_right a40 (by rw [ak _ (by omega) (by omega), r04])
      ⟨fun e he => absurd he (by omega), fun a _ => by rw [am], fun r hr => ak r (by omega)
        (by omega), a49, by rw [ak _ (by omega) (by omega), r42], ar, arm, ao⟩
      (fun i c' hi hw ha hb hJ => by
        obtain ⟨g1, g2, g3, g4, g42, g5, g6, g7⟩ := hJ
        have hSIe : c'.nmem (SIb + i) = c.nmem (SIb + i) := g2 _ (by omega)
        have hELe : c'.nmem (ELb + c.nmem (SIb + i)) = c.nmem (ELb + c.nmem (SIb + i)) :=
          g2 _ ((hEL i hi).2.2.imp_right (fun h => by omega))
        obtain ⟨c'', t, e, ht, b40, bm, bk, br, brm, bo⟩ :=
          fiLnBody_exec (P := P) c' hw ha g42
            (by rw [g3 _ (by omega), r07]) g4 (by rw [g3 _ (by omega), r25])
            (by rw [g3 _ (by omega), r24]) (by rw [g3 _ (by omega), r12]) (by omega)
            (by rw [hSIe]; exact (hEL i hi).1) (by rw [hSIe, hELe]; exact (hEL i hi).2.1)
            (by omega) (by omega)
        refine ⟨c'', t, e, by omega, b40, by rw [bk _ (by omega) (by omega), hb],
          fun e' he' => ?_, fun a ha' => ?_, fun r hr => ?_, by rw [bk _ (by omega) (by omega), g4],
          by rw [bk _ (by omega) (by omega), g42], by rw [br, g5], by rw [brm, g6], by rw [bo, g7]⟩
        · rw [bm]
          by_cases h : e' = i
          · subst h; rw [upd_same, hSIe, hELe]
          · rw [upd_other _ _ _ (by omega), g1 e' (by omega)]
        · rw [bm, upd_other _ _ _ (by omega), g2 a (by omega)]
        · rw [bk r (by omega) (by omega), g3 r hr])
  exact ⟨c₂, _, e₁.seq e₂, by omega, g1, fun a ha => g2 a ha, g3, g5, g6, g7⟩

end Phases

end MsCall

end BKMNW

end PlanarFlow
