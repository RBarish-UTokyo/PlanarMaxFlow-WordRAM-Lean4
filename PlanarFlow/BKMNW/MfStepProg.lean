module

public import PlanarFlow.BKMNW.MfStepSem

/-!
# The step `stepP` of a node call as a program around its subroutines

`StepPSpec` (`PlanarFlow/BKMNW/MfNode.lean`) asks for one program computing the step `sepStep` of
a node call in the parent's flow array `FL`. This file writes that program, **`stepPO`**, as the
control flow of the article (Algorithm 1, lines 9–13 on each part of the separator), with the
calls of the subroutines as parameters, each with its own specification on the frame:

* `cntP` (`CntPSpec`): the number of parts of the separator in `r6801`, and that number plus the
  number of holes of the piece map in `r6806`;
* `fixP` (`FixPSpec`): FixConservationOnPath on the part `j` (`r6800 = j`): the flow
  `C.seg j` in `FL` becomes `C.O.fix C.U (C.seg j) π_j`;
* `c2sP`, `s2cP` (`C2SPSpec`, `S2CPSpec`): CycleToSingleSinkLimitedMaxFlow and
  SingleSourceToCycleLimitedMaxFlow on the hole `i` (`r6802 = i`) of the part `j`;
* `retP`, `frmP` (`RetPSpec`, `FrmPSpec`): the two push-backs of line 13.

Every specification is a `FlowProg`: from the frame of the call (`Lay`) holding a flow `g` in `FL`
(`FL[i] = Z + g (en i)`), within its steps, using memory from the heap top `b` on (`b + rO x ≤ W`),
it writes the next flow of the unrolled step (`SCtx`, `PlanarFlow/BKMNW/MfStepSem.lean`) into
`FL`, keeping the memory and the reals below `b` off `FL`, the registers `3000 … 3012` (the
driver) and `6800 … 6819` (the loops of `stepPO`) and the output. The flows are exactly those of
`arunL` (`SCtx.seg_succ`, `SCtx.hole_succ`, `cflow_node_eq`).

* `stepPO cntP fixP c2sP s2cP retP frmP = cntP ; stA ; while j < ns (fixP ; stH ;
  while i < nH (c2sP ; s2cP ; i += 1) ; retP ; frmP ; j += 1)` (registers `6800 = j`,
  `6801 = ns`, `6802 = i`, `6803 = nH`, `6805 = 1`, `6806 = nh + ns`);
* `lnRangeV` (a loop over `[lo, hi)` with a cost per index), `flow_step`, `holeLoopP_exec`,
  `segBodyP_exec`;
* **`stepPO_spec`**: from the six specifications, `stepPO` meets `StepPSpec` with the steps
  `stTO` (the sum of the steps of the subroutine calls and the loop overhead) and the room `rO`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs NegSSSP.Driver

universe w

/-! ### A loop with a cost per index -/

section Loop

variable {P : Input} {W : ℕ}

/-- **A loop over `[lo, hi)` with the cost `Bc i` of the body at the index `i`**: total cost
`∑ (Bc i + 2) + 2`. -/
theorem lnRangeV {a b : ℕ} {body : Stmt} (J : ℕ → Config → Prop) {lo hi : ℕ} (Bc : ℕ → ℕ)
    (c : Config) (hc : WordsBounded W c) (ha : c.nreg a = lo) (hb : c.nreg b = hi)
    (hle : lo ≤ hi) (hJ : J lo c)
    (hbody : ∀ i c, lo ≤ i → i < hi → WordsBounded W c → c.nreg a = i → c.nreg b = hi →
      J i c → ∃ c' k, Exec P W body c c' k ∧ k ≤ Bc i ∧ c'.nreg a = i + 1 ∧ c'.nreg b = hi ∧
        J (i + 1) c') :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ k ≤ (∑ i ∈ Ico lo hi, (Bc i + 2)) + 2 ∧
      WordsBounded W c' ∧ c'.nreg a = hi ∧ J hi c' := by
  obtain ⟨c', k, e, ⟨hw, h1, h2, h3, hJ'⟩, hn, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := a) (b := b) (body := body)
    (fun c => WordsBounded W c ∧ lo ≤ c.nreg a ∧ c.nreg a ≤ hi ∧ c.nreg b = hi ∧ J (c.nreg a) c)
    (fun c => ∑ i ∈ Ico (c.nreg a) hi, (Bc i + 2)) (fun c h => h.1)
    (fun c ⟨hw, h1, h2, h3, hJ⟩ hlt => by
      rw [h3] at hlt
      obtain ⟨c', k, e, hk, ha', hb', hJ'⟩ := hbody _ c h1 hlt hw rfl h3 hJ
      refine ⟨c', k, e, ⟨e.wb_right, by omega, by omega, hb', by rw [ha']; exact hJ'⟩, ?_⟩
      rw [ha', Finset.sum_eq_sum_Ico_succ_bot hlt]
      omega) ⟨hc, by omega, by omega, hb, by rw [ha]; exact hJ⟩
  have e' : c'.nreg a = hi := by omega
  exact ⟨c', k, e, by rw [ha] at hk; exact hk, hw, e', by rw [e'] at hJ'; exact hJ'⟩

end Loop

/-! ### The small blocks -/

section Blocks

variable {P : Input} {W : ℕ}

/-- `one := 1`, `j := 0`. -/
def stA : Stmt := block [.constN 6805 1, .constN 6800 0]

/-- `i := 0`, `nH := (nh + ns) - j - 1`. -/
def stH : Stmt := block [.constN 6802 0, .subN 6803 6806 6800, .subN 6803 6803 6805]

/-- `i := i + 1`. -/
def stI : Stmt := block [.addN 6802 6802 6805]

/-- `j := j + 1`. -/
def stJ : Stmt := block [.addN 6800 6800 6805]

theorem stA_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' t, Exec P W stA c c' t ∧ t = 2 ∧ c'.nreg 6805 = 1 ∧ c'.nreg 6800 = 0 ∧
      (∀ x, x ≠ 6805 → x ≠ 6800 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold stA
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem stH_exec (c : Config) (hc : WordsBounded W c) {N j : ℕ} (r6 : c.nreg 6806 = N)
    (r0 : c.nreg 6800 = j) (r5 : c.nreg 6805 = 1) :
    ∃ c' t, Exec P W stH c c' t ∧ t = 3 ∧ c'.nreg 6802 = 0 ∧ c'.nreg 6803 = N - j - 1 ∧
      (∀ x, x ≠ 6802 → x ≠ 6803 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hN : N ≤ W := by rw [← r6]; exact WordsBounded.nreg hc 6806
  unfold stH
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r6, r0, r5] <;> omega)
  refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r6, r0, r5])
    try omega

theorem stI_exec (c : Config) (hc : WordsBounded W c) {i : ℕ} (r2 : c.nreg 6802 = i)
    (r5 : c.nreg 6805 = 1) (hw : i + 1 ≤ W) :
    ∃ c' t, Exec P W stI c c' t ∧ t = 1 ∧ c'.nreg 6802 = i + 1 ∧
      (∀ x, x ≠ 6802 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold stI
  exec_block
  all_goals try (config_simp; simp only [r2, r5]; omega)
  refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r2, r5]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem stJ_exec (c : Config) (hc : WordsBounded W c) {j : ℕ} (r0 : c.nreg 6800 = j)
    (r5 : c.nreg 6805 = 1) (hw : j + 1 ≤ W) :
    ∃ c' t, Exec P W stJ c c' t ∧ t = 1 ∧ c'.nreg 6800 = j + 1 ∧
      (∀ x, x ≠ 6800 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold stJ
  exec_block
  all_goals try (config_simp; simp only [r0, r5]; omega)
  refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r0, r5]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

end Blocks

/-! ### The program -/

/-- One hole: `c2s`, `s2c`, `i := i + 1`. -/
def holeBodyP (c2sP s2cP : Stmt) : Stmt := .seq c2sP (.seq s2cP stI)

/-- One part of the separator: FixConservationOnPath, the holes, the two push-backs,
`j := j + 1`. -/
def segBodyP (fixP c2sP s2cP retP frmP : Stmt) : Stmt :=
  .seq fixP (.seq stH (.seq (.whileLtN 6802 6803 (holeBodyP c2sP s2cP))
    (.seq retP (.seq frmP stJ))))

/-- **The step of a node call** around its subroutines. -/
def stepPO (cntP fixP c2sP s2cP retP frmP : Stmt) : Stmt :=
  .seq cntP (.seq stA (.whileLtN 6800 6801 (segBodyP fixP c2sP s2cP retP frmP)))

/-! ### The specifications of the subroutine programs -/

section Spec

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The registers kept by the subroutine programs: the driver's and the loops'. -/
def SRegKeep (c c' : Config) : Prop :=
  ∀ r, (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) → c'.nreg r = c.nreg r

/-- The flow array of a frame holds `g`. -/
def FLHas {B : Finset D} (Z m d : ℕ) (en : ℕ → D) (mem : ℕ → ℕ) (g : SDart B → ℤ) : Prop :=
  ∀ i < m, (mem (d + 4 + 6 * m + i) : ℤ) = Z + fext g (en i)

variable (M) in
/-- **A program rewriting the flow of a call**: from the frame of `x` at `d` (`Lay`) holding the
flow `gin` in `FL`, a configuration meeting `pre`, the driver's registers `3004 = d`, `3005 = e`,
`3006 = b + 5`, within `t` steps, the flow `gout` in `FL`; the memory and the reals below `b` off
`FL`, the registers of `SRegKeep` and the output kept. -/
def FlowProg (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (p : Stmt)
    (x : MCall M) (m : ℕ) (en : ℕ → D) (d e b : ℕ) (pre : Config → Prop) {B : Finset D}
    (gin gout : SDart B → ℤ) (t : ℕ) : Prop :=
  ∀ c : Config, pre c → Lay M gid u S T Z x m en d c.nmem → FLHas Z m d en c.nmem gin →
    WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e → c.nreg 3006 = b + 5 →
    ∃ c' t', Exec I W p c c' t' ∧ t' ≤ t ∧ SRegKeep c c' ∧
      (∀ a, a < b → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      c'.output = c.output ∧ FLHas Z m d en c'.nmem gout

variable (M) in
/-- **The counts**: the number of parts of the separator in `r6801`, plus the number of holes of
the piece map in `r6806`; all the memory and the reals below `b` kept. -/
def CntPSpec (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ) (S T : Finset V) (Z : ℕ)
    (I : Input) (W : ℕ) (cntP : Stmt) (cnT rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (d e b m : ℕ)
    (en : ℕ → D) (c : Config),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) →
    Lay M gid u S T Z (.node l r π, Hs, σ) m en d c.nmem → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → WordsBounded W c → c.nreg 3004 = d → c.nreg 3005 = e →
    c.nreg 3006 = b + 5 →
    ∃ c' t, Exec I W cntP c c' t ∧ t ≤ cnT (.node l r π, Hs, σ) ∧ DRegKeep c c' ∧
      (∀ a, a < b → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      c'.nreg 6801 = π.segs.length ∧
      c'.nreg 6806 = (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length + π.segs.length

variable (M) in
/-- **FixConservationOnPath on the part `j`** (`r6800 = j`). -/
def FixPSpec (O : PlaneOracles.{w}) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (fixP : Stmt) (fT : MCall M → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → (xCtx M O u S T l r π Hs σ h).L[j]? = some πj →
    FlowProg M gid u S T Z I W fixP (.node l r π, Hs, σ) m en d e b (fun c => c.nreg 6800 = j)
      ((xCtx M O u S T l r π Hs σ h).seg j)
      ((xCtx M O u S T l r π Hs σ h).O.fix (xCtx M O u S T l r π Hs σ h).U
        ((xCtx M O u S T l r π Hs σ h).seg j) πj) (fT (.node l r π, Hs, σ) j)

variable (M) in
/-- **CycleToSingleSinkLimitedMaxFlow on the hole `i` of the part `j`** (`r6800 = j`,
`r6802 = i`). -/
def C2SPSpec (O : PlaneOracles.{w}) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (c2sP : Stmt) (cT : MCall M → ℕ → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j i : ℕ) (πj : SPath (pmap h.1))
    (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → (xCtx M O u S T l r π Hs σ h).L[j]? = some πj →
    ((xCtx M O u S T l r π Hs σ h).holes j)[i]? = some H →
    FlowProg M gid u S T Z I W c2sP (.node l r π, Hs, σ) m en d e b
      (fun c => c.nreg 6800 = j ∧ c.nreg 6802 = i)
      ((xCtx M O u S T l r π Hs σ h).hole j πj i)
      ((xCtx M O u S T l r π Hs σ h).c2s j πj i H) (cT (.node l r π, Hs, σ) j i)

variable (M) in
/-- **SingleSourceToCycleLimitedMaxFlow on the hole `i` of the part `j`** (`r6800 = j`,
`r6802 = i`). -/
def S2CPSpec (O : PlaneOracles.{w}) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (s2cP : Stmt) (sT : MCall M → ℕ → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j i : ℕ) (πj : SPath (pmap h.1))
    (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → (xCtx M O u S T l r π Hs σ h).L[j]? = some πj →
    ((xCtx M O u S T l r π Hs σ h).holes j)[i]? = some H →
    FlowProg M gid u S T Z I W s2cP (.node l r π, Hs, σ) m en d e b
      (fun c => c.nreg 6800 = j ∧ c.nreg 6802 = i)
      ((xCtx M O u S T l r π Hs σ h).c2s j πj i H)
      ((xCtx M O u S T l r π Hs σ h).O.s2c (xCtx M O u S T l r π Hs σ h).U
        ((xCtx M O u S T l r π Hs σ h).c2s j πj i H) πj H) (sT (.node l r π, Hs, σ) j i)

variable (M) in
/-- **The push-back of the excess to the sources** on the part `j` (`r6800 = j`). -/
def RetPSpec (O : PlaneOracles.{w}) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (retP : Stmt) (rtT : MCall M → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → (xCtx M O u S T l r π Hs σ h).L[j]? = some πj →
    FlowProg M gid u S T Z I W retP (.node l r π, Hs, σ) m en d e b (fun c => c.nreg 6800 = j)
      ((xCtx M O u S T l r π Hs σ h).hole j πj ((xCtx M O u S T l r π Hs σ h).holes j).length)
      ((xCtx M O u S T l r π Hs σ h).ret j πj) (rtT (.node l r π, Hs, σ) j)

variable (M) in
/-- **The push-back from the sinks** on the part `j` (`r6800 = j`). -/
def FrmPSpec (O : PlaneOracles.{w}) (Reach : MCall M → Prop) (gid : D → ℕ) (u : D → ℤ)
    (S T : Finset V) (Z : ℕ) (I : Input) (W : ℕ) (frmP : Stmt) (fmT : MCall M → ℕ → ℕ)
    (rO : MCall M → ℕ) : Prop :=
  ∀ (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ)
    (d e b m : ℕ) (en : ℕ → D) (j : ℕ) (πj : SPath (pmap h.1)),
    Reach (.node l r π, Hs, σ) → CallOk M S T (.node l r π, Hs, σ) → d + fsz m ≤ e → e ≤ b →
    b + rO (.node l r π, Hs, σ) ≤ W → (xCtx M O u S T l r π Hs σ h).L[j]? = some πj →
    FlowProg M gid u S T Z I W frmP (.node l r π, Hs, σ) m en d e b (fun c => c.nreg 6800 = j)
      ((xCtx M O u S T l r π Hs σ h).ret j πj)
      ((xCtx M O u S T l r π Hs σ h).O.frm (xCtx M O u S T l r π Hs σ h).U
        ((xCtx M O u S T l r π Hs σ h).ret j πj) (xCtx M O u S T l r π Hs σ h).T
        (negSet (pmap h.1) ((xCtx M O u S T l r π Hs σ h).ret j πj) πj.verts))
      (fmT (.node l r π, Hs, σ) j)

/-! ### The steps -/

/-- The steps of the hole loop of the part `j`, with `nH` holes. -/
def hlCost (cT sT : MCall M → ℕ → ℕ → ℕ) (x : MCall M) (j nH : ℕ) : ℕ :=
  ∑ i ∈ range nH, (cT x j i + sT x j i + 1 + 2)

/-- The steps of the part `j`, with `nH` holes. -/
def sgCost (fT : MCall M → ℕ → ℕ) (cT sT : MCall M → ℕ → ℕ → ℕ) (rtT fmT : MCall M → ℕ → ℕ)
    (x : MCall M) (j nH : ℕ) : ℕ :=
  fT x j + 3 + (hlCost cT sT x j nH + 2) + rtT x j + fmT x j + 1

/-- The steps of the step with `ns` parts and `nh` holes. -/
def stCost (cnT : MCall M → ℕ) (fT : MCall M → ℕ → ℕ) (cT sT : MCall M → ℕ → ℕ → ℕ)
    (rtT fmT : MCall M → ℕ → ℕ) (x : MCall M) (ns nh : ℕ) : ℕ :=
  cnT x + 2 + ((∑ j ∈ range ns, (sgCost fT cT sT rtT fmT x j (nh + (ns - (j + 1))) + 2)) + 2)

variable (M) in
/-- **The steps of `stepPO`** at a node call. -/
noncomputable def stTO (cnT : MCall M → ℕ) (fT : MCall M → ℕ → ℕ) (cT sT : MCall M → ℕ → ℕ → ℕ)
    (rtT fmT : MCall M → ℕ → ℕ) : MCall M → ℕ
  | (.node l r π, Hs, σ) => stCost cnT fT cT sT rtT fmT (.node l r π, Hs, σ) π.segs.length
      (pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs).length
  | (.leaf _, _, _) => 0

end Spec

/-! ### The runs -/

section Run

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The state of the step: the driver's registers, the memory and the reals below `b` off `FL`,
the output as at the start `c₀`. -/
def StInv (c₀ c : Config) (d m b : ℕ) : Prop :=
  (∀ r, 3000 ≤ r → r ≤ 3012 → c.nreg r = c₀.nreg r) ∧
  (∀ a, a < b → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
    c.nmem a = c₀.nmem a ∧ c.rmem a = c₀.rmem a) ∧ c.output = c₀.output

lemma StInv.refl (c₀ : Config) (d m b : ℕ) : StInv c₀ c₀ d m b :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => ⟨rfl, rfl⟩, rfl⟩

/-- A block keeping the memory, the reals, the output and the driver's registers keeps the state. -/
lemma StInv.of_block {c₀ c c' : Config} {d m b : ℕ} (h : StInv c₀ c d m b)
    (hr : ∀ x, 3000 ≤ x → x ≤ 3012 → c'.nreg x = c.nreg x) (hm : c'.nmem = c.nmem)
    (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) : StInv c₀ c' d m b :=
  ⟨fun x h1 h2 => by rw [hr x h1 h2, h.1 x h1 h2], fun a h1 h2 => by
    rw [hm, hrm]; exact h.2.1 a h1 h2, by rw [ho, h.2.2]⟩

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {I : Input} {W : ℕ}

/-- **One call of a subroutine program** inside the step: from the state at `c`, a run to the
next flow, the state kept, the loop registers kept. -/
theorem flow_step {p : Stmt} {x : MCall M} {m : ℕ} {en : ℕ → D} {d e b : ℕ}
    {pre : Config → Prop} {B : Finset D} {gin gout : SDart B → ℤ} {t : ℕ}
    (hF : FlowProg M gid u S T Z I W p x m en d e b pre gin gout t) {c₀ : Config}
    (hL₀ : Lay M gid u S T Z x m en d c₀.nmem) (hde : d + fsz m ≤ e) (heb : e ≤ b)
    (r4 : c₀.nreg 3004 = d) (r5 : c₀.nreg 3005 = e) (r6 : c₀.nreg 3006 = b + 5) (c : Config)
    (hc : WordsBounded W c) (hS : StInv c₀ c d m b) (hpre : pre c)
    (hfl : FLHas Z m d en c.nmem gin) :
    ∃ c' t', Exec I W p c c' t' ∧ t' ≤ t ∧ StInv c₀ c' d m b ∧
      (∀ r, 6800 ≤ r → r ≤ 6819 → c'.nreg r = c.nreg r) ∧ FLHas Z m d en c'.nmem gout := by
  unfold fsz at hde
  have hL : Lay M gid u S T Z x m en d c.nmem :=
    hL₀.congr fun a h1 h2 => (hS.2.1 a (by omega) (by omega)).1
  obtain ⟨c', t', ex, ht, hk, hm, ho, hfl'⟩ := hF c hpre hL hfl hc
    (by rw [hS.1 _ (by omega) (by omega), r4]) (by rw [hS.1 _ (by omega) (by omega), r5])
    (by rw [hS.1 _ (by omega) (by omega), r6])
  refine ⟨c', t', ex, ht, ⟨fun r h1 h2 => by rw [hk r (Or.inl ⟨h1, h2⟩), hS.1 r h1 h2],
    fun a h1 h2 => ?_, by rw [ho, hS.2.2]⟩, fun r h1 h2 => hk r (Or.inr ⟨h1, h2⟩), hfl'⟩
  obtain ⟨a1, a2⟩ := hm a h1 h2
  obtain ⟨b1, b2⟩ := hS.2.1 a h1 h2
  exact ⟨a1.trans b1, a2.trans b2⟩

variable {O : PlaneOracles.{w}} {Reach : MCall M → Prop}
  {cntP fixP c2sP s2cP retP frmP : Stmt} {cnT rO : MCall M → ℕ}
  {fT rtT fmT : MCall M → ℕ → ℕ} {cT sT : MCall M → ℕ → ℕ → ℕ}

/-- **The hole loop of the part `j`**. -/
theorem holeLoopP_exec (hc2 : C2SPSpec M O Reach gid u S T Z I W c2sP cT rO)
    (hs2 : S2CPSpec M O Reach gid u S T Z I W s2cP sT rO)
    {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ)
    {d e b m : ℕ} {en : ℕ → D} {j : ℕ} {πj : SPath (pmap h.1)}
    (hR : Reach (.node l r π, Hs, σ)) (hok : CallOk M S T (.node l r π, Hs, σ))
    (hde : d + fsz m ≤ e) (heb : e ≤ b) (hroom : b + rO (.node l r π, Hs, σ) ≤ W)
    (hj : (xCtx M O u S T l r π Hs σ h).L[j]? = some πj) {c₀ : Config}
    (hL₀ : Lay M gid u S T Z (.node l r π, Hs, σ) m en d c₀.nmem)
    (r4 : c₀.nreg 3004 = d) (r5 : c₀.nreg 3005 = e) (r6 : c₀.nreg 3006 = b + 5) (c : Config)
    (hc : WordsBounded W c) (hS : StInv c₀ c d m b) (q0 : c.nreg 6800 = j)
    (q2 : c.nreg 6802 = 0) (q3 : c.nreg 6803 = ((xCtx M O u S T l r π Hs σ h).holes j).length)
    (q5 : c.nreg 6805 = 1)
    (hfl : FLHas Z m d en c.nmem ((xCtx M O u S T l r π Hs σ h).hole j πj 0)) :
    ∃ c' t, Exec I W (.whileLtN 6802 6803 (holeBodyP c2sP s2cP)) c c' t ∧
      t ≤ hlCost cT sT (.node l r π, Hs, σ) j ((xCtx M O u S T l r π Hs σ h).holes j).length + 2 ∧
      StInv c₀ c' d m b ∧
      (∀ r, 6800 ≤ r → r ≤ 6819 → r ≠ 6802 → c'.nreg r = c.nreg r) ∧
      FLHas Z m d en c'.nmem
        ((xCtx M O u S T l r π Hs σ h).hole j πj ((xCtx M O u S T l r π Hs σ h).holes j).length) := by
  set C := xCtx M O u S T l r π Hs σ h with hC
  set nH := (C.holes j).length with hnH
  have hnW : nH ≤ W := by rw [← q3]; exact WordsBounded.nreg hc 6803
  let J : ℕ → Config → Prop := fun i c' =>
    StInv c₀ c' d m b ∧ (∀ r, 6800 ≤ r → r ≤ 6819 → r ≠ 6802 → c'.nreg r = c.nreg r) ∧
      FLHas Z m d en c'.nmem (C.hole j πj i)
  obtain ⟨c', k, ex, hk, -, -, hJ1, hJ2, hJ3⟩ := lnRangeV (P := I) (W := W) (a := 6802)
    (b := 6803) (body := holeBodyP c2sP s2cP) J (lo := 0) (hi := nH)
    (fun i => cT (.node l r π, Hs, σ) j i + sT (.node l r π, Hs, σ) j i + 1) c hc q2 q3
    (Nat.zero_le _) ⟨hS, fun _ _ _ _ => rfl, hfl⟩
    (fun i c₁ _ hi hw₁ a2 a3 ⟨S₁, K₁, F₁⟩ => by
      obtain ⟨H, hH⟩ : ∃ H, (C.holes j)[i]? = some H :=
        ⟨(C.holes j)[i], List.getElem?_eq_getElem hi⟩
      have p0 : c₁.nreg 6800 = j := by rw [K₁ _ (by omega) (by omega) (by omega), q0]
      obtain ⟨c₂, t₂, e₂, ht₂, S₂, K₂, F₂⟩ := flow_step
        (hc2 l r π Hs σ h d e b m en j i πj H hR hok hde heb hroom hj hH) hL₀ hde heb r4 r5 r6
        c₁ hw₁ S₁ ⟨p0, a2⟩ F₁
      obtain ⟨c₃, t₃, e₃, ht₃, S₃, K₃, F₃⟩ := flow_step
        (hs2 l r π Hs σ h d e b m en j i πj H hR hok hde heb hroom hj hH) hL₀ hde heb r4 r5 r6
        c₂ e₂.wb_right S₂ ⟨by rw [K₂ _ (by omega) (by omega), p0],
          by rw [K₂ _ (by omega) (by omega), a2]⟩ F₂
      have p2 : c₃.nreg 6802 = i := by
        rw [K₃ _ (by omega) (by omega), K₂ _ (by omega) (by omega), a2]
      have p5 : c₃.nreg 6805 = 1 := by
        rw [K₃ _ (by omega) (by omega), K₂ _ (by omega) (by omega),
          K₁ _ (by omega) (by omega) (by omega), q5]
      obtain ⟨c₄, t₄, e₄, ht₄, p2', K₄, m₄, rr₄, rm₄, o₄⟩ := stI_exec (P := I) c₃ e₃.wb_right p2 p5
        (by omega)
      refine ⟨c₄, t₂ + (t₃ + t₄), .seq e₂ (.seq e₃ e₄), by omega, p2', ?_, ?_⟩
      · rw [K₄ _ (by omega), K₃ _ (by omega) (by omega), K₂ _ (by omega) (by omega)]; exact a3
      · refine ⟨S₃.of_block (fun x h1 h2 => K₄ x (by omega)) m₄ rm₄ o₄, fun x h1 h2 h3 => ?_, ?_⟩
        · rw [K₄ x h3, K₃ x h1 h2, K₂ x h1 h2, K₁ x h1 h2 h3]
        · rw [m₄, C.hole_succ hH]; exact F₃)
  refine ⟨c', k, ex, ?_, hJ1, hJ2, hJ3⟩
  unfold hlCost; rw [range_eq_Ico]; exact hk

end Run

end MfDrv

end BKMNW

end PlanarFlow
