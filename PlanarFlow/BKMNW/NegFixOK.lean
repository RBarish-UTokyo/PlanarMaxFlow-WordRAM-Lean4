module

public import PlanarFlow.NegSSSP.DrvFix

/-!
# The syntactic facts of `negFix`, proved compositionally

The fixed program `negFix = fxSet ; drvT` (`PlanarFlow/NegSSSP/DrvFix.lean`) is too large for
`decide` as a whole (evaluating its register list exhausts the memory). Its syntactic
facts are proved from those of its components (each one small enough for `decide +kernel`, or
already proved), through the structure of `driver`, `body`, `nodeST`, `FsT`:

* `nfRegsOK_mono` (a register condition is monotone in the predicate);
* **`regsOK_of_hsOK`**: a statement without reals meeting the register condition of constant
  hoisting `hsOK PB np` names only registers `< PB + np`;
* **`drvT_regsOK`**, **`drvT_noInp`**, **`drvT_noRand`**, **`drvT_natOnly`**;
* **`negFix_regsOK`**: `negFix` names only the registers `< nfR = 3200`;
  **`negFix_noInp`**, **`negFix_noRand`**, **`negFix_natOnly`**.
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt PlanarFlow.NegSSSP.Driver PlanarFlow.NegSSSP.Frame

/-- A register condition is monotone in the predicate. -/
theorem nfRegsOK_mono {U U' : ℕ → Bool} (hsub : ∀ r, U r = true → U' r = true) :
    ∀ s : Stmt, s.regsOK U = true → s.regsOK U' = true
  | .skip, _ => rfl
  | .instr i, h => List.all_eq_true.2 fun r hr => hsub r (List.all_eq_true.1 h r hr)
  | .seq s t, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h ⊢
    exact ⟨nfRegsOK_mono hsub s h.1, nfRegsOK_mono hsub t h.2⟩
  | .ifLtN a b s t, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨hsub _ h.1.1.1, hsub _ h.1.1.2⟩, nfRegsOK_mono hsub s h.1.2⟩,
      nfRegsOK_mono hsub t h.2⟩
  | .ifLtR a b s t, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨hsub _ h.1.1.1, hsub _ h.1.1.2⟩, nfRegsOK_mono hsub s h.1.2⟩,
      nfRegsOK_mono hsub t h.2⟩
  | .whileLtN a b s, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h ⊢
    exact ⟨⟨hsub _ h.1.1, hsub _ h.1.2⟩, nfRegsOK_mono hsub s h.2⟩
  | .whileLtR a b s, h => by
    simp only [Stmt.regsOK, Bool.and_eq_true] at h ⊢
    exact ⟨⟨hsub _ h.1.1, hsub _ h.1.2⟩, nfRegsOK_mono hsub s h.2⟩

/-- An instruction meeting the hoisting condition names only registers `< PB + np`. -/
theorem regsOKI_of_hsOKI {PB np : ℕ} {i : Instr} (h : hsOKI PB np i = true) :
    i.regsOK (fun r => decide (r < PB + np)) = true := by
  cases i with
  | copyN r a =>
    simp only [hsOKI, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    simp only [Instr.regsOK, Instr.regs, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    omega
  | _ =>
    simp only [hsOKI] at h
    exact List.all_eq_true.2 fun r hr => by
      have := List.all_eq_true.1 h r hr
      simp only [decide_eq_true_eq] at this ⊢
      omega

/-- **A statement without reals meeting the hoisting condition `hsOK PB np` names only the
registers `< PB + np`.** -/
theorem regsOK_of_hsOK {PB np : ℕ} :
    ∀ s : Stmt, Klein.natOnly s = true → hsOK PB np s = true →
      s.regsOK (fun r => decide (r < PB + np)) = true
  | .skip, _, _ => rfl
  | .instr i, _, h => regsOKI_of_hsOKI h
  | .seq s t, hn, h => by
    simp only [Klein.natOnly, hsOK, Stmt.regsOK, Bool.and_eq_true] at hn h ⊢
    exact ⟨regsOK_of_hsOK s hn.1 h.1, regsOK_of_hsOK t hn.2 h.2⟩
  | .ifLtN a b s t, hn, h => by
    simp only [Klein.natOnly, hsOK, Stmt.regsOK, Bool.and_eq_true, decide_eq_true_eq] at hn h ⊢
    exact ⟨⟨⟨by omega, by omega⟩, regsOK_of_hsOK s hn.1 h.1.2⟩, regsOK_of_hsOK t hn.2 h.2⟩
  | .ifLtR _ _ _ _, hn, _ => by simp [Klein.natOnly] at hn
  | .whileLtN a b s, hn, h => by
    simp only [Klein.natOnly, hsOK, Stmt.regsOK, Bool.and_eq_true, decide_eq_true_eq] at hn h ⊢
    exact ⟨⟨by omega, by omega⟩, regsOK_of_hsOK s hn h.2⟩
  | .whileLtR _ _ _, hn, _ => by simp [Klein.natOnly] at hn

/-! ### The components -/

theorem testS_ni : testS.noInp = true := by decide +kernel
theorem testS_nr : testS.noRand = true := by decide +kernel
theorem splitS0_ni : splitS0.noInp = true := by decide +kernel
theorem splitS0_nr : splitS0.noRand = true := by decide +kernel
theorem peekB_no : peekB.noInp = true ∧ peekB.noRand = true ∧ Klein.natOnly peekB = true := by
  decide +kernel
theorem popB_no : popB.noInp = true ∧ popB.noRand = true ∧ Klein.natOnly popB = true := by
  decide +kernel
theorem pushB_no : pushB.noInp = true ∧ pushB.noRand = true ∧ Klein.natOnly pushB = true := by
  decide +kernel
theorem coB_no : coB.noInp = true ∧ coB.noRand = true ∧ Klein.natOnly coB = true := by
  decide +kernel
theorem coPost_no : coPost.noInp = true ∧ coPost.noRand = true ∧ Klein.natOnly coPost = true := by
  decide +kernel
theorem ndFront_no : ndFront.noInp = true ∧ ndFront.noRand = true ∧
    Klein.natOnly ndFront = true := by decide +kernel
theorem ndNone_no : ndNone.noInp = true ∧ ndNone.noRand = true ∧ Klein.natOnly ndNone = true := by
  decide +kernel
theorem ndC_no : ndC.noInp = true ∧ ndC.noRand = true ∧ Klein.natOnly ndC = true := by
  decide +kernel
theorem resProg_no : resProg.noInp = true ∧ resProg.noRand = true ∧
    Klein.natOnly resProg = true := by decide +kernel
theorem spStage_no : spStage.noInp = true ∧ spStage.noRand = true := by decide +kernel
theorem fbA_no : fbA.noInp = true ∧ fbA.noRand = true ∧ Klein.natOnly fbA = true := by
  decide +kernel
theorem fbMid_no : fbMid.noInp = true ∧ fbMid.noRand = true ∧ Klein.natOnly fbMid = true := by
  decide +kernel
theorem fbR_no : fbR.noInp = true ∧ fbR.noRand = true ∧ Klein.natOnly fbR = true := by
  decide +kernel
theorem lfT_no : lfT.noInp = true ∧ lfT.noRand = true ∧ Klein.natOnly lfT = true := by
  decide +kernel
theorem ndBT_no : ndBT.noInp = true ∧ ndBT.noRand = true ∧ Klein.natOnly ndBT = true := by
  decide +kernel
theorem fbOutT_no : fbOutT.noInp = true ∧ fbOutT.noRand = true ∧
    Klein.natOnly fbOutT = true := by decide +kernel

theorem lgNode_no : (lgS 2925 2926 nodeFullR).noInp = true ∧
    (lgS 2925 2926 nodeFullR).noRand = true ∧ Klein.natOnly (lgS 2925 2926 nodeFullR) = true :=
  ⟨lgS_noInp _ nodeFullR_ok.2.1, lgS_noRand _ nodeFullR_ok.2.2, lgS_natOnly _ nodeFullR_natOnly⟩

/-- The registers of `negFix`: below `3200`. -/
def nfR : ℕ := 3200

/-- The register predicate of `negFix`. -/
abbrev nfU : ℕ → Bool := fun r => decide (r < nfR)

theorem fxU_nfU : ∀ r, fxU r = true → nfU r = true := fun r h => by
  simp only [fxU, nfU, decide_eq_true_eq] at h ⊢; simp only [fxPB, nfR] at h ⊢; omega

theorem hs_nfU : ∀ r, decide (r < fxPB + 2) = true → nfU r = true := fun r h => by
  simp only [nfU, decide_eq_true_eq] at h ⊢; simp only [fxPB, nfR] at h ⊢; omega

/-! ### The recursion's program -/

theorem drvT_natOnly : Klein.natOnly drvT = true := by
  simp only [drvT, driver, body, nodeST, FsT, Klein.natOnly, testS_natOnly, splitS0_natOnly,
    peekB_no.2.2, popB_no.2.2, pushB_no.2.2, coB_no.2.2, coPost_no.2.2, ndFront_no.2.2,
    ndNone_no.2.2, ndC_no.2.2, resProg_no.2.2, spStage_natOnly, fbA_no.2.2, fbMid_no.2.2,
    fbR_no.2.2, lfT_no.2.2, ndBT_no.2.2, fbOutT_no.2.2, lgNode_no.2.2, Bool.and_self]

theorem drvT_noInp : drvT.noInp = true := by
  simp only [drvT, driver, body, nodeST, FsT, Stmt.noInp, testS_ni, splitS0_ni,
    peekB_no.1, popB_no.1, pushB_no.1, coB_no.1, coPost_no.1, ndFront_no.1,
    ndNone_no.1, ndC_no.1, resProg_no.1, spStage_no.1, fbA_no.1, fbMid_no.1,
    fbR_no.1, lfT_no.1, ndBT_no.1, fbOutT_no.1, lgNode_no.1, Bool.and_self]

theorem drvT_noRand : drvT.noRand = true := by
  simp only [drvT, driver, body, nodeST, FsT, Stmt.noRand, testS_nr, splitS0_nr,
    peekB_no.2.1, popB_no.2.1, pushB_no.2.1, coB_no.2.1, coPost_no.2.1, ndFront_no.2.1,
    ndNone_no.2.1, ndC_no.2.1, resProg_no.2.1, spStage_no.2, fbA_no.2.1, fbMid_no.2.1,
    fbR_no.2.1, lfT_no.2.1, ndBT_no.2.1, fbOutT_no.2.1, lgNode_no.2.1, Bool.and_self]

/-- **`drvT` names only registers `< 3200`**: from `hsOK fxPB 2 drvT` (`drvT_ok`) and
`drvT_natOnly` by `regsOK_of_hsOK`. -/
theorem drvT_regsOK : drvT.regsOK nfU = true :=
  nfRegsOK_mono hs_nfU _ (regsOK_of_hsOK drvT drvT_natOnly drvT_ok)

/-! ### The whole program -/

theorem fxSet_facts : fxSet.regsOK nfU = true ∧ fxSet.noInp = true ∧ fxSet.noRand = true ∧
    Klein.natOnly fxSet = true := by decide +kernel

/-- **`negFix` names only the registers `< 3200`.** -/
theorem negFix_regsOK : negFix.regsOK nfU = true := by
  simp only [negFix, Stmt.regsOK, fxSet_facts.1, drvT_regsOK, Bool.and_self]

theorem negFix_noInp : negFix.noInp = true := by
  simp only [negFix, Stmt.noInp, fxSet_facts.2.1, drvT_noInp, Bool.and_self]

theorem negFix_noRand : negFix.noRand = true := by
  simp only [negFix, Stmt.noRand, fxSet_facts.2.2.1, drvT_noRand, Bool.and_self]

theorem negFix_natOnly : Klein.natOnly negFix = true := by
  simp only [negFix, Klein.natOnly, fxSet_facts.2.2.2, drvT_natOnly, Bool.and_self]

end NegSSSP

end PlanarFlow
