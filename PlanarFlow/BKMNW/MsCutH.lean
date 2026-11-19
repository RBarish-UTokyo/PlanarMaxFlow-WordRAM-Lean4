module

public import PlanarFlow.BKMNW.MsCutG

/-!
# The cut map of the path on the machine, part H: the whole program on arrays

**`cutProg`** `= cutPre ; cutWr`. **`cutProg_run`**: from the index arrays `RV = rv`, `RT = rt`
(a permutation), the path flags `LF = lf` and the tour array `TA = ta` (a permutation), below the
scratch `[Z, Z + 6m)`, with two output blocks of `5m` words at `RVo`, `RTo` above it, within
`178 m + 95` steps the words `CutWords` of the cut are written (`nE = reF lf m`,
`nT = rkF lf rt m m`, the inverse tour `tiF ta m`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab

variable {P : Input} {W : ℕ}

/-- **The program of the cut map.** -/
def cutProg : Stmt := .seq cutPre cutWr

/-- The inverse of a permutation of `[0, m)`. -/
noncomputable def tiF (ta : ℕ → ℕ) (m i : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, j < m ∧ ta j = i then Nat.find h else 0

lemma permOn_pre {ta : ℕ → ℕ} {m : ℕ} (h : PermOn ta m) {i : ℕ} (hi : i < m) :
    ∃ j, j < m ∧ ta j = i := by
  obtain ⟨p, hp, e⟩ := iter_period h hi
  refine ⟨ta^[p - 1] i, OrbLab.iter_lt h hi _, ?_⟩
  rw [← Function.iterate_succ_apply' ta (p - 1), show (p - 1).succ = p by omega, e]

lemma tiF_spec {ta : ℕ → ℕ} {m : ℕ} (h : PermOn ta m) {i : ℕ} (hi : i < m) :
    tiF ta m i < m ∧ ta (tiF ta m i) = i := by
  classical
  have hex := permOn_pre h hi
  unfold tiF
  split_ifs
  exact Nat.find_spec hex

lemma tiF_ta {ta : ℕ → ℕ} {m : ℕ} (h : PermOn ta m) {j : ℕ} (hj : j < m) :
    tiF ta m (ta j) = j := by
  obtain ⟨h1, h2⟩ := tiF_spec h (h.lt j hj)
  exact h.inj _ h1 _ hj h2

/-- The step bound of `cutProg`. -/
def cutCost (m : ℕ) : ℕ := 178 * m + 95

set_option maxHeartbeats 1000000 in
/-- **The cut map on arrays.** -/
theorem cutProg_run (c : Config) (hc : WordsBounded W c) {m RVb RTb LFb TAb Z RVo RTo : ℕ}
    (hI : CpIn c m RVb RTb LFb TAb Z RVo RTo) {rv rt lf ta : ℕ → ℕ}
    (hrv : ∀ i < m, c.nmem (RVb + i) = rv i ∧ rv i < m)
    (hrt : ∀ i < m, c.nmem (RTb + i) = rt i) (prt : PermOn rt m)
    (hlf : ∀ i < m, c.nmem (LFb + i) = lf i ∧ lf i ≤ 1)
    (hta : ∀ i < m, c.nmem (TAb + i) = ta i) (pta : PermOn ta m)
    (dRV : RVb + m ≤ Z) (dRT : RTb + m ≤ Z) (dLF : LFb + m ≤ Z) (dTA : TAb + m ≤ Z)
    (dO1 : Z + 6 * m ≤ RVo) (dO2 : RVo + 5 * m ≤ RTo) (hw : RTo + 5 * m + 1 ≤ W) :
    ∃ c' t, Exec P W cutProg c c' t ∧ t ≤ cutCost m ∧
      CutWords c'.nmem RVo RTo (reF lf m) (rkF lf rt m m) m lf (tfF lf rt m) (reF lf)
        (rkF lf rt m) ta (tiF ta m) rv rt ∧
      c'.nreg 8228 = reF lf m ∧ c'.nreg 8230 = reF lf m + rkF lf rt m m ∧
      (∀ a, (a < Z ∨ RTo + 5 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ CpScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, vTF, vR, vTI, hV, h00, h01, h02, hM, hRg, hr, hrm, ho⟩ :=
    cutPre_exec (P := P) c hc hI hrv hrt prt hlf hta pta dRV dRT dLF dTA (by omega)
  have hnE : reF lf m ≤ m := cnt_le_self _ m
  have hnT : rkF lf rt m m ≤ m := cnt_le_self _ m
  have hA : WrArr c₁ LFb (Z + 2 * m) (Z + 3 * m) (Z + 4 * m) TAb (Z + 5 * m) RVb RTb (reF lf m)
      (rkF lf rt m m) m W lf (tfF lf rt m) (reF lf) (rkF lf rt m) ta (tiF ta m) rv rt := by
    refine ⟨fun i hi => by rw [hM _ (by omega)]; exact hlf i hi,
      fun i hi => ⟨vTF i hi, by unfold tfF; split_ifs <;> omega⟩,
      fun i hi => ⟨(vR i hi).1, (cnt_le_self _ i).trans hi.le⟩,
      fun i hi => ⟨(vR i hi).2, (cnt_le_self _ i).trans hi.le⟩,
      fun i hi => ⟨by rw [hM _ (by omega)]; exact hta i hi, pta.lt i hi⟩,
      fun i hi => ⟨?_, (tiF_spec pta hi).1⟩,
      fun i hi => by rw [hM _ (by omega)]; exact hrv i hi,
      fun i hi => ⟨by rw [hM _ (by omega)]; exact hrt i hi, prt.lt i hi⟩,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    obtain ⟨h1, h2⟩ := tiF_spec pta hi
    have := vTI _ h1
    rwa [h2] at this
  have hO : WrOut LFb (Z + 2 * m) (Z + 3 * m) (Z + 4 * m) TAb (Z + 5 * m) RVb RTb m RVo RTo
      (reF lf m + 4 * rkF lf rt m m) := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> omega
  obtain ⟨c₂, k₂, e₂, hk₂, hW, fm, fR, fr, frm, fo⟩ := cutWr_exec (P := P) c₁ e₁.wb_right hV
    h00 h01 h02 hA hO
    (fun i hi h0 => cnt_lt _ hi h0)
    (fun i hi j hj h1 h2 e => cnt_inj (fun j => lf j = 0) h1 h2 e)
    (fun i hi h0 => cnt_lt _ hi h0)
    (fun i hi j hj h1 h2 e => cnt_inj (fun j => 0 < tfF lf rt m j) h1 h2 e)
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by unfold cutCost; unfold cpCost at hk₁; omega, hW,
    by rw [fR _ (by omega), hV.r28], by rw [fR _ (by omega), hV.r30],
    fun a ha => by rw [fm a (by omega) (by omega), hM a (by omega)], fun r hr => ?_,
    by rw [fr, hr], by rw [frm, hrm], by rw [fo, ho]⟩
  have : ¬ (8200 ≤ r ∧ r ≤ 8249) := fun h => hr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  rw [fR r (by omega), hRg r hr]

end MsEnc

end BKMNW

end PlanarFlow
