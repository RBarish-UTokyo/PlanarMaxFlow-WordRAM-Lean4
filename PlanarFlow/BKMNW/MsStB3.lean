module

public import PlanarFlow.BKMNW.MsStB2

/-!
# The MSSP encoder, stage B3 with the scale `N₁` kept

**`msB3_exec'`**: `msB3_exec` with the further conclusion `r7328 = isoN1 cV nD cF` (the scale
`N₁` of the isolating lengths, read back by `mrRead` through `r8013`; stage D copies it).
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

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
/-- **The piece flags and the isolating lengths** (`msB3_exec` with `r7328 = N₁` kept). -/
theorem msB3_exec' {nD cV cF IM nP CL WM : ℕ} (c : Config) (hc : WordsBounded W c)
    (r50 : c.nreg 7950 = nD) (r57 : c.nreg 7957 = cV) (r59 : c.nreg 7959 = cF)
    (r82 : c.nreg 8282 = IM) (r30 : c.nreg 8230 = nP) (r87 : c.nreg 8287 = CL)
    (r86 : c.nreg 8286 = WM) (l1 : IM + 8 * nD ≤ WM) (l2 : WM + nD ≤ CL)
    (hval : ∀ j < nD, c.nmem (CL + j) * MSSP.isoN1 cV nD cF +
      c.nmem (WM + j) * MSSP.isoN3 cV nD + MSSP.isoN2 cV nD cF + j ≤ W)
    (hW : MSSP.isoN1 cV nD cF + cV + 2 * (cF * cV) + IM + 8 * nD + CL + nD + 8 ≤ W) :
    ∃ e t, Exec P W msB3 c e t ∧ t ≤ 17 + (15 + 8) * nD + 5 ∧
      (∀ j < nD, e.nmem (IM + 6 * nD + j) = (if j < nP then 1 else 0) ∧
        e.nmem (IM + 7 * nD + j) = if j < nP then c.nmem (CL + j) * MSSP.isoN1 cV nD cF +
          c.nmem (WM + j) * MSSP.isoN3 cV nD + MSSP.isoN2 cV nD cF + j else 0) ∧
      (∀ a, (a < IM + 6 * nD ∨ IM + 8 * nD ≤ a) → e.nmem a = c.nmem a) ∧
      e.nreg 7328 = MSSP.isoN1 cV nD cF ∧
      (∀ r, (r < 7326 ∨ 7331 < r) → (r < 8200 ∨ 8219 < r) → r ≠ 8264 → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have e1 : MSSP.isoN1 cV nD cF = (cV + 1) * MSSP.isoN2 cV nD cF := by
    simp only [MSSP.isoN1]; ring
  have b2 : MSSP.isoN2 cV nD cF ≤ MSSP.isoN1 cV nD cF := by
    rw [e1]; exact Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨c₁, t₁, e₁, ht₁, a30, a31, a28, aR, am, ar, arm, ao⟩ := bSetD1_exec (P := P) c hc r50
    r57 r59 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b28, b00, b01, b02, b26, b27, bR, bm, br, brm, bo⟩ :=
    bSetD2_exec (P := P) c₁ e₁.wb_right (nD := nD) (cV := cV) (N2 := MSSP.isoN2 cV nD cF)
      (IM := IM) (nP := nP) (CL := CL) a28 a31 ((aR 7950 (by omega) (by omega) (by omega)
      (by omega)).trans r50) ((aR 8282 (by omega) (by omega) (by omega) (by omega)).trans r82)
      ((aR 8230 (by omega) (by omega) (by omega) (by omega)).trans r30)
      ((aR 8287 (by omega) (by omega) (by omega) (by omega)).trans r87) (by rw [← e1]; omega)
  obtain ⟨c₃, t₃, e₃, ht₃, d29, dR, dm, dr, drm, dO⟩ := bSetD3_exec (P := P) c₂ e₂.wb_right
    (WM := WM) ((bR 8286 (by omega) (by omega) (by omega)).trans
      ((aR 8286 (by omega) (by omega) (by omega) (by omega)).trans r86))
  have m3 : c₃.nmem = c.nmem := by rw [dm, bm, am]
  have g26 : c₃.nreg 7326 = nP := (dR _ (by omega)).trans b26
  have g27 : c₃.nreg 7327 = CL := (dR _ (by omega)).trans b27
  have g28 : c₃.nreg 7328 = MSSP.isoN1 cV nD cF := by rw [dR _ (by omega), b28, e1]
  have g30 : c₃.nreg 7330 = MSSP.isoN3 cV nD :=
    (dR _ (by omega)).trans ((bR _ (by omega) (by omega) (by omega)).trans a30)
  have g31 : c₃.nreg 7331 = MSSP.isoN2 cV nD cF :=
    (dR _ (by omega)).trans ((bR _ (by omega) (by omega) (by omega)).trans a31)
  obtain ⟨c₄, t₄, e₄, ht₄, w4, wm4, wm4', wR4, wr4, wrm4, wo4⟩ := wrLoop_exec (P := P) c₃
    e₃.wb_right (VAL := vLN) (B := 15) (m := nD) (RVo := IM + 6 * nD) (RTo := IM + 7 * nD)
    (N := nD) ((dR _ (by omega)).trans b00) ((dR _ (by omega)).trans b01)
    ((dR _ (by omega)).trans b02)
    (vLN_spec (P := P) c₃ (nD := nD) g26 g27 g28 d29 g30 g31
      (fun j hj => ⟨⟨Or.inr (by omega), Or.inr (by omega)⟩, ⟨Or.inr (by omega), Or.inr (by omega)⟩⟩)
      (fun j hj => ⟨by omega, by omega, by rw [m3]; exact hval j hj⟩) (by omega))
    (fun i hi _ => hi) (fun i hi i' hi' _ _ e => e) (Or.inl (by omega)) (by omega) (by omega)
    (by omega)
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega,
    fun j hj => ⟨?_, ?_⟩, fun a ha => ?_, by rw [wR4 _ (by omega)]; exact g28, fun r h1 h2 h3 => ?_, by rw [wr4, dr, br, ar],
    by rw [wrm4, drm, brm, arm], by rw [wo4, dO, bo, ao]⟩
  · rw [(w4 j hj rfl).1]
  · rw [(w4 j hj rfl).2, m3]
  · rw [wm4 a (by omega) (by omega), m3]
  · rw [wR4 r (by omega), dR r (by omega), bR r (by omega) (by omega) h3, aR r (by omega) (by omega)
      (by omega) h3]

end MsEnc

end BKMNW

end PlanarFlow
