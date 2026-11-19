module

public import PlanarFlow.BKMNW.MsEncC3
public import PlanarFlow.BKMNW.MsStB3

/-!
# Stage lemmas of the MSSP encoder with per-entry word bounds (generated)

Copies of the earlier stage lemmas (`MsStB2 … MsStE`, `MsEncC3`), renamed with the
suffix `W`, whose hypotheses bound every address and value by `W` separately instead of bounding
sums of several addresses (which needs `W ≥ 16 (p + R)`). The `hpProg` set-up lemmas take
`v + C ≤ W` for every value `v` they write. Same programs, same conclusions.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

section MsStB2

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}


theorem bSetD1_execW (c : Config) (hc : WordsBounded W c) {nD cV cF : ℕ}
    (r50 : c.nreg 7950 = nD) (r57 : c.nreg 7957 = cV) (r59 : c.nreg 7959 = cF)
    (hw : MSSP.isoN2 cV nD cF + cV + 2 * (cF * cV) + 2 ≤ W) :
    ∃ c' t, Exec P W bSetD1 c c' t ∧ t = 8 ∧ c'.nreg 7330 = MSSP.isoN3 cV nD ∧
      c'.nreg 7331 = MSSP.isoN2 cV nD cF ∧ c'.nreg 7328 = cV + 1 ∧
      (∀ r, r ≠ 7328 → r ≠ 7330 → r ≠ 7331 → r ≠ 8264 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have e3 : MSSP.isoN3 cV nD = cV * nD + 1 := rfl
  have e2 : MSSP.isoN2 cV nD cF = (cF * cV + cF * cV + 1) * (cV * nD + 1) := by
    simp only [MSSP.isoN2, MSSP.isoN3]; ring
  have b3 : cV * nD + 1 ≤ MSSP.isoN2 cV nD cF := by
    rw [e2]; exact Nat.le_mul_of_pos_left _ (by omega)
  have b2 : cF * cV + cF * cV + 1 ≤ MSSP.isoN2 cV nD cF := by
    rw [e2]; exact Nat.le_mul_of_pos_right _ (by omega)
  unfold bSetD1
  exec_block
  all_goals try ((try config_simp); (try simp only [r50, r57, r59]); (try rw [← e2]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r a b d e => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r50, r57, r59]; rw [e3]; done)
    | (simp only [r50, r57, r59]; rw [e2]; done)
    | (simp only [r50, r57, r59]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)


theorem bSetD2_execW (c : Config) (hc : WordsBounded W c) {nD cV N2 IM nP CL : ℕ}
    (r28 : c.nreg 7328 = cV + 1) (r31 : c.nreg 7331 = N2) (r50 : c.nreg 7950 = nD)
    (r82 : c.nreg 8282 = IM) (r30 : c.nreg 8230 = nP) (r87 : c.nreg 8287 = CL)
    (hw : (cV + 1) * N2 + 6 ≤ W ∧ IM + 7 * nD + 6 ≤ W) :
    ∃ c' t, Exec P W bSetD2 c c' t ∧ t = 8 ∧ c'.nreg 7328 = (cV + 1) * N2 ∧
      c'.nreg 8200 = nD ∧ c'.nreg 8201 = IM + 6 * nD ∧ c'.nreg 8202 = IM + 7 * nD ∧
      c'.nreg 7326 = nP ∧ c'.nreg 7327 = CL ∧
      (∀ r, (r < 7326 ∨ 7328 < r) → (r < 8200 ∨ 8202 < r) → r ≠ 8264 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSetD2
  exec_block
  all_goals try ((try config_simp); (try simp only [r28, r31, r50, r82]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r28, r31, r50, r82, r30, r87]; omega)
    | (simp only [r28, r31, r50, r82, r30, r87]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)


theorem bSetD3_execW (c : Config) (hc : WordsBounded W c) {WM : ℕ} (r86 : c.nreg 8286 = WM) :
    ∃ c' t, Exec P W bSetD3 c c' t ∧ t = 1 ∧ c'.nreg 7329 = WM ∧
      (∀ r, r ≠ 7329 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSetD3
  exec_block
  refine ⟨rfl, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · exact r86
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl


theorem bSetE_execW (c : Config) (hc : WordsBounded W c) {nD IM nP : ℕ}
    (r30 : c.nreg 8230 = nP) (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM)
    (hw : IM + 7 * nD + 7 ≤ W) :
    ∃ c' t, Exec P W bSetE c c' t ∧ t = 4 ∧ c'.nreg 7340 = nP ∧ c'.nreg 7341 = IM + 7 * nD ∧
      (∀ r, r ≠ 7340 → r ≠ 7341 → r ≠ 8264 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSetE
  exec_block
  all_goals try ((try config_simp); (try simp only [r50, r82]); omega)
  refine ⟨rfl, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r30, r50, r82]; omega)
    | (simp only [r30, r50, r82]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)


theorem bSetF1_execW (c : Config) (hc : WordsBounded W c) {nD IM LD DU GG : ℕ}
    (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM) (r88 : c.nreg 8288 = LD)
    (r89 : c.nreg 8289 = DU) (r84 : c.nreg 8284 = GG) (hw : IM + 7 * nD + 6 ≤ W) :
    ∃ c' t, Exec P W bSetF1 c c' t ∧ t = 8 ∧ c'.nreg 8200 = nD ∧ c'.nreg 8201 = LD ∧
      c'.nreg 8202 = DU ∧ c'.nreg 7332 = IM + 6 * nD ∧ c'.nreg 7333 = IM + 7 * nD ∧
      c'.nreg 7334 = c.nmem GG ∧
      (∀ r, (r < 7332 ∨ 7334 < r) → (r < 8200 ∨ 8202 < r) → r ≠ 8264 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSetF1
  exec_block
  all_goals try ((try config_simp); (try simp only [r50, r82]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r50, r82, r88, r89, r84]; omega)
    | (simp only [r50, r82, r88, r89, r84]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)


theorem bSetF2_execW (c : Config) (hc : WordsBounded W c) {w : ℕ} (r42 : c.nreg 7342 = w)
    (hw : w + 1 ≤ W) :
    ∃ c' t, Exec P W bSetF2 c c' t ∧ t = 2 ∧ c'.nreg 7335 = w + 1 ∧
      (∀ r, r ≠ 7335 → r ≠ 8264 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSetF2
  exec_block
  all_goals try ((try config_simp); (try simp only [r42]); omega)
  refine ⟨rfl, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r42]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)


set_option maxHeartbeats 2000000 in
/-- **The sum of the lengths and Dijkstra's lengths.** -/
theorem msB4_execW {nD IM nP LD DU GG : ℕ} (c : Config) (hc : WordsBounded W c)
    (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM) (r30 : c.nreg 8230 = nP)
    (r88 : c.nreg 8288 = LD) (r89 : c.nreg 8289 = DU) (r84 : c.nreg 8284 = GG) (hnP : nP ≤ nD)
    (his : ∀ j < nD, c.nmem (IM + 6 * nD + j) ≤ 1) (l1 : IM + 8 * nD ≤ LD)
    (l2 : LD + nD ≤ DU) (l3 : GG < LD)
    (hs : 2 * (∑ j ∈ range nP, c.nmem (IM + 7 * nD + j) + 1) ≤ W)
    (hln : ∀ j < nD, c.nmem (IM + 7 * nD + j) ≤ W) (hW : DU + nD + 8 ≤ W)
    (hG : c.nmem GG ≤ W) :
    ∃ e t, Exec P W msB4 c e t ∧ t ≤ 4 + (6 * nP + 5) + 10 + (18 + 8) * nD + 5 ∧
      e.nreg 7342 = ∑ j ∈ range nP, c.nmem (IM + 7 * nD + j) ∧
      e.nreg 7335 = ∑ j ∈ range nP, c.nmem (IM + 7 * nD + j) + 1 ∧
      (∀ j < nD, e.nmem (LD + j) =
        if c.nmem (IM + 6 * nD + j) = 1 then c.nmem (IM + 7 * nD + j)
        else if j = c.nmem GG then ∑ i ∈ range nP, c.nmem (IM + 7 * nD + i) + 1
        else 2 * (∑ i ∈ range nP, c.nmem (IM + 7 * nD + i) + 1)) ∧
      (∀ a, (a < LD ∨ LD + nD ≤ a) → (a < DU ∨ DU + nD ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 7332 ∨ 7345 < r) → (r < 8200 ∨ 8219 < r) → r ≠ 8264 → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  set w := ∑ j ∈ range nP, c.nmem (IM + 7 * nD + j) with hwd
  obtain ⟨c₁, t₁, e₁, ht₁, a40, a41, aR, am, ar, arm, ao⟩ := bSetE_execW (P := P) c hc r30 r50 r82
    (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, s42, sR, sm, sr, srm, so⟩ := smLoop_exec (P := P) c₁ e₁.wb_right a40 a41
    (by omega) (by rw [am]; omega) (by omega)
  rw [am] at s42
  have q2 : ∀ r, (r < 7340 ∨ 7345 < r) → r ≠ 8264 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [sR r (by omega), aR r (by omega) (by omega) h2]
  obtain ⟨c₃, t₃, e₃, ht₃, f00, f01, f02, f32, f33, f34, fR, fm, fr, frm, fo⟩ :=
    bSetF1_execW (P := P) c₂ e₂.wb_right (nD := nD) (IM := IM) (LD := LD) (DU := DU) (GG := GG)
      ((q2 _ (by omega) (by omega)).trans r50) ((q2 _ (by omega) (by omega)).trans r82)
      ((q2 _ (by omega) (by omega)).trans r88) ((q2 _ (by omega) (by omega)).trans r89)
      ((q2 _ (by omega) (by omega)).trans r84) (by omega)
  rw [sm, am] at f34
  obtain ⟨c₄, t₄, e₄, ht₄, g35, gR, gm, gr, grm, go⟩ := bSetF2_execW (P := P) c₃ e₃.wb_right
    (w := w) ((fR _ (by omega) (by omega) (by omega)).trans s42) (by omega)
  have m4 : c₄.nmem = c.nmem := by rw [gm, fm, sm, am]
  obtain ⟨c₅, t₅, e₅, ht₅, w5, wm5, wm5', wR5, wr5, wrm5, wo5⟩ := wrLoop_exec (P := P) c₄
    e₄.wb_right (VAL := vLD) (B := 18) (m := nD) (RVo := LD) (RTo := DU) (N := nD)
    ((gR _ (by omega) (by omega)).trans f00) ((gR _ (by omega) (by omega)).trans f01)
    ((gR _ (by omega) (by omega)).trans f02)
    (vLD_spec (P := P) c₄ (nD := nD) ((gR _ (by omega) (by omega)).trans f32)
      ((gR _ (by omega) (by omega)).trans f33) ((gR _ (by omega) (by omega)).trans f34) g35
      (fun j hj => ⟨⟨Or.inl (by omega), Or.inl (by omega)⟩, ⟨Or.inl (by omega), Or.inl (by omega)⟩⟩)
      (fun j hj => by rw [m4]; exact his j hj)
      (fun j hj => ⟨by omega, by omega, by rw [m4]; exact hln j hj⟩) (by omega) (by omega)
      (by omega) (by omega))
    (fun i hi _ => hi) (fun i hi i' hi' _ _ e => e) (Or.inl l2) (by omega) (by omega) (by omega)
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    ?_, ?_, fun j hj => ?_, fun a h1 h2 => ?_, fun r h1 h2 h3 => ?_, by rw [wr5, gr, fr, sr, ar],
    by rw [wrm5, grm, frm, srm, arm], by rw [wo5, go, fo, so, ao]⟩
  · rw [wR5 _ (by omega), gR _ (by omega) (by omega), fR _ (by omega) (by omega) (by omega)]
    exact s42
  · rw [wR5 _ (by omega)]; exact g35
  · rw [(w5 j hj rfl).1, m4]
  · rw [wm5 a h1 h2, m4]
  · rw [wR5 r (by omega), gR r (by omega) h3, fR r (by omega) (by omega) h3, q2 r (by omega) h3]


end MsStB2

section MsStB3

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}


set_option maxHeartbeats 2000000 in
/-- **The piece flags and the isolating lengths** (`msB3_exec` with `r7328 = N₁` kept). -/
theorem msB3_execW' {nD cV cF IM nP CL WM : ℕ} (c : Config) (hc : WordsBounded W c)
    (r50 : c.nreg 7950 = nD) (r57 : c.nreg 7957 = cV) (r59 : c.nreg 7959 = cF)
    (r82 : c.nreg 8282 = IM) (r30 : c.nreg 8230 = nP) (r87 : c.nreg 8287 = CL)
    (r86 : c.nreg 8286 = WM) (l1 : IM + 8 * nD ≤ WM) (l2 : WM + nD ≤ CL)
    (hval : ∀ j < nD, c.nmem (CL + j) * MSSP.isoN1 cV nD cF +
      c.nmem (WM + j) * MSSP.isoN3 cV nD + MSSP.isoN2 cV nD cF + j ≤ W)
    (hW : MSSP.isoN1 cV nD cF + cV + 2 * (cF * cV) + 8 ≤ W ∧ CL + nD + 8 ≤ W) :
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
  obtain ⟨c₁, t₁, e₁, ht₁, a30, a31, a28, aR, am, ar, arm, ao⟩ := bSetD1_execW (P := P) c hc r50
    r57 r59 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b28, b00, b01, b02, b26, b27, bR, bm, br, brm, bo⟩ :=
    bSetD2_execW (P := P) c₁ e₁.wb_right (nD := nD) (cV := cV) (N2 := MSSP.isoN2 cV nD cF)
      (IM := IM) (nP := nP) (CL := CL) a28 a31 ((aR 7950 (by omega) (by omega) (by omega)
      (by omega)).trans r50) ((aR 8282 (by omega) (by omega) (by omega) (by omega)).trans r82)
      ((aR 8230 (by omega) (by omega) (by omega) (by omega)).trans r30)
      ((aR 8287 (by omega) (by omega) (by omega) (by omega)).trans r87) (by rw [← e1]; omega)
  obtain ⟨c₃, t₃, e₃, ht₃, d29, dR, dm, dr, drm, dO⟩ := bSetD3_execW (P := P) c₂ e₂.wb_right
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


end MsStB3

section MsStC3

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}

open STFlow

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]


theorem svSet_execW (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W svSet c c' t ∧ t = 3 ∧ c'.nreg 8297 = c.nreg 7950 ∧
      c'.nreg 8298 = c.nreg 7957 ∧ c'.nreg 8299 = c.nreg 7959 ∧
      (∀ r, r < 8297 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold svSet
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | rfl
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)


theorem rsSet_execW (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W rsSet c c' t ∧ t = 3 ∧ c'.nreg 7950 = c.nreg 8297 ∧
      c'.nreg 7957 = c.nreg 8298 ∧ c'.nreg 7959 = c.nreg 8299 ∧
      (∀ r, r ≠ 7950 → r ≠ 7957 → r ≠ 7959 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rsSet
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | rfl
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)


theorem kiSet_execW (c : Config) (hc : WordsBounded W c) {nD cV cF IM k A0 Z p m : ℕ}
    (r97 : c.nreg 8297 = nD) (r98 : c.nreg 8298 = cV) (r99 : c.nreg 8299 = cF)
    (r82 : c.nreg 8282 = IM) (r56 : c.nreg 8156 = k) (r90 : c.nreg 8290 = A0)
    (r92 : c.nreg 8292 = Z) (r80 : c.nreg 8280 = p) (r00 : c.nreg 8000 = m)
    (hW : nD + 37 ≤ W ∧ IM + 4 * nD + 37 ≤ W ∧ IM + nD + 37 ≤ W ∧ IM + 37 ≤ W ∧ IM + 21 * nD + k + 3 + 37 ≤ W ∧ 4 * nD + 1 + 37 ≤ W ∧ 2 * nD + 1 + 37 ≤ W ∧ cV + 37 ≤ W ∧ cF + 37 ≤ W ∧ A0 + 37 * nD + 10 + 37 ≤ W ∧ Z + 37 ≤ W ∧ p + 16 * m + 37 ≤ W) :
    ∃ c', Exec P W kiSet c c' (hpCost kiL) ∧
      c'.nreg 7980 = nD ∧ c'.nreg 7981 = IM + 4 * nD ∧ c'.nreg 7982 = IM + nD ∧
      c'.nreg 7983 = IM ∧ c'.nreg 7984 = IM + 21 * nD + k + 3 ∧ c'.nreg 7985 = 4 * nD + 1 ∧
      c'.nreg 7986 = 2 * nD + 1 ∧ c'.nreg 7987 = cV ∧ c'.nreg 7988 = cF ∧
      c'.nreg 7989 = A0 + 37 * nD + 10 ∧ c'.nreg 7990 = Z ∧ c'.nreg 7991 = p + 16 * m ∧
      (∀ r, (r < 7980 ∨ 7992 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 7980 7370 kiL :=
    hpShape_ok kiL_shape (by omega) (by omega) (by simp [kiL]) (by omega) (by simp [kiL])
  have h98 := hc.1 8298
  have h99 := hc.1 8299
  have h92 := hc.1 8292
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) kiL 7980 hok c hc (fun e he => by
    simp only [kiL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r97,
        r98, r99, r82, r56, r90, r92, r80, r00] <;> omega)
  have g : ∀ j < 12, c'.nreg (7980 + j) =
      hpSum c.nreg (kiL.getD j ([], 0)).1 - (kiL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [kiL]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [kiL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 1 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 2 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 3 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 4 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 5 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 6 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 7 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 8 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 9 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 10 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring
  · have := g 11 (by omega); simp [kiL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r98, r99, r82, r56, r90, r92, r80, r00]; try ring


theorem ggCp_execW (c : Config) (hc : WordsBounded W c) {GG Gb : ℕ} (r84 : c.nreg 8284 = GG)
    (r91 : c.nreg 7991 = Gb) (hGb : Gb + 1 ≤ W) (hGG : GG + 1 ≤ W)
    (hd : GG + 2 ≤ Gb ∨ Gb + 2 ≤ GG) :
    ∃ c' t, Exec P W ggCp c c' t ∧ t = 7 ∧ c'.nmem Gb = c.nmem GG ∧
      c'.nmem (Gb + 1) = c.nmem (GG + 1) ∧
      (∀ a, a ≠ Gb → a ≠ Gb + 1 → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 7360 ∨ 7368 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h1 := hc.2 GG
  have h2 := hc.2 (GG + 1)
  unfold ggCp
  exec_block
  all_goals try ((try config_simp); (try simp only [r84, r91]); omega)
  refine ⟨rfl, ?_, ?_, fun a a1 a2 => ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals (try simp only [r84, r91])
  all_goals (simp only [upd_apply]; split_ifs <;> first | omega | rfl)


theorem osSet_execW (c : Config) (hc : WordsBounded W c) {nD IM k Ob : ℕ}
    (r97 : c.nreg 8297 = nD) (r82 : c.nreg 8282 = IM) (r56 : c.nreg 8156 = k)
    (r93 : c.nreg 8293 = Ob) (hW : nD + 20 ≤ W ∧ 4 * nD + 1 + 20 ≤ W ∧ IM + 4 * nD + 20 ≤ W ∧ IM + 6 * nD + 20 ≤ W ∧ Ob + 20 ≤ W ∧ Ob + 4 * nD + 2 + 20 ≤ W ∧ IM + 12 * nD + 1 + k + 20 ≤ W ∧ IM + 16 * nD + 2 + k + 20 ≤ W ∧ IM + 20 * nD + 3 + k + 20 ≤ W) :
    ∃ c', Exec P W osSet c c' (hpCost osL) ∧
      c'.nreg 1500 = nD ∧ c'.nreg 1501 = 4 * nD + 1 ∧ c'.nreg 1502 = IM + 4 * nD ∧
      c'.nreg 1504 = IM + 6 * nD ∧ c'.nreg 1505 = Ob ∧ c'.nreg 1506 = Ob + 4 * nD + 2 ∧
      c'.nreg 1507 = IM + 12 * nD + 1 + k ∧ c'.nreg 1508 = IM + 16 * nD + 2 + k ∧
      c'.nreg 1509 = IM + 20 * nD + 3 + k ∧
      (∀ r, (r < 1500 ∨ 1510 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 1500 7370 osL :=
    hpShape_ok osL_shape (by omega) (by omega) (by simp [osL]) (by omega) (by simp [osL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) osL 1500 hok c hc (fun e he => by
    simp only [osL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r97,
        r82, r56, r93] <;> omega)
  have g : ∀ j < 10, c'.nreg (1500 + j) =
      hpSum c.nreg (osL.getD j ([], 0)).1 - (osL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [osL]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [osL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 1 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 2 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 4 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 5 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 6 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 7 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 8 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring
  · have := g 9 (by omega); simp [osL, hpSum, hpM.ev] at this; rw [this]; simp only [r97, r82, r56, r93]; try ring


set_option maxHeartbeats 4000000 in
/-- **Stage C2a: the trees** (the words of `KInit`, for any memory agreeing on their region). -/
theorem msC2a_execW [Nonempty D] {M : CombMap D V F} (hM : M.IsPlane) {nD nF nV : ℕ}
    (σ : D ≃ Fin nD) (τv : F ≃ Fin nF) (τf : V ≃ Fin nV) {T₀ : DTree M} (d₀ : D)
    (hroot : T₀.root = M.face d₀) {IM A0 Z p m k GG : ℕ} (c : Config) (hc : WordsBounded W c)
    (r97 : c.nreg 8297 = nD) (r98 : c.nreg 8298 = nF) (r99 : c.nreg 8299 = nV)
    (r82 : c.nreg 8282 = IM) (r56 : c.nreg 8156 = k) (r90 : c.nreg 8290 = A0)
    (r92 : c.nreg 8292 = Z) (r80 : c.nreg 8280 = p) (r00 : c.nreg 8000 = m)
    (r84 : c.nreg 8284 = GG)
    (hNT : ∀ d, c.nmem (IM + 4 * nD + σ d) = 1 + τv (M.face d))
    (hNF : ∀ d, c.nmem (IM + nD + σ d) = 2 * nD + 1 + τf (M.tail d))
    (hRV : ∀ d, c.nmem (IM + σ d) = σ (M.rev d))
    (hPAR : ∀ x, x ≠ T₀.root → c.nmem (A0 + 37 * nD + 10 + 1 + τv x) = σ (T₀.par x))
    (hG0 : c.nmem GG = σ d₀) (hG1 : c.nmem (GG + 1) = σ d₀)
    (hnF : nF ≤ 4 * nD + 1) (hnV : nV ≤ 4 * nD + 1)
    (l1 : p + 16 * m + 2 ≤ IM) (l2 : IM + 37 * nD + k + 9 ≤ GG) (l3 : GG + 2 ≤ A0)
    (l4 : A0 + 37 * nD + 11 + nF ≤ Z)
    (hW : Z + 8 * nF + 4 * nD + 15 * nV + 40 ≤ W) :
    ∃ e t, Exec P W msC2a c e t ∧ t ≤ hpCost kiL + 7 + StEnc.kiCost nD nF nV ∧
      ∃ (ts : List F) (C₀ : DTree M.dual) (cs : List V), C₀.root = M.tail d₀ ∧
        (∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) ∧
        (∀ mem : ℕ → ℕ, (∀ a, IM + 21 * nD + k + 3 ≤ a → a < IM + 37 * nD + k + 11 →
            mem a = e.nmem a) → ∀ Pk : Input, (∀ j, j < Klein.iHD nD (4 * nD + 1) k + 4 →
            Pk.data.getD j 0 = mem (IM + j)) →
          Klein.KInit M.dual σ (fun x => 1 + (τv x : ℕ)) (fun v => 2 * nD + 1 + (τf v : ℕ))
            (4 * nD + 1) k (toDD T₀) C₀ ((List.finRange nF).map τv.symm) ts
            ((List.finRange nV).map τf.symm) cs Pk) ∧
        (∀ a, (a < IM + 21 * nD + k + 3 ∨ IM + 37 * nD + k + 13 ≤ a) → a ≠ p + 16 * m →
          a ≠ p + 16 * m + 1 → (a < A0 + 37 * nD + 11 ∨ A0 + 37 * nD + 11 + nF ≤ a) →
          (a < Z ∨ Z + 8 * nF + 4 * nD + 15 * nV + 3 ≤ a) → e.nmem a = c.nmem a) ∧
        (∀ r, (r < 1400 ∨ 1720 ≤ r) → (r < 7360 ∨ 7372 ≤ r) → (r < 7980 ∨ 8000 ≤ r) →
          e.nreg r = c.nreg r) ∧
        e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := kiOff nD k
  have hσ : ∀ d, (σ d : ℕ) < nD := fun d => (σ d).2
  obtain ⟨c₁, e₁, a80, a81, a82, a83, a84, a85, a86, a87, a88, a89, a90, a91, aR, am, ar, arm,
    ao⟩ := kiSet_execW (P := P) c hc r97 r98 r99 r82 r56 r90 r92 r80 r00 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, g0, g1, gm, gR, gr, grm, go⟩ :=
    ggCp_execW (P := P) c₁ e₁.wb_right (GG := GG) (Gb := p + 16 * m)
      (by rw [aR _ (by omega) (by omega) (by omega)]; exact r84) a91 (by omega) (by omega)
      (Or.inr (by omega))
  rw [am] at g0 g1
  have m2 : ∀ a, a ≠ p + 16 * m → a ≠ p + 16 * m + 1 → c₂.nmem a = c.nmem a := fun a h1 h2 => by
    rw [gm a h1 h2, am]
  have q2 : ∀ r, (r < 7360 ∨ 7368 < r) → c₂.nreg r = c₁.nreg r := gR
  obtain ⟨c₃, t₃, e₃, ht₃, ts, C₀, cs, hC₀, hoff, hOT, hOC, hIV, hIT, hIF, hIC, hH0, hH1, hH2, hH3,
    m3, R3, rr3, rm3, o3⟩ :=
    StEnc.kiProg_exec (P := P) hM σ τv τf d₀ d₀ hroot (NTb := IM + 4 * nD) (NFb := IM + nD)
      (RVb := IM) (IVb := IM + 21 * nD + k + 3) (ofF := 2 * nD + 1) (PRb := A0 + 37 * nD + 10)
      (Z := Z) (Gb := p + 16 * m) (n := 4 * nD + 1) c₂ e₂.wb_right
      (by rw [q2 _ (by omega)]; exact a80) (by rw [q2 _ (by omega)]; exact a81)
      (by rw [q2 _ (by omega)]; exact a82) (by rw [q2 _ (by omega)]; exact a83)
      (by rw [q2 _ (by omega)]; exact a84) (by rw [q2 _ (by omega)]; exact a85)
      (by rw [q2 _ (by omega)]; exact a86) (by rw [q2 _ (by omega)]; exact a87)
      (by rw [q2 _ (by omega)]; exact a88) (by rw [q2 _ (by omega)]; exact a89)
      (by rw [q2 _ (by omega)]; exact a90) (by rw [q2 _ (by omega)]; exact a91)
      (fun d => by have := hσ d; rw [m2 _ (by omega) (by omega)]; exact hNT d)
      (fun d => by have := hσ d; rw [m2 _ (by omega) (by omega)]; exact hNF d)
      (fun d => by have := hσ d; rw [m2 _ (by omega) (by omega)]; exact hRV d)
      (fun x hx => by
        have := (τv x).2
        rw [m2 _ (by omega) (by omega)]; exact hPAR x hx)
      (g0.trans hG0) (g1.trans hG1) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) hnF hnV
      (by omega) (by omega)
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, ts, C₀, cs, hC₀, hoff,
    fun mem hmem Pk hPk => ?_, fun a h1 h2 h3 h4 h5 => ?_, fun r h1 h2 h3 => ?_,
    by rw [rr3, gr, ar], by rw [rm3, grm, arm], by rw [o3, go, ao]⟩
  · refine MsEnc.kInit_ofK σ τv τf hOT hOC (ib := IM) (mem := mem) (fun i h => ?_)
      (fun i h => ?_) (fun i h => ?_) (fun i h => ?_) ?_ ?_ ?_ ?_ Pk hPk hnF hnV
    · have : i < nF := by simpa using h
      rw [hn1, show IM + (21 * nD + k + 3) + i = IM + 21 * nD + k + 3 + i by ring,
        hmem _ (by omega) (by omega)]; exact hIV i h
    · have : ts.length ≤ nF := by
        have h1 := hOT.ylen; have h2 := Fintype.card_fin nF ▸ Fintype.card_congr τv; omega
      rw [hn1, show IM + (21 * nD + k + 3) + (4 * nD + 1) + i =
        IM + 21 * nD + k + 3 + (4 * nD + 1) + i by ring, hmem _ (by omega) (by omega)]
      exact hIT i h
    · have : i < nV := by simpa using h
      rw [hn1, show IM + (21 * nD + k + 3) + 2 * (4 * nD + 1) + i =
        IM + 21 * nD + k + 3 + 2 * (4 * nD + 1) + i by ring, hmem _ (by omega) (by omega)]
      exact hIF i h
    · have : cs.length ≤ nV := by
        have h1 := hOC.ylen; have h2 := Fintype.card_fin nV ▸ Fintype.card_congr τf; omega
      rw [hn1, show IM + (21 * nD + k + 3) + 3 * (4 * nD + 1) + i =
        IM + 21 * nD + k + 3 + 3 * (4 * nD + 1) + i by ring, hmem _ (by omega) (by omega)]
      exact hIC i h
    · rw [hn1, show IM + (21 * nD + k + 3) + 4 * (4 * nD + 1) =
        IM + 21 * nD + k + 3 + 4 * (4 * nD + 1) by ring, hmem _ (by omega) (by omega)]
      exact hH0
    · rw [hn1, show IM + (21 * nD + k + 3) + 4 * (4 * nD + 1) + 1 =
        IM + 21 * nD + k + 3 + 4 * (4 * nD + 1) + 1 by ring, hmem _ (by omega) (by omega)]
      exact hH1
    · rw [hn1, show IM + (21 * nD + k + 3) + 4 * (4 * nD + 1) + 2 =
        IM + 21 * nD + k + 3 + 4 * (4 * nD + 1) + 2 by ring, hmem _ (by omega) (by omega)]
      exact hH2
    · rw [hn1, show IM + (21 * nD + k + 3) + 4 * (4 * nD + 1) + 3 =
        IM + 21 * nD + k + 3 + 4 * (4 * nD + 1) + 3 by ring, hmem _ (by omega) (by omega)]
      exact hH3
  · rw [m3 a (by omega) h4 h5, m2 a h2 h3]
  · rw [R3 r (by omega), q2 r (by omega), aR r (by omega) (by omega) (by omega)]


set_option maxHeartbeats 2000000 in
/-- **Stage C2b: the out-lists** (`KOut` for any input agreeing with the image). -/
theorem msC2b_execW {N : CombMap D' X Y} {S : Finset D'} {nD : ℕ} (σ' : D' ≃ Fin nD)
    {ιv : X → ℕ} (hinj : Function.Injective ιv) (hιv : ∀ x, ιv x < 4 * nD + 1)
    {IM k Ob : ℕ} (c : Config) (hc : WordsBounded W c)
    (r97 : c.nreg 8297 = nD) (r82 : c.nreg 8282 = IM) (r56 : c.nreg 8156 = k)
    (r93 : c.nreg 8293 = Ob)
    (hNT' : ∀ d, c.nmem (IM + Klein.iNT nD + σ' d) = ιv (N.tail d))
    (hIS : ∀ d, c.nmem (IM + Klein.iIS nD + σ' d) = if d ∈ S then 1 else 0)
    (l1 : IM + 21 * nD + k + 3 ≤ Ob) (hW : Ob + 2 * (4 * nD + 1) + 40 ≤ W) :
    ∃ e t, Exec P W msC2b c e t ∧ t ≤ hpCost osL + osCost nD (4 * nD + 1) ∧
      (∀ Pk : Input, (∀ i < Klein.iOL nD (4 * nD + 1) k + nD,
          Pk.data.getD i 0 = e.nmem (IM + i)) →
        Klein.KOut N S σ' ιv (4 * nD + 1) k Pk) ∧
      (∀ a, (a < Ob ∨ Ob + 2 * (4 * nD + 1) + 1 ≤ a) →
        (a < IM + 12 * nD + 1 + k ∨ IM + 21 * nD + k + 3 ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 1500 ∨ 1521 ≤ r) → r ≠ 7370 → r ≠ 7371 → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := kiOff nD k
  have hσ' : ∀ d, (σ' d : ℕ) < nD := fun d => (σ' d).2
  obtain ⟨c₄, e₄, b00, b01, b02, b04, b05, b06, b07, b08, b09, bR, bm, br, brm, bo⟩ :=
    osSet_execW (P := P) c hc (nD := nD) (IM := IM) (k := k) (Ob := Ob) r97 r82 r56 r93 (by omega)
  obtain ⟨c₅, t₅, e₅, ht₅, hKO, m5, R5, rr5, rm5, o5⟩ :=
    osProg_kout (P := P) (M := N) (S := S) σ' (n := 4 * nD + 1) (k := k) (β := IM) (Ob := Ob)
      hinj hιv (Or.inr (by rw [hn2]; omega)) ⟨by omega, by rw [hn2]; omega, by omega, by omega⟩
      c₄ e₄.wb_right (fun d => by rw [bm]; exact hNT' d) (fun d => by rw [bm]; exact hIS d)
      b00 b01 (by rw [b02]; rfl) (by rw [b04]; rfl) b05 (by rw [b06]; ring)
      (by rw [b07, hn3]; ring) (by rw [b08, hn4]; ring) (by rw [b09, hn2]; ring)
  refine ⟨c₅, _, .seq e₄ e₅, by omega, hKO, fun a h1 h2 => ?_, fun r h1 h2 h3 => ?_,
    by rw [rr5, br], by rw [rm5, brm], by rw [o5, bo]⟩
  · rw [m5 a h1 (by rw [hn3, hn2]; omega), bm]
  · rw [R5 r (by omega), bR r (by omega) h2 h3]


end MsStC3

section MsStC4

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}


theorem scA_execW (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W scA c c' t ∧ t = 7 ∧ c'.nreg 8180 = c.nreg 7335 ∧
      c'.nreg 8181 = c.nreg 8282 ∧ c'.nreg 8182 = c.nreg 8297 ∧ c'.nreg 8183 = c.nreg 8290 ∧
      c'.nreg 8184 = c.nreg 8280 ∧ c'.nreg 8185 = c.nreg 8228 ∧ c'.nreg 8186 = c.nreg 8156 ∧
      (∀ r, (r < 8180 ∨ 8187 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold scA
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | rfl
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)


theorem scB_execW (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W scB c c' t ∧ t = 7 ∧ c'.nreg 8187 = c.nreg 8157 ∧
      c'.nreg 8188 = c.nreg 8000 ∧ c'.nreg 8189 = c.nreg 8289 ∧ c'.nreg 8190 = c.nreg 8007 ∧
      c'.nreg 8191 = c.nreg 8006 ∧ c'.nreg 8192 = c.nreg 8294 ∧ c'.nreg 8193 = c.nreg 8295 ∧
      (∀ r, (r < 8187 ∨ 8194 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold scB
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | rfl
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)


theorem xtA_execW (c : Config) (hc : WordsBounded W c) {p nE m : ℕ}
    (s84 : c.nreg 8184 = p) (s85 : c.nreg 8185 = nE) (s88 : c.nreg 8188 = m)
    (hW : p + 8 * m + 37 ≤ W ∧ p + 6 * m + 37 ≤ W ∧ p + 14 * m + 37 ≤ W ∧ nE + 37 ≤ W) :
    ∃ c', Exec P W xtA c c' (hpCost xtAL) ∧
      c'.nreg 7336 = p + 8 * m ∧
      c'.nreg 7337 = p + 6 * m ∧
      c'.nreg 7338 = p + 14 * m ∧
      c'.nreg 7339 = nE ∧
      (∀ r, (r < 7336 ∨ 7340 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 7336 7370 xtAL :=
    hpShape_ok xtAL_shape (by omega) (by omega) (by simp [xtAL]) (by omega) (by simp [xtAL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) xtAL 7336 hok c hc (fun e he => by
    simp only [xtAL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s84, s85, s88] <;> omega)
  have g : ∀ j < 4, c'.nreg (7336 + j) =
      hpSum c.nreg (xtAL.getD j ([], 0)).1 - (xtAL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [xtAL]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [xtAL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [xtAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s85, s88] <;> first | omega | ring
  · have := g 1 (by omega); simp [xtAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s85, s88] <;> first | omega | ring
  · have := g 2 (by omega); simp [xtAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s85, s88] <;> first | omega | ring
  · have := g 3 (by omega); simp [xtAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s85, s88] <;> first | omega | ring


theorem xtB_execW (c : Config) (hc : WordsBounded W c) {H IM nD A0 : ℕ}
    (s80 : c.nreg 8180 = H) (s81 : c.nreg 8181 = IM) (s82 : c.nreg 8182 = nD) (s83 : c.nreg 8183 = A0)
    (hW : IM + 5 * nD + 37 ≤ W ∧ A0 + 21 * nD + 6 + 37 ≤ W ∧ H + 37 ≤ W) :
    ∃ c', Exec P W xtB c c' (hpCost xtBL) ∧
      c'.nreg 7346 = IM + 5 * nD ∧
      c'.nreg 7347 = A0 + 21 * nD + 6 ∧
      c'.nreg 7348 = H ∧
      (∀ r, (r < 7346 ∨ 7349 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 7346 7370 xtBL :=
    hpShape_ok xtBL_shape (by omega) (by omega) (by simp [xtBL]) (by omega) (by simp [xtBL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) xtBL 7346 hok c hc (fun e he => by
    simp only [xtBL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s80, s81, s82, s83] <;> omega)
  have g : ∀ j < 3, c'.nreg (7346 + j) =
      hpSum c.nreg (xtBL.getD j ([], 0)).1 - (xtBL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [xtBL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [xtBL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [xtBL, hpSum, hpM.ev] at this; rw [this]; simp only [s80, s81, s82, s83] <;> first | omega | ring
  · have := g 1 (by omega); simp [xtBL, hpSum, hpM.ev] at this; rw [this]; simp only [s80, s81, s82, s83] <;> first | omega | ring
  · have := g 2 (by omega); simp [xtBL, hpSum, hpM.ev] at this; rw [this]; simp only [s80, s81, s82, s83] <;> first | omega | ring


theorem xtW_execW (c : Config) (hc : WordsBounded W c) {IM nD k t : ℕ}
    (s81 : c.nreg 8181 = IM) (s82 : c.nreg 8182 = nD) (s86 : c.nreg 8186 = k) (s87 : c.nreg 8187 = t)
    (hW : t + 37 ≤ W ∧ IM + 37 * nD + k + 11 + 37 ≤ W ∧ IM + 37 * nD + k + 11 + t + 37 ≤ W) :
    ∃ c', Exec P W xtW c c' (hpCost xtWL) ∧
      c'.nreg 8200 = t ∧
      c'.nreg 8201 = IM + 37 * nD + k + 11 ∧
      c'.nreg 8202 = IM + 37 * nD + k + 11 + t ∧
      (∀ r, (r < 8200 ∨ 8203 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8200 7370 xtWL :=
    hpShape_ok xtWL_shape (by omega) (by omega) (by simp [xtWL]) (by omega) (by simp [xtWL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) xtWL 8200 hok c hc (fun e he => by
    simp only [xtWL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s81, s82, s86, s87] <;> omega)
  have g : ∀ j < 3, c'.nreg (8200 + j) =
      hpSum c.nreg (xtWL.getD j ([], 0)).1 - (xtWL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [xtWL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [xtWL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [xtWL, hpSum, hpM.ev] at this; rw [this]; simp only [s81, s82, s86, s87] <;> first | omega | ring
  · have := g 1 (by omega); simp [xtWL, hpSum, hpM.ev] at this; rw [this]; simp only [s81, s82, s86, s87] <;> first | omega | ring
  · have := g 2 (by omega); simp [xtWL, hpSum, hpM.ev] at this; rw [this]; simp only [s81, s82, s86, s87] <;> first | omega | ring


theorem mkW_execW (c : Config) (hc : WordsBounded W c) {nD t DU : ℕ}
    (s82 : c.nreg 8182 = nD) (s87 : c.nreg 8187 = t) (s89 : c.nreg 8189 = DU)
    (hW : t + 37 ≤ W ∧ 4 * nD + 1 + 37 ≤ W ∧ DU + 37 ≤ W) :
    ∃ c', Exec P W mkW c c' (hpCost mkWL) ∧
      c'.nreg 8200 = t ∧
      c'.nreg 8201 = 4 * nD + 1 ∧
      c'.nreg 8202 = DU ∧
      (∀ r, (r < 8200 ∨ 8203 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8200 7370 mkWL :=
    hpShape_ok mkWL_shape (by omega) (by omega) (by simp [mkWL]) (by omega) (by simp [mkWL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) mkWL 8200 hok c hc (fun e he => by
    simp only [mkWL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s82, s87, s89] <;> omega)
  have g : ∀ j < 3, c'.nreg (8200 + j) =
      hpSum c.nreg (mkWL.getD j ([], 0)).1 - (mkWL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [mkWL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [mkWL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [mkWL, hpSum, hpM.ev] at this; rw [this]; simp only [s82, s87, s89] <;> first | omega | ring
  · have := g 1 (by omega); simp [mkWL, hpSum, hpM.ev] at this; rw [this]; simp only [s82, s87, s89] <;> first | omega | ring
  · have := g 2 (by omega); simp [mkWL, hpSum, hpM.ev] at this; rw [this]; simp only [s82, s87, s89] <;> first | omega | ring


theorem slA_execW (c : Config) (hc : WordsBounded W c) {p m Qb : ℕ}
    (s84 : c.nreg 8184 = p) (s88 : c.nreg 8188 = m) (s90 : c.nreg 8190 = Qb)
    (hW : Qb + 37 ≤ W ∧ p + m + 37 ≤ W ∧ p + 9 * m - 1 + 37 ≤ W) :
    ∃ c', Exec P W slA c c' (hpCost slAL) ∧
      c'.nreg 8270 = Qb ∧
      c'.nreg 8271 = p + m ∧
      c'.nreg 8272 = p + 9 * m - 1 ∧
      (∀ r, (r < 8270 ∨ 8273 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8270 7370 slAL :=
    hpShape_ok slAL_shape (by omega) (by omega) (by simp [slAL]) (by omega) (by simp [slAL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) slAL 8270 hok c hc (fun e he => by
    simp only [slAL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s84, s88, s90] <;> omega)
  have g : ∀ j < 3, c'.nreg (8270 + j) =
      hpSum c.nreg (slAL.getD j ([], 0)).1 - (slAL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [slAL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [slAL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [slAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s88, s90] <;> first | omega | ring
  · have := g 1 (by omega); simp [slAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s88, s90] <;> first | omega | ring
  · have := g 2 (by omega); simp [slAL, hpSum, hpM.ev] at this; rw [this]; simp only [s84, s88, s90] <;> first | omega | ring


theorem slW_execW (c : Config) (hc : WordsBounded W c) {q SL TI : ℕ}
    (s91 : c.nreg 8191 = q) (s92 : c.nreg 8192 = SL) (s93 : c.nreg 8193 = TI)
    (hW : q + 37 ≤ W ∧ SL + 37 ≤ W ∧ TI + 37 ≤ W) :
    ∃ c', Exec P W slW c c' (hpCost slWL) ∧
      c'.nreg 8200 = q ∧
      c'.nreg 8201 = SL ∧
      c'.nreg 8202 = TI ∧
      (∀ r, (r < 8200 ∨ 8203 ≤ r) → r ≠ 7370 → r ≠ 7371 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8200 7370 slWL :=
    hpShape_ok slWL_shape (by omega) (by omega) (by simp [slWL]) (by omega) (by simp [slWL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) slWL 8200 hok c hc (fun e he => by
    simp only [slWL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, s91, s92, s93] <;> omega)
  have g : ∀ j < 3, c'.nreg (8200 + j) =
      hpSum c.nreg (slWL.getD j ([], 0)).1 - (slWL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [slWL]; omega)
  refine ⟨c', e, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [slWL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [slWL, hpSum, hpM.ev] at this; rw [this]; simp only [s91, s92, s93] <;> first | omega | ring
  · have := g 1 (by omega); simp [slWL, hpSum, hpM.ev] at this; rw [this]; simp only [s91, s92, s93] <;> first | omega | ring
  · have := g 2 (by omega); simp [slWL, hpSum, hpM.ev] at this; rw [this]; simp only [s91, s92, s93] <;> first | omega | ring


/-- The scalars: `scA ; scB`. -/
theorem scAB_execW (c : Config) (hc : WordsBounded W c) {H IM nD A0 p nE k t m DU Qb q SL TI : ℕ}
    (r35 : c.nreg 7335 = H) (r82 : c.nreg 8282 = IM) (r97 : c.nreg 8297 = nD)
    (r90 : c.nreg 8290 = A0) (r80 : c.nreg 8280 = p) (r28 : c.nreg 8228 = nE)
    (r56 : c.nreg 8156 = k) (r57 : c.nreg 8157 = t) (r00 : c.nreg 8000 = m)
    (r89 : c.nreg 8289 = DU) (r07 : c.nreg 8007 = Qb) (r06 : c.nreg 8006 = q)
    (r94 : c.nreg 8294 = SL) (r95 : c.nreg 8295 = TI) :
    ∃ c' t', Exec P W (.seq scA scB) c c' t' ∧ t' = 14 ∧
      Scal c' H IM nD A0 p nE k t m DU Qb q SL TI ∧
      (∀ r, (r < 8180 ∨ 8194 ≤ r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a80, a81, a82, a83, a84, a85, a86, aR, am, ar, arm, ao⟩ :=
    scA_execW (P := P) c hc
  obtain ⟨c₂, t₂, e₂, ht₂, b87, b88, b89, b90, b91, b92, b93, bR, bm, br, brm, bo⟩ :=
    scB_execW (P := P) c₁ e₁.wb_right
  refine ⟨c₂, _, .seq e₁ e₂, by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun r hr => ?_, by rw [bm, am], by rw [br, ar], by rw [brm, arm], by rw [bo, ao]⟩
  · rw [bR _ (by omega), a80]; exact r35
  · rw [bR _ (by omega), a81]; exact r82
  · rw [bR _ (by omega), a82]; exact r97
  · rw [bR _ (by omega), a83]; exact r90
  · rw [bR _ (by omega), a84]; exact r80
  · rw [bR _ (by omega), a85]; exact r28
  · rw [bR _ (by omega), a86]; exact r56
  · rw [b87, aR _ (by omega)]; exact r57
  · rw [b88, aR _ (by omega)]; exact r00
  · rw [b89, aR _ (by omega)]; exact r89
  · rw [b90, aR _ (by omega)]; exact r07
  · rw [b91, aR _ (by omega)]; exact r06
  · rw [b92, aR _ (by omega)]; exact r94
  · rw [b93, aR _ (by omega)]; exact r95
  · rw [bR r (by omega), aR r (by omega)]


set_option maxHeartbeats 2000000 in
/-- **Stage C3b: the flags** `MK[CS[r]] := 1` in the low memory at `4 nD + 1`. -/
theorem msC3b_execW (c : Config) (hc : WordsBounded W c) {H IM nD A0 p nE k t m DU Qb q SL TI : ℕ}
    (hS : Scal c H IM nD A0 p nE k t m DU Qb q SL TI) (r36 : c.nreg 7336 = p + 8 * m)
    (hcs : ∀ r < t, c.nmem (p + 8 * m + r) < k)
    (hinj : ∀ r < t, ∀ r' < t, c.nmem (p + 8 * m + r) = c.nmem (p + 8 * m + r') → r = r')
    (l0 : 4 * nD + 1 + k ≤ p) (ht : t ≤ m) (lDU : p + 10 * m ≤ DU)
    (hW : DU + k + 4 * nD + t + 40 ≤ W) :
    ∃ e t', Exec P W msC3b c e t' ∧ t' ≤ hpCost mkWL + (5 + 8) * t + 5 ∧
      Scal e H IM nD A0 p nE k t m DU Qb q SL TI ∧
      (∀ r < t, e.nmem (4 * nD + 1 + c.nmem (p + 8 * m + r)) = 1) ∧
      (∀ a, (∀ r < t, a ≠ 4 * nD + 1 + c.nmem (p + 8 * m + r)) → (a < DU ∨ DU + k ≤ a) →
        e.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 7370 → r ≠ 7371 → (r < 8200 ∨ 8220 ≤ r) → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨c₁, e₁, w00, w01, w02, wR, wm, wr, wrm, wo⟩ :=
    mkW_execW (P := P) c hc hS.s82 hS.s87 hS.s89 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, w5, wm5, wk5, wR5, wr5, wrm5, wo5⟩ := wrLoop_exec (P := P) c₁
    e₁.wb_right (VAL := vMK) (B := 5) (m := t) (RVo := 4 * nD + 1) (RTo := DU) (N := k)
    w00 w01 w02
    (vMK_spec (P := P) c₁ (t := t) (CSb := p + 8 * m)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact r36)
      (fun r hr => ⟨Or.inr (by omega), Or.inl (by omega)⟩) (by omega) (by omega))
    (fun i hi _ => by rw [wm]; exact hcs i hi)
    (fun i hi i' hi' _ _ e => hinj i hi i' hi' (by rw [wm] at e; exact e)) (Or.inl (by omega))
    (by omega) (by omega) (by omega)
  refine ⟨c₂, _, .seq e₁ e₂, by omega,
    hS.congr (fun r h1 h2 => by rw [wR5 r (by omega), wR r (by omega) (by omega) (by omega)]),
    fun r hr => ?_, fun a h1 h2 => ?_, fun r h1 h2 h3 => ?_, by rw [wr5, wr], by rw [wrm5, wrm],
    by rw [wo5, wo]⟩
  · have := (w5 r hr rfl).1; rwa [wm] at this
  · by_cases ha : 4 * nD + 1 ≤ a ∧ a < 4 * nD + 1 + k
    · rw [wk5 a (fun i hi _ => ⟨by rw [wm]; exact h1 i hi, by omega⟩), wm]
    · rw [wm5 a (by omega) h2, wm]
  · rw [wR5 r (by omega), wR r (by omega) h1 h2]


set_option maxHeartbeats 2000000 in
/-- **Stage C3c: the slots** `SL[i] = TI[i] = CN[FL[Q[i]]]`. -/
theorem msC3c_execW (c : Config) (hc : WordsBounded W c) {H IM nD A0 p nE k t m DU Qb q SL TI : ℕ}
    (hS : Scal c H IM nD A0 p nE k t m DU Qb q SL TI)
    (hq : ∀ i < q, c.nmem (Qb + i) < m ∧ c.nmem (p + m + c.nmem (Qb + i)) ≤ m)
    (hm : 1 ≤ m) (lQ : Qb + q ≤ p) (lSL : p + 10 * m ≤ SL) (lTI : SL + q ≤ TI)
    (hW : TI + q + 40 ≤ W) :
    ∃ e t', Exec P W msC3c c e t' ∧ t' ≤ hpCost slAL + hpCost slWL + (9 + 8) * q + 5 ∧
      Scal e H IM nD A0 p nE k t m DU Qb q SL TI ∧
      (∀ i < q, e.nmem (SL + i) = slV c.nmem Qb (p + m) (p + 9 * m - 1) i ∧
        e.nmem (TI + i) = slV c.nmem Qb (p + m) (p + 9 * m - 1) i) ∧
      (∀ a, (a < SL ∨ SL + q ≤ a) → (a < TI ∨ TI + q ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 7370 → r ≠ 7371 → (r < 8200 ∨ 8220 ≤ r) → (r < 8270 ∨ 8273 ≤ r) →
        e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨c₁, e₁, a70, a71, a72, aR, am, ar, arm, ao⟩ :=
    slA_execW (P := P) c hc hS.s84 hS.s88 hS.s90 (by omega)
  have hS1 := hS.congr (c' := c₁) (fun r h1 h2 => aR r (by omega) (by omega) (by omega))
  obtain ⟨c₂, e₂, w00, w01, w02, wR, wm, wr, wrm, wo⟩ :=
    slW_execW (P := P) c₁ e₁.wb_right hS1.s91 hS1.s92 hS1.s93 (by omega)
  have m2 : c₂.nmem = c.nmem := by rw [wm, am]
  obtain ⟨c₃, t₃, e₃, ht₃, w5, wm5, -, wR5, wr5, wrm5, wo5⟩ := wrLoop_exec (P := P) c₂
    e₂.wb_right (VAL := vSL) (B := 9) (m := q) (RVo := SL) (RTo := TI) (N := q)
    w00 w01 w02
    (vSL_spec (P := P) c₂ (q := q) (Qb := Qb) (FLb := p + m) (CNb := p + 9 * m - 1)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact a70)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact a71)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact a72)
      (fun i hi => by
        obtain ⟨b1, b2⟩ := hq i hi
        rw [m2]
        exact ⟨⟨Or.inl (by omega), Or.inl (by omega)⟩, ⟨Or.inl (by omega), Or.inl (by omega)⟩,
          ⟨Or.inl (by omega), Or.inl (by omega)⟩⟩)
      (fun i hi => by
        obtain ⟨b1, b2⟩ := hq i hi
        rw [m2]
        exact ⟨by omega, by omega, by omega⟩) (by omega))
    (fun i hi _ => hi) (fun i hi i' hi' _ _ e => e) (Or.inl lTI) (by omega) (by omega)
    (by omega)
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega,
    hS1.congr (fun r h1 h2 => by rw [wR5 r (by omega), wR r (by omega) (by omega) (by omega)]),
    fun i hi => ?_, fun a h1 h2 => ?_, fun r h1 h2 h3 h4 => ?_, by rw [wr5, wr, ar],
    by rw [wrm5, wrm, arm], by rw [wo5, wo, ao]⟩
  · obtain ⟨g1, g2⟩ := w5 i hi rfl
    rw [m2] at g1 g2
    exact ⟨g1, g2⟩
  · rw [wm5 a h1 h2, m2]
  · rw [wR5 r (by omega), wR r (by omega) h1 h2, aR r (by omega) h1 h2]


end MsStC4

section MsEncC3

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

variable {P : Input} {W : ℕ}


set_option maxHeartbeats 2000000 in
/-- **Stage C3a: the targets and their reach bits.** -/
theorem msC3a_execW' (c : Config) (hc : WordsBounded W c) {H IM nD A0 p nE k t m DU Qb q SL TI : ℕ}
    (r35 : c.nreg 7335 = H) (r82 : c.nreg 8282 = IM) (r97 : c.nreg 8297 = nD)
    (r90 : c.nreg 8290 = A0) (r80 : c.nreg 8280 = p) (r28 : c.nreg 8228 = nE)
    (r56 : c.nreg 8156 = k) (r57 : c.nreg 8157 = t) (r00 : c.nreg 8000 = m)
    (r89 : c.nreg 8289 = DU) (r07 : c.nreg 8007 = Qb) (r06 : c.nreg 8006 = q)
    (r94 : c.nreg 8294 = SL) (r95 : c.nreg 8295 = TI)
    (hb : ∀ r < t, c.nmem (p + 8 * m + r) < k ∧
      c.nmem (p + 6 * m + c.nmem (p + 8 * m + r)) < m ∧
      nE + c.nmem (p + 14 * m + c.nmem (p + 6 * m + c.nmem (p + 8 * m + r))) < nD ∧
      xtN c.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) nE (IM + 5 * nD) r < 4 * nD + 1)
    (ht : t ≤ m) (hk : k ≤ m) (l1 : p + 16 * m ≤ IM) (l2 : IM + 37 * nD + k + 11 + 2 * t ≤ A0)
    (hW : A0 + 25 * nD + 47 ≤ W ∧ H + 40 ≤ W ∧ nE + 40 ≤ W) :
    ∃ e t', Exec P W msC3a c e t' ∧ t' ≤ 14 + hpCost xtAL + hpCost xtBL + hpCost xtWL +
        (16 + 8) * t + 5 ∧
      Scal e H IM nD A0 p nE k t m DU Qb q SL TI ∧
      (∀ r < t, e.nmem (IM + 37 * nD + k + 11 + r) =
          xtN c.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) nE (IM + 5 * nD) r ∧
        e.nmem (IM + 37 * nD + k + 11 + t + r) =
          if c.nmem (A0 + 21 * nD + 6 + xtN c.nmem (p + 8 * m) (p + 6 * m) (p + 14 * m) nE
            (IM + 5 * nD) r) < H then 1 else 0) ∧
      (∀ a, (a < IM + 37 * nD + k + 11 ∨ IM + 37 * nD + k + 11 + 2 * t ≤ a) →
        e.nmem a = c.nmem a) ∧
      e.nreg 7336 = p + 8 * m ∧
      (∀ r, (r < 7336 ∨ 7340 ≤ r) → (r < 7346 ∨ 7349 ≤ r) → r ≠ 7370 → r ≠ 7371 →
        (r < 8180 ∨ 8194 ≤ r) → (r < 8200 ∨ 8220 ≤ r) → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, hS, aR, am, ar, arm, ao⟩ := scAB_execW (P := P) c hc r35 r82 r97 r90 r80
    r28 r56 r57 r00 r89 r07 r06 r94 r95
  obtain ⟨c₂, e₂, x36, x37, x38, x39, xR, xm, xr, xrm, xo⟩ :=
    xtA_execW (P := P) c₁ e₁.wb_right hS.s84 hS.s85 hS.s88 (by omega)
  have hS2 := hS.congr (c' := c₂) (fun r h1 h2 => xR r (by omega) (by omega) (by omega))
  obtain ⟨c₃, e₃, y46, y47, y48, yR, ym, yr, yrm, yo⟩ :=
    xtB_execW (P := P) c₂ e₂.wb_right hS2.s80 hS2.s81 hS2.s82 hS2.s83 (by omega)
  have hS3 := hS2.congr (c' := c₃) (fun r h1 h2 => yR r (by omega) (by omega) (by omega))
  obtain ⟨c₄, e₄, w00, w01, w02, wR, wm, wr, wrm, wo⟩ :=
    xtW_execW (P := P) c₃ e₃.wb_right hS3.s81 hS3.s82 hS3.s86 hS3.s87 (by omega)
  have hS4 := hS3.congr (c' := c₄) (fun r h1 h2 => wR r (by omega) (by omega) (by omega))
  have m4 : c₄.nmem = c.nmem := by rw [wm, ym, xm, am]
  have q4 : ∀ r, 7336 ≤ r → r < 7340 → c₄.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [wR r (by omega) (by omega) (by omega), yR r (by omega) (by omega) (by omega)]
  set X := IM + 37 * nD + k + 11 with hX
  obtain ⟨c₅, t₅, e₅, ht₅, w5, wm5, -, wR5, wr5, wrm5, wo5⟩ := wrLoop_exec (P := P) c₄
    e₄.wb_right (VAL := vXT) (B := 16) (m := t) (RVo := X) (RTo := X + t) (N := t)
    w00 w01 w02
    (vXT_spec (P := P) c₄ (t := t) (CSb := p + 8 * m) (TRb := p + 6 * m) (RKb := p + 14 * m)
      (nE := nE) (NHb := IM + 5 * nD) (DIb := A0 + 21 * nD + 6) (H := H) (by rw [q4 _ (by omega) (by omega)]; exact x36)
      (by rw [q4 _ (by omega) (by omega)]; exact x37) (by rw [q4 _ (by omega) (by omega)]; exact x38)
      (by rw [q4 _ (by omega) (by omega)]; exact x39)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact y46)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact y47)
      (by rw [wR _ (by omega) (by omega) (by omega)]; exact y48)
      (fun r hr => by
        obtain ⟨b1, b2, b3, b4⟩ := hb r hr
        rw [m4]; unfold Off
        refine ⟨⟨Or.inl (by omega), Or.inl (by omega)⟩, ⟨Or.inl (by omega), Or.inl (by omega)⟩,
          ⟨Or.inl (by omega), Or.inl (by omega)⟩, ⟨Or.inl (by omega), Or.inl (by omega)⟩,
          ⟨Or.inr (by omega), Or.inr (by omega)⟩⟩)
      (fun r hr => by
        obtain ⟨b1, b2, b3, b4⟩ := hb r hr
        rw [m4]
        refine ⟨by omega, by omega, by omega, by omega, by omega⟩) (by omega))
    (fun i hi _ => hi) (fun i hi i' hi' _ _ e => e) (Or.inl le_rfl) (by omega) (by omega)
    (by omega)
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    hS4.congr (fun r h1 h2 => wR5 r (by omega)), fun r hr => ?_, fun a ha => ?_,
    by rw [wR5 _ (by omega), q4 _ (by omega) (by omega)]; exact x36,
    fun r h1 h1' h2 h3 h4 h5 => ?_, by rw [wr5, wr, yr, xr, ar], by rw [wrm5, wrm, yrm, xrm, arm],
    by rw [wo5, wo, yo, xo, ao]⟩
  · obtain ⟨g1, g2⟩ := w5 r hr rfl
    rw [m4] at g1 g2
    exact ⟨g1, by rw [show IM + 37 * nD + k + 11 + t + r = X + t + r by rw [hX]]; exact g2⟩
  · rw [wm5 a (by omega) (by omega), m4]
  · rw [wR5 r (by omega), wR r (by omega) h2 h3, yR r (by omega) h2 h3, xR r (by omega) h2 h3,
      aR r h4]


end MsEncC3

end MsEnc

end BKMNW

end PlanarFlow
