module

public import PlanarFlow.BKMNW.MsStB

/-!
# The MSSP encoder, stages B3–B4: the isolating lengths, their sum, Dijkstra's lengths

* **`msB3`** `= bSetD1 ; bSetD2 ; bSetD3 ; wrLoop vLN`: from the counts `cV = r7957`
  (`#CutV`), `cF = r7959` (`#CutF`), `nD`, the factors `N₃ = cV nD + 1`, `N₂ = N₃ (2 cF cV + 1)`,
  `N₁ = N₂ (cV + 1)` (`isoN3/2/1`), then `IS[j] = [j < nP]` and
  `LN[j] = [j < nP] (CL[j] N₁ + WM[j] N₃ + N₂ + j)` at `IM + 6 nD`, `IM + 7 nD`; **`msB3_exec`**;
* **`msB4`** `= bSetE ; smLoop ; bSetF1 ; bSetF2 ; wrLoop vLD`: `w = ∑_{j < nP} LN[j]`
  (`r7342`), `H = w + 1` (`r7335`), Dijkstra's lengths `LD[j] = IS[j] = 1 ? LN[j] :
  (j = G₀ ? H : 2H)` (`G₀ = M[aGG] = σ (g 0)`); **`msB4_exec`**.
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

/-! ### B3 -/

def bSetD1 : Stmt :=
  block [.mulN 7330 7957 7950, .constN 8264 1, .addN 7330 7330 8264, .mulN 7331 7959 7957,
    .addN 7331 7331 7331, .addN 7331 7331 8264, .mulN 7331 7331 7330, .addN 7328 7957 8264]

def bSetD2 : Stmt :=
  block [.mulN 7328 7328 7331, .copyN 8200 7950, .constN 8264 6, .mulN 8201 7950 8264,
    .addN 8201 8201 8282, .addN 8202 8201 7950, .copyN 7326 8230, .copyN 7327 8287]

def bSetD3 : Stmt := block [.copyN 7329 8286]

def msB3 : Stmt := .seq bSetD1 (.seq bSetD2 (.seq bSetD3 (wrLoop vLN)))

theorem bSetD1_exec (c : Config) (hc : WordsBounded W c) {nD cV cF : ℕ}
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

theorem bSetD2_exec (c : Config) (hc : WordsBounded W c) {nD cV N2 IM nP CL : ℕ}
    (r28 : c.nreg 7328 = cV + 1) (r31 : c.nreg 7331 = N2) (r50 : c.nreg 7950 = nD)
    (r82 : c.nreg 8282 = IM) (r30 : c.nreg 8230 = nP) (r87 : c.nreg 8287 = CL)
    (hw : (cV + 1) * N2 + IM + 7 * nD + 6 ≤ W) :
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

theorem bSetD3_exec (c : Config) (hc : WordsBounded W c) {WM : ℕ} (r86 : c.nreg 8286 = WM) :
    ∃ c' t, Exec P W bSetD3 c c' t ∧ t = 1 ∧ c'.nreg 7329 = WM ∧
      (∀ r, r ≠ 7329 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSetD3
  exec_block
  refine ⟨rfl, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  · exact r86
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl

set_option maxHeartbeats 2000000 in
/-- **The piece flags and the isolating lengths.** -/
theorem msB3_exec {nD cV cF IM nP CL WM : ℕ} (c : Config) (hc : WordsBounded W c)
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
    fun j hj => ⟨?_, ?_⟩, fun a ha => ?_, fun r h1 h2 h3 => ?_, by rw [wr4, dr, br, ar],
    by rw [wrm4, drm, brm, arm], by rw [wo4, dO, bo, ao]⟩
  · rw [(w4 j hj rfl).1]
  · rw [(w4 j hj rfl).2, m3]
  · rw [wm4 a (by omega) (by omega), m3]
  · rw [wR4 r (by omega), dR r (by omega), bR r (by omega) (by omega) h3, aR r (by omega) (by omega)
      (by omega) h3]

/-! ### B4 -/

def bSetE : Stmt := block [.copyN 7340 8230, .constN 8264 7, .mulN 7341 7950 8264, .addN 7341 7341 8282]

def bSetF1 : Stmt :=
  block [.copyN 8200 7950, .copyN 8201 8288, .copyN 8202 8289, .constN 8264 6,
    .mulN 7332 7950 8264, .addN 7332 7332 8282, .addN 7333 7332 7950, .loadN 7334 8284]

def bSetF2 : Stmt := block [.constN 8264 1, .addN 7335 7342 8264]

def msB4 : Stmt := .seq bSetE (.seq smLoop (.seq bSetF1 (.seq bSetF2 (wrLoop vLD))))

theorem bSetE_exec (c : Config) (hc : WordsBounded W c) {nD IM nP : ℕ}
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

theorem bSetF1_exec (c : Config) (hc : WordsBounded W c) {nD IM LD DU GG : ℕ}
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

theorem bSetF2_exec (c : Config) (hc : WordsBounded W c) {w : ℕ} (r42 : c.nreg 7342 = w)
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
theorem msB4_exec {nD IM nP LD DU GG : ℕ} (c : Config) (hc : WordsBounded W c)
    (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM) (r30 : c.nreg 8230 = nP)
    (r88 : c.nreg 8288 = LD) (r89 : c.nreg 8289 = DU) (r84 : c.nreg 8284 = GG) (hnP : nP ≤ nD)
    (his : ∀ j < nD, c.nmem (IM + 6 * nD + j) ≤ 1) (l1 : IM + 8 * nD ≤ LD)
    (l2 : LD + nD ≤ DU) (l3 : GG < LD)
    (hs : 2 * (∑ j ∈ range nP, c.nmem (IM + 7 * nD + j) + 1) ≤ W)
    (hln : ∀ j < nD, c.nmem (IM + 7 * nD + j) ≤ W) (hW : DU + nD + IM + 8 * nD + 8 ≤ W)
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
  obtain ⟨c₁, t₁, e₁, ht₁, a40, a41, aR, am, ar, arm, ao⟩ := bSetE_exec (P := P) c hc r30 r50 r82
    (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, s42, sR, sm, sr, srm, so⟩ := smLoop_exec (P := P) c₁ e₁.wb_right a40 a41
    (by omega) (by rw [am]; omega) (by omega)
  rw [am] at s42
  have q2 : ∀ r, (r < 7340 ∨ 7345 < r) → r ≠ 8264 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [sR r (by omega), aR r (by omega) (by omega) h2]
  obtain ⟨c₃, t₃, e₃, ht₃, f00, f01, f02, f32, f33, f34, fR, fm, fr, frm, fo⟩ :=
    bSetF1_exec (P := P) c₂ e₂.wb_right (nD := nD) (IM := IM) (LD := LD) (DU := DU) (GG := GG)
      ((q2 _ (by omega) (by omega)).trans r50) ((q2 _ (by omega) (by omega)).trans r82)
      ((q2 _ (by omega) (by omega)).trans r88) ((q2 _ (by omega) (by omega)).trans r89)
      ((q2 _ (by omega) (by omega)).trans r84) (by omega)
  rw [sm, am] at f34
  obtain ⟨c₄, t₄, e₄, ht₄, g35, gR, gm, gr, grm, go⟩ := bSetF2_exec (P := P) c₃ e₃.wb_right
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

end MsEnc

end BKMNW

end PlanarFlow
