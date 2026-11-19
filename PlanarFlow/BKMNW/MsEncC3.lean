module

public import PlanarFlow.BKMNW.MsEncC1

/-!
# The MSSP encoder, stage C3a with a finer register frame

`msC3a_exec` (`MsStC4`) states the frame of the registers outside `7336 … 7348`; the stages after
it need `r7336 = p + 8 m` (read by `msC3b`) and `r7342 = w` (read by `msD1`).
**`msC3a_exec'`**: the same run (same program `msC3a`) with `r7336 = p + 8 m` and the frame of the
registers outside `7336 … 7339`, `7346 … 7348`.
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
/-- **Stage C3a: the targets and their reach bits.** -/
theorem msC3a_exec' (c : Config) (hc : WordsBounded W c) {H IM nD A0 p nE k t m DU Qb q SL TI : ℕ}
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
    (hW : A0 + 25 * nD + 7 + H + 2 * p + 28 * m + nE + IM + 37 * nD + k + 11 + 2 * t + 40 ≤ W) :
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
  obtain ⟨c₁, t₁, e₁, ht₁, hS, aR, am, ar, arm, ao⟩ := scAB_exec (P := P) c hc r35 r82 r97 r90 r80
    r28 r56 r57 r00 r89 r07 r06 r94 r95
  obtain ⟨c₂, e₂, x36, x37, x38, x39, xR, xm, xr, xrm, xo⟩ :=
    xtA_exec (P := P) c₁ e₁.wb_right hS.s84 hS.s85 hS.s88 (by omega)
  have hS2 := hS.congr (c' := c₂) (fun r h1 h2 => xR r (by omega) (by omega) (by omega))
  obtain ⟨c₃, e₃, y46, y47, y48, yR, ym, yr, yrm, yo⟩ :=
    xtB_exec (P := P) c₂ e₂.wb_right hS2.s80 hS2.s81 hS2.s82 hS2.s83 (by omega)
  have hS3 := hS2.congr (c' := c₃) (fun r h1 h2 => yR r (by omega) (by omega) (by omega))
  obtain ⟨c₄, e₄, w00, w01, w02, wR, wm, wr, wrm, wo⟩ :=
    xtW_exec (P := P) c₃ e₃.wb_right hS3.s81 hS3.s82 hS3.s86 hS3.s87 (by omega)
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

end MsEnc

end BKMNW

end PlanarFlow
