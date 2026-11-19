module

public import PlanarFlow.BKMNW.Nf9bK
public import PlanarFlow.BKMNW.Nf9bN
public import PlanarFlow.BKMNW.MsEncJ

/-!
# A program meeting `FixFrameSpec`

**`F9b.fixFrame_spec`**: for every MSSP call program `msP` whose scratch registers lie below
`9300` and every `200000 ≤ C`,

  `FixFrameSpec (fixC msP) msP Scr Rm wzm C C₀ (fxT9 C C₀) (rOF9 C C₀ Rm) (wzF9 wzm)`:

the frozen fix `fixC msP` (FixConservationOnPath of `fixP`, its stage loop on the frame
of the map with pendant edges, its MSSP call and its final negative-length call on the frame of
the base map) writes `Z' + fixPath (M₀.pendant e he) cap f₀ (πj.lift) (msspP (msspPlaneK M₀))
(frRef F) (negP (negMach (nsIds M₀ henum (en 0)) M₀ I))` in the pendant flow array.

With `fzHypF_of_frame`, `c2sHypF_of_frame`, `s2cHypF_of_frame` and the cost bound
`fxT9_le_fixRun`: **`fzHypF9`**, **`c2sHypF9`**, **`s2cHypF9`**; for the concrete MSSP call
`msspCall' msEnc` (`MsEnc.msspCall'_cMachS_msEnc`): `fixFrame_spec_msEnc`, `fzHypF9_msEnc`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace F9b

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep NcFz SPath
  NcStep WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

set_option maxHeartbeats 16000000 in
/-- **A program meeting `FixFrameSpec`** (see the module docstring). -/
theorem fixFrame_spec {msP : Stmt} {Scr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    {C C₀ : ℕ} (hC : 200000 ≤ C) (hScr : ∀ r, Scr r → r < 9300) :
    FixFrameSpec (fixC msP) msP Scr Rm wzm C C₀ (fxT9 C C₀) (rOF9 C C₀ Rm) (wzF9 wzm) := by
  intro hMS D V F _ _ _ _ _ _ M₀ hpl hrot hft e he I W Wz m m' Z' d d' A0 lo hi Gb j en henum en'
    segs hj cap f₀ c hbm hbrv hbsg hfr' hen hmm hm3 hm0 hS hps hcap r04 r98 r06 r07 r00 hfb hfrA
    hhi hWzd hWlo hWzd' hRW hWZ hMZ hc
  have H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j c.nmem :=
    ⟨hpl, hrot, hft, henum, hen, hbm, hbrv, hbsg, hfr', hmm, hm0, hS, hj, hps, hcap⟩
  have hMS₀ := hMS M₀
  obtain ⟨h1, h2, h3, h4⟩ := hS
  obtain ⟨g1, g2, -⟩ := h4 j hj
  have hW0 : A0 ≤ W := by have := hRW; omega
  obtain ⟨c', t, s, ex, hs, hQ⟩ := fixC_branch (I := I) (W := W) msP c hc (Gb := Gb) (j := j)
    (ns := segs.length) (k := (segs[j]'hj).k) r07 r00 h2
    (by rw [show Gb + 1 + j + segs.length = Gb + 1 + segs.length + j by omega]; exact g2)
    (by omega)
    (fun c' t => t + 9 ≤ fxT9 C C₀ m (segs[j]'hj).faces.card (segs[j]'hj).k ∧
      (∀ i < m', (c'.nmem (d' + 4 + 6 * m' + i) : ℤ) = Z' + fixPath (M₀.pendant e he) cap f₀
        ((segs[j]'hj).lift e he) (msspP (Klein.msspPlaneK M₀)) (frRef F)
        (negP (negMach (NsStep.nsIds M₀ henum (en 0)) M₀ I)) (en' i)) ∧
      (∀ a < A0, (a < d' + 4 + 6 * m' ∨ d' + 4 + 7 * m' ≤ a) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      MemZ Wz c' ∧ (∀ r, NcStep.PKeep r → c'.nreg r = c.nreg r) ∧ c'.output = c.output)
    (fun hk0 c₁ hc₁ hm₁ hr₁ hrr₁ hrm₁ ho₁ => by
      have H₁ : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j c₁.nmem := by
        rw [hm₁]; exact H
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16⟩ :=
        pos_bnds C C₀ H₁ hk0 hRW hWZ hWzd' hfrA
      have kr : ∀ r, (r < 9437 ∨ 9439 < r) → c₁.nreg r = c.nreg r := hr₁
      obtain ⟨c', t, ex, ht, FL, MM, ZZ, KK, OO⟩ :=
        fxPos_exec C C₀ hC hMS₀ hScr I c₁ hc₁ H₁ hk0
          (by rw [kr _ (by norm_num)]; exact r04) (by rw [kr _ (by norm_num)]; exact r06)
          (by rw [kr _ (by norm_num)]; exact r07) (by rw [kr _ (by norm_num)]; exact r00)
          (by rw [kr _ (by norm_num)]; exact r98) (fun a ha => by rw [hm₁]; exact hMZ a ha)
          hWzd hWzd' hWlo hhi hfrA hfb b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16
      have hb := mkP_card H₁ hk0
      have hkm := pq_k_le H₁
      have hkq := pq_k H₁
      have hb1 := one_le_faces9 _ hk0
      have hb2 := (segs[j]'hj).card_faces_le
      refine ⟨c', t, ex, ?_, FL, fun a ha hn => ?_, ZZ, fun r hr => ?_, by rw [OO, ho₁]⟩
      · have hkm' : (segs[j]'hj).k ≤ m :=
          calc (segs[j]'hj).k = (cIn d' m' Gb segs j Z' c₁.nmem).k := hkq.symm
            _ ≤ m := hkm
        have hcond : 0 < (segs[j]'hj).k ∧ 1 ≤ (segs[j]'hj).faces.card ∧
            (segs[j]'hj).faces.card ≤ 2 * (segs[j]'hj).k ∧ (segs[j]'hj).k ≤ m :=
          ⟨hk0, hb1, hb2, hkm'⟩
        unfold fxT9
        rw [if_pos hcond]
        have hmono := posT9_mono (C := C) (C₀ := C₀) (cost := MsEnc.msCostS C C₀) (m := m)
          (k := (segs[j]'hj).k) (b := (segs[j]'hj).faces.card) hm3
        have ht2 : t ≤ posT9 C C₀ (MsEnc.msCostS C C₀) m m' (segs[j]'hj).k
            (segs[j]'hj).faces.card := by
          rw [hb] at ht; exact ht
        have := le_trans ht2 hmono
        omega
      · obtain ⟨e1, e2⟩ := MM a ha hn
        rw [e1, e2, hm₁, hrm₁]; exact ⟨rfl, rfl⟩
      · rw [KK r hr]; unfold NcStep.PKeep at hr; exact kr r (by omega))
    (fun hk00 c₁ hc₁ hm₁ hr₁ hrr₁ hrm₁ ho₁ => by
      have H₁ : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j c₁.nmem := by
        rw [hm₁]; exact H
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := zero_bnds C C₀ H₁ hk00 hRW hWZ
      have kr : ∀ r, (r < 9437 ∨ 9439 < r) → c₁.nreg r = c.nreg r := hr₁
      obtain ⟨c', t, ex, ht, FL, MM, ZZ, KK, OO⟩ :=
        fxZero_exec C C₀ hC I c₁ hc₁ H₁ hk00
          (by rw [kr _ (by norm_num)]; exact r04) (by rw [kr _ (by norm_num)]; exact r06)
          (by rw [kr _ (by norm_num)]; exact r07) (by rw [kr _ (by norm_num)]; exact r00)
          (by rw [kr _ (by norm_num)]; exact r98) (fun a ha => by rw [hm₁]; exact hMZ a ha)
          hWzd hWzd' hWlo hhi hfrA hfb b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
      refine ⟨c', t, ex, ?_, FL, fun a ha hn => ?_, ZZ, fun r hr => ?_, by rw [OO, ho₁]⟩
      · have hcond : ¬ (0 < (segs[j]'hj).k ∧ 1 ≤ (segs[j]'hj).faces.card ∧
            (segs[j]'hj).faces.card ≤ 2 * (segs[j]'hj).k ∧ (segs[j]'hj).k ≤ m) := fun h => by
          omega
        unfold fxT9
        rw [if_neg hcond]
        have hmono := zT9_mono (C := C) (C₀ := C₀) (m := m) hm3
        omega
      · obtain ⟨e1, e2⟩ := MM a ha hn
        rw [e1, e2, hm₁, hrm₁]; exact ⟨rfl, rfl⟩
      · rw [KK r hr]; unfold NcStep.PKeep at hr; exact kr r (by omega))
  exact ⟨c', s, ex, by omega, hQ.2.1, hQ.2.2.1, hQ.2.2.2.1, hQ.2.2.2.2.1, hQ.2.2.2.2.2⟩

/-- **`FzHypF` for `fzP (fixC msP)`** (`fzHypF_of_frame`). -/
theorem fzHypF9 {msP : Stmt} {Scr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    {C C₀ : ℕ} (hC : 200000 ≤ C) (hScr : ∀ r, Scr r → r < 9300) :
    Pp.FzHypF (fzP (fixC msP)) msP Scr Rm wzm C C₀ (fzWz (wzF9 wzm)) (fzRN (rOF9 C C₀ Rm)) :=
  fzHypF_of_frame (fixFrame_spec hC hScr) (fxT9_le_fixRun (by omega))

/-- **`C2SHypF` for `c2sP (fzP (fixC msP)) pbP`.** -/
theorem c2sHypF9 {msP : Stmt} {Scr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    {C C₀ : ℕ} (hC : 200000 ≤ C) (hScr : ∀ r, Scr r → r < 9300) :
    Pp.C2SHypF (c2sP (fzP (fixC msP)) pbP) msP Scr Rm wzm C C₀
      (fun m Z => wzc m Z + fzWz (wzF9 wzm) m Z) (Pp.c2sRC (fzRN (rOF9 C C₀ Rm))) :=
  c2sHypF_of_frame (fixFrame_spec hC hScr) (fxT9_le_fixRun (by omega)) (by omega)

/-- **`S2CHypF` for `s2cP (fzP (fixC msP)) pbP`.** -/
theorem s2cHypF9 {msP : Stmt} {Scr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    {C C₀ : ℕ} (hC : 200000 ≤ C) (hScr : ∀ r, Scr r → r < 9300) :
    Pp.S2CHypF (s2cP (fzP (fixC msP)) pbP) msP Scr Rm wzm C C₀
      (fun m Z => wzc m Z + fzWz (wzF9 wzm) m Z) (Pp.c2sRC (fzRN (rOF9 C C₀ Rm))) :=
  s2cHypF_of_frame (fixFrame_spec hC hScr) (fxT9_le_fixRun (by omega)) (by omega)

/-- The scratch registers of the concrete MSSP call `msspCall' msEnc` lie below `9300`. -/
lemma msEnc_scr_lt (r : ℕ) (h : MsEnc.EScr r ∨ MsCall.msScr r) : r < 9300 := by
  rcases h with h | h
  · unfold MsEnc.EScr at h; omega
  · unfold MsCall.msScr at h; omega

/-- **`FixFrameSpec` for the concrete MSSP call `msspCall' msEnc`.** -/
theorem fixFrame_spec_msEnc {C C₀ : ℕ} (hC : 200000 ≤ C) :
    FixFrameSpec (fixC (MsCall.msspCall' MsEnc.msEnc)) (MsCall.msspCall' MsEnc.msEnc)
      (fun r => MsEnc.EScr r ∨ MsCall.msScr r) MsEnc.Rm MsEnc.wzm C C₀ (fxT9 C C₀)
      (rOF9 C C₀ MsEnc.Rm) (wzF9 MsEnc.wzm) :=
  fixFrame_spec hC msEnc_scr_lt

/-- **`FzHypF` for the concrete MSSP call `msspCall' msEnc`.** -/
theorem fzHypF9_msEnc {C C₀ : ℕ} (hC : 200000 ≤ C) :
    Pp.FzHypF (fzP (fixC (MsCall.msspCall' MsEnc.msEnc))) (MsCall.msspCall' MsEnc.msEnc)
      (fun r => MsEnc.EScr r ∨ MsCall.msScr r) MsEnc.Rm MsEnc.wzm C C₀ (fzWz (wzF9 MsEnc.wzm))
      (fzRN (rOF9 C C₀ MsEnc.Rm)) :=
  fzHypF9 hC msEnc_scr_lt

end F9b

end BKMNW

end PlanarFlow
