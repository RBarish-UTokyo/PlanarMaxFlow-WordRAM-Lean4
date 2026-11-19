module

public import PlanarFlow.BKMNW.Nf9bJ

/-!
# The branch `k = 0` of the frozen fix

* `fz9_pre`: `fz7d_preW` (`proP1a ; proP1b ; proP3a ; z0Blk`: the face labels, `K`, the base
  `T = Q` of the final step) on the frame `MFr` of any map;
* **`fxZero_exec`**: an empty part (`k = 0`): `fxZero` writes the frozen fix
  (`f₀ + cob χ` with `χ` the negative-length potentials of the base map) in the pendant flow array,
  within `zT9 C C₀ m m'` steps.
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
  WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Gen

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {en : ℕ → D} {m Z d : ℕ} {cap f : D → ℤ}

set_option maxHeartbeats 4000000 in
/-- The face labels and the offset of an empty part (`proP1a ; proP1b ; proP3a ; z0Blk`), on a
frame of any map. -/
theorem fz9_pre (I : Input) {W A0 : ℕ} (c : Config) (hc : WordsBounded W c)
    (hL : MFr M en m Z cap f d c.nmem) {segs : List (SPath M)} {lo hi Gb j : ℕ}
    (hS : SegsL M en m segs lo hi Gb c.nmem) (hj : j < segs.length)
    (hq0 : (cIn d m Gb segs j Z c.nmem).k = 0)
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (hfr : d + 4 + 7 * m ≤ A0)
    (hhi : hi ≤ A0) (hZ1 : A0 + 9 * m + 16 ≤ W)
    (hZ2 : ∑ i ∈ range m, (cIn d m Gb segs j Z c.nmem).FLW i + 6 ≤ W)
    (hZ3 : (cIn d m Gb segs j Z c.nmem).AS + 16 * fpB (cIn d m Gb segs j Z c.nmem).AS m 0 + Z +
      16 ≤ W) :
    let q := cIn d m Gb segs j Z c.nmem
    ∃ c' t, Exec I W (.seq proP1a (.seq proP1b (.seq proP3a z0Blk))) c c' t ∧
      t ≤ 63 + (120 * m + 60) + (12 * m + 22) + 1 ∧
      c'.nreg 9469 = A0 + 9 * m + 1 ∧ c'.nreg 9400 = m ∧ c'.nreg 9436 = 1 ∧
      c'.nreg 9434 = d + 4 + 3 * m ∧ c'.nreg 9435 = d + 4 + 6 * m ∧ c'.nreg 9421 = Z ∧
      c'.nreg 9310 = q.K ∧ c'.nreg 9401 = 0 ∧ c'.nreg 9402 = q.PDb ∧
      c'.nreg 9430 = d + 4 + m ∧
      c'.nreg 9374 = A0 + 9 * m + 1 ∧ c'.nreg 9375 = A0 + 9 * m + 1 ∧
      c'.nreg 9376 = A0 + 9 * m + 1 ∧ c'.nreg 9405 = A0 + m ∧
      (∀ a < A0, c'.nmem a = c.nmem a) ∧
      (∀ i < m, c'.nmem (A0 + m + i) = olab (nxF d m c.nmem) i + 1) ∧
      (∀ r, ¬ scr1 r → r ≠ 9420 → r ≠ 9373 → r ≠ 9422 → r ≠ 9310 → (r < 9456 ∨ 9497 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  dsimp only
  set q := cIn d m Gb segs j Z c.nmem with hq
  have eqk : (cIn d m Gb segs j Z c.nmem).k = q.k := rfl
  have eqm : (cIn d m Gb segs j Z c.nmem).m = q.m := rfl
  have eqP : (cIn d m Gb segs j Z c.nmem).PDb = q.PDb := rfl
  have eqc : (cIn d m Gb segs j Z c.nmem).cw.cnt = q.cw.cnt := rfl
  have eqK : (cIn d m Gb segs j Z c.nmem).K = q.K := rfl
  have eqA : (cIn d m Gb segs j Z c.nmem).AS = q.AS := rfl
  have htop := cIn_top (d := d) (Z := Z) (mem := c.nmem) hS hj
  have hpre := cIn_pre (d := d) (Z := Z) hL hS hj
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hpre
  have hQe : q.Qb A0 = A0 + 9 * m + 1 := by
    show A0 + m + m + m + m + 1 + m + m + m + m + m = _; omega
  obtain ⟨c₁, t₁, e₁, ht₁, R1, a5030, a5031, a4470, a4471, a4472, a4473, a7350, a7351, a7352,
      a8430, k1, n1, rr1, rm1, o1⟩ :=
    proP1a_execW (P := I) q c hc (j := j) (A0 := A0) r04 r06 r07 r00 p1 p2 p3 p4 p5
      (by
        have h1 : q.PDb + q.k ≤ hi := htop.1
        have h2 : Gb + 1 + j + segs.length < hi := htop.2.1
        have e1 : q.PDb = Gb + 1 + segs.length + segs.length + q.off := rfl
        have e2 : q.k = 0 := hq0
        show A0 + 9 * m + 15 * q.k + 1 ≤ W ∧ d + 6 * m + 8 ≤ W ∧ Gb + 1 + j + segs.length ≤ W ∧
          Gb + 1 + segs.length + segs.length + q.off ≤ W
        omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b1, bNX, bLAB, -, -, -, -, bk, bR, rr2, rm2, o2⟩ :=
    proP1b_exec (P := I) q c₁ e₁.wb_right (A0 := A0)
      (by rw [k1 _ (by unfold scr1; norm_num)]; exact r04)
      a5030 a5031 a4470 a4471 a4472 a4473 a7350 a7351 a7352 a8430
      (fun a _ => by rw [n1]; rfl) p1 p6 p7 p8 hfr
      (show A0 + 9 * q.m + 2 ≤ W from by show A0 + 9 * m + 2 ≤ W; omega) hZ2
  have R2 : RegP1 q A0 c₂ := R1.congr fun r hr _ _ _ => bR r (by clear * - hr; omega)
    (by clear * - hr; omega) (by clear * - hr; omega) (by clear * - hr; omega)
    (by clear * - hr; omega)
  obtain ⟨c₃, t₃, e₃, ht₃, d20, d73, d22, d10, -, dm, dR, rr3, rm3, o3⟩ :=
    proP3a_exec (P := I) q c₂ e₂.wb_right R2 b1 hfr
      (show A0 + 9 * q.m + 2 ≤ W from by show A0 + 9 * m + 2 ≤ W; omega)
      (show q.AS + 16 * fpB q.AS q.m q.k + q.Z + q.k + 16 ≤ W from by
        rw [hq0]; show q.AS + 16 * fpB q.AS m 0 + Z + 0 + 16 ≤ W; omega)
  obtain ⟨c₄, t₄, e₄, ht₄, z69, zk, zm, rr4, rm4, o4⟩ := z0Blk_exec (P := I) c₃ e₃.wb_right
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, g11, g74, g75, g76, g77, g12, g13, g14, g15, g16, g17, g18⟩ := R2
  have K4 : ∀ r, 9400 ≤ r → r ≤ 9438 → r ≠ 9420 → r ≠ 9422 → c₄.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 h4 => (zk r (by clear * - h2; omega)).trans
      (dR r h3 (by clear * - h1; omega) h4 (by clear * - h1; omega) (by clear * - h2; omega))
  have K4' : ∀ r, 9374 ≤ r → r ≤ 9377 → c₄.nreg r = c₂.nreg r :=
    fun r h1 h2 => (zk r (by clear * - h2; omega)).trans
      (dR r (by clear * - h2; omega) (by clear * - h1; omega) (by clear * - h2; omega)
        (by clear * - h1; omega) (by clear * - h2; omega))
  have m4 : ∀ a, a < A0 → c₄.nmem a = c.nmem a := fun a ha => by
    rw [zm, dm a (by clear * - ha hfr; omega)]; exact b1 a ha
  have ht2' : t₂ ≤ 120 * m + 60 := ht₂
  have ht3' : t₃ ≤ 12 * m + 22 := ht₃
  refine ⟨c₄, _, e₁.seq (e₂.seq (e₃.seq e₄)), by clear * - ht₁ ht2' ht3' ht₄; omega, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, m4, fun i hi => ?_, fun r h1 h2 h3 h4 h5 h6 => ?_,
    by rw [rr4, rr3, rr2, rr1], by rw [rm4, rm3, rm2, rm1], by rw [o4, o3, o2, o1]⟩
  · rw [z69, dR _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g18, hq0]
    simp only [Nat.add_zero]; exact hQe
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g00]; rfl
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g36]
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g34]
    show d + 4 + m + m + m = _; ring
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g35]
    show d + 4 + m + m + m + m + m + m = _; ring
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g21]; rfl
  · rw [zk _ (by norm_num)]; exact d10
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g01, hq0]
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g02]
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g30]; rfl
  · rw [K4' _ (by norm_num) (by norm_num), g74, hQe]
  · rw [K4' _ (by norm_num) (by norm_num), g75, hQe, hq0]
  · rw [K4' _ (by norm_num) (by norm_num), g76, hQe, hq0]
  · rw [K4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g05]; rfl
  · rw [zm, dm _ (by
      show ¬ (A0 + m + m + m + m + 1 + m + m + m ≤ A0 + m + i ∧
        A0 + m + m + m + m + 1 + m + m + m + m > A0 + m + i)
      clear * - hi; omega)]; exact bLAB i hi
  · rw [zk r (by clear * - h6; omega),
      dR r h2 h3 h4 h5 h6,
      bR r (by unfold scr1 at h1; clear * - h1; omega) (by unfold scr1 at h1; clear * - h1; omega)
        (by unfold scr1 at h1; clear * - h1; omega) (by unfold scr1 at h1; clear * - h1; omega)
        (by unfold scr1 at h1; clear * - h1; omega), k1 r h1]

end Gen

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M₀ : CombMap D V F} {e : V → D} {he : ∀ v, M₀.tail (e v) = v}
variable {en : ℕ → D} {en' : ℕ → D ⊕ (V × Bool)} {m m' Z' d d' : ℕ}
  {cap f₀ : D ⊕ (V × Bool) → ℤ} {segs : List (SPath M₀)} {lo hi Gb j : ℕ}

set_option maxHeartbeats 16000000 in
/-- **The branch `k = 0` of the frozen fix.** -/
theorem fxZero_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (I : Input) {W Wz A0 : ℕ} (c : Config)
    (hc : WordsBounded W c)
    (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j c.nmem)
    (hk00 : (segs[j]'H.hj).k = 0)
    (r04 : c.nreg 3004 = d') (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (r98 : c.nreg 9998 = d) (hz : ∀ a ≤ Wz, c.nmem a = 0)
    (hWzd : Wz < d) (hWzd' : Wz < d') (hWlo : Wz < lo)
    (hhi : hi ≤ A0) (hfr : d' + 4 + 7 * m' ≤ A0) (hfb : d + 4 + 3 * m ≤ A0)
    (hZ1 : A0 + 9 * m' + 16 ≤ W)
    (hZ2 : ∑ i ∈ range m', (cIn d' m' Gb segs j Z' c.nmem).FLW i + 6 ≤ W)
    (hZ3 : (cIn d' m' Gb segs j Z' c.nmem).AS + 16 * fpB (cIn d' m' Gb segs j Z' c.nmem).AS m' 0 +
      Z' + 16 ≤ W)
    (hSz : 9 * m + 1 + tsz m ≤ Wz + 1)
    (hWz : rtW m (rtL M₀ (fun y => cap (.inl y) - f₀ (.inl y))) m ≤ Wz)
    (hW : A0 + 9 * m' + 1 + 60 * m + 60 + negT C C₀ m ≤ W)
    (wL : 2 * (cIn d' m' Gb segs j Z' c.nmem).K + rtL M₀ (fun y => cap (.inl y) - f₀ (.inl y))
      ≤ W)
    (hw2' : spWs m + 205 ≤ W) (hw3 : fxWB m (rtL M₀ (fun y => cap (.inl y) - f₀ (.inl y))) ≤ W)
    (hv : Z' + Z' + 2 * (cIn d' m' Gb segs j Z' c.nmem).K +
      2 * rtL M₀ (fun y => cap (.inl y) - f₀ (.inl y)) ≤ W) :
    ∃ c' t, Exec I W fxZero c c' t ∧ t ≤ zT9 C C₀ m m' ∧
      (∀ i < m', (c'.nmem (d' + 4 + 6 * m' + i) : ℤ) = Z' + fixPath (M₀.pendant e he) cap f₀
        ((segs[j]'H.hj).lift e he) (msspP (Klein.msspPlaneK M₀)) (frRef F)
        (negP (negMach (nsIds M₀ H.enum (en 0)) M₀ I)) (en' i)) ∧
      (∀ a < A0, (a < d' + 4 + 6 * m' ∨ d' + 4 + 7 * m' ≤ a) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧ (∀ r, NcStep.PKeep r → c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  set q := cIn d' m' Gb segs j Z' c.nmem with hq
  have eqk : (cIn d' m' Gb segs j Z' c.nmem).k = q.k := rfl
  have eqm : (cIn d' m' Gb segs j Z' c.nmem).m = q.m := rfl
  have eqP : (cIn d' m' Gb segs j Z' c.nmem).PDb = q.PDb := rfl
  have eqc : (cIn d' m' Gb segs j Z' c.nmem).cw.cnt = q.cw.cnt := rfl
  have eqK : (cIn d' m' Gb segs j Z' c.nmem).K = q.K := rfl
  have eqA : (cIn d' m' Gb segs j Z' c.nmem).AS = q.AS := rfl
  set π := segs[j]'H.hj with hπ
  have hmm := H.mm
  have hm0 := H.m0
  have hq0 : q.k = 0 := by rw [← hk00]; exact cIn_k H.hj
  have htop1 : q.PDb + q.k ≤ hi := (cIn_top (d := d') (Z := Z') (m := m) H.sl H.hj).1
  have htop3 : lo ≤ q.PDb := (cIn_top (d := d') (Z := Z') (m := m) H.sl H.hj).2.2
  -- the prologue of an empty part
  have hpre := fz9_pre I (W := W) (A0 := A0) c hc H.fr H.segsL' H.hj'
    (by rw [cIn_lift]; exact hq0) r04 r06 r07 r00 hfr hhi hZ1
    (by rw [cIn_lift]; exact hZ2) (by rw [cIn_lift]; exact hZ3)
  rw [cIn_lift] at hpre
  obtain ⟨c₄, t₄, e₄, ht₄, z69, z00, z36, z34, z35, z21, z10, z01, z02, z30, z74, z75, z76,
      z05, m4, L4, K4, rr4, rm4, o4⟩ := hpre
  -- the base frame
  obtain ⟨c₅, t₅, e₅, ht₅, s00, s31, sk, sm, sr, srm, so⟩ :=
    swF_exec (P := I) c₄ e₄.wb_right (d := d) (m := m)
      (by rw [K4 9998 (by unfold scr1; omega) (by omega) (by omega) (by omega) (by omega)
            (by omega)]; exact r98)
      (by rw [m4 _ (by omega)]; exact H.bm) (by omega)
  have k5 : ∀ r, r ≠ 9400 → r ≠ 9431 → r ≠ 9650 → r ≠ 9651 → c₅.nreg r = c₄.nreg r := sk
  have m5 : ∀ a, a < A0 → c₅.nmem a = c.nmem a := fun a ha => by rw [sm, m4 a ha]
  have H₅ : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j c₅.nmem :=
    H.congr hfr hfb hhi hWzd hWzd' hWlo fun a _ h => m5 a h
  -- the semantics of an empty part
  set u₀ : D → ℤ := fun y => cap (.inl y) with hu₀
  set g₀ : D → ℤ := fun y => f₀ (.inl y) with hg₀
  have hpre' : NegPre M₀ (u₀ - g₀) :=
    ⟨H.pl, H.rot, H.ft, fun y _ => by
      simp only [Pi.sub_apply, hu₀, hg₀]; linarith [H.pseudo.le_cap (.inl y)]⟩
  have hfeas : ∃ Ψ : F → ℤ, IsPseudo M₀ u₀ (g₀ + M₀.cob Ψ) :=
    ⟨0, ⟨fun y => by
      show f₀ (.inl (M₀.rev y)) + M₀.cob 0 (M₀.rev y) = -(f₀ (.inl y) + M₀.cob 0 y)
      have := H.pseudo.antisymm (.inl y)
      simp only [CombMap.cob, Pi.zero_apply, sub_self, add_zero]
      exact this, fun y => by
      show f₀ (.inl y) + M₀.cob 0 y ≤ cap (.inl y)
      simp only [CombMap.cob, Pi.zero_apply, sub_self, add_zero]
      exact H.pseudo.le_cap (.inl y)⟩⟩
  obtain ⟨χ, hχ⟩ := neg_some (negMach_spec (nsIds M₀ H.enum (en 0)) M₀ I) hfeas
  have hpos : ∀ x : V × Bool, 0 ≤ (cap - f₀) (.inr x) := fun x => by
    simp only [Pi.sub_apply]; linarith [H.pseudo.le_cap (.inr x)]
  have hnegP : negP (negMach (nsIds M₀ H.enum (en 0)) M₀ I) (cap - f₀) = some χ := by
    unfold negP
    rw [if_pos hpos]
    exact hχ
  have e0 : fpState (M₀.pendant e he) cap f₀ (π.lift e he) (msspP (Klein.msspPlaneK M₀))
      (frRef F) (π.lift e he).k = (f₀, 0) := by
    show fpState _ _ _ _ _ _ π.k = _
    rw [hk00]; rfl
  have hfx : fixPath (M₀.pendant e he) cap f₀ (π.lift e he) (msspP (Klein.msspPlaneK M₀))
      (frRef F) (negP (negMach (nsIds M₀ H.enum (en 0)) M₀ I)) =
      f₀ + (M₀.pendant e he).cob χ := by
    rw [fixPath_eq_fpState, e0]
    simp only
    rw [hnegP]
  have hmssp : MSSPSpecAt (M₀.pendant e he) (msspP (Klein.msspPlaneK M₀)) (π.lift e he) :=
    msspP_spec (fun ℓ hnn x hx => Klein.msspPlaneK_spec H.pl H.rot H.ft π ℓ hnn x hx)
  have hps := (fixPath_spec (pendant_isPlane he H.pl) H.capnn H.pseudo (π.lift e he) hmssp
    (frRef_spec _) (negP_spec (negMach_spec (nsIds M₀ H.enum (en 0)) M₀ I))).pseudo
  rw [hfx] at hps
  -- the bounds
  have hAS : ((q.AS : ℕ) : ℤ) = SPath.absSum cap := cIn_as H.fr
  have hKe : (16 * (4 * (q.AS + m' * (4 * q.AS + 1)) + 12 * q.AS + 4) : ℤ) ≤ q.K := by
    have e : q.K = 16 * (4 * (q.AS + m' * (4 * q.AS + 1)) + 12 * q.AS + 4) := by
      show 16 * fpB q.AS m' q.k = _; rw [hq0]; unfold fpB; ring
    rw [e]; push_cast; exact le_rfl
  have hAS0 : (0 : ℤ) ≤ q.AS := by positivity
  have hY : (0 : ℤ) ≤ (m' : ℤ) * (4 * q.AS + 1) := by positivity
  have hgK : ∀ y, |f₀ y| ≤ (q.K : ℤ) := fun y => by
    have h1 := abs_le_of_pseudo H.pseudo y
    have h2 := abs_le_absSum cap y
    have h3 := abs_le_absSum cap ((M₀.pendant e he).rev y)
    rw [← hAS] at h2 h3
    push_cast at hKe; nlinarith
  have hℓK : ∀ y, |cap y - f₀ y| ≤ (q.K : ℤ) := fun y => by
    have h1 := abs_le_of_pseudo H.pseudo y
    have h2 := abs_le_absSum cap y
    have h3 := abs_le_absSum cap ((M₀.pendant e he).rev y)
    rw [← hAS] at h2 h3
    have h4 : |cap y - f₀ y| ≤ |cap y| + |f₀ y| := abs_sub _ _
    push_cast at hKe; nlinarith
  -- the final step on the base map
  have q5 : ∀ r, (9400 ≤ r ∧ r ≤ 9438 ∧ r ≠ 9420 ∧ r ≠ 9422 ∧ r ≠ 9400 ∧ r ≠ 9431) ∨
      r = 9469 ∨ r = 9310 ∨ r = 9374 ∨ r = 9375 ∨ r = 9376 → c₅.nreg r = c₄.nreg r :=
    fun r hr => k5 r (by omega) (by omega) (by omega) (by omega)
  obtain ⟨c₆, t₆, e₆, ht₆, F6, z6, k6, r6, rr6, rm6, o6⟩ :=
    finP9_exec C C₀ hC H.enum hm0 u₀ g₀ hpre' I I c₅ e₅.wb_right (Tb := A0 + 9 * m' + 1) (k := 0)
      (PDb := q.PDb) (CWb := A0 + 9 * m' + 1) (CRb := A0 + 9 * m' + 1) (FWb := A0 + 9 * m' + 1)
      (K := q.K) (Wz := Wz) (RVb := d' + 4 + m') (RTb := d + 4 + m + m)
      (CPb := d' + 4 + 3 * m') (FLb := d' + 4 + 6 * m') (LABb := A0 + m') (Z := Z') hχ
      (by rw [q5 _ (by omega), z69]) s00 (by rw [q5 _ (by omega), z36])
      (by rw [q5 _ (by omega), z34]) (by rw [q5 _ (by omega), z35]) (by rw [q5 _ (by omega), z21])
      (by rw [q5 _ (by omega), z10]) (by rw [q5 _ (by omega), z01])
      (by rw [q5 _ (by omega), z02]) (by rw [q5 _ (by omega), z30]) s31
      (by rw [q5 _ (by omega), z74]) (by rw [q5 _ (by omega), z75]) (by rw [q5 _ (by omega), z76])
      (by rw [q5 _ (by omega), z05])
      (fun i hi => by rw [H₅.rvE hi]; exact H₅.brv i hi)
      (fun i hi => by rw [show d + 4 + m + m + i = d + 4 + 2 * m + i by omega]; exact H₅.bsg i hi)
      (fun i hi => by
        have := (H₅.fr.cp i (by omega)).1
        rw [H₅.hen i hi] at this; exact this)
      (fun i hi => by rw [sm, L4 i (by omega), pq_lab H hi])
      (fun l hl' => absurd hl' (Nat.not_lt_zero _)) (fun l hl' => absurd hl' (Nat.not_lt_zero _))
      (fun i hi _ => by
        have hfl := H₅.fr.fl i (by omega)
        rw [H₅.hen i hi] at hfl
        exact hfl)
      (fun l hl' => absurd hl' (Nat.not_lt_zero _)) (fun l hl' => absurd hl' (Nat.not_lt_zero _))
      (fun l hl' => absurd hl' (Nat.not_lt_zero _)) (fun l hl' => absurd hl' (Nat.not_lt_zero _))
      (fun i hi => hgK _) (fun i hi => hℓK _)
      (fun i hi => by
        have h1 := hps.le_cap ((M₀.pendant e he).rev (.inl (en i)))
        rw [hps.antisymm (.inl (en i))] at h1
        have h2 := H₅.fr.cp _ (H₅.fr.rv i (by omega)).1
        have h3 := (H₅.fr.rv i (by omega)).2
        rw [H₅.hen i hi] at h3
        rw [← h3] at h1
        have : (c₅.nmem (d' + 4 + 3 * m' + c₅.nmem (d' + 4 + m' + i)) : ℤ) ≤ Z' := by
          exact_mod_cast h2.2
        have h4 : -((f₀ + (M₀.pendant e he).cob χ) (.inl (en i))) ≤ Z' := by linarith [h2.1]
        show 0 ≤ (Z' : ℤ) + (f₀ (.inl (en i)) + M₀.cob χ (en i))
        have e5 : (f₀ + (M₀.pendant e he).cob χ) (.inl (en i)) =
            f₀ (.inl (en i)) + M₀.cob χ (en i) := rfl
        linarith)
      (fun a ha => by rw [m5 a (by omega)]; exact hz a ha) hSz ⟨by omega, by omega⟩
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
      hWz (by omega) wL hw2' hw3
      (fun i hi => by
        have := (H₅.fr.cp i (by omega)).2
        have hrt : rtL M₀ (u₀ - g₀) = rtL M₀ (fun y => cap (.inl y) - f₀ (.inl y)) := rfl
        clear * - this hv hrt; omega)
      (fun l hl' => absurd hl' (Nat.not_lt_zero _)) (fun l hl' => absurd hl' (Nat.not_lt_zero _))
  refine ⟨c₆, _, e₄.seq (e₅.seq e₆), ?_, fun i hi => ?_, fun a ha hn => ?_, z6, fun r hr => ?_,
    by rw [o6, so, o4]⟩
  · unfold zT9; clear * - ht₄ ht₅ ht₆; omega
  · rw [hfx]
    by_cases him : i < m
    · rw [F6 i him, H.hen i him]; rfl
    · obtain ⟨x, hx⟩ := H.en_inr hi (by omega)
      rw [k6 (d' + 4 + 6 * m' + i) (by omega) (by omega) (Or.inr (by omega)), m5 _ (by omega),
        H.fr.fl i hi, hx]
      show (Z' : ℤ) + f₀ (.inr x) = Z' + (f₀ (.inr x) + (M₀.pendant e he).cob χ (.inr x))
      rw [pcob_inr, add_zero]
  · refine ⟨?_, by rw [rm6, srm, rm4]⟩
    by_cases hw : a ≤ Wz
    · rw [z6 a hw, hz a hw]
    · have hn' : a < d' + 4 + 6 * m' ∨ d' + 4 + 6 * m' + m ≤ a := by
        have := H.mm; omega
      rw [k6 a (by omega) (by omega) hn', m5 a ha]
  · unfold NcStep.PKeep at hr
    rw [r6 r (by unfold KeepR; omega) (by omega), k5 r (by omega) (by omega) (by omega) (by omega),
      K4 r (by unfold scr1; omega) (by omega) (by omega) (by omega) (by omega) (by omega)]

end F9b

end BKMNW

end PlanarFlow
