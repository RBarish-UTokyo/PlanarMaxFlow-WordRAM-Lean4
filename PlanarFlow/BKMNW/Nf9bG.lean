module

public import PlanarFlow.BKMNW.Nf9bF

/-!
# Step 2 of the frozen fix on the machine

* **`st9_run`**: `st2_exec` on the base map `M₀` from the configuration after
  `swB ; qbP` (the queries `QB` of `st9_qb`, the base reverse from the pendant `RV`, the base `SG`);
* **`st9_exec`**: from the prologue on the pendant frame (`ProOut`), `swB ; qbP ; st2 msP ; p7dG`
  within `6 + (16 k + 3) + cost m k b + st2T b k + 4` steps reaches the state of the stage loop for
  `X = mkP …` (`Regs`, `Fix`, `Stt (X.st 0)`, `Img`), with `r9400 = m`, `r9431 = d + 4 + 2m` (the
  base frame for the final negative-length call) and the registers of the final step.
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
  WordRAM WordRAM.Machine WordRAM.Programs

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M₀ : CombMap D V F} {e : V → D} {he : ∀ v, M₀.tail (e v) = v}
variable {en : ℕ → D} {en' : ℕ → D ⊕ (V × Bool)} {m m' Z' d d' : ℕ}
  {cap f₀ : D ⊕ (V × Bool) → ℤ} {segs : List (SPath M₀)} {lo hi Gb j : ℕ} {mem : ℕ → ℕ}

section Ctx

variable (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem)
include H

set_option maxHeartbeats 8000000 in
/-- **Step 2 on the base map** (`st2_exec` instantiated) from the configuration after `swB ; qbP`. -/
theorem st9_run {msP : Stmt} {Scr : ℕ → Prop} {cost Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    (hMS : MsCall.MsspCallSpec M₀ msP Scr cost Rm wzm) (hScr : ∀ r, Scr r → r < 9300)
    (hk0 : 0 < (segs[j]'H.hj).k) {A0 W Wz : ℕ} {I : Input}
    (hG : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem)
      ((cIn d' m' Gb segs j Z' mem).Qb A0)).Good W)
    (c : Config) (hO : ProOut (cIn d' m' Gb segs j Z' mem) A0 c)
    (hhi : hi ≤ A0) (hfr : d' + 4 + 7 * m' ≤ A0) (hfb : d + 4 + 3 * m ≤ A0)
    (hWzd : Wz < d) (hWzd' : Wz < d') (hWlo : Wz < lo)
    (c₂ : Config) (hc₂ : WordsBounded W c₂)
    (hm₂ : c₂.nmem = qbM c.nmem (cIn d' m' Gb segs j Z' mem).PDb (d' + 4 + m')
      (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem)
        ((cIn d' m' Gb segs j Z' mem).Qb A0)).ETb
      ((cIn d' m' Gb segs j Z' mem).Qb A0 + 15 * (cIn d' m' Gb segs j Z' mem).k)
      (cIn d' m' Gb segs j Z' mem).k)
    (hr₂ : ∀ r, r ≠ 9400 → r ≠ 9431 → r ≠ 9410 → (r < 9650 ∨ 9657 < r) → c₂.nreg r = c.nreg r)
    (r00 : c₂.nreg 9400 = m) (r31 : c₂.nreg 9431 = d + 4 + m + m)
    (r10 : c₂.nreg 9410 = (cIn d' m' Gb segs j Z' mem).Qb A0 + 15 * (cIn d' m' Gb segs j Z' mem).k)
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hwz : wzm m (2 * Z') ≤ Wz)
    (hSHz : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem)
      ((cIn d' m' Gb segs j Z' mem).Qb A0)).SH + (mkP M₀ e he en' (segs[j]'H.hj) cap f₀
      (cIn d' m' Gb segs j Z' mem) ((cIn d' m' Gb segs j Z' mem).Qb A0)).WN ≤ Wz)
    (hpw : lyP ((cIn d' m' Gb segs j Z' mem).Qb A0 + 15 * (cIn d' m' Gb segs j Z' mem).k)
      (cIn d' m' Gb segs j Z' mem).cw.cnt (cIn d' m' Gb segs j Z' mem).k +
      Rm m (cIn d' m' Gb segs j Z' mem).k (cIn d' m' Gb segs j Z' mem).cw.cnt ≤ W)
    (hKL : (cIn d' m' Gb segs j Z' mem).K + 8 * fpB (cIn d' m' Gb segs j Z' mem).AS m'
      (cIn d' m' Gb segs j Z' mem).k + moOf (cIn d' m' Gb segs j Z' mem).cw.cnt
      (8 * fpB (cIn d' m' Gb segs j Z' mem).AS m' (cIn d' m' Gb segs j Z' mem).k) ≤ W) :
    let q := cIn d' m' Gb segs j Z' mem
    let X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0)
    ∃ c' t, Exec I W (st2 msP) c₂ c' t ∧ t ≤ cost m q.k q.cw.cnt + st2T q.cw.cnt q.k ∧
      c'.nreg 9501 = c₂.nreg 9416 ∧ c'.nreg 9502 = c₂.nreg 9412 ∧ c'.nreg 9503 = c₂.nreg 9413 ∧
      c'.nreg 9504 = X.ETb ∧ c'.nreg 8100 = q.cw.cnt ∧ c'.nreg 9360 = wfOf q.cw.cnt q.k + 1 ∧
      c'.nreg 9361 = shOf q.cw.cnt q.k X.L + (wfOf q.cw.cnt q.k + 1) ∧
      c'.nreg 8113 = q.cw.cnt * q.cw.cnt ∧
      c'.nreg 8102 = X.PRb ∧ c'.nreg 8125 = moOf q.cw.cnt X.L - X.K % moOf q.cw.cnt X.L ∧
      c'.nreg 8124 = moOf q.cw.cnt X.L ∧
      c'.nreg 8112 = 1 ∧ c'.nreg 8104 = 2 * q.k ∧
      c'.nreg 8115 = q.cw.cnt * q.cw.cnt + q.cw.cnt + q.cw.cnt + 1 + 2 * q.k ∧
      c'.nreg 9362 = lySI (q.Qb A0 + 15 * q.k) q.cw.cnt q.k ∧
      c'.nreg 8107 = X.ELb ∧
      c'.nreg 7600 = q.cw.cnt ∧ c'.nreg 7601 = q.cw.cnt ∧ c'.nreg 7602 = 0 ∧
      c'.nreg 7603 = q.cw.cnt * q.cw.cnt ∧
      c'.nreg 7604 = q.cw.cnt * q.cw.cnt + q.cw.cnt ∧
      c'.nreg 7605 = q.cw.cnt * q.cw.cnt + q.cw.cnt + q.cw.cnt + 1 + 2 * q.k ∧
      c'.nreg 7607 = lySb q.cw.cnt q.k ∧ c'.nreg 7608 = lySb q.cw.cnt q.k + q.cw.cnt ∧
      c'.nreg 7609 = lySb q.cw.cnt q.k + q.cw.cnt + q.cw.cnt ∧ c'.nreg 7610 = moOf q.cw.cnt X.L ∧
      c'.nreg 7611 = 6 * ((q.cw.cnt + 2) * X.L) ∧ c'.nreg 7612 = wfOf q.cw.cnt q.k + 1 ∧
      c'.nreg 7614 = lyOb (q.Qb A0 + 15 * q.k) q.cw.cnt q.k ∧
      c'.nreg 7615 = lyP (q.Qb A0 + 15 * q.k) q.cw.cnt q.k ∧
      c'.nreg 7616 = shOf q.cw.cnt q.k X.L ∧
      (∀ r, KeepR r → ¬ st2W r → c'.nreg r = c₂.nreg r) ∧
      ImgAt c'.nmem (img0 q.cw.cnt X.Dm X.ET X.EH q.k) X.L (lySb q.cw.cnt q.k)
        (wfOf q.cw.cnt q.k) (shOf q.cw.cnt q.k X.L) ∧
      ZeroAt c'.nmem Wz (lySb q.cw.cnt q.k) (wfOf q.cw.cnt q.k) (shOf q.cw.cnt q.k X.L) ∧
      (∀ e' < 2 * q.k, c'.nmem (lySI (q.Qb A0 + 15 * q.k) q.cw.cnt q.k + e') =
        MsCall.sIdx X.ET (2 * q.k) q.cw.cnt e') ∧
      (∀ a, Wz < a → a < q.Qb A0 + 15 * q.k → c'.nmem a = c₂.nmem a) ∧
      c'.rreg = c₂.rreg ∧ c'.rmem = c₂.rmem ∧ c'.output = c₂.output := by
  dsimp only
  set q := cIn d' m' Gb segs j Z' mem with hq
  have eqk : (cIn d' m' Gb segs j Z' mem).k = q.k := rfl
  have eqm : (cIn d' m' Gb segs j Z' mem).m = q.m := rfl
  have eqP : (cIn d' m' Gb segs j Z' mem).PDb = q.PDb := rfl
  have eqc : (cIn d' m' Gb segs j Z' mem).cw.cnt = q.cw.cnt := rfl
  have eqK : (cIn d' m' Gb segs j Z' mem).K = q.K := rfl
  have eqA : (cIn d' m' Gb segs j Z' mem).AS = q.AS := rfl
  set X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0) with hX
  have IN := st9_in H hk0 hG c hO hhi hfr hfb
  have QB := st9_qb H hk0 hG c hO hhi hfr hfb
  have hkq : (segs[j]'H.hj).k = q.k := (pq_k H).symm
  have hk0' : 0 < q.k := hkq ▸ hk0
  obtain ⟨R1, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ := hO
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, g11, g74, g75, g76, g77, g12, g13, g14, g15, g16, g17, g18⟩ := R1
  have alo' : ∀ a < A0, c.nmem a = mem a := alo
  obtain ⟨hb2k, hrv, hrt, hpd, hln, hET, hEH⟩ := IN
  have hmm := H.mm
  have hqm : q.m = m' := rfl
  set QBb := q.Qb A0 + 15 * q.k with hQBb
  have hQe : q.Qb A0 = A0 + 9 * m' + 1 := by
    show A0 + m' + m' + m' + m' + 1 + m' + m' + m' + m' + m' = _; omega
  have hPDk : q.PDb + q.k ≤ hi := (cIn_top (d := d') (Z := Z') (m := m) H.sl H.hj).1
  have hPDl : lo ≤ q.PDb := (cIn_top (d := d') (Z := Z') (m := m) H.sl H.hj).2.2
  -- the memory below the queries is that of `c`
  have hETb : ∀ a < 2 * q.k, c.nmem (X.ETb + a) < q.cw.cnt := fun a ha => by
    rw [hET a (by omega)]; exact SLx.ET_lt hG (by show a < 2 * (segs[j]'H.hj).k; omega)
  have m2 : ∀ a, a < QBb → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hm₂]; exact qbM_out c.nmem hETb (Or.inl ha)
  have hℓ : ∀ y, 0 ≤ ℓ0 cap f₀ y := fun y => by
    unfold ℓ0; simp only [Pi.sub_apply]; linarith [H.pseudo.le_cap (.inl y)]
  -- sizes
  have hSHz' : X.SH + X.WN ≤ Wz := hSHz
  have hWfe : X.Wf = wfOf q.cw.cnt q.k := by
    show MsCall.fW _ _ = _; unfold wfOf lySb; rw [← hkq]; rfl
  have hMo : X.Mo = moOf q.cw.cnt X.L := rfl
  have hSHe : X.SH = shOf q.cw.cnt q.k X.L := rfl
  have hSHWN : X.SH = X.WN + 1 := by
    rw [hSHe]; show _ = 2 * X.Wf + 1 + X.Mo * X.Mo + X.Mo + 1; rw [hMo, hWfe]; unfold shOf; ring
  have hlwf := lySb_le_wfOf q.cw.cnt q.k
  have hWN1 : 2 * wfOf q.cw.cnt q.k + 1 ≤ X.WN := by
    show _ ≤ 2 * X.Wf + 1 + X.Mo * X.Mo + X.Mo; rw [hWfe]; omega
  have hlow : shOf q.cw.cnt q.k X.L + (wfOf q.cw.cnt q.k + 1) + lySb q.cw.cnt q.k ≤ Wz + 1 := by
    rw [← hSHe]; omega
  have hOmP : lyOm QBb q.cw.cnt q.k + q.cw.cnt * q.cw.cnt ≤ lyP QBb q.cw.cnt q.k := by
    unfold lyP lyOb lyS lyA; omega
  have hWA : Wz < A0 := by omega
  have hPRS : X.PRb + q.cw.cnt ≤ QBb := by
    show q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k +
      q.cw.cnt ≤ _; clear * - hb2k hQBb eqk eqc; omega
  have hETS : X.ETb + 2 * q.k ≤ QBb := by
    show q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + 2 * q.k ≤ _; clear * - hQBb; omega
  have hEHS : q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + 2 * q.k ≤ QBb := by
    clear * - hQBb; omega
  have hELS : X.ELb + 2 * q.k ≤ QBb := by
    show q.Qb A0 + q.k + q.k + q.k + 2 * q.k ≤ _; clear * - hQBb; omega
  have hzA : Wz < X.PRb ∧ Wz < X.ETb ∧
      Wz < q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k ∧ Wz < X.ELb := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show Wz < q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k +
        q.k; clear * - hWA hQe; omega
    · show Wz < q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k; clear * - hWA hQe; omega
    · clear * - hWA hQe; omega
    · show Wz < q.Qb A0 + q.k + q.k + q.k; clear * - hWA hQe; omega
  have hlT : q.cw.cnt ≤ lyT q.cw.cnt q.k := by unfold lyT; clear * -; omega
  have hpla : MsCall.MsPlace m (segs[j]'H.hj).k q.cw.cnt Wz W (d' + 4 + m') (d + 4 + m + m)
      q.PDb (A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m) QBb
      (lyOm QBb q.cw.cnt (segs[j]'H.hj).k) (lyP QBb q.cw.cnt (segs[j]'H.hj).k)
      (Rm m (segs[j]'H.hj).k q.cw.cnt) := by
    rw [hkq]
    refine ⟨⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩, ⟨by omega, ?_⟩,
      ⟨?_, hOmP⟩, hpw⟩
    all_goals (unfold lyOm; clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT; omega)
  -- the registers of `c₂`
  have k2 : ∀ r, 9300 ≤ r → r ≠ 9400 → r ≠ 9431 → r ≠ 9410 → (r < 9650 ∨ 9657 < r) →
      c₂.nreg r = c.nreg r := fun r _ h1 h2 h3 h4 => hr₂ r h1 h2 h3 h4
  obtain ⟨c', t, ex, ht, s01, s02, s03, s04, s00, s60, s61, s13, s8102, s25, s24, s12, s8104,
      s15, s62, s8107, b00, b01, b02, b03, b04, b05, b07, b08, b09, b10, b11, b12, b14, b15, b16,
      sk, sI, sZ, sSI, sm, sr, srm, so⟩ :=
    st2_exec M₀ hMS hScr H.pl H.rot (en := en) (m := m) (P := segs[j]'H.hj)
      (ℓ := ℓ0 cap f₀) (Lmax := 2 * Z')
      (b := q.cw.cnt) (ts := fun i => en (c₂.nmem (QBb + i))) (RVb := d' + 4 + m')
      (RTb := d + 4 + m + m) (Pb := q.PDb) (Lb := A0 + q.m + q.m + q.m + q.m + 1 + q.m + q.m + q.m)
      (Qb := QBb) (S1 := QBb) (PRb := X.PRb)
      (ETb := X.ETb) (EHb := q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k)
      (ELb := X.ELb) (K := X.K) (L := X.L) (Wz := Wz) (W := W) (ET := X.ET) (EH := X.EH)
      (Dm := X.Dm) (I := I) c₂ hc₂ H.enum hk0 hℓ
      (fun i hi => by
        show M₀.face (en (c₂.nmem (QBb + i))) ∈ (segs[j]'H.hj).faces
        rw [hm₂, (QB i hi).2, ← SPath.lift_faces (e := e) (he := he)]
        exact (mkP_corners H hk0 (q.Qb A0)).1 i hi)
      (fun i hi i' hi' => by
        show ((Klein.msspPlaneK M₀ (segs[j]'H.hj).darts (ℓ0 cap f₀)
          (M₀.face (en (c₂.nmem (QBb + i)))) (M₀.face (en (c₂.nmem (QBb + i'))))).getD 0).toNat =
          X.Dm i i'
        rw [hm₂, (QB i hi).2, (QB i' hi').2]; rfl)
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g18,
        hQBb]; ring)
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), a19])
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g01,
        hkq])
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g36])
      r00
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g30]; rfl)
      r31
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g02])
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g09])
      r10
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g17]; rfl)
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g14]; rfl)
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g15])
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g77]; rfl)
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), a10]; rfl)
      (by rw [k2 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), a22]; rfl)
      (fun i hi => by rw [m2 _ (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT hi; omega)]; exact hrv i hi)
      (fun i hi => by rw [m2 _ (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT hi; omega)]; exact hrt i hi)
      (fun l hl => by rw [m2 _ (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT hl; omega)]; exact hpd l hl)
      (fun i hi => by rw [m2 _ (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT hi; omega)]; exact hln i hi)
      (fun i hi => by rw [hm₂]; exact ⟨(QB i hi).1, rfl⟩)
      (fun x hx => by rw [m2 _ (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT hx; omega)]; exact (aPW x (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT hx; omega)).2.1)
      (fun a ha => by rw [m2 _ (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT ha; omega)]; exact hET a ha)
      (fun a ha => by rw [m2 _ (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT ha; omega)]; exact hEH a ha)
      (fun a ha => by rw [m2 _ (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT ha; omega)]; exact (aPW a (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT ha; omega)).2.2)
      hpla (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT; omega) hPRS (by rw [hkq]; exact hETS) (by rw [hkq]; exact hEHS)
      (by rw [hkq]; exact hELS) hzA
      (SLx.frImgB0 hG)
      (fun a ha => by rw [m2 _ (by clear * - hfr hfb hhi hmm hqm hQe hQBb hPDk hPDl hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hETS hEHS hELS hPRS hOmP hlT ha; omega)]; exact hz a ha) hwz
      (by rw [hkq]; exact hlow) hKL
  rw [hkq] at ht s62 b14 b15 b16 sI sZ sSI s8104 s15 s60 s61 b05 b07 b08 b09 b12
  exact ⟨c', t, ex, ht, s01, s02, s03, s04, s00, s60, s61, s13, s8102, s25, s24, s12, s8104,
      s15, s62, s8107, b00, b01, b02, b03, b04, b05, b07, b08, b09, b10, b11, b12, b14, b15, b16,
      sk, sI, sZ, sSI, sm, sr, srm, so⟩

set_option maxHeartbeats 8000000 in
/-- **Step 2 of the frozen fix and the glue** (see the module docstring). -/
theorem st9_exec {msP : Stmt} {Scr : ℕ → Prop} {cost Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    (hMS : MsCall.MsspCallSpec M₀ msP Scr cost Rm wzm) (hScr : ∀ r, Scr r → r < 9300)
    (hk0 : 0 < (segs[j]'H.hj).k) {A0 W Wz : ℕ} {I : Input}
    (hG : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem)
      ((cIn d' m' Gb segs j Z' mem).Qb A0)).Good W)
    (c : Config) (hc : WordsBounded W c) (hO : ProOut (cIn d' m' Gb segs j Z' mem) A0 c)
    (r98 : c.nreg 9998 = d)
    (hhi : hi ≤ A0) (hfr : d' + 4 + 7 * m' ≤ A0) (hfb : d + 4 + 3 * m ≤ A0)
    (hWzd : Wz < d) (hWzd' : Wz < d') (hWlo : Wz < lo)
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hwz : wzm m (2 * Z') ≤ Wz)
    (hSHz : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem)
      ((cIn d' m' Gb segs j Z' mem).Qb A0)).SH + (mkP M₀ e he en' (segs[j]'H.hj) cap f₀
      (cIn d' m' Gb segs j Z' mem) ((cIn d' m' Gb segs j Z' mem).Qb A0)).WN ≤ Wz)
    (hpw : lyP ((cIn d' m' Gb segs j Z' mem).Qb A0 + 15 * (cIn d' m' Gb segs j Z' mem).k)
      (cIn d' m' Gb segs j Z' mem).cw.cnt (cIn d' m' Gb segs j Z' mem).k +
      Rm m (cIn d' m' Gb segs j Z' mem).k (cIn d' m' Gb segs j Z' mem).cw.cnt ≤ W)
    (hKL : (cIn d' m' Gb segs j Z' mem).K + 8 * fpB (cIn d' m' Gb segs j Z' mem).AS m'
      (cIn d' m' Gb segs j Z' mem).k + moOf (cIn d' m' Gb segs j Z' mem).cw.cnt
      (8 * fpB (cIn d' m' Gb segs j Z' mem).AS m' (cIn d' m' Gb segs j Z' mem).k) ≤ W) :
    let q := cIn d' m' Gb segs j Z' mem
    let X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0)
    ∃ c' t, Exec I W (.seq swB (.seq qbP (.seq (st2 msP) p7dG))) c c' t ∧
      t ≤ 6 + (16 * q.k + 3) + (cost m q.k q.cw.cnt + st2T q.cw.cnt q.k + 4) ∧
      X.Regs c' ∧ X.Fix c'.nmem ∧ X.Stt (X.st 0) c'.nmem ∧ X.Img c'.nmem ∧
      c'.nreg 9469 = X.p ∧ c'.nreg 9471 = X.SH ∧ c'.nreg 9474 = X.SH + (X.Wf + 1) ∧
      c'.nreg 9475 = 0 ∧ c'.nreg 9400 = m ∧ c'.nreg 9431 = d + 4 + m + m ∧
      (∀ r, KeepR r → ¬ st2W r → r ≠ 9469 → r ≠ 9471 → r ≠ 9474 → r ≠ 9475 → r ≠ 9400 →
        r ≠ 9431 → r ≠ 9410 → (r < 9650 ∨ 9657 < r) → c'.nreg r = c.nreg r) ∧
      (∀ a ≤ Wz, X.WN < a → ¬ (X.SH ≤ a ∧ a ≤ X.SH + X.WN) → c'.nmem a = 0) ∧
      (∀ a, Wz < a → a < q.Qb A0 + 15 * q.k → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  dsimp only
  set q := cIn d' m' Gb segs j Z' mem with hq
  have eqk : (cIn d' m' Gb segs j Z' mem).k = q.k := rfl
  have eqm : (cIn d' m' Gb segs j Z' mem).m = q.m := rfl
  have eqP : (cIn d' m' Gb segs j Z' mem).PDb = q.PDb := rfl
  have eqc : (cIn d' m' Gb segs j Z' mem).cw.cnt = q.cw.cnt := rfl
  have eqK : (cIn d' m' Gb segs j Z' mem).K = q.K := rfl
  have eqA : (cIn d' m' Gb segs j Z' mem).AS = q.AS := rfl
  set X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0) with hX
  have hkq : (segs[j]'H.hj).k = q.k := (pq_k H).symm
  have hk0' : 0 < q.k := hkq ▸ hk0
  have IN := st9_in H hk0 hG c hO hhi hfr hfb
  obtain ⟨hb2k, hrv, -, hpd, -, hET, -⟩ := IN
  have hO' := hO
  obtain ⟨R1, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ := hO'
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, g11, g74, g75, g76, g77, g12, g13, g14, g15, g16, g17, g18⟩ := R1
  have alo' : ∀ a < A0, c.nmem a = mem a := alo
  have hmm := H.mm
  have hqm : q.m = m' := rfl
  have hQe : q.Qb A0 = A0 + 9 * m' + 1 := by
    show A0 + m' + m' + m' + m' + 1 + m' + m' + m' + m' + m' = _; omega
  have hPDk : q.PDb + q.k ≤ hi := (cIn_top (d := d') (Z := Z') (m := m) H.sl H.hj).1
  have hWA : Wz < A0 := by omega
  have hW0 : q.Qb A0 + 15 * q.k + q.cw.cnt + 1 ≤ W := by
    have h14 : X.p + X.LG ≤ W := hG.l14
    have hp : X.p = lyP (q.Qb A0 + 15 * q.k) q.cw.cnt q.k := rfl
    unfold lyP lyOb lyS lyA lyOm lyT at hp
    clear * - h14 hp
    omega
  -- the base frame
  obtain ⟨c₁, t₁, e₁, ht₁, b00, b31, b10, bk, bm, br, brm, bo⟩ :=
    swB_exec (P := I) c hc r98 (m := m) (by rw [alo' _ (by clear * - hfr hfb hhi hmm hqm hQe hPDk hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hW0; omega)]; exact H.bm) (by clear * - hfr hfb hhi hmm hqm hQe hPDk hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hW0; omega)
  -- the queries
  have hET' : ∀ a < 2 * q.k, c.nmem (X.ETb + a) < q.cw.cnt := fun a ha => by
    rw [hET a (by clear * - hkq ha; omega)]
    exact SLx.ET_lt hG (by show a < 2 * (segs[j]'H.hj).k; clear * - hkq ha; omega)
  obtain ⟨c₂, t₂, e₂, ht₂, qm, qk, qr, qrm, qo⟩ :=
    qbP_exec (P := I) c₁ e₁.wb_right (k := q.k) (m := m) (b := q.cw.cnt) (PDb := q.PDb)
      (RVb := d' + 4 + m') (ETb := X.ETb) (QBb := q.Qb A0 + 15 * q.k)
      (by rw [bk _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g01])
      (by rw [bk _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g02])
      (by rw [bk _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g30];
          rfl)
      (by rw [bk _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g14];
          rfl)
      (by rw [bk _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g18];
          ring)
      (by rw [bk _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g36])
      (fun l hl => by rw [bm]; exact (hpd l (by clear * - hfr hfb hhi hmm hqm hQe hPDk hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hW0 hl; omega)).1)
      (fun i hi => by rw [bm]; exact (hrv i hi).1)
      (fun a ha => by rw [bm]; exact hET' a ha)
      ⟨by clear * - hfr hfb hhi hmm hqm hQe hPDk hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hW0; omega, by clear * - hfr hfb hhi hmm hqm hQe hPDk hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hW0; omega,
        by show q.Qb A0 + q.k + q.k + q.k + q.k + q.k + q.k + q.k + 2 * q.k ≤ _; clear * - hfr hfb hhi hmm hqm hQe hPDk hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hW0; omega⟩
      (by clear * - hfr hfb hhi hmm hqm hQe hPDk hWA hWzd hWzd' hWlo hb2k eqk eqc hkq hk0' hW0; omega)
  rw [bm] at qm
  have k12 : ∀ r, r ≠ 9400 → r ≠ 9431 → r ≠ 9410 → (r < 9650 ∨ 9657 < r) →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 h4 => by
    rw [qk r h4, bk r h1 h2 (by clear * - h4; omega) (by clear * - h4; omega) h3]
  -- step 2
  obtain ⟨c₃, t₃, e₃, ht₃, s01, s02, s03, s04, s00, s60, s61, s13, s8102, s25, s24, s12, s8104,
      s15, s62, s8107, x00, x01, x02, x03, x04, x05, x07, x08, x09, x10, x11, x12, x14, x15, x16,
      sk, sI, sZ, sSI, sm, sr, srm, so⟩ :=
    st9_run H hMS hScr hk0 (I := I) hG c hO hhi hfr hfb hWzd hWzd' hWlo c₂ e₂.wb_right qm k12
      (by rw [qk _ (by norm_num)]; exact b00) (by rw [qk _ (by norm_num)]; exact b31)
      (by rw [qk _ (by norm_num), b10, g18]; ring) hz hwz hSHz hpw hKL
  obtain ⟨c₄, t₄, e₄, ht₄, p69, p71, p74, p75, pk, pm, pr, prm, po⟩ :=
    p7dG_exec (P := I) c₃ e₃.wb_right
  -- the registers
  have K3 : ∀ r, r ≠ 9469 → r ≠ 9471 → r ≠ 9474 → r ≠ 9475 → c₄.nreg r = c₃.nreg r := pk
  have K2 : ∀ r, KeepR r → ¬ st2W r → r ≠ 9469 → r ≠ 9471 → r ≠ 9474 → r ≠ 9475 → r ≠ 9400 →
      r ≠ 9431 → r ≠ 9410 → (r < 9650 ∨ 9657 < r) → c₄.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => by
      rw [pk r h3 h4 h5 h6, sk r h1 h2, k12 r h7 h8 h9 h10]
  have nS : ∀ r, 9300 ≤ r → ¬ st2W r → r ≠ 9469 → r ≠ 9471 → r ≠ 9474 → r ≠ 9475 → r ≠ 9400 →
      r ≠ 9431 → r ≠ 9410 → (r < 9650 ∨ 9657 < r) → c₄.nreg r = c.nreg r :=
    fun r h1 => K2 r (keepR_ge h1)
  have mS : ∀ a, Wz < a → a < q.Qb A0 + 15 * q.k → c₄.nmem a = c.nmem a := fun a h1 h2 => by
    rw [pm, sm a h1 h2, qm]; exact qbM_out c.nmem hET' (Or.inl h2)
  have ht₃' : t₃ ≤ cost m q.k q.cw.cnt + st2T q.cw.cnt q.k := ht₃
  have hAS : ((q.AS : ℕ) : ℤ) = SPath.absSum cap := cIn_as H.fr
  have hSHe : X.SH = shOf q.cw.cnt q.k X.L := rfl
  have hWfe : X.Wf = wfOf q.cw.cnt q.k := by
    show MsCall.fW _ _ = _; unfold wfOf lySb; rw [← hkq]; rfl
  have hMo : X.Mo = moOf q.cw.cnt X.L := rfl
  have hSHWN : X.SH = X.WN + 1 := by
    rw [hSHe]; show _ = 2 * X.Wf + 1 + X.Mo * X.Mo + X.Mo + 1; rw [hMo, hWfe]; unfold shOf; ring
  have hSHz' : X.SH + X.WN ≤ Wz := hSHz
  have sZ' : ZeroAt c₃.nmem Wz (lySb q.cw.cnt q.k) (wfOf q.cw.cnt q.k) (shOf q.cw.cnt q.k X.L) :=
    sZ
  have hPk : X.P.k = q.k := hkq
  refine ⟨c₄, _, e₁.seq (e₂.seq (e₃.seq e₄)), by clear * - ht₁ ht₂ ht₃' ht₄; omega, ?_, ?_, ?_, ?_, by rw [p69, x15]; rfl,
    by rw [p71, x16]; rfl, by rw [p74, s61, ← hSHe, hWfe], p75,
    by rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      sk _ (keepR_ge (by norm_num)) (by simp [st2W]), qk _ (by norm_num)]; exact b00,
    by rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      sk _ (keepR_ge (by norm_num)) (by simp [st2W]), qk _ (by norm_num)]; exact b31,
    K2, ?_, mS, by rw [pr, sr, qr, br], by rw [prm, srm, qrm, brm], by rw [po, so, qo, bo]⟩
  · -- the registers of the stage loop
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), a10]; rfl
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g71]; exact hPk.symm
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), a73]
      have e : (4 * SPath.absSum cap + 1).toNat = 4 * q.AS + 1 := by rw [← hAS]; clear * -; omega
      exact e.symm
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g74]; rfl
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g75]; rfl
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g76]; rfl
    · rw [nS _ (by norm_num) (by simp [st2W]) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), g77]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s01,
        k12 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g16]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s02,
        k12 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g12]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s03,
        k12 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), g13]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s04]
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s00
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s60, hWfe]
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s61, ← hSHe, hWfe]
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s13
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s8102
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s25
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s24
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s12
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s8104, hPk]
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s15]
      show _ = q.cw.cnt * q.cw.cnt + q.cw.cnt + q.cw.cnt + 1 + 2 * X.P.k; rw [hPk]
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), s62]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact s8107
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact x00
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact x01
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact x02
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact x03
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact x04
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), x05]
      show _ = q.cw.cnt * q.cw.cnt + q.cw.cnt + q.cw.cnt + 1 + 2 * X.P.k; rw [hPk]
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), x07]
      show _ = q.cw.cnt * q.cw.cnt + q.cw.cnt + q.cw.cnt + 1 + 2 * X.P.k + 2 * X.P.k
      rw [hPk]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), x08]
      show _ = q.cw.cnt * q.cw.cnt + q.cw.cnt + q.cw.cnt + 1 + 2 * X.P.k + 2 * X.P.k + q.cw.cnt
      rw [hPk]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), x09]
      show _ = q.cw.cnt * q.cw.cnt + q.cw.cnt + q.cw.cnt + 1 + 2 * X.P.k + 2 * X.P.k + q.cw.cnt +
        q.cw.cnt
      rw [hPk]; rfl
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact x10
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact x11
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num), x12, hWfe]
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact x14
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact x15
    · rw [K3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)]; exact x16
  · exact (st9_fix H hk0 hG c hO hhi hfr hfb hWA c₄ mS (fun e' he' => by
      rw [pm, hkq]; exact sSI e' (by rw [← hkq]; exact he'))).1
  · exact (st9_fix H hk0 hG c hO hhi hfr hfb hWA c₄ mS (fun e' he' => by
      rw [pm, hkq]; exact sSI e' (by rw [← hkq]; exact he'))).2
  · -- the image
    have hI : ImgAt c₄.nmem (img0 X.b X.Dm X.ET X.EH X.P.k) X.L (lySb X.b X.P.k)
        (wfOf X.b X.P.k) X.SH := by rw [pm, hPk]; exact sI
    have hZ : ZeroAt c₄.nmem Wz (lySb X.b X.P.k) (wfOf X.b X.P.k) X.SH := by
      rw [pm, hPk]; exact sZ
    exact SLx.img_of_st2 hG hI hZ hSHz' (by rw [hWfe, hPk]; rfl)
  · -- the rest of the zero area
    intro a ha h1 h2
    have e1 := hSHWN
    rw [hSHe] at e1 h2
    rw [pm]
    have hlwf := lySb_le_wfOf q.cw.cnt q.k
    have hWN1 : 2 * wfOf q.cw.cnt q.k + 1 ≤ X.WN := by
      show _ ≤ 2 * X.Wf + 1 + X.Mo * X.Mo + X.Mo; rw [hWfe]; clear * -; omega
    refine sZ' a ha (by clear * - ha h1 h2 e1 hlwf hWN1 hSHz'; omega)
      (by clear * - ha h1 h2 e1 hlwf hWN1 hSHz'; omega) (by clear * - ha h1 h2 e1 hlwf hWN1 hSHz'; omega)
      (by clear * - ha h1 h2 e1 hlwf hWN1 hSHz'; omega)

end Ctx

end F9b

end BKMNW

end PlanarFlow
