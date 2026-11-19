module

public import PlanarFlow.BKMNW.Nf9bG
public import PlanarFlow.BKMNW.Nf9bI
public import PlanarFlow.BKMNW.Nf9bL
public import PlanarFlow.BKMNW.Nf7eWH

/-!
# The frozen-fix program `fixC` and its two branches

**`fixC msP = kTst ; if 0 < k then fxPos msP else fxZero`** with

* `fxPos msP = fpPro ; (swB ; qbP ; st2 msP ; p7dG) ; (loopP ; clrP ; finP)`: the prologue on
  the pendant frame, step 2 with the MSSP call on the base map (`st9_exec`), the stage loop on the
  pendant map and the final negative-length call on the base map (`fin9_exec`);
* `fxZero = (proP1a ; proP1b ; proP3a ; z0Blk) ; (swF ; finP)` (an empty part: the final call
  alone).

**`fxPos_exec`**, **`fxZero_exec`**: each branch writes the frozen fix in the pendant flow array,
keeps the memory below the heap top off that array, the zero area, the registers `PKeep` and the
output, within `posT9 C C₀ cost m m' k b` resp. `zT9 C C₀ m m'` steps. `fixC_branch`, `fixC_noEmit`.
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

/-! ### The programs -/

/-- **The branch `0 < k`.** -/
def fxPos (msP : Stmt) : Stmt :=
  .seq fpPro (.seq (.seq swB (.seq qbP (.seq (st2 msP) p7dG))) (.seq loopP (.seq clrP finP)))

/-- **The branch `k = 0`.** -/
def fxZero : Stmt := .seq (.seq proP1a (.seq proP1b (.seq proP3a z0Blk))) (.seq swF finP)

/-- **The frozen-fix program** (FixConservationOnPath with frozen vertices on the pendant frame,
the MSSP and negative-length calls on the base frame). -/
def fixC (msP : Stmt) : Stmt := .seq kTst (.ifLtN 9438 9437 (fxPos msP) fxZero)

theorem fixC_noEmit {msP : Stmt} (h : BKMNW.Stmt.noEmit msP = true) :
    BKMNW.Stmt.noEmit (fixC msP) = true := by
  have h1 : BKMNW.Stmt.noEmit kTst = true := by decide +kernel
  have h2 : BKMNW.Stmt.noEmit fpPro = true := by decide +kernel
  have h3 : BKMNW.Stmt.noEmit p7cA = true := by decide +kernel
  have h4 : BKMNW.Stmt.noEmit p7cM = true := by decide +kernel
  have h5 : BKMNW.Stmt.noEmit p7cSv = true := by decide +kernel
  have h6 : BKMNW.Stmt.noEmit p7cRs = true := by decide +kernel
  have h7 : BKMNW.Stmt.noEmit st2b = true := by decide +kernel
  have h8 : BKMNW.Stmt.noEmit st2c = true := by decide +kernel
  have h9 : BKMNW.Stmt.noEmit p7dG = true := by decide +kernel
  have h10 : BKMNW.Stmt.noEmit loopP = true := by decide +kernel
  have h11 : BKMNW.Stmt.noEmit clrP = true := by decide +kernel
  have h12 : BKMNW.Stmt.noEmit finP = true := by decide +kernel
  have h13 : BKMNW.Stmt.noEmit fxZero = true := by decide +kernel
  have h14 : BKMNW.Stmt.noEmit swB = true := by decide +kernel
  have h15 : BKMNW.Stmt.noEmit qbP = true := by decide +kernel
  simp only [fixC, fxPos, st2, st2ab, st2a, BKMNW.Stmt.noEmit, h, h1, h2, h3, h4, h5, h6, h7, h8,
    h9, h10, h11, h12, h13, h14, h15, Bool.and_self]

/-- **`fixC` from its two branches** (`fixP7_branch`). -/
theorem fixC_branch {I : Input} {W : ℕ} (msP : Stmt) (c : Config) (hc : WordsBounded W c)
    {Gb j ns k : ℕ} (r07 : c.nreg 6807 = Gb) (r00 : c.nreg 6800 = j) (hns : c.nmem Gb = ns)
    (hk : c.nmem (Gb + 1 + j + ns) = k) (hW : Gb + 1 + j + ns ≤ W) (Q : Config → ℕ → Prop)
    (hpos : 0 < k → ∀ c₁ : Config, WordsBounded W c₁ → c₁.nmem = c.nmem →
      (∀ r, (r < 9437 ∨ 9439 < r) → c₁.nreg r = c.nreg r) → c₁.rreg = c.rreg →
      c₁.rmem = c.rmem → c₁.output = c.output → ∃ c' t, Exec I W (fxPos msP) c₁ c' t ∧ Q c' t)
    (hzero : k = 0 → ∀ c₁ : Config, WordsBounded W c₁ → c₁.nmem = c.nmem →
      (∀ r, (r < 9437 ∨ 9439 < r) → c₁.nreg r = c.nreg r) → c₁.rreg = c.rreg →
      c₁.rmem = c.rmem → c₁.output = c.output → ∃ c' t, Exec I W fxZero c₁ c' t ∧ Q c' t) :
    ∃ c' t s, Exec I W (fixC msP) c c' s ∧ s ≤ t + 9 ∧ Q c' t := by
  obtain ⟨c₁, t₁, e₁, ht₁, a37, a38, ak, am, ar, arm, ao⟩ :=
    kTst_exec (P := I) c hc r07 r00 hns hk hW
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · obtain ⟨c', t, e, hQ⟩ := hzero h0 c₁ e₁.wb_right am ak ar arm ao
    exact ⟨c', t, _, e₁.seq (.ifLtN_false (by clear * - a37 a38 h0; omega) e),
      by clear * - ht₁; omega, hQ⟩
  · obtain ⟨c', t, e, hQ⟩ := hpos h0 c₁ e₁.wb_right am ak ar arm ao
    exact ⟨c', t, _, e₁.seq (.ifLtN_true (by clear * - a37 a38 h0; omega) e),
      by clear * - ht₁; omega, hQ⟩

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M₀ : CombMap D V F} {e : V → D} {he : ∀ v, M₀.tail (e v) = v}
variable {en : ℕ → D} {en' : ℕ → D ⊕ (V × Bool)} {m m' Z' d d' : ℕ}
  {cap f₀ : D ⊕ (V × Bool) → ℤ} {segs : List (SPath M₀)} {lo hi Gb j : ℕ}

/-! ### The branch `0 < k` -/

set_option maxHeartbeats 16000000 in
/-- **The branch `0 < k` of the frozen fix.** -/
theorem fxPos_exec (C C₀ : ℕ) (hC : 200000 ≤ C) {msP : Stmt} {Scr : ℕ → Prop}
    {cost Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    (hMS : MsCall.MsspCallSpec M₀ msP Scr cost Rm wzm) (hScr : ∀ r, Scr r → r < 9300)
    (I : Input) {W Wz A0 : ℕ} (c : Config) (hc : WordsBounded W c)
    (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j c.nmem)
    (hk0 : 0 < (segs[j]'H.hj).k)
    (r04 : c.nreg 3004 = d') (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (r98 : c.nreg 9998 = d) (hz : ∀ a ≤ Wz, c.nmem a = 0)
    (hWzd : Wz < d) (hWzd' : Wz < d') (hWlo : Wz < lo)
    (hhi : hi ≤ A0) (hfr : d' + 4 + 7 * m' ≤ A0) (hfb : d + 4 + 3 * m ≤ A0)
    -- the bounds
    (hW1 : (cIn d' m' Gb segs j Z' c.nmem).Qb A0 + 15 * (cIn d' m' Gb segs j Z' c.nmem).k + 16 ≤ W)
    (hW2 : ∑ i ∈ range m', (cIn d' m' Gb segs j Z' c.nmem).FLW i +
      (cIn d' m' Gb segs j Z' c.nmem).AS +
      16 * fpB (cIn d' m' Gb segs j Z' c.nmem).AS m' (cIn d' m' Gb segs j Z' c.nmem).k +
      m' * Z' + Z' + (cIn d' m' Gb segs j Z' c.nmem).k + 16 ≤ W)
    (hl14 : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' c.nmem)
      ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).p + (mkP M₀ e he en' (segs[j]'H.hj) cap f₀
      (cIn d' m' Gb segs j Z' c.nmem) ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).LG ≤ W)
    (hw1 : 16 * (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' c.nmem)
      ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).K + 1 ≤ W)
    (hw2 : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' c.nmem)
      ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).Mo + 3 * (mkP M₀ e he en' (segs[j]'H.hj) cap f₀
      (cIn d' m' Gb segs j Z' c.nmem) ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).K ≤ W)
    (hwz : wzm m (2 * Z') ≤ Wz)
    (hSHz : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' c.nmem)
      ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).SH + (mkP M₀ e he en' (segs[j]'H.hj) cap f₀
      (cIn d' m' Gb segs j Z' c.nmem) ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).WN ≤ Wz)
    (hpw : lyP ((cIn d' m' Gb segs j Z' c.nmem).Qb A0 + 15 * (cIn d' m' Gb segs j Z' c.nmem).k)
      (cIn d' m' Gb segs j Z' c.nmem).cw.cnt (cIn d' m' Gb segs j Z' c.nmem).k +
      Rm m (cIn d' m' Gb segs j Z' c.nmem).k (cIn d' m' Gb segs j Z' c.nmem).cw.cnt ≤ W)
    (hKL : (cIn d' m' Gb segs j Z' c.nmem).K + 8 * fpB (cIn d' m' Gb segs j Z' c.nmem).AS m'
      (cIn d' m' Gb segs j Z' c.nmem).k + moOf (cIn d' m' Gb segs j Z' c.nmem).cw.cnt
      (8 * fpB (cIn d' m' Gb segs j Z' c.nmem).AS m' (cIn d' m' Gb segs j Z' c.nmem).k) ≤ W)
    (hSz : 9 * m + 1 + tsz m ≤ Wz + 1)
    (hWz : rtW m (rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' c.nmem)
        ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).st (segs[j]'H.hj).k).1 (.inl y))) m ≤ Wz)
    (hW : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' c.nmem)
      ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).p + 60 * m + 60 + negT C C₀ m ≤ W)
    (wL : 2 * (cIn d' m' Gb segs j Z' c.nmem).K + rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' c.nmem)
        ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).st (segs[j]'H.hj).k).1 (.inl y)) ≤ W)
    (hw2' : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' c.nmem)
        ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).st (segs[j]'H.hj).k).1 (.inl y))) ≤ W)
    (hv : Z' + Z' + 2 * (cIn d' m' Gb segs j Z' c.nmem).K + 2 * rtL M₀ (fun y => cap (.inl y) -
      ((mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' c.nmem)
        ((cIn d' m' Gb segs j Z' c.nmem).Qb A0)).st (segs[j]'H.hj).k).1 (.inl y)) ≤ W) :
    ∃ c' t, Exec I W (fxPos msP) c c' t ∧
      t ≤ posT9 C C₀ cost m m' (segs[j]'H.hj).k (cIn d' m' Gb segs j Z' c.nmem).cw.cnt ∧
      (∀ i < m', (c'.nmem (d' + 4 + 6 * m' + i) : ℤ) = Z' + fixPath (M₀.pendant e he) cap f₀
        ((segs[j]'H.hj).lift e he) (msspP (Klein.msspPlaneK M₀)) (frRef F)
        (negP (negMach (nsIds M₀ H.enum (en 0)) M₀ I)) (en' i)) ∧
      (∀ a < A0, (a < d' + 4 + 6 * m' ∨ d' + 4 + 7 * m' ≤ a) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧ (∀ r, NcStep.PKeep r → c'.nreg r = c.nreg r) ∧
      c'.output = c.output := by
  set q := cIn d' m' Gb segs j Z' c.nmem with hq
  have hpre := cIn_pre (d := d') (Z := Z') H.fr H.segsL' H.hj'
  rw [cIn_lift] at hpre
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ := hpre
  have htop1 : q.PDb + q.k ≤ hi := (cIn_top (d := d') (Z := Z') (m := m) H.sl H.hj).1
  have htop2 : Gb + 1 + j + segs.length < hi := (cIn_top (d := d') (Z := Z') (m := m) H.sl H.hj).2.1
  have htop3 : lo ≤ q.PDb := (cIn_top (d := d') (Z := Z') (m := m) H.sl H.hj).2.2
  have hkq : (segs[j]'H.hj).k = q.k := (pq_k H).symm
  have hk0' : 0 < q.k := hkq ▸ hk0
  have hmm := H.mm
  have hQe : q.Qb A0 = A0 + 9 * m' + 1 := by
    show A0 + m' + m' + m' + m' + 1 + m' + m' + m' + m' + m' = _; omega
  -- the prologue
  obtain ⟨c₁, t₁, e₁, ht₁, hO, k1, rr1, rm1, o1⟩ :=
    fpPro_execW (P := I) q c hc (j := j) r04 r06 r07 r00 (fun a _ => rfl) p1 p2 p3 p4 p5
      (show Gb + 1 + j + segs.length < A0 by omega) p6 p7 p8 p9 hk0' hfr
      (show q.PDb + q.k ≤ A0 by omega) hW1 hW2
  clear p1 p2 p3 p4 p5 p6 p7 p8 p9 hW1 hW2
  have hO' := hO
  obtain ⟨R1, a19, a20, a73, a22, a10, alo, aLAB, aBT, aCL, aW5, aET, aPW⟩ := hO'
  obtain ⟨g00, g03, g36, g21, g01, g71, g02, g30, g31, g34, g35, g04, g05, g06, g07, g08, g09,
    g10, g11, g74, g75, g76, g77, g12, g13, g14, g15, g16, g17, g18⟩ := R1
  clear g00 g03 g71 g31 g04 g06 g07 g08 g09 g10 g11 g74 g75 g76 g77 g12 g13 g14 g15 g16 g17 g18
    a19 a20 a73 a22 a10 aBT aCL aW5 aET aPW
  have alo' : ∀ a < A0, c₁.nmem a = c.nmem a := alo
  have hz1 : ∀ a ≤ Wz, c₁.nmem a = 0 := fun a ha => by rw [alo' a (by omega)]; exact hz a ha
  set X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0) with hX
  have hG : X.Good W := mkP_good H hk0 (lt_of_le_of_lt hSHz (by rw [hQe]; omega)) hl14 hw1 hw2
  -- step 2
  have r98' : c₁.nreg 9998 = d := by
    rw [k1 9998 (by unfold proScr scr1; omega) (by omega) (by omega) (by omega)]; exact r98
  obtain ⟨c₃, t₃, e₃, ht₃, hR, hFx, hS0, hImg, r69, r71, r74, r75, r00', r31', K3, hz3, m3, rr3,
      rm3, o3⟩ :=
    st9_exec H hMS hScr hk0 (I := I) hG c₁ e₁.wb_right hO r98' hhi hfr hfb hWzd hWzd' hWlo hz1
      hwz hSHz hpw hKL
  clear hl14 hw1 hw2 hpw hKL
  have nK : ∀ r, 9400 ≤ r → r ≤ 9438 → r ≠ 9419 → r ≠ 9420 → r ≠ 9422 → r ≠ 9400 → r ≠ 9431 →
      r ≠ 9410 → c₃.nreg r = c₁.nreg r := fun r h1 h2 h3 h4 h5 h6 h7 h8 =>
    K3 r (keepR_ge (by omega)) (by simp only [st2W]; omega) (by omega) (by omega) (by omega)
      (by omega) h6 h7 h8 (by omega)
  have m31 : ∀ a, Wz < a → a < A0 → c₃.nmem a = c.nmem a := fun a h1 h2 => by
    rw [m3 a h1 (by rw [hQe]; omega), alo' a h2]
  have H₃ : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j c₃.nmem :=
    H.congr hfr hfb hhi hWzd hWzd' hWlo m31
  have hNX : ∀ i < m', nxF d' m' c₃.nmem i = nxF d' m' c.nmem i := fun i hi => by
    unfold nxF
    have h1 := (H.fr.rv i hi).1
    rw [m31 (d' + 4 + m' + i) (by omega) (by omega), m31 _ (by omega) (by omega)]
  have hLAB3 : ∀ i < m, c₃.nmem (A0 + m' + i) = olab (nxF d' m' c₃.nmem) i + 1 := fun i hi => by
    rw [m3 _ (by omega) (by rw [hQe]; omega), show A0 + m' + i = A0 + q.m + i from rfl,
      aLAB i (by show i < m'; omega), olab_congr (f := nxF d' m' c₃.nmem) (g := nxF d' m' c.nmem) hNX
        H₃.fr.permOn_nx (by omega)]
    rfl
  have hPD9 : c₃.nreg 9402 = q.PDb := by
    rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), g02]
  have hPDm3 : ∀ l < (segs[j]'H.hj).k, c₃.nmem (c₃.nreg 9402 + l) < m ∧
      en (c₃.nmem (c₃.nreg 9402 + l)) = (segs[j]'H.hj).d l := fun l hl' => by
    rw [hPD9, m31 _ (by omega) (by omega)]
    have h := pq_pd H hl'
    exact ⟨h.1, h.2.1⟩
  have hPDz : Wz < c₃.nreg 9402 := by rw [hPD9]; omega
  have hcp : ∀ i < m, c₃.nmem (d' + 4 + 3 * m' + i) ≤ Z' := fun i hi => (H₃.fr.cp i (by omega)).2
  -- the stage loop and the final step
  obtain ⟨c₅, t₅, e₅, ht₅, F5, z5, k5, r5, rr5, rm5, o5⟩ :=
    fin9_exec C C₀ hC c₃ H₃ H.hj hG I I e₃.wb_right (LABb := A0 + m') (Wz := Wz) hPDm3 hR hFx hS0 hImg
      r69 r00'
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num), g36])
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num), g34]; show d' + 4 + m' + m' + m' = _; ring)
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num), g35]
          show d' + 4 + m' + m' + m' + m' + m' + m' = _; ring)
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num), g21]; rfl)
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num), g01]; exact hkq.symm)
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num), g30]; rfl)
      r31'
      (by rw [nK _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num), g05]; rfl)
      r75 r71 r74 hLAB3 hz3 hSHz hPDz hSz hWzd hWzd' hWlo
      ⟨by omega, by show A0 + m' + m ≤ q.Qb A0; rw [hQe]; omega,
        by rw [hPD9]; show q.PDb + (segs[j]'H.hj).k ≤ q.Qb A0; rw [hkq, hQe]; omega,
        by show d + 4 + 3 * m ≤ q.Qb A0; rw [hQe]; omega,
        by show hi ≤ q.Qb A0; rw [hQe]; omega⟩
      hWz hW (by exact wL) hw2' hw3
      (fun i hi => by
        have := hcp i hi
        show c₃.nmem (d' + 4 + 3 * m' + i) + Z' + q.K + q.K + 2 * rtL M₀ (fun y => cap (.inl y) -
          (X.st (segs[j]'H.hj).k).1 (.inl y)) ≤ W
        clear * - this hv; omega)
  refine ⟨c₅, _, e₁.seq (e₃.seq e₅), ?_, F5, fun a ha hn => ?_, z5, fun r hr => ?_,
    by rw [o5, o3, o1]⟩
  · have ht5' : t₅ ≤ loopT q.cw.cnt (segs[j]'H.hj).k + (20 * (q.cw.cnt * q.cw.cnt + q.cw.cnt +
        q.cw.cnt + 1 + 2 * (segs[j]'H.hj).k + 2 * (segs[j]'H.hj).k) + 32 +
        finT C C₀ m (segs[j]'H.hj).k) := ht₅
    have ht1' : t₁ ≤ 162 * m' + 103 * q.k + 180 := ht₁
    have ht3' : t₃ ≤ 6 + (16 * q.k + 3) + (cost m q.k q.cw.cnt + st2T q.cw.cnt q.k + 4) := ht₃
    unfold posT9
    rw [hkq] at ht5' ⊢
    clear * - ht1' ht3' ht5'
    omega
  · refine ⟨?_, by rw [rm5, rm3, rm1]⟩
    by_cases hw : a ≤ Wz
    · rw [z5 a hw, hz a hw]
    · rw [k5 a (by omega) (by show a < q.Qb A0; rw [hQe]; omega) hn, m31 a (by omega) ha]
  · unfold NcStep.PKeep at hr
    rw [r5 r (by unfold KeepR; omega) (by omega) (by unfold SLx.scr swScr FrFix.frScr; omega),
      K3 r (by unfold KeepR; omega) (by simp only [st2W]; omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega),
      k1 r (by unfold proScr scr1; omega) (by omega) (by omega) (by omega)]

end F9b

end BKMNW

end PlanarFlow
