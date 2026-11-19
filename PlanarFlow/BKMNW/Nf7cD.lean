module

public import PlanarFlow.BKMNW.Nf7cC

/-!
# Step 2 of `fixP` on the machine

**`st2 msP = st2ab msP ; st2c`** (`st2ab msP = st2a msP ; st2b`) and **`st2_exec`**: from the
prologue's registers and arrays (`ProOut`, given here by their values), under the
hypothesis `MsCall.MsspCallSpec M msP Scr cost room wz` (scratch registers off `KeepR`):

1. the MSSP call along the path `P` with the lengths `ℓ` (array `Lb`) and the `b` query darts
   `ts` (array `Qb`): the matrix `Dm i j = msW M P ℓ (ts i) (ts j)` at `lyOm`;
2. the FR image of `img0 b Dm ET EH k = frPrm b Dm 0 0 ET EH 0 (2k)` written once at the staging
   base `lyA` (`frImg`), copied into the zero area below `Wz`: `frNM` at `[0, sb)` and at
   `[SH, SH + sb)`, `frRS` at `[Wf + 1, Wf + 1 + sb)` and at `[SH + Wf + 1, …)` (`ImgAt`), the
   rest of `[0, Wz]` zero (`ZeroAt`);
3. the sorted arc indices `sIdx ET (2k) b e` at `lySI + e` and the registers of the stage loop.

Within **`cost m k b + st2T b k`** steps, `st2T b k = 30 b² + 132 b + 270 k + 28 lySb + 530`.
(Split in `st2ab_exec` (phases a, b) and `st2_exec`, to keep each proof small in memory.)
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- Phases a and b of step 2. -/
def st2ab (msP : Stmt) : Stmt := .seq (st2a msP) st2b

/-- **Step 2 of `fixP`.** -/
def st2 (msP : Stmt) : Stmt := .seq (st2ab msP) st2c

/-- The registers written by step 2 among those of `KeepR`. -/
def st2W (r : ℕ) : Prop :=
  (9460 ≤ r ∧ r ≤ 9476) ∨ (9501 ≤ r ∧ r ≤ 9504) ∨ (9360 ≤ r ∧ r ≤ 9362) ∨
    (9600 ≤ r ∧ r ≤ 9632)

/-- The step bound of step 2 (without the MSSP call). -/
def st2T (b k : ℕ) : ℕ := 30 * (b * b) + 132 * b + 270 * k + 28 * lySb b k + 530

lemma keepR_ge {r : ℕ} (h : 9300 ≤ r) : KeepR r := Or.inr (Or.inr h)

/-- The image facts of step 2 (live and shadow). -/
def ImgAt (nm : ℕ → ℕ) (X : Monge.FR.Prm) (L sb wf sh : ℕ) : Prop :=
  ∀ a < sb, nm a = FrFix.frNM X a ∧ nm (sh + a) = FrFix.frNM X a ∧
    nm (wf + 1 + a) = FrFix.frRS X L a ∧ nm (sh + (wf + 1) + a) = FrFix.frRS X L a

/-- The rest of the zero area below `Wz`. -/
def ZeroAt (nm : ℕ → ℕ) (Wz sb wf sh : ℕ) : Prop :=
  ∀ a ≤ Wz, ¬ a < sb → ¬ (sh ≤ a ∧ a < sh + sb) → ¬ (wf + 1 ≤ a ∧ a < wf + 1 + sb) →
    ¬ (sh + (wf + 1) ≤ a ∧ a < sh + (wf + 1) + sb) → nm a = 0

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

set_option maxHeartbeats 2000000 in
/-- **Phases a and b of step 2**: the MSSP call and the FR image written once. -/
theorem st2ab_exec (M : CombMap D V F) {msP : Stmt} {Scr : ℕ → Prop}
    {cost room : ℕ → ℕ → ℕ → ℕ} {wz : ℕ → ℕ → ℕ}
    (hMS : MsCall.MsspCallSpec M msP Scr cost room wz) (hScr : ∀ r, Scr r → r < 9300)
    (hpl : M.IsPlane) (hrot : M.RotTrans)
    {en : ℕ → D} {m : ℕ} {P : SPath M} {ℓ : D → ℤ} {Lmax b : ℕ} {ts : ℕ → D}
    {RVb RTb Pb Lb Qb S1 PRb ETb EHb ELb K L Wz W : ℕ} {ET EH : ℕ → ℕ} {Dm : ℕ → ℕ → ℕ}
    {I : Input} (c : Config) (hc : WordsBounded W c)
    (henum : NsStep.EnumOK M en m) (hk : 0 < P.k) (hℓ : ∀ e, 0 ≤ ℓ e)
    (hts : ∀ i < b, M.face (ts i) ∈ P.faces)
    (hDm : ∀ i < b, ∀ j < b, MsCall.msW M P ℓ (ts i) (ts j) = Dm i j)
    (r18 : c.nreg 9418 = S1) (r19 : c.nreg 9419 = b) (r01 : c.nreg 9401 = P.k)
    (r36 : c.nreg 9436 = 1) (r00 : c.nreg 9400 = m) (r30 : c.nreg 9430 = RVb)
    (r31 : c.nreg 9431 = RTb) (r02 : c.nreg 9402 = Pb) (r09 : c.nreg 9409 = Lb)
    (r10 : c.nreg 9410 = Qb) (r17 : c.nreg 9417 = PRb) (r14 : c.nreg 9414 = ETb)
    (r15 : c.nreg 9415 = EHb) (r77 : c.nreg 9377 = ELb) (r9310 : c.nreg 9310 = K)
    (r22 : c.nreg 9422 = L)
    (hrv : ∀ i < m, c.nmem (RVb + i) < m ∧ en (c.nmem (RVb + i)) = M.rev (en i))
    (hrt : ∀ i < m, c.nmem (RTb + i) < m ∧ en (c.nmem (RTb + i)) = M.rot (en i))
    (hpd : ∀ j < P.k, c.nmem (Pb + j) < m ∧ en (c.nmem (Pb + j)) = P.d j)
    (hln : ∀ i < m, (c.nmem (Lb + i) : ℤ) = ℓ (en i) ∧ c.nmem (Lb + i) ≤ Lmax)
    (hqd : ∀ i < b, c.nmem (Qb + i) < m ∧ en (c.nmem (Qb + i)) = ts i)
    (hpr : ∀ x < b, c.nmem (PRb + x) = K) (het : ∀ a < 2 * P.k, c.nmem (ETb + a) = ET a)
    (heh : ∀ a < 2 * P.k, c.nmem (EHb + a) = EH a) (hel : ∀ a < 2 * P.k, c.nmem (ELb + a) = K)
    (hpla : MsCall.MsPlace m P.k b Wz W RVb RTb Pb Lb Qb (lyOm S1 b P.k) (lyP S1 b P.k)
      (room m P.k b))
    (hS1 : Wz < S1) (hPR : PRb + b ≤ S1) (hET : ETb + 2 * P.k ≤ S1) (hEH : EHb + 2 * P.k ≤ S1)
    (hEL : ELb + 2 * P.k ≤ S1) (hzA : Wz < PRb ∧ Wz < ETb ∧ Wz < EHb ∧ Wz < ELb)
    (hB : MsCall.FrImgB b Dm (fun _ => 0) 0 (2 * P.k) ET EH (fun _ => 0) L)
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hwz : wz m Lmax ≤ Wz)
    (hlow : shOf b P.k L + (wfOf b P.k + 1) + lySb b P.k ≤ Wz + 1)
    (hKL : K + L + moOf b L ≤ W) :
    ∃ c' t, Exec I W (st2ab msP) c c' t ∧
      t ≤ cost m P.k b + 104 + (30 * (b * b) + 100 * b + 200 * P.k + 28 * lySb b P.k + 350) ∧
      c'.nreg 9460 = S1 ∧ c'.nreg 9461 = b * b ∧ c'.nreg 9468 = lyOb S1 b P.k ∧
      c'.nreg 9469 = lyP S1 b P.k ∧ c'.nreg 9470 = lySI S1 b P.k ∧
      c'.nreg 7600 = b ∧ c'.nreg 7601 = b ∧ c'.nreg 7602 = 0 ∧ c'.nreg 7603 = b * b ∧
      c'.nreg 7604 = b * b + b ∧ c'.nreg 7605 = b * b + b + b + 1 + 2 * P.k ∧
      c'.nreg 7607 = lySb b P.k ∧ c'.nreg 7608 = lySb b P.k + b ∧
      c'.nreg 7609 = lySb b P.k + b + b ∧ c'.nreg 7610 = moOf b L ∧
      c'.nreg 7611 = 6 * ((b + 2) * L) ∧ c'.nreg 7612 = wfOf b P.k + 1 ∧
      c'.nreg 9471 = shOf b P.k L ∧ c'.nreg 9474 = shOf b P.k L + (wfOf b P.k + 1) ∧
      c'.nreg 8100 = b ∧ c'.nreg 8102 = PRb ∧ c'.nreg 8104 = 2 * P.k ∧ c'.nreg 8105 = ETb ∧
      c'.nreg 8107 = ELb ∧
      (∀ r, KeepR r → (r < 9460 ∨ 9475 < r) → (r < 9600 ∨ 9632 < r) → c'.nreg r = c.nreg r) ∧
      ImgAt c'.nmem (img0 b Dm ET EH P.k) L (lySb b P.k) (wfOf b P.k) (shOf b P.k L) ∧
      ZeroAt c'.nmem Wz (lySb b P.k) (wfOf b P.k) (shOf b P.k L) ∧
      (∀ a, Wz < a → a < S1 → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hT : lyT b P.k = 4 * P.k + 4 * b + 2 := rfl
  have hOm : lyOm S1 b P.k = S1 + lyT b P.k := rfl
  have hAe : lyA S1 b P.k = lyOm S1 b P.k + b * b := rfl
  have hSe : lyS S1 b P.k = lyA S1 b P.k + lySb b P.k + lySb b P.k := rfl
  have hObe : lyOb S1 b P.k = lyS S1 b P.k + lyT b P.k := rfl
  have hPe : lyP S1 b P.k = lyOb S1 b P.k + b + b := rfl
  have hpW : lyP S1 b P.k ≤ W := by have := hpla.pw; omega
  obtain ⟨c₁, t₁, e₁, ht₁, a60, a61, a62, a63, a64, a65, a66, a67, a68, a69, a70, az, aO, am,
      ak, ar, arm, ao⟩ :=
    st2a_exec (I := I) M hMS hScr hpl hrot c hc henum hk hℓ hts r18 r19 r01 r36 r00 r30 r31 r02
      r09 r10 hrv hrt hpd hln hqd hpla hz hwz
  clear hrv hrt hpd hln hqd hMS hScr henum hℓ hwz hz hpla r00 r30 r31 r02 r09 r10 r36 r18
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hzA
  have aO' : ∀ i < b, ∀ j < b, c₁.nmem (lyOm S1 b P.k + i * b + j) = Dm i j := fun i hi j hj =>
    (aO i hi j hj).trans (hDm i hi j hj)
  clear aO hDm hts
  have k1 : ∀ r, KeepR r → (r < 9460 ∨ 9470 < r) → (r < 9600 ∨ 9632 < r) →
      c₁.nreg r = c.nreg r := ak
  have m1 : ∀ a, Wz < a → a < lyOm S1 b P.k → c₁.nmem a = c.nmem a := fun a h1 h2 =>
    am a h1 (Or.inl h2) (Or.inl (by clear * - h2 hPe hObe hSe hAe; omega))
  clear am ak
  have hS1A : S1 < lyOm S1 b P.k := by rw [hOm, hT]; omega
  have hlowA : shOf b P.k L + (wfOf b P.k + 1) + lySb b P.k ≤ lyA S1 b P.k := by
    clear * - hlow hS1 hS1A hAe; omega
  have hObW : lyOb S1 b P.k ≤ W := by clear * - hpW hPe; omega
  have hSHW : shOf b P.k L + (wfOf b P.k + 1) ≤ W := by
    clear * - hlowA hObW hObe hSe; omega
  obtain ⟨c₂, t₂, e₂, ht₂, b00, b01, b02, b03, b04, b05, b07, b08, b09, b10, b11, b12, b71, b74,
      q00, q02, q04, q05, q07, bI, bK, bk, br, brm, bo⟩ :=
    st2b_exec (P := I) c₁ e₁.wb_right (S1 := S1) (Dm := Dm)
      (by rw [k1 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num), r19]) a64
      (by rw [k1 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num), r17]) a62
      (by rw [k1 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num), r14])
      (by rw [k1 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num), r15])
      (by rw [k1 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num), r77])
      (by rw [k1 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num), r9310])
      (by rw [k1 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num), r22]) a66 a67 hB aO'
      (fun x hx => by rw [m1 _ (by clear * - hz1 hx; omega)
        (by clear * - hPR hx hS1A; omega)]; exact hpr x hx)
      (fun a ha => by rw [m1 _ (by clear * - hz2 ha; omega)
        (by clear * - hET ha hS1A; omega)]; exact het a ha)
      (fun a ha => by rw [m1 _ (by clear * - hz3 ha; omega)
        (by clear * - hEH ha hS1A; omega)]; exact heh a ha)
      (fun a ha => by rw [m1 _ (by clear * - hz4 ha; omega)
        (by clear * - hEL ha hS1A; omega)]; exact hel a ha)
      (by clear * - hPR hS1A hAe; omega) (by clear * - hET hS1A hAe; omega)
      (by clear * - hEH hS1A hAe; omega) (by clear * - hEL hS1A hAe; omega) hlowA hObW hKL
      (by have := lySb_le_wfOf b P.k; unfold shOf at hSHW; clear * - hSHW this; omega) hSHW
  refine ⟨c₂, _, e₁.seq e₂, by clear * - ht₁ ht₂; omega,
    by rw [bk _ (keepR_ge (by norm_num)) (by norm_num), a60],
    by rw [bk _ (keepR_ge (by norm_num)) (by norm_num), a61],
    by rw [bk _ (keepR_ge (by norm_num)) (by norm_num), a68],
    by rw [bk _ (keepR_ge (by norm_num)) (by norm_num), a69],
    by rw [bk _ (keepR_ge (by norm_num)) (by norm_num), a70],
    b00, b01, b02, b03, b04, b05, b07, b08, b09, b10, b11, b12, b71, b74, q00, q02, q04, q05, q07,
    fun r hr h2 h3 => by rw [bk r hr (by clear * - h2; omega), k1 r hr (by clear * - h2; omega) h3],
    fun a ha => bI a ha, fun a ha n1 n2 n3 n4 => ?_, fun a h1 h2 => ?_, by rw [br, ar],
    by rw [brm, arm], by rw [bo, ao]⟩
  · rw [bK a n1 n2 n3 n4 (Or.inl (by clear * - ha hS1 hS1A hAe; omega))]
    exact az a ha
  · rw [bK a (by clear * - h1 hlow; omega) (by clear * - h1 hlow; omega)
      (by clear * - h1 hlow; omega) (by clear * - h1 hlow; omega)
      (Or.inl (by clear * - h2 hS1A hAe; omega)), m1 a h1 (by clear * - h2 hS1A; omega)]

set_option maxHeartbeats 2000000 in
/-- **Step 2 of `fixP` on the machine.** -/
theorem st2_exec (M : CombMap D V F) {msP : Stmt} {Scr : ℕ → Prop}
    {cost room : ℕ → ℕ → ℕ → ℕ} {wz : ℕ → ℕ → ℕ}
    (hMS : MsCall.MsspCallSpec M msP Scr cost room wz) (hScr : ∀ r, Scr r → r < 9300)
    (hpl : M.IsPlane) (hrot : M.RotTrans)
    {en : ℕ → D} {m : ℕ} {P : SPath M} {ℓ : D → ℤ} {Lmax b : ℕ} {ts : ℕ → D}
    {RVb RTb Pb Lb Qb S1 PRb ETb EHb ELb K L Wz W : ℕ} {ET EH : ℕ → ℕ} {Dm : ℕ → ℕ → ℕ}
    {I : Input} (c : Config) (hc : WordsBounded W c)
    (henum : NsStep.EnumOK M en m) (hk : 0 < P.k) (hℓ : ∀ e, 0 ≤ ℓ e)
    (hts : ∀ i < b, M.face (ts i) ∈ P.faces)
    (hDm : ∀ i < b, ∀ j < b, MsCall.msW M P ℓ (ts i) (ts j) = Dm i j)
    (r18 : c.nreg 9418 = S1) (r19 : c.nreg 9419 = b) (r01 : c.nreg 9401 = P.k)
    (r36 : c.nreg 9436 = 1) (r00 : c.nreg 9400 = m) (r30 : c.nreg 9430 = RVb)
    (r31 : c.nreg 9431 = RTb) (r02 : c.nreg 9402 = Pb) (r09 : c.nreg 9409 = Lb)
    (r10 : c.nreg 9410 = Qb) (r17 : c.nreg 9417 = PRb) (r14 : c.nreg 9414 = ETb)
    (r15 : c.nreg 9415 = EHb) (r77 : c.nreg 9377 = ELb) (r9310 : c.nreg 9310 = K)
    (r22 : c.nreg 9422 = L)
    (hrv : ∀ i < m, c.nmem (RVb + i) < m ∧ en (c.nmem (RVb + i)) = M.rev (en i))
    (hrt : ∀ i < m, c.nmem (RTb + i) < m ∧ en (c.nmem (RTb + i)) = M.rot (en i))
    (hpd : ∀ j < P.k, c.nmem (Pb + j) < m ∧ en (c.nmem (Pb + j)) = P.d j)
    (hln : ∀ i < m, (c.nmem (Lb + i) : ℤ) = ℓ (en i) ∧ c.nmem (Lb + i) ≤ Lmax)
    (hqd : ∀ i < b, c.nmem (Qb + i) < m ∧ en (c.nmem (Qb + i)) = ts i)
    (hpr : ∀ x < b, c.nmem (PRb + x) = K) (het : ∀ a < 2 * P.k, c.nmem (ETb + a) = ET a)
    (heh : ∀ a < 2 * P.k, c.nmem (EHb + a) = EH a) (hel : ∀ a < 2 * P.k, c.nmem (ELb + a) = K)
    (hpla : MsCall.MsPlace m P.k b Wz W RVb RTb Pb Lb Qb (lyOm S1 b P.k) (lyP S1 b P.k)
      (room m P.k b))
    (hS1 : Wz < S1) (hPR : PRb + b ≤ S1) (hET : ETb + 2 * P.k ≤ S1) (hEH : EHb + 2 * P.k ≤ S1)
    (hEL : ELb + 2 * P.k ≤ S1) (hzA : Wz < PRb ∧ Wz < ETb ∧ Wz < EHb ∧ Wz < ELb)
    (hB : MsCall.FrImgB b Dm (fun _ => 0) 0 (2 * P.k) ET EH (fun _ => 0) L)
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hwz : wz m Lmax ≤ Wz)
    (hlow : shOf b P.k L + (wfOf b P.k + 1) + lySb b P.k ≤ Wz + 1)
    (hKL : K + L + moOf b L ≤ W) :
    ∃ c' t, Exec I W (st2 msP) c c' t ∧ t ≤ cost m P.k b + st2T b P.k ∧
      -- the registers of the stage loop
      c'.nreg 9501 = c.nreg 9416 ∧ c'.nreg 9502 = c.nreg 9412 ∧ c'.nreg 9503 = c.nreg 9413 ∧
      c'.nreg 9504 = ETb ∧ c'.nreg 8100 = b ∧ c'.nreg 9360 = wfOf b P.k + 1 ∧
      c'.nreg 9361 = shOf b P.k L + (wfOf b P.k + 1) ∧ c'.nreg 8113 = b * b ∧
      c'.nreg 8102 = PRb ∧ c'.nreg 8125 = moOf b L - K % moOf b L ∧ c'.nreg 8124 = moOf b L ∧
      c'.nreg 8112 = 1 ∧ c'.nreg 8104 = 2 * P.k ∧
      c'.nreg 8115 = b * b + b + b + 1 + 2 * P.k ∧ c'.nreg 9362 = lySI S1 b P.k ∧
      c'.nreg 8107 = ELb ∧
      c'.nreg 7600 = b ∧ c'.nreg 7601 = b ∧ c'.nreg 7602 = 0 ∧ c'.nreg 7603 = b * b ∧
      c'.nreg 7604 = b * b + b ∧ c'.nreg 7605 = b * b + b + b + 1 + 2 * P.k ∧
      c'.nreg 7607 = lySb b P.k ∧ c'.nreg 7608 = lySb b P.k + b ∧
      c'.nreg 7609 = lySb b P.k + b + b ∧ c'.nreg 7610 = moOf b L ∧
      c'.nreg 7611 = 6 * ((b + 2) * L) ∧ c'.nreg 7612 = wfOf b P.k + 1 ∧
      c'.nreg 7614 = lyOb S1 b P.k ∧ c'.nreg 7615 = lyP S1 b P.k ∧
      c'.nreg 7616 = shOf b P.k L ∧
      (∀ r, KeepR r → ¬ st2W r → c'.nreg r = c.nreg r) ∧
      -- the resident image and its shadow, the rest of the zero area
      ImgAt c'.nmem (img0 b Dm ET EH P.k) L (lySb b P.k) (wfOf b P.k) (shOf b P.k L) ∧
      ZeroAt c'.nmem Wz (lySb b P.k) (wfOf b P.k) (shOf b P.k L) ∧
      -- the sorted indices, the memory kept
      (∀ e < 2 * P.k, c'.nmem (lySI S1 b P.k + e) = MsCall.sIdx ET (2 * P.k) b e) ∧
      (∀ a, Wz < a → a < S1 → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hMo : 0 < moOf b L := by unfold moOf; omega
  have hT : lyT b P.k = 4 * P.k + 4 * b + 2 := rfl
  have hOm : lyOm S1 b P.k = S1 + lyT b P.k := rfl
  have hAe : lyA S1 b P.k = lyOm S1 b P.k + b * b := rfl
  have hSe : lyS S1 b P.k = lyA S1 b P.k + lySb b P.k + lySb b P.k := rfl
  have hObe : lyOb S1 b P.k = lyS S1 b P.k + lyT b P.k := rfl
  have hPe : lyP S1 b P.k = lyOb S1 b P.k + b + b := rfl
  have hpW : lyP S1 b P.k ≤ W := by have := hpla.pw; omega
  obtain ⟨c₂, t₂, e₂, ht₂, a60, a61, a68, a69, a70, b00, b01, b02, b03, b04, b05, b07, b08, b09,
      b10, b11, b12, b71, b74, q00, q02, q04, q05, q07, k2, bI, bZ, bK, br, brm, bo⟩ :=
    st2ab_exec (I := I) M hMS hScr hpl hrot c hc henum hk hℓ hts hDm r18 r19 r01 r36 r00 r30 r31
      r02 r09 r10 r17 r14 r15 r77 r9310 r22 hrv hrt hpd hln hqd hpr het heh hel hpla hS1 hPR hET
      hEH hEL hzA hB hz hwz hlow hKL
  obtain ⟨hz1, hz2, hz3, hz4⟩ := hzA
  clear hrv hrt hpd hln hqd hMS hScr henum hℓ hwz hz hpla r00 r30 r31 r02 r09 r10 r36 r18 hts
    hDm heh hel hpr
  obtain ⟨c₃, t₃, e₃, ht₃, cSI, cK, c01, c02, c03, c04, c60, c61, c13, c24, c25, c12, c15, c62,
      c714, c715, c716, ck, cr, crm, co⟩ :=
    st2c_exec (P := I) c₂ e₂.wb_right (S1 := S1) (ET := ET) (K := K) a60 q00 q04 q05
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num), r9310]) b10 hMo
      (fun a ha => (bK _ (by clear * - hz2 ha; omega) (by clear * - hET ha; omega)).trans
        (het a ha)) hB.et hET (by clear * - hpW hPe hObe hSe hAe hOm; omega)
  have k3 : ∀ r, ¬ st2cScr r → c₃.nreg r = c₂.nreg r := ck
  clear ck
  have nS : ∀ r, (7600 ≤ r ∧ r ≤ 7612) ∨ r = 8100 ∨ r = 8102 ∨ r = 8104 ∨ r = 8107 →
      c₃.nreg r = c₂.nreg r := fun r hr => k3 r (by simp only [st2cScr]; clear * - hr; omega)
  have hS1W : ∀ x, x ≤ Wz → x < S1 := fun x hx => by clear * - hx hS1; omega
  refine ⟨c₃, _, e₂.seq e₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, cSI,
    ?_, by rw [cr, br], by rw [crm, brm], by rw [co, bo]⟩
  · unfold st2T; clear * - ht₂ ht₃; omega
  · rw [c01, k2 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num)]
  · rw [c02, k2 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num)]
  · rw [c03, k2 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num)]
  · rw [c04, k2 _ (keepR_ge (by norm_num)) (by norm_num) (by norm_num), r14]
  · rw [nS _ (by norm_num), q00]
  · rw [c60, b12]
  · rw [c61, b74]
  · rw [c13, a61]
  · rw [nS _ (by norm_num), q02]
  · exact c25
  · exact c24
  · exact c12
  · rw [nS _ (by norm_num), q04]
  · rw [c15, b05]
  · rw [c62, a70]
  · rw [nS _ (by norm_num), q07]
  · rw [nS _ (by norm_num), b00]
  · rw [nS _ (by norm_num), b01]
  · rw [nS _ (by norm_num), b02]
  · rw [nS _ (by norm_num), b03]
  · rw [nS _ (by norm_num), b04]
  · rw [nS _ (by norm_num), b05]
  · rw [nS _ (by norm_num), b07]
  · rw [nS _ (by norm_num), b08]
  · rw [nS _ (by norm_num), b09]
  · rw [nS _ (by norm_num), b10]
  · rw [nS _ (by norm_num), b11]
  · rw [nS _ (by norm_num), b12]
  · rw [c714, a68]
  · rw [c715, a69]
  · rw [c716, b71]
  · intro r hr hw
    simp only [st2W, not_or, not_and, not_le] at hw
    have hr' := hr
    unfold KeepR at hr'
    rw [k3 r (by simp only [st2cScr]; clear * - hr' hw; omega), k2 r hr (by clear * - hw; omega) (by clear * - hw; omega)]
  · intro a ha
    obtain ⟨i1, i2, i3, i4⟩ := bI a ha
    have hsh1 : wfOf b P.k + 1 + lySb b P.k ≤ shOf b P.k L := by
      have := lySb_le_wfOf b P.k; unfold shOf; clear * - this; omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [cK _ (Or.inl (hS1W _ (by clear * - ha hlow; omega))), i1]
    · rw [cK _ (Or.inl (hS1W _ (by clear * - ha hlow; omega))), i2]
    · rw [cK _ (Or.inl (hS1W _ (by clear * - ha hlow hsh1; omega))), i3]
    · rw [cK _ (Or.inl (hS1W _ (by clear * - ha hlow; omega))), i4]
  · intro a ha n1 n2 n3 n4
    rw [cK _ (Or.inl (hS1W _ ha))]
    exact bZ a ha n1 n2 n3 n4
  · intro a h1 h2
    rw [cK _ (Or.inl h2), bK a h1 h2]

end BKMNW

end PlanarFlow
