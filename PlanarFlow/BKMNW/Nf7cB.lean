module

public import PlanarFlow.BKMNW.Nf7cA

/-!
# Step 2 of `fixP`: the three phases on the machine

* **`st2a msP = p7cA ; p7cM ; msP`** and **`st2a_exec`**: the layout and the MSSP call, under the
  hypothesis `MsCall.MsspCallSpec M msP Scr cost room wz` (the MSSP call program), with the
  scratch registers `Scr` of `msP` off the kept registers `KeepR` (the driver's `3000 … 3012`,
  `6800 … 6819` and everything from `9300` on): within `cost m k b + 37` steps, the answers
  `msW M P ℓ (ts i) (ts j)` at `lyOm + i b + j`;
* **`st2b = p7cB ; frImg ; p7cC ; p7cK … (four copies)`** and **`st2b_exec`**: the FR image of the
  input `frPrm b Dm 0 0 ET EH 0 (2k)` written at the staging base `lyA` (`frImg_spec`), then
  copied to `[0, sb)`, `[Wf + 1, Wf + 1 + sb)` (live) and `SH + …` (shadow), with
  `SH = 2 (Wf + 1) + Mo² + Mo`;
* **`st2c = p7cD ; fiO ; fiS ; p7cE`** and **`st2c_exec`**: the sorted arc indices at `lySI` and
  the registers of the stage loop.
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

/-- **The registers every phase of `fixP` keeps**: the driver's (`3000 … 3012`, `6800 … 6819`)
and every register from `9300` on (the layout of `fixP`), except the scratch of each phase. -/
def KeepR (r : ℕ) : Prop := (3000 ≤ r ∧ r ≤ 3012) ∨ (6800 ≤ r ∧ r ≤ 6819) ∨ 9300 ≤ r

lemma keepR_ge' {r : ℕ} (h : 9300 ≤ r) : KeepR r := Or.inr (Or.inr h)

/-! ### Phase a: the layout and the MSSP call -/

/-- The layout and the MSSP call. -/
def st2a (msP : Stmt) : Stmt := .seq p7cA (.seq p7cM (.seq p7cSv (.seq msP p7cRs)))

section A

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The layout and the MSSP call.** -/
theorem st2a_exec (M : CombMap D V F) {msP : Stmt} {Scr : ℕ → Prop}
    {cost room : ℕ → ℕ → ℕ → ℕ} {wz : ℕ → ℕ → ℕ}
    (hMS : MsCall.MsspCallSpec M msP Scr cost room wz) (hScr : ∀ r, Scr r → r < 9300)
    (hpl : M.IsPlane) (hrot : M.RotTrans)
    {en : ℕ → D} {m : ℕ} {P : SPath M} {ℓ : D → ℤ} {Lmax b : ℕ} {ts : ℕ → D}
    {RVb RTb Pb Lb Qb S1 Wz W : ℕ} {I : Input} (c : Config) (hc : WordsBounded W c)
    (henum : NsStep.EnumOK M en m) (hk : 0 < P.k) (hℓ : ∀ e, 0 ≤ ℓ e)
    (hts : ∀ i < b, M.face (ts i) ∈ P.faces)
    (r18 : c.nreg 9418 = S1) (r19 : c.nreg 9419 = b) (r01 : c.nreg 9401 = P.k)
    (r36 : c.nreg 9436 = 1) (r00 : c.nreg 9400 = m) (r30 : c.nreg 9430 = RVb)
    (r31 : c.nreg 9431 = RTb) (r02 : c.nreg 9402 = Pb) (r09 : c.nreg 9409 = Lb)
    (r10 : c.nreg 9410 = Qb)
    (hrv : ∀ i < m, c.nmem (RVb + i) < m ∧ en (c.nmem (RVb + i)) = M.rev (en i))
    (hrt : ∀ i < m, c.nmem (RTb + i) < m ∧ en (c.nmem (RTb + i)) = M.rot (en i))
    (hpd : ∀ j < P.k, c.nmem (Pb + j) < m ∧ en (c.nmem (Pb + j)) = P.d j)
    (hln : ∀ i < m, (c.nmem (Lb + i) : ℤ) = ℓ (en i) ∧ c.nmem (Lb + i) ≤ Lmax)
    (hqd : ∀ i < b, c.nmem (Qb + i) < m ∧ en (c.nmem (Qb + i)) = ts i)
    (hpla : MsCall.MsPlace m P.k b Wz W RVb RTb Pb Lb Qb (lyOm S1 b P.k) (lyP S1 b P.k)
      (room m P.k b))
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hwz : wz m Lmax ≤ Wz) :
    ∃ c' t, Exec I W (st2a msP) c c' t ∧ t ≤ cost m P.k b + 104 ∧
      c'.nreg 9460 = S1 ∧ c'.nreg 9461 = b * b ∧ c'.nreg 9462 = 2 * P.k ∧
      c'.nreg 9463 = lyT b P.k ∧ c'.nreg 9464 = lyOm S1 b P.k ∧ c'.nreg 9465 = lySb b P.k ∧
      c'.nreg 9466 = lyA S1 b P.k ∧ c'.nreg 9467 = lyS S1 b P.k ∧
      c'.nreg 9468 = lyOb S1 b P.k ∧ c'.nreg 9469 = lyP S1 b P.k ∧
      c'.nreg 9470 = lySI S1 b P.k ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∀ i < b, ∀ j < b, c'.nmem (lyOm S1 b P.k + i * b + j) = MsCall.msW M P ℓ (ts i) (ts j)) ∧
      (∀ a, Wz < a → (a < lyOm S1 b P.k ∨ lyOm S1 b P.k + b * b ≤ a) →
        (a < lyP S1 b P.k ∨ lyP S1 b P.k + room m P.k b ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, KeepR r → (r < 9460 ∨ 9470 < r) → (r < 9600 ∨ 9632 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hpW : lyP S1 b P.k ≤ W := by have := hpla.pw; omega
  obtain ⟨c₁, t₁, e₁, ht₁, a60, a61, a62, a63, a64, a65, a66, a67, a68, a69, a70, ak, am, ar,
      arm, ao⟩ := p7cA_exec (P := I) c hc r18 r19 r01 r36 hpW
  obtain ⟨c₂, t₂, e₂, ht₂, b00, b01, b02, b03, b04, b05, b06, b07, b08, b09, bk, bm, br, brm,
      bo⟩ := p7cM_exec (P := I) c₁ e₁.wb_right
  have k1 : ∀ r, (r < 9460 ∨ 9470 < r) → c₁.nreg r = c.nreg r := ak
  have hIn : MsCall.MsIn M en m P ℓ Lmax b ts RVb RTb Pb Lb Qb (lyOm S1 b P.k) (lyP S1 b P.k)
      c₂ :=
    { r00 := by rw [b00, k1 _ (by omega), r00]
      r01 := by rw [b01, k1 _ (by omega), r30]
      r02 := by rw [b02, k1 _ (by omega), r31]
      r03 := by rw [b03, k1 _ (by omega), r01]
      r04 := by rw [b04, k1 _ (by omega), r02]
      r05 := by rw [b05, k1 _ (by omega), r09]
      r06 := by rw [b06, k1 _ (by omega), r19]
      r07 := by rw [b07, k1 _ (by omega), r10]
      r08 := by rw [b08, a64]
      r09 := by rw [b09, a69]
      rv := fun i hi => by rw [bm, am]; exact hrv i hi
      rt := fun i hi => by rw [bm, am]; exact hrt i hi
      pd := fun j hj => by rw [bm, am]; exact hpd j hj
      ln := fun i hi => by rw [bm, am]; exact hln i hi
      qd := fun i hi => by rw [bm, am]; exact hqd i hi }
  obtain ⟨c₂', t₂', e₂', ht₂', sA, sB, sk, sm, sr, srm, so⟩ := p7cSv_exec (P := I) c₂ e₂.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, cz, cO, ck, cn, cr, crm, co⟩ :=
    hMS hpl hrot en m P ℓ Lmax b ts RVb RTb Pb Lb Qb (lyOm S1 b P.k) (lyP S1 b P.k) Wz W I c₂'
      henum hk hℓ hts e₂'.wb_right
      { hIn with
        r00 := by rw [sk _ (by norm_num)]; exact hIn.r00
        r01 := by rw [sk _ (by norm_num)]; exact hIn.r01
        r02 := by rw [sk _ (by norm_num)]; exact hIn.r02
        r03 := by rw [sk _ (by norm_num)]; exact hIn.r03
        r04 := by rw [sk _ (by norm_num)]; exact hIn.r04
        r05 := by rw [sk _ (by norm_num)]; exact hIn.r05
        r06 := by rw [sk _ (by norm_num)]; exact hIn.r06
        r07 := by rw [sk _ (by norm_num)]; exact hIn.r07
        r08 := by rw [sk _ (by norm_num)]; exact hIn.r08
        r09 := by rw [sk _ (by norm_num)]; exact hIn.r09
        rv := fun i hi => by rw [sm]; exact hIn.rv i hi
        rt := fun i hi => by rw [sm]; exact hIn.rt i hi
        pd := fun j hj => by rw [sm]; exact hIn.pd j hj
        ln := fun i hi => by rw [sm]; exact hIn.ln i hi
        qd := fun i hi => by rw [sm]; exact hIn.qd i hi }
      hpla (fun a ha => by rw [sm, bm, am]; exact hz a ha) hwz
  obtain ⟨c₄, t₄, e₄, ht₄, dA, dB, dk, dm, dr, drm, dO⟩ := p7cRs_exec (P := I) c₃ e₃.wb_right
  have k3 : ∀ r, 9300 ≤ r → c₃.nreg r = c₂'.nreg r := fun r hr => cn r (fun h => by
    have := hScr r h; omega)
  have k2 : ∀ r, KeepR r → c₂.nreg r = c₁.nreg r := fun r hr => bk r (by
    unfold KeepR at hr; omega)
  have k4 : ∀ r, KeepR r → (r < 9600 ∨ 9632 < r) → c₄.nreg r = c₂.nreg r := fun r hr h2 => by
    by_cases h3 : 3000 ≤ r ∧ r ≤ 3012
    · rw [dA r h3.1 h3.2, k3 _ (by omega), sA r h3.1 h3.2]
    by_cases h6 : 6800 ≤ r ∧ r ≤ 6819
    · rw [dB r h6.1 h6.2, k3 _ (by omega), sB r h6.1 h6.2]
    unfold KeepR at hr
    rw [dk r (by omega) (by omega), k3 r (by omega), sk r (by omega)]
  refine ⟨c₄, _, e₁.seq (e₂.seq (e₂'.seq (e₃.seq e₄))), by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, fun a ha => by rw [dm]; exact cz a ha,
    fun i hi j hj => by rw [dm]; exact cO i hi j hj,
    fun a h1 h2 h3 => by rw [dm, ck a h1 h2 h3, sm, bm, am], fun r hr h2 h3 => by
      rw [k4 r hr h3, k2 r hr, k1 r h2], by rw [dr, cr, sr, br, ar], by rw [drm, crm, srm, brm, arm],
    by rw [dO, co, so, bo, ao]⟩
  all_goals first
    | (rw [k4 _ (keepR_ge' (by norm_num)) (by norm_num), k2 _ (keepR_ge' (by norm_num))];
       assumption)

end A

/-! ### Phase b: the FR image written once, live and shadow -/

/-- The FR image at the staging base and its four copies. -/
def st2b : Stmt :=
  .seq p7cB (.seq MsCall.frImg (.seq p7cC (.seq (p7cK 9466 9475) (.seq (p7cK 9466 9471)
    (.seq (p7cK 9473 7612) (p7cK 9473 9474))))))

/-- The FR input of the image written once (prices `0`, root `0`, lengths `0`). -/
noncomputable def img0 (b : ℕ) (Dm : ℕ → ℕ → ℕ) (ET EH : ℕ → ℕ) (k : ℕ) : Monge.FR.Prm :=
  MsCall.frPrm b Dm (fun _ => 0) 0 ET EH (fun _ => 0) (2 * k)

/-- The word bound `Wf` of the FR inputs with `b` corners and `2k` arcs. -/
def wfOf (b k : ℕ) : ℕ := MsCall.fW b (lySb b k + b + b)

/-- The modulus `frM` of the FR inputs (bound `L`). -/
def moOf (b L : ℕ) : ℕ := 2 * (6 * ((b + 2) * L)) + 1

/-- The shadow base `SH = 2 (Wf + 1) + Mo² + Mo`. -/
def shOf (b k L : ℕ) : ℕ := (wfOf b k + 1) + (wfOf b k + 1) + moOf b L * moOf b L + moOf b L

lemma img0_W {b k : ℕ} {Dm : ℕ → ℕ → ℕ} {ET EH : ℕ → ℕ} (het : ∀ a < 2 * k, ET a < b) :
    (img0 b Dm ET EH k).W = wfOf b k := by
  unfold img0 wfOf
  rw [MsCall.frPrm_W het]; unfold lySb; ring_nf

lemma img0_sb {b k : ℕ} {Dm : ℕ → ℕ → ℕ} {ET EH : ℕ → ℕ} (het : ∀ a < 2 * k, ET a < b) :
    (img0 b Dm ET EH k).sb = lySb b k := by
  unfold img0; rw [MsCall.frPrm_sb het]; unfold lySb; ring

lemma img0_M {b k L : ℕ} {Dm : ℕ → ℕ → ℕ} {ET EH : ℕ → ℕ} :
    Monge.FR.frM (img0 b Dm ET EH k) L = moOf b L := MsCall.frM_frPrm L

lemma lySb_le_wfOf (b k : ℕ) : lySb b k + b + b ≤ wfOf b k := by
  unfold wfOf MsCall.fW; omega

section B

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The FR image written once, live and shadow.** -/
theorem st2b_exec (c : Config) (hc : WordsBounded W c) {b k K L S1 PRb ETb EHb ELb : ℕ}
    {Dm : ℕ → ℕ → ℕ} {ET EH : ℕ → ℕ}
    (r19 : c.nreg 9419 = b) (r64 : c.nreg 9464 = lyOm S1 b k) (r17 : c.nreg 9417 = PRb)
    (r62 : c.nreg 9462 = 2 * k) (r14 : c.nreg 9414 = ETb) (r15 : c.nreg 9415 = EHb)
    (r77 : c.nreg 9377 = ELb) (r10 : c.nreg 9310 = K) (r22 : c.nreg 9422 = L)
    (r66 : c.nreg 9466 = lyA S1 b k) (r67 : c.nreg 9467 = lyS S1 b k)
    (hB : MsCall.FrImgB b Dm (fun _ => 0) 0 (2 * k) ET EH (fun _ => 0) L)
    (hdm : ∀ i < b, ∀ j < b, c.nmem (lyOm S1 b k + i * b + j) = Dm i j)
    (hpr : ∀ x < b, c.nmem (PRb + x) = K) (het : ∀ a < 2 * k, c.nmem (ETb + a) = ET a)
    (heh : ∀ a < 2 * k, c.nmem (EHb + a) = EH a) (hel : ∀ a < 2 * k, c.nmem (ELb + a) = K)
    (hPR : PRb + b ≤ S1) (hET : ETb + 2 * k ≤ S1) (hEH : EHb + 2 * k ≤ S1)
    (hEL : ELb + 2 * k ≤ S1)
    (hlow : shOf b k L + (wfOf b k + 1) + lySb b k ≤ lyA S1 b k)
    (hWo : lyOb S1 b k ≤ W) (hKL : K + L + moOf b L ≤ W) (hWf : wfOf b k + 1 ≤ W)
    (hSH : shOf b k L + (wfOf b k + 1) ≤ W) :
    ∃ c' t, Exec P W st2b c c' t ∧ t ≤ 30 * (b * b) + 100 * b + 200 * k + 28 * lySb b k + 350 ∧
      c'.nreg 7600 = b ∧ c'.nreg 7601 = b ∧ c'.nreg 7602 = 0 ∧ c'.nreg 7603 = b * b ∧
      c'.nreg 7604 = b * b + b ∧ c'.nreg 7605 = b * b + b + b + 1 + 2 * k ∧
      c'.nreg 7607 = lySb b k ∧ c'.nreg 7608 = lySb b k + b ∧
      c'.nreg 7609 = lySb b k + b + b ∧ c'.nreg 7610 = moOf b L ∧
      c'.nreg 7611 = 6 * ((b + 2) * L) ∧ c'.nreg 7612 = wfOf b k + 1 ∧
      c'.nreg 9471 = shOf b k L ∧ c'.nreg 9474 = shOf b k L + (wfOf b k + 1) ∧
      c'.nreg 8100 = b ∧ c'.nreg 8102 = PRb ∧ c'.nreg 8104 = 2 * k ∧ c'.nreg 8105 = ETb ∧
      c'.nreg 8107 = ELb ∧
      (∀ a < lySb b k, c'.nmem a = FrFix.frNM (img0 b Dm ET EH k) a ∧
        c'.nmem (shOf b k L + a) = FrFix.frNM (img0 b Dm ET EH k) a ∧
        c'.nmem (wfOf b k + 1 + a) = FrFix.frRS (img0 b Dm ET EH k) L a ∧
        c'.nmem (shOf b k L + (wfOf b k + 1) + a) = FrFix.frRS (img0 b Dm ET EH k) L a) ∧
      (∀ a, ¬ a < lySb b k → ¬ (shOf b k L ≤ a ∧ a < shOf b k L + lySb b k) →
        ¬ (wfOf b k + 1 ≤ a ∧ a < wfOf b k + 1 + lySb b k) →
        ¬ (shOf b k L + (wfOf b k + 1) ≤ a ∧ a < shOf b k L + (wfOf b k + 1) + lySb b k) →
        (a < lyA S1 b k ∨ lyOb S1 b k ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, KeepR r → (r < 9471 ∨ 9475 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hlt := hB.et
  have esb := img0_sb (Dm := Dm) (EH := EH) hlt
  have eW := img0_W (Dm := Dm) (EH := EH) hlt
  have hsbW := lySb_le_wfOf b k
  -- the inputs of `frImg`
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a01, a02, a03, a04, a05, a06, a07, a08, a09, a10, a11, ak, am, ar,
      arm, ao⟩ := p7cB_exec (P := P) c hc
  have hIn : MsCall.FrImgIn b Dm (fun _ => 0) 0 (2 * k) ET EH (fun _ => 0) K L
      (lyOm S1 b k) PRb ETb EHb ELb (lyA S1 b k) (lyS S1 b k) c₁ :=
    { r00 := by rw [a00, r19]
      r01 := by rw [a01, r64]
      r02 := by rw [a02, r17]
      r03 := a03
      r04 := by rw [a04, r62]
      r05 := by rw [a05, r14]
      r06 := by rw [a06, r15]
      r07 := by rw [a07, r77]
      r08 := by rw [a08, r10]
      r09 := by rw [a09, r22]
      r10 := by rw [a10, r66]
      r11 := by rw [a11, r67]
      dm := fun i hi j hj => by rw [am]; exact hdm i hi j hj
      pr := fun x hx => by rw [am, hpr x hx]; simp
      et := fun a ha => by rw [am]; exact het a ha
      eh := fun a ha => by rw [am]; exact heh a ha
      el := fun a ha => by rw [am, hel a ha]; simp }
  have hS1 : S1 + lyT b k = lyOm S1 b k := rfl
  have hAe : lyA S1 b k = lyOm S1 b k + b * b := rfl
  have hSe : lyS S1 b k = lyA S1 b k + lySb b k + lySb b k := rfl
  have hObe : lyOb S1 b k = lyS S1 b k + lyT b k := rfl
  have hT : lyT b k = 4 * k + 4 * b + 2 := rfl
  obtain ⟨c₂, t₂, e₂, ht₂, bNM, bRS, s00, s01, s02, s03, s04, s05, s06, s07, s08, s09, s10, s11,
      s12, s13, bk, bn, br, brm, bo⟩ :=
    MsCall.frImg_spec b Dm (fun _ => 0) 0 (2 * k) ET EH (fun _ => 0) K L (lyOm S1 b k) PRb ETb
      EHb ELb (lyA S1 b k) (lyS S1 b k) W P c₁ hB hIn e₁.wb_right (by omega) (by omega)
      (by omega) (by omega) (by omega)
      (by
        show lyA S1 b k + 2 * (img0 b Dm ET EH k).sb ≤ _
        rw [esb]; omega)
      (by unfold MsCall.fiRoom; omega)
      (by rw [MsCall.frM_frPrm]; exact hKL)
      (by show (img0 b Dm ET EH k).W + 1 ≤ W; rw [eW]; exact hWf)
  change ∀ a < (img0 b Dm ET EH k).sb,
    c₂.nmem (lyA S1 b k + a) = FrFix.frNM (img0 b Dm ET EH k) a at bNM
  change ∀ a < (img0 b Dm ET EH k).sb,
    c₂.nmem (lyA S1 b k + (img0 b Dm ET EH k).sb + a) = FrFix.frRS (img0 b Dm ET EH k) L a at bRS
  rw [esb] at bNM bRS
  have e7612 : c₂.nreg 7612 = wfOf b k + 1 := by rw [s12]; exact congrArg (· + 1) eW
  have e7610 : c₂.nreg 7610 = moOf b L := s10
  have e7607 : c₂.nreg 7607 = lySb b k := by rw [s07]; exact esb
  have e9466 : c₂.nreg 9466 = lyA S1 b k := by
    rw [bn _ (by unfold MsCall.fiScr; omega), ak _ (by omega), r66]
  -- `SH` and the copy bases
  have hshe : shOf b k L = (wfOf b k + 1) + (wfOf b k + 1) + moOf b L * moOf b L + moOf b L :=
    rfl
  obtain ⟨c₃, t₃, e₃, ht₃, d71, d73, d74, d75, dk, dm, dr, drm, dO⟩ :=
    p7cC_exec (P := P) c₂ e₂.wb_right e7612 e7610 e7607 e9466
      (by omega) (by omega)
  have q07 : c₃.nreg 7607 = lySb b k := by rw [dk _ (by omega), e7607]
  -- the four copies
  obtain ⟨c₄, t₄, e₄, ht₄, f1, fk, fn, fr, frm, fo⟩ :=
    p7cK_exec (P := P) (rs := 9466) (rd := 9475) c₃ e₃.wb_right (by omega) (by omega) q07
      (by rw [dk _ (by omega), e9466]) d75
      ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  obtain ⟨c₅, t₅, e₅, ht₅, g1, gk, gn, gr, grm, go⟩ :=
    p7cK_exec (P := P) (rs := 9466) (rd := 9471) c₄ e₄.wb_right (by omega) (by omega)
      (by rw [fn _ (by omega), q07]) (by rw [fn _ (by omega), dk _ (by omega), e9466])
      (by rw [fn _ (by omega), d71])
      ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  obtain ⟨c₆, t₆, e₆, ht₆, h1, hk, hn, hr, hrm, ho⟩ :=
    p7cK_exec (P := P) (rs := 9473) (rd := 7612) c₅ e₅.wb_right (by omega) (by omega)
      (by rw [gn _ (by omega), fn _ (by omega), q07]) (by rw [gn _ (by omega), fn _ (by omega), d73])
      (by rw [gn _ (by omega), fn _ (by omega), dk _ (by omega), e7612])
      ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  obtain ⟨c₇, t₇, e₇, ht₇, i1, ik, in_, ir, irm, io⟩ :=
    p7cK_exec (P := P) (rs := 9473) (rd := 9474) c₆ e₆.wb_right (by omega) (by omega)
      (by rw [hn _ (by omega), gn _ (by omega), fn _ (by omega), q07])
      (by rw [hn _ (by omega), gn _ (by omega), fn _ (by omega), d73])
      (by rw [hn _ (by omega), gn _ (by omega), fn _ (by omega), d74])
      ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  -- registers after the copies
  have kr : ∀ r, (r < 4910 ∨ 4916 < r) → c₇.nreg r = c₃.nreg r := fun r hr => by
    rw [in_ r hr, hn r hr, gn r hr, fn r hr]
  have kr2 : ∀ r, (r < 4910 ∨ 4916 < r) → (r < 9471 ∨ 9475 < r) → c₇.nreg r = c₂.nreg r :=
    fun r h1 h2 => by rw [kr r h1, dk r h2]
  -- memory after the copies: the staging image is never a destination
  have f1' : ∀ i < lySb b k, c₄.nmem i = c₃.nmem (lyA S1 b k + i) := fun i hi => by
    simpa using f1 i hi
  have mA : ∀ a, lyA S1 b k ≤ a → c₇.nmem a = c₂.nmem a := fun a ha => by
    rw [ik a (Or.inr (by omega)), hk a (Or.inr (by omega)), gk a (Or.inr (by omega)),
      fk a (Or.inr (by omega)), dm]
  refine ⟨c₇, _, e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq (e₆.seq e₇))))), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : t₂ ≤ 30 * (b * b) + 100 * b + 100 * (2 * k) + 300 := ht₂
    omega
  · rw [kr2 _ (by omega) (by omega), s00]; rfl
  · rw [kr2 _ (by omega) (by omega), s01]; rfl
  · rw [kr2 _ (by omega) (by omega), s02]; rfl
  · rw [kr2 _ (by omega) (by omega), s03]; rfl
  · rw [kr2 _ (by omega) (by omega), s04]; rfl
  · rw [kr2 _ (by omega) (by omega), s05]
    show (img0 b Dm ET EH k).lb = _
    unfold img0; rw [MsCall.frPrm_lb hlt]
  · rw [kr2 _ (by omega) (by omega), e7607]
  · rw [kr2 _ (by omega) (by omega), s08]
    show (img0 b Dm ET EH k).db = _
    unfold img0 lySb; rw [MsCall.frPrm_db hlt]
  · rw [kr2 _ (by omega) (by omega), s09]
    show (img0 b Dm ET EH k).wb = _
    unfold img0 lySb; rw [MsCall.frPrm_wb hlt]
  · rw [kr2 _ (by omega) (by omega), e7610]
  · rw [kr2 _ (by omega) (by omega), s11]; rfl
  · rw [kr2 _ (by omega) (by omega), e7612]
  · rw [kr _ (by omega), d71]; rfl
  · rw [kr _ (by omega), d74]; rfl
  · rw [kr2 _ (by omega) (by omega), bn _ (by unfold MsCall.fiScr; omega), a00, r19]
  · rw [kr2 _ (by omega) (by omega), bn _ (by unfold MsCall.fiScr; omega), a02, r17]
  · rw [kr2 _ (by omega) (by omega), bn _ (by unfold MsCall.fiScr; omega), a04, r62]
  · rw [kr2 _ (by omega) (by omega), bn _ (by unfold MsCall.fiScr; omega), a05, r14]
  · rw [kr2 _ (by omega) (by omega), bn _ (by unfold MsCall.fiScr; omega), a07, r77]
  · intro a ha
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [ik _ (Or.inl (by omega)), hk _ (Or.inl (by omega)), gk _ (Or.inl (by omega)), f1' a ha,
        dm, bNM a ha]
    · rw [hshe, ik _ (Or.inl (by omega)), hk _ (Or.inr (by omega)), g1 a ha,
        fk _ (Or.inr (by omega)),
        dm, bNM a ha]
    · rw [ik _ (Or.inl (by omega)), h1 a ha, gk _ (Or.inr (by omega)), fk _ (Or.inr (by omega)),
        dm, bRS a ha]
    · rw [hshe, i1 a ha, hk _ (Or.inr (by omega)), gk _ (Or.inr (by omega)), fk _ (Or.inr (by omega)),
        dm, bRS a ha]
  · intro a n1 n2 n3 n4 n5
    rw [ik a (by omega), hk a (by omega), gk a (by omega), fk a (by omega), dm,
      bk a (by omega) (by unfold MsCall.fiRoom; omega), am]
  · intro r hr h2
    have hr' : r < 4910 ∨ 4916 < r := by unfold KeepR at hr; omega
    rw [kr r hr', dk r h2, bn r (by unfold MsCall.fiScr; unfold KeepR at hr; omega),
      ak r (by unfold KeepR at hr; omega)]
  · rw [ir, hr, gr, fr, dr, br, ar]
  · rw [irm, hrm, grm, frm, drm, brm, arm]
  · rw [io, ho, go, fo, dO, bo, ao]

end B

end BKMNW

end PlanarFlow
