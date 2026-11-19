module

public import PlanarFlow.BKMNW.MsRunC

/-!
# The MSSP call: the proof of `msspCall_spec`

* `msRef`: from an explicit start held by a configuration `e` (the low memory `kMem`, the
  registers of `natCfg` and the parameters `knVM`), the reference run of the fixed program
  `KleinFix.kNFM` from the truncation of `e` (`kNFM_exec` of `KStart.run`), with the answers of
  Klein's run in its memory;
* **`msspCall_spec`**: `MsEncSpec` implies `MsspCallSpec` for `msspCall`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Klein MSSP STFlow
  DynTree NegSSSP NsStep

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- The truncation of a configuration to the registers `< 1048` and the memory `≤ Wz`. -/
def kTrunc (Wz : ℕ) (e : Config) : Config where
  pc := e.pc
  nreg r := if r < 1048 then e.nreg r else 0
  rreg _ := 0
  nmem a := if a ≤ Wz then e.nmem a else 0
  rmem _ := 0
  output := e.output

/-- **The reference run of the fixed Klein program** from an explicit start held in memory. -/
theorem msRef (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {P : SPath M}
    {ℓ : D → ℤ} (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e)
    {C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts)}
    {w : CutD M P.darts → ℤ} {nD : ℕ} {σ : CutD M P.darts ≃ Fin nD} {n B t : ℕ}
    {ιv : CutV M P.darts → ℕ} {ιg : CutD M P.darts → ℕ} {ιf : CutF M P.darts → ℕ}
    {ιe : CutD M P.darts → ℕ} {X : ℕ → CutV M P.darts} {fl : ℕ → Bool} {Pin : Input}
    {T : DTree C.map.dual} {C₀ : DTree C.map} {vs ts : List (CutV M P.darts)}
    {fs cs : List (CutF M P.darts)} {c₀ : Config} {Hc : ℕ}
    (hS : KStart P ℓ C w nD σ n B t ιv ιg ιf ιe X fl Pin T C₀ vs ts fs cs c₀ Hc)
    {KC Wz : ℕ} (hKC : kSteps (Fintype.card (CutV M P.darts)) (Fintype.card (CutF M P.darts)) nD
      C.piece.card n C.k (kRank fl C.k) t ≤ KC)
    (hHc1 : 1 ≤ Hc) (hWN : 2 * kleinWN B n Hc + 1 ≤ Wz) (hlen : Pin.data.length ≤ kleinWN B n Hc)
    (e : Config) (hmem : ∀ a ≤ Wz, e.nmem a = kMem B n Hc c₀ Pin a)
    (hmemW : ∀ a ≤ Wz, e.nmem a ≤ Wz)
    (hreg : ∀ r < 406, e.nreg r =
      (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀).nreg r)
    (hknv : ∀ j < 48, e.nreg (1000 + j) =
      KleinFix.knVM B nD n C.k t Hc (kleinWN B n Hc + 1) Pin.data.length j)
    (hregW : ∀ r < 1048, e.nreg r ≤ Wz) (I : Input) :
    ∃ d' dref' s', Exec I Wz KleinFix.kNFM (kTrunc Wz e) dref' s' ∧ s' ≤ 3 * KC ∧
      (∀ a ≤ kleinWN B n Hc, dref'.nmem a = d'.nmem a) ∧
      (∀ j < C.k, fl j = true → C.root j ∈ P.faces → ∀ i < t, ∀ y, X i = C.vx y →
        (kOutN nD n C.k t (B + 16 * (n + 1) + 1) d' (kRank fl j) i).map
          (· / (kN1 M P.darts : ℤ)) = msspPlaneK M P.darts ℓ (C.root j) y) ∧
      dref'.output = e.output := by
  obtain ⟨d', s₀, ex', hs₀, hans, hout'⟩ := hS.run hM hrot hface hnn
  have hβ : B + 16 * (n + 1) + 1 = B + 16 * (n + 1) + 1 := rfl
  have hA : Agree (fun r => decide (r < 406)) (kleinWN B n Hc)
      (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) (kTrunc Wz e) := by
    refine ⟨fun r hr => ?_, fun r hr => rfl, fun a ha => ?_, fun a ha => rfl⟩
    · have hr' : r < 406 := by simpa using hr
      simp only [kTrunc, show r < 1048 by omega, ↓reduceIte]
      exact hreg r hr'
    · simp only [kTrunc, show a ≤ Wz by omega, ↓reduceIte]
      rw [hmem a (by omega)]
      simp only [kMem, ha, ↓reduceIte]
  have hd : WordsBounded Wz (kTrunc Wz e) := by
    refine ⟨fun r => ?_, fun a => ?_⟩
    · simp only [kTrunc]; split_ifs with h
      · exact hregW r h
      · exact Nat.zero_le _
    · simp only [kTrunc]; split_ifs with h
      · exact hmemW a h
      · exact Nat.zero_le _
  have hID : InData Pin (kleinWN B n Hc) (kleinWN B n Hc + 1) Pin.data.length Wz
      (kTrunc Wz e) := by
    refine ⟨by omega, by omega, rfl, fun i hi => ?_⟩
    simp only [kTrunc, show kleinWN B n Hc + 1 + i ≤ Wz by omega, ↓reduceIte]
    rw [hmem _ (by omega)]
    simp only [kMem, show ¬ (kleinWN B n Hc + 1 + i ≤ kleinWN B n Hc) by omega, ↓reduceIte,
      show kleinWN B n Hc + 1 + i - (kleinWN B n Hc + 1) = i by omega]
  have hv : ∀ j < 48, (kTrunc Wz e).nreg (1000 + j) =
      KleinFix.knVM B nD n C.k t Hc (kleinWN B n Hc + 1) Pin.data.length j := fun j hj => by
    simp only [kTrunc, show 1000 + j < 1048 by omega, ↓reduceIte]
    exact hknv j hj
  obtain ⟨dref', s', exr, hs', hA', -, -, -, -, L, o1, o2⟩ :=
    KleinFix.kNFM_exec (P' := I) ex' hHc1 (by omega) (kTrunc Wz e) hA hd hID hv
  refine ⟨d', dref', s', exr, by omega, fun a ha => hA'.nmem a ha, hans, ?_⟩
  have h0 : (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀).output =
      c₀.output := rfl
  rw [hout', h0] at o1
  have hL : L = [] := by simpa using o1
  rw [o2, hL, List.append_nil]
  rfl

/-- The value read back at the query pair `k`, in terms of the start. -/
theorem msRead_val (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {P : SPath M}
    {ℓ : D → ℤ} (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) {q : ℕ} {ts : ℕ → D}
    (hq : ∀ i < q, M.face (ts i) ∈ P.faces)
    {C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts)} {nD n B t : ℕ}
    {X : ℕ → CutV M P.darts} {fl : ℕ → Bool} {d' : Config} {Wb : ℕ}
    (hans : ∀ j < C.k, fl j = true → C.root j ∈ P.faces → ∀ i < t, ∀ y, X i = C.vx y →
      (kOutN nD n C.k t (B + 16 * (n + 1) + 1) d' (kRank fl j) i).map
        (· / (kN1 M P.darts : ℤ)) = msspPlaneK M P.darts ℓ (C.root j) y)
    (hRB : aRBM n C.k + kRank fl C.k * t ≤ B) (hOUT : aOUT nD + kRank fl C.k * t ≤ B)
    (hWb : 2 * (B + 16 * (n + 1)) + 1 ≤ Wb)
    {mem : ℕ → ℕ} (hmd : ∀ a ≤ Wb, mem a = d'.nmem a) {SLb TIb : ℕ}
    (hSL : ∀ i < q, ∃ j < C.k, fl j = true ∧ C.root j = M.face (ts i) ∧
      mem (SLb + i) = kRank fl j)
    (hTI : ∀ i < q, mem (TIb + i) < t ∧ X (mem (TIb + i)) = C.vx (M.face (ts i)))
    {i j : ℕ} (hi : i < q) (hj : j < q) :
    mrVal mem q SLb TIb t (aRBM n C.k) (B + 16 * (n + 1) + 1 + aOUT nD) (kN1 M P.darts)
      (i * q + j) = msW M P ℓ (ts i) (ts j) := by
  obtain ⟨hdv, hmd'⟩ := div_mod_q (i := i) hj
  obtain ⟨j₀, hj₀, hfl, hroot, hs⟩ := hSL i hi
  obtain ⟨hτ, hX⟩ := hTI j hj
  have hsl := slot_lt (kRank_succ_le fl hj₀ hfl) hτ
  unfold mrVal
  rw [hdv, hmd', hs]
  have h1 : mem (aRBM n C.k + (kRank fl j₀ * t + mem (TIb + j))) =
      d'.nmem (aRBM n C.k + kRank fl j₀ * t + mem (TIb + j)) := by
    rw [hmd _ (by clear * - hsl hRB hWb; omega), Nat.add_assoc]
  have h2 : mem (B + 16 * (n + 1) + 1 + aOUT nD + (kRank fl j₀ * t + mem (TIb + j))) =
      d'.nmem (B + 16 * (n + 1) + 1 + (aOUT nD + kRank fl j₀ * t + mem (TIb + j))) := by
    rw [hmd _ (by clear * - hsl hOUT hWb hRB; omega)]
    congr 1; ring
  have := kAns_read (P := P) (ℓ := ℓ) (x := C.root j₀) (y := M.face (ts j)) h1 h2
    (hans j₀ hj₀ hfl (by rw [hroot]; exact hq i hi) _ hτ _ hX)
  rw [this, hroot]
  rfl

set_option maxHeartbeats 1000000 in
/-- **The MSSP call meets its specification, given an encoder meeting `MsEncSpec`.** -/
theorem msspCall_spec {encP : Stmt} {EScr : ℕ → Prop} {ecost KC ZC R : ℕ → ℕ → ℕ → ℕ}
    {wz : ℕ → ℕ → ℕ} (hE : MsEncSpec M encP EScr ecost KC ZC R wz) :
    MsspCallSpec M (msspCall encP) (fun r => EScr r ∨ msScr r) (msCost ecost KC ZC) R wz := by
  intro hM hrot en m P ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p Wz W I c hEn hk hnn hq hc hIn hPl hz
    hwz
  have hface := hEn.ft
  obtain ⟨e, t₀, ex₀, ht₀, hOut, hEk, hE89⟩ :=
    hE hM hrot en m P ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p Wz W I c hEn hk hnn hq hc hIn hPl hz hwz
  obtain ⟨C, w, nD, σ, n, B, t, ιv, ιg, ιf, ιe, X, fl, Pin, T, C₀, vs, ts', fs, cs, c₀, Hc, SLb,
    TIb, Lgb, hS, hKC, hHc1, hWN, hlen, hZC, hmem, hmemW, hreg, hknv, hregW, e10, e11, e12, e13,
    e14, e15, e16, e17, e18, e19, hSL, hTI, p1, p2, p3, p4, p5, p6, hup, er, erm, eo⟩ := hOut
  have hpW := hPl.pw
  obtain ⟨hOb1, hOb2⟩ := hPl.ob
  have hRB := hS.hRB
  have hOUT := hS.hOUT
  have hKW : kleinWN B n Hc = 2 * (B + 16 * (n + 1)) + 1 + (2 * Hc + 1) * (2 * Hc + 1) +
      (2 * Hc + 1) := rfl
  have hWs : Wz ≤ W := by clear * - hOb1 hOb2 hpW; omega
  -- the log registers
  obtain ⟨e₁, u₁, ex₁, hu₁, s21, s20, sk, sm, sr, srm, so⟩ :=
    mcSet_exec (P := I) e ex₀.wb_right (by clear * - hWs hOb1 hOb2 hpW; omega)
  have q1 : ∀ r, r ≠ 8020 → r ≠ 8021 → e₁.nreg r = e.nreg r := sk
  -- the reference run
  obtain ⟨d', dref', s', exr, hs', hdr, hans, hro⟩ :=
    msRef hM hrot hface (fun e _ => hnn e) hS hKC hHc1 hWN hlen e₁
      (fun a ha => by rw [sm]; exact hmem a ha) (fun a ha => by rw [sm]; exact hmemW a ha)
      (fun r hr => by rw [q1 r (by omega) (by omega)]; exact hreg r hr)
      (fun j hj => by rw [q1 _ (by omega) (by omega)]; exact hknv j hj)
      (fun r hr => by rw [q1 r (by omega) (by omega)]; exact hregW r hr) I
  -- the logged run in place
  obtain ⟨e₂, u₂, jl, ex₂, hu₂, hjl, hr2, hm2, hK2, rr2, rm2, L, o1, o2⟩ :=
    KleinFix.kNFM_lgRun (P' := I) exr (LP := 8020) (ONE := 8021) (by norm_num) (by norm_num)
      (by norm_num) hWs e₁ (fun r hr => by simp [kTrunc, hr]) (fun a ha => by simp [kTrunc, ha])
      ex₁.wb_right s21 (by rw [s20, e19]; exact p5)
      (by rw [s20, e19]; clear * - hs' hKC p6 hpW; omega)
  have hL : L = [] := by
    have h3 : (kTrunc Wz e₁).output = e₁.output := rfl
    rw [hro, ← h3] at o1
    simpa using o1.symm
  rw [hL, List.append_nil] at o2
  have q2 : ∀ r, 1048 ≤ r → r ≠ 8020 → e₂.nreg r = e₁.nreg r := fun r h1 h2 =>
    hK2.nreg r (by simp; omega) h2
  have hlog := hK2.lp
  rw [s20, e19] at hlog
  -- the memory of `e₂` above `Wz`
  have m2 : ∀ a, Wz < a → (a < Lgb ∨ Lgb + jl ≤ a) → e₂.nmem a = e.nmem a := fun a h1 h2 => by
    rw [hK2.nmem a h1 (by rw [s20, e19]; exact h2), sm]
  -- the read-back
  have hmd : ∀ a ≤ 2 * (B + 16 * (n + 1)) + 1, e₂.nmem a = d'.nmem a := fun a ha => by
    rw [hm2 a (by clear * - ha hWN hKW; omega), hdr a (by rw [hKW]; clear * - ha; omega)]
  have hSL2 : ∀ i < q, ∃ j < C.k, fl j = true ∧ C.root j = M.face (ts i) ∧
      e₂.nmem (SLb + i) = kRank fl j := fun i hi => by
    obtain ⟨j, hj, h1, h2, h3⟩ := hSL i hi
    exact ⟨j, hj, h1, h2, by rw [m2 _ (by clear * - p1 hOb1 hOb2; omega)
      (Or.inl (by clear * - hi p2; omega)), h3]⟩
  have hTI2 : ∀ i < q, e₂.nmem (TIb + i) < t ∧ X (e₂.nmem (TIb + i)) = C.vx (M.face (ts i)) :=
    fun i hi => by
      rw [m2 _ (by clear * - p3 hOb1 hOb2; omega) (Or.inl (by clear * - hi p4; omega))]
      exact hTI i hi
  have hrd : ∀ k < q * q,
      e₂.nmem (SLb + k / q) * t + e₂.nmem (TIb + k % q) ≤ W ∧
      aRBM n C.k + (e₂.nmem (SLb + k / q) * t + e₂.nmem (TIb + k % q)) < Ob ∧
      B + 16 * (n + 1) + 1 + aOUT nD + (e₂.nmem (SLb + k / q) * t + e₂.nmem (TIb + k % q)) <
        Ob := by
    intro k hk
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hk
      · exact h
    have hkq : k / q < q := by rw [Nat.div_lt_iff_lt_mul hq0]; exact hk
    obtain ⟨j, hj, h1, -, h3⟩ := hSL2 _ hkq
    have hτ := (hTI2 _ (Nat.mod_lt k hq0)).1
    have hsl := slot_lt (kRank_succ_le fl hj h1) hτ
    rw [h3]
    refine ⟨?_, ?_, ?_⟩
    · clear * - hsl hRB hKW hWN hOb1 hWs; omega
    · clear * - hsl hRB hKW hWN hOb1; omega
    · clear * - hsl hOUT hRB hKW hWN hOb1; omega
  have r2 : ∀ r, 8000 ≤ r → r ≤ 8019 → e₂.nreg r = e.nreg r := fun r h1 h2 => by
    rw [q2 r (by omega) (by omega), q1 r (by omega) (by omega)]
  obtain ⟨e₃, u₃, ex₃, hu₃, hval, hk3, hn3, rr3, rm3, o3⟩ :=
    mrRead_exec (P := I) e₂ ex₂.wb_right (q := q) (Ob := Ob)
      (by rw [r2 _ (by norm_num) (by norm_num), hE89 _ (by norm_num) (by norm_num), hIn.r06])
      (by rw [r2 _ (by norm_num) (by norm_num), hE89 _ (by norm_num) (by norm_num), hIn.r08])
      (by rw [r2 _ (by norm_num) (by norm_num), e10]) (by rw [r2 _ (by norm_num) (by norm_num), e11])
      (by rw [r2 _ (by norm_num) (by norm_num), e12]) (by rw [r2 _ (by norm_num) (by norm_num), e13])
      (by rw [r2 _ (by norm_num) (by norm_num), e14]) (by rw [r2 _ (by norm_num) (by norm_num), e15])
      (by rw [q2 _ (by norm_num) (by norm_num), s21])
      (by clear * - hOb2 p1; omega) (by clear * - hOb2 p3; omega)
      (by clear * - p2 p5 p6 hpW; omega) (by clear * - p4 p5 p6 hpW; omega) hrd
      (by clear * - hOb2 p1 p2 p5 p6 hpW; omega)
  -- the clearing
  have hlog3 : ∀ i < jl, e₃.nmem (Lgb + i) ≤ Wz := fun i hi => by
    rw [hk3 _ (Or.inr (by clear * - hOb2 p1 p2; omega))]
    have := hK2.logle i hi
    rwa [s20, e19] at this
  have r3 : ∀ r, 8016 ≤ r → r ≤ 8020 → e₃.nreg r = e₂.nreg r := fun r h1 h2 => hn3 r (by omega)
  obtain ⟨e₄, u₄, ex₄, hu₄, hz4, hk4, hn4, rr4, rm4, o4⟩ :=
    mcClr_exec (P := I) e₃ ex₃.wb_right (p := Lgb) (j := jl) (Ws := Wz)
      (Z := 2 * (B + 16 * (n + 1)) + 2) (β' := kleinWN B n Hc + 1) (len := Pin.data.length)
      (by rw [r3 _ (by norm_num) (by norm_num), r2 _ (by norm_num) (by norm_num), e19])
      (by rw [r3 _ (by norm_num) (by norm_num), hlog])
      (by rw [r3 _ (by norm_num) (by norm_num), r2 _ (by norm_num) (by norm_num), e16])
      (by rw [r3 _ (by norm_num) (by norm_num), r2 _ (by norm_num) (by norm_num), e17])
      (by rw [r3 _ (by norm_num) (by norm_num), r2 _ (by norm_num) (by norm_num), e18])
      hlog3 p5 (by clear * - hKW hWN hWs; omega) (by clear * - hlen hWN hWs; omega)
      (by clear * - hlen hWN hWs hKW; omega)
  -- the conclusions
  refine ⟨e₄, _, ex₀.seq (ex₁.seq (ex₂.seq (ex₃.seq ex₄))), ?_, fun a ha => ?_,
    fun i hi j hj => ?_, fun a h1 h2 h3 => ?_, fun r hr => ?_, by rw [rr4, rr3, rr2, sr, er],
    by rw [rm4, rm3, rm2, srm, erm], by rw [o4, o3, o2, so, eo]⟩
  · -- the cost
    unfold msCost
    have : jl ≤ 3 * KC m P.k q := by clear * - hjl hs'; omega
    clear * - ht₀ hu₁ hu₂ hs' hu₃ hu₄ this hZC
    omega
  · -- the memory `≤ Wz` is zero again
    by_cases hl : (∃ i < jl, e₃.nmem (Lgb + i) = a) ∨ a < 2 * (B + 16 * (n + 1)) + 2 ∨
        (kleinWN B n Hc + 1 ≤ a ∧ a < kleinWN B n Hc + 1 + Pin.data.length)
    · exact hz4 a hl
    · simp only [not_or, not_exists, not_and, not_lt] at hl
      obtain ⟨hl1, hl2, hl3⟩ := hl
      rw [hk4 a (fun i hi => hl1 i hi) hl2 (by clear * - hl3; omega),
        hk3 a (Or.inl (by clear * - ha hOb1; omega))]
      rw [hK2.dirty a ha (fun i hi h => hl1 i hi (by
        rw [hk3 _ (Or.inr (by clear * - hOb2 p1 p2 hi; omega))]
        rw [s20, e19] at h; exact h)), sm, hmem a ha]
      exact kMem_zero hl2 (by clear * - hl3; omega)
  · -- the answers
    have hk : i * q + j < q * q := by
      have := Nat.mul_le_mul_right q (show i + 1 ≤ q by omega)
      rw [Nat.succ_mul] at this; omega
    rw [hk4 _ (fun l hl h => by
        have := hlog3 l hl; rw [h] at this; clear * - this hOb1; omega)
      (by clear * - hKW hWN hOb1; omega) (Or.inr (by clear * - hlen hWN hOb1; omega)),
      Nat.add_assoc, hval _ hk]
    exact msRead_val hM hrot hface (fun e _ => hnn e) hq hans hRB hOUT le_rfl hmd hSL2 hTI2 hi hj
  · -- the memory above `Wz`
    have hR := p6
    rw [hk4 a (fun l hl h => by
        have := hlog3 l hl; rw [h] at this; clear * - this h1; omega)
      (by clear * - hKW hWN h1; omega) (Or.inr (by clear * - hlen hWN h1; omega)),
      hk3 a (by clear * - h2; omega), m2 a h1 (by clear * - h3 p1 p2 p6 hjl hs'; omega), hup a h1 h3]
  · -- the registers
    simp only [not_or] at hr
    obtain ⟨hr1, hr2⟩ := hr
    unfold msScr at hr2
    simp only [not_or, not_and, not_le] at hr2
    rw [hn4 r (by clear * - hr2; omega), hn3 r (by clear * - hr2; omega),
      q2 r (by clear * - hr2; omega) (by clear * - hr2; omega),
      q1 r (by clear * - hr2; omega) (by clear * - hr2; omega), hEk r hr1]

/-- The call adds no real instruction to its encoder. -/
theorem msspCall_natOnly {encP : Stmt} (h : Klein.natOnly encP = true) :
    Klein.natOnly (msspCall encP) = true := by
  have h1 : Klein.natOnly mcSet = true := by decide
  have h2 : Klein.natOnly (lgS 8020 8021 KleinFix.kNFM) = true :=
    lgS_natOnly _ KleinFix.kNFM_natOnly
  have h3 : Klein.natOnly mrRead = true := by decide
  have h4 : Klein.natOnly mcClr = true := by decide +kernel
  simp only [msspCall, Klein.natOnly, h, h1, h2, h3, h4, Bool.and_self]

end MsCall

end BKMNW

end PlanarFlow
