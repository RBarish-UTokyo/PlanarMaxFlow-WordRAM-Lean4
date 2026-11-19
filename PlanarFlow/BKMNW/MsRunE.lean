module

public import PlanarFlow.BKMNW.MsRunD

/-!
# The MSSP call with a clearing independent of the length magnitudes: `msspCall'`

`msspCall` (`MsRunC`/`MsRunD`) clears the whole region `[0, 2 (B + 16 (n + 1)) + 2)` of
`natCfg`'s words after Klein's run (`mcClr`), and `KStart.hP` forces `B ≥ max LN ≈ N₁ · Lmax`:
its cost has a term in the magnitudes of the lengths, so `MsEncSpec`
cannot be met with a step bound of `m, k, q` alone.

Here the clearing is targeted: Klein's run is logged (`lgS`), so after the run every cell
`≤ Wz` that is not logged holds what the encoder wrote; the encoder declares three regions
outside which its words below `Wz` are zero (for the start `mkC0` they are `[0, n + k)` (the
flags), `[β, β + 3 nD + 3)` (the residues of the real words) and the input words
`[β', β' + |Pin|)`, all of size `O(m + k²)`):

* **`MsEncOut'`**: `MsEncOut` with `r8016 = Z1`, `r8033 = Zb`, `r8034 = Z2` and the words
  `≤ Wz` zero outside `[0, Z1) ∪ [Zb, Zb + Z2) ∪ [β', β' + |Pin|)`, `Z1 + Z2 + |Pin| ≤ ZC`;
  **`MsEncSpec'`** (as `MsEncSpec`, with `MsEncOut'`);
* **`mcClr'`** `= mcClr ; mcZ3` (log, `[0, Z1)`, `[β', β' + len)`, then `[Zb, Zb + Z2)`);
* **`msspCall'`** `= encP ; mcSet ; lgS 8020 8021 kNFM ; mrRead ; mcClr'`;
* **`msspCall'_spec`**: `MsEncSpec' M encP EScr ecost KC ZC R wz →
  MsspCallSpec M (msspCall' encP) (EScr ∨ msScr) (msCost' ecost KC ZC) R wz`, with
  **`msCost' = ecost + 27 KC + 5 ZC + 23 q² + 40`**: no term in `B`.
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

/-- **What the encoder leaves, with targeted clearing regions** (see the module docstring). -/
def MsEncOut' (P : SPath M) (ℓ : D → ℤ) (q : ℕ) (ts : ℕ → D) (Wz Ob p R KC ZC : ℕ)
    (c e : Config) : Prop :=
  ∃ (C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts))
    (w : CutD M P.darts → ℤ) (nD : ℕ) (σ : CutD M P.darts ≃ Fin nD) (n B t : ℕ)
    (ιv : CutV M P.darts → ℕ) (ιg : CutD M P.darts → ℕ) (ιf : CutF M P.darts → ℕ)
    (ιe : CutD M P.darts → ℕ) (X : ℕ → CutV M P.darts) (fl : ℕ → Bool) (Pin : Input)
    (T : DTree C.map.dual) (C₀ : DTree C.map) (vs ts' : List (CutV M P.darts))
    (fs cs : List (CutF M P.darts)) (c₀ : Config) (Hc SLb TIb Lgb Z1 Zb Z2 : ℕ),
    KStart P ℓ C w nD σ n B t ιv ιg ιf ιe X fl Pin T C₀ vs ts' fs cs c₀ Hc ∧
    kSteps (Fintype.card (CutV M P.darts)) (Fintype.card (CutF M P.darts)) nD C.piece.card n
      C.k (kRank fl C.k) t ≤ KC ∧
    1 ≤ Hc ∧ 2 * kleinWN B n Hc + 1 ≤ Wz ∧ Pin.data.length ≤ kleinWN B n Hc ∧
    Z1 + Z2 + Pin.data.length ≤ ZC ∧ Z1 ≤ Wz ∧ Zb + Z2 ≤ Wz ∧
    (∀ a ≤ Wz, e.nmem a = kMem B n Hc c₀ Pin a) ∧ (∀ a ≤ Wz, e.nmem a ≤ Wz) ∧
    (∀ a ≤ Wz, Z1 ≤ a → (a < Zb ∨ Zb + Z2 ≤ a) →
      (a < kleinWN B n Hc + 1 ∨ kleinWN B n Hc + 1 + Pin.data.length ≤ a) → e.nmem a = 0) ∧
    (∀ r < 406, e.nreg r =
      (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀).nreg r) ∧
    (∀ j < 48, e.nreg (1000 + j) =
      KleinFix.knVM B nD n C.k t Hc (kleinWN B n Hc + 1) Pin.data.length j) ∧
    (∀ r < 1048, e.nreg r ≤ Wz) ∧
    e.nreg 8010 = t ∧ e.nreg 8011 = aRBM n C.k ∧
    e.nreg 8012 = B + 16 * (n + 1) + 1 + aOUT nD ∧ e.nreg 8013 = kN1 M P.darts ∧
    e.nreg 8014 = SLb ∧ e.nreg 8015 = TIb ∧ e.nreg 8016 = Z1 ∧
    e.nreg 8017 = kleinWN B n Hc + 1 ∧ e.nreg 8018 = Pin.data.length ∧ e.nreg 8019 = Lgb ∧
    e.nreg 8033 = Zb ∧ e.nreg 8034 = Z2 ∧
    (∀ i < q, ∃ j < C.k, fl j = true ∧ C.root j = M.face (ts i) ∧
      e.nmem (SLb + i) = kRank fl j) ∧
    (∀ i < q, e.nmem (TIb + i) < t ∧ X (e.nmem (TIb + i)) = C.vx (M.face (ts i))) ∧
    p ≤ SLb ∧ SLb + q ≤ Lgb ∧ p ≤ TIb ∧ TIb + q ≤ Lgb ∧ Wz < Lgb ∧ Lgb + 3 * KC + 1 ≤ p + R ∧
    (∀ a, Wz < a → (a < p ∨ p + R ≤ a) → e.nmem a = c.nmem a) ∧
    e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output

variable (M) in
/-- **The specification of the encoder of an MSSP call, with targeted clearing regions**
(`MsEncSpec` with `MsEncOut'`). -/
def MsEncSpec' (encP : Stmt) (EScr : ℕ → Prop) (ecost KC ZC R : ℕ → ℕ → ℕ → ℕ)
    (wz : ℕ → ℕ → ℕ) : Prop :=
  M.IsPlane → M.RotTrans →
  ∀ (en : ℕ → D) (m : ℕ) (P : SPath M) (ℓ : D → ℤ) (Lmax q : ℕ) (ts : ℕ → D)
    (RVb RTb Pb Lb Qb Ob p Wz W : ℕ) (I : Input) (c : Config),
    EnumOK M en m → 0 < P.k → (∀ e, 0 ≤ ℓ e) → (∀ i < q, M.face (ts i) ∈ P.faces) →
    WordsBounded W c → MsIn M en m P ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p c →
    MsPlace m P.k q Wz W RVb RTb Pb Lb Qb Ob p (R m P.k q) →
    (∀ a ≤ Wz, c.nmem a = 0) → wz m Lmax ≤ Wz →
    ∃ e t, Exec I W encP c e t ∧ t ≤ ecost m P.k q ∧
      MsEncOut' P ℓ q ts Wz Ob p (R m P.k q) (KC m P.k q) (ZC m P.k q) c e ∧
      (∀ r, ¬ EScr r → e.nreg r = c.nreg r) ∧ (∀ r, 8000 ≤ r → r ≤ 8009 → e.nreg r = c.nreg r)

/-- The third clearing region `[r8033, r8033 + r8034)`. -/
def mcZ3 : Stmt := .seq (block [.copyN 5030 8034, .copyN 5031 8033]) mzFill

/-- **The targeted clearing.** -/
def mcClr' : Stmt := .seq mcClr mcZ3

/-- **The MSSP call with targeted clearing.** -/
def msspCall' (encP : Stmt) : Stmt :=
  .seq encP (.seq mcSet (.seq (lgS 8020 8021 KleinFix.kNFM) (.seq mrRead mcClr')))

/-- **The step bound of `msspCall'`**: no term in the magnitudes of the lengths. -/
def msCost' (ecost KC ZC : ℕ → ℕ → ℕ → ℕ) (m k q : ℕ) : ℕ :=
  ecost m k q + 27 * KC m k q + 5 * ZC m k q + 23 * (q * q) + 40

section Run

variable {P : Input} {W : ℕ}

/-- `mcZ3`. -/
theorem mcZ3_exec (c : Config) (hc : WordsBounded W c) {Zb Z2 : ℕ}
    (r33 : c.nreg 8033 = Zb) (r34 : c.nreg 8034 = Z2) (hZ : Zb + Z2 ≤ W) (hZ' : Z2 + 1 ≤ W) :
    ∃ c' u, Exec P W mcZ3 c c' u ∧ u ≤ 5 * Z2 + 7 ∧
      (∀ a, Zb ≤ a → a < Zb + Z2 → c'.nmem a = 0) ∧
      (∀ a, (a < Zb ∨ Zb + Z2 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 5030 ∨ 5035 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, f30, f31, fk, fm, fr, frm, fo⟩ : ∃ c₁ t₁,
      Exec P W (block [.copyN 5030 8034, .copyN 5031 8033]) c c₁ t₁ ∧ t₁ = 2 ∧
        c₁.nreg 5030 = Z2 ∧ c₁.nreg 5031 = Zb ∧
        (∀ r, r ≠ 5030 → r ≠ 5031 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    · rw [r34]
    · rw [r33]
    · repeat rw [upd_other _ _ _ (by omega)]
  obtain ⟨c₂, t₂, e₂, ht₂, gzero, gkeep, gregs, gr, grm, go⟩ :=
    mzFill_exec (P := P) c₁ e₁.wb_right (len := Z2) (Zb := Zb) f30 f31 hZ hZ'
  refine ⟨c₂, _, e₁.seq e₂, by omega, fun a h1 h2 => ?_, fun a ha => ?_, fun r hr => ?_,
    by rw [gr, fr], by rw [grm, frm], by rw [go, fo]⟩
  · have := gzero (a - Zb) (by omega); rwa [show Zb + (a - Zb) = a by omega] at this
  · rw [gkeep a ha, fm]
  · rw [gregs r (by omega), fk r (by omega) (by omega)]

end Run

set_option maxHeartbeats 1000000 in
/-- **The MSSP call with targeted clearing meets its specification**, given an encoder meeting
`MsEncSpec'`; the step bound `msCost'` has no term in the magnitudes of the lengths. -/
theorem msspCall'_spec {encP : Stmt} {EScr : ℕ → Prop} {ecost KC ZC R : ℕ → ℕ → ℕ → ℕ}
    {wz : ℕ → ℕ → ℕ} (hE : MsEncSpec' M encP EScr ecost KC ZC R wz) :
    MsspCallSpec M (msspCall' encP) (fun r => EScr r ∨ msScr r) (msCost' ecost KC ZC) R wz := by
  intro hM hrot en m P ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p Wz W I c hEn hk hnn hq hc hIn hPl hz
    hwz
  have hface := hEn.ft
  obtain ⟨e, t₀, ex₀, ht₀, hOut, hEk, hE89⟩ :=
    hE hM hrot en m P ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p Wz W I c hEn hk hnn hq hc hIn hPl hz hwz
  obtain ⟨C, w, nD, σ, n, B, t, ιv, ιg, ιf, ιe, X, fl, Pin, T, C₀, vs, ts', fs, cs, c₀, Hc, SLb,
    TIb, Lgb, Z1, Zb, Z2, hS, hKC, hHc1, hWN, hlen, hZC, hZ1, hZb, hmem, hmemW, hzero, hreg,
    hknv, hregW, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e33, e34, hSL, hTI, p1, p2,
    p3, p4, p5, p6, hup, er, erm, eo⟩ := hOut
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
      (Z := Z1) (β' := kleinWN B n Hc + 1) (len := Pin.data.length)
      (by rw [r3 _ (by norm_num) (by norm_num), r2 _ (by norm_num) (by norm_num), e19])
      (by rw [r3 _ (by norm_num) (by norm_num), hlog])
      (by rw [r3 _ (by norm_num) (by norm_num), r2 _ (by norm_num) (by norm_num), e16])
      (by rw [r3 _ (by norm_num) (by norm_num), r2 _ (by norm_num) (by norm_num), e17])
      (by rw [r3 _ (by norm_num) (by norm_num), r2 _ (by norm_num) (by norm_num), e18])
      hlog3 p5 (by clear * - hZ1 hOb1 hOb2 hpW hWs; omega) (by clear * - hlen hWN hWs; omega)
      (by clear * - hlen hWN hWs hKW; omega)
  have r4 : ∀ r, r = 8033 ∨ r = 8034 → e₄.nreg r = e.nreg r := fun r hr => by
    rw [hn4 r (by omega), hn3 r (by omega), q2 r (by omega) (by omega),
      q1 r (by omega) (by omega)]
  obtain ⟨e₅, u₅, ex₅, hu₅, hz5, hk5, hn5, rr5, rm5, o5⟩ :=
    mcZ3_exec (P := I) e₄ ex₄.wb_right (Zb := Zb) (Z2 := Z2) (by rw [r4 _ (Or.inl rfl), e33])
      (by rw [r4 _ (Or.inr rfl), e34]) (by clear * - hZb hWs; omega)
      (by clear * - hZb hOb1 hOb2 hpW hWs; omega)
  -- the conclusions
  have ex : Exec I W (msspCall' encP) c e₅ (t₀ + (u₁ + (u₂ + (u₃ + (u₄ + u₅))))) :=
    ex₀.seq (ex₁.seq (ex₂.seq (ex₃.seq (ex₄.seq ex₅))))
  refine ⟨e₅, _, ex, ?_, fun a ha => ?_, fun i hi j hj => ?_, fun a h1 h2 h3 => ?_,
    fun r hr => ?_, by rw [rr5, rr4, rr3, rr2, sr, er], by rw [rm5, rm4, rm3, rm2, srm, erm],
    by rw [o5, o4, o3, o2, so, eo]⟩
  · -- the cost
    unfold msCost'
    have : jl ≤ 3 * KC m P.k q := by clear * - hjl hs'; omega
    clear * - ht₀ hu₁ hu₂ hs' hu₃ hu₄ hu₅ this hZC
    omega
  · -- the memory `≤ Wz` is zero again
    by_cases h3 : Zb ≤ a ∧ a < Zb + Z2
    · exact hz5 a h3.1 h3.2
    rw [hk5 a (by clear * - h3; omega)]
    by_cases hl : (∃ i < jl, e₃.nmem (Lgb + i) = a) ∨ a < Z1 ∨
        (kleinWN B n Hc + 1 ≤ a ∧ a < kleinWN B n Hc + 1 + Pin.data.length)
    · exact hz4 a hl
    · simp only [not_or, not_exists, not_and, not_lt] at hl
      obtain ⟨hl1, hl2, hl3⟩ := hl
      rw [hk4 a (fun i hi => hl1 i hi) hl2 (by clear * - hl3; omega),
        hk3 a (Or.inl (by clear * - ha hOb1; omega))]
      rw [hK2.dirty a ha (fun i hi h => hl1 i hi (by
        rw [hk3 _ (Or.inr (by clear * - hOb2 p1 p2 hi; omega))]
        rw [s20, e19] at h; exact h)), sm]
      exact hzero a ha hl2 (by clear * - h3; omega) (by clear * - hl3; omega)
  · -- the answers
    have hk : i * q + j < q * q := by
      have := Nat.mul_le_mul_right q (show i + 1 ≤ q by omega)
      rw [Nat.succ_mul] at this; omega
    rw [hk5 _ (Or.inr (by clear * - hZb hOb1; omega)),
      hk4 _ (fun l hl h => by
        have := hlog3 l hl; rw [h] at this; clear * - this hOb1; omega)
      (by clear * - hZ1 hOb1; omega) (Or.inr (by clear * - hlen hWN hOb1; omega)),
      Nat.add_assoc, hval _ hk]
    exact msRead_val hM hrot hface (fun e _ => hnn e) hq hans hRB hOUT le_rfl hmd hSL2 hTI2 hi hj
  · -- the memory above `Wz`
    have hR := p6
    rw [hk5 a (Or.inr (by clear * - hZb h1; omega)),
      hk4 a (fun l hl h => by
        have := hlog3 l hl; rw [h] at this; clear * - this h1; omega)
      (by clear * - hZ1 h1; omega) (Or.inr (by clear * - hlen hWN h1; omega)),
      hk3 a (by clear * - h2; omega), m2 a h1 (by clear * - h3 p1 p2 p6 hjl hs'; omega), hup a h1 h3]
  · -- the registers
    simp only [not_or] at hr
    obtain ⟨hr1, hr2⟩ := hr
    unfold msScr at hr2
    simp only [not_or, not_and, not_le] at hr2
    rw [hn5 r (by clear * - hr2; omega), hn4 r (by clear * - hr2; omega),
      hn3 r (by clear * - hr2; omega),
      q2 r (by clear * - hr2; omega) (by clear * - hr2; omega),
      q1 r (by clear * - hr2; omega) (by clear * - hr2; omega), hEk r hr1]

/-- The call adds no real instruction to its encoder. -/
theorem msspCall'_natOnly {encP : Stmt} (h : Klein.natOnly encP = true) :
    Klein.natOnly (msspCall' encP) = true := by
  have h1 : Klein.natOnly mcSet = true := by decide
  have h2 : Klein.natOnly (lgS 8020 8021 KleinFix.kNFM) = true :=
    lgS_natOnly _ KleinFix.kNFM_natOnly
  have h3 : Klein.natOnly mrRead = true := by decide
  have h4 : Klein.natOnly mcClr' = true := by decide +kernel
  simp only [msspCall', Klein.natOnly, h, h1, h2, h3, h4, Bool.and_self]

end MsCall

end BKMNW

end PlanarFlow
