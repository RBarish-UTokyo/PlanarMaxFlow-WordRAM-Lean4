module

public import PlanarFlow.BKMNW.MsStA
public import PlanarFlow.BKMNW.StRankM

/-!
# The MSSP encoder, stage A2: compact node numbers and the boundary darts

**`msA2`** `= cmSetA ; cmSetB ; cmProg ; gSetA ; gSetB ; wrLoop vG ; ggSet`: after stage A1, the
node numbers of Klein's encoding become compact (`StEnc.cmProg_kin` on the map
`Q.dual = (cutMap hL).dual.dual`: vertices `1 + τv`, faces `2 nD + 1 + τf`), the boundary darts
`G[i] = σ (g i)` (`i < fixPer`) are written at `IM + iGB nD n` (`n = 4 nD + 1`), and the word
`σ (g 0)` twice at `aGG` (the terminal words read by `kiProg`). **`msA2_exec`** (`StA2`).
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

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

variable {P : Input} {W : ℕ}

def cmSetA : Stmt :=
  block [.constN 8264 4, .mulN 7950 8230 8264, .constN 8264 3, .mulN 8265 8228 8264,
    .subN 7950 7950 8265, .addN 7953 8282 7950]

def cmSetB : Stmt :=
  block [.addN 7951 7953 7950, .addN 7951 7951 7950, .addN 7951 7951 7950, .addN 7952 7951 7950,
    .copyN 7954 7950, .copyN 7955 8283]

def gSetA : Stmt :=
  block [.copyN 8200 8156, .constN 8264 12, .mulN 8201 7950 8264, .addN 8201 8201 8282,
    .constN 8264 1, .addN 8201 8201 8264, .copyN 8202 8289]

def gSetB : Stmt :=
  block [.constN 8264 6, .mulN 7320 8000 8264, .addN 7320 7320 8009, .constN 8264 14,
    .mulN 7321 8000 8264, .addN 7321 7321 8009, .addN 7322 8230 8230, .subN 7322 7322 8228]

def ggSet : Stmt :=
  block [.loadN 8264 8201, .storeN 8284 8264, .constN 8265 1, .addN 8265 8284 8265,
    .storeN 8265 8264]


theorem cmSetA_exec (c : Config) (hc : WordsBounded W c) {nE nT IM : ℕ}
    (r28 : c.nreg 8228 = nE) (r30 : c.nreg 8230 = nE + nT) (r82 : c.nreg 8282 = IM)
    (hw : 4 * (nE + nT) + IM + 4 ≤ W) :
    ∃ c' t, Exec P W cmSetA c c' t ∧ t = 6 ∧ c'.nreg 7950 = nE + 4 * nT ∧
      c'.nreg 7953 = IM + (nE + 4 * nT) ∧
      (∀ r, r ≠ 7950 → r ≠ 7953 → r ≠ 8264 → r ≠ 8265 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cmSetA
  exec_block
  all_goals try ((try config_simp); (try simp only [r28, r30, r82]); omega)
  refine ⟨rfl, ?_, ?_, fun r a b d e => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r28, r30, r82]; omega)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem cmSetB_exec (c : Config) (hc : WordsBounded W c) {nD IM X : ℕ}
    (r50 : c.nreg 7950 = nD) (r53 : c.nreg 7953 = IM + nD) (r83 : c.nreg 8283 = X)
    (hw : IM + 5 * nD ≤ W) :
    ∃ c' t, Exec P W cmSetB c c' t ∧ t = 6 ∧ c'.nreg 7950 = nD ∧ c'.nreg 7951 = IM + 4 * nD ∧
      c'.nreg 7952 = IM + 5 * nD ∧ c'.nreg 7953 = IM + nD ∧ c'.nreg 7954 = nD ∧
      c'.nreg 7955 = X ∧
      (∀ r, (r < 7951 ∨ 7955 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cmSetB
  exec_block
  all_goals try ((try config_simp); (try simp only [r50, r53, r83]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r50, r53, r83]; omega)
    | (simp only [r50, r53, r83]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem gSetA_exec (c : Config) (hc : WordsBounded W c) {per nD IM DU : ℕ}
    (r56 : c.nreg 8156 = per) (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM)
    (r89 : c.nreg 8289 = DU) (hw : 12 * nD + IM + 13 ≤ W) :
    ∃ c' t, Exec P W gSetA c c' t ∧ t = 7 ∧ c'.nreg 8200 = per ∧
      c'.nreg 8201 = IM + 12 * nD + 1 ∧ c'.nreg 8202 = DU ∧
      (∀ r, (r < 8200 ∨ 8202 < r) → r ≠ 8264 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold gSetA
  exec_block
  all_goals try ((try config_simp); (try simp only [r56, r50, r82, r89]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r56, r50, r82, r89]; omega)
    | (simp only [r56, r50, r82, r89]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem gSetB_exec (c : Config) (hc : WordsBounded W c) {m p nE nT : ℕ}
    (r00 : c.nreg 8000 = m) (r09 : c.nreg 8009 = p) (r28 : c.nreg 8228 = nE)
    (r30 : c.nreg 8230 = nE + nT) (hw : p + 14 * m + 2 * (nE + nT) + 14 ≤ W) :
    ∃ c' t, Exec P W gSetB c c' t ∧ t = 8 ∧ c'.nreg 7320 = p + 6 * m ∧
      c'.nreg 7321 = p + 14 * m ∧ c'.nreg 7322 = nE + 2 * nT ∧
      (∀ r, (r < 7320 ∨ 7322 < r) → r ≠ 8264 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold gSetB
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r09, r28, r30]); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r00, r09, r28, r30]; omega)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem ggSet_exec (c : Config) (hc : WordsBounded W c) {Gb GG : ℕ}
    (r01 : c.nreg 8201 = Gb) (r84 : c.nreg 8284 = GG) (hw : GG + 1 ≤ W) :
    ∃ c' t, Exec P W ggSet c c' t ∧ t = 5 ∧
      c'.nmem = upd (upd c.nmem GG (c.nmem Gb)) (GG + 1) (c.nmem Gb) ∧
      (∀ r, r ≠ 8264 → r ≠ 8265 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ggSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r01, r84]); omega)
  refine ⟨rfl, ?_, fun r a b => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  · simp only [r01, r84]
  · simp only [upd_apply]; split_ifs <;> first | omega | rfl

/-- Klein's map words only depend on the memory `[β, β + 8 nD + E)` (`ιe < E`). -/
lemma kInM_frame {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X]
    {Q : CombMap D' X Y} {nD : ℕ} {σ : D' ≃ Fin nD} {ιv : X → ℕ} {ιg : D' → ℕ} {ιf : Y → ℕ}
    {ιe : D' → ℕ} {mem mem' : ℕ → ℕ} {β E : ℕ} (h : StEnc.KInM Q σ ιv ιg ιf ιe mem β)
    (hE : ∀ d, ιe d < E) (hm : ∀ a, β ≤ a → a < β + 8 * nD + E → mem' a = mem a) :
    StEnc.KInM Q σ ιv ιg ιf ιe mem' β := by
  have e : ∀ (o : ℕ) (d : D'), o + nD ≤ 8 * nD → mem' (β + o + σ d) = mem (β + o + σ d) :=
    fun o d ho => by have := (σ d).2; exact hm _ (by omega) (by omega)
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
    fun d => ?_, fun d => ?_⟩
  · rw [e _ d (by simp [Klein.iRV]; omega)]; exact h.rv d
  · rw [e _ d (by simp [Klein.iNF]; omega)]; exact h.nf d
  · rw [e _ d (by simp [Klein.iNE]; omega)]; exact h.ne d
  · rw [e _ d (by simp [Klein.iNG]; omega)]; exact h.ng d
  · rw [e _ d (by simp [Klein.iNT]; omega)]; exact h.nt d
  · rw [e _ d (by simp [Klein.iNH]; omega)]; exact h.nh d
  · rw [e _ d (by simp [Klein.iIS]; omega)]; exact h.is d
  · have := hE d
    have e' : mem' (β + Klein.iED nD + ιe d) = mem (β + Klein.iED nD + ιe d) :=
      hm _ (by omega) (by simp [Klein.iED]; omega)
    rw [e']; exact h.ed d

/-- **What stage A leaves** (stage A1 and A2). -/
structure StA (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) (p q : ℕ) (c e : Config) {nF nV : ℕ}
    (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV) : Prop where
  lay : ∀ j < 17, e.nreg (8280 + j) = (msLayV m p q).getD j 0
  per : e.nreg 8156 = fixPer M Pa
  ncl : e.nreg 8157 = (fixCornerL M Pa).length
  r28 : e.nreg 8228 = nEc Pa.darts en m
  r30 : e.nreg 8230 = nEc Pa.darts en m + nTc M Pa.darts en m
  r50 : e.nreg 7950 = nEc Pa.darts en m + 4 * nTc M Pa.darts en m
  r57 : e.nreg 7957 = nF
  r59 : e.nreg 7959 = nV
  tr : ∀ s < fixPer M Pa, e.nmem (p + 6 * m + s) = ixOf en m ((tour M Pa.darts)^[s] (Pa.d 0))
  fl : ∀ i < m, e.nmem (p + m + i) = labI M en m i + 1
  lf : ∀ i < m, e.nmem (p + 2 * m + i) = if en i ∈ Pa.darts then 1 else 0
  cs : ∀ r < (fixCornerL M Pa).length,
    e.nmem (p + 8 * m + r) = (fixCornerL M Pa).getD r 0 ∧
      e.nmem (p + 7 * m + r) =
        ixOf en m ((tour M Pa.darts)^[(fixCornerL M Pa).getD r 0] (Pa.d 0))
  cn : ∀ i < m, M.face (en i) ∈ Pa.faces → ∃ r < (fixCornerL M Pa).length,
    e.nmem (p + 9 * m - 1 + (labI M en m i + 1)) = r ∧
      fixCorner M Pa ((fixCornerL M Pa).getD r 0) = M.face (en i)
  rk : ∀ i < m, e.nmem (p + 13 * m + i) = cE Pa.darts en i ∧
    e.nmem (p + 14 * m + i) = cT M Pa.darts en i
  kin : StEnc.KInM (cutMap Pa.rev_mem_darts').dual.dual (StEnc.enEq (cQ h Pa hk))
    (fun x => 1 + (τv x : ℕ)) (StEnc.ιG _ (cQ h Pa hk))
    (fun y => 2 * (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) + 1 + (τf y : ℕ))
    (StEnc.ιE _ (cQ h Pa hk)) e.nmem (aIM m p)
  g : ∀ i < fixPer M Pa, e.nmem (aIM m p + 12 * (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) +
    1 + i) = StEnc.enEq (cQ h Pa hk) (cutG Pa.rev_mem_darts' (fixT0 Pa hk) i)
  gg0 : e.nmem (aGG m p) = StEnc.enEq (cQ h Pa hk) (cD0 Pa hk)
  gg1 : e.nmem (aGG m p + 1) = StEnc.enEq (cQ h Pa hk) (cD0 Pa hk)
  mem : ∀ a, (a < p ∨ aGG m p + 2 ≤ a) → (a < aDU m p ∨ aDU m p + m ≤ a) → e.nmem a = c.nmem a
  reg : ∀ r, ¬ EScr r → e.nreg r = c.nreg r
  rr : e.rreg = c.rreg
  rm : e.rmem = c.rmem
  out : e.output = c.output

/-- The step bound of stage A2. -/
def costA2 (m : ℕ) : ℕ := 12 + (46 * (5 * m) + 30 * (5 * m) + 56) + 15 + ((8 + 8) * m + 5) + 5

/-- The first part of stage A2. -/
def msA2a : Stmt := .seq cmSetA (.seq cmSetB StEnc.cmProg)

/-- The second part of stage A2. -/
def msA2b : Stmt := .seq gSetA (.seq gSetB (.seq (wrLoop vG) ggSet))

/-- **Stage A2.** -/
def msA2 : Stmt := .seq msA2a msA2b

set_option maxHeartbeats 2000000 in
/-- **Compact node numbers** (`cmSetA ; cmSetB ; cmProg`). -/
theorem msA2a_exec (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {p : ℕ} (c : Config)
    (hc : WordsBounded W c)
    (hK : StEnc.KInM (cutMap Pa.rev_mem_darts') (StEnc.enEq (cQ h Pa hk))
      (StEnc.ιF _ (cQ h Pa hk)) (StEnc.ιG _ (cQ h Pa hk)) (StEnc.ιV _ (cQ' hM hrot h Pa hk))
      (StEnc.ιE _ (cQ h Pa hk)) c.nmem (p + 41 * m))
    (r28 : c.nreg 8228 = nEc Pa.darts en m)
    (r30 : c.nreg 8230 = nEc Pa.darts en m + nTc M Pa.darts en m)
    (l2 : c.nreg 8282 = p + 41 * m) (l3 : c.nreg 8283 = p + 241 * m + 20)
    (hW : p + 860 * m + 100 ≤ W) :
    ∃ e t, Exec P W msA2a c e t ∧
      t ≤ 12 + (46 * (5 * m) + 30 * (5 * m) + 56) ∧
      ∃ (τv : CutV M Pa.darts ≃ Fin (e.nreg 7957)) (τf : CutF M Pa.darts ≃ Fin (e.nreg 7959)),
      StEnc.KInM (cutMap Pa.rev_mem_darts').dual.dual (StEnc.enEq (cQ h Pa hk))
        (fun x => 1 + (τv x : ℕ)) (StEnc.ιG _ (cQ h Pa hk))
        (fun y => 2 * (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) + 1 + (τf y : ℕ))
        (StEnc.ιE _ (cQ h Pa hk)) e.nmem (p + 41 * m) ∧
      e.nreg 7950 = nEc Pa.darts en m + 4 * nTc M Pa.darts en m ∧
      (∀ a, (a < p + 41 * m + (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) ∨
          p + 41 * m + 6 * (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) ≤ a) →
        (a < p + 241 * m + 20 ∨ p + 246 * m + 20 ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 7920 ∨ 7959 < r) → r ≠ 8264 → r ≠ 8265 → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have h' := enumOK_dual_of hM hrot h (Pa.d 0)
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  set nE := nEc Pa.darts en m with hnEd
  set nT := nTc M Pa.darts en m with hnTd
  obtain ⟨c₁, t₁, e₁, ht₁, a50, a53, aR, am, ar, arm, ao⟩ := cmSetA_exec (P := P) c hc r28 r30
    l2 (by omega)
  have l3' : c₁.nreg 8283 = p + 241 * m + 20 := by
    rw [aR _ (by omega) (by omega) (by omega) (by omega)]; exact l3
  obtain ⟨c₂, t₂, e₂, ht₂, b50, b51, b52, b53, b54, b55, bR, bm, br, brm, bo⟩ :=
    cmSetB_exec (P := P) c₁ e₁.wb_right a50 a53 l3' (by omega)
  have K₀ := kInM_congr (A := cutMap Pa.rev_mem_darts') (B := (cutMap Pa.rev_mem_darts').dual.dual)
    rfl rfl rfl hK
  have hQ := cQ h Pa hk
  have hQ' := cQ' hM hrot h Pa hk
  have hFl := StEnc.fLab_lt hQ
  have hVl := StEnc.fLab_lt hQ'
  obtain ⟨c₃, t₃, e₃, ht₃, τv, τf, K₃, M₃, R₃, rr₃, rm₃, o₃⟩ :=
    StEnc.cmProg_kin (P := P) (Q := (cutMap Pa.rev_mem_darts').dual.dual)
      (StEnc.enEq (cQ h Pa hk)) (ιv := StEnc.ιF _ (cQ h Pa hk)) (ιg := StEnc.ιG _ (cQ h Pa hk))
      (ιf := StEnc.ιV _ (cQ' hM hrot h Pa hk)) (ιe := StEnc.ιE _ (cQ h Pa hk))
      (m := nE + 4 * nT) (β := p + 41 * m) (Rb := p + 241 * m + 20) (E := 4 * (nE + 4 * nT) + 1)
      c₂ e₂.wb_right (by rw [bm, am]; exact K₀)
      (fun x y e => StEnc.fLab_inj hQ (by unfold StEnc.ιF at e; omega))
      (fun x => by unfold StEnc.ιF; omega) (fun x => by unfold StEnc.ιF; have := hFl x; omega)
      (fun x y e => StEnc.fLab_inj hQ' (by unfold StEnc.ιV at e; omega))
      (fun y => by unfold StEnc.ιV; omega)
      (fun y => by unfold StEnc.ιV; have := hVl y; omega)
      (cutTail_surj Pa.rev_mem_darts' h.fsurj) (cutFace_surj Pa.rev_mem_darts' h'.fsurj (fixT0 Pa hk))
      (StEnc.ιE_lt hQ) (by omega) (by omega) (by omega) b50 b51 b52 b53 b54 b55
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, τv, τf, K₃,
    by rw [R₃ _ (by omega), b50], fun a h1 h2 => ?_, fun r h1 h2 h3 => ?_,
    by rw [rr₃, br, ar], by rw [rm₃, brm, arm], by rw [o₃, bo, ao]⟩
  · rw [M₃ a (by omega) (by omega) (by omega), bm, am]
  · rw [R₃ r (by omega), bR r (by omega), aR r (by omega) (by omega) h2 h3]

set_option maxHeartbeats 2000000 in
/-- **The boundary darts** (`gSetA ; gSetB ; wrLoop vG ; ggSet`). -/
theorem msA2b_exec {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k)
    {p nD : ℕ} (c : Config) (hc : WordsBounded W c)
    (r56 : c.nreg 8156 = fixPer M Pa) (r50 : c.nreg 7950 = nD)
    (hnD : nD = nEc Pa.darts en m + 4 * nTc M Pa.darts en m)
    (l2 : c.nreg 8282 = p + 41 * m) (l4 : c.nreg 8284 = p + 246 * m + 20)
    (l9 : c.nreg 8289 = p + 321 * m + 52) (r00 : c.nreg 8000 = m) (r09 : c.nreg 8009 = p)
    (r28 : c.nreg 8228 = nEc Pa.darts en m)
    (r30 : c.nreg 8230 = nEc Pa.darts en m + nTc M Pa.darts en m)
    (tr : ∀ s < fixPer M Pa, c.nmem (p + 6 * m + s) = ixOf en m ((tour M Pa.darts)^[s] (Pa.d 0)))
    (rk : ∀ x < m, c.nmem (p + 14 * m + x) = cT M Pa.darts en x)
    (hW : p + 860 * m + 100 ≤ W) :
    ∃ e t, Exec P W msA2b c e t ∧ t ≤ 15 + ((8 + 8) * m + 5) + 5 ∧
      (∀ i < fixPer M Pa, e.nmem (p + 41 * m + 12 * nD + 1 + i) =
        StEnc.enEq (cQ h Pa hk) (cutG Pa.rev_mem_darts' (fixT0 Pa hk) i)) ∧
      e.nmem (p + 246 * m + 20) = StEnc.enEq (cQ h Pa hk) (cD0 Pa hk) ∧
      e.nmem (p + 246 * m + 20 + 1) = StEnc.enEq (cQ h Pa hk) (cD0 Pa hk) ∧
      (∀ a, (a < p + 41 * m + 12 * nD + 1 ∨ p + 41 * m + 12 * nD + 1 + m ≤ a) →
        (a < p + 321 * m + 52 ∨ p + 321 * m + 52 + m ≤ a) → a ≠ p + 246 * m + 20 →
        a ≠ p + 246 * m + 20 + 1 → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 7320 ∨ 7322 < r) → (r < 8200 ∨ 8219 < r) → r ≠ 8264 → r ≠ 8265 →
        e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have hper := fixPer_le h Pa
  have hpos := fixPer_pos Pa
  obtain ⟨c₄, t₄, e₄, ht₄, g00, g01, g02, gR, gm, gr, grm, go⟩ := gSetA_exec (P := P) c
    hc (per := fixPer M Pa) (nD := nD) (IM := p + 41 * m) (DU := p + 321 * m + 52) r56 r50 l2 l9
    (by omega)
  obtain ⟨c₅, t₅, e₅, ht₅, h20, h21, h22, hR₅, hm₅, hr₅, hrm₅, ho₅⟩ := gSetB_exec (P := P) c₄
    e₄.wb_right (m := m) (p := p) (nE := nEc Pa.darts en m) (nT := nTc M Pa.darts en m) (by rw [gR _ (by omega) (by omega)]; exact r00)
    (by rw [gR _ (by omega) (by omega)]; exact r09) (by rw [gR _ (by omega) (by omega)]; exact r28)
    (by rw [gR _ (by omega) (by omega)]; exact r30) (by omega)
  have tr5 : ∀ i < fixPer M Pa, c₅.nmem (p + 6 * m + i) =
      ixOf en m ((tour M Pa.darts)^[i] (Pa.d 0)) := fun i hi => by rw [hm₅, gm]; exact tr i hi
  have trl : ∀ i < fixPer M Pa, ixOf en m ((tour M Pa.darts)^[i] (Pa.d 0)) < m :=
    fun i _ => ixOf_lt h _
  have rk5 : ∀ x < m, c₅.nmem (p + 14 * m + x) = cT M Pa.darts en x := fun x hx => by
    rw [hm₅, gm]; exact rk x hx
  have cTle : ∀ x, cT M Pa.darts en x ≤ x := fun x => cnt_le_self _ x
  have s00 : c₅.nreg 8200 = fixPer M Pa := by rw [hR₅ _ (by omega) (by omega)]; exact g00
  have s01 : c₅.nreg 8201 = p + 41 * m + 12 * nD + 1 := by
    rw [hR₅ _ (by omega) (by omega)]; exact g01
  have s02 : c₅.nreg 8202 = p + 321 * m + 52 := by rw [hR₅ _ (by omega) (by omega)]; exact g02
  obtain ⟨c₆, t₆, e₆, ht₆, w6, wm6, wm6', wR6, wr6, wrm6, wo6⟩ := wrLoop_exec (P := P) c₅
    e₅.wb_right (VAL := vG) (B := 8) (m := fixPer M Pa) (N := m) s00 s01 s02
    (vG_spec (P := P) c₅ h20 h21 h22
      (fun i hi => ⟨Or.inl (by omega), Or.inl (by omega)⟩)
      (fun i hi => by
        rw [tr5 i hi]; have := trl i hi
        exact ⟨Or.inl (by omega), Or.inl (by omega)⟩)
      (fun i hi => by
        rw [tr5 i hi]; have := trl i hi
        rw [rk5 _ this]; have := cTle (ixOf en m ((tour M Pa.darts)^[i] (Pa.d 0)))
        exact ⟨by omega, by omega, by omega⟩) (by omega) (by omega))
    (fun i hi _ => by omega) (fun i hi i' hi' _ _ e => e) (Or.inl (by omega)) (by omega)
    (by omega) (by omega)
  have l4' : c₆.nreg 8284 = p + 246 * m + 20 := by
    rw [wR6 _ (by omega), hR₅ _ (by omega) (by omega), gR _ (by omega) (by omega)]; exact l4
  obtain ⟨c₇, t₇, e₇, ht₇, gm7, gR7, gr7, grm7, go7⟩ := ggSet_exec (P := P) c₆ e₆.wb_right
    (Gb := p + 41 * m + 12 * nD + 1) (GG := p + 246 * m + 20)
    (by rw [wR6 _ (by omega)]; exact s01) l4' (by omega)
  have val : ∀ i < fixPer M Pa, c₆.nmem (p + 41 * m + 12 * nD + 1 + i) =
      StEnc.enEq (cQ h Pa hk) (cutG Pa.rev_mem_darts' (fixT0 Pa hk) i) := fun i hi => by
    rw [(w6 i hi rfl).1, tr5 i hi, rk5 _ (trl i hi), enEq_cut Pa.rev_mem_darts' h (cD0 Pa hk)]
    show _ = nEc Pa.darts en m + 2 * nTc M Pa.darts en m +
      cT M Pa.darts en (ixOf en m ((tourT Pa.rev_mem_darts')^[i] (fixT0 Pa hk)).1)
    rw [tourT_iterate_val]; rfl
  have v0 := val 0 hpos
  rw [Nat.add_zero] at v0
  refine ⟨c₇, t₄ + (t₅ + (t₆ + t₇)), .seq e₄ (.seq e₅ (.seq e₆ e₇)), ?_, fun i hi => ?_, ?_, ?_,
    fun a h1 h2 h3 h4 => ?_, fun r h1 h2 h3 h4 => ?_, by rw [gr7, wr6, hr₅, gr],
    by rw [grm7, wrm6, hrm₅, grm], by rw [go7, wo6, ho₅, go]⟩
  · have : t₆ ≤ (8 + 8) * m + 5 := by
      have : (8 + 8) * fixPer M Pa ≤ (8 + 8) * m := Nat.mul_le_mul_left _ hper
      omega
    omega
  · rw [gm7, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact val i hi
  · rw [gm7, upd_other _ _ _ (by omega), upd_same, v0]
  · rw [gm7, upd_same, v0]
  · rw [gm7, upd_other _ _ _ h4, upd_other _ _ _ h3, wm6 a h1 h2, hm₅, gm]
  · rw [gR7 r h3 h4, wR6 r (by omega), hR₅ r h1 h3, gR r (by omega) h3]

set_option maxHeartbeats 2000000 in
/-- **Stage A2 on the machine.** -/
theorem msA2_exec (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {p q : ℕ} (c₀ c : Config)
    (hc : WordsBounded W c) (hA : StA1 hM hrot h Pa hk p q c₀ c)
    (hm : c.nreg 8000 = m) (hp : c.nreg 8009 = p)
    (hW : p + 860 * m + 100 + 2 * q ≤ W) :
    ∃ e t nF nV, ∃ (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV),
      Exec P W msA2 c e t ∧ t ≤ costA2 m ∧ StA hM hrot h Pa hk p q c₀ e τv τf := by
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  have lay := hA.lay
  have l2 : c.nreg 8282 = p + 41 * m := lay 2 (by omega)
  have l3 : c.nreg 8283 = p + 241 * m + 20 := lay 3 (by omega)
  have l4 : c.nreg 8284 = p + 246 * m + 20 := lay 4 (by omega)
  have l9 : c.nreg 8289 = p + 321 * m + 52 := lay 9 (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, τv, τf, K₃, c50, M₃, R₃, rr₃, rm₃, o₃⟩ :=
    msA2a_exec (P := P) hM hrot h Pa hk c hc hA.kin hA.r28 hA.r30 l2 l3 (by omega)
  have q3 : ∀ r, (8000 ≤ r ∧ r ≤ 8009) ∨ (8150 ≤ r ∧ r ≤ 8299 ∧ r ≠ 8264 ∧ r ≠ 8265) →
      c₃.nreg r = c.nreg r := fun r hr => R₃ r (by omega) (by omega) (by omega)
  have mem3 : ∀ a, a < p + 41 * m → c₃.nmem a = c.nmem a := fun a ha =>
    M₃ a (by omega) (by omega)
  obtain ⟨c₇, t₇, e₇, ht₇, gv, g0, g1, M₇, R₇, rr₇, rm₇, o₇⟩ :=
    msA2b_exec (P := P) h Pa hk (nD := nEc Pa.darts en m + 4 * nTc M Pa.darts en m) c₃
    e₃.wb_right (by rw [q3 _ (by omega)]; exact hA.per) c50 rfl (by rw [q3 _ (by omega)]; exact l2)
    (by rw [q3 _ (by omega)]; exact l4) (by rw [q3 _ (by omega)]; exact l9)
    (by rw [q3 _ (by omega)]; exact hm) (by rw [q3 _ (by omega)]; exact hp)
    (by rw [q3 _ (by omega)]; exact hA.r28) (by rw [q3 _ (by omega)]; exact hA.r30)
    (fun s hs => by have := fixPer_le h Pa; rw [mem3 _ (by omega)]; exact hA.tr s hs)
    (fun x hx => by rw [mem3 _ (by omega)]; exact (hA.rk x hx).2) (by omega)
  have q7 : ∀ r, (r < 7320 ∨ 7959 < r) → (r < 8200 ∨ 8219 < r) → r ≠ 8264 → r ≠ 8265 →
      c₇.nreg r = c.nreg r := fun r a1 a2 a3 a4 => by
    rw [R₇ r (by omega) a2 a3 a4, R₃ r (by omega) a3 a4]
  have mem7 : ∀ a, a < p + 41 * m → c₇.nmem a = c.nmem a := fun a ha => by
    rw [M₇ a (by omega) (by omega) (by omega) (by omega), mem3 a ha]
  refine ⟨c₇, t₃ + t₇, c₃.nreg 7957, c₃.nreg 7959, τv, τf, Exec.seq e₃ e₇, ?_, ?_⟩
  · unfold costA2; omega
  · have hper := fixPer_le h Pa
    refine ⟨fun j hj => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun s hs => ?_, fun i hi => ?_,
      fun i hi => ?_, fun r hr => ?_, fun i hi hf => ?_, fun i hi => ?_, ?_, gv, g0, g1,
      fun a h1 h2 => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
    · rw [q7 _ (by omega) (by omega) (by omega) (by omega)]; exact lay j hj
    · rw [q7 _ (by omega) (by omega) (by omega) (by omega)]; exact hA.per
    · rw [q7 _ (by omega) (by omega) (by omega) (by omega)]; exact hA.ncl
    · rw [q7 _ (by omega) (by omega) (by omega) (by omega)]; exact hA.r28
    · rw [q7 _ (by omega) (by omega) (by omega) (by omega)]; exact hA.r30
    · rw [R₇ _ (by omega) (by omega) (by omega) (by omega)]; exact c50
    · rw [R₇ _ (by omega) (by omega) (by omega) (by omega)]
    · rw [R₇ _ (by omega) (by omega) (by omega) (by omega)]
    · rw [mem7 _ (by omega)]; exact hA.tr s hs
    · rw [mem7 _ (by omega)]; exact hA.fl i hi
    · rw [mem7 _ (by omega)]; exact hA.lf i hi
    · have := fixCornerL_le h Pa
      rw [mem7 _ (by omega), mem7 _ (by omega)]; exact hA.cs r hr
    · obtain ⟨r, hr, e1, e2⟩ := hA.cn i hi hf
      have hl := NsStep.labI_lt (M := M) h hi
      exact ⟨r, hr, by rw [mem7 _ (by omega)]; exact e1, e2⟩
    · rw [mem7 _ (by omega), mem7 _ (by omega)]; exact hA.rk i hi
    · refine kInM_frame K₃ (E := 4 * (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) + 1)
        (StEnc.ιE_lt (cQ h Pa hk)) fun a h1 h2 => ?_
      simp only [aIM] at h1 h2
      exact M₇ a (by omega) (by omega) (by omega) (by omega)
    · simp only [aGG, aDU] at h1 h2
      rw [M₇ a (by omega) (by omega) (by omega) (by omega), M₃ a (by omega) (by omega)]
      exact hA.mem a (by unfold aIM; omega)
    · simp only [EScr] at hr
      rw [q7 r (by omega) (by omega) (by omega) (by omega)]
      exact hA.reg r (by simp only [EScr]; omega)
    · rw [rr₇, rr₃]; exact hA.rr
    · rw [rm₇, rm₃]; exact hA.rm
    · rw [o₇, o₃]; exact hA.out

end MsEnc

end BKMNW

end PlanarFlow
