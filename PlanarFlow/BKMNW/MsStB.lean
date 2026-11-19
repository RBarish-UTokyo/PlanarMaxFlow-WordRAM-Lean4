module

public import PlanarFlow.BKMNW.MsStA2
public import PlanarFlow.BKMNW.StIsoM

/-!
# The MSSP encoder, stage B1–B2: the isolating weight and the lengths of the copies

* `card_cutV_le` (`#CutV ≤ 2m`), `card_cutF_le` (`#CutF ≤ 2m + 1`), `cut_isPlane`;
* **`msB1`** `= bSetA1 ; bSetA2 ; ivProg`: a tree `C : DTree Q.dual` of the cut (`Q.dual =
  (cutMap hL).dual.dual`) rooted at the face of the ring, with `WM[σ d] = #CutF + treeW C d` at
  `aWM` (`StEnc.ivProg_exec` on `Q`); **`msB1_exec`**;
* **`msB2`** `= bSetB ; mzFill ; bSetC ; wrLoop vCL`: `CL` zeroed, then `CL[RE[i]] := LEN[i]` for
  the darts off the path; **`msB2_exec`**.
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

/-! ### Sizes -/

lemma card_cutV_le {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (L : List D) :
    Fintype.card (CutV M L) ≤ 2 * m := by
  have hF : Fintype.card F ≤ m := by
    rw [← StEnc.card_eq h]
    exact Fintype.card_le_of_surjective M.face fun f => h.fsurj f
  have hT : Fintype.card (CutT M L) ≤ m := by
    rw [← StEnc.card_eq h]; exact Fintype.card_subtype_le _
  simp only [CutV, Fintype.card_sum]; omega

lemma card_cutF_le (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (L : List D) (d₀ : D) : Fintype.card (CutF M L) ≤ 2 * m + 1 := by
  have h' := enumOK_dual_of hM hrot h d₀
  have hV : Fintype.card V ≤ m := by
    rw [← StEnc.card_eq h]
    exact Fintype.card_le_of_surjective M.tail fun v => h'.fsurj v
  have hT : Fintype.card (CutT M L) ≤ m := by
    rw [← StEnc.card_eq h]; exact Fintype.card_subtype_le _
  have hS : Fintype.card {v : V // v ∉ cutS M L} ≤ m := (Fintype.card_subtype_le _).trans hV
  simp only [CutF, Fintype.card_sum, Fintype.card_unit]; omega

theorem cut_isPlane (hM : M.IsPlane) (hrot : M.RotTrans) (Pa : SPath M) (hk : 0 < Pa.k) :
    (cutMap Pa.rev_mem_darts').IsPlane :=
  (fixCut hM hrot Pa hk 0 fun _ _ => le_rfl).hyp.plane

variable {P : Input} {W : ℕ}

/-! ### B1: the isolating weight -/

def bSetA1 : Stmt :=
  block [.addN 7961 8282 7950, .copyN 7960 7950, .copyN 7962 8282, .addN 7963 7950 7950,
    .constN 8264 1, .addN 7963 7963 8264, .copyN 7964 7959, .copyN 7965 8284]

def bSetA2 : Stmt := block [.copyN 7966 8285, .copyN 7967 8286, .copyN 7968 7959]

def msB1 : Stmt := .seq bSetA1 (.seq bSetA2 StEnc.ivProg)

theorem bSetA1_exec (c : Config) (hc : WordsBounded W c) {nD IM nV GG : ℕ}
    (r50 : c.nreg 7950 = nD) (r82 : c.nreg 8282 = IM) (r59 : c.nreg 7959 = nV)
    (r84 : c.nreg 8284 = GG) (hw : IM + 2 * nD + 1 ≤ W) :
    ∃ c' t, Exec P W bSetA1 c c' t ∧ t = 8 ∧ c'.nreg 7960 = nD ∧ c'.nreg 7961 = IM + nD ∧
      c'.nreg 7962 = IM ∧ c'.nreg 7963 = 2 * nD + 1 ∧ c'.nreg 7964 = nV ∧ c'.nreg 7965 = GG ∧
      (∀ r, (r < 7960 ∨ 7965 < r) → r ≠ 8264 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSetA1
  exec_block
  all_goals try ((try config_simp); (try simp only [r50, r82, r59, r84]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r50, r82, r59, r84]; omega)
    | (simp only [r50, r82, r59, r84]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem bSetA2_exec (c : Config) (hc : WordsBounded W c) {Z Wb nV : ℕ}
    (r85 : c.nreg 8285 = Z) (r86 : c.nreg 8286 = Wb) (r59 : c.nreg 7959 = nV) :
    ∃ c' t, Exec P W bSetA2 c c' t ∧ t = 3 ∧ c'.nreg 7966 = Z ∧ c'.nreg 7967 = Wb ∧
      c'.nreg 7968 = nV ∧ (∀ r, (r < 7966 ∨ 7968 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSetA2
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r85, r86, r59]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

set_option maxHeartbeats 2000000 in
/-- **The isolating weight of the cut.** -/
theorem msB1_exec (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ}
    (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k) {p q nF nV : ℕ}
    (τv : CutV M Pa.darts ≃ Fin nF) (τf : CutF M Pa.darts ≃ Fin nV) (c₀ c : Config)
    (hc : WordsBounded W c) (hA : StA hM hrot h Pa hk p q c₀ c τv τf)
    (hW : p + 860 * m + 100 + 2 * q ≤ W) :
    ∃ e t, ∃ C : STFlow.DTree (cutMap Pa.rev_mem_darts').dual.dual,
      Exec P W msB1 c e t ∧ t ≤ 11 + StEnc.ivCost (5 * m) (2 * m + 1) ∧
      C.root = (cutMap Pa.rev_mem_darts').dual.tail (cD0 Pa hk) ∧
      (∀ d, (e.nmem (aWM m p + StEnc.enEq (cQ h Pa hk) d) : ℤ) = nV + MSSP.treeW C d) ∧
      (∀ a, (a < aZi m p ∨ aZi m p + 60 * m + 30 ≤ a) →
        (a < aWM m p ∨ aWM m p + (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) ≤ a) →
        e.nmem a = c.nmem a) ∧
      (∀ r, (r < 1400 ∨ 8000 ≤ r) → r ≠ 8264 → r ≠ 8265 → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  set nD := nEc Pa.darts en m + 4 * nTc M Pa.darts en m with hnD
  have hcF : nV ≤ 2 * m + 1 := by
    have := card_cutF_le hM hrot h Pa.darts (Pa.d 0)
    rw [Fintype.card_congr τf, Fintype.card_fin] at this; exact this
  have lay := hA.lay
  have l2 : c.nreg 8282 = p + 41 * m := lay 2 (by omega)
  have l4 : c.nreg 8284 = p + 246 * m + 20 := lay 4 (by omega)
  have l5 : c.nreg 8285 = p + 246 * m + 22 := lay 5 (by omega)
  have l6 : c.nreg 8286 = p + 306 * m + 52 := lay 6 (by omega)
  obtain ⟨c₁, t₁, e₁, ht₁, a60, a61, a62, a63, a64, a65, aR, am, ar, arm, ao⟩ :=
    bSetA1_exec (P := P) c hc (nD := nD) (IM := p + 41 * m) (nV := nV)
      (GG := p + 246 * m + 20) hA.r50 l2 hA.r59 l4 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b66, b67, b68, bR, bm, br, brm, bo⟩ :=
    bSetA2_exec (P := P) c₁ e₁.wb_right (Z := p + 246 * m + 22) (Wb := p + 306 * m + 52) (nV := nV)
      (by rw [aR _ (by omega) (by omega)]; exact l5) (by rw [aR _ (by omega) (by omega)]; exact l6)
      (by rw [aR _ (by omega) (by omega)]; exact hA.r59)
  have mc₂ : c₂.nmem = c.nmem := by rw [bm, am]
  have : Nonempty (CutD M Pa.darts) := ⟨cD0 Pa hk⟩
  have hQp : (cutMap Pa.rev_mem_darts').dual.IsPlane := (cut_isPlane hM hrot Pa hk).dual
  obtain ⟨c₃, t₃, e₃, ht₃, C, hC, hW₃, M₃, R₃, rr₃, rm₃, o₃⟩ :=
    StEnc.ivProg_exec (P := P) (M := (cutMap Pa.rev_mem_darts').dual) hQp
      (StEnc.enEq (cQ h Pa hk)) τf (cD0 Pa hk) (NFb := p + 41 * m + nD) (RVb := p + 41 * m)
      (of := 2 * nD + 1) (Gp := p + 246 * m + 20) (Z := p + 246 * m + 22)
      (Wb := p + 306 * m + 52) (B := nV) c₂ e₂.wb_right
      (by rw [bR _ (by omega)]; exact a60) (by rw [bR _ (by omega)]; exact a61)
      (by rw [bR _ (by omega)]; exact a62) (by rw [bR _ (by omega)]; exact a63)
      (by rw [bR _ (by omega)]; exact a64) (by rw [bR _ (by omega)]; exact a65) b66 b67 b68
      (fun d => by
        rw [mc₂]; have := hA.kin.nf d; simp only [Klein.iNF] at this; exact this)
      (fun d => by
        rw [mc₂]; have := hA.kin.rv d; simp only [Klein.iRV, Nat.add_zero] at this; exact this)
      (by rw [mc₂]; exact hA.gg0) (by omega) (by omega) (by omega) (Or.inr (by omega))
      (Or.inr (by omega)) (by rw [Fintype.card_congr τf, Fintype.card_fin])
      (by rw [Fintype.card_congr τf, Fintype.card_fin]; omega) (by omega) (by omega) (by omega)
  refine ⟨c₃, t₁ + (t₂ + t₃), C, .seq e₁ (.seq e₂ e₃), ?_, hC, fun d => hW₃ d,
    fun a h1 h2 => ?_, fun r h1 h2 h3 => ?_, by rw [rr₃, br, ar], by rw [rm₃, brm, arm],
    by rw [o₃, bo, ao]⟩
  · unfold StEnc.ivCost at ht₃ ⊢; omega
  · rw [M₃ a (by unfold aZi at h1; omega) (by unfold aWM at h2; omega), mc₂]
  · rw [R₃ r (by omega), bR r (by omega), aR r (by omega) h2]

/-! ### B2: the lengths of the copies -/

def bSetB : Stmt := block [.copyN 5030 7950, .copyN 5031 8287]

def bSetC1 : Stmt :=
  block [.copyN 8200 8000, .copyN 8201 8287, .copyN 8202 8289, .constN 8264 2,
    .mulN 7323 8000 8264, .addN 7323 7323 8009, .constN 8264 13, .mulN 7324 8000 8264]

def bSetC2 : Stmt := block [.addN 7324 7324 8009, .copyN 7325 8005]

def msB2 : Stmt := .seq bSetB (.seq mzFill (.seq bSetC1 (.seq bSetC2 (wrLoop vCL))))

theorem bSetB_exec (c : Config) (hc : WordsBounded W c) {nD CL : ℕ}
    (r50 : c.nreg 7950 = nD) (r87 : c.nreg 8287 = CL) :
    ∃ c' t, Exec P W bSetB c c' t ∧ t = 2 ∧ c'.nreg 5030 = nD ∧ c'.nreg 5031 = CL ∧
      (∀ r, r ≠ 5030 → r ≠ 5031 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSetB
  exec_block
  all_goals try ((try config_simp); omega)
  refine ⟨rfl, ?_, ?_, fun r a b => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r50, r87]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem bSetC1_exec (c : Config) (hc : WordsBounded W c) {m p CL DU : ℕ}
    (r00 : c.nreg 8000 = m) (r09 : c.nreg 8009 = p) (r87 : c.nreg 8287 = CL)
    (r89 : c.nreg 8289 = DU) (hw : p + 13 * m + 13 ≤ W) :
    ∃ c' t, Exec P W bSetC1 c c' t ∧ t = 8 ∧ c'.nreg 8200 = m ∧ c'.nreg 8201 = CL ∧
      c'.nreg 8202 = DU ∧ c'.nreg 7323 = p + 2 * m ∧ c'.nreg 7324 = 13 * m ∧
      (∀ r, (r < 7323 ∨ 7324 < r) → (r < 8200 ∨ 8202 < r) → r ≠ 8264 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSetC1
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r09]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r00, r09, r87, r89]; omega)
    | (simp only [r00, r09, r87, r89]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

theorem bSetC2_exec (c : Config) (hc : WordsBounded W c) {m p Lb : ℕ}
    (r24 : c.nreg 7324 = 13 * m) (r09 : c.nreg 8009 = p) (r05 : c.nreg 8005 = Lb)
    (hw : p + 13 * m ≤ W) :
    ∃ c' t, Exec P W bSetC2 c c' t ∧ t = 2 ∧ c'.nreg 7324 = p + 13 * m ∧ c'.nreg 7325 = Lb ∧
      (∀ r, (r < 7324 ∨ 7325 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold bSetC2
  exec_block
  all_goals try ((try config_simp); (try simp only [r24, r09]); omega)
  refine ⟨rfl, ?_, ?_, fun r a => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r24, r09, r05]; omega)
    | (simp only [r24, r09, r05]; done)
    | (simp only [upd_apply]; split_ifs <;> first | omega | rfl)

set_option maxHeartbeats 2000000 in
/-- **The lengths of the copies** in `CL` (zero elsewhere). -/
theorem msB2_exec {en : ℕ → D} {m : ℕ} (Pa : SPath M) {p Lb nD CL DU : ℕ} (c : Config)
    (hc : WordsBounded W c) (r00 : c.nreg 8000 = m) (r05 : c.nreg 8005 = Lb)
    (r09 : c.nreg 8009 = p) (r50 : c.nreg 7950 = nD) (r87 : c.nreg 8287 = CL)
    (r89 : c.nreg 8289 = DU) (hnD : nEc Pa.darts en m ≤ nD)
    (lf : ∀ i < m, c.nmem (p + 2 * m + i) = if en i ∈ Pa.darts then 1 else 0)
    (re : ∀ i < m, c.nmem (p + 13 * m + i) = cE Pa.darts en i)
    (lLb : Lb + m ≤ p) (lCL : p + 14 * m ≤ CL) (lDU : CL + nD ≤ DU) (hW : DU + nD + 13 ≤ W)
    (hW' : p + 13 * m + 13 ≤ W) :
    ∃ e t, Exec P W msB2 c e t ∧ t ≤ 12 + 5 * nD + 5 + (8 + 8) * m + 5 ∧
      (∀ i < m, en i ∉ Pa.darts → e.nmem (CL + cE Pa.darts en i) = c.nmem (Lb + i)) ∧
      (∀ j < nD, (∀ i < m, en i ∉ Pa.darts → cE Pa.darts en i ≠ j) → e.nmem (CL + j) = 0) ∧
      (∀ a, (a < CL ∨ CL + nD ≤ a) → (a < DU ∨ DU + nD ≤ a) → e.nmem a = c.nmem a) ∧
      (∀ r, (r < 5030 ∨ 5035 < r) → (r < 7323 ∨ 7325 < r) → (r < 8200 ∨ 8219 < r) →
        r ≠ 8264 → e.nreg r = c.nreg r) ∧
      e.rreg = c.rreg ∧ e.rmem = c.rmem ∧ e.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a30, a31, aR, am, ar, arm, ao⟩ := bSetB_exec (P := P) c hc r50 r87
  obtain ⟨c₂, t₂, e₂, ht₂, z0, zM, zR, zr, zrm, zo⟩ := mzFill_exec (P := P) c₁ e₁.wb_right a30 a31
    (by omega) (by omega)
  have q2 : ∀ r, 5035 < r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [zR r (by omega), aR r (by omega) (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, s00, s01, s02, s23, s24, sR, sm, sr, srm, so⟩ :=
    bSetC1_exec (P := P) c₂ e₂.wb_right (m := m) (p := p) (CL := CL) (DU := DU)
      (by rw [q2 _ (by omega)]; exact r00) (by rw [q2 _ (by omega)]; exact r09)
      (by rw [q2 _ (by omega)]; exact r87) (by rw [q2 _ (by omega)]; exact r89) hW'
  have r09' : c₃.nreg 8009 = p :=
    ((sR 8009 (by omega) (by omega) (by omega)).trans (q2 8009 (by omega))).trans r09
  have r05' : c₃.nreg 8005 = Lb :=
    ((sR 8005 (by omega) (by omega) (by omega)).trans (q2 8005 (by omega))).trans r05
  obtain ⟨c₄, t₄, e₄, ht₄, u24, u25, uR, um, ur, urm, uo⟩ :=
    bSetC2_exec (P := P) c₃ e₃.wb_right (m := m) (p := p) (Lb := Lb) s24 r09' r05' (by omega)
  have v00 : c₄.nreg 8200 = m := (uR 8200 (by omega)).trans s00
  have v01 : c₄.nreg 8201 = CL := (uR 8201 (by omega)).trans s01
  have v02 : c₄.nreg 8202 = DU := (uR 8202 (by omega)).trans s02
  have v23 : c₄.nreg 7323 = p + 2 * m := (uR 7323 (by omega)).trans s23
  have mem4 : ∀ a, (a < CL ∨ CL + nD ≤ a) → c₄.nmem a = c.nmem a := fun a ha => by
    rw [um, sm, zM a ha, am]
  have lf4 : ∀ i < m, c₄.nmem (p + 2 * m + i) = if en i ∈ Pa.darts then 1 else 0 :=
    fun i hi => by rw [mem4 _ (by omega)]; exact lf i hi
  have re4 : ∀ i < m, c₄.nmem (p + 13 * m + i) = cE Pa.darts en i := fun i hi => by
    rw [mem4 _ (by omega)]; exact re i hi
  have hcE : ∀ i < m, en i ∉ Pa.darts → cE Pa.darts en i < nEc Pa.darts en m :=
    fun i hi hn => cnt_lt _ hi hn
  have sel : ∀ i < m, (c₄.nmem (p + 2 * m + i) = 0) ↔ en i ∉ Pa.darts := fun i hi => by
    rw [lf4 i hi]; split_ifs with hh <;> simp [hh]
  obtain ⟨c₅, t₅, e₅, ht₅, w5, wm5, wm5', wR5, wr5, wrm5, wo5⟩ := wrLoop_exec (P := P) c₄
    e₄.wb_right (VAL := vCL) (B := 8) (m := m) (RVo := CL) (RTo := DU) (N := nD)
    v00 v01 v02
    (vCL_spec (P := P) c₄ (LFb := p + 2 * m) (REb := p + 13 * m) (Lb := Lb) v23 u24 u25
      (fun i hi X hX => by rcases hX with rfl | rfl | rfl <;> constructor <;> omega)
      (fun i hi => by rw [lf4 i hi]; split_ifs <;> omega) ⟨by omega, by omega, by omega⟩
      (by omega))
    (fun i hi hs => by
      have := (sel i hi).1 (by simpa using hs)
      rw [re4 i hi]; have := hcE i hi this; omega)
    (fun i hi i' hi' hs hs' e => by
      have a1 := (sel i hi).1 (by simpa using hs)
      have a2 := (sel i' hi').1 (by simpa using hs')
      rw [re4 i hi, re4 i' hi'] at e
      exact cnt_inj (fun j => en j ∉ Pa.darts) a1 a2 e)
    (Or.inl lDU) (by omega) (by omega) (by omega)
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    fun i hi hn => ?_, fun j hj hne => ?_, fun a h1 h2 => ?_, fun r h1 h2 h3 h4 => ?_,
    by rw [wr5, ur, sr, zr, ar], by rw [wrm5, urm, srm, zrm, arm], by rw [wo5, uo, so, zo, ao]⟩
  · have hs : decide (c₄.nmem (p + 2 * m + i) = 0) = true := by simpa using (sel i hi).2 hn
    have := (w5 i hi hs).1
    rw [re4 i hi] at this
    rw [this, mem4 _ (by omega)]
  · rw [wm5' _ (fun i hi hs => ?_), um, sm, z0 j hj]
    have hn := (sel i hi).1 (by simpa using hs)
    rw [re4 i hi]
    have := hne i hi hn
    constructor <;> omega
  · rw [wm5 a h1 h2, mem4 a h1]
  · rw [wR5 r (by omega), uR r (by omega), sR r (by omega) (by omega) h4, zR r (by omega), aR r (by omega) (by omega)]

end MsEnc

end BKMNW

end PlanarFlow
