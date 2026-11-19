module

public import PlanarFlow.BKMNW.NsMath
public import PlanarFlow.BKMNW.NsOut

/-!
# The negSSSP step of a call as one program: the program and its first stage

**`nsPrep`** writes, from the dart order of a map `M` (index arrays `RV` of the reverse, `RT` of
the rotation, lengths `LN = ℓ + K`), the input part `InP` of the root frame of the negative-length
shortest paths on `M.dual` for the identifiers `nsIds` at `A`, using a scratch region `[S, S +
9 m + 1 + tsz m)` of zero memory, which it leaves zero again. **`negStep`** `= nsPrep ; negCallH`.

Layout (registers `7510 … 7519`): `NX = S` (face permutation, then first returns), `PR = S + m`
(its inverse), `LAB = S + 2m`, `DF = S + 3m`, `KEEP = S + 4m`, `MLN = S + 5m`, `POS = S + 6m`,
`CD = S + 7m` (`m + 1` cells), `Z0 = S + 8m + 1` (zeros), the table `T = S + 9m + 1`; `7520 = m+1`,
`7521 = 2K`, `7522 = 1`.

Stage A (`nsA`, **`nsA_exec`**): the layout, `NX[i] := RT[RV[i]]` (`lgProg`, the face permutation
`phiI`), `PR[NX[i]] := i` (`lsProg`, its inverse), `LAB` (`olProg`, the labels `labI + 1`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset Function Equiv Orbit CombMap NegSSSP NegSSSP.Frame OrbLab WordRAM WordRAM.Machine
  WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The program -/

/-- The layout registers. -/
def nsLay : Stmt := block [.constN 7522 1, .addN 7520 7500 7522, .addN 7521 7504 7504,
  .copyN 7510 7505, .addN 7511 7510 7500, .addN 7512 7511 7500, .addN 7513 7512 7500,
  .addN 7514 7513 7500, .addN 7515 7514 7500, .addN 7516 7515 7500, .addN 7517 7516 7500,
  .addN 7518 7517 7500, .addN 7518 7518 7522, .addN 7519 7518 7500]

/-- The face permutation: `NX[i] := RT[RV[i]]`. -/
def nsG : Stmt :=
  .seq (block [.copyN 6210 7500, .copyN 6211 7501, .copyN 6212 7502, .copyN 6213 7510]) lgProg

/-- Its inverse: `PR[NX[i]] := i`. -/
def nsS : Stmt := .seq (block [.copyN 6220 7500, .copyN 6221 7510, .copyN 6222 7518,
  .constN 6223 1, .copyN 6224 7511]) lsProg

/-- The labels. -/
def nsO : Stmt := .seq (block [.copyN 7350 7510, .copyN 7351 7512, .copyN 7352 7500]) olProg

/-- Stage A. -/
def nsA : Stmt := .seq (.seq nsLay nsG) (.seq nsS nsO)

/-- The deletion flags `DF[i] := 1 - POS[i]`. -/
def nsM : Stmt := .seq (block [.copyN 6230 7500, .copyN 6231 7516, .copyN 6232 7518,
  .copyN 6233 7513]) lmProg

/-- The first returns. -/
def nsD : Stmt := .seq (block [.copyN 6240 7500, .copyN 6241 7513, .copyN 6242 7510,
  .copyN 6243 7511]) ldProg

/-- Clearing the scratch arrays `[S, T)`. -/
def nsZ : Stmt := .seq (block [.subN 5030 7519 7505, .copyN 5031 7505]) mzFill

/-- The arguments of the call. -/
def nsF : Stmt := block [.copyN 7325 7506, .copyN 7326 7500]

/-- **The preparation of the call**: the root frame's input part at `A`. -/
def nsPrep : Stmt := .seq nsA (.seq (.seq tbProg (.seq nmProg (.seq nsM nsD)))
  (.seq wrProg (.seq nsZ nsF)))

/-- **The negSSSP step of a call**: the preparation, then the in-place call. -/
def negStep : Stmt := .seq nsPrep MfDrv.negCallH

/-- The registers written by `nsPrep`. -/
def NsScr (r : ℕ) : Prop :=
  (6210 ≤ r ∧ r ≤ 6250) ∨ (7350 ≤ r ∧ r ≤ 7352) ∨ (7400 ≤ r ∧ r ≤ 7405) ∨
    (5030 ≤ r ∧ r ≤ 5036) ∨ (7510 ≤ r ∧ r ≤ 7556) ∨ r = 7325 ∨ r = 7326

/-! ### Stage A -/

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

variable {P : Input} {W : ℕ}

/-- The layout registers after `nsLay`. -/
def LayRegs (c : Config) (m K S : ℕ) : Prop :=
  c.nreg 7510 = S ∧ c.nreg 7511 = S + m ∧ c.nreg 7512 = S + 2 * m ∧ c.nreg 7513 = S + 3 * m ∧
    c.nreg 7514 = S + 4 * m ∧ c.nreg 7515 = S + 5 * m ∧ c.nreg 7516 = S + 6 * m ∧
    c.nreg 7517 = S + 7 * m ∧ c.nreg 7518 = S + 8 * m + 1 ∧ c.nreg 7519 = S + 9 * m + 1 ∧
    c.nreg 7520 = m + 1 ∧ c.nreg 7521 = 2 * K ∧ c.nreg 7522 = 1

lemma LayRegs.of {c d : Config} {m K S : ℕ} (h : LayRegs c m K S)
    (hd : ∀ r, 7510 ≤ r → r ≤ 7522 → d.nreg r = c.nreg r) : LayRegs d m K S := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨by rw [hd _ (by omega) (by omega), a0], by rw [hd _ (by omega) (by omega), a1],
    by rw [hd _ (by omega) (by omega), a2], by rw [hd _ (by omega) (by omega), a3],
    by rw [hd _ (by omega) (by omega), a4], by rw [hd _ (by omega) (by omega), a5],
    by rw [hd _ (by omega) (by omega), a6], by rw [hd _ (by omega) (by omega), a7],
    by rw [hd _ (by omega) (by omega), a8], by rw [hd _ (by omega) (by omega), a9],
    by rw [hd _ (by omega) (by omega), a10], by rw [hd _ (by omega) (by omega), a11],
    by rw [hd _ (by omega) (by omega), a12]⟩

theorem nsLay_exec (c : Config) (hc : WordsBounded W c) {m K S : ℕ} (r00 : c.nreg 7500 = m)
    (r04 : c.nreg 7504 = K) (r05 : c.nreg 7505 = S) (w1 : S + 9 * m + 1 ≤ W) (w2 : 2 * K ≤ W)
    (w3 : m + 1 ≤ W) :
    ∃ c' t, Exec P W nsLay c c' t ∧ t = 14 ∧ LayRegs c' m K S ∧
      (∀ r, (r < 7510 ∨ 7522 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nsLay
  exec_block
  all_goals try ((try config_simp); (try simp only [r00, r04, r05]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_, rfl, rfl,
    rfl, rfl⟩
  all_goals try (config_simp; simp only [r00, r04, r05]; try omega)
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

/-- A block setting registers from registers. -/
theorem setG_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.copyN 6210 7500, .copyN 6211 7501, .copyN 6212 7502,
      .copyN 6213 7510]) c c' t ∧ t = 4 ∧ c'.nreg 6210 = c.nreg 7500 ∧
      c'.nreg 6211 = c.nreg 7501 ∧ c'.nreg 6212 = c.nreg 7502 ∧ c'.nreg 6213 = c.nreg 7510 ∧
      (∀ r, (r < 6210 ∨ 6213 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

theorem setS_exec (c : Config) (hc : WordsBounded W c) (hW : 1 ≤ W) :
    ∃ c' t, Exec P W (block [.copyN 6220 7500, .copyN 6221 7510, .copyN 6222 7518,
      .constN 6223 1, .copyN 6224 7511]) c c' t ∧ t = 5 ∧ c'.nreg 6220 = c.nreg 7500 ∧
      c'.nreg 6221 = c.nreg 7510 ∧ c'.nreg 6222 = c.nreg 7518 ∧ c'.nreg 6223 = 1 ∧
      c'.nreg 6224 = c.nreg 7511 ∧
      (∀ r, (r < 6220 ∨ 6224 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

theorem setO_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W (block [.copyN 7350 7510, .copyN 7351 7512, .copyN 7352 7500]) c c' t ∧
      t = 3 ∧ c'.nreg 7350 = c.nreg 7510 ∧ c'.nreg 7351 = c.nreg 7512 ∧
      c'.nreg 7352 = c.nreg 7500 ∧
      (∀ r, (r < 7350 ∨ 7352 < r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  refine ⟨rfl, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  all_goals (config_simp; simp (disch := omega) only [Machine.upd_other])

/-- The face permutation by the reverse and the rotation. -/
lemma phiI_eq (h : EnumOK M en m) {i : ℕ} (hi : i < m) :
    ixOf en m (M.rot (en (rvI M en m i))) = phiI M en m i := by
  unfold phiI
  rw [en_rvI h]
  unfold CombMap.rot
  rw [M.rev_rev]

lemma rotPerm_dual_apply (d : D) : rotPerm M.dual d = M.next d := by
  rw [rotPerm_apply]
  show M.rot (M.rev d) = _
  unfold CombMap.rot
  rw [M.rev_rev]

/-- The inverse of the face permutation. -/
lemma phiI_symm (h : EnumOK M en m) {i : ℕ} (hi : i < m) :
    phiI M en m (ixOf en m ((rotPerm M.dual).symm (en i))) = i := by
  unfold phiI
  rw [en_ixOf h, ← rotPerm_dual_apply, Equiv.apply_symm_apply, ixOf_en h hi]

lemma nsScr_out {r : ℕ} (hr : ¬ NsScr r) : (r < 6210 ∨ 6250 < r) ∧ (r < 7350 ∨ 7352 < r) ∧
    (r < 7400 ∨ 7405 < r) ∧ (r < 5030 ∨ 5036 < r) ∧ (r < 7510 ∨ 7556 < r) ∧ r ≠ 7325 ∧
    r ≠ 7326 := by
  unfold NsScr at hr; omega

/-- Stage A1: the layout and the face permutation. -/
theorem nsAG_exec (h : EnumOK M en m) (c : Config) (hc : WordsBounded W c) {RVb RTb K S : ℕ}
    (r00 : c.nreg 7500 = m) (r01 : c.nreg 7501 = RVb) (r02 : c.nreg 7502 = RTb)
    (r04 : c.nreg 7504 = K) (r05 : c.nreg 7505 = S)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hRT : ∀ i < m, c.nmem (RTb + i) = ixOf en m (M.rot (en i)))
    (sR : S + 9 * m + 1 ≤ RVb) (sT : S + 9 * m + 1 ≤ RTb) (wR : RVb + m ≤ W)
    (wT : RTb + m ≤ W) (wK : 2 * K ≤ W) :
    ∃ c' t, Exec P W (.seq nsLay nsG) c c' t ∧ t ≤ 9 * m + 22 ∧ LayRegs c' m K S ∧
      (∀ i < m, c'.nmem (S + i) = phiI M en m i) ∧
      (∀ a, (a < S ∨ S + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 6210 ∨ (6217 < r ∧ r < 7510) ∨ 7522 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nsG
  obtain ⟨c₁, t₁, e₁, ht₁, L₁, n₁, m₁, rr₁, rm₁, o₁⟩ :=
    nsLay_exec (P := P) c hc r00 r04 r05 (by omega) wK (by omega)
  have a0 := L₁.1
  obtain ⟨c₂, t₂, e₂, ht₂, b0, b1, b2, b3, n₂, m₂, rr₂, rm₂, o₂⟩ := setG_exec (P := P) c₁ e₁.wb_right
  have hrv : ∀ j < m, rvI M en m j < m := fun j _ => rvI_lt h j
  obtain ⟨c₃, t₃, e₃, ht₃, g1, g2, n₃, rr₃, rm₃, o₃⟩ := lgProg_exec (P := P) c₂ e₂.wb_right
    (m := m) (IXb := RVb) (Ab := RTb) (OUTb := S)
    (by rw [b0, n₁ _ (by omega), r00]) (by rw [b1, n₁ _ (by omega), r01])
    (by rw [b2, n₁ _ (by omega), r02]) (by rw [b3, a0]) wR (by omega) (by omega)
    (fun j hj => by rw [m₂, m₁, hRV j hj]; have := hrv j hj; omega)
    (fun j hj => by omega)
    (fun j hj => by rw [m₂, m₁, hRV j hj]; have := hrv j hj; omega)
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega,
    L₁.of fun r h1 h2 => by rw [n₃ r (by omega), n₂ r (by omega)], fun i hi => ?_,
    fun a ha => by rw [g2 a (by omega), m₂, m₁], fun r hr => ?_, by rw [rr₃, rr₂, rr₁],
    by rw [rm₃, rm₂, rm₁], by rw [o₃, o₂, o₁]⟩
  · rw [g1 i hi, m₂, m₁, hRV i hi, hRT _ (rvI_lt h i), phiI_eq h hi]
  · rw [n₃ r (by omega), n₂ r (by omega), n₁ r (by omega)]

/-- Stage A2: the inverse of the face permutation. -/
theorem nsAS_exec (h : EnumOK M en m) (c : Config) (hc : WordsBounded W c) {K S : ℕ}
    (r00 : c.nreg 7500 = m) (hL : LayRegs c m K S)
    (hNX : ∀ i < m, c.nmem (S + i) = phiI M en m i)
    (hZ : ∀ j < m, c.nmem (S + 8 * m + 1 + j) = 0) (w : S + 9 * m + 1 ≤ W) :
    ∃ c' t, Exec P W nsS c c' t ∧ t ≤ 11 * m + 9 ∧
      (∀ i < m, c'.nmem (S + m + i) < m ∧
        en (c'.nmem (S + m + i)) = (rotPerm M.dual).symm (en i)) ∧
      (∀ a, (a < S + m ∨ S + 2 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 6220 ∨ 6228 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨d0, d1, -, -, -, -, -, -, d8, -, -, -, -⟩ := hL
  unfold nsS
  obtain ⟨c₄, t₄, e₄, ht₄, s0, s1, s2, s3, s4, n₄, m₄, rr₄, rm₄, o₄⟩ :=
    setS_exec (P := P) c hc (by omega)
  have hp := phi_permOn h
  obtain ⟨c₅, t₅, e₅, ht₅, p1, p2, n₅, rr₅, rm₅, o₅⟩ := lsProg_exec (P := P) c₄ e₄.wb_right
    (m := m) (IXb := S) (FLb := S + 8 * m + 1) (thr := 1) (OUTb := S + m)
    (by rw [s0, r00]) (by rw [s1, d0]) (by rw [s2, d8]) s3 (by rw [s4, d1]) (by omega) (by omega)
    (by omega)
    (fun j hj _ => by rw [m₄, hNX j hj]; have := hp.lt j hj; omega)
    (fun i hi j hj _ _ e => by rw [m₄, hNX i hi, hNX j hj] at e; exact hp.inj i hi j hj e)
    (fun i hi _ j hj => by rw [m₄, hNX i hi]; have := hp.lt i hi; omega)
    (fun i hi _ j hj => by rw [m₄, hNX i hi]; have := hp.lt i hi; omega)
  have hsel : ∀ j < m, c₄.nmem (S + 8 * m + 1 + j) < 1 := fun j hj => by
    rw [m₄, hZ j hj]; omega
  refine ⟨c₅, t₄ + t₅, .seq e₄ e₅, by omega, fun i hi => ?_, fun a ha => ?_,
    fun r hr => by rw [n₅ r (by omega), n₄ r (by omega)], by rw [rr₅, rr₄], by rw [rm₅, rm₄],
    by rw [o₅, o₄]⟩
  · set j := ixOf en m ((rotPerm M.dual).symm (en i)) with hj
    have hjm : j < m := ixOf_lt h _
    have e := p1 j hjm (hsel j hjm)
    rw [m₄, hNX j hjm, phiI_symm h hi] at e
    rw [e, hj, en_ixOf h]
    exact ⟨ixOf_lt h _, rfl⟩
  · rw [p2 a fun i hi _ => by rw [m₄, hNX i hi]; have := hp.lt i hi; omega, m₄]

/-- Stage A3: the labels. -/
theorem nsAO_exec (h : EnumOK M en m) (c : Config) (hc : WordsBounded W c) {K S : ℕ}
    (r00 : c.nreg 7500 = m) (hL : LayRegs c m K S)
    (hNX : ∀ i < m, c.nmem (S + i) = phiI M en m i)
    (hZ : ∀ j < m, c.nmem (S + 2 * m + j) = 0) (w : S + 9 * m + 1 ≤ W) :
    ∃ c' t, Exec P W nsO c c' t ∧ t ≤ 20 * m + 7 ∧
      (∀ i < m, c'.nmem (S + 2 * m + i) = labI M en m i + 1) ∧
      (∀ a, (a < S + 2 * m ∨ S + 3 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 7350 ∨ (7352 < r ∧ r < 7400) ∨ 7405 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨d0, -, d2, -, -, -, -, -, -, -, -, -, -⟩ := hL
  unfold nsO
  obtain ⟨c₆, t₆, e₆, ht₆, o0, o1, o2, n₆, m₆, rr₆, rm₆, o₆⟩ := setO_exec (P := P) c hc
  obtain ⟨c₇, t₇, e₇, ht₇, l1, l2, n₇, rr₇, rm₇, o₇⟩ := olProg_exec (P := P) (f := phiI M en m)
    (m := m) (phi_permOn h) (Pb := S) (Lb := S + 2 * m) (by omega) (by omega) (by omega) c₆
    e₆.wb_right (by rw [o0, d0]) (by rw [o1, d2]) (by rw [o2, r00])
    (fun x hx => by rw [m₆]; exact hNX x hx) (fun x hx => by rw [m₆]; exact hZ x hx)
  refine ⟨c₇, t₆ + t₇, .seq e₆ e₇, by omega, l1, fun a ha => by rw [l2 a (by omega), m₆],
    fun r hr => by rw [n₇ r (by omega), n₆ r (by omega)], by rw [rr₇, rr₆], by rw [rm₇, rm₆],
    by rw [o₇, o₆]⟩

/-- **Stage A** (see the module docstring): within `40 m + 38` steps. -/
theorem nsA_exec (h : EnumOK M en m) (c : Config) (hc : WordsBounded W c) {RVb RTb K S : ℕ}
    (r00 : c.nreg 7500 = m) (r01 : c.nreg 7501 = RVb) (r02 : c.nreg 7502 = RTb)
    (r04 : c.nreg 7504 = K) (r05 : c.nreg 7505 = S)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hRT : ∀ i < m, c.nmem (RTb + i) = ixOf en m (M.rot (en i)))
    (hz : ∀ a, S ≤ a → a < S + 9 * m + 1 → c.nmem a = 0)
    (sR : S + 9 * m + 1 ≤ RVb) (sT : S + 9 * m + 1 ≤ RTb) (wR : RVb + m ≤ W)
    (wT : RTb + m ≤ W) (wK : 2 * K ≤ W) :
    ∃ c' t, Exec P W nsA c c' t ∧ t ≤ 40 * m + 38 ∧ LayRegs c' m K S ∧
      (∀ i < m, c'.nmem (S + i) = phiI M en m i) ∧
      (∀ i < m, c'.nmem (S + m + i) < m ∧
        en (c'.nmem (S + m + i)) = (rotPerm M.dual).symm (en i)) ∧
      (∀ i < m, c'.nmem (S + 2 * m + i) = labI M en m i + 1) ∧
      (∀ a, (a < S ∨ S + 3 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ NsScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold nsA
  obtain ⟨c₁, t₁, e₁, ht₁, L₁, X₁, F₁, R₁, rr₁, rm₁, o₁⟩ :=
    nsAG_exec h c hc r00 r01 r02 r04 r05 hRV hRT sR sT wR wT wK (P := P)
  have r00₁ : c₁.nreg 7500 = m := by rw [R₁ _ (by omega), r00]
  obtain ⟨c₂, t₂, e₂, ht₂, P₂, F₂, R₂, rr₂, rm₂, o₂⟩ := nsAS_exec h c₁ e₁.wb_right r00₁ L₁ X₁
    (fun j hj => by rw [F₁ _ (by omega), hz _ (by omega) (by omega)]) (by omega) (P := P)
  have L₂ : LayRegs c₂ m K S := L₁.of fun r h1 h2 => R₂ r (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, B₃, F₃, R₃, rr₃, rm₃, o₃⟩ := nsAO_exec h c₂ e₂.wb_right
    (by rw [R₂ _ (by omega), r00₁]) L₂
    (fun i hi => by rw [F₂ _ (by omega)]; exact X₁ i hi)
    (fun j hj => by rw [F₂ _ (by omega), F₁ _ (by omega), hz _ (by omega) (by omega)]) (by omega)
    (P := P)
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega,
    L₂.of fun r h1 h2 => R₃ r (by omega), fun i hi => ?_, fun i hi => ?_, B₃, fun a ha => ?_,
    fun r hr => ?_, by rw [rr₃, rr₂, rr₁], by rw [rm₃, rm₂, rm₁], by rw [o₃, o₂, o₁]⟩
  · rw [F₃ _ (by omega), F₂ _ (by omega)]; exact X₁ i hi
  · rw [F₃ _ (by omega)]; exact P₂ i hi
  · rw [F₃ a (by omega), F₂ a (by omega), F₁ a (by omega)]
  · obtain ⟨q1, q2, q3, -, q5, -, -⟩ := nsScr_out hr
    rw [R₃ r (by omega), R₂ r (by omega), R₁ r (by omega)]

end NsStep

end BKMNW

end PlanarFlow
