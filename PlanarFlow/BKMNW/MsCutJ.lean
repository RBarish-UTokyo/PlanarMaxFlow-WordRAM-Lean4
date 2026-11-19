module

public import PlanarFlow.BKMNW.MsCutI

/-!
# The cut map of the path on the machine, part J: Klein's encoding of the cut map

**`cutKin`** `= cutProg ; cjSet ; StEnc.smP`: after the arrays of the cut (`cutProg_spec`), the
map encoder of the s-t flow (`StEnc.smP_kin`) is run on the map `Q = (cutMap hL).dual` in the
order `cutEn` (the reverse and rotation of `Q` are the reverse and next of the cut). Its output
is **Klein's encoding `StEnc.KInM` of the cut map `cutMap hL`** (with no piece: the words
`RV`, `NF`, `NE`, `NG`, `NT`, `NH`, `IS = 0`, `ED`) at `β`, with the dart numbering
`enEq hQ` (`= cutIx`, `enEq_cut`) and the node layout of `StEnc.smLayout`.
**`cutKin_spec`**, within `cutCost m + 8 + 140 nD + 150` steps (`nD = nE + 4 nT ≤ 5 m`).
Input registers `8250 … 8257` (as `cutProg`) and `8258 = S'` (scratch of `smP`, `3 nD` words),
`8259 = β`.
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

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab NsStep
  CombMap

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

variable {P : Input} {W : ℕ}

/-- The registers of `smP`: `nD = nE + 4 nT`, `RVo`, `RTo`, `S'`, `β`. -/
def cjSet : Stmt :=
  block [.subN 8260 8230 8228, .addN 8261 8230 8260, .addN 8261 8261 8260,
    .addN 7700 8261 8260, .copyN 7701 8256, .copyN 7702 8257, .copyN 7703 8258,
    .copyN 7704 8259]

/-- **Klein's encoding of the cut map.** -/
def cutKin : Stmt := .seq cutProg (.seq cjSet StEnc.smP)

theorem cjSet_exec (c : Config) (hc : WordsBounded W c) {nE nT RVo RTo S β : ℕ}
    (r28 : c.nreg 8228 = nE) (r30 : c.nreg 8230 = nE + nT) (r56 : c.nreg 8256 = RVo)
    (r57 : c.nreg 8257 = RTo) (r58 : c.nreg 8258 = S) (r59 : c.nreg 8259 = β)
    (hw : nE + 4 * nT ≤ W) :
    ∃ c' t, Exec P W cjSet c c' t ∧ t = 8 ∧ c'.nreg 7700 = nE + 4 * nT ∧ c'.nreg 7701 = RVo ∧
      c'.nreg 7702 = RTo ∧ c'.nreg 7703 = S ∧ c'.nreg 7704 = β ∧
      (∀ r, (r < 7700 ∨ 7704 < r) → r ≠ 8260 → r ≠ 8261 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cjSet
  exec_block
  all_goals try ((try config_simp); (try simp only [r28, r30, r56, r57, r58, r59]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun r a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals first
    | (simp only [r28, r30, r56, r57, r58, r59]; done)
    | (simp only [r28, r30, r56, r57, r58, r59]; omega)
    | (simp only [upd_apply]; split_ifs <;> omega)

/-- `cutKin` uses natural words only. -/
theorem cutKin_natOnly : Klein.natOnly cutKin = true := by decide +kernel

/-- The numbering of the darts of the cut by the map encoder is `cutIx`. -/
lemma enEq_cut {L : List D} (hL : ∀ e ∈ L, M.rev e ∈ L) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (d₀ : CutD M L)
    (hQ : EnumOK (cutMap hL).dual (cutEn M L en m d₀) (nEc L en m + 4 * nTc M L en m))
    (d : CutD M L) : (StEnc.enEq hQ d : ℕ) = cutIx M L en m d := by
  rw [StEnc.enEq_val, ixOf_cutEn hL h]

/-- The rotation of the dual of the cut is its next dart. -/
lemma rot_dual_cut {L : List D} (hL : ∀ e ∈ L, M.rev e ∈ L) (d : CutD M L) :
    (cutMap hL).dual.rot d = cutNext hL d := by
  show cutNext hL (cutRev hL (cutRev hL d)) = cutNext hL d
  rw [show cutRev hL (cutRev hL d) = d from (cutMap hL).rev_rev d]

/-- Klein's encoding only depends on the reverse, the tails and the faces of the map. -/
lemma kInM_congr {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X]
    {A B : CombMap D' X Y} (h1 : A.rev = B.rev) (h2 : A.tail = B.tail) (h3 : A.face = B.face)
    {nD : ℕ} {σ : D' ≃ Fin nD} {ιv : X → ℕ} {ιg : D' → ℕ} {ιf : Y → ℕ} {ιe : D' → ℕ}
    {mem : ℕ → ℕ} {β : ℕ} (h : StEnc.KInM A σ ιv ιg ιf ιe mem β) :
    StEnc.KInM B σ ιv ιg ιf ιe mem β := by
  obtain ⟨rv, nf, ne, ng, nt, nh, is, ed⟩ := h
  refine ⟨fun d => ?_, fun d => ?_, ne, ng, fun d => ?_, fun d => ?_, is, fun d => ?_⟩
  · rw [rv d, h1]
  · rw [nf d, h3]
  · rw [nt d, h2]
  · rw [nh d]; simp only [CombMap.head, h1, h2]
  · rw [← h1]; exact ed d

set_option maxHeartbeats 1000000 in
/-- **Klein's encoding of the cut map on the machine** (see the module docstring). -/
theorem cutKin_spec {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (h' : EnumOK M.dual en m)
    (Pa : SPath M) (d₀ : CutD M Pa.darts)
    (hQ : EnumOK (cutMap Pa.rev_mem_darts').dual (cutEn M Pa.darts en m d₀)
      (nEc Pa.darts en m + 4 * nTc M Pa.darts en m))
    (hQ' : EnumOK (cutMap Pa.rev_mem_darts').dual.dual (cutEn M Pa.darts en m d₀)
      (nEc Pa.darts en m + 4 * nTc M Pa.darts en m))
    (c : Config) (hc : WordsBounded W c) {RVb RTb LFb TAb Z RVo RTo S β : ℕ}
    (hI : CpIn c m RVb RTb LFb TAb Z RVo RTo) (r58 : c.nreg 8258 = S) (r59 : c.nreg 8259 = β)
    (hrv : ∀ i < m, c.nmem (RVb + i) < m ∧ en (c.nmem (RVb + i)) = M.rev (en i))
    (hrt : ∀ i < m, c.nmem (RTb + i) < m ∧ en (c.nmem (RTb + i)) = M.rot (en i))
    (hlf : ∀ i < m, c.nmem (LFb + i) = if en i ∈ Pa.darts then 1 else 0)
    (hta : ∀ i < m, c.nmem (TAb + i) = ixOf en m (tour M Pa.darts (en i)))
    (dRV : RVb + m ≤ Z) (dRT : RTb + m ≤ Z) (dLF : LFb + m ≤ Z) (dTA : TAb + m ≤ Z)
    (dO1 : Z + 6 * m ≤ RVo) (dO2 : RVo + 5 * m ≤ RTo) (dO3 : RTo + 5 * m ≤ S)
    (dO4 : S + 15 * m ≤ β) (hw : β + 60 * m + 1 ≤ W) :
    ∃ c' t, Exec P W cutKin c c' t ∧
      t ≤ cutCost m + 8 + (140 * (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) + 150) ∧
      StEnc.KInM (cutMap Pa.rev_mem_darts') (StEnc.enEq hQ) (StEnc.ιF _ hQ) (StEnc.ιG _ hQ)
        (StEnc.ιV _ hQ') (StEnc.ιE _ hQ) c'.nmem β ∧
      (∀ a, (a < Z ∨ β + 12 * (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) + 1 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ CpScr r → ¬ StEnc.SmScr r → (r < 7700 ∨ 7704 < r) → r ≠ 8260 → r ≠ 8261 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  obtain ⟨c₁, k₁, e₁, hk₁, hW, h28, h30, hM, hR, hr, hrm, ho⟩ := cutProg_spec (P := P) h h' Pa c hc
    hI hrv hrt hlf hta dRV dRT dLF dTA dO1 dO2 (by omega)
  have g : ∀ r, 8256 ≤ r → r ≤ 8259 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    hR r (by simp only [CpScr]; omega)
  obtain ⟨c₂, k₂, e₂, hk₂, s0, s1, s2, s3, s4, sR, sm, sr, srm, so⟩ := cjSet_exec (P := P) c₁
    e₁.wb_right h28 h30 (by rw [g _ (by omega) (by omega), hI.r56])
    (by rw [g _ (by omega) (by omega), hI.r57]) (by rw [g _ (by omega) (by omega), r58])
    (by rw [g _ (by omega) (by omega), r59]) (by omega)
  have hRV : ∀ i < (nEc Pa.darts en m + 4 * nTc M Pa.darts en m), c₂.nmem (RVo + i) =
      rvI (cutMap Pa.rev_mem_darts').dual (cutEn M Pa.darts en m d₀) (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) i := fun i hi => by
    rw [sm]
    have e := cutIx_cutEn h d₀ hi
    unfold rvI
    rw [ixOf_cutEn Pa.rev_mem_darts' h]
    conv_lhs => rw [← e]
    exact (hW _).1
  have hRT : ∀ i < (nEc Pa.darts en m + 4 * nTc M Pa.darts en m), c₂.nmem (RTo + i) =
      ixOf (cutEn M Pa.darts en m d₀) (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) ((cutMap Pa.rev_mem_darts').dual.rot (cutEn M Pa.darts en m d₀ i)) := fun i hi => by
    rw [sm, ixOf_cutEn Pa.rev_mem_darts' h, rot_dual_cut Pa.rev_mem_darts']
    have e := cutIx_cutEn h d₀ hi
    conv_lhs => rw [← e]
    exact (hW _).2
  obtain ⟨c₃, k₃, e₃, hk₃, hK, hz, hm₃, hR₃, hr₃, hrm₃, ho₃⟩ := StEnc.smP_kin (P := P) hQ hQ' c₂
    e₂.wb_right s0 s1 s2 s3 s4 hRV hRT (by omega) (by omega) (by omega) (by omega)
  have hK' := kInM_congr (A := (cutMap Pa.rev_mem_darts').dual.dual)
    (B := cutMap Pa.rev_mem_darts') rfl rfl rfl hK
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, hK', fun a ha => ?_,
    fun r h1 h2 h3 h4 h5 => ?_, by rw [hr₃, sr, hr], by rw [hrm₃, srm, hrm],
    by rw [ho₃, so, ho]⟩
  · rw [hm₃ a (by omega) (by omega), sm, hM a (by omega)]
  · rw [hR₃ r h2, sR r h3 h4 h5, hR r h1]

end MsEnc

end BKMNW

end PlanarFlow
