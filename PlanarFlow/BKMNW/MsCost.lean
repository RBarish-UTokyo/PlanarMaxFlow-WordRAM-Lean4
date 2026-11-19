module

public import PlanarFlow.BKMNW.MsStE
public import PlanarFlow.BKMNW.MsRunE
public import PlanarFlow.BKMNW.CsScale

/-!
# The step bound of the MSSP call with targeted clearing: within `cMachS.mssp`

The encoder of the call is `msA1 ; msA2 ; svSet ; msB1 ; rsSet ; msB2 ; msB3 ; msB4 ; msC1 ;
msC2 ; msC3 ; msD1 ; msD2 ; msE2`; its stage bounds (`costA1`, `costA2`, `ivCost`, …,
`stdCost`, `costC2`, `costE2`) evaluated at the maxima `nD ≤ 5 m`, `#CutV ≤ 2 m`,
`#CutF ≤ 2 m + 1`, `fixPer ≤ m`, `|fixCornerL| ≤ m` give **`msEncCost m k q`**. Klein's run is
bounded by **`KCf m k = kSteps (2m) (2m+1) (5m) (5m) (20m+1) m (2k) (2k)`** (`kSteps_le_KCf`:
monotonicity, `|fixCornerL| ≤ 2k` by `fixCornerL_len_le`), the clearing regions by
**`ZCf m = (20 m + 1 + m) + (15 m + 3) + dLen (5 m) m m`**.

**`msCost'_le_cMachS`**: for `1 ≤ m` and `q ≤ 2 k`,
`msCost' msEncCost KCf ZCf m k q ≤ (cMachS C C₀).mssp m k = 10¹⁵ · 24637500000 (m lg m + k² lg m)`
— no term in the magnitudes of the lengths.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Klein NegSSSP

/-- The corners are at most the faces along the path: `|fixCornerL| ≤ 2 k`. -/
theorem fixCornerL_len_le.{u} {D V F : Type u} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F} (hrot : M.RotTrans)
    (P : SPath M) : (fixCornerL M P).length ≤ 2 * P.k := by
  obtain ⟨-, -, hin, hinj, -⟩ := fixCornerL_spec hrot P
  have h1 : (fixCornerL M P).length ≤ P.faces.card := by
    have := Finset.card_le_card_of_injOn
      (s := Finset.range (fixCornerL M P).length) (t := P.faces)
      (fun r => fixCorner M P ((fixCornerL M P).getD r 0))
      (fun r hr => hin r (by simpa using hr))
      (fun r hr r' hr' e => hinj r (by simpa using hr) r' (by simpa using hr') e)
    simpa using this
  exact h1.trans P.card_faces_le

/-- Klein's run bound at the maxima. -/
def KCf (m k : ℕ) : ℕ := MsCall.kSteps (2 * m) (2 * m + 1) (5 * m) (5 * m) (20 * m + 1) m (2 * k) (2 * k)

lemma opCostE_mono {a b : ℕ} (h : a ≤ b) : DynTree.opCostE a ≤ DynTree.opCostE b := by
  unfold DynTree.opCostE
  have := Nat.log_mono_right (b := 2) h
  omega

/-- **Monotonicity of Klein's step bound.** -/
theorem kSteps_le_KCf {nV nF nD nS n kk f t m k : ℕ} (h1 : nV ≤ 2 * m) (h2 : nF ≤ 2 * m + 1)
    (h3 : nD ≤ 5 * m) (h4 : nS ≤ 5 * m) (h5 : n ≤ 20 * m + 1) (h6 : kk ≤ m) (h7 : f ≤ 2 * k)
    (h8 : t ≤ 2 * k) : MsCall.kSteps nV nF nD nS n kk f t ≤ KCf m k := by
  unfold KCf MsCall.kSteps
  have hft : f * t ≤ 2 * k * (2 * k) := Nat.mul_le_mul h7 h8
  have hops : kleinOpsM nV nF nD nS kk f t ≤
      kleinOpsM (2 * m) (2 * m + 1) (5 * m) (5 * m) m (2 * k) (2 * k) := by
    unfold kleinOpsM; omega
  have hext : kleinExtM nV nF nD nS kk f t ≤
      kleinExtM (2 * m) (2 * m + 1) (5 * m) (5 * m) m (2 * k) (2 * k) := by
    unfold kleinExtM; omega
  have hop := Nat.mul_le_mul hops (opCostE_mono h5)
  omega

/-- The clearing regions at the maxima. -/
def ZCf (m : ℕ) : ℕ := (20 * m + 1 + m) + (15 * m + 3) + dLen (5 * m) m m

/-- **The step bound of the encoder** at the maxima. -/
def msEncCost (m k q : ℕ) : ℕ :=
  costA1 m k + costA2 m + 3 + (11 + StEnc.ivCost (5 * m) (2 * m + 1)) + 3 +
    (12 + 5 * (5 * m) + 5 + (8 + 8) * m + 5) + (17 + (15 + 8) * (5 * m) + 5) +
    (4 + (6 * (5 * m) + 5) + 10 + (18 + 8) * (5 * m) + 5) +
    (10 + 2 * (15 + stdCost (4 * (5 * m) + 1) (5 * m))) + costC2 (5 * m) (2 * m) (2 * m + 1) +
    (14 + hpCost xtAL + hpCost xtBL + hpCost xtWL + (16 + 8) * m + 5) +
    (hpCost mkWL + (5 + 8) * m + 5) + (hpCost slAL + hpCost slWL + (9 + 8) * q + 5) +
    (13 + 4 + hpCost dh1L + hpCost dh2L + hpCost dh3L + (3 + hpCost dh4L + hpCost dh5L)) +
    (hpCost twSL + hpCost twWL + (19 + 8) * (5 * m) + 5 + 6) + costE2 (dLen (5 * m) m m)

lemma log_mul_two_pow (m j : ℕ) (hm : m ≠ 0) : Nat.log 2 (m * 2 ^ j) = Nat.log 2 m + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, Nat.log_mul_base (by norm_num) (by positivity), ih]; omega

lemma log_le_256 {m x : ℕ} (hm : 1 ≤ m) (hx : x ≤ 256 * m) : Nat.log 2 x ≤ Nat.log 2 m + 8 := by
  have h := Nat.log_mono_right (b := 2) (show x ≤ m * 2 ^ 8 by norm_num; omega)
  rwa [log_mul_two_pow m 8 (by omega)] at h

lemma stdCost_le {m : ℕ} (hm : 1 ≤ m) :
    stdCost (4 * (5 * m) + 1) (5 * m) ≤ 10 ^ 6 * (m * BKMNW.lg m) := by
  have hL : BKMNW.lg (2 * (4 * (5 * m) + 1)) ≤ BKMNW.lg m + 8 := by
    unfold BKMNW.lg; have := log_le_256 hm (x := 2 * (4 * (5 * m) + 1)) (by omega); omega
  have hL1 := BKMNW.one_le_lg m
  unfold stdCost osCost
  rw [Heap.lg_eq_log (by omega)]
  have hL' : Nat.log 2 (2 * (4 * (5 * m) + 1)) + 1 ≤ BKMNW.lg m + 8 := by
    unfold BKMNW.lg at hL ⊢; exact hL
  set L := BKMNW.lg m
  set l2 := Nat.log 2 (2 * (4 * (5 * m) + 1)) + 1
  have a1 : (4 * (5 * m) + 1) * (23 * l2 + 21) ≤ (21 * m) * (23 * (9 * L) + 21 * L) :=
    Nat.mul_le_mul (by omega) (by omega)
  have a2 : (13 * l2 + 20) * (5 * m) ≤ (13 * (9 * L) + 20 * L) * (5 * m) :=
    Nat.mul_le_mul (by omega) le_rfl
  have a3 : m ≤ m * L := Nat.le_mul_of_pos_right m (by omega)
  have a4 : l2 ≤ 9 * (m * L) := by
    have : 9 * L ≤ 9 * (m * L) := by nlinarith
    omega
  have e1 : (21 * m) * (23 * (9 * L) + 21 * L) = 4788 * (m * L) := by ring
  have e2 : (13 * (9 * L) + 20 * L) * (5 * m) = 685 * (m * L) := by ring
  omega

set_option maxHeartbeats 2000000 in
/-- **The step bound of the MSSP call is within `cMachS.mssp`** (`1 ≤ m`, `q ≤ 2 k`). -/
theorem msCost'_le_cMachS (C C₀ : ℕ) {m k q : ℕ} (hm : 1 ≤ m) (hq : q ≤ 2 * k) :
    MsCall.msCost' msEncCost (fun m k _ => KCf m k) (fun m _ _ => ZCf m) m k q ≤
      (cMachS C C₀).mssp m k := by
  have hL1 := BKMNW.one_le_lg m
  have hstd := stdCost_le hm
  have hlog : Nat.log 2 (20 * m + 1) ≤ BKMNW.lg m + 7 := by
    have := log_le_256 hm (x := 20 * m + 1) (by omega); unfold BKMNW.lg; omega
  set L := BKMNW.lg m with hLd
  have hX : m ≤ m * L := Nat.le_mul_of_pos_right m (by omega)
  have hkk : k ≤ k * k := Nat.le_mul_self k
  have hY : k * k ≤ k ^ 2 * L := by rw [sq]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hqq : q * q ≤ 2 * k * (2 * k) := Nat.mul_le_mul hq hq
  -- Klein's run
  have hop : DynTree.opCostE (20 * m + 1) ≤ 3000000 * L := by
    unfold DynTree.opCostE; omega
  have hops : kleinOpsM (2 * m) (2 * m + 1) (5 * m) (5 * m) m (2 * k) (2 * k) ≤
      391 * m + 4 * (k * k) := by
    unfold kleinOpsM
    have : 2 * k * (2 * k) = 4 * (k * k) := by ring
    omega
  have hext : kleinExtM (2 * m) (2 * m + 1) (5 * m) (5 * m) m (2 * k) (2 * k) ≤
      1000 * m + 56 * (k * k) + 120 := by
    unfold kleinExtM
    have : 2 * k * (2 * k) = 4 * (k * k) := by ring
    omega
  have hprod := Nat.mul_le_mul hops hop
  have e1 : (391 * m + 4 * (k * k)) * (3000000 * L) =
      1173000000 * (m * L) + 12000000 * (k * k * L) := by ring
  have hY' : k * k * L = k ^ 2 * L := by ring
  have hKC : KCf m k ≤ 5000000000 * (m * L) + 50000001000 * (k ^ 2 * L) := by
    unfold KCf MsCall.kSteps
    omega
  -- the encoder
  have cxtAL : hpCost xtAL = 40 := by decide +kernel
  have cxtBL : hpCost xtBL = 33 := by decide +kernel
  have cxtWL : hpCost xtWL = 49 := by decide +kernel
  have cmkWL : hpCost mkWL = 25 := by decide +kernel
  have cslAL : hpCost slAL = 29 := by decide +kernel
  have cslWL : hpCost slWL = 21 := by decide +kernel
  have cdh1L : hpCost dh1L = 45 := by decide +kernel
  have cdh2L : hpCost dh2L = 11 := by decide +kernel
  have cdh3L : hpCost dh3L = 38 := by decide +kernel
  have cdh4L : hpCost dh4L = 254 := by decide +kernel
  have cdh5L : hpCost dh5L = 45 := by decide +kernel
  have ctwSL : hpCost twSL = 42 := by decide +kernel
  have ctwWL : hpCost twWL = 25 := by decide +kernel
  have ckiL : hpCost kiL = 124 := by decide +kernel
  have cosL : hpCost osL = 122 := by decide +kernel
  have cceSL : hpCost ceSL = 14 := by decide +kernel
  have cceWL : hpCost ceWL = 21 := by decide +kernel
  have ckpSL : hpCost kpSL = 56 := by decide +kernel
  have ckPrmL : hpCost kPrmL = 556 := by decide +kernel
  have cfnAL : hpCost fnAL = 70 := by decide +kernel
  have cfnBL : hpCost fnBL = 14 := by decide +kernel
  have cmsLayL : hpCost msLayL = 247 := by decide +kernel
  have cfcL : hpCost fcL = 42 := by decide +kernel
  have cckL : hpCost ckL = 98 := by decide +kernel
  have hEnc : msEncCost m k q ≤ 2100000 * (m * L) + 11 * k + 17 * q + 200000 := by
    unfold msEncCost costA1 costA2 fcCost cutCost StEnc.ivCost costC2 StEnc.kiCost osCost
      costE2 dLen
    omega
  have hZ : ZCf m ≤ 300 * m + 20 := by unfold ZCf dLen; omega
  unfold MsCall.msCost'
  show msEncCost m k q + 27 * KCf m k + 5 * ZCf m + 23 * (q * q) + 40 ≤
    csK * (24637500000 * (m * L + k ^ 2 * L))
  unfold csK
  have e2 : 2 * k * (2 * k) = 4 * (k * k) := by ring
  omega

/-- **Monotonicity of `MsspCallSpec` in the step bound.** -/
theorem msspCallSpec_mono.{u} {D V F : Type u} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} {msP : WordRAM.Machine.Stmt}
    {Scr : ℕ → Prop} {cost cost' R : ℕ → ℕ → ℕ → ℕ} {wz : ℕ → ℕ → ℕ}
    (h : MsCall.MsspCallSpec M msP Scr cost R wz) (hc : ∀ m k q, cost m k q ≤ cost' m k q) :
    MsCall.MsspCallSpec M msP Scr cost' R wz := by
  intro hM hrot en m P ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p Wz W I c h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨c', t, ex, ht, rest⟩ :=
    h hM hrot en m P ℓ Lmax q ts RVb RTb Pb Lb Qb Ob p Wz W I c h1 h2 h3 h4 h5 h6 h7 h8 h9
  exact ⟨c', t, ex, ht.trans (hc _ _ _), rest⟩

/-- **The step bound of the MSSP call for `cMachS`**: `(cMachS C C₀).mssp m k` whenever
`1 ≤ m` and `q ≤ 2 k` (the corner queries of `fixPath`), `msCost'` otherwise. -/
def msCostS (C C₀ m k q : ℕ) : ℕ :=
  if 1 ≤ m ∧ q ≤ 2 * k then (cMachS C C₀).mssp m k
  else MsCall.msCost' msEncCost (fun m k _ => KCf m k) (fun m _ _ => ZCf m) m k q

/-- **The interface for the node step**: an encoder meeting `MsEncSpec'` with the step bounds
`msEncCost`, `KCf`, `ZCf` gives `MsspCallSpec` for `msspCall'` with the step bound `msCostS C C₀`,
i.e. `(cMachS C C₀).mssp m k` for `q ≤ 2 k` queries. -/
theorem msspCall'_cMachS.{u} {D V F : Type u} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (C C₀ : ℕ) {encP : WordRAM.Machine.Stmt}
    {EScr : ℕ → Prop} {R : ℕ → ℕ → ℕ → ℕ} {wz : ℕ → ℕ → ℕ}
    (hE : MsCall.MsEncSpec' M encP EScr msEncCost (fun m k _ => KCf m k) (fun m _ _ => ZCf m)
      R wz) :
    MsCall.MsspCallSpec M (MsCall.msspCall' encP) (fun r => EScr r ∨ MsCall.msScr r)
      (msCostS C C₀) R wz := by
  refine msspCallSpec_mono (MsCall.msspCall'_spec hE) (fun m k q => ?_)
  unfold msCostS
  split_ifs with h
  · exact msCost'_le_cMachS C C₀ h.1 h.2
  · exact le_rfl

end MsEnc

end BKMNW

end PlanarFlow
