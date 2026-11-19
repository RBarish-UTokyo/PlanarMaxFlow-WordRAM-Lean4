module

public import PlanarFlow.BKMNW.Nf7fB

/-!
# The per-address statements and `fixPos` within the envelopes

* **`FixPosW`**, **`FixZeroW`**: the statements of `fixPos_execW`, `fixZero_execW`
  (`fixPos_exec`/`fixZero_exec` with the address sums `hW1`, `hW` resp.
  `hZ1`, `hW` replaced by `Q + 15k + 16 ≤ W`, `X.p + 60m + 60 + negT ≤ W` resp. `A0 + 9m + 16 ≤ W`,
  `A0 + 9m + 1 + 60m + 60 + negT ≤ W`), as propositions, so that the glue does not depend on their
  proofs;
* `fx7f_FLW_le` (`FLW ≤ 2Z` for a pseudoflow in `FL`);
* **`fx7f_pos`**: `FixPosW` ⟹ the run of `fixPos msP` from the frame with all the bounds of
  `fixPos_execW` discharged by the envelopes `A0 + rOF7 C C₀ Rm m Z ≤ W + 5` and
  `wzF7 wzm m Z ≤ Wz`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep SPath
  WordRAM WordRAM.Machine WordRAM.Programs

universe w

/-- **The statement of `fixPos_execW`** (`fixPos_exec` with per-address word bounds). -/
def FixPosW : Prop :=
  ∀ {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} {gid : D → ℕ} {u : D → ℤ} {S T : Finset V}
    {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ}
    (C C₀ : ℕ) (hC : 200000 ≤ C) {msP : Stmt} {Scr : ℕ → Prop}
    {cost Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ} (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hMS : MsCall.MsspCallSpec (pmap hP) msP Scr cost Rm wzm) (hScr : ∀ r, Scr r → r < 9300)
    (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans) (hface : (pmap hP).FaceTrans)
    (I : Input) {W Wz A0 : ℕ} (c : Config) (hc : WordsBounded W c)
    (hl : Lay M gid u S T Z x m en d c.nmem) (hm : 0 < m) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb c.nmem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z c.nmem).k) (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
    (hk0 : 0 < πj.k) {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en c.nmem f₀)
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (hz : ∀ a ≤ Wz, c.nmem a = 0) (hWzd : Wz < d) (hWlo : Wz < lo)
    (hhi : hi ≤ A0) (hfr : d + 4 + 7 * m ≤ A0)
    (hW1 : (callIn d m Gb π j Z c.nmem).Qb A0 + 15 * (callIn d m Gb π j Z c.nmem).k + 16 ≤ W)
    (hW2 : ∑ i ∈ range m, (callIn d m Gb π j Z c.nmem).FLW i + (callIn d m Gb π j Z c.nmem).AS +
      16 * fpB (callIn d m Gb π j Z c.nmem).AS m (callIn d m Gb π j Z c.nmem).k + m * Z + Z +
      (callIn d m Gb π j Z c.nmem).k + 16 ≤ W)
    (hl14 : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).p + (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).LG ≤ W)
    (hw1 : 16 * (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).K + 1 ≤ W)
    (hw2 : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).Mo + 3 * (mkX hP hl hm πj f₀
      (callIn d m Gb π j Z c.nmem) ((callIn d m Gb π j Z c.nmem).Qb A0)).K ≤ W)
    (hwz : wzm m (2 * Z) ≤ Wz)
    (hSHz : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).SH + (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).WN ≤ Wz)
    (hpw : lyP ((callIn d m Gb π j Z c.nmem).Qb A0 + 15 * (callIn d m Gb π j Z c.nmem).k)
      (callIn d m Gb π j Z c.nmem).cw.cnt (callIn d m Gb π j Z c.nmem).k +
      Rm m (callIn d m Gb π j Z c.nmem).k (callIn d m Gb π j Z c.nmem).cw.cnt ≤ W)
    (hKL : (callIn d m Gb π j Z c.nmem).K + 8 * fpB (callIn d m Gb π j Z c.nmem).AS m
      (callIn d m Gb π j Z c.nmem).k + moOf (callIn d m Gb π j Z c.nmem).cw.cnt
      (8 * fpB (callIn d m Gb π j Z c.nmem).AS m (callIn d m Gb π j Z c.nmem).k) ≤ W)
    (hSz : 9 * m + 1 + tsz m ≤ Wz + 1)
    (hWz : rtW m (rtL (pmap hP) (fun y => u y.1 - (fpState (pmap hP) (fun y => u y.1) f₀ πj
      (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y)) m ≤ Wz)
    (hW : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z c.nmem)
      ((callIn d m Gb π j Z c.nmem).Qb A0)).p + 60 * m + 60 + negT C C₀ m ≤ W)
    (wL : 2 * (callIn d m Gb π j Z c.nmem).K + rtL (pmap hP) (fun y => u y.1 -
      (fpState (pmap hP) (fun y => u y.1) f₀ πj (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y)
      ≤ W)
    (hw2' : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL (pmap hP) (fun y => u y.1 - (fpState (pmap hP) (fun y => u y.1) f₀ πj
      (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y)) ≤ W)
    (hv : Z + Z + 2 * (callIn d m Gb π j Z c.nmem).K + 2 * rtL (pmap hP) (fun y => u y.1 -
      (fpState (pmap hP) (fun y => u y.1) f₀ πj (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y)
      ≤ W),
    ∃ c' t, Exec I W (fixPos msP) c c' t ∧
      t ≤ posT C C₀ cost m πj.k (callIn d m Gb π j Z c.nmem).cw.cnt ∧ SRegKeep c c' ∧
      (∀ a, a < A0 → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      FLHas Z m d en c'.nmem (fixPath (pmap hP) (fun y => u y.1) f₀ πj
        (Klein.msspPlaneK (pmap hP)) (frRef _) (negLay gid I x hP))

/-- **The statement of `fixZero_execW`** (`fixZero_exec` with per-address word bounds). -/
def FixZeroW : Prop :=
  ∀ {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} {gid : D → ℕ} {u : D → ℤ} {S T : Finset V}
    {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ}
    (C C₀ : ℕ) (hC : 200000 ≤ C) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans) (hface : (pmap hP).FaceTrans)
    (I : Input) {W Wz A0 : ℕ} (c : Config) (hc : WordsBounded W c)
    (hl : Lay M gid u S T Z x m en d c.nmem) (hm : 0 < m) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb c.nmem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z c.nmem).k) (hk00 : πj.k = 0)
    {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en c.nmem f₀)
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (hz : ∀ a ≤ Wz, c.nmem a = 0) (hWzd : Wz < d) (hWlo : Wz < lo)
    (hhi : hi ≤ A0) (hfr : d + 4 + 7 * m ≤ A0)
    (hZ1 : A0 + 9 * m + 16 ≤ W)
    (hZ2 : ∑ i ∈ range m, (callIn d m Gb π j Z c.nmem).FLW i + 6 ≤ W)
    (hZ3 : (callIn d m Gb π j Z c.nmem).AS + 16 * fpB (callIn d m Gb π j Z c.nmem).AS m 0 + Z +
      16 ≤ W)
    (hSz : 9 * m + 1 + tsz m ≤ Wz + 1)
    (hWz : rtW m (rtL (pmap hP) (fun y => u y.1 - f₀ y)) m ≤ Wz)
    (hW : A0 + 9 * m + 1 + 60 * m + 60 + negT C C₀ m ≤ W)
    (wL : 2 * (callIn d m Gb π j Z c.nmem).K + rtL (pmap hP) (fun y => u y.1 - f₀ y) ≤ W)
    (hw2' : spWs m + 205 ≤ W) (hw3 : fxWB m (rtL (pmap hP) (fun y => u y.1 - f₀ y)) ≤ W)
    (hv : Z + Z + 2 * (callIn d m Gb π j Z c.nmem).K +
      2 * rtL (pmap hP) (fun y => u y.1 - f₀ y) ≤ W),
    ∃ c' t, Exec I W fixZero c c' t ∧ t ≤ zT C C₀ m ∧ SRegKeep c c' ∧
      (∀ a, a < A0 → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      FLHas Z m d en c'.nmem (fixPath (pmap hP) (fun y => u y.1) f₀ πj
        (Klein.msspPlaneK (pmap hP)) (frRef _) (negLay gid I x hP))

section Call

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ}

/-- **The flow words of a pseudoflow are at most `2Z`.** -/
lemma fx7f_FLW_le (hl : Lay M gid u S T Z x m en d mem)
    {hP : PieceInv M x.1.piece x.2.1 x.2.2} {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en mem f₀)
    (Gb : ℕ) (π : HSep M) (j : ℕ) {i : ℕ} (hi : i < m) :
    (callIn d m Gb π j Z mem).FLW i ≤ 2 * Z := by
  have h := hFL i hi
  rw [fext_mem f₀ (hl.en_mem i hi)] at h
  have h1 := hf₀.le_cap ⟨en i, hl.en_mem i hi⟩
  have h2 := (hl.cp i hi)
  have e : (callIn d m Gb π j Z mem).FLW i = mem (d + 4 + 6 * m + i) := by
    simp only [FpIn.FLW, callIn]; congr 1; omega
  rw [e]
  simp only at h1
  have h3 := h2.2
  have h4 := h2.1
  omega

/-- The sum of the flow words. -/
lemma fx7f_sumFLW_le (hl : Lay M gid u S T Z x m en d mem)
    {hP : PieceInv M x.1.piece x.2.1 x.2.2} {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en mem f₀)
    (Gb : ℕ) (π : HSep M) (j : ℕ) :
    ∑ i ∈ range m, (callIn d m Gb π j Z mem).FLW i ≤ 2 * (m * Z) := by
  calc ∑ i ∈ range m, (callIn d m Gb π j Z mem).FLW i ≤ ∑ _i ∈ range m, 2 * Z :=
        sum_le_sum fun i hi => fx7f_FLW_le hl hf₀ hFL Gb π j (mem_range.1 hi)
    _ = 2 * (m * Z) := by rw [sum_const, card_range, smul_eq_mul]; ring

set_option maxHeartbeats 8000000 in
/-- **`fixPos` at a call within the envelopes**: from `FixPosW`, the frame, the parts, an input
pseudoflow in `FL`, the room `A0 + rOF7 C C₀ Rm m Z ≤ W + 5` above the heap top `A0 − 5` and the
zero area `wzF7 wzm m Z ≤ Wz`. -/
theorem fx7f_pos (hPW : FixPosW.{w}) (C C₀ : ℕ) (hC : 200000 ≤ C) {msP : Stmt} {Scr : ℕ → Prop}
    {cost Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ} (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hMS : MsCall.MsspCallSpec (pmap hP) msP Scr cost Rm wzm) (hScr : ∀ r, Scr r → r < 9300)
    (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans) (hface : (pmap hP).FaceTrans)
    (I : Input) {W Wz A0 : ℕ} (c : Config) (hc : WordsBounded W c)
    (hl : Lay M gid u S T Z x m en d c.nmem) (hm : 0 < m) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb c.nmem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z c.nmem).k) (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
    (hk0 : 0 < πj.k) {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en c.nmem f₀)
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (hz : ∀ a ≤ Wz, c.nmem a = 0) (hWzd : Wz < d) (hWlo : Wz < lo)
    (hhi : hi ≤ A0) (hfr : d + 4 + 7 * m ≤ A0)
    (hR : A0 + rOF7 C C₀ Rm m Z ≤ W + 5) (hWzF : wzF7 wzm m Z ≤ Wz) :
    ∃ c' t, Exec I W (fixPos msP) c c' t ∧
      t ≤ posT C C₀ cost m πj.k (callIn d m Gb π j Z c.nmem).cw.cnt ∧ SRegKeep c c' ∧
      (∀ a, a < A0 → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      FLHas Z m d en c'.nmem (fixPath (pmap hP) (fun y => u y.1) f₀ πj
        (Klein.msspPlaneK (pmap hP)) (frRef _) (negLay gid I x hP)) := by
  set q := callIn d m Gb π j Z c.nmem with hq
  have hkm : πj.k ≤ m := (SPath.k_le_card' πj).trans_eq hl.card_sdart
  have hqk : q.k = πj.k := hk.symm
  have hkm' : q.k ≤ m := by omega
  have hbF : q.cw.cnt = πj.faces.card := mkX_card hP hl hm hrot hS hj hk hd hk0
  have hb2 : q.cw.cnt ≤ 2 * m := by have := πj.card_faces_le; omega
  have hAS : q.AS ≤ m * Z := callIn_AS_le hl Gb π j
  have hK : q.K ≤ KM m Z := K_le_KM hAS hkm'
  have hL : 8 * fpB q.AS m q.k ≤ LM m Z := L_le_LM hAS hkm'
  have hrt0 := fx7f_rtL hP hpl hrot hface hl hf₀ (callIn_as hl (Gb := Gb) (π := π) (j := j))
    (k := q.k) (K := q.K) (by omega) le_rfl (n := πj.k) le_rfl
  have hrt : rtL (pmap hP) (fun y => u y.1 - (fpState (pmap hP) (fun y => u y.1) f₀ πj
      (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y) ≤ rtLM m Z :=
    hrt0.trans (Nat.mul_le_mul_left m hK)
  have hFLW : ∑ i ∈ range m, q.FLW i ≤ 2 * (m * Z) := fx7f_sumFLW_le hl hf₀ hFL Gb π j
  have ep : (mkX hP hl hm πj f₀ q (q.Qb A0)).p =
      A0 + 9 * m + 1 + 15 * q.k + lyP 0 q.cw.cnt q.k := by
    show lyP (q.Qb A0 + 15 * q.k) q.cw.cnt q.k = _
    rw [lyP_eq]
    show A0 + m + m + m + m + 1 + m + m + m + m + m + 15 * q.k + _ = _
    omega
  have hY := lyP0_mono hb2 hkm'
  have eLG : (mkX hP hl hm πj f₀ q (q.Qb A0)).LG = lgT q.cw.cnt πj.k := rfl
  have hLG := lgT_mono hb2 hkm
  have eK : (mkX hP hl hm πj f₀ q (q.Qb A0)).K = q.K := rfl
  have eMo : (mkX hP hl hm πj f₀ q (q.Qb A0)).Mo = moOf q.cw.cnt (8 * fpB q.AS m q.k) := rfl
  have hMo := moOf_mono hb2 hL
  have hMo2 := Nat.mul_le_mul hMo hMo
  have eSH : (mkX hP hl hm πj f₀ q (q.Qb A0)).SH = shOf q.cw.cnt q.k (8 * fpB q.AS m q.k) := rfl
  have hSH := shOf_mono hb2 hkm' hL
  have eWf : (mkX hP hl hm πj f₀ q (q.Qb A0)).Wf = wfOf q.cw.cnt πj.k := rfl
  have hWf := wfOf_mono hb2 hkm
  have eWN : (mkX hP hl hm πj f₀ q (q.Qb A0)).WN = 2 * (mkX hP hl hm πj f₀ q (q.Qb A0)).Wf + 1 +
      (mkX hP hl hm πj f₀ q (q.Qb A0)).Mo * (mkX hP hl hm πj f₀ q (q.Qb A0)).Mo +
      (mkX hP hl hm πj f₀ q (q.Qb A0)).Mo := rfl
  have hRm := Rm_le_RmS Rm hkm' hb2
  have hrtW := rtW_mono (n := m) (G := m) hrt
  have hfx := fxWB_mono (n := m) hrt
  have eKq : q.K = 16 * fpB q.AS m q.k := rfl
  have eQ : q.Qb A0 = A0 + 9 * m + 1 := by
    show A0 + m + m + m + m + 1 + m + m + m + m + m = _; omega
  have eR : rOF7 C C₀ Rm m Z = 100 + 100 * m + lyP 0 (2 * m) m + lgT (2 * m) m + RmS Rm m +
      negT C C₀ m + valM m Z := rfl
  have eV : valM m Z = 4 * (m * Z) + 20 * KM m Z + 2 * LM m Z + 2 * moOf (2 * m) (LM m Z) +
      3 * rtLM m Z + spWs m + fxWB m (rtLM m Z) + 3 * Z + m + 300 := rfl
  have eZ : wzF7 wzm m Z = wzm m (2 * Z) + shwM m Z + (9 * m + 1 + tsz m) +
      rtW m (rtLM m Z) m := rfl
  have eS : shwM m Z = shOf (2 * m) m (LM m Z) + (2 * wfOf (2 * m) m + 1 +
      moOf (2 * m) (LM m Z) * moOf (2 * m) (LM m Z) + moOf (2 * m) (LM m Z)) := rfl
  rw [eR, eV] at hR
  rw [eZ, eS] at hWzF
  have hW1 : q.Qb A0 + 15 * q.k + 16 ≤ W := by
    rw [eQ]; clear * - hR hkm'; omega
  have hW2 : ∑ i ∈ range m, q.FLW i + q.AS + 16 * fpB q.AS m q.k + m * Z + Z + q.k + 16 ≤ W := by
    rw [← eKq]; clear * - hR hkm' hFLW hAS hK; omega
  have hl14 : (mkX hP hl hm πj f₀ q (q.Qb A0)).p + (mkX hP hl hm πj f₀ q (q.Qb A0)).LG ≤ W := by
    rw [ep, eLG]; clear * - hR hkm' hY hLG; omega
  have hw1 : 16 * (mkX hP hl hm πj f₀ q (q.Qb A0)).K + 1 ≤ W := by
    rw [eK]; clear * - hR hK; omega
  have hw2 : (mkX hP hl hm πj f₀ q (q.Qb A0)).Mo + 3 * (mkX hP hl hm πj f₀ q (q.Qb A0)).K ≤ W := by
    rw [eK, eMo]; clear * - hR hK hMo; omega
  have hwz : wzm m (2 * Z) ≤ Wz := by clear * - hWzF; omega
  have hSHz : (mkX hP hl hm πj f₀ q (q.Qb A0)).SH + (mkX hP hl hm πj f₀ q (q.Qb A0)).WN ≤ Wz := by
    rw [eWN, eSH, eWf, eMo]; clear * - hWzF hSH hWf hMo hMo2; omega
  have hpw : lyP (q.Qb A0 + 15 * q.k) q.cw.cnt q.k + Rm m q.k q.cw.cnt ≤ W := by
    rw [lyP_eq, eQ]; clear * - hR hkm' hY hRm; omega
  have hKL : q.K + 8 * fpB q.AS m q.k + moOf q.cw.cnt (8 * fpB q.AS m q.k) ≤ W := by
    clear * - hR hK hL hMo; omega
  have hSz : 9 * m + 1 + tsz m ≤ Wz + 1 := by clear * - hWzF; omega
  have hWz : rtW m (rtL (pmap hP) (fun y => u y.1 - (fpState (pmap hP) (fun y => u y.1) f₀ πj
      (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y)) m ≤ Wz := by
    clear * - hWzF hrtW; omega
  have hW : (mkX hP hl hm πj f₀ q (q.Qb A0)).p + 60 * m + 60 + negT C C₀ m ≤ W := by
    rw [ep]; clear * - hR hkm' hY; omega
  have wL : 2 * q.K + rtL (pmap hP) (fun y => u y.1 - (fpState (pmap hP) (fun y => u y.1) f₀ πj
      (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y) ≤ W := by
    clear * - hR hK hrt; omega
  have hw2' : spWs m + 205 ≤ W := by clear * - hR; omega
  have hw3 : fxWB m (rtL (pmap hP) (fun y => u y.1 - (fpState (pmap hP) (fun y => u y.1) f₀ πj
      (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y)) ≤ W := by
    clear * - hR hfx; omega
  have hv : Z + Z + 2 * q.K + 2 * rtL (pmap hP) (fun y => u y.1 - (fpState (pmap hP)
      (fun y => u y.1) f₀ πj (Klein.msspPlaneK (pmap hP)) (frRef _) πj.k).1 y) ≤ W := by
    clear * - hR hK hrt; omega
  exact hPW C C₀ hC hP hMS hScr hpl hrot hface I c hc hl hm hS hj hk hd hk0 hf₀ hFL r04 r06 r07
    r00 hz hWzd hWlo hhi hfr hW1 hW2 hl14 hw1 hw2 hwz hSHz hpw hKL hSz hWz hW wL hw2' hw3 hv

set_option maxHeartbeats 8000000 in
/-- **`fixZero` at a call within the envelopes** (from `FixZeroW`). -/
theorem fx7f_zero (hZW : FixZeroW.{w}) (C C₀ : ℕ) (hC : 200000 ≤ C) {Rm : ℕ → ℕ → ℕ → ℕ}
    {wzm : ℕ → ℕ → ℕ} (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans) (hface : (pmap hP).FaceTrans)
    (I : Input) {W Wz A0 : ℕ} (c : Config) (hc : WordsBounded W c)
    (hl : Lay M gid u S T Z x m en d c.nmem) (hm : 0 < m) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb c.nmem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z c.nmem).k) (hk00 : πj.k = 0)
    {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) (hFL : FLHas Z m d en c.nmem f₀)
    (r04 : c.nreg 3004 = d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = Gb)
    (r00 : c.nreg 6800 = j) (hz : ∀ a ≤ Wz, c.nmem a = 0) (hWzd : Wz < d) (hWlo : Wz < lo)
    (hhi : hi ≤ A0) (hfr : d + 4 + 7 * m ≤ A0)
    (hR : A0 + rOF7 C C₀ Rm m Z ≤ W + 5) (hWzF : wzF7 wzm m Z ≤ Wz) :
    ∃ c' t, Exec I W fixZero c c' t ∧ t ≤ zT C C₀ m ∧ SRegKeep c c' ∧
      (∀ a, a < A0 → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      FLHas Z m d en c'.nmem (fixPath (pmap hP) (fun y => u y.1) f₀ πj
        (Klein.msspPlaneK (pmap hP)) (frRef _) (negLay gid I x hP)) := by
  set q := callIn d m Gb π j Z c.nmem with hq
  have hq0 : q.k = 0 := by omega
  have hAS : q.AS ≤ m * Z := callIn_AS_le hl Gb π j
  have hK : q.K ≤ KM m Z := K_le_KM hAS (by omega)
  have hK0 : 16 * fpB q.AS m 0 ≤ KM m Z := K_le_KM hAS (Nat.zero_le _)
  have hrt0 : rtL (pmap hP) (fun y => u y.1 - f₀ y) ≤ m * q.K :=
    fx7f_rtL hP hpl hrot hface hl hf₀ (callIn_as hl (Gb := Gb) (π := π) (j := j))
      (πj := πj) (k := q.k) (K := q.K) (by omega) le_rfl (n := 0) (Nat.zero_le _)
  have hrt : rtL (pmap hP) (fun y => u y.1 - f₀ y) ≤ rtLM m Z :=
    hrt0.trans (Nat.mul_le_mul_left m hK)
  have hFLW : ∑ i ∈ range m, q.FLW i ≤ 2 * (m * Z) := fx7f_sumFLW_le hl hf₀ hFL Gb π j
  have hrtW := rtW_mono (n := m) (G := m) hrt
  have hfx := fxWB_mono (n := m) hrt
  have eR : rOF7 C C₀ Rm m Z = 100 + 100 * m + lyP 0 (2 * m) m + lgT (2 * m) m + RmS Rm m +
      negT C C₀ m + valM m Z := rfl
  have eV : valM m Z = 4 * (m * Z) + 20 * KM m Z + 2 * LM m Z + 2 * moOf (2 * m) (LM m Z) +
      3 * rtLM m Z + spWs m + fxWB m (rtLM m Z) + 3 * Z + m + 300 := rfl
  have eZ : wzF7 wzm m Z = wzm m (2 * Z) + shwM m Z + (9 * m + 1 + tsz m) +
      rtW m (rtLM m Z) m := rfl
  rw [eR, eV] at hR
  rw [eZ] at hWzF
  have hZ1 : A0 + 9 * m + 16 ≤ W := by clear * - hR; omega
  have hZ2 : ∑ i ∈ range m, q.FLW i + 6 ≤ W := by clear * - hR hFLW; omega
  have hZ3 : q.AS + 16 * fpB q.AS m 0 + Z + 16 ≤ W := by clear * - hR hAS hK0; omega
  have hSz : 9 * m + 1 + tsz m ≤ Wz + 1 := by clear * - hWzF; omega
  have hWz : rtW m (rtL (pmap hP) (fun y => u y.1 - f₀ y)) m ≤ Wz := by
    clear * - hWzF hrtW; omega
  have hW : A0 + 9 * m + 1 + 60 * m + 60 + negT C C₀ m ≤ W := by clear * - hR; omega
  have wL : 2 * q.K + rtL (pmap hP) (fun y => u y.1 - f₀ y) ≤ W := by
    clear * - hR hK hrt; omega
  have hw2' : spWs m + 205 ≤ W := by clear * - hR; omega
  have hw3 : fxWB m (rtL (pmap hP) (fun y => u y.1 - f₀ y)) ≤ W := by clear * - hR hfx; omega
  have hv : Z + Z + 2 * q.K + 2 * rtL (pmap hP) (fun y => u y.1 - f₀ y) ≤ W := by
    clear * - hR hK hrt; omega
  exact hZW C C₀ hC hP hpl hrot hface I c hc hl hm hS hj hk hk00 hf₀ hFL r04 r06 r07 r00 hz hWzd
    hWlo hhi hfr hZ1 hZ2 hZ3 hSz hWz hW wL hw2' hw3 hv

end Call

end BKMNW

end PlanarFlow
