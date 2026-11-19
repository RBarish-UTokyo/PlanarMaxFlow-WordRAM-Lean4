module

public import PlanarFlow.BKMNW.Nf9bM

/-!
# The bounds of the two branches from the envelopes

**`pos_bnds`**, **`zero_bnds`**: all the word bounds and zero-area bounds of `fxPos_exec` and
`fxZero_exec` follow from `A0 + rOF9 C C₀ Rm m' Z' ≤ W` and `wzF9 wzm m' Z' ≤ Wz`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace F9b

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep NcFz SPath
  WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M₀ : CombMap D V F} {e : V → D} {he : ∀ v, M₀.tail (e v) = v}
variable {en : ℕ → D} {en' : ℕ → D ⊕ (V × Bool)} {m m' Z' d d' : ℕ}
  {cap f₀ : D ⊕ (V × Bool) → ℤ} {segs : List (SPath M₀)} {lo hi Gb j : ℕ} {mem : ℕ → ℕ}

set_option maxHeartbeats 16000000 in
/-- **The bounds of the branch `0 < k`.** -/
theorem pos_bnds (C C₀ : ℕ) {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem)
    (hk0 : 0 < (segs[j]'H.hj).k) {W Wz A0 : ℕ}
    (hRW : A0 + rOF9 C C₀ Rm m' Z' ≤ W) (hWZ : wzF9 wzm m' Z' ≤ Wz)
    (hWzd' : Wz < d') (hfr : d' + 4 + 7 * m' ≤ A0) :
    let q := cIn d' m' Gb segs j Z' mem
    let X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0)
    q.Qb A0 + 15 * q.k + 16 ≤ W ∧
    ∑ i ∈ range m', q.FLW i + q.AS + 16 * fpB q.AS m' q.k + m' * Z' + Z' + q.k + 16 ≤ W ∧
    X.p + X.LG ≤ W ∧ 16 * X.K + 1 ≤ W ∧ X.Mo + 3 * X.K ≤ W ∧
    wzm m (2 * Z') ≤ Wz ∧ X.SH + X.WN ≤ Wz ∧
    lyP (q.Qb A0 + 15 * q.k) q.cw.cnt q.k + Rm m q.k q.cw.cnt ≤ W ∧
    q.K + 8 * fpB q.AS m' q.k + moOf q.cw.cnt (8 * fpB q.AS m' q.k) ≤ W ∧
    9 * m + 1 + tsz m ≤ Wz + 1 ∧
    rtW m (rtL M₀ (fun y => cap (.inl y) - (X.st (segs[j]'H.hj).k).1 (.inl y))) m ≤ Wz ∧
    X.p + 60 * m + 60 + negT C C₀ m ≤ W ∧
    2 * q.K + rtL M₀ (fun y => cap (.inl y) - (X.st (segs[j]'H.hj).k).1 (.inl y)) ≤ W ∧
    spWs m + 205 ≤ W ∧
    fxWB m (rtL M₀ (fun y => cap (.inl y) - (X.st (segs[j]'H.hj).k).1 (.inl y))) ≤ W ∧
    Z' + Z' + 2 * q.K + 2 * rtL M₀ (fun y => cap (.inl y) -
      (X.st (segs[j]'H.hj).k).1 (.inl y)) ≤ W := by
  dsimp only
  set q := cIn d' m' Gb segs j Z' mem with hq
  have eqk : (cIn d' m' Gb segs j Z' mem).k = q.k := rfl
  have eqm : (cIn d' m' Gb segs j Z' mem).m = q.m := rfl
  have eqP : (cIn d' m' Gb segs j Z' mem).PDb = q.PDb := rfl
  have eqc : (cIn d' m' Gb segs j Z' mem).cw.cnt = q.cw.cnt := rfl
  have eqK : (cIn d' m' Gb segs j Z' mem).K = q.K := rfl
  have eqA : (cIn d' m' Gb segs j Z' mem).AS = q.AS := rfl
  have eqF : ∑ i ∈ range m', (cIn d' m' Gb segs j Z' mem).FLW i = ∑ i ∈ range m', q.FLW i := rfl
  set X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q (q.Qb A0) with hX
  have hmm := H.mm
  have hkm : q.k ≤ m := pq_k_le H
  have hkq : (segs[j]'H.hj).k = q.k := (pq_k H).symm
  have hk' : q.k ≤ m' := by omega
  have hb : q.cw.cnt ≤ 2 * q.k := by
    rw [mkP_card H hk0, ← hkq]; exact (segs[j]'H.hj).card_faces_le
  have hb' : q.cw.cnt ≤ 2 * m' := by omega
  have hAS := pq_AS_le H
  have hFLW := pq_FLW_le H
  have hK : q.K ≤ KM9 m' Z' := pq_K_le H hk'
  have hL : 8 * fpB q.AS m' q.k ≤ LM9 m' Z' := pq_L_le H hk'
  have hKM : KM9 m' Z' = 2 * LM9 m' Z' := by unfold KM9 LM9; ring
  have hfpK : 16 * fpB q.AS m' q.k = q.K := rfl
  have hQe : q.Qb A0 = A0 + 9 * m' + 1 := by
    show A0 + m' + m' + m' + m' + 1 + m' + m' + m' + m' + m' = _; omega
  -- the fields of `X`
  have hXK : X.K = q.K := rfl
  have hXL : X.L = 8 * fpB q.AS m' q.k := rfl
  have hXp : X.p = q.Qb A0 + 15 * q.k + lyP 0 q.cw.cnt q.k := lyP_eq9 _ _ _
  have hXLG : X.LG = lgT9 q.cw.cnt q.k := by
    show 4 * (6300 * (q.cw.cnt * lg q.cw.cnt ^ 2 + 2 * (segs[j]'H.hj).k * lg q.cw.cnt)) + 3 = _
    rw [hkq]; rfl
  have hXMo : X.Mo = moOf q.cw.cnt (8 * fpB q.AS m' q.k) := rfl
  have hXSH : X.SH = shOf q.cw.cnt q.k (8 * fpB q.AS m' q.k) := rfl
  have hXWf : X.Wf = wfOf q.cw.cnt q.k := by
    show MsCall.fW _ _ = _; unfold wfOf lySb; rw [← hkq]; rfl
  have hXWN : X.WN = 2 * X.Wf + 1 + X.Mo * X.Mo + X.Mo := rfl
  -- monotone bounds
  have m1 := lyP0_mono9 hb' hk'
  have m2 := lgT9_mono hb' hk'
  have m3 := moOf_mono9 hb' hL
  have m4 := shOf_mono9 hb' hk' hL
  have m5 := wfOf_mono9 hb' hk'
  have m6 : moOf q.cw.cnt (8 * fpB q.AS m' q.k) * moOf q.cw.cnt (8 * fpB q.AS m' q.k) ≤
      moOf (2 * m') (LM9 m' Z') * moOf (2 * m') (LM9 m' Z') := Nat.mul_le_mul m3 m3
  have hshw : X.SH + X.WN ≤ shw9 m' Z' := by
    rw [hXWN, hXWf, hXMo, hXSH]; unfold shw9; omega
  have hRm : Rm m q.k q.cw.cnt + negT C C₀ m ≤
      ∑ n ∈ range (m' + 1), (RmS9 Rm n + negT C C₀ n) := by
    have h1 := Rm_le_RmS9 Rm (n := m) hkm (by omega : q.cw.cnt ≤ 2 * m)
    have h2 := sum_ge9 (f := fun n => RmS9 Rm n + negT C C₀ n) hmm
    (try simp only at h2); omega
  have hRm' : Rm m q.k q.cw.cnt ≤ ∑ n ∈ range (m' + 1), (RmS9 Rm n + negT C C₀ n) := by omega
  have hnT : negT C C₀ m ≤ ∑ n ∈ range (m' + 1), (RmS9 Rm n + negT C C₀ n) := by omega
  have hwzS := sum_ge9 (f := fun n => wzm n (2 * Z') + (9 * n + 1 + tsz n) +
    rtW n (n * KM9 m' Z') n) hmm
  try simp only at hwzS
  have hspS := sum_ge9 (f := fun n => spWs n + fxWB n (n * KM9 m' Z')) hmm
  try simp only at hspS
  have hrO : A0 + (100 + 100 * m' + lyP 0 (2 * m') m' + lgT9 (2 * m') m' +
      ∑ n ∈ range (m' + 1), (RmS9 Rm n + negT C C₀ n) + (4 * (m' * Z') + 20 * KM9 m' Z' +
      2 * LM9 m' Z' + 2 * moOf (2 * m') (LM9 m' Z') + 3 * (m' * KM9 m' Z') + 3 * Z' + m' + 300 +
      ∑ n ∈ range (m' + 1), (spWs n + fxWB n (n * KM9 m' Z')))) ≤ W := hRW
  have hwZ : ∑ n ∈ range (m' + 1), (wzm n (2 * Z') + (9 * n + 1 + tsz n) +
      rtW n (n * KM9 m' Z') n) + shw9 m' Z' ≤ Wz := hWZ
  -- `X.Good`
  have hl2 : X.SH + X.WN < q.Qb A0 := by rw [hQe]; omega
  have hl14 : X.p + X.LG ≤ W := by rw [hXp, hXLG, hQe]; omega
  have hw1 : 16 * X.K + 1 ≤ W := by rw [hXK]; omega
  have hw2 : X.Mo + 3 * X.K ≤ W := by rw [hXMo, hXK]; omega
  have hG : X.Good W := mkP_good H hk0 hl2 hl14 hw1 hw2
  -- the lengths of the final call
  have hcard := card_eq_m H.enum
  have hrtL : rtL M₀ (fun y => cap (.inl y) - (X.st (segs[j]'H.hj).k).1 (.inl y)) ≤ m * q.K := by
    have := rtL_le_mul9 M₀ (fun y => cap (.inl y) - (X.st (segs[j]'H.hj).k).1 (.inl y))
      (B := q.K) (fun y => lenK_of_good hG (.inl y))
    rwa [hcard] at this
  have hmK1 : m * q.K ≤ m * KM9 m' Z' := Nat.mul_le_mul_left _ hK
  have hmK2 : m * KM9 m' Z' ≤ m' * KM9 m' Z' := Nat.mul_le_mul_right _ hmm
  have hrW := rtW_mono9 (n := m) (G := m) (hrtL.trans hmK1)
  have hfW := fxWB_mono9 (n := m) (hrtL.trans hmK1)
  have h2Z : m' * (2 * Z') = 2 * (m' * Z') := by ring
  refine ⟨by rw [hQe]; omega, by omega, hl14, hw1, hw2, by omega, by omega,
    by rw [lyP_eq9, hQe]; omega, by omega, by omega, by omega, by rw [hXp, hQe]; omega,
    by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 16000000 in
/-- **The bounds of the branch `k = 0`.** -/
theorem zero_bnds (C C₀ : ℕ) {Rm : ℕ → ℕ → ℕ → ℕ} {wzm : ℕ → ℕ → ℕ}
    (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem)
    (hk00 : (segs[j]'H.hj).k = 0) {W Wz A0 : ℕ}
    (hRW : A0 + rOF9 C C₀ Rm m' Z' ≤ W) (hWZ : wzF9 wzm m' Z' ≤ Wz) :
    let q := cIn d' m' Gb segs j Z' mem
    A0 + 9 * m' + 16 ≤ W ∧
    ∑ i ∈ range m', q.FLW i + 6 ≤ W ∧
    q.AS + 16 * fpB q.AS m' 0 + Z' + 16 ≤ W ∧
    9 * m + 1 + tsz m ≤ Wz + 1 ∧
    rtW m (rtL M₀ (fun y => cap (.inl y) - f₀ (.inl y))) m ≤ Wz ∧
    A0 + 9 * m' + 1 + 60 * m + 60 + negT C C₀ m ≤ W ∧
    2 * q.K + rtL M₀ (fun y => cap (.inl y) - f₀ (.inl y)) ≤ W ∧
    spWs m + 205 ≤ W ∧ fxWB m (rtL M₀ (fun y => cap (.inl y) - f₀ (.inl y))) ≤ W ∧
    Z' + Z' + 2 * q.K + 2 * rtL M₀ (fun y => cap (.inl y) - f₀ (.inl y)) ≤ W := by
  dsimp only
  set q := cIn d' m' Gb segs j Z' mem with hq
  have eqk : (cIn d' m' Gb segs j Z' mem).k = q.k := rfl
  have eqm : (cIn d' m' Gb segs j Z' mem).m = q.m := rfl
  have eqP : (cIn d' m' Gb segs j Z' mem).PDb = q.PDb := rfl
  have eqc : (cIn d' m' Gb segs j Z' mem).cw.cnt = q.cw.cnt := rfl
  have eqK : (cIn d' m' Gb segs j Z' mem).K = q.K := rfl
  have eqA : (cIn d' m' Gb segs j Z' mem).AS = q.AS := rfl
  have eqF : ∑ i ∈ range m', (cIn d' m' Gb segs j Z' mem).FLW i = ∑ i ∈ range m', q.FLW i := rfl
  have hmm := H.mm
  have hkq : (segs[j]'H.hj).k = q.k := (pq_k H).symm
  have hq0 : q.k = 0 := by rw [← hkq]; exact hk00
  have hAS := pq_AS_le H
  have hFLW := pq_FLW_le H
  have hK : q.K ≤ KM9 m' Z' := pq_K_le H (by omega)
  have hK0 : 16 * fpB q.AS m' 0 = q.K := by show _ = 16 * fpB q.AS q.m q.k; rw [hq0]; rfl
  have hnT := sum_ge9 (f := fun n => RmS9 Rm n + negT C C₀ n) hmm
  try simp only at hnT
  have hwzS := sum_ge9 (f := fun n => wzm n (2 * Z') + (9 * n + 1 + tsz n) +
    rtW n (n * KM9 m' Z') n) hmm
  try simp only at hwzS
  have hspS := sum_ge9 (f := fun n => spWs n + fxWB n (n * KM9 m' Z')) hmm
  try simp only at hspS
  have hrO : A0 + (100 + 100 * m' + lyP 0 (2 * m') m' + lgT9 (2 * m') m' +
      ∑ n ∈ range (m' + 1), (RmS9 Rm n + negT C C₀ n) + (4 * (m' * Z') + 20 * KM9 m' Z' +
      2 * LM9 m' Z' + 2 * moOf (2 * m') (LM9 m' Z') + 3 * (m' * KM9 m' Z') + 3 * Z' + m' + 300 +
      ∑ n ∈ range (m' + 1), (spWs n + fxWB n (n * KM9 m' Z')))) ≤ W := hRW
  have hwZ : ∑ n ∈ range (m' + 1), (wzm n (2 * Z') + (9 * n + 1 + tsz n) +
      rtW n (n * KM9 m' Z') n) + shw9 m' Z' ≤ Wz := hWZ
  have hcard := card_eq_m H.enum
  have hrtL : rtL M₀ (fun y => cap (.inl y) - f₀ (.inl y)) ≤ m * q.K := by
    have := rtL_le_mul9 M₀ (fun y => cap (.inl y) - f₀ (.inl y)) (B := q.K)
      (fun y => (capf_le H (.inl y)).2)
    rwa [hcard] at this
  have hmK1 : m * q.K ≤ m * KM9 m' Z' := Nat.mul_le_mul_left _ hK
  have hmK2 : m * KM9 m' Z' ≤ m' * KM9 m' Z' := Nat.mul_le_mul_right _ hmm
  have hrW := rtW_mono9 (n := m) (G := m) (hrtL.trans hmK1)
  have hfW := fxWB_mono9 (n := m) (hrtL.trans hmK1)
  have h2Z : m' * (2 * Z') = 2 * (m' * Z') := by ring
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega⟩

end F9b

end BKMNW

end PlanarFlow
