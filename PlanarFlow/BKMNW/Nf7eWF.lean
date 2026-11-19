module

public import PlanarFlow.BKMNW.Nf7cK
public import PlanarFlow.BKMNW.Nf7eWE

/-!
# The final step of `fixP` with a per-address word bound

**`finP_execW`**: `finP_exec` with the word hypothesis
`5 Tb + LABb + 3 d + 60 m + 60 + PDb + CWb + CRb + FWb + k + negT ≤ W` replaced by the bound of the
largest base, `Tb + 60 m + 60 + negT ≤ W` (`Tb = r9469`, the base of the final step's scratch; the
frame, `LAB`, `PD`, `CW`, `CR`, `FW` are below `Tb` by `hlo`). Also `finAB_execW`
(`Tb + 22m + 13 + negT ≤ W`). Same programs and conclusions.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep
  WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Call

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ}

set_option maxHeartbeats 2000000 in
/-- **Phases A and B of the final step at a max-flow call.** -/
theorem finAB_execW (C C₀ : ℕ) (hC : 200000 ≤ C) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (g : SDart (pdarts M x.1.piece x.2.1) → ℤ)
    (hpre : NegPre (pmap hP) (fun y => u y.1 - g y)) (I P' : Input) {W : ℕ}
    (c : Config) (hc : WordsBounded W c) (hl : Lay M gid u S T Z x m en d c.nmem) (hm : 0 < m)
    {Tb k PDb CWb CRb FWb K Wz : ℕ}
    (r69 : c.nreg 9469 = Tb) (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1)
    (r34 : c.nreg 9434 = d + 4 + 3 * m) (r35 : c.nreg 9435 = d + 4 + 6 * m)
    (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K) (r01 : c.nreg 9401 = k)
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = d + 4 + m) (r31 : c.nreg 9431 = d + 4 + 2 * m)
    (r74 : c.nreg 9374 = CWb) (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb)
    (hPD : ∀ l < k, c.nmem (PDb + l) < m)
    (hdist : ∀ l < k, ∀ l' < k, c.nmem (PDb + l) ≠ c.nmem (d + 4 + m + c.nmem (PDb + l')) ∧
      (c.nmem (PDb + l) = c.nmem (PDb + l') → l = l') ∧
      (c.nmem (d + 4 + m + c.nmem (PDb + l)) = c.nmem (d + 4 + m + c.nmem (PDb + l')) → l = l'))
    (hFLo : ∀ i < m, (∀ l < k, c.nmem (PDb + l) ≠ i ∧ c.nmem (d + 4 + m + c.nmem (PDb + l)) ≠ i) →
      (c.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i))
    (hCW : ∀ l < k, (c.nmem (CWb + l) : ℤ) = u (en (c.nmem (PDb + l))))
    (hCR : ∀ l < k, (c.nmem (CRb + l) : ℤ) = u (en (c.nmem (d + 4 + m + c.nmem (PDb + l)))))
    (hFW : ∀ l < k, (c.nmem (FWb + l) : ℤ) =
      g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm (c.nmem (PDb + l))) + K)
    (hgr : ∀ l < k, g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm
      (c.nmem (d + 4 + m + c.nmem (PDb + l)))) =
        - g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm (c.nmem (PDb + l))))
    (hgK : ∀ i < m, |g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i)| ≤ K)
    (hℓK : ∀ i < m, |u (en i) - g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i)| ≤ K)
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hS : 9 * m + 1 + tsz m ≤ Wz + 1) (hWzd : Wz < d)
    (hlo : d + 4 + 7 * m ≤ Tb ∧ PDb + k ≤ Tb ∧ CWb + k ≤ Tb ∧ CRb + k ≤ Tb ∧ FWb + k ≤ Tb)
    (hWz : rtW m (rtL (pmap hP) (fun y => u y.1 - g y)) m ≤ Wz)
    (hW : Tb + 22 * m + 13 + negT C C₀ m ≤ W)
    (wL : 2 * K + rtL (pmap hP) (fun y => u y.1 - g y) ≤ W) (hw2 : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL (pmap hP) (fun y => u y.1 - g y)) ≤ W)
    (hv : ∀ i < m, c.nmem (d + 4 + 3 * m + i) + Z + K ≤ W)
    (hx : ∀ l < k, c.nmem (CWb + l) + K + K ≤ W)
    (hy : ∀ l < k, c.nmem (CRb + l) + c.nmem (FWb + l) ≤ W) :
    ∃ c' t, Exec P' W (.seq finA finB) c c' t ∧ t ≤ 9 * negT C C₀ m + 486 * m + 21 * k + 8300 ∧
      c'.nreg 9477 = Tb ∧ c'.nreg 9479 = Tb + m ∧ c'.nreg 9480 = Tb + m + m + 1 ∧
      c'.nreg 9481 = Tb + m + m + 1 + (10 * m + 6) ∧
      (∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → c'.nreg r = c.nreg r) ∧
      (∀ i < m, c'.nmem (Tb + i) = (u (en i) -
        g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i) + K).toNat) ∧
      Res (layIds hP hl hm hpre.2.2.1) (pmap hP).dual (rtL (pmap hP) (fun y => u y.1 - g y))
        (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)
        (negLay gid I x hP (fun y => u y.1 - g y)) (Tb + m + m + 1 + (10 * m + 6))
        (Tb + m + m + 1 + (10 * m + 6) +
          Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd))) c' ∧
      c'.nmem (Tb + m + m + 1 + 1) = (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card ∧
      c'.nmem (Tb + m + m + 1 + 1 + 1) =
        ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd) ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∀ a, Wz < a → a < Tb → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := hlo
  obtain ⟨hf1, hf2, hf3⟩ := fsz_le hP hl (layIds hP hl hm hpre.2.2.1).gd
  obtain ⟨c₁, t₁, e₁, ht₁, a77, a79, a80, a81, a82, A1, A2, A3, am, ak, ar, arm, ao⟩ :=
    finA_execW (P := P') c hc (T := Tb) (CWb := CWb) (CRb := CRb) (FWb := FWb) r69 r00 r36 r34 r35
      r21 r10 r01 r02 r30 r74 r75 r76 hPD (fun i hi => (hl.rv i hi).1) hdist
      ⟨by omega, by omega, l2, by omega, l3, l4, l5⟩ (by omega) hv hx hy
  have hLN := ln_all (nm := c.nmem) (nm' := c₁.nmem) (Ui := fun i => u (en i))
    (gi := fun i => g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i)) hPD hdist A1 A2 A3
    (fun i hi => by
      have := (hl.cp i hi).1
      rw [show d + 4 + 3 * m + i = d + 4 + 3 * m + i from rfl]; exact this)
    hFLo hCW hCR hFW hgr hgK hℓK
  have hl₁ : Lay M gid u S T Z x m en d c₁.nmem := hl.congr fun a h1 h2 => am a (Or.inl (by omega))
  obtain ⟨c₂, t₂, e₂, ht₂, b00, b01, b02, b03, b04, b05, b06, b22, b24, bk, bm, br, brm, bo⟩ :=
    fnN_exec (P := P') c₁ e₁.wb_right
  have hl₂ : Lay M gid u S T Z x m en d c₂.nmem := by rw [bm]; exact hl₁
  have k1 : ∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → c₁.nreg r = c.nreg r := fun r hr h2 =>
    ak r (by omega) (by omega) (by omega)
  have k2 : ∀ r, KeepR r → c₂.nreg r = c₁.nreg r := fun r hr => bk r
    (by unfold KeepR at hr; omega) (by unfold KeepR at hr; omega) (by unfold KeepR at hr; omega)
  have eE : layEn (pdarts M x.1.piece x.2.1) en m hl₂.en_mem hm =
      layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm := rfl
  have eId : layIds hP hl₂ hm hpre.2.2.1 = layIds hP hl hm hpre.2.2.1 := rfl
  obtain ⟨c₃, t₃, e₃, ht₃, cz, cRes, cIn, cK, ck1, ck2, cr, crm, co⟩ :=
    negStep_lay_exec' C C₀ hC hP (fun y => u y.1 - g y) hpre I P' c₂ e₂.wb_right hl₂ hm
      (LNb := Tb) (K := K) (S' := 0) (A := Tb + m + m + 1) (Wz := Wz)
      (Ob := Tb + m + m + 1 + (10 * m + 6)) (p := Tb + m + m + 1 + (10 * m + 6) + (10 * m + 6))
      (by rw [b00, k1 _ (keepR_ge (by norm_num)) (by norm_num), r00])
      (by rw [b01, k1 _ (keepR_ge (by norm_num)) (by norm_num), r30])
      (by rw [b02, k1 _ (keepR_ge (by norm_num)) (by norm_num), r31]) (by rw [b03, a77])
      (by rw [b04, k1 _ (keepR_ge (by norm_num)) (by norm_num), r10]) b05 (by rw [b06, a80])
      (by rw [b22, a81]) (by rw [b24, a82])
      (fun i hi => (congrFun bm (Tb + i)).trans (by rw [hLN i hi, layEn_val hi]))
      (fun i hi => by
        show |u (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i).1 -
          g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i)| ≤ K
        rw [layEn_val hi]; exact hℓK i hi)
      (fun a ha => by
        rw [bm, am a (Or.inl (by omega))]; exact hz a ha)
      (by omega) hWzd (by omega) (by omega) (Or.inl (by omega)) (by omega) (by omega) (by omega)
      wL hWz (by rw [eId]; omega) (by rw [eId]; omega) (by omega) hw2 hw3
  have k3 : ∀ r, KeepR r → c₃.nreg r = c₂.nreg r := fun r hr => by
    by_cases h3 : 3000 ≤ r ∧ r ≤ 3012
    · exact ck1 r h3.1 h3.2
    · unfold KeepR at hr
      exact ck2 r (by unfold ncScr; omega) (by unfold NsScr; omega)
  have hA0 : Wz < Tb := by omega
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), ?_,
    by rw [k3 _ (keepR_ge (by norm_num)), k2 _ (keepR_ge (by norm_num)), a77],
    by rw [k3 _ (keepR_ge (by norm_num)), k2 _ (keepR_ge (by norm_num)), a79],
    by rw [k3 _ (keepR_ge (by norm_num)), k2 _ (keepR_ge (by norm_num)), a80],
    by rw [k3 _ (keepR_ge (by norm_num)), k2 _ (keepR_ge (by norm_num)), a81],
    fun r hr h2 => by rw [k3 r hr, k2 r hr, k1 r hr h2], fun i hi => ?_,
    cRes, ?_, ?_, cz, fun a h1 h2 => ?_, by rw [cr, br, ar], by rw [crm, brm, arm],
    by rw [co, bo, ao]⟩
  · clear * - ht₁ ht₂ ht₃ hf1 hf2
    omega
  · rw [cK _ (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)), bm]
    exact hLN i hi
  · exact cIn.rm
  · rw [show Tb + m + m + 1 + 1 + 1 = Tb + m + m + 1 + 2 by omega]; exact cIn.rk
  · rw [cK _ h1 (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega)), bm,
      am a (Or.inl h2)]

set_option maxHeartbeats 4000000 in
/-- **The final step of `fixP` at a max-flow call.** -/
theorem finP_execW (C C₀ : ℕ) (hC : 200000 ≤ C) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (g : SDart (pdarts M x.1.piece x.2.1) → ℤ)
    (hpre : NegPre (pmap hP) (fun y => u y.1 - g y)) (I P' : Input) {W : ℕ}
    (c : Config) (hc : WordsBounded W c) (hl : Lay M gid u S T Z x m en d c.nmem) (hm : 0 < m)
    {Tb k PDb CWb CRb FWb K Wz LABb : ℕ} {χ : SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M) → ℤ}
    (hχ : negLay gid I x hP (fun y => u y.1 - g y) = some χ)
    (r69 : c.nreg 9469 = Tb) (r00 : c.nreg 9400 = m) (r36 : c.nreg 9436 = 1)
    (r34 : c.nreg 9434 = d + 4 + 3 * m) (r35 : c.nreg 9435 = d + 4 + 6 * m)
    (r21 : c.nreg 9421 = Z) (r10 : c.nreg 9310 = K) (r01 : c.nreg 9401 = k)
    (r02 : c.nreg 9402 = PDb) (r30 : c.nreg 9430 = d + 4 + m) (r31 : c.nreg 9431 = d + 4 + 2 * m)
    (r74 : c.nreg 9374 = CWb) (r75 : c.nreg 9375 = CRb) (r76 : c.nreg 9376 = FWb)
    (r05 : c.nreg 9405 = LABb)
    (hLAB : ∀ i < m, c.nmem (LABb + i) = olab (nxF d m c.nmem) i + 1)
    (hPD : ∀ l < k, c.nmem (PDb + l) < m)
    (hdist : ∀ l < k, ∀ l' < k, c.nmem (PDb + l) ≠ c.nmem (d + 4 + m + c.nmem (PDb + l')) ∧
      (c.nmem (PDb + l) = c.nmem (PDb + l') → l = l') ∧
      (c.nmem (d + 4 + m + c.nmem (PDb + l)) = c.nmem (d + 4 + m + c.nmem (PDb + l')) → l = l'))
    (hFLo : ∀ i < m, (∀ l < k, c.nmem (PDb + l) ≠ i ∧ c.nmem (d + 4 + m + c.nmem (PDb + l)) ≠ i) →
      (c.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i))
    (hCW : ∀ l < k, (c.nmem (CWb + l) : ℤ) = u (en (c.nmem (PDb + l))))
    (hCR : ∀ l < k, (c.nmem (CRb + l) : ℤ) = u (en (c.nmem (d + 4 + m + c.nmem (PDb + l)))))
    (hFW : ∀ l < k, (c.nmem (FWb + l) : ℤ) =
      g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm (c.nmem (PDb + l))) + K)
    (hgr : ∀ l < k, g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm
      (c.nmem (d + 4 + m + c.nmem (PDb + l)))) =
        - g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm (c.nmem (PDb + l))))
    (hgK : ∀ i < m, |g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i)| ≤ K)
    (hℓK : ∀ i < m, |u (en i) - g (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i)| ≤ K)
    (hfin : ∀ i < m, 0 ≤ (Z : ℤ) + (g + (pmap hP).cob χ)
      (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i))
    (hz : ∀ a ≤ Wz, c.nmem a = 0) (hS : 9 * m + 1 + tsz m ≤ Wz + 1) (hWzd : Wz < d)
    (hlo : d + 4 + 7 * m ≤ LABb ∧ LABb + m ≤ Tb ∧ PDb + k ≤ Tb ∧ CWb + k ≤ Tb ∧ CRb + k ≤ Tb ∧
      FWb + k ≤ Tb)
    (hWz : rtW m (rtL (pmap hP) (fun y => u y.1 - g y)) m ≤ Wz)
    (hW : Tb + 60 * m + 60 + negT C C₀ m ≤ W)
    (wL : 2 * K + rtL (pmap hP) (fun y => u y.1 - g y) ≤ W) (hw2 : spWs m + 205 ≤ W)
    (hw3 : fxWB m (rtL (pmap hP) (fun y => u y.1 - g y)) ≤ W)
    (hv : ∀ i < m, c.nmem (d + 4 + 3 * m + i) + Z + K + K +
      2 * rtL (pmap hP) (fun y => u y.1 - g y) ≤ W)
    (hx : ∀ l < k, c.nmem (CWb + l) + K + K ≤ W)
    (hy : ∀ l < k, c.nmem (CRb + l) + c.nmem (FWb + l) ≤ W) :
    ∃ c' t, Exec P' W finP c c' t ∧ t ≤ finT C C₀ m k ∧
      FLHas Z m d en c'.nmem (g + (pmap hP).cob χ) ∧
      (∀ a ≤ Wz, c'.nmem a = 0) ∧
      (∀ a, Wz < a → a < Tb → ¬ (d + 4 + 6 * m ≤ a ∧ a < d + 4 + 6 * m + m) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l0, l1, l2, l3, l4, l5⟩ := hlo
  set E := layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm with hE
  set Ob := Tb + m + m + 1 + (10 * m + 6) with hOb
  obtain ⟨hf1, hf2, hf3⟩ := fsz_le hP hl (layIds hP hl hm hpre.2.2.1).gd
  obtain ⟨c₂, t₂, e₂, ht₂, a77, a79, a80, a81, ak, aLN, aRes, aM, aK, az, am, ar, arm, ao⟩ :=
    finAB_execW C C₀ hC hP g hpre I P' c hc hl hm (Tb := Tb) (k := k) (PDb := PDb) (CWb := CWb)
      (CRb := CRb) (FWb := FWb) (K := K) (Wz := Wz) r69 r00 r36 r34 r35 r21 r10 r01 r02 r30 r31
      r74 r75 r76 hPD hdist hFLo hCW hCR hFW hgr hgK hℓK hz hS hWzd
      ⟨by omega, l2, l3, l4, l5⟩ hWz (by omega) wL hw2 hw3
      (fun i hi => by have := hv i hi; omega) hx hy
  -- the outcome
  rw [hχ] at aRes
  obtain ⟨-, a0, w, ι, hw2', hw1, hv', hcov⟩ := aRes
  set G := layIds hP hl hm hpre.2.2.1 with hG
  set Pr := repsN (pmap hP).dual G.gd with hPr
  set m' := Pr.card with hm'
  set k' := ck (pmap hP).dual Pr with hk'
  have hfin' : Frame.fin m' k' = 4 + 5 * k' + m' := rfl
  rw [hfin'] at hw1 hv'
  have k2 : ∀ r, KeepR r → (r < 9477 ∨ 9498 < r) → c₂.nreg r = c.nreg r := ak
  have m2 : ∀ a, Wz < a → a < Tb → c₂.nmem a = c.nmem a := am
  have hk'm : k' ≤ m ∧ m' ≤ m := by
    have := ck_le_n (pmap hP).dual Pr
    rw [hl.card_sdart] at this
    exact ⟨this, hf3⟩
  have hR0 : ∀ v, Ob + (4 + 5 * k' + m') + 2 + v = Ob + (4 + 5 * k' + m') + 2 + v := fun _ => rfl
  have hid : ∀ v < w, c₂.nmem (Ob + (4 + 5 * k' + m') + 2 + v) < m := fun v hv => by
    rw [(hv' v hv).2.1]; exact G.gv_lt _
  have hRV2 : ∀ i < m, c₂.nmem (d + 4 + m + i) < m := fun i hi => by
    rw [m2 _ (by omega) (by omega)]; exact (hl.rv i hi).1
  have hLAB2 : ∀ i < m, c₂.nmem (LABb + i) ≤ m := fun i hi => by
    rw [m2 _ (by omega) (by omega), hLAB i hi]; have := olab_lt hl.permOn_nx hi; omega
  have hVL : ∀ v < w, c₂.nmem (Ob + (4 + 5 * k' + m') + 2 + m' + m' + v) ≤ 2 * rtL (pmap hP) (fun y => u y.1 - g y) := fun v hv => by
    obtain ⟨-, -, h3, h4⟩ := hv' v hv
    rw [show Ob + (4 + 5 * k' + m') + 2 + m' + m' + v = Ob + (4 + 5 * k' + m') + 2 + 2 * m' + v
      by omega, h3]
    exact Int.toNat_le.2 (by have := (abs_le.1 h4).2; push_cast; omega)
  have h4 : ∀ i < m, c₂.nmem (d + 4 + 3 * m + i) + Z + K + K + 2 * rtL (pmap hP) (fun y => u y.1 - g y) ≤ W := fun i hi => by
    rw [m2 _ (by omega) (by omega)]; exact hv i hi
  have h5 : 2 * rtL (pmap hP) (fun y => u y.1 - g y) + K ≤ W := by have := hv 0 hm; omega
  obtain ⟨c₃, t₃, e₃, ht₃, cFL, cK, cn, cr, crm, co⟩ :=
    finC_execW (P := P') c₂ e₂.wb_right (T := Tb) (m := m) (A := Tb + m + m + 1) (Ob := Ob)
      (m' := m') (k' := k') (w := w) (CPb := d + 4 + 3 * m) (RVb := d + 4 + m) (LABb := LABb)
      (FLb := d + 4 + 6 * m) (Z := Z) (K := K) (B := 2 * rtL (pmap hP) (fun y => u y.1 - g y)) a77 a79 a80 a81
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r00])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r36])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r34])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r30])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r05])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r35])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r21])
      (by rw [k2 _ (keepR_ge (by norm_num)) (by norm_num), r10]) aM aK hw1 hw2' hid hRV2 hLAB2
      ⟨by omega, by omega, by omega, by omega, by omega, l1⟩ (by omega) hVL h4 h5
  refine ⟨c₃, _, e₂.seq e₃, ?_, fun i hi => ?_, fun a ha => ?_, fun a h1 h2 h3 => ?_,
    fun r hr h2 => ?_, by rw [cr, ar], by rw [crm, arm], by rw [co, ao]⟩
  · unfold finT; omega
  · -- the flow array holds `g + cob χ`
    rw [cFL i hi, fext_mem _ (hl.en_mem i hi)]
    have hft : (pmap hP).FaceTrans := hpre.2.2.1
    have eE : ∀ j (hj : j < m), (⟨en j, hl.en_mem j hj⟩ : SDart (pdarts M x.1.piece x.2.1)) = E j :=
      fun j hj => (Subtype.ext (layEn_val hj)).symm
    rw [eE i hi]
    set IDb := Ob + (4 + 5 * k' + m') + 2 with hIDb
    set VLb := Ob + (4 + 5 * k' + m') + 2 + m' + m' with hVLb
    set nm0 := potZ c₂.nmem (Tb + m) m with hnm0
    have n0 : ∀ a, (a < Tb + m ∨ Tb + m + (m + 1) ≤ a) → nm0 a = c₂.nmem a := fun a ha => by
      rw [hnm0]; unfold potZ; split_ifs with h
      · omega
      · rfl
    have hidm : ∀ v < w, nm0 (IDb + v) < m := fun v hv => by
      rw [n0 _ (Or.inr (by omega))]; exact hid v hv
    set nm := potM nm0 IDb VLb (Tb + m) w with hnm
    have rd : ∀ a, a < Tb + m → nm a = c₂.nmem a := fun a ha => by
      rw [hnm, potM_out _ (G := m) hidm (Or.inl ha), n0 a (Or.inl ha)]
    have rd2 : ∀ a, Wz < a → a < Tb → nm a = c.nmem a := fun a h1 h2 => by
      rw [rd a (by omega), m2 a h1 h2]
    -- the potential cells
    have hcons : ∀ v' < w, ∀ v'' < w, nm0 (IDb + v') = nm0 (IDb + v'') →
        nm0 (VLb + v') = nm0 (VLb + v'') := fun v' h1 v'' h2 e => by
      rw [n0 _ (Or.inr (by omega)), n0 _ (Or.inr (by omega)), (hv' v' h1).2.1,
        (hv' v'' h2).2.1] at e
      have := G.gv_inj e
      rw [n0 _ (Or.inr (by omega)), n0 _ (Or.inr (by omega)),
        show VLb + v' = Ob + (4 + 5 * k' + m') + 2 + 2 * m' + v' by omega,
        show VLb + v'' = Ob + (4 + 5 * k' + m') + 2 + 2 * m' + v'' by omega,
        (hv' v' h1).2.2.1, (hv' v'' h2).2.2.1, this]
    have hPOT : ∀ j < m, (pmap hP).face (E j) ∈ verts (pmap hP).dual Pr →
        (nm (Tb + m + (olab (nxF d m c.nmem) j + 1)) : ℤ) =
          χ ((pmap hP).face (E j)) + rtL (pmap hP) (fun y => u y.1 - g y) := fun j hj hmem => by
      obtain ⟨v, hv, hιv⟩ := hcov _ hmem
      have e1 : olab (nxF d m c.nmem) j = G.gv (ι v) := by
        have e0 : olab (nxF d m c.nmem) j = G.gv ((pmap hP).face (E j)) := lab_gv hP hl hm hft hj
        rw [e0, hιv]
      have e2 : nm0 (IDb + v) = G.gv (ι v) := by
        rw [n0 _ (Or.inr (by omega))]; exact (hv' v hv).2.1
      rw [show Tb + m + (olab (nxF d m c.nmem) j + 1) = Tb + m + nm0 (IDb + v) + 1 by
        rw [e1, e2]; omega, hnm, potM_val nm0 hcons hv, n0 _ (Or.inr (by omega)),
        show VLb + v = Ob + (4 + 5 * k' + m') + 2 + 2 * m' + v by omega, (hv' v hv).2.2.1,
        ← hιv, Int.toNat_of_nonneg (by have := (abs_le.1 (hv' v hv).2.2.2).1; omega)]
    -- the reads of `flV`
    have hr := (hl.rv i hi)
    set r := c.nmem (d + 4 + m + i) with hr'
    have eR : E r = (pmap hP).rev (E i) := Subtype.ext (by
      rw [layEn_val hr.1, hr.2, pmap_rev, layEn_val hi])
    have rCP : nm (d + 4 + 3 * m + i) = c.nmem (d + 4 + 3 * m + i) := rd2 _ (by omega) (by omega)
    have rRV : nm (d + 4 + m + i) = r := rd2 _ (by omega) (by omega)
    have rLr : nm (LABb + r) = olab (nxF d m c.nmem) r + 1 := by
      rw [rd2 _ (by omega) (by omega), hLAB r hr.1]
    have rLi : nm (LABb + i) = olab (nxF d m c.nmem) i + 1 := by
      rw [rd2 _ (by omega) (by omega), hLAB i hi]
    have rLN : nm (Tb + i) = (u (en i) - g (E i) + K).toNat := by
      rw [rd _ (by omega), aLN i hi]
    unfold flV
    rw [rCP, rRV, rLr, rLi, rLN]
    show _ = (Z : ℤ) + (g (E i) + (χ ((pmap hP).face ((pmap hP).rev (E i))) -
      χ ((pmap hP).face (E i))))
    have hCP' : (c.nmem (d + 4 + 3 * m + i) : ℤ) = u (en i) := (hl.cp i hi).1
    have hu : u (en i) = u (E i).1 := by rw [layEn_val hi]
    refine fl_dart (L := rtL (pmap hP) (fun y => u y.1 - g y)) hCP' rfl (hgK i hi) (hℓK i hi) ?_
      (by have := hfin i hi; exact this)
    by_cases hlp : (pmap hP).face (E i) = (pmap hP).face ((pmap hP).rev (E i))
    · left
      have : olab (nxF d m c.nmem) r = olab (nxF d m c.nmem) i := by
        have e1 : olab (nxF d m c.nmem) r = G.gv ((pmap hP).face (E r)) := lab_gv hP hl hm hft hr.1
        have e2 : olab (nxF d m c.nmem) i = G.gv ((pmap hP).face (E i)) := lab_gv hP hl hm hft hi
        rw [e1, e2, eR, ← hlp]
      exact ⟨by rw [this], by rw [← hlp]⟩
    · right
      obtain ⟨v1, v2⟩ := face_mem_verts (pmap hP) G.gd (y := E i) hlp
      refine ⟨?_, hPOT i hi v1⟩
      have := hPOT r hr.1 (by rw [eR]; exact v2)
      rw [eR] at this
      exact this
  · rw [cK a (Or.inl (by omega)) (Or.inl (by omega)), az a ha]
  · rw [cK a (Or.inl (by omega)) (by omega), m2 a h1 h2]
  · unfold KeepR at hr
    rw [cn r (by omega) (by omega), k2 r (by unfold KeepR; omega) h2]

end Call

end BKMNW

end PlanarFlow
