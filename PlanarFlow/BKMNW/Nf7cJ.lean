module

public import PlanarFlow.BKMNW.Nf7cI

/-!
# The final step of `fixP`: the lengths and the negative-length call

**`finAB_exec`**: `finA ; finB` at a max-flow call: from the frame (`Lay`), the words of the path
(`PD`, `CW`, `CR`, `FW = g (d l) + K`) and the flow array (`Z + g` off the path), the lengths
`LN[i] = ℓ (en i) + K` of `ℓ = U − g` (`ln_all`), then the negative-length call
(`negStep_lay_exec'`): its outcome `negLay gid I x hP ℓ` in the copy at `Ob' = r9481`, the root
frame's input part at `A' = r9480`.
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

/-- **All the words of `LN`**: the three cases of a frame index. -/
theorem ln_all {nm nm' : ℕ → ℕ} {m k Tb PDb RVb CPb FLb CWb CRb FWb Z K : ℕ}
    {Ui gi : ℕ → ℤ}
    (hPD : ∀ l < k, nm (PDb + l) < m)
    (hdist : ∀ l < k, ∀ l' < k, nm (PDb + l) ≠ nm (RVb + nm (PDb + l')) ∧
      (nm (PDb + l) = nm (PDb + l') → l = l') ∧
      (nm (RVb + nm (PDb + l)) = nm (RVb + nm (PDb + l')) → l = l'))
    (a1 : ∀ l < k, nm' (Tb + nm (PDb + l)) = nm (CWb + l) + K + K - nm (FWb + l))
    (a2 : ∀ l < k, nm' (Tb + nm (RVb + nm (PDb + l))) = nm (CRb + l) + nm (FWb + l))
    (a3 : ∀ i < m, (∀ l < k, nm (PDb + l) ≠ i ∧ nm (RVb + nm (PDb + l)) ≠ i) →
      nm' (Tb + i) = nm (CPb + i) + Z + K - nm (FLb + i))
    (hCP : ∀ i < m, (nm (CPb + i) : ℤ) = Ui i)
    (hFLo : ∀ i < m, (∀ l < k, nm (PDb + l) ≠ i ∧ nm (RVb + nm (PDb + l)) ≠ i) →
      (nm (FLb + i) : ℤ) = Z + gi i)
    (hCW : ∀ l < k, (nm (CWb + l) : ℤ) = Ui (nm (PDb + l)))
    (hCR : ∀ l < k, (nm (CRb + l) : ℤ) = Ui (nm (RVb + nm (PDb + l))))
    (hFW : ∀ l < k, (nm (FWb + l) : ℤ) = gi (nm (PDb + l)) + K)
    (hgr : ∀ l < k, gi (nm (RVb + nm (PDb + l))) = - gi (nm (PDb + l)))
    (hgK : ∀ i < m, |gi i| ≤ K) (hℓK : ∀ i < m, |Ui i - gi i| ≤ K) :
    ∀ i < m, nm' (Tb + i) = (Ui i - gi i + K).toNat := by
  intro i hi
  have key : ((nm' (Tb + i) : ℕ) : ℤ) = Ui i - gi i + K := by
    by_cases h1 : ∃ l < k, nm (PDb + l) = i
    · obtain ⟨l, hl, rfl⟩ := h1
      rw [a1 l hl]
      exact (ln_word (CP := 0) (FLW := 0) (CR := 0) (Z := Z) (f₀ := 0) (Ur := 0) (gd := 0)
        (hℓK _ hi)).2.1 (hCW l hl) (hFW l hl) (hgK _ hi)
    by_cases h2 : ∃ l < k, nm (RVb + nm (PDb + l)) = i
    · obtain ⟨l, hl, rfl⟩ := h2
      rw [a2 l hl]
      exact (ln_word (CP := 0) (FLW := 0) (CW := 0) (Z := Z) (f₀ := 0)
        (U := gi (nm (RVb + nm (PDb + l)))) (g := gi (nm (RVb + nm (PDb + l)))) (K := K)
        (by simp)).2.2 (hCR l hl) (hFW l hl) (hgr l hl) (hℓK _ hi)
    have hn : ∀ l < k, nm (PDb + l) ≠ i ∧ nm (RVb + nm (PDb + l)) ≠ i := fun l hl =>
      ⟨fun e => h1 ⟨l, hl, e⟩, fun e => h2 ⟨l, hl, e⟩⟩
    rw [a3 i hi hn]
    exact (ln_word (CW := 0) (CR := 0) (FW := 0) (Ur := 0) (gd := 0) (hℓK i hi)).1 (hCP i hi)
      (hFLo i hi hn) rfl
  have h0 : 0 ≤ Ui i - gi i + K := by have := (abs_le.1 (hℓK i hi)).1; omega
  rw [← key, Int.toNat_natCast]

section Call

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ}

/-- The root frame of a negative call of a piece map with `m` darts fits in `6 + 10 m` cells. -/
lemma fsz_le (hP : PieceInv M x.1.piece x.2.1 x.2.2) {mem : ℕ → ℕ}
    (hl : Lay M gid u S T Z x m en d mem) (μ : SDart (pdarts M x.1.piece x.2.1) → ℕ) :
    Frame.fsz (repsN (pmap hP).dual μ).card (ck (pmap hP).dual (repsN (pmap hP).dual μ)) ≤
      6 + 10 * m ∧
    Frame.fin (repsN (pmap hP).dual μ).card (ck (pmap hP).dual (repsN (pmap hP).dual μ)) ≤
      4 + 6 * m ∧ (repsN (pmap hP).dual μ).card ≤ m := by
  have h1 := card_le_n (repsN (pmap hP).dual μ)
  have h2 := ck_le_n (pmap hP).dual (repsN (pmap hP).dual μ)
  rw [hl.card_sdart] at h1 h2
  unfold Frame.fsz Frame.fin
  omega

set_option maxHeartbeats 2000000 in
/-- **Phases A and B of the final step at a max-flow call.** -/
theorem finAB_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
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
    (hW : Tb + 22 * m + 13 + (d + 4 + 3 * m) + (d + 4 + 6 * m) + PDb + (d + 4 + m) + CWb + CRb +
      FWb + k + negT C C₀ m ≤ W)
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
    finA_exec (P := P') c hc (T := Tb) (CWb := CWb) (CRb := CRb) (FWb := FWb) r69 r00 r36 r34 r35
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

end Call

end BKMNW

end PlanarFlow
