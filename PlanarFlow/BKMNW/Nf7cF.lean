module

public import PlanarFlow.BKMNW.Nf7cE
public import PlanarFlow.BKMNW.NsCall

/-!
# The negSSSP step with the root frame kept

To read the outcome `Res` of the negative-length call in the copy at `Ob`, the machine needs the
sizes `m' = #reps`, `k' = ck` of the root frame (the outcome region is at
`Ob + fin m' k' = Ob + 4 + 5 k' + m'`). The root frame's input part `InP` at `A` holds them
(`A + 1`, `A + 2`), and `negCallH` keeps the memory at `A` (it writes only the copy and the
log). Here:

* **`negStep_exec'`**: `negStep_exec` with, in addition, the input part `InP` of the root frame
  at `A` in the final configuration;
* **`negStep_lay_exec'`**: the same at a max-flow call (`negStep_lay_exec` with `InP` for the
  frame's identifiers `layIds`).
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

universe w

section Gen

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

variable {P : Input} {W : ℕ}

open MfDrv in
/-- **`negStep_exec` with the root frame kept** (`InP` at `A` after the run). -/
theorem negStep_exec' (C C₀ : ℕ) (hC : 200000 ≤ C) (h : EnumOK M en m) (d₀ : D) (ℓ : D → ℤ)
    (hpre : NegPre M ℓ) (I P' : Input) (c : Config) (hc : WordsBounded W c)
    {RVb RTb LNb K S A Wz Ob p : ℕ} (r00 : c.nreg 7500 = m) (r01 : c.nreg 7501 = RVb)
    (r02 : c.nreg 7502 = RTb) (r03 : c.nreg 7503 = LNb) (r04 : c.nreg 7504 = K)
    (r05 : c.nreg 7505 = S) (r06 : c.nreg 7506 = A) (r22 : c.nreg 7322 = Ob)
    (r24 : c.nreg 7324 = p)
    (hRV : ∀ i < m, c.nmem (RVb + i) = rvI M en m i)
    (hRT : ∀ i < m, c.nmem (RTb + i) = ixOf en m (M.rot (en i)))
    (hLN : ∀ i < m, c.nmem (LNb + i) = (ℓ (en i) + K).toNat) (hK : ∀ i < m, |ℓ (en i)| ≤ K)
    (hzW : ∀ a ≤ Wz, c.nmem a = 0) (hS : S + 9 * m + 1 + tsz m ≤ Wz + 1)
    (sR : Wz < RVb) (sT : Wz < RTb) (sN : Wz < LNb) (hA : Wz < A)
    (dR : RVb + m ≤ A ∨ A + 6 + 10 * m ≤ RVb) (wR : RVb + m ≤ W) (wT : RTb + m ≤ W)
    (wN : LNb + m ≤ W) (wA : A + 6 + 10 * m ≤ W) (wL : 2 * K + rtL M ℓ ≤ W)
    (hWz : rtW m (rtL M ℓ) m ≤ Wz)
    (hAO : A + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
      (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ Ob)
    (hOp : Ob + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
      (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ p)
    (hpW : p + negT C C₀ m ≤ W) (hw2 : spWs m + 205 ≤ W) (hw3 : fxWB m (rtL M ℓ) ≤ W) :
    ∃ d' t, Exec P' W negStep c d' t ∧
      t ≤ 300 * m + 200 + (9 * negT C C₀ m +
        12 * Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) +
        7 * Frame.fin (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) + 3291 + (12 * m + 4628)) ∧
      (∀ a ≤ Wz, d'.nmem a = 0) ∧
      Res (nsIds M h d₀) M.dual (rtL M ℓ) (repsN M.dual (nsIds M h d₀).gd)
        (negMach (nsIds M h d₀) M I ℓ) Ob
        (Ob + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd))) d' ∧
      InP (nsIds M h d₀) M.dual (minLen M.dual ℓ) (rtL M ℓ) (Fintype.card D)
        (repsN M.dual (nsIds M h d₀).gd) A
        (A + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd))) d' ∧
      (∀ a, Wz < a →
        (a < A ∨ A + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ a) →
        (a < Ob ∨ Ob + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
          (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ a) →
        (a < p ∨ p + negT C C₀ m ≤ a) → d'.nmem a = c.nmem a) ∧
      (∀ r, 3000 ≤ r → r ≤ 3012 → d'.nreg r = c.nreg r) ∧
      (∀ r, ¬ ncScr r → ¬ NsScr r → d'.nreg r = c.nreg r) ∧
      d'.rreg = c.rreg ∧ d'.rmem = c.rmem ∧ d'.output = c.output := by
  have hcard := card_eq_m h
  have hfsz : Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
      (ck M.dual (repsN M.dual (nsIds M h d₀).gd)) ≤ 6 + 10 * m := by
    have h1 := card_le_n (repsN M.dual (nsIds M h d₀).gd)
    have h2 := ck_le_n M.dual (repsN M.dual (nsIds M h d₀).gd)
    unfold Frame.fsz; rw [hcard] at h1 h2; clear * - h1 h2; omega
  obtain ⟨c₁, t₁, e₁, ht₁, I₁, Z₁, F₁, r25, r26, R₁, rr₁, rm₁, o₁⟩ :=
    nsPrep_exec h d₀ ℓ c hc r00 r01 r02 r03 r04 r05 r06 hRV hRT hLN hK
      (fun a h1 h2 => hzW a (by clear * - h2 hS; omega)) (by clear * - hS sR; omega)
      (by clear * - hS sT; omega) (by clear * - hS sN; omega) (by clear * - hS hA; omega)
      dR wR wT wN wA wL (P := P')
  have hz₁ : ∀ a ≤ Wz, c₁.nmem a = 0 := fun a ha => by
    by_cases h1 : S ≤ a ∧ a < S + 9 * m + 1 + tsz m
    · exact Z₁ a h1.1 h1.2
    · rw [F₁ a (by clear * - h1; omega) (Or.inl (by clear * - ha hA; omega)), hzW a ha]
  have q : ∀ r, ¬ NsScr r → c₁.nreg r = c.nreg r := R₁
  have hWz' : rtW (Fintype.card D) (rtL M ℓ) (nsIds M h d₀).G ≤ Wz := by
    rw [nsIds_G, hcard]; exact hWz
  have hpW' : p + negT C C₀ (Fintype.card D) ≤ W := by rw [hcard]; exact hpW
  have hw2' : spWs (Fintype.card D) + 205 ≤ W := by rw [hcard]; exact hw2
  have hw3' : fxWB (Fintype.card D) (rtL M ℓ) ≤ W := by rw [hcard]; exact hw3
  obtain ⟨d', t, ex, ht, hz', hres, hF, hk1, hk2, hr', hrm', ho'⟩ :=
    negCallH_exec C C₀ hC (nsIds M h d₀) hpre I P' c₁ e₁.wb_right
      (by rw [q _ (by clear * -; unfold NsScr; omega), r22])
      (by rw [q _ (by clear * -; unfold NsScr; omega), r24]) r25
      (by rw [r26, nsIds_G]) hz₁ I₁ hWz' hA hAO hOp hpW' hw2' hw3'
  have hin : InP (nsIds M h d₀) M.dual (minLen M.dual ℓ) (rtL M ℓ) (Fintype.card D)
      (repsN M.dual (nsIds M h d₀).gd) A
      (A + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
        (ck M.dual (repsN M.dual (nsIds M h d₀).gd))) d' :=
    inP_stab I₁ fun a h1 h2 => ⟨hF a (by clear * - h1 hA; omega)
      (Or.inl (by clear * - h2 hAO; omega)) (Or.inl (by clear * - h2 hAO hOp; omega)),
      by rw [hrm']⟩
  rw [hcard] at ht hF
  refine ⟨d', t₁ + t, .seq e₁ ex, by clear * - ht₁ ht; omega, hz', hres, hin,
    fun a h1 h2 h3 h4 => ?_, fun r h1 h2 => ?_, fun r h1 h2 => ?_, by rw [hr', rr₁],
    by rw [hrm', rm₁], by rw [ho', o₁]⟩
  · rw [hF a h1 h3 h4, F₁ a (Or.inr (by clear * - h1 hS; omega)) h2]
  · rw [hk1 r h1 h2, q r (by clear * - h1 h2; unfold NsScr; omega)]
  · rw [hk2 r h1, q r h2]

end Gen

section Lay

open MfDrv

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ} {W : ℕ}

open MfDrv in
/-- **`negStep_lay_exec` with the root frame kept** (`InP` at `A` for the frame's identifiers). -/
theorem negStep_lay_exec' (C C₀ : ℕ) (hC : 200000 ≤ C) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
    (ℓ : SDart (pdarts M x.1.piece x.2.1) → ℤ) (hpre : NegPre (pmap hP) ℓ) (I P' : Input)
    (c : Config) (hc : WordsBounded W c) (hl : Lay M gid u S T Z x m en d c.nmem) (hm : 0 < m)
    {LNb K S' A Wz Ob p : ℕ} (r00 : c.nreg 7500 = m) (r01 : c.nreg 7501 = d + 4 + m)
    (r02 : c.nreg 7502 = d + 4 + 2 * m) (r03 : c.nreg 7503 = LNb) (r04 : c.nreg 7504 = K)
    (r05 : c.nreg 7505 = S') (r06 : c.nreg 7506 = A) (r22 : c.nreg 7322 = Ob)
    (r24 : c.nreg 7324 = p)
    (hLN : ∀ i < m, c.nmem (LNb + i) =
      (ℓ (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i) + K).toNat)
    (hK : ∀ i < m, |ℓ (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i)| ≤ K)
    (hzW : ∀ a ≤ Wz, c.nmem a = 0) (hS : S' + 9 * m + 1 + tsz m ≤ Wz + 1)
    (sR : Wz < d) (sN : Wz < LNb) (hA : Wz < A)
    (dR : d + 4 + m + m ≤ A ∨ A + 6 + 10 * m ≤ d + 4 + m) (wR : d + 4 + 3 * m ≤ W)
    (wN : LNb + m ≤ W) (wA : A + 6 + 10 * m ≤ W)
    (wL : 2 * K + rtL (pmap hP) ℓ ≤ W) (hWz : rtW m (rtL (pmap hP) ℓ) m ≤ Wz)
    (hAO : A + Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
      (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) ≤ Ob)
    (hOp : Ob + Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
      (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) ≤ p)
    (hpW : p + negT C C₀ m ≤ W) (hw2 : spWs m + 205 ≤ W) (hw3 : fxWB m (rtL (pmap hP) ℓ) ≤ W) :
    ∃ d' t, Exec P' W negStep c d' t ∧
      t ≤ 300 * m + 200 + (9 * negT C C₀ m +
        12 * Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) +
        7 * Frame.fin (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) + 3291 +
        (12 * m + 4628)) ∧
      (∀ a ≤ Wz, d'.nmem a = 0) ∧
      Res (layIds hP hl hm hpre.2.2.1) (pmap hP).dual (rtL (pmap hP) ℓ)
        (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)
        (negLay gid I x hP ℓ) Ob
        (Ob + Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd))) d' ∧
      InP (layIds hP hl hm hpre.2.2.1) (pmap hP).dual (minLen (pmap hP).dual ℓ)
        (rtL (pmap hP) ℓ) (Fintype.card (SDart (pdarts M x.1.piece x.2.1)))
        (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd) A
        (A + Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd))) d' ∧
      (∀ a, Wz < a →
        (a < A ∨ A + Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) ≤ a) →
        (a < Ob ∨ Ob + Frame.fsz (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd).card
          (ck (pmap hP).dual (repsN (pmap hP).dual (layIds hP hl hm hpre.2.2.1).gd)) ≤ a) →
        (a < p ∨ p + negT C C₀ m ≤ a) → d'.nmem a = c.nmem a) ∧
      (∀ r, 3000 ≤ r → r ≤ 3012 → d'.nreg r = c.nreg r) ∧
      (∀ r, ¬ ncScr r → ¬ NsScr r → d'.nreg r = c.nreg r) ∧
      d'.rreg = c.rreg ∧ d'.rmem = c.rmem ∧ d'.output = c.output := by
  rw [negLay_lay I hP hl hm hpre.2.2.1]
  exact negStep_exec' C C₀ hC (lay_enumOK hP hl hm hpre.2.2.1) _ ℓ hpre I P' c hc r00 r01 r02 r03
    r04 r05 r06 r22 r24 (fun i hi => lay_rv hP hl hm hpre.2.2.1 hi)
    (fun i hi => lay_rt hP hl hm hpre.2.2.1 hi) hLN hK hzW hS (by omega) (by omega) sN hA dR
    (by omega) (by omega) wN wA wL hWz hAO hOp hpW hw2 hw3

end Lay

end NsStep

end BKMNW

end PlanarFlow
