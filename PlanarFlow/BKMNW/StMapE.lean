module

public import PlanarFlow.BKMNW.StMapD

/-!
# The map part of the s-t flow encoding: the whole program on index arrays

**`smP_exec`**: from index arrays `RV` (values `< m`) and `RT` with `RT` and `NX = RT ∘ RV`
permutations of `[0, m)`, `smP` writes within `140 m + 150` steps at `β` the arrays `RV`,
`NF = olab RT + 1 + 2m`, `NE = 3m + 1 + min i RV[i]`, `NG = m + 1 + min i RV[i]`,
`NT = olab NX + 1`, `NH[i] = NT[RV[i]]`, `IS = LN = 0`, and `ED` (one of the two darts of each
edge at its node `3m + 1 + min i RV[i]`); the scratch `[S, S + 3m)` is zero at the end, all
memory outside the scratch and `[β, β + 12 m + 1)` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset Function CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  OrbLab NsStep

variable {P : Input} {W : ℕ}

/-- **The map part of the encoding on index arrays** (see the module docstring). -/
theorem smP_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb S β : ℕ}
    (r00 : c.nreg 7700 = m) (r01 : c.nreg 7701 = RVb) (r02 : c.nreg 7702 = RTb)
    (r03 : c.nreg 7703 = S) (r04 : c.nreg 7704 = β)
    (hRV : ∀ i < m, c.nmem (RVb + i) < m)
    (hNX : PermOn (fun i => c.nmem (RTb + c.nmem (RVb + i))) m)
    (hRT : PermOn (fun i => c.nmem (RTb + i)) m)
    (l1 : RVb + m ≤ S) (l2 : RTb + m ≤ S) (l3 : S + 3 * m ≤ β) (w : β + 12 * m + 1 ≤ W) :
    ∃ c' t, Exec P W smP c c' t ∧ t ≤ 140 * m + 150 ∧
      (∀ i < m, c'.nmem (β + i) = c.nmem (RVb + i)) ∧
      (∀ i < m, c'.nmem (β + m + i) = olab (fun i => c.nmem (RTb + i)) i + 1 + 2 * m) ∧
      (∀ i < m, c'.nmem (β + 2 * m + i) = 3 * m + 1 + min i (c.nmem (RVb + i))) ∧
      (∀ i < m, c'.nmem (β + 3 * m + i) = m + 1 + min i (c.nmem (RVb + i))) ∧
      (∀ i < m, c'.nmem (β + 4 * m + i) =
        olab (fun i => c.nmem (RTb + c.nmem (RVb + i))) i + 1) ∧
      (∀ i < m, c'.nmem (β + 5 * m + i) =
        olab (fun i => c.nmem (RTb + c.nmem (RVb + i))) (c.nmem (RVb + i)) + 1) ∧
      (∀ i < 2 * m, c'.nmem (β + 6 * m + i) = 0) ∧
      (∀ x < m, ∃ x' < m, min x' (c.nmem (RVb + x')) = min x (c.nmem (RVb + x)) ∧
        c'.nmem (β + 8 * m + (3 * m + 1 + min x (c.nmem (RVb + x)))) = x') ∧
      (∀ i < 3 * m, c'.nmem (S + i) = 0) ∧
      (∀ a, ¬ (S ≤ a ∧ a < S + 3 * m) → ¬ (β ≤ a ∧ a < β + 12 * m + 1) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ SmScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set RV : ℕ → ℕ := fun i => c.nmem (RVb + i) with hRVd
  set NX : ℕ → ℕ := fun i => c.nmem (RTb + c.nmem (RVb + i)) with hNXd
  set RT : ℕ → ℕ := fun i => c.nmem (RTb + i) with hRTd
  have hRT' : ∀ i < m, c.nmem (RTb + i) < m := fun i hi => hRT.lt i hi
  unfold smP
  -- stage A
  obtain ⟨c₁, t₁, e₁, ht₁, L₁, A1, A2, A3, An, Arr, Arm, Ao⟩ :=
    smA_exec (P := P) c hc r00 r01 r02 r03 r04 hRV hRT' l1 l2 l3 w
  -- stage B
  obtain ⟨c₂, t₂, e₂, ht₂, B1, B2, B3, Bn, L₂, Brr, Brm, Bo⟩ := smB_exec (P := P) c₁ e₁.wb_right
    L₁ hNX hRT (fun i hi => A2 i hi)
    (fun i hi => A3 _ (by clear * - l2 hi; omega) (by clear * - l2 l3 hi; omega)) l2
    (by clear * - l3 w; omega) (by clear * - l3 w; omega)
  -- stage C
  obtain ⟨c₃, t₃, e₃, ht₃, C1, C2, C3, Cn, L₃, Crr, Crm, Co⟩ := smC_exec (P := P) c₂ e₂.wb_right
    L₂ l3 w (fun i hi => by
      rw [B2 i hi]; have := olab_lt hRT hi; clear * - this l3 w; omega)
  -- the memory of `RV` after stage C
  have mRV : ∀ i < m, c₃.nmem (β + i) = RV i := fun i hi => by
    rw [C3 _ (by clear * - hi; omega) (by clear * - hi; omega),
      B3 _ (Or.inr (by clear * - l3; omega)), A1 i hi]
  -- stage D
  obtain ⟨c₄, t₄, e₄, ht₄, D1, D2, D3, Dn, L₄, Drr, Drm, Do⟩ := smED_exec (P := P) c₃
    e₃.wb_right L₃ (fun x hx => by rw [mRV x hx]; exact hRV x hx) w
  -- stage E
  obtain ⟨c₅, t₅, e₅, ht₅, E1, E2, E3, E4, E5, En, -, Err, Erm, Eo⟩ := smE_exec (P := P) c₄
    e₄.wb_right L₄ l3 w
  have mNT : ∀ i < m, c₃.nmem (β + 4 * m + i) = olab NX i + 1 := fun i hi => by
    rw [C1 i hi, B1 i hi]
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
    by clear * - ht₁ ht₂ ht₃ ht₄ ht₅; omega, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, E3, fun x hx => ?_, E4,
    fun a ha hb => ?_, fun r hr => ?_, by rw [Err, Drr, Crr, Brr, Arr],
    by rw [Erm, Drm, Crm, Brm, Arm], by rw [Eo, Do, Co, Bo, Ao]⟩
  · -- RV
    rw [E5 _ (by clear * - l3; omega) (by clear * - hi; omega) (by clear * - hi; omega),
      D3 _ (Or.inl (by clear * - hi; omega)), mRV i hi]
  · -- NF
    rw [E5 _ (by clear * - l3; omega) (by clear * - hi; omega) (by clear * - hi; omega),
      D3 _ (Or.inl (by clear * - hi; omega)), C2 i hi, B2 i hi]
  · -- NE
    rw [E2 i hi, (D1 i hi).2.2, mRV i hi]
  · -- NG
    rw [E1 i hi, (D1 i hi).2.1, mRV i hi]
  · -- NT
    rw [E5 _ (by clear * - l3; omega) (by clear * - hi; omega) (by clear * - hi; omega),
      D3 _ (Or.inl (by clear * - hi; omega)), mNT i hi]
  · -- NH
    rw [E5 _ (by clear * - l3; omega) (by clear * - hi; omega) (by clear * - hi; omega),
      (D1 i hi).1, mRV i hi, mNT _ (hRV i hi)]
  · -- ED
    obtain ⟨x', hx', h1, h2⟩ := D2 x hx
    rw [mRV x hx, mRV x' hx'] at h1
    rw [mRV x hx] at h2
    refine ⟨x', hx', h1, ?_⟩
    rw [E5 _ (by clear * - l3; omega) (by clear * - hx; omega)
      (by clear * - hx; omega)]
    exact h2
  · -- the rest of the memory
    rw [E5 a ha (by clear * - hb; omega) (by clear * - hb; omega),
      D3 a (by clear * - hb; omega), C3 a (by clear * - hb; omega) (by clear * - hb; omega),
      B3 a (by clear * - ha; omega), A3 a (by clear * - ha; omega) (by clear * - hb; omega)]
  · rw [En r hr, Dn r hr, Cn r hr, Bn r hr, An r hr]

end StEnc

end BKMNW

end PlanarFlow
