module

public import PlanarFlow.BKMNW.Nf9bF
public import PlanarFlow.BKMNW.Nf9bL

/-!
# The bounds of the frozen fix from the envelopes

From the hypotheses of `FixFrameSpec` (`PCtx`, the room `A0 + rOF9 C C₀ Rm m' Z' ≤ W`, the
zero area `wzF9 wzm m' Z' ≤ Wz`), all the word and zero-area hypotheses of `fxPos_exec`
(**`pos_bnds`**) and of `fxZero_exec` (**`zero_bnds`**):

* the values: `pq_AS_le` (`AS ≤ m' Z'`), `pq_FLW_le` (`Σ FLW ≤ m' · 2Z'`), `pq_k_le` (`k ≤ m`),
  `pq_K_le` (`K ≤ KM9 m' Z'`), `capf_le` (`|cap − f₀| ≤ K`), `lenK_of_good` (the lengths of the
  final call are bounded by `K`), hence `rtL ≤ m · K`.
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

section Vals

variable (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem)
include H

lemma pq_AS_le : (cIn d' m' Gb segs j Z' mem).AS ≤ m' * Z' := by
  unfold FpIn.AS
  calc ∑ i ∈ range (cIn d' m' Gb segs j Z' mem).m, (cIn d' m' Gb segs j Z' mem).CP i
      ≤ ∑ _i ∈ range m', Z' := sum_le_sum fun i hi => by
        have := (H.fr.cp i (mem_range.1 hi)).2
        show mem (d' + 4 + m' + m' + m' + i) ≤ Z'
        rw [show d' + 4 + m' + m' + m' + i = d' + 4 + 3 * m' + i by omega]; exact this
    _ = m' * Z' := by simp

lemma pq_FLW_le : ∑ i ∈ range m', (cIn d' m' Gb segs j Z' mem).FLW i ≤ m' * (2 * Z') := by
  calc ∑ i ∈ range m', (cIn d' m' Gb segs j Z' mem).FLW i ≤ ∑ _i ∈ range m', 2 * Z' :=
        sum_le_sum fun i hi => by
          have hi' := mem_range.1 hi
          have h1 := H.fr.fl i hi'
          have h2 := H.fr.cp i hi'
          have h3 := H.pseudo.le_cap (en' i)
          show mem (d' + 4 + m' + m' + m' + m' + m' + m' + i) ≤ 2 * Z'
          rw [show d' + 4 + m' + m' + m' + m' + m' + m' + i = d' + 4 + 6 * m' + i by omega]
          have : (mem (d' + 4 + 3 * m' + i) : ℤ) ≤ Z' := by exact_mod_cast h2.2
          have : (mem (d' + 4 + 6 * m' + i) : ℤ) ≤ 2 * Z' := by linarith [h2.1]
          exact_mod_cast this
    _ = m' * (2 * Z') := by simp

lemma pq_k_le : (cIn d' m' Gb segs j Z' mem).k ≤ m := by
  rw [pq_k H]
  have h := k_le_card9 (segs[j]'H.hj)
  rw [card_eq_m H.enum] at h
  exact h

lemma pq_K_le (hk : (cIn d' m' Gb segs j Z' mem).k ≤ m') :
    (cIn d' m' Gb segs j Z' mem).K ≤ KM9 m' Z' := by
  have h : fpB (cIn d' m' Gb segs j Z' mem).AS (cIn d' m' Gb segs j Z' mem).m
      (cIn d' m' Gb segs j Z' mem).k ≤ fpB (m' * Z') m' m' := fpB_mono9 (pq_AS_le H) le_rfl hk
  show 16 * _ ≤ 16 * _
  exact Nat.mul_le_mul_left 16 h

lemma pq_L_le (hk : (cIn d' m' Gb segs j Z' mem).k ≤ m') :
    8 * fpB (cIn d' m' Gb segs j Z' mem).AS m' (cIn d' m' Gb segs j Z' mem).k ≤ LM9 m' Z' := by
  show 8 * fpB _ _ _ ≤ 8 * fpB _ _ _
  have := fpB_mono9 (pq_AS_le H) (le_refl m') hk
  omega

/-- **The capacities and the flow are bounded by `K`** (`16 fpB AS m' k ≥ 16 (12 AS + 4)`). -/
lemma capf_le (y : D ⊕ (V × Bool)) :
    |f₀ y| ≤ ((cIn d' m' Gb segs j Z' mem).K : ℤ) ∧
      |cap y - f₀ y| ≤ ((cIn d' m' Gb segs j Z' mem).K : ℤ) := by
  set q := cIn d' m' Gb segs j Z' mem
  have hAS : ((q.AS : ℕ) : ℤ) = SPath.absSum cap := cIn_as H.fr
  have hKe : (16 * (12 * q.AS + 4) : ℤ) ≤ q.K := by
    have e : q.K = 16 * fpB q.AS q.m q.k := rfl
    have h0 : 12 * q.AS + 4 ≤ fpB q.AS q.m q.k := by unfold fpB; omega
    rw [e]; push_cast; exact_mod_cast Nat.mul_le_mul_left 16 h0
  have h1 := abs_le_of_pseudo H.pseudo y
  have h2 := abs_le_absSum cap y
  have h3 := abs_le_absSum cap ((M₀.pendant e he).rev y)
  rw [← hAS] at h2 h3
  have h4 : |cap y - f₀ y| ≤ |cap y| + |f₀ y| := abs_sub _ _
  have hA0 : (0 : ℤ) ≤ q.AS := by positivity
  push_cast at hKe
  constructor <;> linarith [abs_nonneg (f₀ y)]

end Vals

/-- **The lengths of the final call are bounded by `K`**, for the data of the stage loop. -/
lemma lenK_of_good {q : FpIn} {Q W : ℕ} {π : SPath M₀}
    (hG : (mkP M₀ e he en' π cap f₀ q Q).Good W) (y : D ⊕ (V × Bool)) :
    |(cap - ((mkP M₀ e he en' π cap f₀ q Q).st (π.lift e he).k).1) y| ≤
      ((mkP M₀ e he en' π cap f₀ q Q).K : ℤ) := by
  set X := mkP M₀ e he en' π cap f₀ q Q with hX
  have hinv : EffInvB (M₀.pendant e he) X.c X.f₀ X.P X.P.k (X.st X.P.k) :=
    fixPath_invB hG.plane hG.c_nn hG.pseudo hG.mssp_spec hG.fr_spec X.P.k le_rfl
  have h1 := hinv.len_bound hG.c_nn hG.pseudo y
  have h2 : ((16 * X.B : ℕ) : ℤ) ≤ X.K := by exact_mod_cast hG.hK
  push_cast at h2
  have hbst := hG.bst
  have hbc := hG.bc
  have hA := absSum_nonneg X.c
  have hkB : (0 : ℤ) ≤ (X.P.k : ℤ) * Bst (D ⊕ (V × Bool)) X.c := by
    have := Bst_nonneg (D := D ⊕ (V × Bool)) X.c; positivity
  have : |(X.c - (X.st X.P.k).1) y| ≤ X.K := by linarith
  exact this

end F9b

end BKMNW

end PlanarFlow
