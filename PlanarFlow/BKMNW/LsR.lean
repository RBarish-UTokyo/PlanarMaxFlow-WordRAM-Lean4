module

public import PlanarFlow.BKMNW.LsQ
public import PlanarFlow.BKMNW.NpSeg

/-!
# **The separator conjuncts of `SubSpecS` for `sepL` and `sepX = sepPXS' 100000 sepL`**

* `sepX = sepPXS' 100000 sepL`, `sTX n k = sTL n k + 700 n + 70 k + 800`,
  `sRX n m k = sRL n m k + smRS' n m k` (the step and room functions of `sepPXS'_spec`);
* **`sep_cost_le`**: for `1 ≤ n`, `m ≤ n`:
  `sTL n k + (sTX n k + 13 sRX n m k + 30) ≤ 3200000 n lg n + 3200000 k` (the separator steps of
  `SubSpecS`, `segT = sTX + 13 sRX + 30`, are `O(n lg n + k)` with `C = 3200000`);
* `sRL_mono`;
* **`sep_subSpec`**: under the hypotheses of `sepL_spec`, `SepPSpecXL … sepL sTL sRL`,
  `SepPSpecXS … sepX sTX sRX`, the cost conjunct of `SubSpecS` with `C = 3200000` at every node
  call with a nonempty piece, and `sRL n m k ≤ sRL N N N` for `n, m, k ≤ N`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The separator program of the node step.** -/
def sepX : Stmt := sepPXS' 100000 sepL

/-- The steps of `sepX`. -/
def sTX (n k : ℕ) : ℕ := sTL n k + 700 * n + 70 * k + 800

/-- The room of `sepX`. -/
def sRX (n m k : ℕ) : ℕ := sRL n m k + smRS' n m k

lemma sRL_mono {n m k n' m' k' : ℕ} (hn : n ≤ n') (hm : m ≤ m') (hk : k ≤ k') :
    sRL n m k ≤ sRL n' m' k' := by
  have := lsEncB_mono (show 223 * n + 84 ≤ 223 * n' + 84 by omega)
  unfold sRL; omega

/-- `encB' (223 n + 84) ≤ 614 n lg n + 38068 n + 7`. -/
lemma encB'_lin_le {n : ℕ} (hn : 1 ≤ n) :
    encB' (223 * n + 84) ≤ 614 * (n * lg n) + 38068 * n + 7 := by
  have e := encB'_eq (223 * n + 84)
  have h := lg2_two_mul_le (x := 223 * n + 84) hn le_rfl
  have hL : lg n = Nat.log 2 n + 1 := rfl
  generalize Nat.log 2 (2 * (223 * n + 84)) = a at h e
  generalize Nat.log 2 n = b at h hL
  have p1 : (a + 2) * (2 * (223 * n + 84)) ≤ (b + 12) * (614 * n) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e2 : (b + 12) * (614 * n) = 614 * (n * (b + 1)) + 6754 * n := by ring
  rw [hL]
  generalize encB' (223 * n + 84) = E at e ⊢
  omega

set_option maxRecDepth 20000 in
/-- **The separator steps of `SubSpecS` in `O(n lg n + k)`.** -/
theorem sep_cost_le {n m k : ℕ} (hn : 1 ≤ n) (hm : m ≤ n) :
    sTL n k + (sTX n k + 13 * sRX n m k + 30) ≤ 3200000 * n * lg n + 3200000 * k := by
  have h1 := encB'_lin_le hn
  have h2 : n ≤ n * lg n := Nat.le_mul_of_pos_right n (by unfold lg; omega)
  have e1 : 1010000 * n * lg n = 1010000 * (n * lg n) := by ring
  have e2 : 3200000 * n * lg n = 3200000 * (n * lg n) := by ring
  unfold sTX sRX sTL sRL smRS' smR
  rw [e1, e2]
  generalize encB' (223 * n + 84) = E at h1
  generalize n * lg n = L at h1 h2
  omega

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {ds : DSys M}
  {Reach : MCall M → Prop} {I : Input} {W : ℕ}

/-- **The separator conjuncts of `SubSpecS`** (see the module docstring). -/
theorem sep_subSpec {κ : ℕ} {eG : ℕ → D} {N : ℕ} {d₀ : D}
    (hF : SplitFnsS M S T κ ds.s (CInvS M ds.Q)
      (spSR M (pcChoiceE M ds.Q eG N d₀) (s5sc M eG N) ds.Q)
      (spHR M (pcChoiceE M ds.Q eG N d₀) (s5sc M eG N) ds.Q) (smD M ds.pk S T) (chRot M ds.Q))
    (hsm : ∀ P Hs, RevClosed M P → (smD M ds.pk S T P Hs).piece = P)
    (hdS : ds.spS = guardS M (gSz M S T ds.s (CInvS M ds.Q))
      (spSR M (pcChoiceE M ds.Q eG N d₀) (s5sc M eG N) ds.Q))
    (hdH : ds.spH = guardS M (gHl M S T ds.s (CInvS M ds.Q))
      (spHR M (pcChoiceE M ds.Q eG N d₀) (s5sc M eG N) ds.Q))
    (hdC : ds.chS = chRot M ds.Q) (hds : ds.s = 100000)
    (hdpk : ds.pk = (pcChoiceE M ds.Q eG N d₀).pick)
    (hSTQ : S ∪ T ⊆ ds.Q) (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ ds.Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ ds.Q ∧ M.head d ∈ ds.Q)) (hTS : TailSorted M gid ν)
    (hQ : QPar ds.Q ν) (hν : Injective ν) (hgid : Injective gid)
    (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d) (hsW : 100000 ≤ W)
    (Nb : ℕ) :
    SepPSpecXL M ds Reach gid ν u S T Z I W sepL sTL sRL ∧
    SepPSpecXS M ds Reach gid ν u S T Z I W sepX sTX sRX ∧
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) → 0 < (l.piece ∪ r.piece).card →
      sTL (l.piece ∪ r.piece).card Hs.length + segT M sTX sRX (.node l r π, Hs, σ) ≤
        3200000 * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card +
          3200000 * Hs.length) ∧
    (∀ n m k, n ≤ Nb → m ≤ Nb → k ≤ Nb → sRL n m k ≤ sRL Nb Nb Nb) := by
  have hL := sepL_spec (Reach := Reach) (u := u) (Z := Z) (I := I) hF hsm hdS hdH hdC hds hdpk
    hSTQ hloopM hQdeg hQ5 hTS hQ hν hgid he hesurj hsW
  have hpk : PkMin gid ds.pk := by rw [hdpk]; exact pkMin_pcChoiceE (M := M) (Q := ds.Q) hesurj he d₀
  refine ⟨hL.toXLS.toXL, ?_, fun l r π Hs σ _ hpos => ?_, fun n m k hn hm hk => sRL_mono hn hm hk⟩
  · have := sepPXS'_spec hL hpk hν hloopM (by rw [hds]; exact hsW)
    rw [hds] at this
    exact this.toXS
  · unfold segT
    have hm : (pdarts M (ADec.node l r π).piece Hs).card ≤ (l.piece ∪ r.piece).card :=
      card_le_card (pdarts_subset _ _)
    exact sep_cost_le hpos hm

end MfDrv

end BKMNW

end PlanarFlow
