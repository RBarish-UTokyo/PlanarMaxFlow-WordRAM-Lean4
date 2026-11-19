module

public import PlanarFlow.BKMNW.Nf7fA

/-!
# The envelopes of the bounds of `fixP7` in `m` and `Z`

With `k ≤ m` darts on the part, `b ≤ 2k` corners and `AS ≤ m Z`:

* `fpM m Z = fpB (m Z) m m`, `KM = 16 fpM`, `LM = 8 fpM`, `rtLM = m · KM` (the bounds of `K`, `L`,
  `rtL`);
* **`wzF7 wzm m Z`**: the zero area of `fixP7` (`wzm m (2Z)`, the resident image `SH + WN`, the
  table `9m + 1 + tsz m` and the root word bound `rtW m rtLM m` of the final call);
* **`rOF7 C C₀ Rm m Z`**: the room above the heap top (the largest base `X.p = Q + 15k + lyP 0 b k`,
  the log `LG`, `Rm` summed over `k ≤ m`, `b ≤ 2m`, `negT`, and the address-free values);
  **`rF7 C C₀ Rm N Z = Σ_{m ≤ N} rOF7 C C₀ Rm m Z`**;
* monotonicity: `PE.eval_mono`, `PE.evalU_mono`, `fxWB_mono`, `WNb_mono`, `rtW_mono`, `fW_mono`,
  `wfOf_mono`, `moOf_mono`, `shOf_mono`, `lyP_eq`, `lyP0_mono`, `lgT_mono`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace NegSSSP

namespace PE

/-- `eval` is monotone in the values of the variables. -/
theorem eval_mono {ρ ρ' : ℕ → ℕ} (h : ∀ i, ρ i ≤ ρ' i) : ∀ e : PE, eval ρ e ≤ eval ρ' e
  | cst _ => le_rfl
  | var i => h i
  | add a b => Nat.add_le_add (eval_mono h a) (eval_mono h b)
  | mul a b => Nat.mul_le_mul (eval_mono h a) (eval_mono h b)

/-- `evalU` is monotone in the values of the variables. -/
theorem evalU_mono {ρ ρ' : ℕ → ℕ} (h : ∀ i, ρ i ≤ ρ' i) : ∀ e : PE, evalU ρ e ≤ evalU ρ' e
  | cst _ => le_rfl
  | var i => Nat.add_le_add_right (h i) 1
  | add a b => Nat.add_le_add (evalU_mono h a) (evalU_mono h b)
  | mul a b => Nat.mul_le_mul (evalU_mono h a) (evalU_mono h b)

end PE

lemma fxρ_mono {n L L' : ℕ} (h : L ≤ L') : ∀ i, fxρ n L i ≤ fxρ n L' i
  | 0 => le_rfl
  | 1 => h
  | 2 => le_rfl
  | _ + 3 => le_rfl

/-- `fxWB` is monotone in `L`. -/
lemma fxWB_mono {n L L' : ℕ} (h : L ≤ L') : fxWB n L ≤ fxWB n L' :=
  PE.evalU_mono (fxρ_mono h) _

/-- `WNb` is monotone in `L`. -/
lemma WNb_mono {n L L' : ℕ} (h : L ≤ L') : WNb n L ≤ WNb n L' := by
  have e1 := PE.eval_WNbE (fxρ n L) rfl
  have e2 := PE.eval_WNbE (fxρ n L') rfl
  have h3 := PE.eval_mono (fxρ_mono (n := n) h) PE.WNbE
  have a1 : fxρ n L 0 = n := rfl
  have a2 : fxρ n L 1 = L := rfl
  have a3 : fxρ n L' 0 = n := rfl
  have a4 : fxρ n L' 1 = L' := rfl
  rw [a1, a2] at e1; rw [a3, a4] at e2
  omega

/-- `rtW` is monotone in `L`. -/
lemma rtW_mono {n L L' G : ℕ} (h : L ≤ L') : rtW n L G ≤ rtW n L' G := by
  have h1 := WNb_mono (n := n) h
  have h2 := fxWB_mono (n := n) h
  have h3 : 8 * n * n * (L + 1) ≤ 8 * n * n * (L' + 1) := Nat.mul_le_mul_left _ (by omega)
  unfold rtW rtH rtHb
  omega

end NegSSSP

namespace BKMNW

open Finset NegSSSP NegSSSP.Frame MsCall

/-! ### Monotonicity -/

lemma fLv_mono {b b' : ℕ} (h : b ≤ b') : fLv b ≤ fLv b' := by
  unfold fLv; have := Nat.log_mono_right (b := 2) h; omega

lemma fP2_mono {b b' : ℕ} (h : b ≤ b') : fP2 b ≤ fP2 b' := by
  unfold fP2
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.add_le_add_right (Nat.log_mono_right (Nat.mul_le_mul h (fLv_mono h))) 1)

lemma fW_mono {b b' w w' : ℕ} (hb : b ≤ b') (hw : w ≤ w') : fW b w ≤ fW b' w' := by
  have h1 := fLv_mono hb
  have h2 := fP2_mono hb
  unfold fW
  gcongr

lemma lySb_mono {b b' k k' : ℕ} (hb : b ≤ b') (hk : k ≤ k') : lySb b k ≤ lySb b' k' := by
  unfold lySb; gcongr

lemma wfOf_mono {b b' k k' : ℕ} (hb : b ≤ b') (hk : k ≤ k') : wfOf b k ≤ wfOf b' k' := by
  unfold wfOf
  exact fW_mono hb (by have := lySb_mono hb hk; omega)

lemma moOf_mono {b b' L L' : ℕ} (hb : b ≤ b') (hL : L ≤ L') : moOf b L ≤ moOf b' L' := by
  unfold moOf; gcongr

lemma shOf_mono {b b' k k' L L' : ℕ} (hb : b ≤ b') (hk : k ≤ k') (hL : L ≤ L') :
    shOf b k L ≤ shOf b' k' L' := by
  have h1 := wfOf_mono hb hk
  have h2 := moOf_mono hb hL
  unfold shOf
  gcongr

/-- `lyP` is linear in its base. -/
lemma lyP_eq (S1 b k : ℕ) : lyP S1 b k = S1 + lyP 0 b k := by
  unfold lyP lyOb lyS lyA lyOm; omega

lemma lyP0_mono {b b' k k' : ℕ} (hb : b ≤ b') (hk : k ≤ k') : lyP 0 b k ≤ lyP 0 b' k' := by
  have h1 := lySb_mono hb hk
  unfold lyP lyOb lyS lyA lyOm lyT
  have : b * b ≤ b' * b' := Nat.mul_le_mul hb hb
  omega

/-- The room of the log of a run (`SLx.LG`) as a function of `b`, `k`. -/
def lgT (b k : ℕ) : ℕ := 4 * (6300 * (b * lg b ^ 2 + 2 * k * lg b)) + 3

lemma lgT_mono {b b' k k' : ℕ} (hb : b ≤ b') (hk : k ≤ k') : lgT b k ≤ lgT b' k' := by
  have := lg_mono hb
  unfold lgT; gcongr

/-! ### The envelopes -/

/-- `fpB` at `AS ≤ m Z`, `k ≤ m`. -/
def fpM (m Z : ℕ) : ℕ := fpB (m * Z) m m
/-- The bound of `K = 16 fpB`. -/
def KM (m Z : ℕ) : ℕ := 16 * fpM m Z
/-- The bound of `L = 8 fpB`. -/
def LM (m Z : ℕ) : ℕ := 8 * fpM m Z
/-- The bound of `rtL` (`m · K`). -/
def rtLM (m Z : ℕ) : ℕ := m * KM m Z

/-- The bound of the resident image `SH + WN` of the stages. -/
def shwM (m Z : ℕ) : ℕ :=
  shOf (2 * m) m (LM m Z) + (2 * wfOf (2 * m) m + 1 + moOf (2 * m) (LM m Z) * moOf (2 * m) (LM m Z) +
    moOf (2 * m) (LM m Z))

/-- **The zero area of `fixP7`.** -/
def wzF7 (wzm : ℕ → ℕ → ℕ) (m Z : ℕ) : ℕ :=
  wzm m (2 * Z) + shwM m Z + (9 * m + 1 + NsStep.tsz m) + rtW m (rtLM m Z) m

/-- The address-free values bounded by the word size. -/
def valM (m Z : ℕ) : ℕ :=
  4 * (m * Z) + 20 * KM m Z + 2 * LM m Z + 2 * moOf (2 * m) (LM m Z) + 3 * rtLM m Z + spWs m +
    fxWB m (rtLM m Z) + 3 * Z + m + 300

/-- `Rm` summed over `k ≤ m`, `b ≤ 2m`. -/
def RmS (Rm : ℕ → ℕ → ℕ → ℕ) (m : ℕ) : ℕ :=
  ∑ k ∈ range (m + 1), ∑ b ∈ range (2 * m + 1), Rm m k b

/-- **The room of `fixP7` above the heap top** (frame of `m` darts). -/
def rOF7 (C C₀ : ℕ) (Rm : ℕ → ℕ → ℕ → ℕ) (m Z : ℕ) : ℕ :=
  100 + 100 * m + lyP 0 (2 * m) m + lgT (2 * m) m + RmS Rm m + MfDrv.negT C C₀ m + valM m Z

/-- **The room of `fixP7` at the calls with at most `N` darts.** -/
def rF7 (C C₀ : ℕ) (Rm : ℕ → ℕ → ℕ → ℕ) (N Z : ℕ) : ℕ :=
  ∑ m ∈ range (N + 1), rOF7 C C₀ Rm m Z

lemma Rm_le_RmS (Rm : ℕ → ℕ → ℕ → ℕ) {m k b : ℕ} (hk : k ≤ m) (hb : b ≤ 2 * m) :
    Rm m k b ≤ RmS Rm m := by
  unfold RmS
  have h1 : Rm m k b ≤ ∑ b ∈ range (2 * m + 1), Rm m k b :=
    single_le_sum (f := fun b => Rm m k b) (fun _ _ => Nat.zero_le _)
      (mem_range.2 (by omega))
  exact h1.trans (single_le_sum (f := fun k => ∑ b ∈ range (2 * m + 1), Rm m k b)
    (fun _ _ => Nat.zero_le _) (mem_range.2 (by omega)))

lemma rOF7_le_rF7 (C C₀ : ℕ) (Rm : ℕ → ℕ → ℕ → ℕ) {m N : ℕ} (h : m ≤ N) (Z : ℕ) :
    rOF7 C C₀ Rm m Z ≤ rF7 C C₀ Rm N Z :=
  single_le_sum (f := fun m => rOF7 C C₀ Rm m Z) (fun _ _ => Nat.zero_le _)
    (mem_range.2 (by omega))

/-- The bounds of `K`, `L` from `AS ≤ m Z`, `k ≤ m`. -/
lemma K_le_KM {AS m k Z : ℕ} (hA : AS ≤ m * Z) (hk : k ≤ m) : 16 * fpB AS m k ≤ KM m Z := by
  unfold KM fpM; have := fpB_mono (m := m) (m' := m) hA le_rfl hk; omega

lemma L_le_LM {AS m k Z : ℕ} (hA : AS ≤ m * Z) (hk : k ≤ m) : 8 * fpB AS m k ≤ LM m Z := by
  unfold LM fpM; have := fpB_mono (m := m) (m' := m) hA le_rfl hk; omega

end BKMNW

end PlanarFlow
