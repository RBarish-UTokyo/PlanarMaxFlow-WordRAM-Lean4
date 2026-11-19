module

public import PlanarFlow.BKMNW.Nf7fF
public import PlanarFlow.BKMNW.Nf9aG
public import PlanarFlow.BKMNW.Nf9aD
public import PlanarFlow.BKMNW.ThFinalB

/-!
# The maximum flow from a frame-level frozen-fix program

**`Pp.maxFlowMachine_of_frame`**: `MaxFlowMachine'` from a program `fixC` meeting
`FixFrameSpec` for the concrete MSSP call `msspCall' msEnc` (scratch `EScr ∨ msScr`, room
`MsEnc.Rm`, zero area `MsEnc.wzm`, `C = 3200000`, any `C₀`) — accepted in the form
`(∀ x, EScr x ∨ msScr x → x < 9300) → FixFrameSpec …` —, with `noEmit fixC`, the cost hypothesis
of `NcFz.fzHypF_of_frame` and polynomial bounds `wzf m Z ≤ a (m + Z + 1)^p`,
`fxR m Z ≤ r (m + Z + 1)^q`. It is `Pp.maxFlowMachine_final'` with

* `fixP = fixP7 (msspCall' msEnc)` and **`Pp.fixHypF'_fixP7`** (`Nf7fF`);
* `c2sP (fzP fixC) pbP`, `s2cP (fzP fixC) pbP` by `NcFz.c2sHypF_of_frame`, `s2cHypF_of_frame`;
* the encoder facts `MsEnc.msEnc_spec`, `MsCall.msspCall'_spec` (step bound
  `cost = msCost' msEncCost KCf ZCf`), `MsEnc.msCost'_slack_cMachS`, `EScr r → r < 9300`
  (the step bound `msCostS C C₀` of the MSSP premises of `FixHypF'`, `C2SHypF`, `S2CHypF` is
  supplied inside `maxFlowMachine_final'` by `msspCall'_cMachS`); none of them constrains `C₀`;
* the zero areas `wzF7 MsEnc.wzm + 2 (wzc + fzWz wzf) ≤ (10⁶⁵ + 6a)(m + Z + 1)^(2p + 33)`
  (`wz_total_le`) and the rooms `rF7 + 2 c2sRC (fzRN fxR) ≤ (10⁴² + 6r)(N + Z + 1)^(2q + 33)`
  (`r_total_le`), from `Nf9aC`, `Nf9aD`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open WordRAM WordRAM.Machine MfDrv NcStep

/-- **The scratch of the MSSP call with the encoder is below `9300`.** -/
lemma escr_lt {x : ℕ} (h : MsEnc.EScr x ∨ MsCall.msScr x) : x < 9300 := by
  rcases h with h | h
  · unfold MsEnc.EScr at h; omega
  · unfold MsCall.msScr at h; omega

/-- The MSSP call with the encoder has no output instruction. -/
theorem msspCall'_msEnc_noEmit : Stmt.noEmit (MsCall.msspCall' MsEnc.msEnc) = true := by
  decide +kernel

/-- `fzP fixC` has no output instruction when `fixC` has none. -/
theorem fzP_noEmit {fixC : Stmt} (h : Stmt.noEmit fixC = true) :
    Stmt.noEmit (NcFz.fzP fixC) = true := by
  have h1 : Stmt.noEmit NcFz.pfP = true := by decide +kernel
  have h2 : Stmt.noEmit NcFz.fxG = true := by decide +kernel
  have h3 : Stmt.noEmit NcFz.cbP = true := by decide +kernel
  simp only [NcFz.fzP, Stmt.noEmit, h, h1, h2, h3, Bool.and_self]

/-- `wzc m Z ≤ 3 · 10⁶⁴ (m + Z + 1)³²`. -/
lemma wzc_le (m Z : ℕ) : wzc m Z ≤ 3 * 10 ^ 64 * (m + Z + 1) ^ 32 := by
  calc wzc m Z = 3 * (m + Z + 100) ^ 32 := rfl
    _ ≤ 3 * (100 * (m + Z + 1)) ^ 32 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = 3 * 10 ^ 64 * (m + Z + 1) ^ 32 :=
        (fun (X : ℕ) => (by ring : 3 * (100 * X) ^ 32 = 3 * 10 ^ 64 * X ^ 32)) _

/-- **The total zero area** of `fixP7`, `c2sP (fzP fixC) pbP` and `s2cP (fzP fixC) pbP`. -/
theorem wz_total_le {wzf : ℕ → ℕ → ℕ} {a p : ℕ} (hwz : ∀ m Z, wzf m Z ≤ a * (m + Z + 1) ^ p)
    (m Z : ℕ) :
    wzF7 MsEnc.wzm m Z + (wzc m Z + NcFz.fzWz wzf m Z) + (wzc m Z + NcFz.fzWz wzf m Z) ≤
      (10 ^ 65 + 6 * a) * (m + Z + 1) ^ (2 * p + 33) := by
  have h1 := P9.wzF7_wzm_le m Z
  have h2 := wzc_le m Z
  have h3 := fzWz_le hwz m Z
  have hX : 1 ≤ m + Z + 1 := by omega
  have e1 : (m + Z + 1) ^ 32 ≤ (m + Z + 1) ^ (2 * p + 33) := Nat.pow_le_pow_right hX (by omega)
  have e2 : (m + Z + 1) ^ (2 * p + 1) ≤ (m + Z + 1) ^ (2 * p + 33) :=
    Nat.pow_le_pow_right hX (by omega)
  generalize (m + Z + 1) ^ 32 = A at h1 h2 e1
  generalize (m + Z + 1) ^ (2 * p + 1) = B at h3 e2
  generalize (m + Z + 1) ^ (2 * p + 33) = Y at e1 e2 ⊢
  have f1 : 10 ^ 41 * A ≤ 10 ^ 41 * Y := Nat.mul_le_mul_left _ e1
  have f2 : 3 * 10 ^ 64 * A ≤ 3 * 10 ^ 64 * Y := Nat.mul_le_mul_left _ e1
  have f3 : 3 * a * B ≤ 3 * a * Y := Nat.mul_le_mul_left _ e2
  have f4 : 10 ^ 41 * Y + 2 * (3 * 10 ^ 64 * Y) ≤ 10 ^ 65 * Y := by
    have : 10 ^ 41 * Y + 2 * (3 * 10 ^ 64 * Y) = (10 ^ 41 + 6 * 10 ^ 64) * Y := by ring
    rw [this]; exact Nat.mul_le_mul_right _ (by norm_num)
  have f5 : (10 ^ 65 + 6 * a) * Y = 10 ^ 65 * Y + 2 * (3 * a * Y) := by ring
  rw [f5]
  omega

/-- **The total room** of `fixP7`, `c2sP (fzP fixC) pbP` and `s2cP (fzP fixC) pbP`. -/
theorem r_total_le {fxR : ℕ → ℕ → ℕ} {r q : ℕ} (hr : ∀ m Z, fxR m Z ≤ r * (m + Z + 1) ^ q)
    (C₀ N Z : ℕ) :
    rF7 3200000 C₀ MsEnc.Rm N Z + c2sRC (NcFz.fzRN fxR) N Z + c2sRC (NcFz.fzRN fxR) N Z ≤
      (10 ^ 42 + 6 * r) * (N + Z + 1) ^ (2 * q + 33) := by
  have h1 := P9.rF7_Rm_le C₀ N Z
  have h2 := c2sRC_fzRN_le hr N Z
  have hX : 1 ≤ N + Z + 1 := by omega
  have e1 : (N + Z + 1) ^ 33 ≤ (N + Z + 1) ^ (2 * q + 33) := Nat.pow_le_pow_right hX (by omega)
  have e2 : (N + Z + 1) ^ (2 * q + 5) ≤ (N + Z + 1) ^ (2 * q + 33) :=
    Nat.pow_le_pow_right hX (by omega)
  generalize (N + Z + 1) ^ 33 = A at h1 e1
  generalize (N + Z + 1) ^ (2 * q + 5) = B at h2 e2
  generalize (N + Z + 1) ^ (2 * q + 33) = Y at e1 e2 ⊢
  have f1 : 10 ^ 41 * A ≤ 10 ^ 41 * Y := Nat.mul_le_mul_left _ e1
  have f2 : (3 * r + 4000000144) * B ≤ (3 * r + 4000000144) * Y := Nat.mul_le_mul_left _ e2
  have f3 : (3 * r + 4000000144) * Y = 3 * (r * Y) + 4000000144 * Y := by ring
  have f4 : 10 ^ 41 * Y + 8000000288 * Y ≤ 10 ^ 42 * Y := by
    have : 10 ^ 41 * Y + 8000000288 * Y = (10 ^ 41 + 8000000288) * Y := by ring
    rw [this]; exact Nat.mul_le_mul_right _ (by norm_num)
  have f5 : (10 ^ 42 + 6 * r) * Y = 10 ^ 42 * Y + 6 * (r * Y) := by ring
  rw [f5]
  omega

/-- **The maximum flow from a frame-level frozen-fix program** (see the module docstring). -/
theorem maxFlowMachine_of_frame {fixC : Stmt} {C₀ : ℕ} {fxT : ℕ → ℕ → ℕ → ℕ}
    {fxR wzf : ℕ → ℕ → ℕ} {a p r q : ℕ}
    (hFF : (∀ x, (MsEnc.EScr x ∨ MsCall.msScr x) → x < 9300) →
      NcFz.FixFrameSpec fixC (MsCall.msspCall' MsEnc.msEnc)
        (fun x => MsEnc.EScr x ∨ MsCall.msScr x) MsEnc.Rm MsEnc.wzm 3200000 C₀ fxT fxR wzf)
    (hT : ∀ m xf k L, 1 ≤ m → m ≤ L →
      NcFz.pfT m + 3 + fxT m xf k + (24 * m + 40) ≤ (cMachS 3200000 C₀).fixRun m xf k (3 * L))
    (hE : Stmt.noEmit fixC = true)
    (hwz : ∀ m Z, wzf m Z ≤ a * (m + Z + 1) ^ p)
    (hr : ∀ m Z, fxR m Z ≤ r * (m + Z + 1) ^ q) :
    MaxFlowMachine' := by
  have hF := hFF fun x hx => escr_lt hx
  exact maxFlowMachine_final' (C := 3200000) (C₀ := C₀) le_rfl
    (cost := MsCall.msCost' MsEnc.msEncCost (fun m k _ => MsEnc.KCf m k)
      (fun m _ _ => MsEnc.ZCf m))
    (a := 10 ^ 65 + 6 * a) (p := 2 * p + 33) (r := 10 ^ 42 + 6 * r) (q := 2 * q + 33)
    (fun M => MsEnc.msEnc_spec) (fun M => MsCall.msspCall'_spec MsEnc.msEnc_spec)
    (fun m k q hm hq => MsEnc.msCost'_slack_cMachS 3200000 C₀ hm hq)
    (fun x hx => escr_lt (Or.inl hx))
    (fixHypF'_fixP7 (by norm_num) _ _ _ _ _)
    (NcFz.c2sHypF_of_frame hF hT (by norm_num))
    (NcFz.s2cHypF_of_frame hF hT (by norm_num))
    (fixP7_noEmit msspCall'_msEnc_noEmit) (c2sP_noEmit (fzP_noEmit hE))
    (s2cP_noEmit (fzP_noEmit hE))
    (fun m Z => wz_total_le hwz m Z) (fun N Z => r_total_le hr C₀ N Z)

end Pp

end BKMNW

end PlanarFlow
