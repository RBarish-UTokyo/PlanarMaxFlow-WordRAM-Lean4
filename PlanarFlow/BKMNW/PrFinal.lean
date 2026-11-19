module

public import PlanarFlow.BKMNW.PrTop
public import PlanarFlow.BKMNW.PqRoom

/-!
# Assembling the maximum-flow target

The target `MaxFlowMachine'` of `PlanarFlow/Spec.lean` and its definitions: `Feas.srcs'`, `Feas.snks'`, `Feas.IsSTFlow'`, `Feas.stValue'`, `Feas.MEnc'` (a plane map
**with loops allowed**, transitive rotations and faces, disjoint sources and sinks, words at most
`W`), `Feas.size'`, and **`MaxFlowMachine'`**: one program computes a maximum flow from the
sources to the sinks within `c (n + K + 1)(⌊log₂ n⌋ + 1)³` steps whenever the word size is at least
`c (7 · size)^k`.

* **`ppBound`**: `ppHeadS C C₀ n + 31200 n + 50 K + 2 p + 3210 ≤ cMF C C₀ p · (n + K + 1) ·
  (log₂ n + 1)³` with the explicit `cMF C C₀ p = (100000+11)²·448·(27·102256+25)·machKS C +
  (100000+11)²·28·C₀ + 2 p + 34410`;
* **`maxFlowMachine_of_spec`**: `MfMainSpecS sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ`, the seven
  programs print nothing, `R` monotone with `R N Z ≤ r (N + Z + 1)^q`, `WZ N Z ≤ a (N + Z + 1)^p`,
  `1 ≤ C` ⟹ `MaxFlowMachine'`.
The target follows from seven programs meeting `MfMainSpecS` (`Pp.maxFlowMachine'_holds`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

open Finset

-- The definitions `Feas.srcs'`, `Feas.snks'`, `Feas.IsSTFlow'`, `Feas.stValue'`, `Feas.MEnc'`,
-- `Feas.size'` and `MaxFlowMachine'` that stood here are now part of the PlanarFlow specification
-- (`PlanarFlow/Spec.lean`, maximum-flow target), byte for byte.

namespace BKMNW

namespace Pp

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv Feas

/-- The constant of the time bound. -/
def cMF (C C₀ p : ℕ) : ℕ :=
  (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machKS C + (100000 + 11) ^ 2 * 28 * C₀ +
    2 * p + 34410

/-- **The time bound of the maximum-flow program as `O((n + K + 1) log³ n)`.** -/
theorem ppBound (C C₀ p n K : ℕ) :
    ppHeadS C C₀ n + 31200 * n + 50 * K + 2 * p + 3210 ≤
      cMF C C₀ p * (n + K + 1) * (Nat.log 2 n + 1) ^ 3 := by
  set L := Nat.log 2 n + 1 with hL
  set A := (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machKS C
  set Bc := (100000 + 11) ^ 2 * 28 * C₀
  have hlg : lg n = L := rfl
  have hL1 : 1 ≤ L := by omega
  have hL3 : 1 ≤ L ^ 3 := Nat.one_le_pow _ _ hL1
  have hLL : L ≤ L ^ 3 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 3 := Nat.pow_le_pow_right hL1 (by norm_num)
  set X := n + K + 1 with hX
  have e1 : ppHeadS C C₀ n = A * n * L ^ 3 + Bc * n * L := by
    unfold ppHeadS; rw [hlg]
  have h1 : A * n * L ^ 3 ≤ A * X * L ^ 3 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have h2 : Bc * n * L ≤ Bc * X * L ^ 3 :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hLL
  have h3 : 31200 * n + 50 * K + 2 * p + 3210 ≤ (2 * p + 34410) * X * L ^ 3 := by
    have : 31200 * n + 50 * K + 2 * p + 3210 ≤ (2 * p + 34410) * X := by
      rw [hX]; ring_nf; nlinarith
    calc _ ≤ (2 * p + 34410) * X := this
      _ = (2 * p + 34410) * X * 1 := (mul_one _).symm
      _ ≤ (2 * p + 34410) * X * L ^ 3 := Nat.mul_le_mul_left _ hL3
  have e2 : cMF C C₀ p * X * L ^ 3 = A * X * L ^ 3 + Bc * X * L ^ 3 +
      (2 * p + 34410) * X * L ^ 3 := by
    unfold cMF; ring
  rw [e1, e2]
  omega

lemma runsWithin_mono {prog : Program} {P : Input} {W T T' : ℕ} {out : List ℕ}
    (h : RunsWithin prog P W T out) (hT : T ≤ T') : RunsWithin prog P W T' out := by
  obtain ⟨k, hk, rest⟩ := h
  exact ⟨k, by omega, rest⟩

/-- The flows of the primed target are those of `IsFlow`. -/
lemma isSTFlow'_iff {d : List ℕ} (h : Wf d) (f : Fin (nd d) → ℤ) :
    IsSTFlow' h f ↔ IsFlow (map h) (ucap d) (srcF d) (snkF d) f :=
  ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

lemma stValue'_eq {d : List ℕ} (h : Wf d) (f : Fin (nd d) → ℤ) :
    stValue' h f = val (map h) (srcF d) f := rfl

/-- **The maximum-flow theorem from the specification of the seven programs.** -/
theorem maxFlowMachine_of_spec {sepL sepX fixP c2sP s2cP retP frmP : Stmt} {C C₀ : ℕ}
    {R WZ : ℕ → ℕ → ℕ} {a p r q : ℕ}
    (hspec : MfMainSpecS sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ) (hC : 1 ≤ C)
    (hE1 : Stmt.noEmit sepL = true) (hE2 : Stmt.noEmit sepX = true)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true) (hE6 : Stmt.noEmit retP = true)
    (hE7 : Stmt.noEmit frmP = true)
    (hRm : ∀ N N' Z Z', N ≤ N' → Z ≤ Z' → R N Z ≤ R N' Z')
    (hR : ∀ N Z, R N Z ≤ r * (N + Z + 1) ^ q)
    (hWZ : ∀ N Z, WZ N Z ≤ a * (N + Z + 1) ^ p) :
    MaxFlowMachine' := by
  refine ⟨compile (mfTopL a p sepL sepX fixP c2sP s2cP retP frmP) 0 ++ [Instr.halt],
    20 * (r + a) + 1000000 + cMF C C₀ p, p + q + 4, fun d W he hW => ?_⟩
  have h : MEncL d W := ⟨he.wf, he.plane, he.rotT, he.faceT, he.disj, he.word_le⟩
  have hpw : pipeW r a p q d ≤ W := by
    unfold pipeW
    have e : nd d + nv d + zb d + 2 = size' d := rfl
    rw [e]
    exact le_trans (Nat.mul_le_mul_right _ (by omega)) hW
  obtain ⟨pp, Z, q', hl, hrun, hmax⟩ := mf_pipelineTL hspec hC hE1 hE2 hE3 hE4 hE5 hE6 hE7 hRm
    hWZ h (pipeRoomS_of_pow hR hpw)
  refine ⟨pp, Z, q', hl, (isSTFlow'_iff he.wf _).2 hmax.1, fun g hg => ?_,
    runsWithin_mono hrun ?_⟩
  · rw [stValue'_eq, stValue'_eq]
    exact hmax.2 g ((isSTFlow'_iff he.wf g).1 hg)
  · refine (ppBound C C₀ p (nd d) (nv d)).trans ?_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))

end Pp

end BKMNW

end PlanarFlow
