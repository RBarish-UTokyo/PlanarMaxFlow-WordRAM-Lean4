module

public import PlanarFlow.BKMNW.PfP

/-!
# `lgPF` with the vertex keys exported

**`lgPF_execK`**: `lgPF_exec` (proof copied) plus `VK[i] = vkF VP i` at `Yb` (the vertex keys,
needed by stage 7's `S7In`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Exec

variable {P : Input} {W : ℕ}

theorem lgPF_execK (c : Config) (hc : WordsBounded W c) {n np n' RPb IXb PDb Yb VPb : ℕ}
    (r00 : c.nreg 6000 = n) (r17 : c.nreg 6017 = np) (r01 : c.nreg 6001 = RPb) (r02 : c.nreg 6002 = IXb)
    (r03 : c.nreg 6003 = PDb) (r11 : c.nreg 6011 = Yb) (r12 : c.nreg 6012 = VPb)
    (hn : 1 ≤ n) (hn' : 1 ≤ n') (hnp1 : 1 ≤ np) (hnp : np ≤ n)
    (hRP : ∀ i < n, c.nmem (RPb + i) < n) (hIX : ∀ q < n', c.nmem (IXb + q) < n)
    (hPD : ∀ j < np, c.nmem (PDb + j) ≤ n')
    (lay : RPb + n ≤ Yb ∧ IXb + n' ≤ Yb ∧ PDb + np ≤ Yb ∧ VPb + n ≤ Yb ∧ Yb + 8 * n + 2 ≤ W) :
    ∃ c' t, Exec P W lgPF c c' t ∧ t ≤ 150 * n + 100 ∧
      (∀ i < n, c'.nmem (Yb + 2 * n + 1 + i) =
        if ∃ j < np - 1, pfKB (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q)) n j = i ∨
          pfKC (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
            (fun i => c.nmem (RPb + i)) n j = i then 1 else 0) ∧
      (∀ i < n, c'.nmem (Yb + 3 * n + 2 + i) =
        if (∃ j < np, pfKA (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
            (vkF (fun j => c.nmem (VPb + j))) n j = vkF (fun j => c.nmem (VPb + j)) i) ∨
          (∃ j < np - 1, pfKD (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
            (fun i => c.nmem (RPb + i)) (vkF (fun j => c.nmem (VPb + j))) n j =
              vkF (fun j => c.nmem (VPb + j)) i) then 1 else 0) ∧
      (∀ i < n, c'.nmem (Yb + i) = vkF (fun j => c.nmem (VPb + j)) i) ∧
      (∀ a, ¬ (Yb ≤ a ∧ a < Yb + 8 * n + 2) → c'.nmem a = c.nmem a) ∧
      (∀ x, pfKeepR x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l0, l1, l2, l3, l4⟩ := lay
  have hvkn : ∀ i < n, vkF (fun j => c.nmem (VPb + j)) i < n := fun i hi =>
    lt_of_le_of_lt (vkF_le _ i) hi
  -- the set-up
  obtain ⟨c₁, t₁, e₁, ht₁, hR₁, vk₁, z₁, m₁, k₁, rr₁, rm₁, o₁⟩ := pfA1_exec (P := P) c hc r00 r17 r11
    r12 hn ⟨l3, l4⟩
  have hw₁ := e₁.wb_right
  have hpd₁ : ∀ j < np, c₁.nmem (PDb + j) = c.nmem (PDb + j) := fun j hj => m₁ _ (by omega)
  have hix₁ : ∀ q < n', c₁.nmem (IXb + q) = c.nmem (IXb + q) := fun q hq => m₁ _ (by omega)
  have hrp₁ : ∀ i < n, c₁.nmem (RPb + i) = c.nmem (RPb + i) := fun i hi => m₁ _ (by omega)
  have r01₁ : c₁.nreg 6001 = RPb := by rw [k₁ _ (by omega), r01]
  have r02₁ : c₁.nreg 6002 = IXb := by rw [k₁ _ (by omega), r02]
  have r03₁ : c₁.nreg 6003 = PDb := by rw [k₁ _ (by omega), r03]
  -- the keys
  obtain ⟨c₂, t₂, e₂, ht₂, KA, m₂, k₂, rr₂, rm₂, o₂⟩ := pfKA_exec (P := P) c₁ hw₁ (n' := n')
    hR₁ r02₁ r03₁ hpd₁ hix₁ vk₁ hPD hIX hn' hnp ⟨by omega, by omega, l4⟩
  have hw₂ := e₂.wb_right
  have g2 : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c₂.nreg x = c₁.nreg x := fun x hx =>
    k₂ x (by unfold vscr; omega) (by omega) (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, KB, m₃, k₃, rr₃, rm₃, o₃⟩ := pfKB_exec (P := P) c₂ hw₂ (n' := n')
    (hR₁.congr g2) (by rw [g2 _ (by omega), r02₁]) (by rw [g2 _ (by omega), r03₁])
    (fun j hj => by rw [m₂ _ (by omega), hpd₁ j hj])
    (fun q hq => by rw [m₂ _ (by omega), hix₁ q hq]) hPD hnp hn hn' ⟨by omega, by omega, l4⟩
  have hw₃ := e₃.wb_right
  have g3 : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c₃.nreg x = c₁.nreg x := fun x hx => by
    rw [k₃ x (by unfold vscr; omega) (by omega) (by omega), g2 x hx]
  have hm3 : ∀ a, (a < Yb ∨ (Yb ≤ a ∧ a < Yb + 4 * n + 2)) → c₃.nmem a = c₁.nmem a :=
    fun a ha => by rw [m₃ a (by omega), m₂ a (by omega)]
  obtain ⟨c₄, t₄, e₄, ht₄, KC, m₄, k₄, rr₄, rm₄, o₄⟩ := pfKC_exec (P := P) c₃ hw₃ (n' := n')
    (hR₁.congr g3) (by rw [g3 _ (by omega), r01₁]) (by rw [g3 _ (by omega), r02₁])
    (by rw [g3 _ (by omega), r03₁])
    (fun j hj => by rw [hm3 _ (by omega), hpd₁ j hj])
    (fun q hq => by rw [hm3 _ (by omega), hix₁ q hq])
    (fun i hi => by rw [hm3 _ (by omega), hrp₁ i hi]) hPD hnp hIX hn hn'
    ⟨by omega, by omega, by omega, l4⟩
  have hw₄ := e₄.wb_right
  have g4 : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c₄.nreg x = c₁.nreg x := fun x hx => by
    rw [k₄ x (by unfold vscr; omega) (by omega) (by omega), g3 x hx]
  have hm4 : ∀ a, (a < Yb ∨ (Yb ≤ a ∧ a < Yb + 4 * n + 2)) → c₄.nmem a = c₁.nmem a :=
    fun a ha => by rw [m₄ a (by omega), hm3 a ha]
  obtain ⟨c₅, t₅, e₅, ht₅, KD, m₅, k₅, rr₅, rm₅, o₅⟩ := pfKD_exec (P := P) c₄ hw₄ (n' := n')
    (hR₁.congr g4) (by rw [g4 _ (by omega), r01₁]) (by rw [g4 _ (by omega), r02₁])
    (by rw [g4 _ (by omega), r03₁])
    (fun j hj => by rw [hm4 _ (by omega), hpd₁ j hj])
    (fun q hq => by rw [hm4 _ (by omega), hix₁ q hq])
    (fun i hi => by rw [hm4 _ (by omega), hrp₁ i hi])
    (fun i hi => by rw [hm4 _ (by omega), vk₁ i hi]) hPD hnp hIX hRP hn hn'
    ⟨by omega, by omega, by omega, l4⟩
  have hw₅ := e₅.wb_right
  have g5 : ∀ x, ((6000 ≤ x ∧ x ≤ 6018) ∨ x = 6521) → c₅.nreg x = c₁.nreg x := fun x hx => by
    rw [k₅ x (by unfold vscr; omega) (by omega) (by omega), g4 x hx]
  have hR₅ : PfRegs c₅ n np Yb := hR₁.congr g5
  -- the memory after the keys
  have hk5 : ∀ a, (a < Yb + 4 * n + 2 ∨ Yb + 8 * n + 2 ≤ a) → c₅.nmem a = c₁.nmem a :=
    fun a ha => by rw [m₅ a (by omega), m₄ a (by omega), m₃ a (by omega), m₂ a (by omega)]
  have hKA5 : ∀ j < np, c₅.nmem (Yb + 4 * n + 2 + j) = pfKA (fun j => c.nmem (PDb + j))
      (fun q => c.nmem (IXb + q)) (vkF (fun j => c.nmem (VPb + j))) n j := fun j hj => by
    rw [m₅ _ (by omega), m₄ _ (by omega), m₃ _ (by omega)]; exact KA j hj
  have hKB5 : ∀ j < np - 1, c₅.nmem (Yb + 5 * n + 2 + j) = pfKB (fun j => c.nmem (PDb + j))
      (fun q => c.nmem (IXb + q)) n j := fun j hj => by
    rw [m₅ _ (by omega), m₄ _ (by omega)]; exact KB j hj
  have hKC5 : ∀ j < np - 1, c₅.nmem (Yb + 6 * n + 2 + j) = pfKC (fun j => c.nmem (PDb + j))
      (fun q => c.nmem (IXb + q)) (fun i => c.nmem (RPb + i)) n j := fun j hj => by
    rw [m₅ _ (by omega)]; exact KC j hj
  -- the bounds of the keys
  have bA : ∀ j < np, pfKA (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
      (vkF (fun j => c.nmem (VPb + j))) n j ≤ n := fun j hj => by
    have := hPD j hj
    exact pf_key_le (dself_le _) (hvkn _ (hIX (c.nmem (PDb + j) - 1) (by omega)))
  have bB : ∀ j < np - 1, pfKB (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q)) n j ≤ n :=
    fun j hj => by
      have := hPD j (by omega)
      exact pf_key_le (dself_le _) (hIX (c.nmem (PDb + j) - 1) (by omega))
  have bC : ∀ j < np - 1, pfKC (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
      (fun i => c.nmem (RPb + i)) n j ≤ n := fun j hj => by
    have := hPD j (by omega)
    exact pf_key_le (dself_le _) (hRP _ (hIX (c.nmem (PDb + j) - 1) (by omega)))
  have bD : ∀ j < np - 1, pfKD (fun j => c.nmem (PDb + j)) (fun q => c.nmem (IXb + q))
      (fun i => c.nmem (RPb + i)) (vkF (fun j => c.nmem (VPb + j))) n j ≤ n := fun j hj => by
    have := hPD j (by omega)
    exact pf_key_le (dself_le _) (hvkn _ (hRP _ (hIX (c.nmem (PDb + j) - 1) (by omega))))
  -- the marks
  obtain ⟨c₆, t₆, e₆, ht₆, T6, mm₆, n6, rr₆, rm₆, o₆⟩ := pfMark_exec (P := P) c₅ hw₅
    (a := 6017) (b := 6008) (d := 6005) (n := n) (by omega) (by omega) (by omega) hR₅.r17
    hR₅.r08 hR₅.r05 hKA5 bA (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hw₆ := e₆.wb_right
  have hR₆ : PfRegs c₆ n np Yb := hR₅.congr fun x hx => n6 x (by omega)
  obtain ⟨c₇, t₇, e₇, ht₇, T7, mm₇, n7, rr₇, rm₇, o₇⟩ := pfMark_exec (P := P) c₆ hw₆
    (a := 6018) (b := 6014) (d := 6005) (n := n) (key := pfKD (fun j => c.nmem (PDb + j))
      (fun q => c.nmem (IXb + q)) (fun i => c.nmem (RPb + i)) (vkF (fun j => c.nmem (VPb + j))) n)
    (by omega) (by omega) (by omega) hR₆.r18 hR₆.r14 hR₆.r05
    (fun j hj => by rw [mm₆ _ (by omega)]; exact KD j hj) bD
    (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hw₇ := e₇.wb_right
  have hR₇ : PfRegs c₇ n np Yb := hR₆.congr fun x hx => n7 x (by omega)
  obtain ⟨c₈, t₈, e₈, ht₈, T8, mm₈, n8, rr₈, rm₈, o₈⟩ := pfMark_exec (P := P) c₇ hw₇
    (a := 6018) (b := 6009) (d := 6006) (n := n) (by omega) (by omega) (by omega) hR₇.r18
    hR₇.r09 hR₇.r06 (fun j hj => by rw [mm₇ _ (by omega), mm₆ _ (by omega)]; exact hKB5 j hj) bB
    (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hw₈ := e₈.wb_right
  have hR₈ : PfRegs c₈ n np Yb := hR₇.congr fun x hx => n8 x (by omega)
  obtain ⟨c₉, t₉, e₉, ht₉, T9, mm₉, n9, rr₉, rm₉, o₉⟩ := pfMark_exec (P := P) c₈ hw₈
    (a := 6018) (b := 6013) (d := 6006) (n := n) (by omega) (by omega) (by omega) hR₈.r18
    hR₈.r13 hR₈.r06
    (fun j hj => by rw [mm₈ _ (by omega), mm₇ _ (by omega), mm₆ _ (by omega)]; exact hKC5 j hj) bC
    (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have hw₉ := e₉.wb_right
  have hR₉ : PfRegs c₉ n np Yb := hR₈.congr fun x hx => n9 x (by omega)
  -- the vertex flags
  have hvk₉ : ∀ i < n, c₉.nmem (Yb + i) = vkF (fun j => c.nmem (VPb + j)) i := fun i hi => by
    rw [mm₉ _ (by omega), mm₈ _ (by omega), mm₇ _ (by omega), mm₆ _ (by omega),
      hk5 _ (by omega)]
    exact vk₁ i hi
  obtain ⟨c₁₀, t₁₀, e₁₀, ht₁₀, VF, mm₁₀, n10, rr₁₀, rm₁₀, o₁₀⟩ := pfVF_exec (P := P) c₉ hw₉ hR₉
    hvk₉ hvkn l4
  refine ⟨c₁₀, t₁ + ((t₂ + (t₃ + (t₄ + t₅))) + ((t₆ + (t₇ + (t₈ + t₉))) + t₁₀)),
    .seq e₁ (.seq (.seq e₂ (.seq e₃ (.seq e₄ e₅))) (.seq (.seq e₆ (.seq e₇ (.seq e₈ e₉))) e₁₀)),
    ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun a ha => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · have : np - 1 ≤ np := Nat.sub_le np 1
    omega
  · have hz : c₁.nmem (Yb + 2 * n + 1 + i) = 0 := by
      have := z₁ (n + 1 + i) (by omega)
      rwa [show Yb + n + (n + 1 + i) = Yb + 2 * n + 1 + i by omega] at this
    rw [mm₁₀ _ (by omega), T9 i (by omega), T8 i (by omega), mm₇ _ (by omega), mm₆ _ (by omega),
      hk5 _ (by omega), hz]
    exact pf_if_or2
  · have hv := hvkn i hi
    rw [VF i hi, mm₉ _ (by omega), mm₈ _ (by omega), T7 _ (by omega), T6 _ (by omega),
      hk5 _ (by omega), show Yb + n + vkF (fun j => c.nmem (VPb + j)) i =
        Yb + n + vkF (fun j => c.nmem (VPb + j)) i from rfl, z₁ _ (by omega)]
    exact pf_if_or
  · rw [mm₁₀ _ (by omega)]; exact hvk₉ i hi
  · rw [mm₁₀ a (by omega), mm₉ a (by omega), mm₈ a (by omega), mm₇ a (by omega),
      mm₆ a (by omega), hk5 a (by omega), m₁ a (by omega)]
  · unfold pfKeepR at hx
    rw [n10 x (by unfold vscr; omega) (by omega) (by omega), n9 x (by omega), n8 x (by omega),
      n7 x (by omega), n6 x (by omega), k₅ x (by unfold vscr; omega) (by omega) (by omega),
      k₄ x (by unfold vscr; omega) (by omega) (by omega),
      k₃ x (by unfold vscr; omega) (by omega) (by omega),
      k₂ x (by unfold vscr; omega) (by omega) (by omega), k₁ x (by omega)]
  · rw [rr₁₀, rr₉, rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁]
  · rw [rm₁₀, rm₉, rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁]
  · rw [o₁₀, o₉, o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
