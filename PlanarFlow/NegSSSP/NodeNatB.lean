module

public import PlanarFlow.NegSSSP.NodeNatA

/-!
# The node run on natural words: Bellman–Ford of the node

`bfFull_cmp_emb`: the run of `bfFull` inside a larger configuration (as in `bfFull_exec_emb`,
word bound `W' ≥ bfWP b`) is compare-bounded by `bfHc b L` and leaves its real memory `≤ bfWP b`
bounded by `bfB b L` (from `bfFull_good` on the truncation, `ExecCmp.lift_det`).

`bfStage_cmp`: from a configuration as in `bfPre_start` (the start of `bfStage` in the node run)
with the invariant `NInv W' B` (real memory `≤ W'` and the registers `500 … 519` bounded by `B`)
and integer reals, every run of `bfStage` compares within `2 bfB b B` and ends with
`NInv W' (bfB b B)`: the preparation `bfPre` and the outputs (`bfOut`, the copy of the values)
pass the abstract interpretation (`bfPre_glueOK`, `bfTail_glueOK`), Bellman–Ford is
`bfFull_cmp_emb` with the lengths bounded by `L = B`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge CmpAbs ModNat

variable {P : Input} {b L : ℕ} {X₁ X₂ : ℕ → ℕ → Prop} {D₁ D₂ : ℕ → ℕ → ℤ} {π : ℕ → ℕ}

/-- **Bellman–Ford inside the node is compare-bounded.** -/
theorem bfFull_cmp_emb (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁)
    (hD₂ : CrossingX b X₂ D₂) (hL₁ : ∀ s t, s < b → t < b → |(D₁ s t : ℝ)| ≤ L)
    (hL₂ : ∀ s t, s < b → t < b → |(D₂ s t : ℝ)| ≤ L) {W' : ℕ} (hW : bfWP b ≤ W') (d : Config)
    (hd : WordsBounded W' d) (hR : BFRegs b d) (hM : BFMem b X₁ D₁ X₂ D₂ π d)
    (hrb : ∀ r < 85, d.nreg r ≤ bfWP b) (hmb : ∀ a ≤ bfWP b, d.nmem a ≤ bfWP b)
    (hMB : MemB (bfWP b) (bfB b L) d) {d' : Config} {k : ℕ} (e : Exec P W' bfFull d d' k) :
    ExecCmp P W' (bfHc b L) bfFull d d' k ∧ MemB (bfWP b) (bfB b L) d' ∧ Keep bfU (bfWP b) d d' := by
  set c := trunc bfU (bfWP b) d with hcdef
  have hA := agree_trunc bfU (bfWP b) d
  have hn : ∀ r < 85, c.nreg r = d.nreg r := fun r hr => (hA.nreg r (by simp [bfU, hr])).symm
  have hm : ∀ a ≤ bfWP b, c.nmem a = d.nmem a := fun a ha => (hA.nmem a ha).symm
  have hrm : ∀ a ≤ bfWP b, c.rmem a = d.rmem a := fun a ha => (hA.rmem a ha).symm
  have hw : WordsBounded (bfWP b) c :=
    wordsBounded_trunc (fun r hr => hrb r (by simpa [bfU] using hr)) hmb
  have hRc : BFRegs b c := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [hn _ (by omega)]
    exacts [hR.r1, hR.r2, hR.r3, hR.r4, hR.r7, hR.r8, hR.r9, hR.r10, hR.r40, hR.r41, hR.r42,
      hR.r43, hR.r80, hR.r81]
  have hWb : bfWP b = 8 * (b * b) + 14 * b + 12 := rfl
  have hMc : BFMem b X₁ D₁ X₂ D₂ π c := by
    refine ⟨fun i hi => ?_, fun s t hs ht => ?_, fun s t hs ht => ?_, fun s t hs ht => ?_,
      fun s t hs ht => ?_⟩
    · rw [hm _ (by omega)]; exact hM.pm i hi
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [hm _ (by omega)]; exact hM.f1 s t hs ht
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [hm _ (by omega)]; exact hM.f2 s t hs ht
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [hrm _ (by omega)]; exact hM.d1 s t hs ht
    · obtain ⟨-, -, d3⟩ := rowcol hs ht
      rw [hrm _ (by omega)]; exact hM.d2 s t hs ht
  obtain ⟨c', kc, ec, -⟩ := bfFull_exec_any (P := P) hπ hD₁ hD₂ c hw hRc hMc
  have hMBc : MemB (bfWP b) (bfB b L) c := fun a ha => by rw [hrm a ha]; exact hMB a ha
  have hg := bfFull_good (P := P) hπ hD₁ hD₂ hL₁ hL₂ c hw hRc hMc
  have hMB' := hg.mem ec hMBc
  obtain ⟨hC, hA', hK⟩ := ((hg.toCmp hMBc).exec ec).lift_det bfFull_regsOK bfFull_noInp
    bfFull_noRand hW hd e
  exact ⟨hC, fun a ha => by rw [hA'.rmem a ha]; exact hMB' a ha, hK⟩

/-- A run of `bfStage` from the runs of its preparation and of the rest. -/
theorem bfStage_cmp_join {W H : ℕ} {c c₉ c' : Config} {k₁ k₂ : ℕ}
    (h₁ : ExecCmp P W H bfPre c c₉ k₁)
    (h₂ : ExecCmp P W H (.seq bfFull (.seq bfOut (.seq (cpS 802 809 973 810 86) cpyProg))) c₉ c'
      k₂) : ∃ k, ExecCmp P W H bfStage c c' k := by
  unfold bfPre at h₁
  unfold bfStage
  cases h₁ with | seq a1 h₁ =>
  cases h₁ with | seq a2 h₁ =>
  cases h₁ with | seq a3 h₁ =>
  cases h₁ with | seq a4 h₁ =>
  cases h₁ with | seq a5 h₁ =>
  cases h₁ with | seq a6 h₁ =>
  cases h₁ with | seq a7 h₁ =>
  cases h₁ with | seq a8 a9 =>
  cases h₂ with | seq a10 h₂ =>
  exact ⟨_, .seq a1 (.seq a2 (.seq a3 (.seq a4 (.seq a5 (.seq a6 (.seq a7 (.seq a8 (.seq a9
    (.seq a10 h₂)))))))))⟩

theorem le_bfB {b B : ℕ} (hb : 1 ≤ b) : B ≤ bfB b B := by
  unfold bfB
  have : B ≤ b * b * B := Nat.le_mul_of_pos_left B (Nat.mul_pos hb hb)
  omega

set_option maxHeartbeats 1000000 in
/-- **Bellman–Ford of the node is compare-bounded** (see the module docstring). -/
theorem bfStage_cmp {b B : ℕ} (hb : 1 ≤ b) {X₁ X₂ : ℕ → ℕ → Prop} {D₁ D₂ : ℕ → ℕ → ℤ}
    {π : ℕ → ℕ} (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁) (hD₂ : CrossingX b X₂ D₂)
    {πb F0 F1 Ob R Z6 Z7 W' : ℕ} (hL : BLay b πb F0 F1 Ob R Z6 Z7 W') (c : Config)
    (hc : WordsBounded W' c) (h802 : c.nreg 802 = b) (h970 : c.nreg 970 = πb)
    (h971 : c.nreg 971 = F0) (h972 : c.nreg 972 = F1) (h974 : c.nreg 974 = R)
    (hπm : ∀ i < b, c.nmem (πb + i) = π i)
    (hF0 : ∀ s < b, ∀ t < b, c.nmem (F0 + (s * b + t)) = finB X₁ s t ∧
      c.rmem (F0 + (s * b + t)) = (D₁ s t : ℝ))
    (hF1 : ∀ s < b, ∀ t < b, c.nmem (F1 + (s * b + t)) = finB X₂ s t ∧
      c.rmem (F1 + (s * b + t)) = (D₂ s t : ℝ))
    (hB₁ : ∀ s < b, ∀ t < b, |(D₁ s t : ℝ)| ≤ B) (hB₂ : ∀ s < b, ∀ t < b, |(D₂ s t : ℝ)| ≤ B)
    (hI : NInv W' B c) (hZ : IntAll c) {c' : Config} {k : ℕ} (e : Exec P W' bfStage c c' k) :
    ExecCmp P W' (2 * bfB b B) bfStage c c' k ∧ NInv W' (bfB b B) c' := by
  have hBB := le_bfB (B := B) hb
  have hWP : bfWP b ≤ W' := by have := hL.1; omega
  obtain ⟨c₉', k₁, k₂, e₁, e₂⟩ := bfStage_split e
  obtain ⟨c₉, k₉, e₉, hR₉, hM₉, hrb₉, hmb₉, hMB₉, -, -, -, -, -, -⟩ :=
    bfPre_start (I := P) hπ hL c hc h802 h970 h971 h972 h974 hπm hF0 hF1 hB₁ hB₂
      (fun r _ => hZ.1 r) (fun a _ => hZ.2 a) (fun a ha => hI.1 a (ha.trans hWP))
  obtain ⟨rfl, rfl⟩ := Exec.det e₉ e₁
  obtain ⟨C₁, hI₉⟩ := glue_cmp bfPre_glueOK e₁ hI
  cases e₂ with | @seq _ _ _ c₁₀ _ k₃ k₄ e₃ e₄ =>
  obtain ⟨C₃, hMB₃, hK₃⟩ := bfFull_cmp_emb (L := B) hπ hD₁ hD₂ (fun s t hs ht => hB₁ s hs t ht)
    (fun s t hs ht => hB₂ s hs t ht) hWP c₉ e₁.wb_right hR₉ hM₉ hrb₉ hmb₉
    (fun a ha => (hMB₉ a ha).trans (by exact_mod_cast hBB)) e₃
  have hI₁₀ : NInv W' (bfB b B) c₁₀ := by
    refine ⟨fun a ha => ?_, fun r h1 h2 => ?_⟩
    · by_cases hab : a ≤ bfWP b
      · exact hMB₃ a hab
      · rw [hK₃.rmem a (by omega)]; exact (hI₉.1 a ha).trans (by exact_mod_cast hBB)
    · rw [hK₃.rreg r (by simp [bfU]; omega)]; exact (hI₉.2 r h1 h2).trans (by exact_mod_cast hBB)
  obtain ⟨C₄, hI'⟩ := glue_cmp bfTail_glueOK e₄ hI₁₀
  obtain ⟨k', E⟩ := bfStage_cmp_join (C₁.mono_H (by omega))
    (.seq (C₃.mono_H (by unfold bfHc; omega)) C₄)
  obtain ⟨-, rfl⟩ := Exec.det E.toExec e
  exact ⟨E, hI'⟩

end NegSSSP

end PlanarFlow
