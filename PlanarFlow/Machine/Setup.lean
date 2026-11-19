module

public import PlanarFlow.Machine.Enc

/-!
# Feasibility on the machine: the constants and the offset

The setup block, the sum `B` of the supplies and demands, and the offset `Z = (F S + 1)(B + 1)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Feas

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

variable {d : List ℕ} {W : ℕ}

lemma zz_ge (d : List ℕ) : bsum d + 1 ≤ zz d := by
  unfold zz; exact Nat.le_mul_of_pos_left _ (by omega)

lemma nf_nd_le (d : List ℕ) : nf d * nd d + 1 ≤ zz d := by
  unfold zz; exact Nat.le_mul_of_pos_right _ (by omega)

lemma bp_le_bsum {v : ℕ} (hv : v < nv d) : bp d v + bn d v ≤ bsum d := by
  unfold bsum
  exact single_le_sum (f := fun v => bp d v + bn d v) (fun _ _ => Nat.zero_le _)
    (mem_range.2 hv)

theorem setup_exec (he : Enc d W) :
    ∃ c' k, Exec (inp d) W setup initConfig c' k ∧ WordsBounded W c' ∧ Regs0 d c' ∧
      c'.nreg 20 = 0 ∧ c'.nreg 21 = 0 ∧ c'.nmem = (fun _ => 0) ∧ c'.output = [] ∧ k = 15 := by
  have hs := he.size
  have hw : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  unfold setup
  exec_block
  · omega
  · exact he.word_le _
  · exact he.word_le _
  · omega
  · exact he.word_le _
  · omega
  · omega
  · config_simp; simp only [initConfig, inp]; unfold nv nd word at hs; omega
  · config_simp; simp only [initConfig, inp]; unfold nv nd word at hs; omega
  · config_simp; simp only [initConfig, inp]; unfold nv nd word at hs; omega
  · config_simp; simp only [initConfig, inp]; unfold nv nd word at hs; omega
  · config_simp; simp only [inp]; unfold nd word at hs; omega
  · config_simp; simp only [inp]; unfold nd word at hs; omega
  refine ⟨‹_›, ?_, by config_simp; rfl, by config_simp; rfl, by config_simp; rfl,
    by config_simp; rfl, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
    simp [initConfig, inp, nv, nf, nd, word] <;> omega

/-- The state of the sum of the supplies and demands. -/
structure IS (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs0 d c
  r20 : c.nreg 20 ≤ nv d
  r21 : c.nreg 21 = ∑ v ∈ range (c.nreg 20), (bp d v + bn d v)
  mem : c.nmem = fun _ => 0
  out : c.output = []

theorem bsumStep_exec (he : Enc d W) (c : Config) (hI : IS d W c) (hlt : c.nreg 20 < c.nreg 2) :
    ∃ c' k, Exec (inp d) W bsumStep c c' k ∧ IS d W c' ∧
      (nv d - c'.nreg 20) * 10 + k + 2 ≤ (nv d - c.nreg 20) * 10 := by
  have hc := hI.wb
  have hs := he.size
  have hb := he.big
  obtain ⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩ := hI.regs
  rw [h2] at hlt
  have hle := bp_le_bsum (d := d) hlt
  have hpart : ∑ v ∈ range (c.nreg 20 + 1), (bp d v + bn d v) ≤ bsum d :=
    sum_le_sum_of_subset (range_subset_range.2 (by omega))
  rw [sum_range_succ] at hpart
  have hr21 := hI.r21
  have e1 : word d (c.nreg 20 * 2 + (nd d * 5 + 3)) = bp d (c.nreg 20) := rfl
  have e2 : word d (c.nreg 20 * 2 + (nd d * 5 + 3) + 1) = bn d (c.nreg 20) := rfl
  unfold bsumStep
  exec_block
  · config_simp; rw [h12]; omega
  · config_simp; rw [h12, h11]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [hr21, word_inp, h12, h11, e1]; omega
  · config_simp; rw [h12, h11, h1]; omega
  · config_simp; exact he.word_le _
  · config_simp; rw [hr21, word_inp, word_inp, h12, h11, h1, e1, e2]; omega
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, regs0_of hI.regs fun r hr _ => ?_, by config_simp; rw [h1]; omega, ?_,
    by config_simp; exact hI.mem, by config_simp; exact hI.out⟩, by config_simp; rw [h1]; omega⟩
  · config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
  · config_simp
    simp only [h1, h11, h12, word_inp]
    rw [sum_range_succ, hr21, e1, e2]
    omega

theorem bsum_exec (he : Enc d W) :
    ∃ c' k, Exec (inp d) W (.seq setup (.seq (.whileLtN 20 2 bsumStep) zset)) initConfig c' k ∧
      WordsBounded W c' ∧ Regs d c' ∧ c'.nmem = (fun _ => 0) ∧ c'.output = [] ∧
      k ≤ 10 * nv d + 21 := by
  obtain ⟨c₁, k₁, e₁, hw₁, hR₁, h20, h21, hm₁, ho₁, rfl⟩ := setup_exec he
  have hI : IS d W c₁ := ⟨hw₁, hR₁, by omega, by rw [h21, h20]; simp, hm₁, ho₁⟩
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 20)
    (b := 2) (body := bsumStep) (IS d W) (fun c => (nv d - c.nreg 20) * 10) (fun c h => h.wb)
    (fun c hc hlt => bsumStep_exec he c hc hlt) hI
  obtain ⟨h0, h1, h2, h3, h4, h5, h7, h8, h9, h10, h11, h12, h13⟩ := hI₂.regs
  have h20₂ : c₂.nreg 20 = nv d := by have := hI₂.r20; rw [h2] at hn₂; omega
  have hB : c₂.nreg 21 = bsum d := by rw [hI₂.r21, h20₂]; rfl
  have hc := hI₂.wb
  have hz1 := nf_nd_le d
  have hz2 := zz_ge d
  have hb := he.big
  obtain ⟨c₃, k₃, e₃, hw₃, hpost⟩ : ∃ c₃ k₃, Exec (inp d) W zset c₂ c₃ k₃ ∧ WordsBounded W c₃ ∧
      (Regs d c₃ ∧ c₃.nmem = (fun _ => 0) ∧ c₃.output = [] ∧ k₃ = 4) := by
    unfold zset
    exec_block
    · config_simp; rw [h3, h4]; omega
    · config_simp; rw [h3, h4, h1]; omega
    · config_simp; rw [hB, h1]; omega
    · config_simp; rw [h3, h4, h1, hB]; unfold zz at hb; omega
    refine ⟨‹_›, ⟨regs0_of hI₂.regs fun r hr h6 => ?_, ?_⟩, by config_simp; exact hI₂.mem,
      by config_simp; exact hI₂.out, rfl⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
    · config_simp; rw [h3, h4, h1, hB]; rfl
  obtain ⟨hR₃, hm₃, ho₃, rfl⟩ := hpost
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), hw₃, hR₃, hm₃, ho₃, ?_⟩
  beta_reduce at hk₂
  have := Nat.sub_le (nv d) (c₁.nreg 20)
  omega

end Feas

end PlanarFlow
