module

public import PlanarFlow.Machine.BF

/-!
# Feasible flows in plane graphs on the machine: the main theorem

**`PlanarFlow.Feas.feas_runsWithin`.** On a well-formed input describing a plane map with `V`
vertices, `F` faces and `S` darts, capacities on the darts and supplies and demands at the
vertices, the program `PlanarFlow.Feas.prog` halts within `26 (S + 2)(V + F + 2)` steps and
outputs a single word, `1` if a flow meeting the supplies and demands within the capacities
exists and `0` otherwise.

For a plane graph without loops and parallel edges with `n ≥ 3` vertices there are at most
`3n - 6` edges (`S ≤ 6n`) and at most `2n - 4` faces, so the bound is `O(n²)`.

The proof composes the phases: the search finds a spanning tree, the base flow `g` along it
has the prescribed net flow at every vertex when the supplies and demands balance, and by the
theorem of Miller–Naor (`PlanarFlow.CombMap.bflow_iff_potential`) a flow exists exactly when they
balance and the dual graph with lengths `cp - g` has a feasible potential, which the
Bellman–Ford rounds find (`PlanarFlow.Digraph.isPot_bf_card`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Feas

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

variable {d : List ℕ} {W : ℕ}

/-! ### From the memory to the map -/

lemma div_map (he : Enc d W) (g : ℕ → ℤ) (v : Fin (nv d)) :
    (map he.wf).div (fun j => g j) v = dv d g v := by
  unfold CombMap.div dv
  rw [sum_filter, sum_filter]
  rw [← Fin.sum_univ_eq_sum_range (fun j => if tl d j = v then g j else 0)]
  refine sum_congr rfl fun j _ => ?_
  simp only [map, Fin.ext_iff]

lemma antisymm_map (he : Enc d W) {g : ℕ → ℤ} (hg : ∀ j < nd d, g (rv d j) = - g j) :
    (map he.wf).IsAntisymm (fun j => g j) := fun j => hg j j.2

lemma sum_bvec (d : List ℕ) : ∑ v, bvec d v = ∑ v ∈ range (nv d), bb d v :=
  Fin.sum_univ_eq_sum_range (fun v => bb d v) _

lemma potential_iff (he : Enc d W) (m : ℕ → ℕ) (φ : Fin (nf d) → ℤ) :
    (map he.wf).IsPotential (ucap d - fun j : Fin (nd d) => sv d m j) φ ↔ (dual he m).IsPot φ := by
  unfold CombMap.IsPotential Digraph.IsPot
  refine forall_congr' fun j => ?_
  simp only [CombMap.cob, map, dual, ucap, Pi.sub_apply]
  constructor <;> intro h <;> linarith

/-! ### Reassociating sequences -/

theorem Exec.seq_assoc {P : Input} {a b t : Stmt} {c c₁ c₂ : Config} {k₁ k₂ : ℕ}
    (h : Exec P W (.seq a b) c c₁ k₁) (h' : Exec P W t c₁ c₂ k₂) :
    Exec P W (.seq a (.seq b t)) c c₂ (k₁ + k₂) := by
  cases h with
  | seq e₁ e₂ => exact (Exec.seq e₁ (Exec.seq e₂ h')).cast (by omega)

theorem Exec.seq_assoc3 {P : Input} {a b c' t : Stmt} {c c₁ c₂ : Config} {k₁ k₂ : ℕ}
    (h : Exec P W (.seq a (.seq b c')) c c₁ k₁) (h' : Exec P W t c₁ c₂ k₂) :
    Exec P W (.seq a (.seq b (.seq c' t))) c c₂ (k₁ + k₂) := by
  cases h with
  | seq e₁ e₂ =>
    cases e₂ with
    | seq e₂ e₃ => exact (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ h'))).cast (by omega)

/-! ### The whole program -/

theorem feas_exec (he : Enc d W) :
    ∃ c' k ans, Exec (inp d) W prog initConfig c' k ∧ c'.output = [ans] ∧ ans ≤ 1 ∧
      (ans = 1 ↔ Feasible he.wf) ∧ k + 1 ≤ 26 * (nd d + 2) * (nv d + nf d + 2) := by
  -- the constants
  obtain ⟨c₁, k₁, e₁, hw₁, hR₁, hm₁, ho₁, hk₁⟩ := bsum_exec he
  -- the search
  obtain ⟨c₂, k₂, e₂, hw₂, hR₂, ho₂, hT, h25, hk₂⟩ := reach_exec he c₁ hw₁ hR₁ hm₁ ho₁
  have a0 : c₂.nreg 0 = 0 := hR₂.1.1
  -- the base flow
  have e₃ := Exec.copyN (P := inp d) hw₂ 20 0
  obtain ⟨c₄, k₄, e₄, hw₄, hR₄, ho₄, hg₄, hf₄, hk₄⟩ := gloop_exec he _ e₃.wb_right
    (regs_of hR₂ fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]) ho₂
    (by config_simp; exact a0)
  have e₅ := Exec.copyN (P := inp d) hw₄ 20 0
  have b0 : c₄.nreg 0 = 0 := hR₄.1.1
  obtain ⟨c₆, k₆, e₆, hw₆, hR₆, ho₆, hx₆, hf₆, hk₆⟩ := xloop_exec he _ e₅.wb_right
    (regs_of hR₄ fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]) ho₄
    (by config_simp; exact b0)
  have e₇ := Exec.copyN (P := inp d) hw₆ 29 2
  have hIT : IT d W c₂.nmem { c₆ with nreg := upd c₆.nreg 29 (c₆.nreg 2) } := by
    refine IT.start he hT e₇.wb_right (regs_of hR₆ fun r hr => by
      config_simp; rw [upd_other _ _ _ (by omega)]) ho₆ (by config_simp; exact hR₆.1.2.2.1)
      (fun a h1 h2 => ?_) (fun j hj => ?_) hx₆
    · rw [hf₆ a h2]; exact hf₄ a h1
    · rw [hf₆ j (by omega)]; exact hg₄ j hj
  obtain ⟨c₈, k₈, e₈, hI₈, h29, hk₈⟩ := tloop_exec he hT _ hIT
  obtain ⟨hroot, hdone⟩ := IT.result he hT hI₈ h29
  -- the root check
  obtain ⟨c₉, k₉, e₉, hw₉, hK₉, hm₉, ho₉, h32₉, h32le, hk₉⟩ := rootCheck_exec c₈ hI₈.wb hI₈.regs
  have hR₉ := regs_of hI₈.regs hK₉
  have e₁₀ := Exec.copyN (P := inp d) hw₉ 20 0
  have hg : ∀ j < nd d, |sv d c₉.nmem j| ≤ bsum d := fun j hj => by rw [hm₉]; exact hI₈.gbd j hj
  -- Bellman–Ford
  obtain ⟨c₁₁, k₁₁, c₁₂, c₁₃, k₁₃, e₁₁, e₁₂, e₁₃, hw₁₃, hR₁₃, ho₁₃, h32₁₃, hfr, hub, hlb, hpot,
    hk₁₁, hk₁₃⟩ := rounds_exec he hg _ e₁₀.wb_right
      (regs_of hR₉ fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)])
      (by config_simp; exact ho₉.trans hI₈.out) rfl (by config_simp; exact hR₉.1.1)
  have e₁₄ := Exec.copyN (P := inp d) hw₁₃ 20 0
  obtain ⟨c₁₅, k₁₅, e₁₅, hw₁₅, hR₁₅, ho₁₅, h32le', h32', hk₁₅⟩ := check_exec he hg
    (m₃ := c₁₃.nmem) hfr (fun f hf => hub f hf) hlb _ e₁₄.wb_right
    (regs_of hR₁₃ fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)])
    (by config_simp; exact ho₁₃) rfl (by config_simp; exact hR₁₃.1.1)
    (by config_simp; rw [h32₁₃]; config_simp; exact h32le)
  have e₁₆ := Exec.outN (P := inp d) hw₁₅ 32
  -- the program
  have e : Exec (inp d) W prog initConfig _ _ :=
    Exec.seq_assoc3 e₁ (Exec.seq_assoc e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈
      (.seq e₉ (.seq e₁₀ (.seq e₁₁ (.seq e₁₂ (.seq e₁₃ (.seq e₁₄ (.seq e₁₅ e₁₆))))))))))))))
  refine ⟨_, _, c₁₅.nreg 32, e, by config_simp; rw [ho₁₅]; rfl, h32le', ?_, ?_⟩
  · -- correctness
    have hok : ({ c₉ with nreg := upd c₉.nreg 20 (c₉.nreg 0) } : Config).nreg 32 = c₉.nreg 32 := by
      config_simp
    have hok' : ({ c₁₃ with nreg := upd c₁₃.nreg 20 (c₁₃.nreg 0) } : Config).nreg 32 =
        c₁₃.nreg 32 := by config_simp
    rw [h32', hok', h32₁₃, hok, h32₉, hroot]
    have hanti := antisymm_map he (g := sv d c₉.nmem) (fun j hj => by rw [hm₉]; exact hI₈.anti j hj)
    constructor
    · rintro ⟨hb, hP⟩
      have hdiv : ∀ v : Fin (nv d), (map he.wf).div (fun j => sv d c₉.nmem j) v = bvec d v := by
        intro v
        rw [div_map he, hm₉]
        by_cases hv0 : (v : ℕ) = 0
        · have h0 := hI₈.todo 0 (by rw [h29]; omega)
          rw [hT.od0, hroot, hb] at h0
          rw [hv0]; unfold bvec; rw [hv0]; unfold bb at h0; linarith
        · exact hdone v v.2 hv0
      exact (CombMap.bflow_iff_potential he.plane (ucap d) hanti hdiv).2
        ⟨evf d c₁₃.nmem, (potential_iff he _ _).2 hP⟩
    · intro hF
      obtain ⟨f, hf⟩ := hF
      have hb : ∑ v ∈ range (nv d), bb d v = 0 := by
        rw [← sum_bvec]; exact CombMap.sum_eq_zero_of_bflow hf
      refine ⟨hb, hpot ?_⟩
      have hdiv : ∀ v : Fin (nv d), (map he.wf).div (fun j => sv d c₉.nmem j) v = bvec d v := by
        intro v
        rw [div_map he, hm₉]
        by_cases hv0 : (v : ℕ) = 0
        · have h0 := hI₈.todo 0 (by rw [h29]; omega)
          rw [hT.od0, hroot, hb] at h0
          rw [hv0]; unfold bvec; rw [hv0]; unfold bb at h0; linarith
        · exact hdone v v.2 hv0
      obtain ⟨φ, hφ⟩ := (CombMap.bflow_iff_potential he.plane (ucap d) hanti hdiv).1 ⟨f, hf⟩
      exact ⟨φ, (potential_iff he _ _).1 hφ⟩
  · -- the cost
    have hk : k₁ + k₂ + 1 + k₄ + 1 + k₆ + 1 + k₈ + k₉ + 1 + k₁₁ + 1 + k₁₃ + 1 + k₁₅ + 1 + 1 ≤
        26 * (nd d + 2) * (nv d + nf d + 2) := by
      nlinarith
    omega

/-- **Feasibility of supplies and demands in a plane graph, on the machine.** On a well-formed
input with `V` vertices, `F` faces and `S` darts, the program halts within
`26 (S + 2)(V + F + 2)` steps, every word along the run bounded by `W`, and prints one word: `1`
if there is a flow meeting the supplies and demands within the capacities, `0` otherwise. -/
theorem feas_runsWithin (he : Enc d W) :
    ∃ ans, ans ≤ 1 ∧ (ans = 1 ↔ Feasible he.wf) ∧
      RunsWithin (compile prog 0 ++ [Instr.halt]) (inp d) W
        (26 * (nd d + 2) * (nv d + nf d + 2)) [ans] := by
  obtain ⟨c', k, ans, e, hout, hle, hiff, hk⟩ := feas_exec he
  obtain ⟨k', hk', h1, h2⟩ := runsWithin_of_exec_output e hout
  exact ⟨ans, hle, hiff, k', by omega, h1, h2⟩

end Feas

end PlanarFlow
