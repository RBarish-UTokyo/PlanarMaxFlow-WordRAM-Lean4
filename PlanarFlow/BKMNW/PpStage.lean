module

public import PlanarFlow.BKMNW.PpRead

/-!
# Stages of the preprocessing: arrays at offsets of a base

The preprocessing keeps its arrays at `B + k n` (`B = r8730`, `n = r8700`). A **stage**
`stageM k vb` sets the output base `r8742 := B + k n` and runs the map loop `mapL vb`.

* `setB r k`, `setB_exec`: `r := B + k n`;
* `wscr`: the registers a stage may write;
* **`stageM_exec`**: the stage writes `g j` at `B + k n + j` (`j < r8741`), keeps the memory
  elsewhere and the registers off `wscr`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv

variable {P : Input} {W : ℕ}

/-- The registers a stage may write. -/
def wscr (x : ℕ) : Prop := pscr x ∨ x = 8738 ∨ x = 8740 ∨ x = 8742 ∨ x = 8743

/-- `r := B + k n`. -/
def setB (r k : ℕ) : Stmt := block [.constN 8778 k, .mulN 8778 8700 8778, .addN r 8778 8730]

theorem setB_exec (c : Config) (hc : WordsBounded W c) {r k n B : ℕ} (hr : r ≠ 8778)
    (r00 : c.nreg 8700 = n) (r30 : c.nreg 8730 = B) (w : B + k * n + k ≤ W) :
    ∃ c' t, Exec P W (setB r k) c c' t ∧ t = 3 ∧ c'.nreg r = B + k * n ∧
      (∀ x, x ≠ r → x ≠ 8778 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hkn : n * k = k * n := Nat.mul_comm _ _
  unfold setB
  exec_block
  · omega
  · config_simp; rw [r00, hkn]; omega
  · config_simp; rw [r00, r30, hkn]; omega
  refine ⟨rfl, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [r00, r30, hkn]; omega
  · config_simp; simp (disch := omega) only [upd_other]

/-- **A stage**: the output base `B + k n`, then the map loop. -/
def stageM (k : ℕ) (vb : Stmt) : Stmt := .seq (setB 8742 k) (mapL vb)

theorem stageM_exec (c : Config) (hc : WordsBounded W c) {vb : Stmt} {n B k m B' : ℕ}
    (g : ℕ → ℕ) (r00 : c.nreg 8700 = n) (r30 : c.nreg 8730 = B) (r41 : c.nreg 8741 = m)
    (r04 : c.nreg 8704 = 1) (w1 : B + k * n + m + k ≤ W) (w2 : m + 1 ≤ W)
    (hvb : ∀ i < m, ∀ c' : Config, WordsBounded W c' → c'.nreg 8740 = i →
      (∀ x, ¬ wscr x → c'.nreg x = c.nreg x) →
      (∀ a, ¬ (B + k * n ≤ a ∧ a < B + k * n + m) → c'.nmem a = c.nmem a) →
      ∃ c'' t, Exec P W vb c' c'' t ∧ VBPost c' (g i) B' c'' t) :
    ∃ c' t, Exec P W (stageM k vb) c c' t ∧ t ≤ (B' + 5) * m + 6 ∧
      (∀ j < m, c'.nmem (B + k * n + j) = g j) ∧
      (∀ a, ¬ (B + k * n ≤ a ∧ a < B + k * n + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ wscr x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, v1, n1, m1, rr1, rm1, o1⟩ := setB_exec (P := P) (r := 8742) (k := k)
    c hc (by omega) r00 r30 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, j1, j2, j3, j4, j5, j6⟩ := mapL_exec (P := P) c₁ e₁.wb_right (vb := vb)
    (m := m) (Ob := B + k * n) (B := B') g (by rw [n1 _ (by omega) (by omega)]; exact r41)
    (by rw [n1 _ (by omega) (by omega)]; exact r04) v1 (by omega) w2
    (fun i hi c' hw h40 hr hm => hvb i hi c' hw h40 (fun x hx => by
      unfold wscr pscr at hx
      rw [hr x (by unfold pscr; omega) (by omega) (by omega), n1 x (by omega) (by omega)])
      (fun a ha => by rw [hm a ha, m1]))
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega, j1, fun a ha => by rw [j2 a ha, m1],
    fun x hx => ?_, by rw [j4, rr1], by rw [j5, rm1], by rw [j6, o1]⟩
  unfold wscr pscr at hx
  rw [j3 x (by unfold pscr; omega) (by omega) (by omega), n1 x (by omega) (by omega)]

end Pp

end BKMNW

end PlanarFlow
