module

public import PlanarFlow.BKMNW.NsCall
public import PlanarFlow.NegSSSP.KEncLay

/-!
# The map part of the s-t flow encoding: an array loop

The input of the s-t flow program (`PlanarFlow.STFlow.pcore_exec`) holds Klein's encoding
`Klein.KInput` of the **dual** of the map on which the flow is computed, for a layout of the nodes
(`Klein.Layout`). The node of a vertex of the dual (a face of the map) and the node of a face of the
dual (a vertex of the map) are orbit labels (`PlanarFlow.BKMNW.OrbLab.olProg`) shifted by
constants. This file has the loop adding a constant to an array:

* **`laProg`** (`OUT[i] := A[i] + K`, `i < m`; registers `7730 = m`, `7731 = Ab`, `7732 = OUTb`,
  `7733 = K`; scratch `7734 … 7737`), **`laProg_exec`** (`8 m + 4` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- `OUT[i] := A[i] + K`; then `i := i + 1`. -/
def laBody : Stmt :=
  block [.addN 7736 7731 7735, .loadN 7736 7736, .addN 7736 7736 7733, .addN 7737 7732 7735,
    .storeN 7737 7736, .addN 7735 7735 7734]

/-- **The shifted copy** `OUT[i] := A[i] + K`, `i < m`. -/
def laProg : Stmt :=
  .seq (block [.constN 7734 1, .constN 7735 0]) (.whileLtN 7735 7730 laBody)

theorem laBody_exec (c : Config) (hc : WordsBounded W c) {Ab OUTb K j : ℕ}
    (r1 : c.nreg 7731 = Ab) (r2 : c.nreg 7732 = OUTb) (r3 : c.nreg 7733 = K)
    (r4 : c.nreg 7734 = 1) (r5 : c.nreg 7735 = j) (w1 : Ab + j ≤ W)
    (w2 : c.nmem (Ab + j) + K ≤ W) (w3 : OUTb + j ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' k, Exec P W laBody c c' k ∧ k = 6 ∧ c'.nreg 7735 = j + 1 ∧
      c'.nmem = upd c.nmem (OUTb + j) (c.nmem (Ab + j) + K) ∧
      (∀ x, (x < 7735 ∨ 7737 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold laBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r4, r5]
  · config_simp; simp only [r1, r2, r3, r4, r5]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The shifted copy**: within `8 m + 4` steps `OUT[i] = A[i] + K` for `i < m`; memory outside
`[OUTb, OUTb + m)`, registers outside `7734 … 7737`, reals and output kept (the arrays
disjoint). -/
theorem laProg_exec (c : Config) (hc : WordsBounded W c) {m Ab OUTb K : ℕ}
    (r0 : c.nreg 7730 = m) (r1 : c.nreg 7731 = Ab) (r2 : c.nreg 7732 = OUTb)
    (r3 : c.nreg 7733 = K) (w1 : Ab + m ≤ W) (w3 : OUTb + m ≤ W) (w4 : m + 1 ≤ W)
    (hA : ∀ j < m, c.nmem (Ab + j) + K ≤ W) (dj : Ab + m ≤ OUTb ∨ OUTb + m ≤ Ab) :
    ∃ c' k, Exec P W laProg c c' k ∧ k ≤ 8 * m + 4 ∧
      (∀ j < m, c'.nmem (OUTb + j) = c.nmem (Ab + j) + K) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 7734 ∨ 7737 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold laProg
  obtain ⟨c₁, k₁, e₁, hk₁, g4, g5, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 7734 1, .constN 7735 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 7734 = 1 ∧ c₁.nreg 7735 = 0 ∧
      (∀ x, x ≠ 7734 → x ≠ 7735 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 7734 → x ≠ 7735 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 7735 ∨ 7737 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (OUTb + j) = m₀ (Ab + j) + K) ∧
    (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h75, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 7735)
    (b := 7730) (body := laBody) J (B := 6) c₁ hw₁ g5 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h75 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 7735 ∨ 7737 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (Ab + i) = m₀ (Ab + i) := j3 _ (fun h => by omega)
      obtain ⟨c'', t, ex, ht, h75', hm', hn', hr', hrm', ho'⟩ := laBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), g4]) h75 (by omega) (by rw [e1]; exact hA i hhi) (by omega)
        (by omega)
      rw [e1] at hm'
      refine ⟨c'', t, ex, ht.le, h75', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha ⟨h.1, by omega⟩))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

end StEnc

end BKMNW

end PlanarFlow
