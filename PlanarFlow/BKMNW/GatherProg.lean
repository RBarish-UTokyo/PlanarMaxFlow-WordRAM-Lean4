module

public import PlanarFlow.BKMNW.TwoGroupsProg

/-!
# Gathering an array through an index array on the machine

`OUT[j] := A[IX[j]]` for `j < m`: the input bridges of the per-piece programs (the hole flags of
the path vertices `HF[j] = VH[PV[j]]` for `rnProg_runsF`, the flags and class numbers of the tails
and heads of the darts `YT[i] = VY[TL[i]]`, `TK[i] = CID[TL[i]]` for `clsProg_clsF`, …) are such
gathers.

Registers: `4470 = m`, `4471 = IXb`, `4472 = Ab`, `4473 = OUTb`; written `4474 = 1`, `4475`
(index), `4476`, `4477` (scratch).

* `gaBody`, **`gaProg`**, `gaBody_exec` (7 steps), **`gaProg_exec`** (`9 m + 4` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- `OUT[j] := A[IX[j]]`. -/
def gaBody : Stmt :=
  block [.addN 4476 4471 4475, .loadN 4476 4476, .addN 4476 4472 4476, .loadN 4476 4476,
    .addN 4477 4473 4475, .storeN 4477 4476, .addN 4475 4475 4474]

/-- **The gather on the machine.** -/
def gaProg : Stmt :=
  .seq (block [.constN 4474 1, .constN 4475 0]) (.whileLtN 4475 4470 gaBody)

section Exec

variable {P : Input} {W : ℕ}

theorem gaBody_exec (c : Config) (hc : WordsBounded W c) {IXb Ab OUTb j : ℕ}
    (r1 : c.nreg 4471 = IXb) (r2 : c.nreg 4472 = Ab) (r3 : c.nreg 4473 = OUTb)
    (r4 : c.nreg 4474 = 1) (r5 : c.nreg 4475 = j) (w1 : IXb + j ≤ W)
    (w2 : Ab + c.nmem (IXb + j) ≤ W) (w3 : OUTb + j ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' k, Exec P W gaBody c c' k ∧ k = 7 ∧ c'.nreg 4475 = j + 1 ∧
      c'.nmem = upd c.nmem (OUTb + j) (c.nmem (Ab + c.nmem (IXb + j))) ∧
      (∀ x, (x < 4475 ∨ 4477 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold gaBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r5]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r4, r5]
  · config_simp; simp only [r1, r2, r3, r4, r5]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The gather**: with the index array `IX[j] = nmem (IXb + j)`, `j < m`, pointing into `A`
(`Ab + IX[j] ≤ W`) and the output `OUT` disjoint from both arrays, within `9 m + 4` steps
`OUT[j] = A[IX[j]]` for `j < m`; memory outside `[OUTb, OUTb + m)`, registers outside
`4474 … 4477`, reals and output kept. -/
theorem gaProg_exec (c : Config) (hc : WordsBounded W c) {m IXb Ab OUTb : ℕ}
    (r0 : c.nreg 4470 = m) (r1 : c.nreg 4471 = IXb) (r2 : c.nreg 4472 = Ab)
    (r3 : c.nreg 4473 = OUTb) (w1 : IXb + m ≤ W) (w3 : OUTb + m ≤ W) (w4 : m + 1 ≤ W)
    (hIX : ∀ j < m, Ab + c.nmem (IXb + j) ≤ W)
    (d1 : ∀ j < m, ¬ (OUTb ≤ IXb + j ∧ IXb + j < OUTb + m))
    (d2 : ∀ j < m, ¬ (OUTb ≤ Ab + c.nmem (IXb + j) ∧ Ab + c.nmem (IXb + j) < OUTb + m)) :
    ∃ c' k, Exec P W gaProg c c' k ∧ k ≤ 9 * m + 4 ∧
      (∀ j < m, c'.nmem (OUTb + j) = c.nmem (Ab + c.nmem (IXb + j))) ∧
      (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4474 ∨ 4477 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold gaProg
  obtain ⟨c₁, k₁, e₁, hk₁, g4, g5, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4474 1, .constN 4475 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 4474 = 1 ∧ c₁.nreg 4475 = 0 ∧
      (∀ x, x ≠ 4474 → x ≠ 4475 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 4474 → x ≠ 4475 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4475 ∨ 4477 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (OUTb + j) = m₀ (Ab + m₀ (IXb + j))) ∧
    (∀ a, ¬ (OUTb ≤ a ∧ a < OUTb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h75, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P) (a := 4475)
    (b := 4470) (body := gaBody) J (B := 7) c₁ hw₁ g5 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h75 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 4475 ∨ 4477 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (IXb + i) = m₀ (IXb + i) :=
        j3 _ (fun h => d1 i hhi ⟨h.1, by omega⟩)
      have e2 : c'.nmem (Ab + m₀ (IXb + i)) = m₀ (Ab + m₀ (IXb + i)) :=
        j3 _ (fun h => d2 i hhi ⟨h.1, by omega⟩)
      obtain ⟨c'', t, ex, ht, h75', hm', hn', hr', hrm', ho'⟩ := gaBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), g4]) h75 (by omega) (by rw [e1]; exact hIX i hhi) (by omega)
        (by omega)
      rw [e1, e2] at hm'
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

end Exec

end BKMNW

end PlanarFlow
