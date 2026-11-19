module

public import PlanarFlow.NegSSSP.Enc.StoreLog

/-!
# Restoring the logged cells from a shadow copy

`NegSSSP.lgClr` clears the cells named in a store log (`lgS`), which restores a memory that was
zero there. To run a logged program **on a resident input** (FR-Dijkstra on the dense distance
graph kept in the low memory across the stages of FixConservationOnPath, instead of copying it
in and clearing it at every stage), the logged cells must get back their old values. Here they
are read from a **shadow copy** at `SH`: **`lgRst`** sets `mem[a] := mem[SH + a]` for every
logged address `a` (`p = r2924`, `LP = r2925`, `ONE = r2926`, `SH = r9300`; scratch `2923`,
`2927`, `2928`, `9301`).

**`lgRst_exec`**: within `8 j + 4` steps, every logged cell holds its shadow value, every other
cell is kept (the log entries are `≤ Ws < p` and `Ws < SH`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

/-- The body of the restoring loop: `mem[mem[p + i]] := mem[SH + mem[p + i]]`, `i := i + 1`. -/
def lgRstBody : Stmt :=
  block [.addN 2928 2924 2927, .loadN 2928 2928, .addN 9301 9300 2928, .loadN 9301 9301,
    .storeN 2928 9301, .addN 2927 2927 2926]

/-- **Restore the logged cells from the shadow at `SH = r9300`.** -/
def lgRst : Stmt :=
  .seq (block [.constN 2927 0, .subN 2923 2925 2924]) (.whileLtN 2927 2923 lgRstBody)

theorem lgRst_natOnly : Klein.natOnly lgRst = true := by decide

variable {P : Input} {W : ℕ}

/-- **The restoring loop.** -/
theorem lgRst_exec (c : Config) (hc : WordsBounded W c) {p j Ws SH : ℕ}
    (r24 : c.nreg 2924 = p) (r25 : c.nreg 2925 = p + j) (r26 : c.nreg 2926 = 1)
    (r00 : c.nreg 9300 = SH)
    (hlog : ∀ i < j, c.nmem (p + i) ≤ Ws) (hp : Ws < p) (hSH : Ws < SH) (hSHW : SH + Ws ≤ W) :
    ∃ c' t, Exec P W lgRst c c' t ∧ t ≤ 8 * j + 4 ∧
      (∀ a, (∃ i < j, c.nmem (p + i) = a) → c'.nmem a = c.nmem (SH + a)) ∧
      (∀ a, (∀ i < j, c.nmem (p + i) ≠ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2923 → r ≠ 2927 → r ≠ 2928 → r ≠ 9301 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hpW : p + j ≤ W := r25 ▸ WordsBounded.nreg hc 2925
  obtain ⟨c₁, k₁, e₁, hk₁, g27, g23, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2927 0, .subN 2923 2925 2924]) c c₁ k₁ ∧
      k₁ = 2 ∧ c₁.nreg 2927 = 0 ∧ c₁.nreg 2923 = j ∧
      (∀ r, r ≠ 2923 → r ≠ 2927 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try (simp only [r24, r25]; omega)
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ a, (∃ i' < i, c.nmem (p + i') = a) → c'.nmem a = c.nmem (SH + a)) ∧
      (∀ a, (∀ i' < i, c.nmem (p + i') ≠ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 2927 → r ≠ 2928 → r ≠ 9301 → c'.nreg r = c₁.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2927) (bR := 2923)
    (body := lgRstBody) J (K := 6) (n := j) c₁ e₁.wb_right g27 g23
    ⟨fun a ⟨i, hi, _⟩ => absurd hi (by omega), fun a _ => by rw [gm₁], fun _ _ _ _ => rfl,
      gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
      have q24 : c'.nreg 2924 = p := by
        rw [jn _ (by omega) (by omega) (by omega), gn₁ _ (by omega) (by omega)]; exact r24
      have q26 : c'.nreg 2926 = 1 := by
        rw [jn _ (by omega) (by omega) (by omega), gn₁ _ (by omega) (by omega)]; exact r26
      have q00 : c'.nreg 9300 = SH := by
        rw [jn _ (by omega) (by omega) (by omega), gn₁ _ (by omega) (by omega)]; exact r00
      have hlogi : c'.nmem (p + i) = c.nmem (p + i) := j2 _ fun i' hi' e => by
        have := hlog i' (by omega); omega
      have hai : c.nmem (p + i) ≤ Ws := hlog i hi
      have hshi : c'.nmem (SH + c.nmem (p + i)) = c.nmem (SH + c.nmem (p + i)) :=
        j2 _ fun i' hi' e => by have := hlog i' (by omega); omega
      obtain ⟨c'', t, ex, ht, hm, h27, hn, hr, hrm, ho⟩ : ∃ c'' t,
          Exec P W lgRstBody c' c'' t ∧ t = 6 ∧
          c''.nmem = upd c'.nmem (c.nmem (p + i)) (c.nmem (SH + c.nmem (p + i))) ∧
          c''.nreg 2927 = i + 1 ∧
          (∀ r, r ≠ 2927 → r ≠ 2928 → r ≠ 9301 → c''.nreg r = c'.nreg r) ∧
          c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output := by
        unfold lgRstBody
        have hw1 := hw.2 (SH + c.nmem (p + i))
        rw [hshi] at hw1
        exec_block
        all_goals try ((try config_simp); (try simp only [q24, q26, q00, ha, hlogi]); omega)
        refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try (simp only [q24, q26, q00, ha, hlogi, hshi])
        all_goals try omega
        simp only [upd_apply]; split_ifs <;> omega
      refine ⟨c'', t, ex, by omega, h27, (hn _ (by omega) (by omega) (by omega)).trans hb,
        fun a ha' => ?_, fun a ha' => ?_,
        fun r h1 h2 h3 => (hn r h1 h2 h3).trans (jn r h1 h2 h3), by rw [hr, jr],
        by rw [hrm, jrm], by rw [ho, jo]⟩
      · obtain ⟨i', hi', rfl⟩ := ha'
        rw [hm, upd_apply]
        split_ifs with h
        · rw [h]
        · exact j1 _ ⟨i', by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h' | h'
            · exact h'
            · subst h'; exact absurd rfl h, rfl⟩
      · rw [hm, upd_other _ _ _ (fun e => ha' i (by omega) e.symm)]
        exact j2 a fun i' hi' => ha' i' (by omega))
  obtain ⟨j1, j2, jn, jr, jrm, jo⟩ := hJ
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j1, j2, fun r h1 h2 h3 h4 => ?_, jr, jrm, jo⟩
  rw [jn r h2 h3 h4, gn₁ r h1 h2]

end BKMNW

end PlanarFlow
