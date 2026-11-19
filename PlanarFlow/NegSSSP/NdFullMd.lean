module

public import PlanarFlow.NegSSSP.NdFullC2b

/-!
# The full branch: the positions reduced modulo `k`

`fbC1` gathers the positions of the sources through `J` for every node vertex `v < w`; for the
vertices off the boundary the gathered words are arbitrary (read from the room above the heap
top, which holds arbitrary words). The node needs every cell below its word bound `WN` to be at
most `WN` (`hdm`, `hmW` of `fs_node`), so the positions are reduced modulo `k` (the boundary
positions are `< C.k ≤ k`, hence unchanged):

* **`mdProg`** `= block [r2115 := r2315 + 16 r2316, r2114 := 2 r2464, …] ; while (i < n)
  OUT[i] := OUT[i] % r2475` (scratch `2114 … 2119`);
* **`mdProg_exec`**: within `5 + 7 (2w) + 2` steps, `OUT[i] = old % k` for `i < 2w`
  (`OUT = Y + 16S`), every other cell, every register outside `2114 … 2119`, reals, output kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The body: `OUT[i] := OUT[i] % r2475`. -/
def mdBody : Stmt :=
  block [.addN 2118 2115 2116, .loadN 2119 2118, .modN 2119 2119 2475, .storeN 2118 2119,
    .addN 2116 2116 2117]

/-- **The positions modulo `k`** (see the module docstring). -/
def mdProg : Stmt :=
  .seq (block [.constN 2119 16, .mulN 2115 2119 2316, .addN 2115 2115 2315, .addN 2114 2464 2464,
    .constN 2116 0, .constN 2117 1]) (.whileLtN 2116 2114 mdBody)

theorem mdProg_natOnly : Klein.natOnly mdProg = true := by kernel_rfl

theorem mdProg_exec {w Y S k : ℕ} (c : Config) (hc : WordsBounded W c) (r64 : c.nreg 2464 = w)
    (r15 : c.nreg 2315 = Y) (r16 : c.nreg 2316 = S) (r75 : c.nreg 2475 = k)
    (hW : Y + 16 * S + 2 * w ≤ W) (h16 : 16 ≤ W) :
    ∃ c' t, Exec P W mdProg c c' t ∧ t ≤ 14 * w + 8 ∧
      (∀ i < 2 * w, c'.nmem (Y + 16 * S + i) = c.nmem (Y + 16 * S + i) % k) ∧
      (∀ a, (a < Y + 16 * S ∨ Y + 16 * S + 2 * w ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2114 ∨ 2119 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mdProg
  obtain ⟨c₁, k₁, e₁, hk₁, g14, g15, g16, g17, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2119 16, .mulN 2115 2119 2316, .addN 2115 2115 2315,
        .addN 2114 2464 2464, .constN 2116 0, .constN 2117 1]) c c₁ k₁ ∧ k₁ = 6 ∧
      c₁.nreg 2114 = 2 * w ∧ c₁.nreg 2115 = Y + 16 * S ∧ c₁.nreg 2116 = 0 ∧
      c₁.nreg 2117 = 1 ∧
      (∀ r, (r < 2114 ∨ 2119 < r) → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); (try simp only [r64, r15, r16]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals try simp only [r64, r15, r16]
    all_goals try (simp (disch := omega) only [upd_other])
    all_goals try ring
    all_goals try omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Y + 16 * S + e) = c.nmem (Y + 16 * S + e) % k) ∧
      (∀ a, (a < Y + 16 * S ∨ Y + 16 * S + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2114 ∨ 2119 < r) → c'.nreg r = c.nreg r) ∧ c'.nreg 2117 = 1 ∧
      c'.nreg 2115 = Y + 16 * S ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2116) (bR := 2114)
    (body := mdBody) J (K := 5) (n := 2 * w) c₁ e₁.wb_right g16 g14
    ⟨fun e he => absurd he (by omega), fun a _ => by rw [gm₁], fun r hr => gn₁ r hr, g17, g15,
      gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j17, j15, jr, jrm, jo⟩ := hJ
      have j75 : c'.nreg 2475 = k := by rw [j3 _ (by omega)]; exact r75
      obtain ⟨c'', t, ex, ht, h16, h17, h15, hn, hm, hr, hrm, ho⟩ : ∃ c'' t,
          Exec P W mdBody c' c'' t ∧ t = 5 ∧ c''.nreg 2116 = i + 1 ∧ c''.nreg 2117 = 1 ∧
          c''.nreg 2115 = Y + 16 * S ∧
          (∀ r, r ≠ 2116 → r ≠ 2118 → r ≠ 2119 → c''.nreg r = c'.nreg r) ∧
          c''.nmem = upd c'.nmem (Y + 16 * S + i) (c'.nmem (Y + 16 * S + i) % k) ∧
          c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output := by
        have hv := hw.2 (Y + 16 * S + i)
        unfold mdBody
        exec_block
        all_goals try ((try config_simp); (try simp only [ha, j15, j17, j75]); omega)
        all_goals try ((try config_simp); (try simp only [ha, j15, j17, j75]); exact (Nat.mod_le _ _).trans hv)
        refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, ?_, rfl, rfl, rfl⟩
        all_goals config_simp
        all_goals try simp only [ha, j15, j17, j75]
        all_goals try (simp (disch := omega) only [upd_other])
      have hold : c'.nmem (Y + 16 * S + i) = c.nmem (Y + 16 * S + i) := j2 _ (Or.inr (by omega))
      refine ⟨c'', t, ex, by omega, h16, by rw [hn 2114 (by omega) (by omega) (by omega)]; exact hb,
        ⟨fun e he => ?_, fun a h => ?_, fun r hr' => ?_, h17, h15, by rw [hr, jr],
        by rw [hrm, jrm], by rw [ho, jo]⟩⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact j1 e he
        · rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), hold]
      · rw [hm, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
        exact j2 a (by omega)
      · rw [hn r (by omega) (by omega) (by omega)]; exact j3 r hr')
  obtain ⟨j1, j2, j3, -, -, jr, jrm, jo⟩ := hJ
  exact ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, j3, jr, jrm, jo⟩

end NegSSSP

end PlanarFlow
