module

public import PlanarFlow.BKMNW.LinLoops

/-!
# A generic map loop over an array

`OUT[i] := g i` for `i < m`, where a value block `vb` computes `g i` into a register from the
memory (unchanged outside `OUT`) and the registers of the start:

* `mapBody vb ctr one ob t v` (`vb`, then `mem (ob + ctr) := v`, `ctr := ctr + 1`), `mapProg`
  (the loop `while ctr < bnd`).
* **`mapProg_exec`**: if `vb` takes at most `B` steps, writes only the registers of `scr` and
  computes `g i` into `v` from any configuration whose registers off `scr` (but the counter `i`)
  are those of the start and whose memory off `[ob, ob + m)` is that of the start, then the loop
  takes at most `(B + 5) m + 2` steps and ends with `OUT[i] = g i` (`i < m`), the memory off `OUT`,
  the registers off `scr`, `t`, `ctr`, the reals and the output kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- One step of the map: the value block, then `mem (ob + ctr) := v`, `ctr := ctr + 1`. -/
def mapBody (vb : Stmt) (ctr one ob t v : ℕ) : Stmt :=
  .seq vb (block [.addN t ob ctr, .storeN t v, .addN ctr ctr one])

/-- **The map loop** `OUT[i] := g i` for `ctr < bnd`. -/
def mapProg (vb : Stmt) (ctr bnd one ob t v : ℕ) : Stmt :=
  .whileLtN ctr bnd (mapBody vb ctr one ob t v)

section Exec

variable {P : Input} {W : ℕ}

theorem mapStore_exec (c : Config) (hc : WordsBounded W c) {ctr one ob t v Ob i : ℕ}
    (r1 : c.nreg ctr = i) (r2 : c.nreg one = 1) (r3 : c.nreg ob = Ob) (w1 : Ob + i ≤ W)
    (w2 : i + 1 ≤ W) (h1 : t ≠ ctr) (h2 : t ≠ one) (h3 : t ≠ ob) (h4 : t ≠ v) (h5 : ctr ≠ one) :
    ∃ c' k, Exec P W (block [.addN t ob ctr, .storeN t v, .addN ctr ctr one]) c c' k ∧ k = 3 ∧
      c'.nreg ctr = i + 1 ∧ c'.nmem = upd c.nmem (Ob + i) (c.nreg v) ∧
      (∀ x, x ≠ t → x ≠ ctr → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  all_goals try omega
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same, r1, r2, r3]; omega)
  refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl⟩
  · config_simp; simp (disch := omega) only [upd_other, upd_same, r1, r2]
  · config_simp; simp (disch := omega) only [upd_other, upd_same, r1, r3]
  · config_simp; simp (disch := omega) only [upd_other, upd_same]

/-- **The map loop** (see the module docstring). -/
theorem mapProg_exec (c : Config) (hc : WordsBounded W c) {vb : Stmt}
    {ctr bnd one ob t v m Ob B : ℕ} (scr : ℕ → Prop) (g : ℕ → ℕ)
    (r0 : c.nreg ctr = 0) (r1 : c.nreg bnd = m) (r2 : c.nreg one = 1) (r3 : c.nreg ob = Ob)
    (w1 : Ob + m ≤ W) (w2 : m + 1 ≤ W)
    (s1 : ¬ scr ctr) (s2 : ¬ scr bnd) (s3 : ¬ scr one) (s4 : ¬ scr ob)
    (h1 : t ≠ ctr) (h2 : t ≠ one) (h3 : t ≠ ob) (h4 : t ≠ v) (h5 : ctr ≠ one) (h6 : t ≠ bnd)
    (h7 : ctr ≠ bnd) (h8 : ob ≠ ctr)
    (hvb : ∀ i < m, ∀ c' : Config, WordsBounded W c' → c'.nreg ctr = i →
      (∀ x, ¬ scr x → x ≠ t → x ≠ ctr → c'.nreg x = c.nreg x) →
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + m) → c'.nmem a = c.nmem a) →
      ∃ c'' k, Exec P W vb c' c'' k ∧ k ≤ B ∧ c''.nreg v = g i ∧
        (∀ x, ¬ scr x → c''.nreg x = c'.nreg x) ∧ c''.nmem = c'.nmem ∧
        c''.rreg = c'.rreg ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output) :
    ∃ c' k, Exec P W (mapProg vb ctr bnd one ob t v) c c' k ∧ k ≤ (B + 5) * m + 2 ∧
      c'.nreg ctr = m ∧ (∀ j < m, c'.nmem (Ob + j) = g j) ∧
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ scr x → x ≠ t → x ≠ ctr → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, ¬ scr x → x ≠ t → x ≠ ctr → c'.nreg x = c.nreg x) ∧
    (∀ j < i, c'.nmem (Ob + j) = g j) ∧
    (∀ a, ¬ (Ob ≤ a ∧ a < Ob + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, hct, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := ctr)
    (b := bnd) (body := mapBody vb ctr one ob t v) J (B := B + 3) c hc r0 r1 (Nat.zero_le m)
    ⟨fun _ _ _ _ => rfl, fun j hj => absurd hj (by omega), fun a _ => rfl, rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw hci hbn ⟨j1, j2, j3, j4, j5, j6⟩ => by
      obtain ⟨c₁, k₁, e₁, hk₁, hv, hn₁, hm₁, hr₁, hrm₁, ho₁⟩ := hvb i hhi c' hw hci j1
        (fun a ha => j3 a (fun h => ha ⟨h.1, by omega⟩))
      have q1 : c₁.nreg ctr = i := by rw [hn₁ _ s1, hci]
      have q2 : c₁.nreg one = 1 := by rw [hn₁ _ s3, j1 _ s3 h2.symm h5.symm, r2]
      have q3 : c₁.nreg ob = Ob := by
        rw [hn₁ _ s4, j1 _ s4 h3.symm h8, r3]
      obtain ⟨c₃, k₃, e₃, hk₃, g1, gm, gn, gr, grm, go⟩ := mapStore_exec (P := P) c₁ e₁.wb_right
        q1 q2 q3 (by omega) (by omega) h1 h2 h3 h4 h5
      refine ⟨c₃, k₁ + k₃, .seq e₁ e₃, by omega, g1, ?_, ⟨fun x hx ht hc => ?_, fun j hj => ?_,
        fun a ha => ?_, by rw [gr, hr₁, j4], by rw [grm, hrm₁, j5], by rw [go, ho₁, j6]⟩⟩
      · rw [gn _ h6.symm h7.symm, hn₁ _ s2, hbn]
      · rw [gn x ht hc, hn₁ x hx, j1 x hx ht hc]
      · rw [gm, hm₁]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same, hv]
      · rw [gm, hm₁, upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]
        exact j3 a (fun h => ha ⟨h.1, by omega⟩))
  refine ⟨c₂, k₂, e₂, ?_, hct, j2, j3, j1, j4, j5, j6⟩
  simpa [Nat.sub_zero, show B + 3 + 2 = B + 5 by omega] using hk₂

end Exec

end BKMNW

end PlanarFlow
