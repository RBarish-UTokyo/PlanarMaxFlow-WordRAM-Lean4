module

public import PlanarSeparator.Machine.MillerThin

/-!
# Miller's separator on the machine: a dart at every vertex

Part of step 1 of the plan in `PlanarSeparator/Machine/Miller.lean`. The heavy test, the
bisection and the concentrated weights read, for every vertex `v`, a dart `fd v` at `v` (at
`bF + v`; `MillerProg.Setup`, `MillerProg.InMem`). With the vertices `V x` of the darts
`x < 3 k` at `bV`, the program `dpass` stores every dart `x` at `bF + V x`, so that the last dart
at each vertex stays there (`dpass_exec`, within `21 k + 4` steps); read through the coding of
the darts and a numbering of the vertices, it is a dart at every vertex (`dpass_dart`).

Registers: `r140 … r143` (`0`, `1`, `3`, `k`), `r162 = bV`, `r164 = bF`; the program writes
`r211 … r214`.
-/

@[expose] public section

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-- **One dart** `r211 = x`: store it at its vertex. -/
def dbody : Stmt :=
  block [.addN 212 162 211, .loadN 213 212, .addN 212 164 213, .storeN 212 211, .addN 211 211 141]

/-- **A dart at every vertex.** -/
def dpass : Stmt := .seq (block [.copyN 211 140, .mulN 214 143 142]) (.whileLtN 211 214 dbody)

section proofs

variable {W : ℕ} {P : Input} {k n bV bF : ℕ} {V : ℕ → ℕ}

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
/-- **A dart at every vertex.** After `dpass`, the slot of the vertex of every dart holds a dart
at that vertex. -/
theorem dpass_exec (hlay : bV + 3 * k ≤ bF) (hW : bF + n + 3 * k ≤ W) (c : Config)
    (hc : WordsBounded W c) (h140 : c.nreg 140 = 0) (h141 : c.nreg 141 = 1)
    (h142 : c.nreg 142 = 3) (h143 : c.nreg 143 = k) (h162 : c.nreg 162 = bV)
    (h164 : c.nreg 164 = bF) (hV : ∀ x < 3 * k, c.nmem (bV + x) = V x ∧ V x < n) :
    ∃ c' t, Exec P W dpass c c' t ∧ t ≤ 21 * k + 4 ∧
      (∀ x < 3 * k, c'.nmem (bF + V x) < 3 * k ∧ V (c'.nmem (bF + V x)) = V x) ∧
      (∀ r, r < 211 ∨ 215 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bF ∨ bF + n ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 211 = i ∧
    c'.nreg 214 = 3 * k ∧ i ≤ 3 * k ∧
    (∀ x < i, c'.nmem (bF + V x) < i ∧ V (c'.nmem (bF + V x)) = V x) ∧
    (∀ r, r < 211 ∨ 215 ≤ r → c'.nreg r = c.nreg r) ∧
    (∀ a, a < bF ∨ bF + n ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 211 140, .mulN 214 143 142])
      c c₁ k₁ ∧ I 0 c₁ ∧ k₁ = 2 := by
    exec_block
    · config_simp; rw [h143, h142]; omega
    exact ⟨⟨‹_›, by config_simp; exact h140, by config_simp; rw [h143, h142]; ring, by omega,
      fun x hx => absurd hx (by omega),
      fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega,
      fun a _ => rfl, rfl⟩, rfl⟩
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 211) (rN := 214)
    (N := 3 * k) (lo := 0) (B := 5) (body := dbody) I (fun i c' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i c₁ ⟨hw₁, h211, h214, hin, hP, hr, hf, ho⟩ hi => by
      have g141 : c₁.nreg 141 = 1 := by rw [hr 141 (by omega)]; exact h141
      have g162 : c₁.nreg 162 = bV := by rw [hr 162 (by omega)]; exact h162
      have g164 : c₁.nreg 164 = bF := by rw [hr 164 (by omega)]; exact h164
      have mV : c₁.nmem (bV + i) = V i := by rw [hf _ (Or.inl (by omega))]; exact (hV i hi).1
      have hVi := (hV i hi).2
      unfold dbody
      exec_block
      all_goals try (config_simp; (try simp only [g162, h211, mV, g164, g141]); omega)
      rename_i hwb
      simp only [g162, h211, mV, g164, g141] at hwb ⊢
      refine ⟨⟨‹_›, by config_simp; try omega, by config_simp; exact h214, by omega,
        fun x hx => ?_, fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
        fun a ha => by config_simp; rw [upd_other _ _ _ (by omega)]; exact hf a ha,
        by config_simp; exact ho⟩, by omega⟩
      config_simp
      by_cases hx' : V x = V i
      · rw [hx', upd_same]; exact ⟨by omega, rfl⟩
      · rw [upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
        · obtain ⟨a1, a2⟩ := hP x hx; exact ⟨by omega, a2⟩
        · exact absurd rfl hx')
    (by omega) hI₁
  obtain ⟨-, -, -, -, hP', hr', hf', ho'⟩ := hI
  exact ⟨c', 2 + t, .seq e₁ e, by omega, hP', hr', hf', ho'⟩

end proofs

section Bridge

open Map CycleSearch

variable {D P : Type*} [Fintype D] [DecidableEq D] [Fintype P] {M : Map D P} {k n : ℕ}
  (cd : D ≃ Fin (3 * k)) (vi : P ≃ Fin n) {V : ℕ → ℕ}

/-- **The darts of `dpass` are darts at the vertices**: for a plane map coded by `cd`, with the
vertices of the darts read through a numbering `vi` of the vertices, the numbers `F u` that
`dpass_exec` leaves at the vertices are the codes of darts `fdD v` at the vertices `v`. -/
theorem dpass_dart (hM : M.IsPlane) (hV : ∀ x, V (cd x) = vi (M.vert x)) {F : ℕ → ℕ}
    (hF : ∀ x < 3 * k, F (V x) < 3 * k ∧ V (F (V x)) = V x) :
    ∃ fdD : P → D, (∀ v, M.vert (fdD v) = v) ∧ ∀ v, F (vi v) = cd (fdD v) := by
  have hd : ∀ v, ∃ x : D, V (cd x) = vi v := fun v => by
    obtain ⟨d, hd⟩ := hM.exists_dart v
    exact ⟨d, by rw [hV, hd]⟩
  choose d hd using hd
  have hlt : ∀ v, F (vi v) < 3 * k := fun v => by
    have := (hF _ (cd (d v)).2).1; rwa [hd] at this
  refine ⟨fun v => cd.symm ⟨F (vi v), hlt v⟩, fun v => ?_, fun v => by simp⟩
  apply vi.injective
  apply Fin.ext
  rw [← hV]
  have := (hF _ (cd (d v)).2).2
  rw [hd] at this
  simpa using this

end Bridge

end MillerProg

end PlanarSeparator
