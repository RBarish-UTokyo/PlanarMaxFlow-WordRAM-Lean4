module

public import PlanarFlow.NegSSSP.Enc.PrmChain

/-!
# The weight bound `Wc = (srcW …).toNat` of an instance, computed from its plain arrays

`pwWc dst rIS rLN rN`: with the base of the flags `IS` in `r rIS`, the base of the lengths `LN` in
`r rLN` and the number of darts in `r rN`, `r dst := 1 + Σ_{i < n} IS[i] · LN[i]` (scratch
registers `10690 … 10697`).

* **`pwWc_exec`**: within `9 n + 9` steps; memory, reals, output and the registers outside
  `[10690, 10697]` but `dst` kept.
* **`pw_srcW`**: for the plain arrays of an instance (`IS[σ d] = [d ∈ S]`,
  `LN[σ d] = (ℓ d).toNat`, `ℓ ≥ 0`), that value is `(Klein.srcW S ℓ).toNat`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- `acc += IS[i] · LN[i]; i += 1`. -/
def pwBody : Stmt :=
  block [.addN 10696 10690 10694, .loadN 10696 10696, .addN 10697 10691 10694,
    .loadN 10697 10697, .mulN 10696 10696 10697, .addN 10693 10693 10696,
    .addN 10694 10694 10695]

/-- **`r dst := 1 + Σ_{i < n} IS[i] · LN[i]`.** -/
def pwWc (dst rIS rLN rN : ℕ) : Stmt :=
  .seq (block [.copyN 10690 rIS, .copyN 10691 rLN, .copyN 10692 rN, .constN 10693 1,
      .constN 10694 0, .constN 10695 1])
    (.seq (.whileLtN 10694 10692 pwBody) (block [.copyN dst 10693]))

theorem pwWc_natOnly (dst rIS rLN rN : ℕ) : Klein.natOnly (pwWc dst rIS rLN rN) = true := by
  kernel_rfl

/-- The partial sums. -/
def pwS (m : ℕ → ℕ) (a b i : ℕ) : ℕ := ∑ j ∈ range i, m (a + j) * m (b + j)

theorem pwS_succ (m : ℕ → ℕ) (a b i : ℕ) :
    pwS m a b (i + 1) = pwS m a b i + m (a + i) * m (b + i) := by
  simp [pwS, sum_range_succ]

theorem pwS_mono (m : ℕ → ℕ) (a b : ℕ) {i j : ℕ} (h : i ≤ j) : pwS m a b i ≤ pwS m a b j :=
  sum_le_sum_of_subset (range_subset_range.2 h)

theorem pwBody_exec (c : Config) (hc : WordsBounded W c) {a b i acc : ℕ}
    (r90 : c.nreg 10690 = a) (r91 : c.nreg 10691 = b) (r93 : c.nreg 10693 = acc)
    (r94 : c.nreg 10694 = i) (r95 : c.nreg 10695 = 1) (w1 : a + i ≤ W) (w2 : b + i ≤ W)
    (w3 : i + 1 ≤ W) (w4 : acc + c.nmem (a + i) * c.nmem (b + i) ≤ W) :
    ∃ c' k, Exec P W pwBody c c' k ∧ k = 7 ∧
      c'.nreg 10693 = acc + c.nmem (a + i) * c.nmem (b + i) ∧ c'.nreg 10694 = i + 1 ∧
      (∀ r, r ≠ 10693 → r ≠ 10694 → r ≠ 10696 → r ≠ 10697 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pwBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r90, r91, r93, r94, r95]); omega)
  refine ⟨rfl, ?_, ?_, fun r hr1 hr2 hr3 hr4 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r90, r91, r93, r94]
  · config_simp; simp only [r94, r95]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The weight bound on the machine** (see the module docstring). -/
theorem pwWc_exec {dst rIS rLN rN a b n : ℕ} (hd : dst < 10690 ∨ 10697 < dst)
    (hr1 : rLN < 10690 ∨ 10697 < rLN) (hr2 : rN < 10690 ∨ 10697 < rN) (c : Config)
    (hc : WordsBounded W c) (hIS : c.nreg rIS = a) (hLN : c.nreg rLN = b) (hN : c.nreg rN = n)
    (w1 : a + n ≤ W) (w2 : b + n ≤ W) (w3 : 1 + pwS c.nmem a b n ≤ W) :
    ∃ c' k, Exec P W (pwWc dst rIS rLN rN) c c' k ∧ k ≤ 9 * n + 9 ∧
      c'.nreg dst = 1 + pwS c.nmem a b n ∧
      (∀ r, r ≠ dst → (r < 10690 ∨ 10697 < r) → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold pwWc
  obtain ⟨c₁, k₁, e₁, hk₁, g90, g91, g92, g93, g94, g95, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 10690 rIS, .copyN 10691 rLN, .copyN 10692 rN, .constN 10693 1,
        .constN 10694 0, .constN 10695 1]) c c₁ k₁ ∧ k₁ = 6 ∧ c₁.nreg 10690 = a ∧
      c₁.nreg 10691 = b ∧ c₁.nreg 10692 = n ∧ c₁.nreg 10693 = 1 ∧ c₁.nreg 10694 = 0 ∧
      c₁.nreg 10695 = 1 ∧
      (∀ r, r < 10690 ∨ 10697 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    have n1 : rLN ≠ 10690 := by omega
    have n2 : rN ≠ 10690 := by omega
    have n3 : rN ≠ 10691 := by omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals (try config_simp); (try simp only [upd_apply, n1, n2, n3, ite_false])
    all_goals first | exact hIS | exact hLN | exact hN | (split_ifs <;> omega)
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nreg 10693 = 1 + pwS c.nmem a b i ∧ c'.nreg 10690 = a ∧ c'.nreg 10691 = b ∧
      c'.nreg 10695 = 1 ∧ (∀ r, r < 10690 ∨ 10697 < r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, hJ⟩ := forLoop_exec (P := P) (a := 10694) (bR := 10692)
    (body := pwBody) J (K := 7) (n := n) c₁ e₁.wb_right g94 g92
    ⟨by rw [g93]; simp [pwS], g90, g91, g95, gn₁, gm₁, gr₁, grm₁, go₁⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j93, j90, j91, j95, jn, jm, jr, jrm, jo⟩ := hJ
      have hle := pwS_mono c.nmem a b (show i + 1 ≤ n by omega)
      rw [pwS_succ] at hle
      obtain ⟨c'', k, ex, hk, h93, h94, hn, hm, hr, hrm, ho⟩ := pwBody_exec (P := P) c' hw j90
        j91 j93 ha j95 (by omega) (by omega) (by omega) (by rw [jm]; omega)
      refine ⟨c'', k, ex, by omega, h94,
        by rw [hn 10692 (by omega) (by omega) (by omega) (by omega)]; exact hb,
        by rw [h93, jm, pwS_succ]; ring,
        by rw [hn 10690 (by omega) (by omega) (by omega) (by omega)]; exact j90,
        by rw [hn 10691 (by omega) (by omega) (by omega) (by omega)]; exact j91,
        by rw [hn 10695 (by omega) (by omega) (by omega) (by omega)]; exact j95,
        fun r hr' => by rw [hn r (by omega) (by omega) (by omega) (by omega)]; exact jn r hr',
        by rw [hm, jm], by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩)
  obtain ⟨j93, -, -, -, jn, jm, jr, jrm, jo⟩ := hJ
  obtain ⟨c₃, k₃, e₃, hk₃, h3, hn3, hm3, hr3, hrm3, ho3⟩ : ∃ c₃ k₃,
      Exec P W (block [.copyN dst 10693]) c₂ c₃ k₃ ∧ k₃ = 1 ∧ c₃.nreg dst = c₂.nreg 10693 ∧
      (∀ r, r ≠ dst → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, k₁ + (k₂ + k₃), Exec.seq e₁ (Exec.seq e₂ e₃), by omega,
    by rw [h3, j93], fun r h1 h2 => by rw [hn3 r h1, jn r h2], by rw [hm3, jm], by rw [hr3, jr],
    by rw [hrm3, jrm], by rw [ho3, jo]⟩

/-- **The value of the loop is the weight bound of the instance.** -/
theorem pw_srcW {D : Type*} [Fintype D] [DecidableEq D] {n : ℕ} (σ : D ≃ Fin n) (S : Finset D)
    (ℓ : D → ℤ) (hnn : ∀ d, 0 ≤ ℓ d) (m : ℕ → ℕ) (a b : ℕ)
    (hIS : ∀ d, m (a + σ d) = if d ∈ S then 1 else 0) (hLN : ∀ d, m (b + σ d) = (ℓ d).toNat) :
    1 + pwS m a b n = (Klein.srcW S ℓ).toNat := by
  have h1 : pwS m a b n = ∑ d, m (a + σ d) * m (b + σ d) := by
    unfold pwS
    rw [← Fin.sum_univ_eq_sum_range (fun j => m (a + j) * m (b + j))]
    exact (Equiv.sum_comp σ (fun j : Fin n => m (a + j) * m (b + j))).symm
  have h2 : ∑ d, m (a + σ d) * m (b + σ d) = ∑ d ∈ S, (ℓ d).toNat := by
    simp only [hIS, hLN, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, h2]
  unfold Klein.srcW
  have : (1 : ℤ) + ∑ d ∈ S, ℓ d = ((1 + ∑ d ∈ S, (ℓ d).toNat : ℕ) : ℤ) := by
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun d _ => (Int.toNat_of_nonneg (hnn d)).symm
  rw [this, Int.toNat_natCast]

end NegSSSP

end PlanarFlow
