module

public import PlanarFlow.NegSSSP.Enc.HoistPrm

/-!
# Chains of polynomial steps (single assignment)

A chain is a list of steps `(dst, ts, d)`: `dst := Σ c · m − d` (`hpTC`), each `m` a monomial
(`1`, a register, a product of two registers). Unlike `hpProg`, a step may read the register written
by an earlier step. Under the single-assignment condition **`pcWF`** (checked by the kernel: every
register is written at most once, a step reads neither its own target nor a later target nor the
scratch `t`, `t + 1`; coefficients and constants `≤ C`), the final registers of the run are **a
solution** of the equations of the chain (`PcSol`: `g dst = Σ c · m (g) − d` for every step), and
any solution agreeing with the start off the targets gives the word bounds.

* `pcProg t l`, `pcCost l`, `pcEval` (the solution computed step by step), **`pcEval_sol`**,
* **`pcProg_exec`**: within `pcCost l` steps, the final registers solve the chain; registers off
  the targets and `t`, `t + 1`, the memory, reals and output are kept.
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- A step of a chain: target, terms, subtracted constant. -/
abbrev PcStep := ℕ × List (ℕ × hpM) × ℕ

/-- The program of a chain (scratch `t`, `t + 1`). -/
def pcProg (t : ℕ) : List PcStep → Stmt
  | [] => .skip
  | s :: l => .seq (hpTC s.1 t s.2.1 s.2.2) (pcProg t l)

/-- Its number of steps. -/
def pcCost : List PcStep → ℕ
  | [] => 0
  | s :: l => 4 * s.2.1.length + 3 + pcCost l

/-- The registers a monomial reads. -/
def hpM.regs : hpM → List ℕ
  | .one => []
  | .v r => [r]
  | .vv r s => [r, s]

/-- The registers read by a list of terms. -/
def pcReads (ts : List (ℕ × hpM)) : List ℕ := ts.flatMap fun x => x.2.regs

/-- The targets of a chain. -/
def pcDsts (l : List PcStep) : List ℕ := l.map (·.1)

/-- **Single assignment** (Boolean, for the kernel). -/
def pcWF (t C : ℕ) : List PcStep → Bool
  | [] => true
  | s :: l => (s.1 != t) && (s.1 != t + 1) && !((pcDsts l).contains s.1) &&
      (pcReads s.2.1).all (fun r => (r != t) && (r != t + 1) && (r != s.1) &&
        !((pcDsts l).contains r)) &&
      s.2.1.all (fun x => decide (1 ≤ x.1) && decide (x.1 ≤ C)) && decide (s.2.2 ≤ C) &&
      pcWF t C l

/-- The equations of a chain. -/
def PcSol (l : List PcStep) (g : ℕ → ℕ) : Prop := ∀ s ∈ l, g s.1 = hpSum g s.2.1 - s.2.2

/-- The solution computed step by step. -/
def pcEval (f : ℕ → ℕ) : List PcStep → ℕ → ℕ
  | [] => f
  | s :: l => pcEval (Function.update f s.1 (hpSum f s.2.1 - s.2.2)) l

theorem hpM_avoid_of_regs {m : hpM} {x : ℕ} (h : x ∉ m.regs) : m.avoid x := by
  cases m <;> simp_all [hpM.regs, hpM.avoid] <;> omega

theorem hpM_ev_congr {m : hpM} {f g : ℕ → ℕ} (h : ∀ r ∈ m.regs, g r = f r) :
    m.ev g = m.ev f := by
  cases m <;> simp_all [hpM.regs, hpM.ev]

theorem hpSum_congr {ts : List (ℕ × hpM)} {f g : ℕ → ℕ} (h : ∀ r ∈ pcReads ts, g r = f r) :
    hpSum g ts = hpSum f ts := by
  unfold hpSum; congr 1
  apply List.map_congr_left
  intro x hx
  rw [hpM_ev_congr (fun r hr => h r (by
    simp only [pcReads, List.mem_flatMap]; exact ⟨x, hx, hr⟩))]

theorem pcEval_off {f : ℕ → ℕ} {l : List PcStep} {r : ℕ} (h : r ∉ pcDsts l) :
    pcEval f l r = f r := by
  induction l generalizing f with
  | nil => rfl
  | cons s l ih =>
    simp only [pcDsts, List.map_cons, List.mem_cons, not_or] at h
    simp only [pcEval]
    rw [ih h.2, Function.update_of_ne h.1]

/-- The pieces of `pcWF` for a step. -/
theorem pcWF_cons {t C : ℕ} {s : PcStep} {l : List PcStep} (h : pcWF t C (s :: l) = true) :
    s.1 ≠ t ∧ s.1 ≠ t + 1 ∧ s.1 ∉ pcDsts l ∧
      (∀ r ∈ pcReads s.2.1, r ≠ t ∧ r ≠ t + 1 ∧ r ≠ s.1 ∧ r ∉ pcDsts l) ∧
      (∀ x ∈ s.2.1, 1 ≤ x.1 ∧ x.1 ≤ C) ∧ s.2.2 ≤ C ∧ pcWF t C l = true := by
  simp only [pcWF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨by simpa using h1, by simpa using h2, by simpa [pcDsts] using h3, fun r hr => ?_, h5,
    h6, h7⟩
  · obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h4 r hr
    exact ⟨by simpa using a, by simpa using b, by simpa using c, by simpa [pcDsts] using d⟩

/-- **`pcEval` solves the chain.** -/
theorem pcEval_sol {t C : ℕ} {l : List PcStep} (hwf : pcWF t C l = true) (f : ℕ → ℕ) :
    PcSol l (pcEval f l) := by
  induction l generalizing f with
  | nil => intro s hs; simp at hs
  | cons s l ih =>
    obtain ⟨-, -, h3, h4, -, -, h7⟩ := pcWF_cons hwf
    intro s' hs'
    simp only [List.mem_cons] at hs'
    rcases hs' with rfl | hs'
    · simp only [pcEval]
      rw [pcEval_off h3, Function.update_self]
      congr 1
      exact (hpSum_congr fun r hr => by
        rw [pcEval_off (h4 r hr).2.2.2, Function.update_of_ne (h4 r hr).2.2.1]).symm
    · exact ih h7 _ s' hs'

/-- **A chain on the machine** (see the module docstring). -/
theorem pcProg_exec {I : Input} {W t C : ℕ} (l : List PcStep) (hwf : pcWF t C l = true)
    (hC : C ≤ W) (c : Config) (hc : WordsBounded W c)
    (hB : ∀ g : ℕ → ℕ, (∀ r, r ∉ pcDsts l → r ≠ t → r ≠ t + 1 → g r = c.nreg r) →
      PcSol l g → ∀ s ∈ l, hpSum g s.2.1 ≤ W) :
    ∃ c', Exec I W (pcProg t l) c c' (pcCost l) ∧ PcSol l c'.nreg ∧
      (∀ r, r ∉ pcDsts l → r ≠ t → r ≠ t + 1 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  induction l generalizing c with
  | nil => exact ⟨c, .skip hc, fun s hs => by simp at hs, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | cons s l ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := pcWF_cons hwf
    have hok : hpOK W s.1 t s.2.1 := fun x hx => by
      have hr : ∀ r ∈ x.2.regs, r ∈ pcReads s.2.1 := fun r hr => by
        simp only [pcReads, List.mem_flatMap]; exact ⟨x, hx, hr⟩
      refine ⟨(h5 x hx).1, (h5 x hx).2.trans hC, hpM_avoid_of_regs fun h => ?_,
        hpM_avoid_of_regs fun h => ?_, hpM_avoid_of_regs fun h => ?_⟩
      · exact (h4 _ (hr _ h)).2.2.1 rfl
      · exact (h4 _ (hr _ h)).1 rfl
      · exact (h4 _ (hr _ h)).2.1 rfl
    -- the bound of the first step, from the computed solution
    have hB₀ : hpSum c.nreg s.2.1 ≤ W := by
      have := hB (pcEval c.nreg (s :: l)) (fun r hr _ _ => pcEval_off hr)
        (pcEval_sol hwf _) s (by simp)
      rwa [hpSum_congr (g := pcEval c.nreg (s :: l)) (f := c.nreg) fun r hr => by
        rw [pcEval_off (l := s :: l) (by
          simp only [pcDsts, List.map_cons, List.mem_cons, not_or]
          exact ⟨(h4 r hr).2.2.1, (h4 r hr).2.2.2⟩)]] at this
    obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁⟩ := hpTC_exec (I := I) s.2.1 s.2.2 hok h1 h2 c hc
      hB₀ (h6.trans hC)
    obtain ⟨c', e', v', f', m', r', rm', o'⟩ := ih h7 c₁ e₁.wb_right (fun g hg hs => by
      have hsol : PcSol (s :: l) g := by
        intro s' hs'
        simp only [List.mem_cons] at hs'
        rcases hs' with rfl | hs'
        · rw [hg _ h3 h1 h2, v₁]
          congr 1
          exact (hpSum_congr fun r hr => by
            rw [hg r (h4 r hr).2.2.2 (h4 r hr).1 (h4 r hr).2.1,
              f₁ r (h4 r hr).2.2.1 (h4 r hr).1 (h4 r hr).2.1]).symm
        · exact hs s' hs'
      have := hB g (fun r hr ht ht' => by
        simp only [pcDsts, List.map_cons, List.mem_cons, not_or] at hr
        rw [hg r hr.2 ht ht', f₁ r hr.1 ht ht']) hsol
      exact fun s' hs' => this s' (by simp [hs']))
    refine ⟨c', (Exec.seq e₁ e').cast (by simp [pcCost]), ?_, fun r hr ht ht' => ?_,
      by rw [m', m₁], by rw [r', r₁], by rw [rm', rm₁], by rw [o', o₁]⟩
    · intro s' hs'
      simp only [List.mem_cons] at hs'
      rcases hs' with rfl | hs'
      · rw [f' _ h3 h1 h2, v₁]
        congr 1
        exact (hpSum_congr fun r hr => by
          rw [f' r (h4 r hr).2.2.2 (h4 r hr).1 (h4 r hr).2.1,
            f₁ r (h4 r hr).2.2.1 (h4 r hr).1 (h4 r hr).2.1]).symm
      · exact v' s' hs'
    · simp only [pcDsts, List.map_cons, List.mem_cons, not_or] at hr
      rw [f' r hr.2 ht ht', f₁ r hr.1 ht ht']

end NegSSSP

end PlanarFlow
