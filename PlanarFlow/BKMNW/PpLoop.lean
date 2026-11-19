module

public import PlanarFlow.BKMNW.PpVB

/-!
# Loops of the preprocessing: maps, sums, scatters

Registers: the counter `8740`, the bound `8741`, `8704 = 1`, the output base `8742`, the address
`8743`, the value `8744` (written by the value blocks, scratch `pscr`), the accumulator `8738`,
the input base of the scatter `8748`.

* `mapL vb`, **`mapL_exec`**: `OUT[i] := g i` for `i < m` (`mapProg` with the counter reset);
* `sumL vb`, **`sumL_exec`**: `r8738 := ∑_{i < m} g i`;
* `scatL`, **`scatL_exec`**: `OUT[A[i]] := i` for `i < m`, `A` a permutation of `[0, m)`.
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

/-! ### The map loop -/

/-- **The map loop** `OUT[i] := g i`, `i < r8741`, `OUT` at `r8742`. -/
def mapL (vb : Stmt) : Stmt :=
  .seq (block [.constN 8740 0]) (mapProg vb 8740 8741 8704 8742 8743 8744)

/-- The frame of a loop: the registers outside a set kept. -/
def LFr (pr : ℕ → Prop) (c c' : Config) : Prop := ∀ x, ¬ pr x → c'.nreg x = c.nreg x

theorem mapL_exec (c : Config) (hc : WordsBounded W c) {vb : Stmt} {m Ob B : ℕ} (g : ℕ → ℕ)
    (r1 : c.nreg 8741 = m) (r2 : c.nreg 8704 = 1) (r3 : c.nreg 8742 = Ob)
    (w1 : Ob + m ≤ W) (w2 : m + 1 ≤ W)
    (hvb : ∀ i < m, ∀ c' : Config, WordsBounded W c' → c'.nreg 8740 = i →
      (∀ x, ¬ pscr x → x ≠ 8743 → x ≠ 8740 → c'.nreg x = c.nreg x) →
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + m) → c'.nmem a = c.nmem a) →
      ∃ c'' k, Exec P W vb c' c'' k ∧ VBPost c' (g i) B c'' k) :
    ∃ c' t, Exec P W (mapL vb) c c' t ∧ t ≤ (B + 5) * m + 3 ∧
      (∀ j < m, c'.nmem (Ob + j) = g j) ∧
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ pscr x → x ≠ 8743 → x ≠ 8740 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := cst_exec (P := P) (r := 8740) (v := 0)
    c hc (Nat.zero_le _)
  have hs : ∀ x, ¬ pscr x ↔ ¬ (8744 ≤ x ∧ x ≤ 8779) := fun x => Iff.rfl
  obtain ⟨c₂, k₂, e₂, hk₂, h20, j1, j2, j3, j4, j5, j6⟩ := mapProg_exec (P := P) c₁ e₁.wb_right
    (vb := vb) (ctr := 8740) (bnd := 8741) (one := 8704) (ob := 8742) (t := 8743) (v := 8744)
    (m := m) (Ob := Ob) (B := B) pscr g v1 (by rw [n1 _ (by omega)]; exact r1)
    (by rw [n1 _ (by omega)]; exact r2) (by rw [n1 _ (by omega)]; exact r3) w1 w2
    (by unfold pscr; omega) (by unfold pscr; omega) (by unfold pscr; omega)
    (by unfold pscr; omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
    (fun i hi c' hw h20 hr hm => hvb i hi c' hw h20 (fun x hx h1 h2 => by
      rw [hr x hx h1 h2, n1 x h2]) (fun a ha => by rw [hm a ha, m1]))
  refine ⟨c₂, _, .seq e₁ e₂, by omega, j1, fun a ha => by rw [j2 a ha, m1],
    fun x hx h1 h2 => by rw [j3 x hx h1 h2, n1 x h2], by rw [j4, rr1], by rw [j5, rm1],
    by rw [j6, o1]⟩

/-! ### The sum loop -/

/-- **The sum loop** `r8738 := ∑_{i < r8741} g i`. -/
def sumL (vb : Stmt) : Stmt :=
  .seq (block [.constN 8740 0, .constN 8738 0])
    (.whileLtN 8740 8741 (.seq vb (block [.addN 8738 8738 8744, .addN 8740 8740 8704])))

theorem sumL_exec (c : Config) (hc : WordsBounded W c) {vb : Stmt} {m B : ℕ} (g : ℕ → ℕ)
    (r1 : c.nreg 8741 = m) (r2 : c.nreg 8704 = 1) (w1 : ∑ j ∈ range m, g j ≤ W) (w2 : m + 1 ≤ W)
    (hvb : ∀ i < m, ∀ c' : Config, WordsBounded W c' → c'.nreg 8740 = i →
      (∀ x, ¬ pscr x → x ≠ 8738 → x ≠ 8740 → c'.nreg x = c.nreg x) →
      c'.nmem = c.nmem →
      ∃ c'' k, Exec P W vb c' c'' k ∧ VBPost c' (g i) B c'' k) :
    ∃ c' t, Exec P W (sumL vb) c c' t ∧ t ≤ (B + 4) * m + 4 ∧
      c'.nreg 8738 = ∑ j ∈ range m, g j ∧ c'.nmem = c.nmem ∧
      (∀ x, ¬ pscr x → x ≠ 8738 → x ≠ 8740 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v40, v38, n1, m1, rr1, rm1, o1⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 8740 0, .constN 8738 0]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 8740 = 0 ∧
      c₁.nreg 8738 = 0 ∧ (∀ x, x ≠ 8740 → x ≠ 8738 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · omega
    · omega
    refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩ <;>
    · config_simp; try simp (disch := omega) only [upd_other]
  let J : ℕ → Config → Prop := fun i d =>
    d.nreg 8738 = ∑ j ∈ range i, g j ∧ d.nmem = c.nmem ∧
      (∀ x, ¬ pscr x → x ≠ 8738 → x ≠ 8740 → d.nreg x = c.nreg x) ∧
      d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h40, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 8740)
    (b := 8741) (body := .seq vb (block [.addN 8738 8738 8744, .addN 8740 8740 8704])) J
    (B := B + 2) c₁ e₁.wb_right v40 (by rw [n1 _ (by omega) (by omega)]; exact r1)
    (Nat.zero_le m)
    ⟨by rw [v38]; simp, m1, fun x hx h1 h2 => n1 x h2 h1, rr1, rm1, o1⟩
    (fun i d hlo hhi hw hci hbn ⟨j1, j2, j3, j4, j5, j6⟩ => by
      obtain ⟨d₁, k₁, e₁, hk₁, hv, hn₁, hm₁, hr₁, hrm₁, ho₁⟩ := hvb i hhi d hw hci j3 j2
      have q38 : d₁.nreg 8738 = ∑ j ∈ range i, g j := by
        rw [hn₁ _ (by unfold pscr; omega), j1]
      have q40 : d₁.nreg 8740 = i := by rw [hn₁ _ (by unfold pscr; omega), hci]
      have q04 : d₁.nreg 8704 = 1 := by
        rw [hn₁ _ (by unfold pscr; omega), j3 _ (by unfold pscr; omega) (by omega) (by omega), r2]
      have hsum : ∑ j ∈ range (i + 1), g j ≤ W :=
        le_trans (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))) w1
      have hd₁ := e₁.wb_right
      obtain ⟨d₂, k₂, e₂, hk₂, a38, a40, a41, aR, am, ar, arm, ao⟩ : ∃ d₂ k₂,
          Exec P W (block [.addN 8738 8738 8744, .addN 8740 8740 8704]) d₁ d₂ k₂ ∧ k₂ = 2 ∧
          d₂.nreg 8738 = ∑ j ∈ range (i + 1), g j ∧ d₂.nreg 8740 = i + 1 ∧
          d₂.nreg 8741 = m ∧ (∀ x, x ≠ 8738 → x ≠ 8740 → d₂.nreg x = d₁.nreg x) ∧
          d₂.nmem = d₁.nmem ∧ d₂.rreg = d₁.rreg ∧ d₂.rmem = d₁.rmem ∧
          d₂.output = d₁.output := by
        exec_block
        · config_simp; rw [q38, hv, ← Finset.sum_range_succ]; exact hsum
        · config_simp; rw [q40, q04]; omega
        refine ⟨rfl, ?_, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [q38, hv, Finset.sum_range_succ]
        · config_simp; rw [q40, q04]
        · config_simp; rw [hn₁ _ (by unfold pscr; omega), hbn]
        · config_simp; simp (disch := omega) only [upd_other]
      refine ⟨d₂, k₁ + k₂, .seq e₁ e₂, by omega, a40, a41, a38,
        by rw [am, hm₁, j2], fun x hx h1 h2 => by rw [aR x h1 h2, hn₁ x hx, j3 x hx h1 h2],
        by rw [ar, hr₁, j4], by rw [arm, hrm₁, j5], by rw [ao, ho₁, j6]⟩)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, ?_, j1, j2, j3, j4, j5, j6⟩
  have : (B + 2 + 2) * (m - 0) + 2 = (B + 4) * m + 2 := by rw [Nat.sub_zero]
  omega

/-! ### The scatter loop -/

/-- **The scatter loop** `OUT[A[i]] := i`, `i < r8741`, `A` at `r8748`, `OUT` at `r8742`. -/
def scatL : Stmt :=
  .seq (block [.constN 8740 0]) (.whileLtN 8740 8741
    (block [.addN 8743 8748 8740, .loadN 8745 8743, .addN 8743 8742 8745, .storeN 8743 8740,
      .addN 8740 8740 8704]))

theorem scatL_exec (c : Config) (hc : WordsBounded W c) {m Ab Ob : ℕ} (A : ℕ → ℕ)
    (r1 : c.nreg 8741 = m) (r2 : c.nreg 8704 = 1) (r3 : c.nreg 8742 = Ob) (r4 : c.nreg 8748 = Ab)
    (hA : ∀ i < m, c.nmem (Ab + i) = A i) (hlt : ∀ i < m, A i < m)
    (hinj : ∀ i < m, ∀ j < m, A i = A j → i = j)
    (hdis : Ab + m ≤ Ob ∨ Ob + m ≤ Ab) (w1 : Ob + m ≤ W) (w2 : Ab + m ≤ W) :
    ∃ c' t, Exec P W scatL c c' t ∧ t ≤ 7 * m + 3 ∧
      (∀ i < m, c'.nmem (Ob + A i) = i) ∧
      (∀ a, ¬ (Ob ≤ a ∧ a < Ob + m) → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 8740 → x ≠ 8743 → x ≠ 8745 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, v1, n1, m1, rr1, rm1, o1⟩ := cst_exec (P := P) (r := 8740) (v := 0)
    c hc (Nat.zero_le _)
  let J : ℕ → Config → Prop := fun i d =>
    (∀ j < i, d.nmem (Ob + A j) = j) ∧
      (∀ a, (∀ j < i, a ≠ Ob + A j) → d.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 8740 → x ≠ 8743 → x ≠ 8745 → d.nreg x = c.nreg x) ∧
      d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h40, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 8740)
    (b := 8741) (body := block [.addN 8743 8748 8740, .loadN 8745 8743, .addN 8743 8742 8745,
      .storeN 8743 8740, .addN 8740 8740 8704]) J (B := 5) c₁ e₁.wb_right v1
    (by rw [n1 _ (by omega)]; exact r1) (Nat.zero_le m)
    ⟨fun j hj => absurd hj (by omega), fun a _ => by rw [m1],
      fun x h1 h2 h3 => n1 x h1, rr1, rm1, o1⟩
    (fun i d hlo hhi hw hci hbn ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have q48 : d.nreg 8748 = Ab := by rw [j3 _ (by omega) (by omega) (by omega), r4]
      have q42 : d.nreg 8742 = Ob := by rw [j3 _ (by omega) (by omega) (by omega), r3]
      have q04 : d.nreg 8704 = 1 := by rw [j3 _ (by omega) (by omega) (by omega), r2]
      have hAi : d.nmem (Ab + i) = A i := by
        rw [j2 _ (fun j hj e => by
          have := hlt j (by omega); rcases hdis with h | h <;> omega)]
        exact hA i hhi
      have hli := hlt i hhi
      exec_block
      · config_simp; rw [q48, hci]; omega
      · config_simp; rw [q48, hci, hAi, q42]; omega
      · config_simp; rw [hci, q04]; omega
      refine ⟨by omega, ?_, ?_, ⟨fun j hj => ?_, fun a ha => ?_, fun x h1 h2 h3 => ?_,
        ?_, ?_, ?_⟩⟩
      · config_simp; rw [hci, q04]
      · config_simp; exact hbn
      · config_simp; rw [q48, hci, hAi, q42]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · have hne : Ob + A j ≠ Ob + A i := fun e =>
            absurd (hinj j (by omega) i hhi (by omega)) (by omega)
          rw [upd_other _ _ _ hne]; exact j1 j hj
        · rw [upd_same]
      · config_simp; rw [q48, hci, hAi, q42]
        rw [upd_other _ _ _ (ha i (by omega))]
        exact j2 a (fun j hj => ha j (by omega))
      · config_simp; simp (disch := omega) only [upd_other]; exact j3 x h1 h2 h3
      · config_simp; exact j4
      · config_simp; exact j5
      · config_simp; exact j6)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by rw [Nat.sub_zero] at hk₂; omega, j1,
    fun a ha => j2 a (fun j hj e => ha ⟨by omega, by have := hlt j (by omega); omega⟩), j3,
    j4, j5, j6⟩

end Pp

end BKMNW

end PlanarFlow
