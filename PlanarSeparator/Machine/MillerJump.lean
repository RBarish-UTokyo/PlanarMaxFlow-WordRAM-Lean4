module

public import PlanarSeparator.Machine.MillerMarks

/-!
# Miller's separator on the machine: depths and root sums without an order

The pass `rspass` of `PlanarSeparator/Machine/MillerRoot.lean` needs an order of the vertices in
which parents come first. The breadth-first order of step 1 is such an order for the
breadth-first tree `T`, but not for the redirected tree `T₁` of the inner region (step 6), whose
parents along the boundary cycle are not one level up. This file computes the depths and the root
sums of any tree by **pointer jumping** along the table of ancestors of
`PlanarSeparator/Machine/MillerLCA.lean` (`f^[2 ^ j] v` at `bU + j n + v`):

* `upass` stores the parents (the root fixed) at `bU` from the parent darts (`upass_exec`,
  `14 n + 3` steps);
* `jpass` starts from `D₀ v = [v ≠ r₀]`, `S₀ v = [v ≠ r₀] w v` and doubles: after round `j`,
  `D_j v = Σ_{i < 2^j} [f^[i] v ≠ r₀]` and `S_j v = Σ_{i < 2^j} [f^[i] v ≠ r₀] w (f^[i] v)`
  (`Dj`, `Sj`, `Dj_succ`); after `L` rounds, with `f^[2^L] v = r₀`, these are the depths and the
  root sums less `w r₀` (`dpRec_Dj`, `rsRec_Sj`). Within `(30 n + 10) L + 22 n + 10` steps
  (`jpass_exec`).

For a spanning tree read through the coding, the depths are `#(anc v) - 1` and the root sums
`∑ u ∈ anc v, w u` (`jpass_tree`), with no order of the vertices.

Registers: `r140 = 0`, `r141 = 1`, `r161 = n`, `r250 = bW`, `r252 = bS`, `r253 = bD`, `r254 = bU`,
`r255 = r₀`, `r271 = L`, `r381 = bD₂`, `r382 = bS₂` (scratch arrays); the programs write
`r380`, `r383 … r389`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace PlanarSeparator

namespace MillerProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### Doubling sums -/

/-- `1` off the root. -/
def gN (r₀ u : ℕ) : ℕ := if u = r₀ then 0 else 1

/-- The weight off the root. -/
def wN (w : ℕ → ℕ) (r₀ u : ℕ) : ℕ := if u = r₀ then 0 else w u

/-- The number of the first `2 ^ j` iterated parents of `v` other than the root. -/
def Dj (f : ℕ → ℕ) (r₀ j v : ℕ) : ℕ := ∑ i ∈ range (2 ^ j), gN r₀ (f^[i] v)

/-- The weight of the first `2 ^ j` iterated parents of `v` other than the root. -/
def Sj (f w : ℕ → ℕ) (r₀ j v : ℕ) : ℕ := ∑ i ∈ range (2 ^ j), wN w r₀ (f^[i] v)

theorem sum_double (h f : ℕ → ℕ) (j v : ℕ) :
    ∑ i ∈ range (2 ^ (j + 1)), h (f^[i] v) =
      ∑ i ∈ range (2 ^ j), h (f^[i] v) + ∑ i ∈ range (2 ^ j), h (f^[i] (f^[2 ^ j] v)) := by
  rw [pow_succ, mul_two, sum_range_add]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [← Function.iterate_add_apply, add_comm]

theorem Dj_succ (f : ℕ → ℕ) (r₀ j v : ℕ) : Dj f r₀ (j + 1) v = Dj f r₀ j v + Dj f r₀ j (f^[2 ^ j] v) :=
  sum_double _ f j v

theorem Sj_succ (f w : ℕ → ℕ) (r₀ j v : ℕ) :
    Sj f w r₀ (j + 1) v = Sj f w r₀ j v + Sj f w r₀ j (f^[2 ^ j] v) :=
  sum_double _ f j v

theorem Dj_zero (f : ℕ → ℕ) (r₀ v : ℕ) : Dj f r₀ 0 v = gN r₀ v := by simp [Dj]

theorem Sj_zero (f w : ℕ → ℕ) (r₀ v : ℕ) : Sj f w r₀ 0 v = wN w r₀ v := by simp [Sj]

theorem Dj_mono (f : ℕ → ℕ) (r₀ : ℕ) {j j' : ℕ} (h : j ≤ j') (v : ℕ) : Dj f r₀ j v ≤ Dj f r₀ j' v :=
  sum_le_sum_of_subset (range_subset_range.2 (Nat.pow_le_pow_right (by omega) h))

theorem Sj_mono (f w : ℕ → ℕ) (r₀ : ℕ) {j j' : ℕ} (h : j ≤ j') (v : ℕ) :
    Sj f w r₀ j v ≤ Sj f w r₀ j' v :=
  sum_le_sum_of_subset (range_subset_range.2 (Nat.pow_le_pow_right (by omega) h))

theorem iter_fix {f : ℕ → ℕ} {r₀ : ℕ} (h : f r₀ = r₀) (m : ℕ) : f^[m] r₀ = r₀ := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, h, ih]

/-- The last step of a doubling sum: once the root is reached, the sum from `v` is the term at
`v` plus the sum from its parent. -/
theorem sum_last (h f : ℕ → ℕ) (r₀ : ℕ) (hr : h r₀ = 0) {N v : ℕ} (hN : 1 ≤ N)
    (hv : f^[N] v = r₀) :
    ∑ i ∈ range N, h (f^[i] v) = h v + ∑ i ∈ range N, h (f^[i] (f v)) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [sum_range_succ', sum_range_succ]
  have e : f^[M] (f v) = r₀ := by rw [← Function.iterate_succ_apply]; exact hv
  have : ∀ i, f^[i + 1] v = f^[i] (f v) := fun i => Function.iterate_succ_apply f i v
  rw [e, hr]
  simp only [this, Function.iterate_zero, id_eq]
  omega

/-- **After `L` rounds the doubling counts are the depths.** -/
theorem dpRec_Dj {n r₀ L : ℕ} {f : ℕ → ℕ} (hr : f r₀ = r₀)
    (hL : ∀ v < n, f^[2 ^ L] v = r₀) : DpRec n r₀ f (Dj f r₀ L) := by
  refine ⟨?_, fun v hv hne => ?_⟩
  · unfold Dj; refine sum_eq_zero fun i _ => ?_; rw [iter_fix hr]; simp [gN]
  · unfold Dj
    rw [sum_last _ f r₀ (by simp [gN]) (Nat.one_le_two_pow) (hL v hv)]
    simp [gN, hne]; omega

/-- **After `L` rounds the doubling sums are the root sums less the weight of the root.** -/
theorem rsRec_Sj {n r₀ L : ℕ} {f w : ℕ → ℕ} (hr : f r₀ = r₀)
    (hL : ∀ v < n, f^[2 ^ L] v = r₀) : RsRec n r₀ f w (fun v => Sj f w r₀ L v + w r₀) := by
  refine ⟨?_, fun v hv hne => ?_⟩
  · simp only
    have : Sj f w r₀ L r₀ = 0 := by
      unfold Sj; refine sum_eq_zero fun i _ => ?_; rw [iter_fix hr]; simp [wN]
    rw [this, zero_add]
  · simp only
    unfold Sj
    rw [sum_last _ f r₀ (by simp [wN]) (Nat.one_le_two_pow) (hL v hv)]
    simp [wN, hne]; omega

/-- **Uniqueness of the solutions of a recurrence along the parents.** -/
theorem rec_unique {n r₀ : ℕ} {f g R R' : ℕ → ℕ} (hf : ∀ v < n, f v < n)
    (ht : ∀ v < n, ∃ m, f^[m] v = r₀) (h0 : R r₀ = R' r₀)
    (h1 : ∀ v < n, v ≠ r₀ → R v = R (f v) + g v) (h2 : ∀ v < n, v ≠ r₀ → R' v = R' (f v) + g v) :
    ∀ v < n, R v = R' v := by
  suffices key : ∀ m v, v < n → f^[m] v = r₀ → R v = R' v from fun v hv =>
    let ⟨m, hm⟩ := ht v hv; key m v hv hm
  intro m
  induction m with
  | zero => intro v _ hv; simp at hv; rw [hv, h0]
  | succ m ih =>
    intro v hv hm
    by_cases hne : v = r₀
    · rw [hne, h0]
    · rw [Function.iterate_succ_apply] at hm
      rw [h1 v hv hne, h2 v hv hne, ih (f v) (hf v hv) hm]

/-! ### The programs -/

/-- **The parent** of `r380 = v` at `bU + v` (the root `r₀` fixed). -/
def ubody : Stmt :=
  .seq (.ifLtN 380 255 (block [.addN 385 215 380, .loadN 386 385, .addN 385 147 386,
      .loadN 386 385, .addN 385 162 386, .loadN 386 385])
    (.ifLtN 255 380 (block [.addN 385 215 380, .loadN 386 385, .addN 385 147 386,
      .loadN 386 385, .addN 385 162 386, .loadN 386 385]) (.instr (.copyN 386 380))))
    (block [.addN 385 254 380, .storeN 385 386, .addN 380 380 141])

/-- **The parents.** -/
def upass : Stmt := .seq (.instr (.copyN 380 140)) (.whileLtN 380 161 ubody)

/-- The start of the doubling at `r380 = v`: `D v := [v ≠ r₀]`, `S v := [v ≠ r₀] w v`. -/
def jinit : Stmt :=
  .seq (.ifLtN 380 255 (block [.copyN 387 141, .addN 385 250 380, .loadN 388 385])
    (.ifLtN 255 380 (block [.copyN 387 141, .addN 385 250 380, .loadN 388 385])
      (block [.copyN 387 140, .copyN 388 140])))
    (block [.addN 385 253 380, .storeN 385 387, .addN 385 252 380, .storeN 385 388,
      .addN 380 380 141])

/-- One vertex of a round: `D₂ v := D v + D p`, `S₂ v := S v + S p` for `p = f^[2^j] v`
(level `j` of the table at `r384`). -/
def jinner : Stmt :=
  block [.addN 385 384 380, .loadN 386 385, .addN 385 253 380, .loadN 387 385,
    .addN 385 253 386, .loadN 388 385, .addN 387 387 388, .addN 385 252 380, .loadN 388 385,
    .addN 385 252 386, .loadN 389 385, .addN 388 388 389, .addN 385 381 380, .storeN 385 387,
    .addN 385 382 380, .storeN 385 388, .addN 380 380 141]

/-- Copy back `D₂`, `S₂`. -/
def jcopy : Stmt :=
  block [.addN 385 381 380, .loadN 387 385, .addN 385 382 380, .loadN 388 385,
    .addN 385 253 380, .storeN 385 387, .addN 385 252 380, .storeN 385 388, .addN 380 380 141]

/-- One round `r383 = j`. -/
def jouter : Stmt :=
  .seq (.instr (.copyN 380 140)) <| .seq (.whileLtN 380 161 jinner) <|
  .seq (.instr (.copyN 380 140)) <| .seq (.whileLtN 380 161 jcopy) <|
  block [.addN 384 384 161, .addN 383 383 141]

/-- The end: `S v := S v + w r₀`. -/
def jfinal : Stmt :=
  block [.addN 385 250 255, .loadN 389 385, .addN 385 252 380, .loadN 387 385,
    .addN 387 387 389, .storeN 385 387, .addN 380 380 141]

/-- **Depths and root sums by pointer jumping.** -/
def jpass : Stmt :=
  .seq (.instr (.copyN 380 140)) <| .seq (.whileLtN 380 161 jinit) <|
  .seq (block [.copyN 383 140, .copyN 384 254]) <| .seq (.whileLtN 383 271 jouter) <|
  .seq (.instr (.copyN 380 140)) (.whileLtN 380 161 jfinal)

/-! ### The parents -/

section upass

variable {W : ℕ} {P : Input} {k n r₀ bR bV bPr bU : ℕ} {A V Pr : ℕ → ℕ}

/-- **The parents.** From the parent darts at `bPr` (reversals at `bR`, vertices at `bV`), within
`14 n + 3` steps `bU + v` holds `upN A V Pr r₀ v` for every `v < n`. -/
theorem upass_exec (hin : RootIn k n r₀ A V Pr)
    (hlay : bR + 3 * k ≤ bU ∧ bV + 3 * k ≤ bU ∧ bPr + n ≤ bU ∧ bU + n ≤ W) (c : Config)
    (hc : WordsBounded W c) (h140 : c.nreg 140 = 0) (h141 : c.nreg 141 = 1)
    (h147 : c.nreg 147 = bR) (h161 : c.nreg 161 = n) (h162 : c.nreg 162 = bV)
    (h215 : c.nreg 215 = bPr) (h254 : c.nreg 254 = bU) (h255 : c.nreg 255 = r₀)
    (mA : ∀ x < 3 * k, c.nmem (bR + x) = A x) (mV : ∀ x < 3 * k, c.nmem (bV + x) = V x)
    (mP : ∀ v < n, v ≠ r₀ → c.nmem (bPr + v) = Pr v) :
    ∃ c' t, Exec P W upass c c' t ∧ t ≤ 14 * n + 3 ∧
      (∀ v < n, c'.nmem (bU + v) = upN A V Pr r₀ v) ∧
      (∀ r, r ≠ 380 → r ≠ 385 → r ≠ 386 → c'.nreg r = c.nreg r) ∧
      (∀ a, a < bU ∨ bU + n ≤ a → c'.nmem a = c.nmem a) ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4⟩ := hlay
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.nreg 380 = i ∧ i ≤ n ∧
    (∀ r, r ≠ 380 → r ≠ 385 → r ≠ 386 → c'.nreg r = c.nreg r) ∧
    (∀ a, a < bU ∨ bU + n ≤ a → c'.nmem a = c.nmem a) ∧
    (∀ u < i, c'.nmem (bU + u) = upN A V Pr r₀ u) ∧ c'.output = c.output
  have e₁ := Exec.copyN (P := P) hc 380 140
  obtain ⟨c', t, e, hI, ht⟩ := Exec.forN (P := P) (W := W) (ri := 380) (rN := 161) (N := n)
    (lo := 0) (B := 12) (body := ubody) I
    (fun i c' h => ⟨h.1, h.2.1, (h.2.2.2.1 161 (by omega) (by omega) (by omega)).trans h161⟩)
    (fun i c₁ ⟨hw, h380, hi, hr, hm, hd, ho⟩ hlt => by
      have hc := hw
      have g141 := (hr 141 (by omega) (by omega) (by omega)).trans h141
      have g147 := (hr 147 (by omega) (by omega) (by omega)).trans h147
      have g162 := (hr 162 (by omega) (by omega) (by omega)).trans h162
      have g215 := (hr 215 (by omega) (by omega) (by omega)).trans h215
      have g254 := (hr 254 (by omega) (by omega) (by omega)).trans h254
      have g255 := (hr 255 (by omega) (by omega) (by omega)).trans h255
      -- the parent in `r386`
      have par : ∃ c₂ t₂, Exec P W (.ifLtN 380 255 (block [.addN 385 215 380, .loadN 386 385,
          .addN 385 147 386, .loadN 386 385, .addN 385 162 386, .loadN 386 385])
          (.ifLtN 255 380 (block [.addN 385 215 380, .loadN 386 385, .addN 385 147 386,
            .loadN 386 385, .addN 385 162 386, .loadN 386 385]) (.instr (.copyN 386 380)))) c₁ c₂ t₂ ∧
          t₂ ≤ 9 ∧ WordsBounded W c₂ ∧ c₂.nreg 386 = upN A V Pr r₀ i ∧
          (∀ r, r ≠ 385 → r ≠ 386 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
          c₂.output = c₁.output := by
        have gen : i ≠ r₀ → ∃ c₂ t₂, Exec P W (block [.addN 385 215 380, .loadN 386 385,
            .addN 385 147 386, .loadN 386 385, .addN 385 162 386, .loadN 386 385]) c₁ c₂ t₂ ∧
            t₂ = 6 ∧ WordsBounded W c₂ ∧ c₂.nreg 386 = upN A V Pr r₀ i ∧
            (∀ r, r ≠ 385 → r ≠ 386 → c₂.nreg r = c₁.nreg r) ∧ c₂.nmem = c₁.nmem ∧
            c₂.output = c₁.output := by
          intro hne
          have hP := hin.Pr_lt i hlt hne
          have hA := hin.A_lt _ hP
          have m1 : c₁.nmem (bPr + i) = Pr i := by rw [hm _ (Or.inl (by omega))]; exact mP i hlt hne
          have m2 : c₁.nmem (bR + Pr i) = A (Pr i) := by rw [hm _ (Or.inl (by omega))]; exact mA _ hP
          have m3 : c₁.nmem (bV + A (Pr i)) = V (A (Pr i)) := by
            rw [hm _ (Or.inl (by omega))]; exact mV _ hA
          exec_block
          all_goals try (config_simp; simp only [g215, h380, m1, g147, m2, g162]; omega)
          refine ⟨rfl, ‹_›, ?_, fun r a b => ?_, rfl, rfl⟩
          all_goals config_simp
          · simp only [g215, h380, m1, g147, m2, g162, m3, upN, hne, ↓reduceIte]; rfl
          · simp only [upd_apply]; split_ifs <;> first | omega | rfl
        rcases Nat.lt_trichotomy i r₀ with h | h | h
        · obtain ⟨c₂, t₂, e₂, rfl, rest⟩ := gen (by omega)
          exact ⟨c₂, 6 + 1, .ifLtN_true (by rw [h380, g255]; exact h) e₂, by omega, rest⟩
        · have e₂ := Exec.copyN (P := P) hw 386 380
          refine ⟨_, 1 + 2 + 2, .ifLtN_false (by rw [h380, g255]; omega)
            (.ifLtN_false (by rw [h380, g255]; omega) e₂), by omega, e₂.wb_right, ?_,
            fun r a b => ?_, rfl, rfl⟩
          all_goals config_simp
          · rw [h380, h]; simp [upN]
          · rw [upd_other _ _ _ b]
        · obtain ⟨c₂, t₂, e₂, rfl, rest⟩ := gen (by omega)
          exact ⟨c₂, 6 + 1 + 2, .ifLtN_false (by rw [h380, g255]; omega)
            (.ifLtN_true (by rw [h380, g255]; exact h) e₂), by omega, rest⟩
      obtain ⟨c₂, t₂, e₂, ht₂, hw₂, g386, fr₂, hm₂, ho₂⟩ := par
      have k254 := (fr₂ 254 (by omega) (by omega)).trans g254
      have k380 := (fr₂ 380 (by omega) (by omega)).trans h380
      have k141 := (fr₂ 141 (by omega) (by omega)).trans g141
      obtain ⟨c₃, t₃, e₃, hI₃, rfl⟩ : ∃ c₃ t₃, Exec P W
          (block [.addN 385 254 380, .storeN 385 386, .addN 380 380 141]) c₂ c₃ t₃ ∧
          I (i + 1) c₃ ∧ t₃ = 3 := by
        have hc := hw₂
        exec_block
        all_goals try (config_simp; simp only [k254, k380, k141]; omega)
        refine ⟨⟨‹_›, ?_, by omega, fun r a b d => ?_, fun a ha => ?_, fun u hu => ?_, ?_⟩, rfl⟩
        all_goals config_simp
        · rw [k380, k141]
        · simp only [upd_apply]; split_ifs <;> first | omega | (rw [fr₂ r b d]; exact hr r a b d)
        · rw [k254, k380, upd_other _ _ _ (by omega), hm₂]; exact hm a ha
        · rw [k254, k380, g386]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
          · rw [upd_other _ _ _ (by omega), hm₂]; exact hd u hu
          · rw [upd_same]
        · rw [ho₂]; exact ho
      exact ⟨c₃, t₂ + 3, .seq e₂ e₃, hI₃, by omega⟩)
    (by omega) ⟨e₁.wb_right, by config_simp; exact h140, by omega,
      fun r a _ _ => by config_simp; rw [upd_other _ _ _ a], fun a _ => rfl,
      fun u hu => absurd hu (by omega), rfl⟩
  obtain ⟨-, -, -, hr, hm, hd, ho⟩ := hI
  exact ⟨c', 1 + t, .seq e₁ e, by omega, hd, hr, hm, ho⟩

end upass

/-! ### The doubling -/

/-- The registers and the memory `jpass` reads, and its layout. -/
structure JFix (n r₀ bW bS bD bU L bD₂ bS₂ W : ℕ) (f w : ℕ → ℕ) (c : Config) : Prop where
  r140 : c.nreg 140 = 0
  r141 : c.nreg 141 = 1
  r161 : c.nreg 161 = n
  r250 : c.nreg 250 = bW
  r252 : c.nreg 252 = bS
  r253 : c.nreg 253 = bD
  r254 : c.nreg 254 = bU
  r255 : c.nreg 255 = r₀
  r271 : c.nreg 271 = L
  r381 : c.nreg 381 = bD₂
  r382 : c.nreg 382 = bS₂
  tab : Tab n bU L f c.nmem
  mW : ∀ v < n, c.nmem (bW + v) = w v
  r₀_lt : r₀ < n
  f_lt : ∀ v < n, f v < n
  hL : 1 ≤ L
  l1 : bU + L * n ≤ bW
  l2 : bW + n ≤ bD
  l3 : bD + n ≤ bS
  l4 : bS + n ≤ bD₂
  l5 : bD₂ + n ≤ bS₂
  l6 : bS₂ + n ≤ W
  hDW : ∀ v < n, Dj f r₀ L v ≤ W
  hSW : ∀ v < n, Sj f w r₀ L v + w r₀ ≤ W

section jpass

variable {W : ℕ} {P : Input} {n r₀ bW bS bD bU L bD₂ bS₂ : ℕ} {f w : ℕ → ℕ} {c₀ : Config}
  (hF : JFix n r₀ bW bS bD bU L bD₂ bS₂ W f w c₀)
include hF

/-- The registers `jpass` keeps. -/
def JR (c₀ c : Config) : Prop :=
  ∀ r, r ≠ 380 → r ≠ 383 → r ≠ 384 → r ≠ 385 → r ≠ 386 → r ≠ 387 → r ≠ 388 → r ≠ 389 →
    c.nreg r = c₀.nreg r

omit hF in
theorem JR.get {c : Config} (h : JR c₀ c) {r : ℕ} (hr : r ≠ 380 ∧ (r < 383 ∨ 389 < r)) :
    c.nreg r = c₀.nreg r :=
  h r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- The state of the start loop. -/
structure JI0 (i : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  r380 : c.nreg 380 = i
  le : i ≤ n
  regs : JR c₀ c
  mem : ∀ a, a < bD ∨ bS + n ≤ a → c.nmem a = c₀.nmem a
  out : c.output = c₀.output
  done : ∀ u < i, c.nmem (bD + u) = Dj f r₀ 0 u ∧ c.nmem (bS + u) = Sj f w r₀ 0 u

set_option maxHeartbeats 2000000 in
theorem jinit_exec (i : ℕ) (c : Config) (hI : JI0 (W := W) (n := n) (bD := bD) (bS := bS)
    (r₀ := r₀) (f := f) (w := w) (c₀ := c₀) i c) (hi : i < n) :
    ∃ c' t, Exec P W jinit c c' t ∧ JI0 (W := W) (n := n) (bD := bD) (bS := bS) (r₀ := r₀) (f := f)
      (w := w) (c₀ := c₀) (i + 1) c' ∧ t ≤ 11 := by
  have hc := hI.wb
  have g := hI.regs
  have g140 := (g.get (by omega)).trans hF.r140
  have g141 := (g.get (by omega)).trans hF.r141
  have g250 := (g.get (by omega)).trans hF.r250
  have g252 := (g.get (by omega)).trans hF.r252
  have g253 := (g.get (by omega)).trans hF.r253
  have g255 := (g.get (by omega)).trans hF.r255
  have l2 := hF.l2
  have l3 := hF.l3
  have l6 := hF.l6
  have l4 := hF.l4
  have l5 := hF.l5
  have mw : c.nmem (bW + i) = w i := by rw [hI.mem _ (Or.inl (by omega))]; exact hF.mW i hi
  have hwle : w i ≤ W := by have := hc.2 (bW + i); rw [mw] at this; exact this
  -- the two values in `r387`, `r388`
  have val : ∃ c₂ t₂, Exec P W (.ifLtN 380 255 (block [.copyN 387 141, .addN 385 250 380,
      .loadN 388 385]) (.ifLtN 255 380 (block [.copyN 387 141, .addN 385 250 380, .loadN 388 385])
        (block [.copyN 387 140, .copyN 388 140]))) c c₂ t₂ ∧ t₂ ≤ 6 ∧ WordsBounded W c₂ ∧
      c₂.nreg 387 = gN r₀ i ∧ c₂.nreg 388 = wN w r₀ i ∧
      (∀ r, r ≠ 385 → r ≠ 387 → r ≠ 388 → c₂.nreg r = c.nreg r) ∧ c₂.nmem = c.nmem ∧
      c₂.output = c.output := by
    have gen : i ≠ r₀ → ∃ c₂ t₂, Exec P W (block [.copyN 387 141, .addN 385 250 380,
        .loadN 388 385]) c c₂ t₂ ∧ t₂ = 3 ∧ WordsBounded W c₂ ∧ c₂.nreg 387 = gN r₀ i ∧
        c₂.nreg 388 = wN w r₀ i ∧ (∀ r, r ≠ 385 → r ≠ 387 → r ≠ 388 → c₂.nreg r = c.nreg r) ∧
        c₂.nmem = c.nmem ∧ c₂.output = c.output := by
      intro hne
      exec_block
      · config_simp; rw [g250, hI.r380]; omega
      refine ⟨rfl, ‹_›, ?_, ?_, fun r a b d => ?_, rfl, rfl⟩
      all_goals config_simp
      · rw [g141]; simp [gN, hne]
      · rw [g250, hI.r380, mw]; simp [wN, hne]
      · simp only [upd_apply]; split_ifs <;> first | omega | rfl
    rcases Nat.lt_trichotomy i r₀ with h | h | h
    · obtain ⟨c₂, t₂, e₂, rfl, rest⟩ := gen (by omega)
      exact ⟨c₂, 3 + 1, .ifLtN_true (by rw [hI.r380, g255]; exact h) e₂, by omega, rest⟩
    · obtain ⟨c₂, t₂, e₂, rest, rfl⟩ : ∃ c₂ t₂, Exec P W (block [.copyN 387 140, .copyN 388 140])
          c c₂ t₂ ∧ (WordsBounded W c₂ ∧ c₂.nreg 387 = gN r₀ i ∧ c₂.nreg 388 = wN w r₀ i ∧
          (∀ r, r ≠ 385 → r ≠ 387 → r ≠ 388 → c₂.nreg r = c.nreg r) ∧ c₂.nmem = c.nmem ∧
          c₂.output = c.output) ∧ t₂ = 2 := by
        exec_block
        refine ⟨⟨‹_›, ?_, ?_, fun r a b d => ?_, rfl, rfl⟩, rfl⟩
        all_goals config_simp
        · rw [g140, h]; simp [gN]
        · rw [g140, h]; simp [wN]
        · simp only [upd_apply]; split_ifs <;> first | omega | rfl
      exact ⟨c₂, 2 + 2 + 2, .ifLtN_false (by rw [hI.r380, g255]; omega)
        (.ifLtN_false (by rw [hI.r380, g255]; omega) e₂), by omega, rest⟩
    · obtain ⟨c₂, t₂, e₂, rfl, rest⟩ := gen (by omega)
      exact ⟨c₂, 3 + 1 + 2, .ifLtN_false (by rw [hI.r380, g255]; omega)
        (.ifLtN_true (by rw [hI.r380, g255]; exact h) e₂), by omega, rest⟩
  obtain ⟨c₂, t₂, e₂, ht₂, hw₂, g387, g388, fr₂, hm₂, ho₂⟩ := val
  have k252 := (fr₂ 252 (by omega) (by omega) (by omega)).trans g252
  have k253 := (fr₂ 253 (by omega) (by omega) (by omega)).trans g253
  have k380 := (fr₂ 380 (by omega) (by omega) (by omega)).trans hI.r380
  have k141 := (fr₂ 141 (by omega) (by omega) (by omega)).trans g141
  have hgle : gN r₀ i ≤ 1 := by unfold gN; split_ifs <;> omega
  have hwNle : wN w r₀ i ≤ W := by unfold wN; split_ifs <;> omega
  obtain ⟨c₃, t₃, e₃, hI₃, rfl⟩ : ∃ c₃ t₃, Exec P W (block [.addN 385 253 380, .storeN 385 387,
      .addN 385 252 380, .storeN 385 388, .addN 380 380 141]) c₂ c₃ t₃ ∧
      JI0 (W := W) (n := n) (bD := bD) (bS := bS) (r₀ := r₀) (f := f) (w := w) (c₀ := c₀) (i + 1) c₃ ∧
      t₃ = 5 := by
    have hc := hw₂
    exec_block
    all_goals try (config_simp; simp only [k252, k253, k380, k141]; omega)
    refine ⟨⟨‹_›, ?_, by omega, fun r a b d e f' g' h' i' => ?_, fun a ha => ?_, ?_,
      fun u hu => ?_⟩, rfl⟩
    all_goals config_simp
    · rw [k380, k141]
    · simp only [upd_apply]; split_ifs <;> first | omega | (rw [fr₂ r e g' h']; exact g r a b d e f' g' h' i')
    · rw [k252, k253, k380, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), hm₂]
      exact hI.mem a ha
    · rw [ho₂]; exact hI.out
    · rw [k252, k253, k380, g387, g388, Dj_zero, Sj_zero]
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
      · have := hI.done u hu; rw [Dj_zero, Sj_zero, ← hm₂] at this
        constructor
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact this.1
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact this.2
      · rw [upd_other _ _ _ (by omega), upd_same, upd_same]; exact ⟨rfl, rfl⟩
  exact ⟨c₃, t₂ + 5, .seq e₂ e₃, hI₃, by omega⟩

/-- The state between rounds: after `j` rounds. -/
structure JO (j : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  r383 : c.nreg 383 = j
  r384 : c.nreg 384 = bU + j * n
  le : j ≤ L
  regs : JR c₀ c
  mem : ∀ a, a < bD ∨ bS₂ + n ≤ a → c.nmem a = c₀.nmem a
  out : c.output = c₀.output
  cur : ∀ v < n, c.nmem (bD + v) = Dj f r₀ j v ∧ c.nmem (bS + v) = Sj f w r₀ j v

/-- Within a round, the first loop. -/
structure JA (j : ℕ) (cᵣ : Config) (i : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  r380 : c.nreg 380 = i
  le : i ≤ n
  regs : ∀ r, r ≠ 380 → r ≠ 385 → r ≠ 386 → r ≠ 387 → r ≠ 388 → r ≠ 389 → c.nreg r = cᵣ.nreg r
  mem : ∀ a, ¬ (bD₂ ≤ a ∧ a < bS₂ + n) → c.nmem a = cᵣ.nmem a
  out : c.output = cᵣ.output
  done : ∀ u < i, c.nmem (bD₂ + u) = Dj f r₀ (j + 1) u ∧ c.nmem (bS₂ + u) = Sj f w r₀ (j + 1) u

/-- Within a round, the copy. -/
structure JB (j : ℕ) (cₐ : Config) (i : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  r380 : c.nreg 380 = i
  le : i ≤ n
  regs : ∀ r, r ≠ 380 → r ≠ 385 → r ≠ 387 → r ≠ 388 → c.nreg r = cₐ.nreg r
  mem : ∀ a, ¬ ((bD ≤ a ∧ a < bD + n) ∨ (bS ≤ a ∧ a < bS + n)) → c.nmem a = cₐ.nmem a
  out : c.output = cₐ.output
  done : ∀ u < i, c.nmem (bD + u) = Dj f r₀ (j + 1) u ∧ c.nmem (bS + u) = Sj f w r₀ (j + 1) u

set_option maxHeartbeats 2000000 in
theorem jinner_exec {j : ℕ} {cᵣ : Config} (hO : JO (W := W) (n := n) (bD := bD) (bS := bS)
    (bU := bU) (L := L) (bS₂ := bS₂) (r₀ := r₀) (f := f) (w := w) (c₀ := c₀) j cᵣ) (hj : j < L)
    (i : ℕ) (c : Config) (hI : JA (W := W) (n := n) (bD₂ := bD₂) (bS₂ := bS₂) (r₀ := r₀) (f := f)
      (w := w) j cᵣ i c) (hi : i < n) :
    ∃ c' t, Exec P W jinner c c' t ∧ JA (W := W) (n := n) (bD₂ := bD₂) (bS₂ := bS₂) (r₀ := r₀)
      (f := f) (w := w) j cᵣ (i + 1) c' ∧ t ≤ 17 := by
  have hc := hI.wb
  have gr : ∀ r, r ≠ 380 ∧ (r < 383 ∨ 389 < r) → c.nreg r = c₀.nreg r := fun r hr => by
    rw [hI.regs r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hO.regs.get hr
  have g141 := (gr 141 (by omega)).trans hF.r141
  have g252 := (gr 252 (by omega)).trans hF.r252
  have g253 := (gr 253 (by omega)).trans hF.r253
  have g381 := (gr 381 (by omega)).trans hF.r381
  have g382 := (gr 382 (by omega)).trans hF.r382
  have g384 : c.nreg 384 = bU + j * n := by
    rw [hI.regs 384 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hO.r384
  have l1 := hF.l1
  have l2 := hF.l2
  have l3 := hF.l3
  have l4 := hF.l4
  have l5 := hF.l5
  have l6 := hF.l6
  have hjn : j * n + n ≤ L * n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  have hp : f^[2 ^ j] i < n := iter_lt_of hF.f_lt _ hi
  have mp : c.nmem (bU + j * n + i) = f^[2 ^ j] i := by
    rw [hI.mem _ (by omega), hO.mem _ (Or.inl (by omega))]; exact hF.tab j hj i hi
  have m1 : c.nmem (bD + i) = Dj f r₀ j i := by
    rw [hI.mem _ (by omega)]; exact (hO.cur i hi).1
  have m2 : c.nmem (bD + f^[2 ^ j] i) = Dj f r₀ j (f^[2 ^ j] i) := by
    rw [hI.mem _ (by omega)]; exact (hO.cur _ hp).1
  have m3 : c.nmem (bS + i) = Sj f w r₀ j i := by
    rw [hI.mem _ (by omega)]; exact (hO.cur i hi).2
  have m4 : c.nmem (bS + f^[2 ^ j] i) = Sj f w r₀ j (f^[2 ^ j] i) := by
    rw [hI.mem _ (by omega)]; exact (hO.cur _ hp).2
  have hD := (Dj_succ f r₀ j i).symm.trans_le ((Dj_mono f r₀ (show j + 1 ≤ L by omega) i).trans
    (hF.hDW i hi))
  have hS := (Sj_succ f w r₀ j i).symm.trans_le ((Sj_mono f w r₀ (show j + 1 ≤ L by omega) i).trans
    (show Sj f w r₀ L i ≤ W by have := hF.hSW i hi; omega))
  unfold jinner
  exec_block
  all_goals try (config_simp; simp only [g384, hI.r380, mp, g253, m1, m2, g252, m3, m4, g381,
    g382, g141]; omega)
  refine ⟨⟨‹_›, ?_, by omega, fun r a b d e f' g' => ?_, fun a ha => ?_, hI.out, fun u hu => ?_⟩,
    le_rfl⟩
  all_goals config_simp
  · rw [hI.r380, g141]
  · simp only [upd_apply]; split_ifs <;> first | omega | exact hI.regs r a b d e f' g'
  · simp only [g384, hI.r380, mp, g253, m1, m2, g252, m3, m4, g381, g382]
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hI.mem a ha
  · simp only [g384, hI.r380, mp, g253, m1, m2, g252, m3, m4, g381, g382]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
    · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
        upd_other _ _ _ (by omega)]
      exact hI.done u hu
    · rw [upd_other _ _ _ (by omega), upd_same, upd_same, Dj_succ, Sj_succ]; exact ⟨rfl, rfl⟩

set_option maxHeartbeats 2000000 in
theorem jcopy_exec {j : ℕ} {cᵣ cₐ : Config} (hO : JO (W := W) (n := n) (bD := bD) (bS := bS)
    (bU := bU) (L := L) (bS₂ := bS₂) (r₀ := r₀) (f := f) (w := w) (c₀ := c₀) j cᵣ)
    (hA : JA (W := W) (n := n) (bD₂ := bD₂) (bS₂ := bS₂) (r₀ := r₀) (f := f) (w := w) j cᵣ n cₐ)
    (i : ℕ) (c : Config) (hI : JB (W := W) (n := n) (bD := bD) (bS := bS) (r₀ := r₀) (f := f)
      (w := w) j cₐ i c) (hi : i < n) :
    ∃ c' t, Exec P W jcopy c c' t ∧ JB (W := W) (n := n) (bD := bD) (bS := bS) (r₀ := r₀) (f := f)
      (w := w) j cₐ (i + 1) c' ∧ t ≤ 9 := by
  have hc := hI.wb
  have gr : ∀ r, r ≠ 380 ∧ (r < 383 ∨ 389 < r) → c.nreg r = c₀.nreg r := fun r hr => by
    rw [hI.regs r (by omega) (by omega) (by omega) (by omega),
      hA.regs r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hO.regs.get hr
  have g141 := (gr 141 (by omega)).trans hF.r141
  have g252 := (gr 252 (by omega)).trans hF.r252
  have g253 := (gr 253 (by omega)).trans hF.r253
  have g381 := (gr 381 (by omega)).trans hF.r381
  have g382 := (gr 382 (by omega)).trans hF.r382
  have l3 := hF.l3
  have l4 := hF.l4
  have l5 := hF.l5
  have l6 := hF.l6
  have m1 : c.nmem (bD₂ + i) = Dj f r₀ (j + 1) i := by
    rw [hI.mem _ (by omega)]; exact (hA.done i hi).1
  have m2 : c.nmem (bS₂ + i) = Sj f w r₀ (j + 1) i := by
    rw [hI.mem _ (by omega)]; exact (hA.done i hi).2
  unfold jcopy
  exec_block
  all_goals try (config_simp; simp only [hI.r380, g253, g252, g381, g382, g141]; omega)
  refine ⟨⟨‹_›, ?_, by omega, fun r a b d e => ?_, fun a ha => ?_, hI.out, fun u hu => ?_⟩,
    le_rfl⟩
  all_goals config_simp
  · rw [hI.r380, g141]
  · simp only [upd_apply]; split_ifs <;> first | omega | exact hI.regs r a b d e
  · simp only [hI.r380, g253, g252, g381, g382]
    rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hI.mem a ha
  · simp only [hI.r380, g253, g252, g381, g382, m1, m2]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
    · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
        upd_other _ _ _ (by omega)]
      exact hI.done u hu
    · rw [upd_other _ _ _ (by omega), upd_same, upd_same]; exact ⟨rfl, rfl⟩

/-- **One round.** -/
theorem jouter_exec (j : ℕ) (c : Config) (hO : JO (W := W) (n := n) (bD := bD) (bS := bS)
    (bU := bU) (L := L) (bS₂ := bS₂) (r₀ := r₀) (f := f) (w := w) (c₀ := c₀) j c) (hj : j < L) :
    ∃ c' t, Exec P W jouter c c' t ∧ JO (W := W) (n := n) (bD := bD) (bS := bS) (bU := bU) (L := L)
      (bS₂ := bS₂) (r₀ := r₀) (f := f) (w := w) (c₀ := c₀) (j + 1) c' ∧ t ≤ 30 * n + 8 := by
  have hc := hO.wb
  have g140 := (hO.regs.get (by omega)).trans hF.r140
  have g161 := (hO.regs.get (by omega)).trans hF.r161
  have g141 := (hO.regs.get (by omega)).trans hF.r141
  have l1 := hF.l1
  have l2 := hF.l2
  have l3 := hF.l3
  have l4 := hF.l4
  have l5 := hF.l5
  have l6 := hF.l6
  -- the first loop
  have e₁ := Exec.copyN (P := P) hc 380 140
  obtain ⟨c₂, t₂, e₂, hA, ht₂⟩ := Exec.forN (P := P) (W := W) (ri := 380) (rN := 161) (N := n)
    (lo := 0) (B := 17) (body := jinner)
    (JA (W := W) (n := n) (bD₂ := bD₂) (bS₂ := bS₂) (r₀ := r₀) (f := f) (w := w) j c)
    (fun i c' h => ⟨h.wb, h.r380, by
      rw [h.regs 161 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact g161⟩)
    (fun i c' h hi => jinner_exec hF hO hj i c' h hi) (by omega)
    ⟨e₁.wb_right, by config_simp; exact g140, by omega,
      fun r a _ _ _ _ _ => by config_simp; rw [upd_other _ _ _ a], fun a _ => rfl, rfl,
      fun u hu => absurd hu (by omega)⟩
  -- the copy
  have hw₂ := hA.wb
  have e₃ := Exec.copyN (P := P) hw₂ 380 140
  have k140 : c₂.nreg 140 = 0 := by
    rw [hA.regs 140 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact g140
  have k161 : c₂.nreg 161 = n := by
    rw [hA.regs 161 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact g161
  obtain ⟨c₄, t₄, e₄, hB, ht₄⟩ := Exec.forN (P := P) (W := W) (ri := 380) (rN := 161) (N := n)
    (lo := 0) (B := 9) (body := jcopy)
    (JB (W := W) (n := n) (bD := bD) (bS := bS) (r₀ := r₀) (f := f) (w := w) j c₂)
    (fun i c' h => ⟨h.wb, h.r380, by
      rw [h.regs 161 (by omega) (by omega) (by omega) (by omega)]; exact k161⟩)
    (fun i c' h hi => jcopy_exec hF hO hA i c' h hi) (by omega)
    ⟨e₃.wb_right, by config_simp; exact k140, by omega,
      fun r a _ _ _ => by config_simp; rw [upd_other _ _ _ a], fun a _ => rfl, rfl,
      fun u hu => absurd hu (by omega)⟩
  have hw₄ := hB.wb
  have regs₄ : ∀ r, r ≠ 380 → r ≠ 385 → r ≠ 386 → r ≠ 387 → r ≠ 388 → r ≠ 389 →
      c₄.nreg r = c.nreg r := fun r a b d e f' g' => by
    rw [hB.regs r a b e f', hA.regs r a b d e f' g']
  have k384 : c₄.nreg 384 = bU + j * n := by
    rw [regs₄ 384 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hO.r384
  have k383 : c₄.nreg 383 = j := by
    rw [regs₄ 383 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hO.r383
  have k161' : c₄.nreg 161 = n := by
    rw [regs₄ 161 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact g161
  have k141 : c₄.nreg 141 = 1 := by
    rw [regs₄ 141 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact g141
  have hjn : j * n + n ≤ L * n := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hj
  have hLW : L ≤ W := by
    have : L ≤ L * n := Nat.le_mul_of_pos_right L (by have := hF.r₀_lt; omega)
    omega
  obtain ⟨c₅, t₅, e₅, hO₅, rfl⟩ : ∃ c₅ t₅, Exec P W (block [.addN 384 384 161, .addN 383 383 141])
      c₄ c₅ t₅ ∧ JO (W := W) (n := n) (bD := bD) (bS := bS) (bU := bU) (L := L) (bS₂ := bS₂)
        (r₀ := r₀) (f := f) (w := w) (c₀ := c₀) (j + 1) c₅ ∧ t₅ = 2 := by
    have hc := hw₄
    exec_block
    · config_simp; rw [k384, k161']; omega
    · config_simp; rw [k383, k141]; omega
    refine ⟨⟨‹_›, ?_, ?_, by omega, fun r a b d e f' g' h' i' => ?_, fun a ha => ?_, ?_,
      fun v hv => ?_⟩, rfl⟩
    all_goals config_simp
    · rw [k383, k141]
    · rw [k384, k161', add_assoc, ← Nat.succ_mul]
    · rw [upd_other _ _ _ b, upd_other _ _ _ d, regs₄ r a e f' g' h' i']
      exact hO.regs r a b d e f' g' h' i'
    · rw [hB.mem a (by omega), hA.mem a (by omega)]; exact hO.mem a ha
    · rw [hB.out, hA.out, hO.out]
    · exact hB.done v hv
  exact ⟨c₅, 1 + (t₂ + (1 + (t₄ + 2))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), hO₅, by omega⟩

/-- The end loop. -/
structure JF (cᵣ : Config) (i : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  r380 : c.nreg 380 = i
  le : i ≤ n
  regs : ∀ r, r ≠ 380 → r ≠ 385 → r ≠ 387 → r ≠ 389 → c.nreg r = cᵣ.nreg r
  mem : ∀ a, ¬ (bS ≤ a ∧ a < bS + i) → c.nmem a = cᵣ.nmem a
  out : c.output = cᵣ.output
  done : ∀ u < i, c.nmem (bS + u) = Sj f w r₀ L u + w r₀

set_option maxHeartbeats 1000000 in
theorem jfinal_exec {cᵣ : Config} (hO : JO (W := W) (n := n) (bD := bD) (bS := bS)
    (bU := bU) (L := L) (bS₂ := bS₂) (r₀ := r₀) (f := f) (w := w) (c₀ := c₀) L cᵣ) (i : ℕ)
    (c : Config) (hI : JF (W := W) (n := n) (bS := bS) (r₀ := r₀) (L := L) (f := f) (w := w) cᵣ i c)
    (hi : i < n) :
    ∃ c' t, Exec P W jfinal c c' t ∧ JF (W := W) (n := n) (bS := bS) (r₀ := r₀) (L := L) (f := f)
      (w := w) cᵣ (i + 1) c' ∧ t ≤ 7 := by
  have hc := hI.wb
  have gr : ∀ r, r ≠ 380 ∧ (r < 383 ∨ 389 < r) → c.nreg r = c₀.nreg r := fun r hr => by
    rw [hI.regs r (by omega) (by omega) (by omega) (by omega)]; exact hO.regs.get hr
  have g141 := (gr 141 (by omega)).trans hF.r141
  have g250 := (gr 250 (by omega)).trans hF.r250
  have g252 := (gr 252 (by omega)).trans hF.r252
  have g255 := (gr 255 (by omega)).trans hF.r255
  have l2 := hF.l2
  have l3 := hF.l3
  have l6 := hF.l6
  have l4 := hF.l4
  have l5 := hF.l5
  have hr₀ := hF.r₀_lt
  have mw : c.nmem (bW + r₀) = w r₀ := by
    rw [hI.mem _ (by omega), hO.mem _ (Or.inl (by omega))]; exact hF.mW _ hr₀
  have ms : c.nmem (bS + i) = Sj f w r₀ L i := by
    rw [hI.mem _ (by omega)]; exact (hO.cur i hi).2
  have hS := hF.hSW i hi
  unfold jfinal
  exec_block
  all_goals try (config_simp; simp only [g250, g255, mw, g252, hI.r380, ms, g141]; omega)
  refine ⟨⟨‹_›, ?_, by omega, fun r a b d e => ?_, fun a ha => ?_, hI.out, fun u hu => ?_⟩, le_rfl⟩
  all_goals config_simp
  · rw [hI.r380, g141]
  · simp only [upd_apply]; split_ifs <;> first | omega | exact hI.regs r a b d e
  · simp only [g250, g255, mw, g252, hI.r380, ms]
    rw [upd_other _ _ _ (by omega)]; exact hI.mem a (by omega)
  · simp only [g250, g255, mw, g252, hI.r380, ms]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hu with hu | rfl
    · rw [upd_other _ _ _ (by omega)]; exact hI.done u hu
    · rw [upd_same]

/-- **Depths and root sums by pointer jumping.** With the table of the `2 ^ j`-th ancestors
(`j < L`) of a function `f` (fixing the root `r₀`) and the weights in memory (`JFix`), within
`(30 n + 10) L + 22 n + 10` steps `bD + v` holds `Dj f r₀ L v` and `bS + v` holds
`Sj f w r₀ L v + w r₀` for every `v < n`. -/
theorem jpass_exec (hc₀ : WordsBounded W c₀) :
    ∃ c' t, Exec P W jpass c₀ c' t ∧ t ≤ (30 * n + 10) * L + 22 * n + 10 ∧
      (∀ v < n, c'.nmem (bD + v) = Dj f r₀ L v ∧ c'.nmem (bS + v) = Sj f w r₀ L v + w r₀) ∧
      JR c₀ c' ∧ (∀ a, a < bD ∨ bS₂ + n ≤ a → c'.nmem a = c₀.nmem a) ∧
      c'.output = c₀.output := by
  have l1 := hF.l1
  have l2 := hF.l2
  have l3 := hF.l3
  have l4 := hF.l4
  have l5 := hF.l5
  have l6 := hF.l6
  -- the start
  have e₁ := Exec.copyN (P := P) hc₀ 380 140
  obtain ⟨c₂, t₂, e₂, h₂, ht₂⟩ := Exec.forN (P := P) (W := W) (ri := 380) (rN := 161) (N := n)
    (lo := 0) (B := 11) (body := jinit)
    (JI0 (W := W) (n := n) (bD := bD) (bS := bS) (r₀ := r₀) (f := f) (w := w) (c₀ := c₀))
    (fun i c' h => ⟨h.wb, h.r380, (h.regs.get (by omega)).trans hF.r161⟩)
    (fun i c' h hi => jinit_exec hF i c' h hi) (by omega)
    ⟨e₁.wb_right, by config_simp; exact hF.r140, by omega,
      fun r a _ _ _ _ _ _ _ => by config_simp; rw [upd_other _ _ _ a], fun a _ => rfl, rfl,
      fun u hu => absurd hu (by omega)⟩
  have hw₂ := h₂.wb
  -- the rounds
  obtain ⟨c₃, t₃, e₃, hO₃, rfl⟩ : ∃ c₃ t₃, Exec P W (block [.copyN 383 140, .copyN 384 254]) c₂ c₃ t₃ ∧
      JO (W := W) (n := n) (bD := bD) (bS := bS) (bU := bU) (L := L) (bS₂ := bS₂) (r₀ := r₀)
        (f := f) (w := w) (c₀ := c₀) 0 c₃ ∧ t₃ = 2 := by
    have hc := hw₂
    exec_block
    refine ⟨⟨‹_›, ?_, ?_, by omega, fun r a b d e f' g' h' i' => ?_, fun a ha => ?_, h₂.out,
      fun v hv => ?_⟩, rfl⟩
    all_goals config_simp
    · rw [h₂.regs.get (by omega)]; exact hF.r140
    · rw [h₂.regs.get (by omega)]; simp [hF.r254]
    · rw [upd_other _ _ _ d, upd_other _ _ _ b]; exact h₂.regs r a b d e f' g' h' i'
    · exact h₂.mem a (by omega)
    · exact h₂.done v hv
  obtain ⟨c₄, t₄, e₄, hO₄, ht₄⟩ := Exec.forN (P := P) (W := W) (ri := 383) (rN := 271) (N := L)
    (lo := 0) (B := 30 * n + 8) (body := jouter)
    (JO (W := W) (n := n) (bD := bD) (bS := bS) (bU := bU) (L := L) (bS₂ := bS₂) (r₀ := r₀)
      (f := f) (w := w) (c₀ := c₀))
    (fun j c' h => ⟨h.wb, h.r383, (h.regs.get (by omega)).trans hF.r271⟩)
    (fun j c' h hj => jouter_exec hF j c' h hj) (by omega) hO₃
  -- the end
  have hw₄ := hO₄.wb
  have e₅ := Exec.copyN (P := P) hw₄ 380 140
  obtain ⟨c₆, t₆, e₆, hF₆, ht₆⟩ := Exec.forN (P := P) (W := W) (ri := 380) (rN := 161) (N := n)
    (lo := 0) (B := 7) (body := jfinal)
    (JF (W := W) (n := n) (bS := bS) (r₀ := r₀) (L := L) (f := f) (w := w) c₄)
    (fun i c' h => ⟨h.wb, h.r380, by
      rw [h.regs 161 (by omega) (by omega) (by omega) (by omega)]
      exact (hO₄.regs.get (by omega)).trans hF.r161⟩)
    (fun i c' h hi => jfinal_exec hF hO₄ i c' h hi) (by omega)
    ⟨e₅.wb_right, by config_simp; exact (hO₄.regs.get (by omega)).trans hF.r140, by omega,
      fun r a _ _ _ => by config_simp; rw [upd_other _ _ _ a], fun a _ => rfl, rfl,
      fun u hu => absurd hu (by omega)⟩
  refine ⟨c₆, 1 + (t₂ + (2 + (t₄ + (1 + t₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), ?_, fun v hv => ⟨?_, hF₆.done v hv⟩,
    fun r a b d e f' g' h' i' => ?_, fun a ha => ?_, ?_⟩
  · have : (30 * n + 8 + 2) * (L - 0) = (30 * n + 10) * L := by rw [Nat.sub_zero]
    omega
  · rw [hF₆.mem _ (by omega)]; exact (hO₄.cur v hv).1
  · rw [hF₆.regs r a e g' i', hO₄.regs r a b d e f' g' h' i']
  · rw [hF₆.mem a (by omega)]; exact hO₄.mem a ha
  · rw [hF₆.out, hO₄.out]

end jpass

/-! ### The bridge to spanning trees -/

section Bridge

open Map

variable {D Q : Type*} [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q] {M : Map D Q}
  {n : ℕ} (vi : Q ≃ Fin n) (T : M.SpTree) {f w : ℕ → ℕ} (wv : Q → ℕ) {L : ℕ}
  (hf : ∀ x, f (vi x) = vi (T.parent x)) (hw : ∀ x, w (vi x) = wv x) (hnL : n ≤ 2 ^ L)
include hf hnL

omit [Fintype D] in
theorem iter_root_tree : ∀ v < n, f^[2 ^ L] v = vi T.root := by
  have hT := ptree_tree vi T hf (dep := ofV vi fun v => #(T.anc v) - 1) (fun x => ofV_vi vi _ x)
  intro v hv
  exact hT.iter_of_le hv (by have := hT.dep_lt v hv; omega)

omit [Fintype D] in
/-- **The doubling counts of a spanning tree are its depths.** -/
theorem Dj_tree (x : Q) : Dj f (vi T.root) L (vi x) = #(T.anc x) - 1 := by
  have hT := ptree_tree vi T hf (dep := ofV vi fun v => #(T.anc v) - 1) (fun x => ofV_vi vi _ x)
  have hr : f (vi T.root) = vi T.root := hT.f_r₀
  have h1 := dpRec_Dj (n := n) (L := L) hr (iter_root_tree vi T hf hnL)
  have e := rec_unique (n := n) (r₀ := vi T.root) (f := f) (g := fun _ => 1)
    (R := Dj f (vi T.root) L) (R' := ofV vi fun v => #(T.anc v) - 1) hT.f_lt
    (fun v hv => ⟨_, iter_root_tree vi T hf hnL v hv⟩) (by rw [h1.1, hT.dep_r₀]) h1.2
    (fun v hv hne => (hT.dep_f v hv hne).symm) (vi x) (vi x).2
  rw [e, ofV_vi]

include hw in
omit [Fintype D] in
/-- **The doubling sums of a spanning tree are its root sums.** -/
theorem Sj_tree (x : Q) : Sj f w (vi T.root) L (vi x) + w (vi T.root) = ∑ u ∈ T.anc x, wv u := by
  have hT := ptree_tree vi T hf (dep := ofV vi fun v => #(T.anc v) - 1) (fun x => ofV_vi vi _ x)
  have hr : f (vi T.root) = vi T.root := hT.f_r₀
  have h1 := rsRec_Sj (n := n) (L := L) (w := w) hr (iter_root_tree vi T hf hnL)
  have h2 : ∀ v < n, v ≠ vi T.root → (ofV vi fun v => ∑ u ∈ T.anc v, wv u) v =
      (ofV vi fun v => ∑ u ∈ T.anc v, wv u) (f v) + w v := fun v hv hne => by
    obtain ⟨y, rfl⟩ := exists_vi vi hv
    have hy : y ≠ T.root := fun e => hne (by rw [e])
    rw [hf, ofV_vi, ofV_vi, hw, T.anc_of_ne hy,
      sum_insert (SpTree.notMem_anc_parent (T := T) hy), add_comm]
  have e := rec_unique (n := n) (r₀ := vi T.root) (f := f) (g := w)
    (R := fun v => Sj f w (vi T.root) L v + w (vi T.root))
    (R' := ofV vi fun v => ∑ u ∈ T.anc v, wv u) hT.f_lt
    (fun v hv => ⟨_, iter_root_tree vi T hf hnL v hv⟩)
    (by have := h1.1; simp only at this; rw [this, ofV_vi, T.anc_root, sum_singleton, hw])
    h1.2 h2 (vi x) (vi x).2
  rw [e, ofV_vi]

include hw in
/-- **Depths and root sums of a spanning tree without an order.** With the table of the
ancestors of a spanning tree `T` (the parents `f` read through `vi`; `n ≤ 2 ^ L`) and the weights
in memory, `jpass` stores the depths `#(anc v) - 1` and the root sums `∑ u ∈ anc v, wv u`,
within `(30 n + 10) L + 22 n + 10` steps. -/
theorem jpass_tree {W : ℕ} {P' : Input} {bW bS bD bU bD₂ bS₂ : ℕ} {c₀ : Config}
    (hF : JFix n (vi T.root) bW bS bD bU L bD₂ bS₂ W f w c₀) (hc₀ : WordsBounded W c₀) :
    ∃ c' t, Exec P' W jpass c₀ c' t ∧ t ≤ (30 * n + 10) * L + 22 * n + 10 ∧
      (∀ x, c'.nmem (bD + vi x) = #(T.anc x) - 1 ∧ c'.nmem (bS + vi x) = ∑ u ∈ T.anc x, wv u) ∧
      JR c₀ c' ∧ (∀ a, a < bD ∨ bS₂ + n ≤ a → c'.nmem a = c₀.nmem a) ∧
      c'.output = c₀.output := by
  obtain ⟨c', t, e, ht, hd, hr, hm, ho⟩ := jpass_exec (P := P') hF hc₀
  refine ⟨c', t, e, ht, fun x => ?_, hr, hm, ho⟩
  obtain ⟨h1, h2⟩ := hd (vi x) (vi x).2
  rw [h1, h2, Dj_tree vi T hf hnL, Sj_tree vi T wv hf hw hnL]
  exact ⟨rfl, rfl⟩

end Bridge

end MillerProg

end PlanarSeparator
