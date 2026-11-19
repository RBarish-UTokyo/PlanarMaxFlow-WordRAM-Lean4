module

public import PlanarFlow.Monge.SmawkUp

/-!
# SMAWK on the machine: the whole run

`smawk ent` computes the leftmost row minima of an `m × n` totally monotone matrix given by an
entry oracle `ent`, with `O(E (m + n))` steps (`E` the cost of an entry): the algorithm of
Aggarwal, Klawe, Moran, Shor and Wilber.

1. The identity list `0, 1, …, n` is written at `pb + 4m + 1`.
2. **Down.** For `s = 1, 2, 4, …, ≤ m`, the list of the level `s / 2` (the identity list for
   `s = 1`) is reduced for the rows `s, 2s, …` (`PlanarFlow.Monge.reduce_exec`); the reduced list
   of the level `s` is stored at the cells `pb + m + (2k + 1) s`, which are distinct for distinct
   levels and positions (`odd_pow_inj`).
3. **Up.** For `s` from the largest level down to `1`, the rows `s, 3s, 5s, …` are found by
   interpolation (`PlanarFlow.Monge.upRows_exec`).

The reduction at the level `s` costs `O(E)` per column of its input list, which has `n` columns
for `s = 1` and at most `2m / s` for the other levels; the interpolation at the level `s` costs
`O(E m / s)`. Summing the geometric series gives the bound.

**`PlanarFlow.Monge.smawk_exec`.** With `m, n ≥ 1` in `r60, r61`, the output base `pb` in `r62`,
`pb + 4m + n + 2 ≤ W` and an entry oracle of cost `≤ E` using the frame `Agree pb (4m + n + 1)`,
`smawk ent` runs within `(20E + 320)(m + n + 1)` steps and leaves, for every row `i < m`, the
position `lmin n A i` at `pb + i + 1` of the natural memory and the value `A i (lmin n A i)` at
`pb + i + 1` of the real memory; the memory outside `pb + 1, …, pb + 4m + n + 1`, the registers
below `60` and the output are unchanged.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The program -/

/-- The identity list `0, 1, …, n` at `r67`. -/
def initId : Stmt :=
  .seq (.instr (.constN 79 0)) <|
  .seq (.whileLtN 79 61 (block [.addN 78 67 79, .storeN 78 79, .addN 79 79 63])) <|
  block [.addN 78 67 61, .storeN 78 61]

/-- One level of the way down: reduce the input list for the rows of the level `s = r65`. -/
def downLevel (ent : Stmt) : Stmt :=
  .seq (block [.divN 74 60 65, .addN 69 62 60, .addN 69 69 65, .addN 72 65 65]) <|
  .seq (reduce ent) <|
  block [.copyN 67 69, .copyN 68 72, .addN 65 65 65]

/-- One level of the way up: `s := s / 2`, then the rows `s, 3s, 5s, …`. -/
def upLevel (ent : Stmt) : Stmt :=
  .seq (block [.divN 65 65 64, .addN 69 62 60, .addN 69 69 65, .addN 72 65 65]) (upRows ent)

/-- **SMAWK.** -/
def smawk (ent : Stmt) : Stmt :=
  .seq (block [.constN 63 1, .constN 64 2, .addN 66 60 63, .addN 67 62 60, .addN 67 67 60,
    .addN 67 67 60, .addN 67 67 60, .addN 67 67 63, .constN 68 1]) <|
  .seq initId <|
  .seq (.instr (.constN 65 1)) <|
  .seq (.whileLtN 65 66 (downLevel ent)) <|
  .whileLtN 63 65 (upLevel ent)

/-! ### The cells of the lists -/

/-- **The odd part and the power of two of a number are unique.** -/
theorem odd_pow_inj {u v : ℕ} : ∀ {a b : ℕ}, (2 * u + 1) * 2 ^ a = (2 * v + 1) * 2 ^ b →
    a = b ∧ u = v := by
  intro a
  induction a with
  | zero =>
    intro b h
    rcases b with _ | b
    · simp at h; exact ⟨rfl, by omega⟩
    · rw [pow_succ, pow_zero] at h
      have : (2 * v + 1) * (2 ^ b * 2) = 2 * ((2 * v + 1) * 2 ^ b) := by ring
      omega
  | succ a ih =>
    intro b h
    rcases b with _ | b
    · rw [pow_succ, pow_zero] at h
      have : (2 * u + 1) * (2 ^ a * 2) = 2 * ((2 * u + 1) * 2 ^ a) := by ring
      omega
    · have h' : (2 * u + 1) * 2 ^ a = (2 * v + 1) * 2 ^ b := by
        rw [pow_succ, pow_succ] at h
        have e1 : (2 * u + 1) * (2 ^ a * 2) = 2 * ((2 * u + 1) * 2 ^ a) := by ring
        have e2 : (2 * v + 1) * (2 ^ b * 2) = 2 * ((2 * v + 1) * 2 ^ b) := by ring
        omega
      obtain ⟨h1, h2⟩ := ih h'
      exact ⟨by omega, h2⟩

/-- The cell of the position `k` of the list of the level `2 ^ a`. -/
lemma cell_eq (pb m a k : ℕ) :
    pb + m + 2 ^ a + k * (2 * 2 ^ a) = pb + m + (2 * k + 1) * 2 ^ a := by ring

lemma cell_ne {pb m a b k k' : ℕ} (h : a ≠ b) :
    pb + m + 2 ^ a + k * (2 * 2 ^ a) ≠ pb + m + 2 ^ b + k' * (2 * 2 ^ b) := by
  rw [cell_eq, cell_eq]
  intro e
  exact h (odd_pow_inj (Nat.add_left_cancel e)).1

lemma cell_le {m s k : ℕ} (hs : 0 < s) (hk : k ≤ m / s) : s + k * (2 * s) ≤ 2 * m + s := by
  have := Nat.div_mul_le_self m s
  have := Nat.mul_le_mul_right s hk
  nlinarith

/-- The list of the level `s` is in memory: increasing, ended by the sentinel `n`, of length at
most `m / s`, containing the leftmost minima of the rows of the level. -/
def LevOK (A : ℕ → ℕ → ℝ) (m n pb : ℕ) (c : Config) (s : ℕ) : Prop :=
  ∃ t ≤ m / s, IsCols n (fun k => c.nmem (pb + m + s + k * (2 * s))) t ∧
    ∀ k < m / s, ∃ u < t, c.nmem (pb + m + s + u * (2 * s)) = lmin n A (rowL s k)

lemma LevOK.of_mem {A : ℕ → ℕ → ℝ} {m n pb s : ℕ} {c c' : Config} (h : LevOK A m n pb c s)
    (hm : ∀ k ≤ m / s, c'.nmem (pb + m + s + k * (2 * s)) = c.nmem (pb + m + s + k * (2 * s))) :
    LevOK A m n pb c' s := by
  obtain ⟨t, ht, ⟨h1, h2⟩, h3⟩ := h
  refine ⟨t, ht, ⟨fun i j hij hj => ?_, ?_⟩, fun k hk => ?_⟩
  · beta_reduce; rw [hm i (by omega), hm j (by omega)]; exact h1 i j hij hj
  · beta_reduce; rw [hm t ht]; exact h2
  · obtain ⟨u, hu, e⟩ := h3 k hk
    exact ⟨u, hu, by rw [hm u (by omega)]; exact e⟩

/-! ### The identity list -/

variable {P : Input} {W : ℕ} {ent : Stmt} {A : ℕ → ℕ → ℝ} {E m n pb K : ℕ} {c₀ : Config}

/-- The state of the writing of the identity list at `inB`. -/
structure IId (W pb K n inB : ℕ) (c₀ c₁ c : Config) : Prop where
  wb : WordsBounded W c
  agree : Agree pb K c₀ c
  nreg : ∀ r, r ≠ 78 → r ≠ 79 → c.nreg r = c₁.nreg r
  rreg : c.rreg = c₁.rreg
  rmem : c.rmem = c₁.rmem
  out : c.output = c₁.output
  nmem : ∀ a, (a < inB ∨ inB + n < a) → c.nmem a = c₁.nmem a
  jle : c.nreg 79 ≤ n
  done : ∀ j < c.nreg 79, c.nmem (inB + j) = j

theorem initId_exec {inB : ℕ} {c₁ : Config} (hc : WordsBounded W c₁) (hA₁ : Agree pb K c₀ c₁)
    (h67 : c₁.nreg 67 = inB) (h61 : c₁.nreg 61 = n) (h63 : c₁.nreg 63 = 1) (hpb : pb < inB)
    (hK : inB + n ≤ pb + K) (hW : pb + K ≤ W) :
    ∃ c' k, Exec P W initId c₁ c' k ∧ k ≤ 5 * n + 5 ∧
      (Agree pb K c₀ c' ∧ (∀ r, r ≠ 78 → r ≠ 79 → c'.nreg r = c₁.nreg r) ∧ c'.rreg = c₁.rreg ∧
        c'.rmem = c₁.rmem ∧ c'.output = c₁.output ∧
        (∀ a, (a < inB ∨ inB + n < a) → c'.nmem a = c₁.nmem a) ∧
        ∀ j ≤ n, c'.nmem (inB + j) = j) := by
  unfold initId
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 79 0 (Nat.zero_le _)) fun hw₁ => ?_
  refine spec_seq ?_
  refine spec_while (IId W pb K n inB c₀ c₁) (fun c => 5 * (n - c.nreg 79)) (fun c h => h.wb)
    (fun c hI hlt => ?_) ⟨hw₁, hA₁.of_eq (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)])
      (fun _ _ => rfl) rfl rfl rfl, fun r _ h => by config_simp; rw [upd_other _ _ _ h], rfl, rfl,
      rfl, fun _ _ => rfl, by config_simp; omega, fun j hj => by config_simp at hj; omega⟩ ?_
  · have hw := hI.wb
    have g61 : c.nreg 61 = n := (hI.nreg 61 (by omega) (by omega)).trans h61
    have g63 : c.nreg 63 = 1 := (hI.nreg 63 (by omega) (by omega)).trans h63
    have g67 : c.nreg 67 = inB := (hI.nreg 67 (by omega) (by omega)).trans h67
    rw [g61] at hlt
    generalize hj : c.nreg 79 = j at hlt
    have hreg : pb < inB + j ∧ inB + j ≤ pb + K := ⟨by omega, by omega⟩
    exec_block
    · rw [g67, hj]; omega
    · config_simp; rw [hj, g63]; omega
    refine ⟨⟨‹_›, ?_, fun r a b => ?_, hI.rreg, hI.rmem, hI.out, fun a ha => ?_, ?_, fun j' hj' => ?_⟩,
      ?_⟩
    · obtain ⟨a1, a2, a3, a4, a5⟩ := hI.agree
      exact ⟨fun r hr => by config_simp; rw [upd_other _ _ _ (by omega),
        upd_other _ _ _ (by omega)]; exact a1 r hr, a2,
        fun a ha => by config_simp; rw [g67, hj, upd_other _ _ _ (by omega)]; exact a3 a ha, a4, a5⟩
    · config_simp; rw [upd_other _ _ _ b, upd_other _ _ _ a]; exact hI.nreg r a b
    · config_simp; rw [g67, hj, upd_other _ _ _ (by omega)]; exact hI.nmem a ha
    · config_simp; rw [hj, g63]; omega
    · config_simp at hj'; config_simp
      rw [hj, g63] at hj'
      rw [g67, hj]
      by_cases e : j' = j
      · subst e; rw [upd_same]
      · rw [upd_other _ _ _ (by omega)]; exact hI.done j' (by omega)
    · config_simp; rw [hj, g63]; omega
  intro c₂ k₂ hI₂ hn₂ hk₂
  have hw₂ := hI₂.wb
  have g61 : c₂.nreg 61 = n := (hI₂.nreg 61 (by omega) (by omega)).trans h61
  have g67 : c₂.nreg 67 = inB := (hI₂.nreg 67 (by omega) (by omega)).trans h67
  have h79 : c₂.nreg 79 = n := by have := hI₂.jle; rw [g61] at hn₂; omega
  exec_block
  · rw [g67, g61]; omega
  refine ⟨?_, ?_, fun r a b => ?_, hI₂.rreg, hI₂.rmem, hI₂.out, fun a ha => ?_, fun j hj => ?_⟩
  · beta_reduce at hk₂; config_simp at hk₂; omega
  · obtain ⟨a1, a2, a3, a4, a5⟩ := hI₂.agree
    exact ⟨fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]; exact a1 r hr, a2,
      fun a ha => by config_simp; rw [g67, g61, upd_other _ _ _ (by omega)]; exact a3 a ha, a4, a5⟩
  · config_simp; rw [upd_other _ _ _ a]; exact hI₂.nreg r a b
  · config_simp; rw [g67, g61, upd_other _ _ _ (by omega)]; exact hI₂.nmem a ha
  · config_simp; rw [g67, g61]
    by_cases e : j = n
    · subst e; rw [upd_same]
    · rw [upd_other _ _ _ (by omega)]; exact hI₂.done j (by omega)

/-! ### The way down -/

/-- The state between the levels of the way down, at the level `s = r65`. -/
structure IDn (W : ℕ) (A : ℕ → ℕ → ℝ) (m n pb K : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  agree : Agree pb K c₀ c
  r60 : c.nreg 60 = m
  r61 : c.nreg 61 = n
  r62 : c.nreg 62 = pb
  r63 : c.nreg 63 = 1
  r64 : c.nreg 64 = 2
  r66 : c.nreg 66 = m + 1
  pow : ∃ a, c.nreg 65 = 2 ^ a
  sle : c.nreg 65 ≤ 2 * m
  inp : (c.nreg 65 = 1 ∧ c.nreg 67 = pb + 4 * m + 1 ∧ c.nreg 68 = 1 ∧
      ∀ j ≤ n, c.nmem (pb + 4 * m + 1 + j * 1) = j) ∨
    (2 ≤ c.nreg 65 ∧ c.nreg 67 = pb + m + c.nreg 65 / 2 ∧ c.nreg 68 = c.nreg 65 ∧
      LevOK A m n pb c (c.nreg 65 / 2))
  levs : ∀ a, 2 ^ a < c.nreg 65 → LevOK A m n pb c (2 ^ a)

/-- The input list of a level of the way down. -/
theorem IDn.input {c : Config} (h : IDn W A m n pb K c₀ c) (hm : 0 < m) (hn : 0 < n)
    (hK : K = 4 * m + n + 1) (hsm : c.nreg 65 ≤ m) :
    ∃ N In, IsCols n In N ∧ (∀ k ≤ N, c.nmem (c.nreg 67 + k * c.nreg 68) = In k) ∧
      (∀ k < m / c.nreg 65, ∃ i' < N, In i' = lmin n A (rowL (c.nreg 65) k)) ∧
      (∀ u ≤ m / c.nreg 65, ∀ k ≤ N, pb + m + c.nreg 65 + u * (2 * c.nreg 65) ≠
        c.nreg 67 + k * c.nreg 68) ∧
      c.nreg 67 + N * c.nreg 68 ≤ pb + K ∧ 0 < c.nreg 68 ∧
      N ≤ (if c.nreg 65 = 1 then n else 2 * m / c.nreg 65) := by
  obtain ⟨a, ha⟩ := h.pow
  generalize hs : c.nreg 65 = s at ha hsm
  have hs0 : 0 < s := by rw [ha]; exact Nat.two_pow_pos a
  rcases h.inp with ⟨h1, h67, h68, hid⟩ | ⟨h2, h67, h68, hlev⟩
  · rw [hs] at h1
    subst h1
    refine ⟨n, fun j => j, isCols_id n, fun k hk => ?_, fun k hk => ⟨lmin n A (rowL 1 k),
      lmin_lt A _ hn, rfl⟩, fun u hu k hk => ?_, ?_, by rw [h68]; omega, by simp⟩
    · rw [h67, h68]; exact hid k hk
    · rw [h67, h68]; rw [Nat.div_one] at hu; simp only [Nat.mul_one]; omega
    · rw [h67, h68, hK]; omega
  · rw [hs] at h2 h67 h68 hlev
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by
      rcases a with _ | a
      · rw [ha] at h2; simp at h2
      · omega⟩
    have hs2 : s / 2 = 2 ^ a' := by rw [ha, pow_succ]; simp
    have hss : s = 2 * 2 ^ a' := by rw [ha, pow_succ, mul_comm]
    obtain ⟨t, ht, hcols, hmin⟩ := hlev
    rw [hs2] at hcols hmin ht
    refine ⟨t, fun k => c.nmem (pb + m + 2 ^ a' + k * (2 * 2 ^ a')), hcols, fun k hk => ?_,
      fun k hk => ?_, fun u hu k hk => ?_, ?_, by rw [h68]; omega, ?_⟩
    · rw [h67, h68, hs2, hss]
    · have hk' : 2 * k + 1 < m / 2 ^ a' := by
        have h1 := (Nat.le_div_iff_mul_le hs0).1 hk
        have h2 : 2 * k + 2 ≤ m / 2 ^ a' := by
          apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos a')).2
          rw [hss] at h1
          calc (2 * k + 2) * 2 ^ a' = (k + 1) * (2 * 2 ^ a') := by ring
            _ ≤ m := h1
        omega
      obtain ⟨u, hu, e⟩ := hmin (2 * k + 1) hk'
      refine ⟨u, hu, ?_⟩
      beta_reduce
      rw [e, hss, rowL_double]
    · rw [h67, h68, hs2]
      have := cell_ne (pb := pb) (m := m) (k := u) (k' := k) (show a' + 1 ≠ a' by omega)
      rw [ha, show k * 2 ^ (a' + 1) = k * (2 * 2 ^ a') by ring]
      exact this
    · rw [h67, h68, hs2, hK]
      have := cell_le (m := m) (s := 2 ^ a') (k := t) (Nat.two_pow_pos a') ht
      rw [hss]
      have : t * (2 * 2 ^ a') = t * (2 * 2 ^ a') := rfl
      omega
    · rw [ite_eq_right (by omega), hss, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]
      exact ht

/-- The potential of the way down. -/
def phiDown (E m n : ℕ) (c : Config) : ℕ :=
  (4 * E + 45) * (if c.nreg 65 = 1 then n else 0) + (4 * E + 55) * (4 * m / c.nreg 65)

theorem downLevel_exec (hent : EntSpecK P W ent A E m n pb K c₀) (hA : IsTotMono m n A)
    (hm : 0 < m) (hn : 0 < n) (hK : K = 4 * m + n + 1) (hW : pb + K + 1 ≤ W) (c : Config)
    (hI : IDn W A m n pb K c₀ c) (hlt : c.nreg 65 < c.nreg 66) :
    ∃ c' k, Exec P W (downLevel ent) c c' k ∧ IDn W A m n pb K c₀ c' ∧
      phiDown E m n c' + k + 2 ≤ phiDown E m n c := by
  have hc := hI.wb
  rw [hI.r66] at hlt
  have hsm : c.nreg 65 ≤ m := by omega
  obtain ⟨N, In, hcols, hin, hall, hdisj, hwin, hinS, hN⟩ := hI.input hm hn hK hsm
  obtain ⟨a, ha⟩ := hI.pow
  generalize hs : c.nreg 65 = s at ha hsm hall hdisj hN hlt
  have hs0 : 0 < s := by rw [ha]; exact Nat.two_pow_pos a
  generalize hinB : c.nreg 67 = inB at hin hdisj hwin
  generalize hinS' : c.nreg 68 = inS at hin hdisj hwin hinS
  have hp : 0 < m / s := Nat.div_pos hsm hs0
  have hps : m / s * s ≤ m := Nat.div_mul_le_self m s
  unfold downLevel
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hI.r62, hI.r60]; omega
  · config_simp; rw [hI.r62, hI.r60, hs]; omega
  · config_simp; rw [hs]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded W c₁ := hc₁ ▸ ‹_›
  have e₁ : ∀ r, r ≠ 69 → r ≠ 72 → r ≠ 74 → c₁.nreg r = c.nreg r := fun r a b d => by
    rw [← hc₁]; config_simp; rw [upd_other _ _ _ b, upd_other _ _ _ a, upd_other _ _ _ d]
  have hm₁ : c₁.nmem = c.nmem := by rw [← hc₁]
  have hD : RedData W n pb K s (m / s) inB inS (pb + m + s) (2 * s) N In c₁ := by
    refine ⟨(e₁ 61 (by omega) (by omega) (by omega)).trans hI.r61,
      (e₁ 63 (by omega) (by omega) (by omega)).trans hI.r63,
      (e₁ 65 (by omega) (by omega) (by omega)).trans hs, (e₁ 67 (by omega) (by omega)
      (by omega)).trans hinB, (e₁ 68 (by omega) (by omega) (by omega)).trans hinS',
      by rw [← hc₁]; config_simp; rw [hI.r62, hI.r60, hs],
      by rw [← hc₁]; config_simp; rw [hs, two_mul],
      by rw [← hc₁]; config_simp; rw [hI.r60, hs], fun k hk => by rw [hm₁]; exact hin k hk,
      hcols, fun u hu k hk => hdisj u hu k hk, fun u hu => ?_, ?_, ?_, by omega, by omega,
      hinS⟩
    · have := cell_le (m := m) hs0 hu; rw [hK]; constructor <;> omega
    · have := cell_le (m := m) hs0 le_rfl; rw [hK] at hW; omega
    · rw [hK] at hwin hW; omega
  have hA₁ : Agree pb K c₀ c₁ := hI.agree.of_eq (fun r hr => e₁ r (by omega) (by omega)
    (by omega)) (fun r _ => by rw [← hc₁]) hm₁ (by rw [← hc₁]) (by rw [← hc₁])
  refine spec_seq ?_
  refine spec_use (reduce_exec hent hA hs0 hps hp hD hall hw₁ hA₁) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hA₂, hn₂, hr₂, hnm₂, hrm₂, ho₂, t, ht, hcols₂, hmin₂⟩
  have f₂ : ∀ r, r < 67 → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hn₂ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), e₁ r (by omega) (by omega) (by omega)]
  have g69 : c₂.nreg 69 = pb + m + s := by
    rw [hn₂ 69 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), ← hD.r69]
  have g72 : c₂.nreg 72 = 2 * s := by
    rw [hn₂ 72 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega), ← hD.r72]
  have g65 : c₂.nreg 65 = s := (f₂ 65 (by omega)).trans hs
  exec_block
  · config_simp; rw [g65]; rw [hK] at hW; omega
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
  have hw₃ : WordsBounded W c₃ := hc₃ ▸ ‹_›
  have hm₃ : c₃.nmem = c₂.nmem := by rw [← hc₃]
  have e₃ : ∀ r, r ≠ 65 → r ≠ 67 → r ≠ 68 → c₃.nreg r = c₂.nreg r := fun r a b d => by
    rw [← hc₃]; config_simp; rw [upd_other _ _ _ a, upd_other _ _ _ d, upd_other _ _ _ b]
  have g65₃ : c₃.nreg 65 = 2 * s := by rw [← hc₃]; config_simp; rw [g65]; ring
  have g67₃ : c₃.nreg 67 = pb + m + s := by rw [← hc₃]; config_simp; exact g69
  have g68₃ : c₃.nreg 68 = 2 * s := by rw [← hc₃]; config_simp; exact g72
  have hLs : LevOK A m n pb c₃ s := ⟨t, ht, by rw [hm₃]; exact hcols₂, fun k hk => by
    rw [hm₃]; exact hmin₂ k hk⟩
  -- the lists of the lower levels are kept
  have hkeep : ∀ a', 2 ^ a' < s → LevOK A m n pb c₃ (2 ^ a') := by
    intro a' ha'
    have hne : a' ≠ a := by rintro rfl; rw [ha] at ha'; omega
    refine (hI.levs a' (by rw [hs]; exact ha')).of_mem fun k _ => ?_
    rw [hm₃, hnm₂ _ (fun u _ => by rw [ha]; exact (cell_ne hne)), hm₁]
  refine ⟨⟨hw₃, hA₂.of_eq (fun r hr => by rw [e₃ r (by omega) (by omega) (by omega)])
      (fun r _ => by rw [← hc₃]) hm₃ (by rw [← hc₃]) (by rw [← hc₃]),
    by rw [e₃ 60 (by omega) (by omega) (by omega), f₂ 60 (by omega)]; exact hI.r60,
    by rw [e₃ 61 (by omega) (by omega) (by omega), f₂ 61 (by omega)]; exact hI.r61,
    by rw [e₃ 62 (by omega) (by omega) (by omega), f₂ 62 (by omega)]; exact hI.r62,
    by rw [e₃ 63 (by omega) (by omega) (by omega), f₂ 63 (by omega)]; exact hI.r63,
    by rw [e₃ 64 (by omega) (by omega) (by omega), f₂ 64 (by omega)]; exact hI.r64,
    by rw [e₃ 66 (by omega) (by omega) (by omega), f₂ 66 (by omega)]; exact hI.r66,
    ⟨a + 1, by rw [g65₃, ha, pow_succ]; ring⟩, by rw [g65₃]; omega,
    Or.inr ⟨by rw [g65₃]; omega, by rw [g67₃, g65₃, Nat.mul_div_cancel_left _ (by norm_num)],
      by rw [g68₃, g65₃], by rw [g65₃, Nat.mul_div_cancel_left _ (by norm_num)]; exact hLs⟩,
    fun a' ha' => ?_⟩, ?_⟩
  · rw [g65₃] at ha'
    by_cases hlt' : 2 ^ a' < s
    · exact hkeep a' hlt'
    · have : a' = a := by
        rw [ha] at hlt' ha'
        have h1 : a ≤ a' := by
          by_contra hc'; exact hlt' (Nat.pow_lt_pow_right (by norm_num) (by omega))
        have h2 : a' < a + 1 := by
          by_contra hc'
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show a + 1 ≤ a' by omega)
          rw [pow_succ] at this; omega
        omega
      rw [this, ← ha]; exact hLs
  · unfold phiDown
    rw [g65₃, hs]
    have q0 : 1 ≤ m / s := hp
    have hN' := hN
    have q1 : 4 * m / (2 * s) = 2 * m / s := by
      rw [show 4 * m = 2 * (2 * m) by ring, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]
    have q2 : 2 * (2 * m / s) ≤ 4 * m / s := by
      rw [show 4 * m = 2 * (2 * m) by ring]
      exact (Nat.le_div_iff_mul_le hs0).2 (by
        rw [mul_assoc]; exact Nat.mul_le_mul_left 2 (Nat.div_mul_le_self _ _))
    have q3 : 2 * (m / s) ≤ 2 * m / s :=
      (Nat.le_div_iff_mul_le hs0).2 (by rw [mul_assoc]; exact Nat.mul_le_mul_left 2 (Nat.div_mul_le_self _ _))
    rw [ite_eq_right (show ¬ 2 * s = 1 by omega), Nat.mul_zero, Nat.zero_add, q1]
    by_cases h1 : s = 1
    · subst h1
      rw [ite_eq_left rfl] at hN ⊢
      simp only [Nat.div_one] at q1 q2 q3 ⊢
      have := Nat.mul_le_mul_left (4 * E + 45) hN
      nlinarith
    · rw [ite_eq_right h1] at hN ⊢
      rw [Nat.mul_zero, Nat.zero_add]
      have := Nat.mul_le_mul_left (4 * E + 45) hN
      have := Nat.mul_le_mul_left (4 * E + 55) q2
      nlinarith

/-! ### The way up -/

/-- The state between the levels of the way up: the rows divisible by `S = r65` are done. -/
structure IUpS (W : ℕ) (A : ℕ → ℕ → ℝ) (m n pb K : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  agree : Agree pb K c₀ c
  r60 : c.nreg 60 = m
  r61 : c.nreg 61 = n
  r62 : c.nreg 62 = pb
  r63 : c.nreg 63 = 1
  r64 : c.nreg 64 = 2
  r66 : c.nreg 66 = m + 1
  pow : ∃ a, c.nreg 65 = 2 ^ a
  sle : c.nreg 65 ≤ 2 * m
  levs : ∀ a, 2 ^ a < c.nreg 65 → LevOK A m n pb c (2 ^ a)
  done : ∀ r, 1 ≤ r → r ≤ m → c.nreg 65 ∣ r → Done A n pb c r

/-- The potential of the way up. -/
def phiUp (E m : ℕ) (c : Config) : ℕ := (E + 25) * (4 * m + 2 - 2 * (2 * m / c.nreg 65))

theorem upLevel_exec (hent : EntSpecK P W ent A E m n pb K c₀) (hA : IsTotMono m n A)
    (hm : 0 < m) (hK : K = 4 * m + n + 1) (hW : pb + K + 1 ≤ W) (c : Config)
    (hI : IUpS W A m n pb K c₀ c) (hlt : c.nreg 63 < c.nreg 65) :
    ∃ c' k, Exec P W (upLevel ent) c c' k ∧ IUpS W A m n pb K c₀ c' ∧
      phiUp E m c' + k + 2 ≤ phiUp E m c := by
  have hc := hI.wb
  rw [hI.r63] at hlt
  obtain ⟨a, ha⟩ := hI.pow
  have hSle := hI.sle
  generalize hS : c.nreg 65 = S at ha hlt hSle
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by
    rcases a with _ | a
    · rw [ha] at hlt; simp at hlt
    · omega⟩
  generalize hsd : 2 ^ a' = s
  have hs0 : 0 < s := by rw [← hsd]; exact Nat.two_pow_pos a'
  have hSs : S = 2 * s := by rw [ha, pow_succ, hsd, mul_comm]
  have hsm : s ≤ m := by omega
  obtain ⟨t, ht, hcols, hmin⟩ := hI.levs a' (by rw [hS, hsd]; omega)
  rw [hsd] at hcols hmin ht
  unfold upLevel
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hI.r62, hI.r60]; rw [hK] at hW; omega
  · config_simp; rw [hI.r62, hI.r60, hS, hI.r64, hSs]; rw [hK] at hW
    rw [Nat.mul_div_cancel_left _ (by norm_num)]; omega
  · config_simp; rw [hS, hI.r64, hSs, Nat.mul_div_cancel_left _ (by norm_num)]; rw [hK] at hW
    omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded W c₁ := hc₁ ▸ ‹_›
  have e₁ : ∀ r, r ≠ 65 → r ≠ 69 → r ≠ 72 → c₁.nreg r = c.nreg r := fun r a b d => by
    rw [← hc₁]; config_simp; rw [upd_other _ _ _ d, upd_other _ _ _ b, upd_other _ _ _ a]
  have g65 : c₁.nreg 65 = s := by
    rw [← hc₁]; config_simp; rw [hS, hI.r64, hSs, Nat.mul_div_cancel_left _ (by norm_num)]
  have hm₁ : c₁.nmem = c.nmem := by rw [← hc₁]
  have hU : UpData W A m n pb K s t (pb + m + s) (fun k => c.nmem (pb + m + s + k * (2 * s))) c₁ :=
    ⟨(e₁ 60 (by omega) (by omega) (by omega)).trans hI.r60,
      (e₁ 61 (by omega) (by omega) (by omega)).trans hI.r61,
      (e₁ 62 (by omega) (by omega) (by omega)).trans hI.r62,
      (e₁ 63 (by omega) (by omega) (by omega)).trans hI.r63, g65,
      (e₁ 66 (by omega) (by omega) (by omega)).trans hI.r66,
      by rw [← hc₁]; config_simp; rw [hI.r62, hI.r60, hS, hI.r64, hSs,
        Nat.mul_div_cancel_left _ (by norm_num)],
      by rw [← hc₁]; config_simp; rw [hS, hI.r64, hSs, Nat.mul_div_cancel_left _ (by norm_num),
        two_mul],
      hcols, fun k _ => by rw [hm₁], hmin, by omega,
      by have := cell_le (m := m) hs0 ht; rw [hK] at hW; omega, hs0, hsm,
      by rw [hK] at hW; omega, by rw [hK]; omega⟩
  have hA₁ : Agree pb K c₀ c₁ := hI.agree.of_eq (fun r hr => e₁ r (by omega) (by omega)
    (by omega)) (fun r _ => by rw [← hc₁]) hm₁ (by rw [← hc₁]) (by rw [← hc₁])
  refine spec_use (upRows_exec hent hA hU hw₁ hA₁ (fun r h1 h2 hr => ?_)) ?_
  · obtain ⟨d1, d2⟩ := hI.done r h1 h2 (by rw [hS, hSs]; exact hr)
    refine ⟨by rw [hm₁]; exact d1, by rw [← hc₁]; exact d2⟩
  intro c₂ k₂ hk₂ hw₂ ⟨hA₂, hn₂, hr₂, hnm₂, hrm₂, ho₂, hdone₂⟩
  have f₂ : ∀ r, r < 67 → r ≠ 65 → c₂.nreg r = c.nreg r := fun r hr h => by
    rw [hn₂ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), e₁ r h (by omega) (by omega)]
  have g65₂ : c₂.nreg 65 = s := by
    rw [hn₂ 65 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), g65]
  refine ⟨⟨hw₂, hA₂, by rw [f₂ 60 (by omega) (by omega)]; exact hI.r60,
    by rw [f₂ 61 (by omega) (by omega)]; exact hI.r61,
    by rw [f₂ 62 (by omega) (by omega)]; exact hI.r62,
    by rw [f₂ 63 (by omega) (by omega)]; exact hI.r63,
    by rw [f₂ 64 (by omega) (by omega)]; exact hI.r64,
    by rw [f₂ 66 (by omega) (by omega)]; exact hI.r66, ⟨a', by rw [g65₂, hsd]⟩,
    by rw [g65₂]; omega, fun b hb => ?_, fun r h1 h2 hr => hdone₂ r h1 h2 (by rw [← g65₂]; exact hr)⟩,
    ?_⟩
  · rw [g65₂] at hb
    refine (hI.levs b (by rw [hS]; omega)).of_mem fun k hk => ?_
    rw [hnm₂ _ (Or.inr (by have := Nat.two_pow_pos b; omega)), hm₁]
  · unfold phiUp
    rw [g65₂, hS, hSs]
    have q0 : 1 ≤ m / s := Nat.div_pos hsm hs0
    have q1 : 2 * m / (2 * s) = m / s := Nat.mul_div_mul_left _ _ (by norm_num)
    have q3 : 2 * (m / s) ≤ 2 * m / s :=
      (Nat.le_div_iff_mul_le hs0).2 (by rw [mul_assoc]; exact Nat.mul_le_mul_left 2 (Nat.div_mul_le_self _ _))
    have q4 : 2 * m / s ≤ 2 * m := Nat.div_le_self _ _
    have q5 : (m + s) / (2 * s) ≤ m / s := by
      apply (Nat.le_div_iff_mul_le hs0).2
      calc (m + s) / (2 * s) * s ≤ (m + s) / 2 := by
            rw [Nat.le_div_iff_mul_le (by norm_num), mul_assoc, mul_comm s 2]
            exact Nat.div_mul_le_self _ _
        _ ≤ m := by omega
    rw [q1]
    have := Nat.mul_le_mul_left (E + 30) q5
    have := Nat.mul_le_mul_left (E + 10) ht
    have e1 : 4 * m + 2 - 2 * (m / s) = (4 * m + 2 - 2 * (2 * m / s)) + 2 * (2 * m / s - m / s) := by
      omega
    rw [e1, Nat.mul_add]
    have : (E + 25) * (2 * (2 * m / s - m / s)) ≥ (E + 25) * (2 * (m / s)) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith

/-! ### The whole run -/

/-- **SMAWK on the machine.** With `m, n ≥ 1` in `r60, r61`, the output base `pb` in `r62`,
`pb + 4m + n + 2 ≤ W` and an entry oracle of cost `≤ E` with the frame `Agree pb (4m + n + 1)`,
`smawk ent` stores, for every row `i < m`, the leftmost position `lmin n A i` of a minimum of the
row at `pb + i + 1` of the natural memory and the minimum `A i (lmin n A i)` at `pb + i + 1` of
the real memory, within `(20E + 320)(m + n + 1)` steps. -/
theorem smawk_exec (hent : EntSpecK P W ent A E m n pb (4 * m + n + 1) c₀) (hA : IsTotMono m n A)
    (hm : 0 < m) (hn : 0 < n) (hW : pb + 4 * m + n + 2 ≤ W) (hc : WordsBounded W c₀)
    (h60 : c₀.nreg 60 = m) (h61 : c₀.nreg 61 = n) (h62 : c₀.nreg 62 = pb) :
    ∃ c' k, Exec P W (smawk ent) c₀ c' k ∧ k ≤ (20 * E + 320) * (m + n + 1) ∧
      (Agree pb (4 * m + n + 1) c₀ c' ∧ c'.nreg 60 = m ∧ c'.nreg 61 = n ∧ c'.nreg 62 = pb ∧
        ∀ i < m, c'.nmem (pb + i + 1) = lmin n A i ∧ c'.rmem (pb + i + 1) = A i (lmin n A i)) := by
  generalize hK : 4 * m + n + 1 = K at hent ⊢
  have hW' : pb + K + 1 ≤ W := by omega
  unfold smawk
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  · config_simp; rw [h60]; omega
  · config_simp; rw [h62, h60]; omega
  · config_simp; rw [h62, h60]; omega
  · config_simp; rw [h62, h60]; omega
  · config_simp; rw [h62, h60]; omega
  · config_simp; rw [h62, h60]; omega
  · omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded W c₁ := hc₁ ▸ ‹_›
  have e₁ : ∀ r, r < 63 → c₁.nreg r = c₀.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have hA₁ : Agree pb K c₀ c₁ := (Agree.refl pb K c₀).of_eq (fun r hr => e₁ r (by omega))
    (fun r _ => by rw [← hc₁]) (by rw [← hc₁]) (by rw [← hc₁]) (by rw [← hc₁])
  have g67 : c₁.nreg 67 = pb + 4 * m + 1 := by rw [← hc₁]; config_simp; rw [h62, h60]; try ring
  refine spec_seq ?_
  refine spec_use (initId_exec (n := n) hw₁ hA₁ g67 (by rw [e₁ 61 (by omega)]; exact h61)
    (by rw [← hc₁]; config_simp) (by omega) (by omega) (by omega)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hA₂, hn₂, hr₂, hrm₂, ho₂, hnm₂, hid₂⟩
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₂ 65 1 (by omega)) fun hw₃ => ?_
  have f₃ : ∀ r, r ≠ 65 → r ≠ 78 → r ≠ 79 → ({ c₂ with nreg := upd c₂.nreg 65 1 } : Config).nreg r =
      c₁.nreg r := fun r a b d => by config_simp; rw [upd_other _ _ _ a, hn₂ r b d]
  refine spec_seq ?_
  refine spec_while (IDn W A m n pb K c₀) (phiDown E m n) (fun c h => h.wb)
    (fun c hI hlt => downLevel_exec hent hA hm hn hK.symm hW' c hI hlt)
    ⟨hw₃, hA₂.of_eq (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)])
      (fun _ _ => rfl) rfl rfl rfl,
      by rw [f₃ 60 (by omega) (by omega) (by omega), e₁ 60 (by omega)]; exact h60,
      by rw [f₃ 61 (by omega) (by omega) (by omega), e₁ 61 (by omega)]; exact h61,
      by rw [f₃ 62 (by omega) (by omega) (by omega), e₁ 62 (by omega)]; exact h62,
      by rw [f₃ 63 (by omega) (by omega) (by omega)]; rw [← hc₁]; config_simp,
      by rw [f₃ 64 (by omega) (by omega) (by omega)]; rw [← hc₁]; config_simp,
      by rw [f₃ 66 (by omega) (by omega) (by omega)]; rw [← hc₁]; config_simp; rw [h60],
      ⟨0, by config_simp; rfl⟩, by config_simp; omega,
      Or.inl ⟨by config_simp, by rw [f₃ 67 (by omega) (by omega) (by omega), g67],
        by rw [f₃ 68 (by omega) (by omega) (by omega)]; rw [← hc₁]; config_simp,
        fun j hj => by config_simp; rw [Nat.mul_one]; exact hid₂ j hj⟩,
      fun a ha => by config_simp at ha; have := Nat.one_le_two_pow (n := a); omega⟩ ?_
  intro c₄ k₄ hI₄ hn₄ hk₄
  rw [hI₄.r66, not_lt] at hn₄
  refine spec_while (IUpS W A m n pb K c₀) (phiUp E m) (fun c h => h.wb)
    (fun c hI hlt => upLevel_exec hent hA hm hK.symm hW' c hI hlt)
    ⟨hI₄.wb, hI₄.agree, hI₄.r60, hI₄.r61, hI₄.r62, hI₄.r63, hI₄.r64, hI₄.r66, hI₄.pow, hI₄.sle,
      hI₄.levs, fun r h1 h2 hr => absurd (Nat.le_of_dvd (by omega) hr) (by omega)⟩ ?_
  intro c₅ k₅ hI₅ hn₅ hk₅
  rw [hI₅.r63] at hn₅
  have hS1 : c₅.nreg 65 = 1 := by
    obtain ⟨a, ha⟩ := hI₅.pow
    have := Nat.one_le_two_pow (n := a); omega
  refine ⟨?_, hI₅.agree, hI₅.r60, hI₅.r61, hI₅.r62, fun i hi => ?_⟩
  · unfold phiDown at hk₄
    unfold phiUp at hk₅
    config_simp at hk₄
    simp only [Nat.div_one, ↓reduceIte] at hk₄
    have : (E + 25) * (4 * m + 2 - 2 * (2 * m / c₄.nreg 65)) ≤ (E + 25) * (4 * m + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    nlinarith
  · have := hI₅.done (i + 1) (by omega) (by omega) (by rw [hS1]; exact one_dvd _)
    simp only [Done, Nat.add_sub_cancel] at this
    rw [← Nat.add_assoc] at this
    exact this

end Monge

end PlanarFlow
