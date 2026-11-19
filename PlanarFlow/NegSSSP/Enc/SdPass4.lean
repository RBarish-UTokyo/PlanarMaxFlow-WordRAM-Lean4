module

public import PlanarFlow.NegSSSP.Enc.SdPass2

/-!
# The program writing the plain arrays of a side: passes 4 and 5

* `sdB4w_exec`: the five words of one dart of the disc, read first, then stored at
  `o, o + nD, …, o + 4 nD`, `o = I0 + NUM[y]`;
* `sdL4_exec`: **pass 4**, for every code `y` flagged at `INF`, the five words at
  `I0 + j nD + NUM[y]` (`sdW0 … sdW4`), the memory outside `[I0, I0 + 5 nD)` kept;
* `sdL5_exec`: **pass 5**, `G[t] = NUM[Wk[t]]` at `I0 + 5 nD + t`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge.CmpAbs

variable {P : Input} {W : ℕ}

theorem sdB4_ok : sdB4.allI (sdOk 2562 2579) = true := by decide
theorem sdB5_ok : sdB5.allI (sdOk 2562 2579) = true := by decide

/-- The word of `RV`: the count of the reverse. -/
def sdW0 (mem : ℕ → ℕ) (bA NUM y : ℕ) : ℕ := mem (NUM + mem (bA + y))

/-- The word of `NT`: the number of the vertex. -/
def sdW1 (mem : ℕ → ℕ) (bV VN y : ℕ) : ℕ := mem (VN + mem (bV + y))

/-- The word of `NF`: the number of the triangle if it is in `Z`, `nZ` otherwise. -/
def sdW2 (mem : ℕ → ℕ) (bz sv TN nZ y : ℕ) : ℕ :=
  sdEq (mem (bz + y / 3)) sv * mem (TN + y / 3) + (1 - sdEq (mem (bz + y / 3)) sv) * nZ

/-- The word of `IS`: old dart, triangle in `Z`, dart of `K`. -/
def sdW3 (mem : ℕ → ℕ) (bz sv bK y : ℕ) : ℕ :=
  sdEq (y % 3) 0 * sdEq (mem (bz + y / 3)) sv * mem (bK + y / 3)

/-- The word of `LN`. -/
def sdW4 (mem : ℕ → ℕ) (bz sv bK bL y : ℕ) : ℕ := sdW3 mem bz sv bK y * mem (bL + y / 3)

lemma sd_mul1_le {a b W : ℕ} (ha : a ≤ 1) (hb : b ≤ W) : a * b ≤ W := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl <;> simp [hb]

lemma sd_sel_le {e a b W : ℕ} (he : e ≤ 1) (ha : a ≤ W) (hb : b ≤ W) :
    e * a + (1 - e) * b ≤ W := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 he with rfl | rfl <;> simp [ha, hb]

lemma sd_eq_le' (a b : ℕ) : 1 - (a - b + (b - a)) ≤ 1 := Nat.sub_le 1 _

lemma sd_mul11 {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with rfl | rfl <;> simp [hb]

set_option maxHeartbeats 1000000 in
theorem sdB4w_exec (c : Config) (hc : WordsBounded W c)
    {bA NUM bV VN bz sv TN nZ bK bL I0 nD y : ℕ}
    (r53 : c.nreg 2553 = bA) (r83 : c.nreg 2583 = NUM) (r54 : c.nreg 2554 = bV)
    (r85 : c.nreg 2585 = VN) (r90 : c.nreg 2590 = 3) (r51 : c.nreg 2551 = bz)
    (r52 : c.nreg 2552 = sv) (r89 : c.nreg 2589 = 1) (r86 : c.nreg 2586 = TN)
    (r81 : c.nreg 2581 = nZ) (r91 : c.nreg 2591 = 0) (r56 : c.nreg 2556 = bK)
    (r57 : c.nreg 2557 = bL) (r61 : c.nreg 2561 = I0) (r80 : c.nreg 2580 = nD)
    (r62 : c.nreg 2562 = y)
    (w1 : bA + y ≤ W) (w2 : NUM + c.nmem (bA + y) ≤ W) (w3 : bV + y ≤ W)
    (w4 : VN + c.nmem (bV + y) ≤ W) (w5 : bz + y / 3 ≤ W) (w6 : TN + y / 3 ≤ W)
    (w7 : bK + y / 3 ≤ W) (w8 : bL + y / 3 ≤ W) (w9 : NUM + y ≤ W)
    (w10 : I0 + c.nmem (NUM + y) + 4 * nD ≤ W) (w11 : 1 ≤ W)
    (hK : c.nmem (bK + y / 3) ≤ 1) :
    ∃ c' k, Exec P W sdB4w c c' k ∧ k = 45 ∧
      c'.nmem = upd (upd (upd (upd (upd c.nmem (I0 + c.nmem (NUM + y)) (sdW0 c.nmem bA NUM y))
        (I0 + c.nmem (NUM + y) + nD) (sdW1 c.nmem bV VN y))
        (I0 + c.nmem (NUM + y) + nD + nD) (sdW2 c.nmem bz sv TN nZ y))
        (I0 + c.nmem (NUM + y) + nD + nD + nD) (sdW3 c.nmem bz sv bK y))
        (I0 + c.nmem (NUM + y) + nD + nD + nD + nD) (sdW4 c.nmem bz sv bK bL y) := by
  have hsv : sv ≤ W := r52 ▸ hc.1 2552
  have hnZ : nZ ≤ W := r81 ▸ hc.1 2581
  unfold sdB4w
  exec_block
  all_goals try (config_simp; simp only [r53, r83, r54, r85, r90, r51, r52, r89, r86, r81, r91, r56, r57, r61, r80, r62]; first | omega | exact sd_absd_le (hc.2 _) hsv | exact sd_mul1_le (sd_eq_le' _ _) (hc.2 _) | exact sd_mul1_le (Nat.sub_le 1 _) hnZ | exact sd_sel_le (sd_eq_le' _ _) (hc.2 _) hnZ | exact sd_absd_le (Nat.zero_le _) (by omega) | exact le_trans (Nat.mul_le_mul (sd_eq_le' _ _) (sd_eq_le' _ _)) (by omega) | exact sd_mul1_le (le_trans (Nat.mul_le_mul (sd_eq_le' _ _) (sd_eq_le' _ _)) (by omega)) (hc.2 _) | exact sd_mul1_le (sd_mul11 (sd_mul11 (sd_eq_le' _ _) (sd_eq_le' _ _)) hK) (hc.2 _))
  refine ⟨rfl, ?_⟩
  config_simp
  simp only [r53, r83, r54, r85, r90, r51, r52, r89, r86, r81, r91, r56, r57, r61, r80, r62]
  rfl

lemma sd_upd5 (mem : ℕ → ℕ) (o d v0 v1 v2 v3 v4 a : ℕ) :
    upd (upd (upd (upd (upd mem o v0) (o + d) v1) (o + d + d) v2) (o + d + d + d) v3)
      (o + d + d + d + d) v4 a =
    if a = o + d + d + d + d then v4 else if a = o + d + d + d then v3 else
    if a = o + d + d then v2 else if a = o + d then v1 else if a = o then v0 else mem a := by
  simp only [upd_apply]

set_option maxHeartbeats 1000000 in
/-- One code of pass 4: the flag `f = INF[y]` read; if `0 < f` the five words of the dart. -/
theorem sdB4_exec (c : Config) (hc : WordsBounded W c)
    {bA NUM bV VN bz sv TN nZ bK bL I0 nD y INF : ℕ}
    (r53 : c.nreg 2553 = bA) (r83 : c.nreg 2583 = NUM) (r54 : c.nreg 2554 = bV)
    (r85 : c.nreg 2585 = VN) (r90 : c.nreg 2590 = 3) (r51 : c.nreg 2551 = bz)
    (r52 : c.nreg 2552 = sv) (r89 : c.nreg 2589 = 1) (r86 : c.nreg 2586 = TN)
    (r81 : c.nreg 2581 = nZ) (r91 : c.nreg 2591 = 0) (r56 : c.nreg 2556 = bK)
    (r57 : c.nreg 2557 = bL) (r61 : c.nreg 2561 = I0) (r80 : c.nreg 2580 = nD)
    (r62 : c.nreg 2562 = y) (r82 : c.nreg 2582 = INF)
    (w1 : bA + y ≤ W) (w2 : NUM + c.nmem (bA + y) ≤ W) (w3 : bV + y ≤ W)
    (w4 : VN + c.nmem (bV + y) ≤ W) (w5 : bz + y / 3 ≤ W) (w6 : TN + y / 3 ≤ W)
    (w7 : bK + y / 3 ≤ W) (w8 : bL + y / 3 ≤ W) (w9 : NUM + y ≤ W)
    (w10 : I0 + c.nmem (NUM + y) + 4 * nD ≤ W) (w11 : 1 ≤ W) (w12 : INF + y ≤ W)
    (w13 : y + 1 ≤ W) (hK : c.nmem (bK + y / 3) ≤ 1) :
    ∃ c' k, Exec P W sdB4 c c' k ∧ k ≤ 50 ∧ c'.nreg 2562 = y + 1 ∧
      (c.nmem (INF + y) = 0 → c'.nmem = c.nmem) ∧
      (0 < c.nmem (INF + y) →
        c'.nmem = upd (upd (upd (upd (upd c.nmem (I0 + c.nmem (NUM + y))
          (sdW0 c.nmem bA NUM y)) (I0 + c.nmem (NUM + y) + nD) (sdW1 c.nmem bV VN y))
          (I0 + c.nmem (NUM + y) + nD + nD) (sdW2 c.nmem bz sv TN nZ y))
          (I0 + c.nmem (NUM + y) + nD + nD + nD) (sdW3 c.nmem bz sv bK y))
          (I0 + c.nmem (NUM + y) + nD + nD + nD + nD) (sdW4 c.nmem bz sv bK bL y)) := by
  obtain ⟨c₁, k₁, e₁, hk₁, h71, hn₁, hm₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 2568 2582 2562, .loadN 2571 2568]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 2571 = c.nmem (INF + y) ∧ (∀ r, r ≠ 2568 → r ≠ 2571 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    all_goals try (config_simp; simp only [r82, r62]; omega)
    refine ⟨rfl, ?_, fun r h1 h2 => ?_, rfl⟩
    · config_simp; simp only [r82, r62]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have R : ∀ r, r ≠ 2568 → r ≠ 2571 → c₁.nreg r = c.nreg r := hn₁
  have hw₁ := e₁.wb_right
  have inc : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 2562 = y → c₂.nreg 2589 = 1 →
      Exec P W (.instr (.addN 2562 2562 2589)) c₂
        { c₂ with nreg := upd c₂.nreg 2562 (c₂.nreg 2562 + c₂.nreg 2589) } 1 :=
    fun c₂ hw h1 h2 => Exec.addN hw 2562 2562 2589 (by rw [h1, h2]; exact w13)
  by_cases hf : 0 < c.nmem (INF + y)
  · obtain ⟨c₂, k₂, e₂, hk₂, hm₂⟩ := sdB4w_exec (P := P) c₁ hw₁
      ((R 2553 (by omega) (by omega)).trans r53) ((R 2583 (by omega) (by omega)).trans r83)
      ((R 2554 (by omega) (by omega)).trans r54) ((R 2585 (by omega) (by omega)).trans r85)
      ((R 2590 (by omega) (by omega)).trans r90) ((R 2551 (by omega) (by omega)).trans r51)
      ((R 2552 (by omega) (by omega)).trans r52) ((R 2589 (by omega) (by omega)).trans r89)
      ((R 2586 (by omega) (by omega)).trans r86) ((R 2581 (by omega) (by omega)).trans r81)
      ((R 2591 (by omega) (by omega)).trans r91) ((R 2556 (by omega) (by omega)).trans r56)
      ((R 2557 (by omega) (by omega)).trans r57) ((R 2561 (by omega) (by omega)).trans r61)
      ((R 2580 (by omega) (by omega)).trans r80) ((R 2562 (by omega) (by omega)).trans r62)
      w1 (by rw [hm₁]; exact w2) w3 (by rw [hm₁]; exact w4) w5 w6 w7 w8 w9
      (by rw [hm₁]; exact w10) w11 (by rw [hm₁]; exact hK)
    have keep := (sd_keep e₂ (by decide : sdB4w.allI (sdOk 2562 2579) = true)).1
    have e3 : Exec P W (.ifLtN 2591 2571 sdB4w .skip) c₁ c₂ (k₂ + 1) :=
      Exec.ifLtN_true (by rw [R 2591 (by omega) (by omega), r91, h71]; exact hf) e₂
    have g62 : c₂.nreg 2562 = y :=
      (e₂.nreg_keep (by decide : keepsN 2562 sdB4w = true)).trans
        ((R 2562 (by omega) (by omega)).trans r62)
    have g89 : c₂.nreg 2589 = 1 :=
      (keep 2589 (by omega)).trans ((R 2589 (by omega) (by omega)).trans r89)
    refine ⟨_, _, Exec.seq e₁ (Exec.seq e3 (inc c₂ e₂.wb_right g62 g89)), by omega, ?_,
      fun h0 => absurd h0 (by omega), fun _ => ?_⟩
    · show upd c₂.nreg 2562 (c₂.nreg 2562 + c₂.nreg 2589) 2562 = y + 1
      rw [upd_apply, sd_ifP rfl, g62, g89]
    · show c₂.nmem = _
      rw [hm₂, hm₁]
  · have e3 : Exec P W (.ifLtN 2591 2571 sdB4w .skip) c₁ c₁ (0 + 2) :=
      Exec.ifLtN_false (by rw [R 2591 (by omega) (by omega), r91, h71]; exact hf) (Exec.skip hw₁)
    have g62 : c₁.nreg 2562 = y := (R 2562 (by omega) (by omega)).trans r62
    have g89 : c₁.nreg 2589 = 1 := (R 2589 (by omega) (by omega)).trans r89
    refine ⟨_, _, Exec.seq e₁ (Exec.seq e3 (inc c₁ hw₁ g62 g89)), by omega, ?_,
      fun _ => ?_, fun h0 => absurd h0 hf⟩
    · show upd c₁.nreg 2562 (c₁.nreg 2562 + c₁.nreg 2589) 2562 = y + 1
      rw [upd_apply, sd_ifP rfl, g62, g89]
    · show c₁.nmem = _
      rw [hm₁]

set_option maxHeartbeats 2000000 in
/-- **Pass 4**: for every code `y < 3 m` flagged at `INF`, the five words of its dart at
`I0 + j nD + NUM[y]` (`j < 5`), the memory outside `[I0, I0 + 5 nD)` kept, within
`52 (3 m) + 5` steps (`nZ = r2564` at the start, copied to `r2581`). -/
theorem sdL4_exec (c : Config) (hc : WordsBounded W c)
    {m nVF bA NUM bV VN bz sv TN nZ bK bL I0 nD INF : ℕ}
    (r87 : c.nreg 2587 = 3 * m) (r64 : c.nreg 2564 = nZ)
    (r53 : c.nreg 2553 = bA) (r83 : c.nreg 2583 = NUM) (r54 : c.nreg 2554 = bV)
    (r85 : c.nreg 2585 = VN) (r90 : c.nreg 2590 = 3) (r51 : c.nreg 2551 = bz)
    (r52 : c.nreg 2552 = sv) (r89 : c.nreg 2589 = 1) (r86 : c.nreg 2586 = TN)
    (r91 : c.nreg 2591 = 0) (r56 : c.nreg 2556 = bK)
    (r57 : c.nreg 2557 = bL) (r61 : c.nreg 2561 = I0) (r80 : c.nreg 2580 = nD)
    (r82 : c.nreg 2582 = INF)
    (hF : ∀ y < 3 * m, c.nmem (INF + y) ≤ 1)
    (hN1 : ∀ y < 3 * m, c.nmem (INF + y) = 1 → c.nmem (NUM + y) < nD)
    (hN2 : ∀ y < 3 * m, ∀ y' < y, c.nmem (INF + y') = 1 → c.nmem (INF + y) = 1 →
      c.nmem (NUM + y') < c.nmem (NUM + y))
    (hN0 : ∀ y < 3 * m, c.nmem (NUM + y) ≤ 3 * m)
    (hA : ∀ y < 3 * m, c.nmem (bA + y) < 3 * m) (hV : ∀ y < 3 * m, c.nmem (bV + y) < nVF)
    (hK : ∀ x < m, c.nmem (bK + x) ≤ 1)
    (l1 : bA + 3 * m ≤ I0) (l2 : NUM + 3 * m ≤ I0) (l3 : bV + 3 * m ≤ I0)
    (l4 : VN + nVF ≤ I0) (l5 : bz + m ≤ I0) (l6 : TN + m ≤ I0) (l7 : bK + m ≤ I0)
    (l8 : bL + m ≤ I0) (l9 : INF + 3 * m ≤ I0) (w : I0 + 5 * nD + 3 * m + 1 ≤ W) :
    ∃ c' k, Exec P W sdL4 c c' k ∧ k ≤ 52 * (3 * m) + 5 ∧
      (∀ y < 3 * m, c.nmem (INF + y) = 1 →
        c'.nmem (I0 + c.nmem (NUM + y)) = sdW0 c.nmem bA NUM y ∧
        c'.nmem (I0 + nD + c.nmem (NUM + y)) = sdW1 c.nmem bV VN y ∧
        c'.nmem (I0 + 2 * nD + c.nmem (NUM + y)) = sdW2 c.nmem bz sv TN nZ y ∧
        c'.nmem (I0 + 3 * nD + c.nmem (NUM + y)) = sdW3 c.nmem bz sv bK y ∧
        c'.nmem (I0 + 4 * nD + c.nmem (NUM + y)) = sdW4 c.nmem bz sv bK bL y) ∧
      (∀ a, a < I0 ∨ I0 + 5 * nD ≤ a → c'.nmem a = c.nmem a) ∧ c'.nreg 2581 = nZ ∧
      (∀ r, r < 2562 ∨ 2592 < r → r ≠ 2581 → c'.nreg r = c.nreg r) := by
  unfold sdL4
  obtain ⟨c₁, k₁, e₁, hk₁, g81, g62, g92, gn₁, gm₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 2581 2564, .constN 2562 0, .copyN 2592 2587]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 2581 = nZ ∧ c₁.nreg 2562 = 0 ∧ c₁.nreg 2592 = 3 * m ∧
      (∀ r, r ≠ 2581 → r ≠ 2562 → r ≠ 2592 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl⟩
    all_goals config_simp
    · exact r64
    · exact r87
    · simp only [upd_apply]; split_ifs <;> omega
  let Q : ℕ → (ℕ → ℕ) → Prop := fun y mem =>
    mem (I0 + c.nmem (NUM + y)) = sdW0 c.nmem bA NUM y ∧
      mem (I0 + nD + c.nmem (NUM + y)) = sdW1 c.nmem bV VN y ∧
      mem (I0 + 2 * nD + c.nmem (NUM + y)) = sdW2 c.nmem bz sv TN nZ y ∧
      mem (I0 + 3 * nD + c.nmem (NUM + y)) = sdW3 c.nmem bz sv bK y ∧
      mem (I0 + 4 * nD + c.nmem (NUM + y)) = sdW4 c.nmem bz sv bK bL y
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ y < i, c.nmem (INF + y) = 1 → Q y c'.nmem) ∧
      (∀ a, a < I0 ∨ I0 + 5 * nD ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2562 ∨ 2579 < r → c'.nreg r = c₁.nreg r)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2562) (bR := 2592)
    (body := sdB4) J (K := 50) (n := 3 * m) c₁ e₁.wb_right g62 g92
    ⟨fun y hy => absurd hy (by omega), fun a _ => by rw [gm₁], fun r _ => rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j4⟩ := hJ
      have R : ∀ r, r < 2562 ∨ 2579 < r → r ≠ 2592 → r ≠ 2581 → c'.nreg r = c.nreg r :=
        fun r hr h1 h2 => (j4 r hr).trans (gn₁ r h2 (by omega) h1)
      have M : ∀ a, a < I0 → c'.nmem a = c.nmem a := fun a h => j2 a (Or.inl h)
      have hAi := hA i hi
      have hVi := hV i hi
      have hKi := hK (i / 3) (by omega)
      have hNi : c.nmem (INF + i) = 1 → c.nmem (NUM + i) < nD := hN1 i hi
      obtain ⟨c'', k, ex, hk, h62, h0, h1⟩ := sdB4_exec (P := P) c' hw
        ((R 2553 (by omega) (by omega) (by omega)).trans r53)
        ((R 2583 (by omega) (by omega) (by omega)).trans r83)
        ((R 2554 (by omega) (by omega) (by omega)).trans r54)
        ((R 2585 (by omega) (by omega) (by omega)).trans r85)
        ((R 2590 (by omega) (by omega) (by omega)).trans r90)
        ((R 2551 (by omega) (by omega) (by omega)).trans r51)
        ((R 2552 (by omega) (by omega) (by omega)).trans r52)
        ((R 2589 (by omega) (by omega) (by omega)).trans r89)
        ((R 2586 (by omega) (by omega) (by omega)).trans r86)
        ((j4 2581 (by omega)).trans g81)
        ((R 2591 (by omega) (by omega) (by omega)).trans r91)
        ((R 2556 (by omega) (by omega) (by omega)).trans r56)
        ((R 2557 (by omega) (by omega) (by omega)).trans r57)
        ((R 2561 (by omega) (by omega) (by omega)).trans r61)
        ((R 2580 (by omega) (by omega) (by omega)).trans r80) ha
        ((R 2582 (by omega) (by omega) (by omega)).trans r82)
        (by omega) (by rw [M _ (by omega)]; omega) (by omega) (by rw [M _ (by omega)]; omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by rw [M _ (by omega)]; have := hN0 i hi; omega)
        (by omega) (by omega) (by omega) (by rw [M _ (by omega)]; exact hKi)
      have hfi : c'.nmem (INF + i) = c.nmem (INF + i) := M _ (by omega)
      have hF' := hF i hi
      have hW0 : sdW0 c'.nmem bA NUM i = sdW0 c.nmem bA NUM i := by
        unfold sdW0; rw [M (bA + i) (by omega), M (NUM + c.nmem (bA + i)) (by omega)]
      have hW1 : sdW1 c'.nmem bV VN i = sdW1 c.nmem bV VN i := by
        unfold sdW1; rw [M (bV + i) (by omega), M (VN + c.nmem (bV + i)) (by omega)]
      have hW2 : sdW2 c'.nmem bz sv TN nZ i = sdW2 c.nmem bz sv TN nZ i := by
        unfold sdW2; rw [M (bz + i / 3) (by omega), M (TN + i / 3) (by omega)]
      have hW3 : sdW3 c'.nmem bz sv bK i = sdW3 c.nmem bz sv bK i := by
        unfold sdW3; rw [M (bz + i / 3) (by omega), M (bK + i / 3) (by omega)]
      have hW4 : sdW4 c'.nmem bz sv bK bL i = sdW4 c.nmem bz sv bK bL i := by
        unfold sdW4; rw [hW3, M (bL + i / 3) (by omega)]
      have h1' : c.nmem (INF + i) = 1 → ∀ a, c''.nmem a =
          if a = I0 + c.nmem (NUM + i) + nD + nD + nD + nD then sdW4 c.nmem bz sv bK bL i else
          if a = I0 + c.nmem (NUM + i) + nD + nD + nD then sdW3 c.nmem bz sv bK i else
          if a = I0 + c.nmem (NUM + i) + nD + nD then sdW2 c.nmem bz sv TN nZ i else
          if a = I0 + c.nmem (NUM + i) + nD then sdW1 c.nmem bV VN i else
          if a = I0 + c.nmem (NUM + i) then sdW0 c.nmem bA NUM i else c'.nmem a := by
        intro hf a
        rw [h1 (by rw [hfi]; omega), sd_upd5, M (NUM + i) (by omega), hW0, hW1, hW2, hW3, hW4]
      have h0' : c.nmem (INF + i) ≠ 1 → c''.nmem = c'.nmem := fun hf =>
        h0 (by rw [hfi]; omega)
      have keep := (sd_keep ex sdB4_ok).1
      refine ⟨c'', k, ex, by omega, h62, by rw [keep 2592 (by omega)]; exact hb, ?_, ?_,
        fun r hr => (keep r hr).trans (j4 r hr)⟩
      · intro y hy hfy
        rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
        · by_cases hf : c.nmem (INF + i) = 1
          · have hlt := hN2 i hi y hy hfy hf
            have hnd := hNi hf
            obtain ⟨q0, q1, q2, q3, q4⟩ := j1 y hy hfy
            refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [h1' hf] <;>
              rw [sd_ifN (by omega), sd_ifN (by omega), sd_ifN (by omega), sd_ifN (by omega),
                sd_ifN (by omega)]
            exacts [q0, q1, q2, q3, q4]
          · rw [h0' hf]; exact j1 y hy hfy
        · have hnd := hNi hfy
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [h1' hfy]
          · rw [sd_ifN (by omega), sd_ifN (by omega), sd_ifN (by omega), sd_ifN (by omega),
              sd_ifP (by omega)]
          · rw [sd_ifN (by omega), sd_ifN (by omega), sd_ifN (by omega), sd_ifP (by omega)]
          · rw [sd_ifN (by omega), sd_ifN (by omega), sd_ifP (by omega)]
          · rw [sd_ifN (by omega), sd_ifP (by omega)]
          · rw [sd_ifP (by omega)]
      · intro a h
        by_cases hf : c.nmem (INF + i) = 1
        · have hnd := hNi hf
          rw [h1' hf, sd_ifN (by omega), sd_ifN (by omega), sd_ifN (by omega), sd_ifN (by omega),
            sd_ifN (by omega)]
          exact j2 a h
        · rw [h0' hf]; exact j2 a h)
  obtain ⟨j1, j2, j4⟩ := hJ
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, by rw [j4 2581 (by omega), g81],
    fun r hr h81 => ?_⟩
  by_cases h : 2579 < r ∧ r ≤ 2592
  · rcases hr with hr | hr <;> omega
  · rw [j4 r (by omega), gn₁ r h81 (by omega) (by omega)]

/-! ### Pass 5 -/

theorem sdB5_exec (c : Config) (hc : WordsBounded W c) {bW NUM G t : ℕ}
    (r58 : c.nreg 2558 = bW) (r83 : c.nreg 2583 = NUM) (r88 : c.nreg 2588 = G)
    (r89 : c.nreg 2589 = 1) (r62 : c.nreg 2562 = t) (w1 : bW + t ≤ W)
    (w2 : NUM + c.nmem (bW + t) ≤ W) (w3 : G + t ≤ W) (w4 : t + 1 ≤ W) :
    ∃ c' k, Exec P W sdB5 c c' k ∧ k = 7 ∧
      c'.nmem = upd c.nmem (G + t) (c.nmem (NUM + c.nmem (bW + t))) ∧ c'.nreg 2562 = t + 1 := by
  unfold sdB5
  exec_block
  all_goals try (config_simp; simp only [r58, r83, r88, r89, r62]; omega)
  refine ⟨rfl, ?_, ?_⟩
  · config_simp; simp only [r58, r83, r88, r62]
  · config_simp; simp only [r89, r62]

/-- **Pass 5**: `G[t] = NUM[Wk[t]]` at `I0 + 5 nD + t` for `t < k`, within `9 k + 7`
steps. -/
theorem sdL5_exec (c : Config) (hc : WordsBounded W c) {m kk bW NUM I0 nD : ℕ}
    (r59 : c.nreg 2559 = kk) (r58 : c.nreg 2558 = bW) (r83 : c.nreg 2583 = NUM)
    (r80 : c.nreg 2580 = nD) (r61 : c.nreg 2561 = I0) (r89 : c.nreg 2589 = 1)
    (hWk : ∀ t < kk, c.nmem (bW + t) < 3 * m)
    (l1 : bW + kk ≤ I0 + 5 * nD) (l2 : NUM + 3 * m ≤ I0 + 5 * nD)
    (w : I0 + 5 * nD + kk + 1 ≤ W) (w5 : 5 ≤ W) :
    ∃ c' k, Exec P W sdL5 c c' k ∧ k ≤ 9 * kk + 7 ∧
      (∀ t < kk, c'.nmem (I0 + 5 * nD + t) = c.nmem (NUM + c.nmem (bW + t))) ∧
      (∀ a, a < I0 + 5 * nD ∨ I0 + 5 * nD + kk ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2562 ∨ 2592 < r → c'.nreg r = c.nreg r) := by
  unfold sdL5
  obtain ⟨c₁, k₁, e₁, hk₁, g88, g62, g92, gn₁, gm₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2568 5, .mulN 2588 2568 2580, .addN 2588 2588 2561,
        .constN 2562 0, .copyN 2592 2559]) c c₁ k₁ ∧ k₁ = 5 ∧
      c₁.nreg 2588 = I0 + 5 * nD ∧ c₁.nreg 2562 = 0 ∧ c₁.nreg 2592 = kk ∧
      (∀ r, r ≠ 2568 → r ≠ 2588 → r ≠ 2562 → r ≠ 2592 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    all_goals try (config_simp; (try simp only [r80, r61]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 h4 => ?_, rfl⟩
    all_goals config_simp
    · simp only [r80, r61]; omega
    · exact r59
    · simp only [upd_apply]; split_ifs <;> omega
  set G := I0 + 5 * nD with hG
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ t < i, c'.nmem (G + t) = c.nmem (NUM + c.nmem (bW + t))) ∧
      (∀ a, a < G ∨ G + kk ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2562 ∨ 2579 < r → c'.nreg r = c₁.nreg r)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2562) (bR := 2592)
    (body := sdB5) J (K := 7) (n := kk) c₁ e₁.wb_right g62 g92
    ⟨fun t ht => absurd ht (by omega), fun a _ => by rw [gm₁], fun r _ => rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j4⟩ := hJ
      have R : ∀ r, r < 2562 ∨ 2579 < r → r ≠ 2592 → r ≠ 2588 → c'.nreg r = c.nreg r :=
        fun r hr h1 h2 => (j4 r hr).trans (gn₁ r (by omega) h2 (by omega) h1)
      have hw1 : c'.nmem (bW + i) = c.nmem (bW + i) := j2 _ (by omega)
      have hwl := hWk i hi
      have hw2 : c'.nmem (NUM + c.nmem (bW + i)) = c.nmem (NUM + c.nmem (bW + i)) :=
        j2 _ (by omega)
      obtain ⟨c'', k, ex, hk, hm, h62⟩ := sdB5_exec (P := P) c' hw
        ((R 2558 (by omega) (by omega) (by omega)).trans r58)
        ((R 2583 (by omega) (by omega) (by omega)).trans r83)
        ((j4 2588 (by omega)).trans g88)
        ((R 2589 (by omega) (by omega) (by omega)).trans r89) ha (by omega)
        (by rw [hw1]; omega) (by omega) (by omega)
      have keep := (sd_keep ex sdB5_ok).1
      refine ⟨c'', k, ex, by omega, h62, by rw [keep 2592 (by omega)]; exact hb,
        fun t ht => ?_, fun a h => ?_, fun r hr => (keep r hr).trans (j4 r hr)⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
        · rw [sd_ifN (by omega)]; exact j1 t ht
        · rw [sd_ifP rfl, hw1, hw2]
      · rw [hm, upd_apply, sd_ifN (by omega)]
        exact j2 a h)
  obtain ⟨j1, j2, j4⟩ := hJ
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, fun r hr => ?_⟩
  by_cases h : 2579 < r ∧ r ≤ 2592
  · rcases hr with hr | hr <;> omega
  · rw [j4 r (by omega), gn₁ r (by omega) (by omega) (by omega) (by omega)]

end NegSSSP

end PlanarFlow
