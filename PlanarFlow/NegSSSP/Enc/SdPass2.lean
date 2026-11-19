module

public import PlanarFlow.NegSSSP.Enc.SdProg

/-!
# The program writing the plain arrays of a side: passes 2 and 3

* `sdL2a_exec`: `nD := cnt`, the flags `U[v]` cleared (`v < nV + nF`);
* `sdL2b_exec`: `U[v] = sdUse … v`, the flag of the vertex numbers of the darts of the disc;
* `sdL2c_exec`: `VN[v]` the prefix counts of the flags `U`;
* `sdL3_exec`: `TN[x]` the prefix counts of the triangles in `Z`, their number in `r2564`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge.CmpAbs

variable {P : Input} {W : ℕ}

theorem sdB2a_ok : sdB2a.allI (sdOk 2562 2579) = true := by decide
theorem sdB2b_ok : sdB2b.allI (sdOk 2562 2579) = true := by decide
theorem sdB2c_ok : sdB2c.allI (sdOk 2562 2579) = true := by decide
theorem sdB3_ok : sdB3.allI (sdOk 2562 2579) = true := by decide

/-! ### Pass 2a -/

theorem sdB2a_exec (c : Config) (hc : WordsBounded W c) {U v : ℕ}
    (r84 : c.nreg 2584 = U) (r89 : c.nreg 2589 = 1) (r91 : c.nreg 2591 = 0)
    (r62 : c.nreg 2562 = v) (w1 : U + v ≤ W) (w2 : v + 1 ≤ W) :
    ∃ c' k, Exec P W sdB2a c c' k ∧ k = 3 ∧ c'.nmem = upd c.nmem (U + v) 0 ∧
      c'.nreg 2562 = v + 1 := by
  unfold sdB2a
  exec_block
  all_goals try (config_simp; simp only [r84, r89, r91, r62]; omega)
  refine ⟨rfl, ?_, ?_⟩
  · config_simp; simp only [r84, r91, r62]
  · config_simp; simp only [r89, r62]

/-- **Pass 2a**: `nD := r2564`, `U[v] := 0` for `v < n` (`n = r2555`), within `5 n + 5`
steps. -/
theorem sdL2a_exec (c : Config) (hc : WordsBounded W c) {n U : ℕ}
    (r55 : c.nreg 2555 = n) (r84 : c.nreg 2584 = U) (r89 : c.nreg 2589 = 1)
    (r91 : c.nreg 2591 = 0) (w : U + n + 2 ≤ W) :
    ∃ c' k, Exec P W sdL2a c c' k ∧ k ≤ 5 * n + 5 ∧ (∀ v < n, c'.nmem (U + v) = 0) ∧
      c'.nreg 2580 = c.nreg 2564 ∧ c'.nreg 2592 = n ∧
      (∀ a, a < U ∨ U + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2562 ∨ 2579 < r → r ≠ 2580 → r ≠ 2592 → c'.nreg r = c.nreg r) := by
  unfold sdL2a
  obtain ⟨c₁, k₁, e₁, hk₁, g80, g62, g92, gn₁, gm₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 2580 2564, .constN 2562 0, .copyN 2592 2555]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 2580 = c.nreg 2564 ∧ c₁.nreg 2562 = 0 ∧ c₁.nreg 2592 = n ∧
      (∀ r, r ≠ 2580 → r ≠ 2562 → r ≠ 2592 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl⟩
    all_goals config_simp
    · exact r55
    · simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ v < i, c'.nmem (U + v) = 0) ∧ (∀ a, a < U ∨ U + i ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2562 ∨ 2579 < r → c'.nreg r = c₁.nreg r)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2562) (bR := 2592)
    (body := sdB2a) J (K := 3) (n := n) c₁ e₁.wb_right g62 g92
    ⟨fun v hv => absurd hv (by omega), fun a _ => by rw [gm₁], fun r _ => rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j4⟩ := hJ
      have R : ∀ r, r < 2562 ∨ 2579 < r → r ≠ 2580 → r ≠ 2592 → c'.nreg r = c.nreg r :=
        fun r hr h1 h2 => (j4 r hr).trans (gn₁ r h1 (by omega) h2)
      obtain ⟨c'', k, ex, hk, hm, h62⟩ := sdB2a_exec (P := P) c' hw
        ((R 2584 (by omega) (by omega) (by omega)).trans r84)
        ((R 2589 (by omega) (by omega) (by omega)).trans r89)
        ((R 2591 (by omega) (by omega) (by omega)).trans r91) ha (by omega) (by omega)
      have keep := (sd_keep ex sdB2a_ok).1
      refine ⟨c'', k, ex, by omega, h62, by rw [keep 2592 (by omega)]; exact hb,
        fun v hv => ?_, fun a h => ?_, fun r hr => (keep r hr).trans (j4 r hr)⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · rw [sd_ifN (by omega)]; exact j1 v hv
        · rw [sd_ifP rfl]
      · rw [hm, upd_apply, sd_ifN (by omega)]
        exact j2 a (by omega))
  obtain ⟨j1, j2, j4⟩ := hJ
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, by rw [j4 2580 (by omega), g80],
    by rw [j4 2592 (by omega), g92], j2, fun r hr h1 h2 => ?_⟩
  rw [j4 r hr, gn₁ r h1 (by omega) h2]

/-! ### Pass 2b -/

lemma sdUse_zero (mem : ℕ → ℕ) (bV : ℕ) (fl : ℕ → ℕ) (v : ℕ) : sdUse mem bV fl 0 v = 0 := by
  unfold sdUse; rw [sd_ifN (by rintro ⟨y, hy, -⟩; omega)]

lemma sdUse_succ (mem : ℕ → ℕ) (bV : ℕ) (fl : ℕ → ℕ) (i v : ℕ) (hfl : fl i ≤ 1) :
    sdUse mem bV fl (i + 1) v =
      if mem (bV + i) = v then sdOr (sdUse mem bV fl i v) (fl i) else sdUse mem bV fl i v := by
  unfold sdUse sdOr
  by_cases h1 : ∃ y < i, fl y = 1 ∧ mem (bV + y) = v
  · obtain ⟨y, hy, h2, h3⟩ := h1
    have e1 : ∃ y' < i + 1, fl y' = 1 ∧ mem (bV + y') = v := ⟨y, by omega, h2, h3⟩
    have e2 : ∃ y' < i, fl y' = 1 ∧ mem (bV + y') = v := ⟨y, hy, h2, h3⟩
    rw [sd_ifP e1, sd_ifP e2]
    split_ifs <;> omega
  · rw [sd_ifN h1]
    by_cases h2 : fl i = 1 ∧ mem (bV + i) = v
    · have e1 : ∃ y' < i + 1, fl y' = 1 ∧ mem (bV + y') = v := ⟨i, by omega, h2⟩
      rw [sd_ifP e1, sd_ifP h2.2, h2.1]
    · rw [sd_ifN (by
        rintro ⟨y, hy, h3, h4⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
        · exact h1 ⟨y, hy, h3, h4⟩
        · exact h2 ⟨h3, h4⟩)]
      split_ifs with h3
      · have : fl i ≠ 1 := fun h => h2 ⟨h, h3⟩
        omega
      · rfl

lemma sdUse_congr {mem mem' : ℕ → ℕ} {bV : ℕ} {fl fl' : ℕ → ℕ} {n v : ℕ}
    (h1 : ∀ y < n, mem' (bV + y) = mem (bV + y)) (h2 : ∀ y < n, fl' y = fl y) :
    sdUse mem' bV fl' n v = sdUse mem bV fl n v := by
  unfold sdUse
  congr 1
  apply propext
  constructor
  · rintro ⟨y, hy, h3, h4⟩; exact ⟨y, hy, by rw [← h2 y hy]; exact h3, by rw [← h1 y hy]; exact h4⟩
  · rintro ⟨y, hy, h3, h4⟩; exact ⟨y, hy, by rw [h2 y hy]; exact h3, by rw [h1 y hy]; exact h4⟩

theorem sdB2b_exec (c : Config) (hc : WordsBounded W c) {bV U INF y : ℕ}
    (r54 : c.nreg 2554 = bV) (r84 : c.nreg 2584 = U) (r82 : c.nreg 2582 = INF)
    (r89 : c.nreg 2589 = 1) (r62 : c.nreg 2562 = y) (w1 : bV + y ≤ W)
    (w2 : U + c.nmem (bV + y) ≤ W) (w3 : INF + y ≤ W) (w4 : y + 1 ≤ W) (w5 : 2 ≤ W)
    (hu : c.nmem (U + c.nmem (bV + y)) ≤ 1) (hf : c.nmem (INF + y) ≤ 1) :
    ∃ c' k, Exec P W sdB2b c c' k ∧ k = 11 ∧
      c'.nmem = upd c.nmem (U + c.nmem (bV + y))
        (sdOr (c.nmem (U + c.nmem (bV + y))) (c.nmem (INF + y))) ∧ c'.nreg 2562 = y + 1 := by
  unfold sdB2b
  exec_block
  all_goals try (config_simp; simp only [r54, r84, r82, r89, r62]; first | omega | exact le_trans (sd_or_le hu hf) (by omega) | exact le_trans (Nat.add_le_add hu hf) (by omega) | exact le_trans (Nat.mul_le_mul hu hf) (by omega))
  refine ⟨rfl, ?_, ?_⟩
  · config_simp; simp only [r54, r84, r82, r62]; rfl
  · config_simp; simp only [r89, r62]

/-- **Pass 2b**: `U[v] = sdUse mem bV (INF[·]) (3 m) v` for `v < n`, within `13 (3 m) + 4`
steps. -/
theorem sdL2b_exec (c : Config) (hc : WordsBounded W c) {m n bV U INF : ℕ}
    (r87 : c.nreg 2587 = 3 * m) (r54 : c.nreg 2554 = bV) (r84 : c.nreg 2584 = U)
    (r82 : c.nreg 2582 = INF) (r89 : c.nreg 2589 = 1)
    (hV : ∀ y < 3 * m, c.nmem (bV + y) < n) (hF : ∀ y < 3 * m, c.nmem (INF + y) ≤ 1)
    (hU : ∀ v < n, c.nmem (U + v) = 0)
    (l1 : bV + 3 * m ≤ U ∨ U + n ≤ bV) (l2 : INF + 3 * m ≤ U ∨ U + n ≤ INF)
    (w : U + n + 2 ≤ W) (wV : bV + 3 * m ≤ W) (wI : INF + 3 * m ≤ W) :
    ∃ c' k, Exec P W sdL2b c c' k ∧ k ≤ 13 * (3 * m) + 4 ∧
      (∀ v < n, c'.nmem (U + v) = sdUse c.nmem bV (fun y => c.nmem (INF + y)) (3 * m) v) ∧
      (∀ a, a < U ∨ U + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2562 ∨ 2592 < r → c'.nreg r = c.nreg r) := by
  unfold sdL2b
  obtain ⟨c₁, k₁, e₁, hk₁, g62, g92, gn₁, gm₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2562 0, .copyN 2592 2587]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 2562 = 0 ∧ c₁.nreg 2592 = 3 * m ∧
      (∀ r, r ≠ 2562 → r ≠ 2592 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl⟩
    all_goals config_simp
    · exact r87
    · simp only [upd_apply]; split_ifs <;> omega
  set fl : ℕ → ℕ := fun y => c.nmem (INF + y) with hfl
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ v < n, c'.nmem (U + v) = sdUse c.nmem bV fl i v) ∧
      (∀ a, a < U ∨ U + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2562 ∨ 2579 < r → c'.nreg r = c₁.nreg r)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2562) (bR := 2592)
    (body := sdB2b) J (K := 11) (n := 3 * m) c₁ e₁.wb_right g62 g92
    ⟨fun v hv => by rw [gm₁, hU v hv, sdUse_zero], fun a _ => by rw [gm₁], fun r _ => rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j4⟩ := hJ
      have R : ∀ r, r < 2562 ∨ 2579 < r → r ≠ 2592 → c'.nreg r = c.nreg r := fun r hr h' =>
        (j4 r hr).trans (gn₁ r (by omega) h')
      have hv : c'.nmem (bV + i) = c.nmem (bV + i) := j2 _ (by omega)
      have hvl := hV i hi
      have hf : c'.nmem (INF + i) = c.nmem (INF + i) := j2 _ (by omega)
      have hu : c'.nmem (U + c'.nmem (bV + i)) = sdUse c.nmem bV fl i (c.nmem (bV + i)) := by
        rw [hv]; exact j1 _ hvl
      have hul : sdUse c.nmem bV fl i (c.nmem (bV + i)) ≤ 1 := sdUse_le _ _ _ _ _
      obtain ⟨c'', k, ex, hk, hm, h62⟩ := sdB2b_exec (P := P) c' hw
        ((R 2554 (by omega) (by omega)).trans r54) ((R 2584 (by omega) (by omega)).trans r84)
        ((R 2582 (by omega) (by omega)).trans r82) ((R 2589 (by omega) (by omega)).trans r89)
        ha (by omega) (by rw [hv]; omega) (by omega) (by omega) (by omega) (by rw [hu]; exact hul)
        (by rw [hf]; exact hF i hi)
      have keep := (sd_keep ex sdB2b_ok).1
      refine ⟨c'', k, ex, by omega, h62, by rw [keep 2592 (by omega)]; exact hb,
        fun v hv' => ?_, fun a h => ?_, fun r hr => (keep r hr).trans (j4 r hr)⟩
      · rw [hm, upd_apply, hu, hv, hf, sdUse_succ c.nmem bV fl i v (hF i hi)]
        by_cases e : c.nmem (bV + i) = v
        · rw [sd_ifP (by omega), sd_ifP e, e]
        · rw [sd_ifN (by omega), sd_ifN e]; exact j1 v hv'
      · rw [hm, upd_apply, sd_ifN (by rw [hv]; omega)]
        exact j2 a h)
  obtain ⟨j1, j2, j4⟩ := hJ
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j2, fun r hr => ?_⟩
  by_cases h : 2579 < r ∧ r ≤ 2592
  · rcases hr with hr | hr <;> omega
  · rw [j4 r (by omega), gn₁ r (by omega) (by omega)]

/-! ### Pass 2c -/

theorem sdB2c_exec (c : Config) (hc : WordsBounded W c) {U VN v cnt : ℕ}
    (r84 : c.nreg 2584 = U) (r85 : c.nreg 2585 = VN) (r89 : c.nreg 2589 = 1)
    (r62 : c.nreg 2562 = v) (r64 : c.nreg 2564 = cnt) (w1 : U + v ≤ W) (w2 : VN + v ≤ W)
    (w3 : cnt + c.nmem (U + v) ≤ W) (w4 : v + 1 ≤ W) (hd : U ≠ VN) :
    ∃ c' k, Exec P W sdB2c c c' k ∧ k = 6 ∧ c'.nmem = upd c.nmem (VN + v) cnt ∧
      c'.nreg 2564 = cnt + c.nmem (U + v) ∧ c'.nreg 2562 = v + 1 := by
  unfold sdB2c
  exec_block
  all_goals try (config_simp; simp only [r84, r85, r89, r62, r64, upd_apply]; split_ifs <;> omega)
  all_goals try (config_simp; simp only [r84, r85, r89, r62, r64]; omega)
  refine ⟨rfl, ?_, ?_, ?_⟩
  · config_simp; simp only [r85, r62, r64]
  · config_simp; simp only [r84, r62, r64, upd_apply]
    split_ifs with h
    · omega
    · rfl
  · config_simp; simp only [r89, r62]

/-- **Pass 2c**: `VN[v] = sdCnt (U[·]) v` for `v < n`, `cnt := 0` first, within
`8 n + 5` steps. -/
theorem sdL2c_exec (c : Config) (hc : WordsBounded W c) {n U VN : ℕ}
    (r55 : c.nreg 2555 = n) (r84 : c.nreg 2584 = U) (r85 : c.nreg 2585 = VN)
    (r89 : c.nreg 2589 = 1) (hU : ∀ v < n, c.nmem (U + v) ≤ 1)
    (l1 : U + n ≤ VN ∨ VN + n ≤ U) (w : U + n + 2 ≤ W) (w' : VN + n + 2 ≤ W) :
    ∃ c' k, Exec P W sdL2c c c' k ∧ k ≤ 8 * n + 5 ∧
      (∀ v < n, c'.nmem (VN + v) = sdCnt (fun v => c.nmem (U + v)) v) ∧
      c'.nreg 2564 = sdCnt (fun v => c.nmem (U + v)) n ∧
      (∀ a, a < VN ∨ VN + n ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2562 ∨ 2592 < r → c'.nreg r = c.nreg r) := by
  unfold sdL2c
  obtain ⟨c₁, k₁, e₁, hk₁, g62, g92, g64, gn₁, gm₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 2562 0, .copyN 2592 2555, .constN 2564 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 2562 = 0 ∧ c₁.nreg 2592 = n ∧ c₁.nreg 2564 = 0 ∧
      (∀ r, r ≠ 2562 → r ≠ 2592 → r ≠ 2564 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, fun r h1 h2 h3 => ?_, rfl⟩
    all_goals config_simp
    · exact r55
    · simp only [upd_apply]; split_ifs <;> omega
  set fl : ℕ → ℕ := fun v => c.nmem (U + v) with hfl
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ v < i, c'.nmem (VN + v) = sdCnt fl v) ∧
      (∀ a, a < VN ∨ VN + n ≤ a → c'.nmem a = c.nmem a) ∧ c'.nreg 2564 = sdCnt fl i ∧
      (∀ r, r < 2562 ∨ 2579 < r → c'.nreg r = c₁.nreg r)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2562) (bR := 2592)
    (body := sdB2c) J (K := 6) (n := n) c₁ e₁.wb_right g62 g92
    ⟨fun v hv => absurd hv (by omega), fun a _ => by rw [gm₁], by rw [g64, sdCnt_zero],
      fun r _ => rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j4⟩ := hJ
      have R : ∀ r, r < 2562 ∨ 2579 < r → r ≠ 2592 → c'.nreg r = c.nreg r := fun r hr h' =>
        (j4 r hr).trans (gn₁ r (by omega) h' (by omega))
      have hu : c'.nmem (U + i) = c.nmem (U + i) := j2 _ (by omega)
      have hcnt : sdCnt fl i ≤ i := sdCnt_le (fun y hy => hU y (by omega))
      have hfi := hU i hi
      obtain ⟨c'', k, ex, hk, hm, h64, h62⟩ := sdB2c_exec (P := P) c' hw
        ((R 2584 (by omega) (by omega)).trans r84) ((R 2585 (by omega) (by omega)).trans r85)
        ((R 2589 (by omega) (by omega)).trans r89) ha j3 (by omega) (by omega)
        (by rw [hu]; omega) (by omega) (by omega)
      have keep := (sd_keep ex sdB2c_ok).1
      refine ⟨c'', k, ex, by omega, h62, by rw [keep 2592 (by omega)]; exact hb,
        fun v hv => ?_, fun a h => ?_, by rw [h64, hu, sdCnt_succ, hfl],
        fun r hr => (keep r hr).trans (j4 r hr)⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · rw [sd_ifN (by omega)]; exact j1 v hv
        · rw [sd_ifP rfl]
      · rw [hm, upd_apply, sd_ifN (by omega)]
        exact j2 a h)
  obtain ⟨j1, j2, j3, j4⟩ := hJ
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j3, j2, fun r hr => ?_⟩
  by_cases h : 2579 < r ∧ r ≤ 2592
  · rcases hr with hr | hr <;> omega
  · rw [j4 r (by omega), gn₁ r (by omega) (by omega) (by omega)]

/-! ### Pass 3 -/

theorem sdB3_exec (c : Config) (hc : WordsBounded W c) {bz sv TN x cnt : ℕ}
    (r86 : c.nreg 2586 = TN) (r51 : c.nreg 2551 = bz) (r52 : c.nreg 2552 = sv)
    (r89 : c.nreg 2589 = 1) (r62 : c.nreg 2562 = x) (r64 : c.nreg 2564 = cnt)
    (w1 : TN + x ≤ W) (w2 : bz + x ≤ W) (w3 : cnt + 1 ≤ W) (w4 : x + 1 ≤ W) (w5 : 1 ≤ W)
    (hd : bz ≠ TN) :
    ∃ c' k, Exec P W sdB3 c c' k ∧ k = 10 ∧ c'.nmem = upd c.nmem (TN + x) cnt ∧
      c'.nreg 2564 = cnt + sdMk c.nmem bz sv x ∧ c'.nreg 2562 = x + 1 := by
  have hsv : sv ≤ W := r52 ▸ hc.1 2552
  unfold sdB3
  exec_block
  all_goals try (config_simp; simp only [r86, r51, r52, r89, r62, r64, upd_apply]; first | omega | exact sd_absd_le (hc.2 _) hsv | (split_ifs <;> first | omega | exact sd_absd_le (hc.2 _) hsv))
  refine ⟨rfl, ?_, ?_, ?_⟩
  · config_simp; simp only [r86, r62, r64]
  · config_simp; simp only [r51, r52, r89, r62, r64, upd_apply]
    split_ifs with h
    · omega
    · rfl
  · config_simp; simp only [r89, r62]

/-- **Pass 3**: `TN[x] = sdCnt (sdMk mem bz sv) x` for `x < m`, the count of all the triangles in
`Z` in `r2564`, within `12 m + 5` steps. -/
theorem sdL3_exec (c : Config) (hc : WordsBounded W c) {m bz sv TN : ℕ}
    (r50 : c.nreg 2550 = m) (r86 : c.nreg 2586 = TN) (r51 : c.nreg 2551 = bz)
    (r52 : c.nreg 2552 = sv) (r89 : c.nreg 2589 = 1) (l1 : bz + m ≤ TN ∨ TN + m ≤ bz)
    (w : TN + m + 2 ≤ W) (w' : bz + m ≤ W) :
    ∃ c' k, Exec P W sdL3 c c' k ∧ k ≤ 12 * m + 6 ∧
      (∀ x < m, c'.nmem (TN + x) = sdCnt (sdMk c.nmem bz sv) x) ∧
      c'.nreg 2564 = sdCnt (sdMk c.nmem bz sv) m ∧ c'.nreg 2593 = c.nreg 2564 ∧
      (∀ a, a < TN ∨ TN + m ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2562 ∨ 2593 < r → c'.nreg r = c.nreg r) := by
  unfold sdL3
  obtain ⟨c₁, k₁, e₁, hk₁, g93, g62, g92, g64, gn₁, gm₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 2593 2564, .constN 2562 0, .copyN 2592 2550, .constN 2564 0]) c c₁
        k₁ ∧ k₁ = 4 ∧ c₁.nreg 2593 = c.nreg 2564 ∧
      c₁.nreg 2562 = 0 ∧ c₁.nreg 2592 = m ∧ c₁.nreg 2564 = 0 ∧
      (∀ r, r ≠ 2593 → r ≠ 2562 → r ≠ 2592 → r ≠ 2564 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h0 h1 h2 h3 => ?_, rfl⟩
    all_goals config_simp
    · exact r50
    · simp only [upd_apply]; split_ifs <;> omega
  set fl : ℕ → ℕ := sdMk c.nmem bz sv with hfl
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x < i, c'.nmem (TN + x) = sdCnt fl x) ∧
      (∀ a, a < TN ∨ TN + m ≤ a → c'.nmem a = c.nmem a) ∧ c'.nreg 2564 = sdCnt fl i ∧
      (∀ r, r < 2562 ∨ 2579 < r → c'.nreg r = c₁.nreg r)
  obtain ⟨c₂, k₂, e₂, hk₂, -, hJ⟩ := forLoop_exec (P := P) (a := 2562) (bR := 2592)
    (body := sdB3) J (K := 10) (n := m) c₁ e₁.wb_right g62 g92
    ⟨fun v hv => absurd hv (by omega), fun a _ => by rw [gm₁], by rw [g64, sdCnt_zero],
      fun r _ => rfl⟩
    (fun i c' hi hw ha hb hJ => by
      obtain ⟨j1, j2, j3, j4⟩ := hJ
      have R : ∀ r, r < 2562 ∨ 2579 < r → r ≠ 2592 → r ≠ 2593 → c'.nreg r = c.nreg r :=
        fun r hr h' h'' => (j4 r hr).trans (gn₁ r h'' (by omega) h' (by omega))
      have hcnt : sdCnt fl i ≤ i := sdCnt_le (fun y _ => sdEq_le _ _)
      obtain ⟨c'', k, ex, hk, hm, h64, h62⟩ := sdB3_exec (P := P) c' hw
        ((R 2586 (by omega) (by omega) (by omega)).trans r86) ((R 2551 (by omega) (by omega) (by omega)).trans r51)
        ((R 2552 (by omega) (by omega) (by omega)).trans r52) ((R 2589 (by omega) (by omega) (by omega)).trans r89)
        ha j3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      have hmk : sdMk c'.nmem bz sv i = fl i := by
        rw [hfl, sdMk, sdMk, j2 _ (by omega)]
      have keep := (sd_keep ex sdB3_ok).1
      refine ⟨c'', k, ex, by omega, h62, by rw [keep 2592 (by omega)]; exact hb,
        fun v hv => ?_, fun a h => ?_, by rw [h64, hmk, sdCnt_succ],
        fun r hr => (keep r hr).trans (j4 r hr)⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · rw [sd_ifN (by omega)]; exact j1 v hv
        · rw [sd_ifP rfl]
      · rw [hm, upd_apply, sd_ifN (by omega)]
        exact j2 a h)
  obtain ⟨j1, j2, j3, j4⟩ := hJ
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by omega, j1, j3, by rw [j4 2593 (by omega), g93], j2,
    fun r hr => ?_⟩
  by_cases h : 2579 < r ∧ r ≤ 2593
  · rcases hr with hr | hr <;> omega
  · rw [j4 r (by omega), gn₁ r (by omega) (by omega) (by omega) (by omega)]

end NegSSSP

end PlanarFlow
