module

public import PlanarFlow.NegSSSP.Enc.SdPass4

/-!
# The program writing the plain arrays of a side: the whole run

`sdProg_exec`: from the registers `2550 … 2561` (`m`, `bz`, `sv`, `bA`, `bV`, `nVF`, `bK`,
`bL`, `bW`, `k`, `S`, `I0`), the inputs below the scratch `S`, the scratch
`[S, S + 7 m + 2 nVF)` below the output `I0`, `I0 + 18 m + k + 5 ≤ W`, `sdProg` runs within
`288 m + 13 nVF + 9 k + 46` steps and leaves, with `inf = sdInf mem bz bA sv`,
`nD = sdCnt inf (3 m)`, at `I0 + j nD + sdCnt inf y` (`y` a flagged code) the words of the six
arrays of `sd_arrays` (hypotheses `oRV … oG`), `nD` in `r2580`, the number of the triangles in
`Z` in `r2581`, the count of the used vertex numbers in `r2593`; the memory outside
`[S, I0 + 5 nD + k)`, the registers outside `[2562, 2593]`, the reals and the output kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge.CmpAbs

variable {P : Input} {W : ℕ}

theorem sdSetup_exec (c : Config) (hc : WordsBounded W c) {m nVF S : ℕ}
    (r50 : c.nreg 2550 = m) (r55 : c.nreg 2555 = nVF) (r60 : c.nreg 2560 = S)
    (w : S + 6 * m + 2 * nVF + 3 ≤ W) :
    ∃ c' k, Exec P W sdSetup c c' k ∧ k = 10 ∧ c'.nreg 2589 = 1 ∧ c'.nreg 2590 = 3 ∧
      c'.nreg 2591 = 0 ∧ c'.nreg 2564 = 0 ∧ c'.nreg 2587 = 3 * m ∧ c'.nreg 2582 = S ∧
      c'.nreg 2583 = S + 3 * m ∧ c'.nreg 2584 = S + 6 * m ∧
      c'.nreg 2585 = S + 6 * m + nVF ∧ c'.nreg 2586 = S + 6 * m + 2 * nVF ∧
      c'.nmem = c.nmem := by
  unfold sdSetup
  exec_block
  all_goals try (config_simp; (try simp only [r50, r55, r60]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals config_simp
  all_goals simp only [r50, r55, r60]
  all_goals omega

set_option maxHeartbeats 4000000 in
/-- **The plain arrays of a side, on the machine.** See the module docstring. -/
theorem sdProg_exec (c : Config) (hc : WordsBounded W c)
    {m bz sv bA bV nVF bK bL bW kk S I0 : ℕ}
    (r50 : c.nreg 2550 = m) (r51 : c.nreg 2551 = bz) (r52 : c.nreg 2552 = sv)
    (r53 : c.nreg 2553 = bA) (r54 : c.nreg 2554 = bV) (r55 : c.nreg 2555 = nVF)
    (r56 : c.nreg 2556 = bK) (r57 : c.nreg 2557 = bL) (r58 : c.nreg 2558 = bW)
    (r59 : c.nreg 2559 = kk) (r60 : c.nreg 2560 = S) (r61 : c.nreg 2561 = I0)
    (hA : ∀ y < 3 * m, c.nmem (bA + y) < 3 * m) (hV : ∀ y < 3 * m, c.nmem (bV + y) < nVF)
    (hK : ∀ x < m, c.nmem (bK + x) ≤ 1) (hWk : ∀ t < kk, c.nmem (bW + t) < 3 * m)
    (l1 : bz + m ≤ S) (l2 : bA + 3 * m ≤ S) (l3 : bV + 3 * m ≤ S) (l4 : bK + m ≤ S)
    (l5 : bL + m ≤ S) (l6 : bW + kk ≤ S) (l7 : S + 7 * m + 2 * nVF ≤ I0)
    (w : I0 + 18 * m + kk + 5 ≤ W) :
    ∃ c' k, Exec P W sdProg c c' k ∧ k ≤ 288 * m + 13 * nVF + 9 * kk + 46 ∧
      (∀ y < 3 * m, sdInf c.nmem bz bA sv y = 1 →
        c'.nmem (I0 + sdCnt (sdInf c.nmem bz bA sv) y) =
          sdCnt (sdInf c.nmem bz bA sv) (c.nmem (bA + y)) ∧
        c'.nmem (I0 + sdCnt (sdInf c.nmem bz bA sv) (3 * m) +
          sdCnt (sdInf c.nmem bz bA sv) y) =
          sdCnt (sdUse c.nmem bV (sdInf c.nmem bz bA sv) (3 * m)) (c.nmem (bV + y)) ∧
        c'.nmem (I0 + 2 * sdCnt (sdInf c.nmem bz bA sv) (3 * m) +
          sdCnt (sdInf c.nmem bz bA sv) y) =
          (if sdMk c.nmem bz sv (y / 3) = 1 then sdCnt (sdMk c.nmem bz sv) (y / 3)
            else sdCnt (sdMk c.nmem bz sv) m) ∧
        c'.nmem (I0 + 3 * sdCnt (sdInf c.nmem bz bA sv) (3 * m) +
          sdCnt (sdInf c.nmem bz bA sv) y) =
          sdEq (y % 3) 0 * sdMk c.nmem bz sv (y / 3) * c.nmem (bK + y / 3) ∧
        c'.nmem (I0 + 4 * sdCnt (sdInf c.nmem bz bA sv) (3 * m) +
          sdCnt (sdInf c.nmem bz bA sv) y) =
          sdEq (y % 3) 0 * sdMk c.nmem bz sv (y / 3) * c.nmem (bK + y / 3) *
            c.nmem (bL + y / 3)) ∧
      (∀ t < kk, c'.nmem (I0 + 5 * sdCnt (sdInf c.nmem bz bA sv) (3 * m) + t) =
        sdCnt (sdInf c.nmem bz bA sv) (c.nmem (bW + t))) ∧
      c'.nreg 2580 = sdCnt (sdInf c.nmem bz bA sv) (3 * m) ∧
      c'.nreg 2581 = sdCnt (sdMk c.nmem bz sv) m ∧
      c'.nreg 2593 = sdCnt (sdUse c.nmem bV (sdInf c.nmem bz bA sv) (3 * m)) nVF ∧
      (∀ a, a < S ∨ I0 + 5 * sdCnt (sdInf c.nmem bz bA sv) (3 * m) + kk ≤ a →
        c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2562 ∨ 2593 < r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set inf := sdInf c.nmem bz bA sv with hinf
  set nD := sdCnt inf (3 * m) with hnD
  set use := sdUse c.nmem bV inf (3 * m) with huse
  set mk := sdMk c.nmem bz sv with hmk
  have hinfle : ∀ y, inf y ≤ 1 := fun y => sdInf_le _ _ _ _ _
  have hnD3 : nD ≤ 3 * m := sdCnt_le (fun y _ => hinfle y)
  -- setup
  obtain ⟨c₁, k₁, e₁, hk₁, s89, s90, s91, s64, s87, s82, s83, s84, s85, s86, sm₁⟩ :=
    sdSetup_exec (P := P) c hc r50 r55 r60 (by omega)
  have K₁ := (sd_keep e₁ (by decide : sdSetup.allI (sdOk 2562 2593) = true)).1
  have I₁ : ∀ r, r < 2562 → c₁.nreg r = c.nreg r := fun r h => K₁ r (Or.inl h)
  -- pass 1
  obtain ⟨c₂, k₂, e₂, hk₂, p1, p64, pm₂, pr₂⟩ := sdL1_exec (P := P) c₁ e₁.wb_right
    (m := m) (sv := sv) s87 ((I₁ 2551 (by omega)).trans r51) ((I₁ 2552 (by omega)).trans r52)
    ((I₁ 2553 (by omega)).trans r53) s89 s90 s82 s83 s64
    (fun y hy => by rw [sm₁]; exact hA y hy) (by omega) (by omega) (by omega)
  rw [sm₁, ← hinf] at p1 p64
  have M₂ : ∀ a, a < S → c₂.nmem a = c.nmem a := fun a h => by rw [pm₂ a (Or.inl h), sm₁]
  have G₂ : ∀ r, r < 2562 → c₂.nreg r = c.nreg r := fun r h =>
    (pr₂ r (Or.inl h)).trans (I₁ r h)
  have N2 : ∀ r, keepsN r sdL1 = true → c₂.nreg r = c₁.nreg r := fun r h => e₂.nreg_keep h
  -- pass 2a
  obtain ⟨c₃, k₃, e₃, hk₃, q0, q80, -, qm₃, qr₃⟩ := sdL2a_exec (P := P) c₂ e₂.wb_right
    (n := nVF) (U := S + 6 * m) ((G₂ 2555 (by omega)).trans r55)
    ((N2 2584 (by decide)).trans s84) ((N2 2589 (by decide)).trans s89)
    ((N2 2591 (by decide)).trans s91) (by omega)
  rw [p64] at q80
  have G₃ : ∀ r, r < 2562 → c₃.nreg r = c.nreg r := fun r h =>
    (qr₃ r (Or.inl h) (by omega) (by omega)).trans (G₂ r h)
  have N3 : ∀ r, keepsN r sdL2a = true → keepsN r sdL1 = true → c₃.nreg r = c₁.nreg r :=
    fun r h1 h2 => (e₃.nreg_keep h1).trans (N2 r h2)
  -- pass 2b
  obtain ⟨c₄, k₄, e₄, hk₄, u1, um₄, ur₄⟩ := sdL2b_exec (P := P) c₃ e₃.wb_right (m := m)
    (n := nVF) (U := S + 6 * m) (INF := S) ((N3 2587 (by decide) (by decide)).trans s87)
    ((G₃ 2554 (by omega)).trans r54) ((N3 2584 (by decide) (by decide)).trans s84)
    ((N3 2582 (by decide) (by decide)).trans s82) ((N3 2589 (by decide) (by decide)).trans s89)
    (fun y hy => by rw [qm₃ _ (Or.inl (by omega)), M₂ _ (by omega)]; exact hV y hy)
    (fun y hy => by rw [qm₃ _ (Or.inl (by omega)), (p1 y hy).1]; exact hinfle y)
    q0 (by omega) (by omega) (by omega) (by omega) (by omega)
  have u1' : ∀ v < nVF, c₄.nmem (S + 6 * m + v) = use v := fun v hv => by
    rw [u1 v hv, huse]
    exact sdUse_congr (fun y hy => by rw [qm₃ _ (Or.inl (by omega)), M₂ _ (by omega)])
      (fun y hy => by rw [qm₃ _ (Or.inl (by omega)), (p1 y hy).1])
  have G₄ : ∀ r, r < 2562 → c₄.nreg r = c.nreg r := fun r h =>
    (ur₄ r (Or.inl h)).trans (G₃ r h)
  have N4 : ∀ r, keepsN r sdL2b = true → keepsN r sdL2a = true → keepsN r sdL1 = true →
      c₄.nreg r = c₁.nreg r := fun r h1 h2 h3 => (e₄.nreg_keep h1).trans (N3 r h2 h3)
  -- pass 2c
  obtain ⟨c₅, k₅, e₅, hk₅, v1, v64, vm₅, vr₅⟩ := sdL2c_exec (P := P) c₄ e₄.wb_right
    (n := nVF) (U := S + 6 * m) (VN := S + 6 * m + nVF) ((G₄ 2555 (by omega)).trans r55)
    ((N4 2584 (by decide) (by decide) (by decide)).trans s84)
    ((N4 2585 (by decide) (by decide) (by decide)).trans s85)
    ((N4 2589 (by decide) (by decide) (by decide)).trans s89)
    (fun v hv => by rw [u1' v hv]; exact sdUse_le _ _ _ _ _) (by omega) (by omega) (by omega)
  have v1' : ∀ v < nVF, c₅.nmem (S + 6 * m + nVF + v) = sdCnt use v := fun v hv => by
    rw [v1 v hv]; exact sdCnt_congr (fun v' hv' => u1' v' (by omega))
  have v64' : c₅.nreg 2564 = sdCnt use nVF := by
    rw [v64]; exact sdCnt_congr (fun v hv => u1' v hv)
  have G₅ : ∀ r, r < 2562 → c₅.nreg r = c.nreg r := fun r h =>
    (vr₅ r (Or.inl h)).trans (G₄ r h)
  have N5 : ∀ r, keepsN r sdL2c = true → keepsN r sdL2b = true → keepsN r sdL2a = true →
      keepsN r sdL1 = true → c₅.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 h4 => (e₅.nreg_keep h1).trans (N4 r h2 h3 h4)
  -- the memory below `S + 6 m`
  have M₅ : ∀ a, a < S + 6 * m → c₅.nmem a = c₂.nmem a := fun a h => by
    rw [vm₅ a (Or.inl (by omega)), um₄ a (Or.inl (by omega)), qm₃ a (Or.inl (by omega))]
  -- pass 3
  obtain ⟨c₆, k₆, e₆, hk₆, t1, t64, t93, tm₆, tr₆⟩ := sdL3_exec (P := P) c₅ e₅.wb_right
    (m := m) (bz := bz) (sv := sv) (TN := S + 6 * m + 2 * nVF)
    ((G₅ 2550 (by omega)).trans r50)
    ((N5 2586 (by decide) (by decide) (by decide) (by decide)).trans s86)
    ((G₅ 2551 (by omega)).trans r51) ((G₅ 2552 (by omega)).trans r52)
    ((N5 2589 (by decide) (by decide) (by decide) (by decide)).trans s89) (by omega) (by omega)
    (by omega)
  have hmk5 : ∀ x < m, sdMk c₅.nmem bz sv x = mk x := fun x hx => by
    rw [hmk, sdMk, sdMk, M₅ _ (by omega), M₂ _ (by omega)]
  have t1' : ∀ x < m, c₆.nmem (S + 6 * m + 2 * nVF + x) = sdCnt mk x := fun x hx => by
    rw [t1 x hx]; exact sdCnt_congr (fun x' hx' => hmk5 x' (by omega))
  have t64' : c₆.nreg 2564 = sdCnt mk m := by
    rw [t64]; exact sdCnt_congr (fun x hx => hmk5 x hx)
  rw [v64'] at t93
  have G₆ : ∀ r, r < 2562 → c₆.nreg r = c.nreg r := fun r h =>
    (tr₆ r (Or.inl h)).trans (G₅ r h)
  have N6 : ∀ r, keepsN r sdL3 = true → keepsN r sdL2c = true → keepsN r sdL2b = true →
      keepsN r sdL2a = true → keepsN r sdL1 = true → c₆.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 h4 h5 => (e₆.nreg_keep h1).trans (N5 r h2 h3 h4 h5)
  have M₆ : ∀ a, a < S + 6 * m → c₆.nmem a = c₂.nmem a := fun a h => by
    rw [tm₆ a (Or.inl (by omega)), M₅ a h]
  have M₆' : ∀ a, a < S → c₆.nmem a = c.nmem a := fun a h => by
    rw [M₆ a (by omega), M₂ a h]
  have F₆ : ∀ y < 3 * m, c₆.nmem (S + y) = inf y := fun y hy => by
    rw [M₆ _ (by omega), (p1 y hy).1]
  have C₆ : ∀ y < 3 * m, c₆.nmem (S + 3 * m + y) = sdCnt inf y := fun y hy => by
    rw [M₆ _ (by omega), (p1 y hy).2]
  have n80 : c₆.nreg 2580 = nD := by
    rw [e₆.nreg_keep (by decide : keepsN 2580 sdL3 = true),
      e₅.nreg_keep (by decide : keepsN 2580 sdL2c = true),
      e₄.nreg_keep (by decide : keepsN 2580 sdL2b = true), q80]
  -- pass 4
  obtain ⟨c₇, k₇, e₇, hk₇, o1, om₇, o81, or₇⟩ := sdL4_exec (P := P) c₆ e₆.wb_right (m := m)
    (nVF := nVF) (bA := bA) (NUM := S + 3 * m) (bV := bV) (VN := S + 6 * m + nVF) (bz := bz)
    (sv := sv) (TN := S + 6 * m + 2 * nVF) (nZ := sdCnt mk m) (bK := bK) (bL := bL) (I0 := I0)
    (nD := nD) (INF := S)
    ((N6 2587 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s87) t64'
    ((G₆ 2553 (by omega)).trans r53)
    ((N6 2583 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s83)
    ((G₆ 2554 (by omega)).trans r54)
    ((N6 2585 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s85)
    ((N6 2590 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s90)
    ((G₆ 2551 (by omega)).trans r51) ((G₆ 2552 (by omega)).trans r52)
    ((N6 2589 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s89)
    ((N6 2586 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s86)
    ((N6 2591 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s91)
    ((G₆ 2556 (by omega)).trans r56) ((G₆ 2557 (by omega)).trans r57)
    ((G₆ 2561 (by omega)).trans r61) n80
    ((N6 2582 (by decide) (by decide) (by decide) (by decide) (by decide)).trans s82)
    (fun y hy => by rw [F₆ y hy]; exact hinfle y)
    (fun y hy hf => by rw [F₆ y hy] at hf; rw [C₆ y hy]; exact sdCnt_lt _ hy hf)
    (fun y hy y' hy' hf' hf => by
      rw [F₆ y' (by omega)] at hf'; rw [C₆ y hy, C₆ y' (by omega)]; exact sdCnt_lt _ hy' hf')
    (fun y hy => by rw [C₆ y hy]; exact le_trans (sdCnt_mono _ hy.le) hnD3)
    (fun y hy => by rw [M₆' _ (by omega)]; exact hA y hy)
    (fun y hy => by rw [M₆' _ (by omega)]; exact hV y hy)
    (fun x hx => by rw [M₆' _ (by omega)]; exact hK x hx)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  have G₇ : ∀ r, r < 2562 → c₇.nreg r = c.nreg r := fun r h =>
    (or₇ r (Or.inl h) (by omega)).trans (G₆ r h)
  have M₇ : ∀ a, a < I0 → c₇.nmem a = c₆.nmem a := fun a h => om₇ a (Or.inl h)
  have n80' : c₇.nreg 2580 = nD := by
    rw [e₇.nreg_keep (by decide : keepsN 2580 sdL4 = true), n80]
  have n89 : c₇.nreg 2589 = 1 := by
    rw [e₇.nreg_keep (by decide : keepsN 2589 sdL4 = true),
      N6 2589 (by decide) (by decide) (by decide) (by decide) (by decide), s89]
  have n83 : c₇.nreg 2583 = S + 3 * m := by
    rw [e₇.nreg_keep (by decide : keepsN 2583 sdL4 = true),
      N6 2583 (by decide) (by decide) (by decide) (by decide) (by decide), s83]
  -- pass 5
  obtain ⟨c₈, k₈, e₈, hk₈, g1, gm₈, -⟩ := sdL5_exec (P := P) c₇ e₇.wb_right (m := m)
    (kk := kk) (bW := bW) (NUM := S + 3 * m) (I0 := I0) (nD := nD)
    ((G₇ 2559 (by omega)).trans r59) ((G₇ 2558 (by omega)).trans r58) n83 n80'
    ((G₇ 2561 (by omega)).trans r61) n89
    (fun t ht => by rw [M₇ (bW + t) (by omega), M₆' (bW + t) (by omega)]; exact hWk t ht)
    (by omega) (by omega) (by omega) (by omega)
  have e : Exec P W sdProg c c₈ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + (k₇ + k₈))))))) :=
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ (Exec.seq e₆
      (Exec.seq e₇ e₈))))))
  obtain ⟨KR, kr, km, ko⟩ := sd_keep e sdProg_ok
  have M₈ : ∀ a, a < I0 + 5 * nD → c₈.nmem a = c₇.nmem a := fun a h => gm₈ a (Or.inl h)
  refine ⟨c₈, _, e, by omega, fun y hy hf => ?_, fun t ht => ?_, ?_, ?_, ?_, fun a ha => ?_,
    KR, kr, km, ko⟩
  · have hf6 : c₆.nmem (S + y) = 1 := by rw [F₆ y hy]; exact hf
    have hc : sdCnt inf y < nD := sdCnt_lt inf hy hf
    obtain ⟨o0, o1', o2, o3, o4⟩ := o1 y hy hf6
    rw [C₆ y hy] at o0 o1' o2 o3 o4
    have hAy := hA y hy
    have hVy := hV y hy
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [M₈ _ (by omega), o0, sdW0, M₆' (bA + y) (by omega), C₆ _ hAy]
    · rw [M₈ _ (by omega), o1', sdW1, M₆' (bV + y) (by omega),
        tm₆ (S + 6 * m + nVF + c.nmem (bV + y)) (Or.inl (by omega)), v1' _ hVy]
    · rw [M₈ _ (by omega), o2, sdW2, M₆' (bz + y / 3) (by omega),
        t1' (y / 3) (by omega)]
      have e1 : sdEq (c.nmem (bz + y / 3)) sv = mk (y / 3) := rfl
      have hm1 : mk (y / 3) ≤ 1 := sdEq_le _ _
      rw [e1]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm1 with h | h <;> rw [h] <;> simp
    · rw [M₈ _ (by omega), o3, sdW3, M₆' (bz + y / 3) (by omega), M₆' (bK + y / 3) (by omega)]
      rfl
    · rw [M₈ _ (by omega), o4, sdW4, sdW3, M₆' (bz + y / 3) (by omega),
        M₆' (bK + y / 3) (by omega), M₆' (bL + y / 3) (by omega)]
      rfl
  · rw [g1 t ht, M₇ (bW + t) (by omega), M₆' (bW + t) (by omega)]
    have := hWk t ht
    rw [M₇ _ (by omega), C₆ _ this]
  · rw [e₈.nreg_keep (by decide : keepsN 2580 sdL5 = true), n80']
  · rw [e₈.nreg_keep (by decide : keepsN 2581 sdL5 = true), o81]
  · rw [e₈.nreg_keep (by decide : keepsN 2593 sdL5 = true),
      e₇.nreg_keep (by decide : keepsN 2593 sdL4 = true), t93]
  · rcases ha with h | h
    · rw [M₈ a (by omega), M₇ a (by omega), M₆' a h]
    · rw [gm₈ a (Or.inr h), om₇ a (Or.inr (by omega)), tm₆ a (Or.inr (by omega)),
        vm₅ a (Or.inr (by omega)), um₄ a (Or.inr (by omega)), qm₃ a (Or.inr (by omega)),
        pm₂ a (Or.inr (by omega)), sm₁]

end NegSSSP

end PlanarFlow
