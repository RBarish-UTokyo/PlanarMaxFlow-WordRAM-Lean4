module

public import PlanarFlow.NegSSSP.Enc.DkLoop

/-!
# Dijkstra's algorithm in memory: the initialization and the main theorem

**`dkProg_exec`**: from any configuration holding the arcs (`DkMem`) with the registers set,
`dkProg` ends within `17 n + 13 L + 22 + n (23 L + 21) + (13 L + 20) mm` steps
(`L = lg (2n) = ⌊log₂ n⌋ + 2`, `mm ≥ Σ_y (oe y - ob y)` the number of arcs), i.e.
**`O((n + mm) log n)`**, with the distances `D y` at `Db + y`: `D y ≤ Inf`; if `D y < Inf` some
walk from the source to `y` has length `D y`; every walk from the source to `y` has length at
least `D y`. The memory outside `[Db, Db + n) ∪ [Xb, Xb + 3n)`, the registers outside
`[2500, 2548)`, the reals and the output are kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Heap

variable {P : Input} {W : ℕ}

/-! ### Initialization -/

/-- The state of the initialization of the distances and the marks. -/
structure DkI0 (p : DkP) (W : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : DkRegs p c
  r20 : c.nreg 2520 ≤ p.n
  dist : ∀ y < c.nreg 2520, c.nmem (p.Db + y) = p.Inf
  dn : ∀ y < c.nreg 2520, c.nmem (p.Xb + y) = 0
  fr : ∀ a, ¬ DkOut p a → c.nmem a = m₀ a

theorem dkInitStep_exec {p : DkP} (hG : DkG p W) {m₀ : ℕ → ℕ} (c : Config) (hI : DkI0 p W m₀ c)
    (hlt : c.nreg 2520 < c.nreg 2500) :
    ∃ c' k, Exec P W dkInitStep c c' k ∧ DkI0 p W m₀ c' ∧
      (p.n - c'.nreg 2520) * 7 + k + 2 ≤ (p.n - c.nreg 2520) * 7 := by
  have hc := hI.wb
  have hX := hG.wX
  have hDw := hG.wD
  have hdx := hG.dDX
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hI.regs
  rw [h0] at hlt
  unfold dkInitStep
  exec_block
  · config_simp; rw [h1]; omega
  · config_simp; rw [h2]; omega
  · config_simp; rw [h12]; omega
  refine ⟨⟨‹_›, dkRegs_of hI.regs fun r hr hr' => by
      config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega,
    by config_simp; rw [h12]; omega, fun y hy => ?_, fun y hy => ?_, fun a ha => ?_⟩,
    by config_simp; rw [h12]; omega⟩
  · config_simp at hy; rw [h12] at hy; config_simp
    rw [upd_apply, upd_apply, h1, h2]; split_ifs with ha hb
    · omega
    · rw [h9]
    · exact hI.dist y (by omega)
  · config_simp at hy; rw [h12] at hy; config_simp
    rw [upd_apply, upd_apply, h1, h2]; split_ifs with ha hb
    · rw [h11]
    · omega
    · exact hI.dn y (by omega)
  · have ha' := ha
    unfold DkOut at ha'
    config_simp; rw [upd_apply, upd_apply, h1, h2]; split_ifs
    · omega
    · omega
    · exact hI.fr a ha

/-- The state of the initialization of the tree. -/
structure DkIT0 (p : DkP) (W : ℕ) (m₀ : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : DkRegs p c
  r20 : 1 ≤ c.nreg 2520 ∧ c.nreg 2520 ≤ 2 * p.n
  done : ∀ i, 1 ≤ i → i < c.nreg 2520 → dkT p c.nmem i = p.Inf
  dist : ∀ y < p.n, c.nmem (p.Db + y) = p.Inf
  dn : ∀ y < p.n, c.nmem (p.Xb + y) = 0
  fr : ∀ a, ¬ DkOut p a → c.nmem a = m₀ a

theorem dkTreeStep_exec {p : DkP} (hG : DkG p W) {m₀ : ℕ → ℕ} (c : Config) (hI : DkIT0 p W m₀ c)
    (hlt : c.nreg 2520 < c.nreg 2514) :
    ∃ c' k, Exec P W dkTreeStep c c' k ∧ DkIT0 p W m₀ c' ∧
      (2 * p.n - c'.nreg 2520) * 5 + k + 2 ≤ (2 * p.n - c.nreg 2520) * 5 := by
  have hc := hI.wb
  have hX := hG.wX
  have hDw := hG.wD
  have hdx := hG.dDX
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hI.regs
  rw [h14] at hlt
  unfold dkTreeStep
  exec_block
  · config_simp; rw [h3]; omega
  · config_simp; rw [h12]; omega
  refine ⟨⟨‹_›, dkRegs_of hI.regs fun r hr hr' => by
      config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega,
    by config_simp; rw [h12]; omega, fun i hi1 hi2 => ?_, fun y hy => ?_, fun y hy => ?_,
    fun a ha => ?_⟩, by config_simp; rw [h12]; omega⟩
  · config_simp at hi2; rw [h12] at hi2; simp only [dkT]; config_simp
    rw [upd_apply, h3]; split_ifs with h
    · exact h9
    · exact hI.done i hi1 (by omega)
  · config_simp; rw [upd_other _ _ _ (by rw [h3]; omega)]; exact hI.dist y hy
  · config_simp; rw [upd_other _ _ _ (by rw [h3]; have := hI.r20; omega)]; exact hI.dn y hy
  · have ha' := ha
    unfold DkOut at ha'
    config_simp; rw [upd_other _ _ _ (by rw [h3]; have := hI.r20; omega)]; exact hI.fr a ha

set_option maxHeartbeats 2000000 in
/-- **Initialization.** -/
theorem dkInit_exec {p : DkP} (hG : DkG p W) (c : Config) (hc : WordsBounded W c)
    (h00 : c.nreg 2500 = p.n) (h01 : c.nreg 2501 = p.Db) (h02 : c.nreg 2502 = p.Xb)
    (h04 : c.nreg 2504 = p.OBb) (h05 : c.nreg 2505 = p.OEb) (h06 : c.nreg 2506 = p.OLb)
    (h07 : c.nreg 2507 = p.NHb) (h08 : c.nreg 2508 = p.Lb) (h09 : c.nreg 2509 = p.Inf)
    (h10 : c.nreg 2510 = p.s) :
    ∃ c₇ k, (∀ t c' k', Exec P W t c₇ c' k' → Exec P W (dkInitPart t) c c' (k + k')) ∧
      DkIM p W c.nmem c₇ ∧ (∀ y < p.n, c₇.nmem (p.Xb + y) = 0) ∧
      k ≤ 17 * p.n + 13 * lg (2 * p.n) + 20 := by
  have hX := hG.wX
  have hDw := hG.wD
  have hdx := hG.dDX
  have hn := hG.n_pos
  have hsrc := hG.s_lt
  have hIW := hG.infW
  -- the constants
  obtain ⟨c₁, k₁, e₁, hw₁, hpost⟩ : ∃ c₁ k₁, Exec P W dkSetup c c₁ k₁ ∧
      WordsBounded W c₁ ∧ (DkRegs p c₁ ∧ c₁.nreg 2520 = 0 ∧ c₁.nmem = c.nmem ∧ k₁ = 6) := by
    unfold dkSetup
    exec_block
    · omega
    · omega
    · omega
    · config_simp; rw [h00]; omega
    · config_simp; rw [h00, h02]; omega
    · omega
    refine ⟨‹_›, ?_, by config_simp, by config_simp, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      simp only [h00, h01, h02, h04, h05, h06, h07, h08, h09, h10] <;> omega
  obtain ⟨hR₁, h20₁, hm₁, rfl⟩ := hpost
  -- the distances and the marks
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 2520)
    (b := 2500) (body := dkInitStep) (DkI0 p W c.nmem) (fun c => (p.n - c.nreg 2520) * 7)
    (fun c h => h.wb) (fun c hc hlt => dkInitStep_exec hG c hc hlt)
    ⟨hw₁, hR₁, by omega, fun y hy => by omega, fun y hy => by omega,
      fun a _ => by rw [hm₁]⟩
  have h20₂ : c₂.nreg 2520 = p.n := by have := hI₂.r20; rw [hI₂.regs.1] at hn₂; omega
  have e₃ := Exec.constN (P := P) hI₂.wb 2520 1 (by omega)
  -- the tree
  obtain ⟨c₄, k₄, e₄, hI₄, hn₄, hk₄⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 2520)
    (b := 2514) (body := dkTreeStep) (DkIT0 p W c.nmem) (fun c => (2 * p.n - c.nreg 2520) * 5)
    (fun c h => h.wb) (fun c hc hlt => dkTreeStep_exec hG c hc hlt)
    ⟨e₃.wb_right, dkRegs_of hI₂.regs fun r hr hr' => by
        config_simp; rw [upd_other _ _ _ (by omega)],
      by config_simp; omega, fun i h1 h2 => by config_simp at h2; omega,
      fun y hy => hI₂.dist y (by omega), fun y hy => hI₂.dn y (by omega),
      fun a ha => hI₂.fr a ha⟩
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ := hI₄.regs
  have h20₄ : c₄.nreg 2520 = 2 * p.n := by have := hI₄.r20; rw [g14] at hn₄; omega
  have hc₄ := hI₄.wb
  have hTour : IsTour p.n (dkT p c₄.nmem) := fun i h1 h2 => by
    rw [hI₄.done i h1 (by omega), hI₄.done _ (by omega) (by omega),
      hI₄.done _ (by omega) (by omega)]; simp
  -- the source
  obtain ⟨c₅, k₅, e₅, hw₅, hpost⟩ : ∃ c₅ k₅, Exec P W (block [.addN 2547 2501 2510,
      .storeN 2547 2511, .addN 2530 2500 2510, .addN 2547 2503 2530, .storeN 2547 2511,
      .divN 2530 2530 2513]) c₄ c₅ k₅ ∧ WordsBounded W c₅ ∧
      (k₅ = 6 ∧ (∀ r, r ≠ 2547 → r ≠ 2530 → c₅.nreg r = c₄.nreg r) ∧
        c₅.nreg 2530 = (p.n + p.s) / 2 ∧
        c₅.nmem = upd (upd c₄.nmem (p.Db + p.s) 0) (p.Xb + p.n + (p.n + p.s)) 0) := by
    exec_block
    · config_simp; rw [g1, g10]; omega
    · config_simp; rw [g0, g10]; omega
    · config_simp; rw [g0, g10, g3]; omega
    refine ⟨‹_›, rfl, fun r a b => ?_, by config_simp; rw [g0, g10, g13],
      by config_simp; rw [g1, g10, g11, g0, g3]⟩
    config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
  obtain ⟨rfl, hK₅, h30₅, hm₅⟩ := hpost
  have hR₅ := dkRegs_of ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩
    fun r h1 h2 => hK₅ r (by omega) (by omega)
  have hexc : IsTourExc p.n (dkT p c₅.nmem) (c₅.nreg 2530) := by
    rw [h30₅]
    exact dk_isTourExc_set hTour (by omega) fun a ha2 ha => by
      simp only [dkT, hm₅, upd_apply]; split_ifs <;> first | omega | rfl
  obtain ⟨c₆, k₆, e₆, hw₆, hK₆, hT₆, hf₆, hk₆⟩ := dkUpd_exec (P := P) hG c₅ hw₅ hR₅
    (by rw [h30₅]; omega) hexc
  have hR₆ := dkRegs_of hR₅ fun r h1 h2 => hK₆ r (Or.inl (by omega))
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩ := hR₆
  obtain ⟨c₇, k₇, e₇, hw₇, hpost⟩ : ∃ c₇ k₇, Exec P W (block [.addN 2547 2503 2512,
      .loadN 2537 2547]) c₆ c₇ k₇ ∧ WordsBounded W c₇ ∧
      (k₇ = 2 ∧ (∀ r, r ≠ 2547 → r ≠ 2537 → c₇.nreg r = c₆.nreg r) ∧
        c₇.nreg 2537 = dkT p c₆.nmem 1 ∧ c₇.nmem = c₆.nmem) := by
    exec_block
    · config_simp; rw [f3, f12]; omega
    refine ⟨‹_›, rfl, fun r a b => ?_, by config_simp; rw [f3, f12]; rfl, by config_simp⟩
    config_simp; simp only [upd_apply, a, b, ite_false]
  obtain ⟨rfl, hK₇, h37₇, hm₇⟩ := hpost
  -- the memory
  have hmem : ∀ a, (a < p.Xb + p.n + 1 ∨ p.Xb + 2 * p.n ≤ a) → c₇.nmem a =
      if a = p.Xb + p.n + (p.n + p.s) then 0 else if a = p.Db + p.s then 0 else c₄.nmem a := by
    intro a ha; rw [hm₇, hf₆ a ha, hm₅]; simp only [upd_apply]
  have hdist : ∀ x < p.n, c₇.nmem (p.Db + x) = if x = p.s then 0 else p.Inf := by
    intro x hx; rw [hmem _ (by omega)]
    split_ifs <;> first | omega | rfl | exact hI₄.dist x hx
  have hdn : ∀ x < p.n, c₇.nmem (p.Xb + x) = 0 := by
    intro x hx; rw [hmem _ (by omega)]
    split_ifs <;> first | omega | rfl | exact hI₄.dn x hx
  have hfr : ∀ a, ¬ DkOut p a → c₇.nmem a = c.nmem a := by
    intro a ha
    have ha' := ha
    unfold DkOut at ha'
    rw [hmem a (by omega)]; split_ifs <;> first | omega | exact hI₄.fr a ha
  refine ⟨c₇, 6 + (k₂ + (1 + (k₄ + (6 + (k₆ + 2))))), fun t c' k' et =>
    (Exec.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ et))))))).cast (by omega),
    ⟨hw₇, dkRegs_of ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14⟩
        fun r h1 h2 => hK₇ r (by omega) (by omega),
      hfr, by rw [hm₇]; exact hT₆, fun x hx => ?_,
      fun x hx => Or.inl (hdn x hx), fun x hx => by rw [hdist x hx]; split_ifs <;> omega,
      ⟨0, fun x hx h => by rw [hdn x hx] at h; omega, fun _ _ _ => Nat.zero_le _⟩,
      fun u hu h => by rw [hdn u hu] at h; omega, fun x hx h => ?_,
      by rw [hdist _ hsrc]; simp, by rw [h37₇, hm₇]⟩, hdn, ?_⟩
  · simp only [dkT]; rw [hmem _ (by omega), hdn x hx, hdist x hx]
    by_cases hxs : x = p.s
    · simp [hxs]
    · simp only [hxs, ite_false, show p.Xb + p.n + (p.n + x) ≠ p.Xb + p.n + (p.n + p.s) by omega]
      have := hI₄.done (p.n + x) (by omega) (by omega)
      simp only [dkT] at this
      rw [ite_eq_right_of_eq_false _ _ (eq_false (show ¬ p.Xb + p.n + (p.n + x) = p.Db + p.s by omega)),
        this]; simp
  · rw [hdist x hx] at h ⊢
    by_cases hxs : x = p.s
    · subst hxs; simp; exact DkReach.src
    · simp [hxs] at h
  · beta_reduce at hk₂ hk₄
    config_simp at hk₄
    rw [h20₁] at hk₂
    have := lg_mono (show (p.n + p.s) / 2 ≤ 2 * p.n by omega)
    rw [h30₅] at hk₆
    omega

/-! ### The main theorem -/

/-- The distances computed are the shortest walk lengths. -/
theorem DkIM.correct {p : DkP} (hG : DkG p W) {m₀ : ℕ → ℕ} {c : Config} (hI : DkIM p W m₀ c)
    (hend : ¬ c.nreg 2537 < c.nreg 2509) :
    ∀ y L, DkReach p y L → y < p.n ∧ c.nmem (p.Db + y) ≤ L := by
  have h9 := hI.regs.2.2.2.2.2.2.2.2.2.1
  rw [hI.r37, h9] at hend
  -- every node not done is at infinity
  have hinf : ∀ w < p.n, c.nmem (p.Xb + w) = 0 → c.nmem (p.Db + w) = p.Inf := by
    intro w hw h
    have h1 := root_le hI.tour (l := p.n + w) (by omega) (by omega)
    have h2 := hI.leaf w hw
    rw [h] at h2; simp at h2
    have := hI.dle w hw
    omega
  intro y L hr
  induction hr with
  | src => exact ⟨hG.s_lt, by rw [hI.srcz]⟩
  | @step u L i _ hu h1 h2 ih =>
    refine ⟨hG.nh_lt u hu i h1 h2, ?_⟩
    by_cases hfin : c.nmem (p.Db + u) < p.Inf
    · have hdone : c.nmem (p.Xb + u) = 1 := by
        rcases hI.done01 u hu with h | h
        · rw [hinf u hu h] at hfin; omega
        · exact h
      have := hI.relaxed u hu hdone i h1 h2
      have := ih.2
      omega
    · have := hI.dle _ (hG.nh_lt u hu i h1 h2)
      omega

set_option maxHeartbeats 2000000 in
/-- **Dijkstra's algorithm in memory** (see the module docstring). -/
theorem dkProg_exec {p : DkP} (hG : DkG p W) (c : Config) (hc : WordsBounded W c)
    (hM : DkMem p c.nmem)
    (h00 : c.nreg 2500 = p.n) (h01 : c.nreg 2501 = p.Db) (h02 : c.nreg 2502 = p.Xb)
    (h04 : c.nreg 2504 = p.OBb) (h05 : c.nreg 2505 = p.OEb) (h06 : c.nreg 2506 = p.OLb)
    (h07 : c.nreg 2507 = p.NHb) (h08 : c.nreg 2508 = p.Lb) (h09 : c.nreg 2509 = p.Inf)
    (h10 : c.nreg 2510 = p.s) {mm : ℕ} (hdeg : ∑ y ∈ range p.n, (p.oe y - p.ob y) ≤ mm) :
    ∃ c' t, Exec P W dkProg c c' t ∧
      t ≤ 17 * p.n + 13 * lg (2 * p.n) + 22 + p.n * (23 * lg (2 * p.n) + 21) +
        (13 * lg (2 * p.n) + 20) * mm ∧
      (∀ y < p.n, c'.nmem (p.Db + y) ≤ p.Inf ∧
        (c'.nmem (p.Db + y) < p.Inf → DkReach p y (c'.nmem (p.Db + y))) ∧
        ∀ L, DkReach p y L → c'.nmem (p.Db + y) ≤ L) ∧
      (∀ a, ¬ DkOut p a → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2500 ∨ 2548 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hn := hG.n_pos
  obtain ⟨c₁, k₁, e₁, hI₁, hdn₁, hk₁⟩ :=
    dkInit_exec (P := P) hG c hc h00 h01 h02 h04 h05 h06 h07 h08 h09 h10
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 2537)
    (b := 2509) (body := dkRound) (DkIM p W c.nmem) (fun c => dkPot p c.nmem) (fun c h => h.wb)
    (fun c hc hlt => dkRound_exec hG hM c hc hlt) hI₁
  have hcor := DkIM.correct hG hI₂ hn₂
  have e : Exec P W dkProg c c₂ (k₁ + k₂) := e₁ _ _ _ e₂
  have hpot : dkPot p c₁.nmem = p.n * (23 * lg (2 * p.n) + 21) +
      (13 * lg (2 * p.n) + 20) * ∑ y ∈ range p.n, (p.oe y - p.ob y) := by
    unfold dkPot
    rw [sum_congr rfl fun w hw => by rw [ite_eq_left_of_eq_true _ _ (eq_true (hdn₁ w (mem_range.1 hw)))], sum_add_distrib,
      ← mul_sum]
    simp [mul_comm]
  have hpm : (13 * lg (2 * p.n) + 20) * ∑ y ∈ range p.n, (p.oe y - p.ob y) ≤
      (13 * lg (2 * p.n) + 20) * mm := Nat.mul_le_mul_left _ hdeg
  obtain ⟨hrr, hrm, ho⟩ := dk_exec_pure e dkProg_pure
  refine ⟨c₂, k₁ + k₂, e, by beta_reduce at hk₂; rw [hpot] at hk₂; omega,
    fun y hy => ⟨hI₂.dle y hy, fun h => hI₂.reach y hy h, fun L hr => (hcor y L hr).2⟩,
    fun a ha => hI₂.fr a ha, dk_exec_keep e, hrr, hrm, ho⟩

end NegSSSP

end PlanarFlow
