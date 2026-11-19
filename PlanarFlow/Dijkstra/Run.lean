module

public import PlanarFlow.Dijkstra.Loop

/-!
# Dijkstra's algorithm on the machine: the main theorem

**`PlanarFlow.Dijk.dijkstra_runsWithin`.** On a well-formed input (`PlanarFlow.Dijk.DEnc`) with
`n` vertices and `m` arcs of nonnegative lengths, the program halts within
`(n + m + 1)(36 log₂ n + 143)` steps and prints the distances `D 0, …, D (n-1)` from the source:
`D v ≤ INF`; every walk from the source to `v` has length at least `D v`; and if `D v < INF` some
walk from the source to `v` has length exactly `D v`. (With `INF` larger than the total length of
the arcs, `D v = INF` means that `v` is unreachable.)

This is Dijkstra's algorithm with a binary heap with decrease-key (a tournament tree over the
vertices), `O((n + m) log n)`.

## References

* E. W. Dijkstra, *A note on two problems in connexion with graphs*, Numer. Math. 1 (1959),
  269–271.
* J. W. J. Williams, *Algorithm 232: Heapsort*, Comm. ACM 7 (1964), 347–348.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Dijk

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset Heap

variable {d : List ℕ} {W : ℕ}

lemma sum_deg (he : DEnc d W) : ∀ k ≤ nn d, ∑ v ∈ range k, (off d (v + 1) - off d v) = off d k := by
  intro k hk
  induction k with
  | zero => simp [he.off_zero]
  | succ k ih =>
    rw [sum_range_succ, ih (by omega)]
    have := he.off_mono k (by omega)
    omega

/-! ### Initialization -/

/-- The state of the initialization of the distances. -/
structure ID0 (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r40 : c.nreg 40 ≤ nn d
  done : ∀ v < c.nreg 40, c.nmem v = inf d
  zero : ∀ a, nn d ≤ a → c.nmem a = 0

theorem distStep_exec (he : DEnc d W) (c : Config) (hI : ID0 d W c) (hlt : c.nreg 40 < c.nreg 2) :
    ∃ c' k, Exec (inp d) W distStep c c' k ∧ ID0 d W c' ∧
      (nn d - c'.nreg 40) * 4 + k + 2 ≤ (nn d - c.nreg 40) * 4 := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.regs
  rw [h2] at hlt
  unfold distStep
  exec_block
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, regs_of hI.regs fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)],
    by config_simp; exact hI.out, by config_simp; rw [h1]; omega, fun v hv => ?_, fun a ha => ?_⟩,
    by config_simp; rw [h1]; omega⟩
  · config_simp at hv; rw [h1] at hv; config_simp
    rw [upd_apply]; split_ifs with h
    · exact h3
    · exact hI.done v (by omega)
  · config_simp; rw [upd_other _ _ _ (by omega)]; exact hI.zero a ha

/-- The state of the initialization of the tree. -/
structure IT0 (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r40 : 1 ≤ c.nreg 40 ∧ c.nreg 40 ≤ 2 * nn d
  done : ∀ i, 1 ≤ i → i < c.nreg 40 → c.nmem (2 * nn d + i) = inf d
  dist : ∀ v < nn d, c.nmem v = inf d
  zero : ∀ a, nn d ≤ a → a < 2 * nn d + 1 → c.nmem a = 0

theorem treeStep_exec (he : DEnc d W) (c : Config) (hI : IT0 d W c) (hlt : c.nreg 40 < c.nreg 4) :
    ∃ c' k, Exec (inp d) W treeStep c c' k ∧ IT0 d W c' ∧
      (2 * nn d - c'.nreg 40) * 5 + k + 2 ≤ (2 * nn d - c.nreg 40) * 5 := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.regs
  rw [h4] at hlt
  unfold treeStep
  exec_block
  · config_simp; rw [h4]; omega
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, regs_of hI.regs fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega,
    by config_simp; exact hI.out, by config_simp; rw [h1]; omega, fun i hi1 hi2 => ?_,
    fun v hv => ?_, fun a ha1 ha2 => ?_⟩, by config_simp; rw [h1]; omega⟩
  · config_simp at hi2; rw [h1] at hi2; config_simp
    rw [upd_apply, h4]; split_ifs with h
    · exact h3
    · exact hI.done i hi1 (by omega)
  · config_simp; rw [upd_other _ _ _ (by rw [h4]; omega)]; exact hI.dist v hv
  · config_simp; rw [upd_other _ _ _ (by rw [h4]; have := hI.r40; omega)]; exact hI.zero a ha1 ha2

/-- The initialization, followed by `t`. -/
def initPart (t : Stmt) : Stmt := .seq setup <| .seq (.whileLtN 40 2 distStep) <|
  .seq (.instr (.constN 40 1)) <| .seq (.whileLtN 40 4 treeStep) <|
  .seq (block [.storeN 8 0, .addN 40 2 8, .addN 41 4 40, .storeN 41 0, .divN 40 40 6]) <|
  .seq updS <| .seq (block [.addN 48 4 1, .loadN 47 48]) t

lemma prog_eq : prog = initPart (.seq (.whileLtN 47 3 round)
    (.seq (.instr (.copyN 55 0)) (.whileLtN 55 2 outStep))) := rfl

/-- **Initialization.** -/
theorem init_exec (he : DEnc d W) :
    ∃ c k, (∀ t c' k', Exec (inp d) W t c c' k' → Exec (inp d) W (initPart t) initConfig c' (k + k'))
      ∧ IM d W c ∧
      (∀ v < nn d, c.nmem (nn d + v) = 0) ∧ k ≤ 14 * nn d + 13 * lg (2 * nn d) + 23 := by
  have hs := he.size
  have hn := he.n_pos
  have hsrc := he.src_lt
  have hw : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  -- the constants
  obtain ⟨c₁, k₁, e₁, hw₁, hpost⟩ : ∃ c₁ k₁, Exec (inp d) W setup initConfig c₁ k₁ ∧
      WordsBounded W c₁ ∧ (Regs d c₁ ∧ c₁.nreg 40 = 0 ∧ c₁.nmem = (fun _ => 0) ∧ c₁.output = [] ∧
        k₁ = 11) := by
    unfold setup
    exec_block
    · omega
    · exact he.word_le _
    · omega
    · omega
    · exact he.word_le _
    · exact he.word_le _
    · config_simp; simp only [initConfig, inp, nn, word] at hs ⊢; omega
    · omega
    · config_simp; simp only [initConfig, inp, nn, word] at hs ⊢; omega
    · config_simp; simp only [initConfig, inp, nn, word] at hs ⊢; omega
    refine ⟨‹_›, ?_, by config_simp; rfl, by config_simp; rfl, by config_simp; rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      simp [initConfig, inp, nn, inf, src, word] <;> omega
  obtain ⟨hR₁, h40₁, hm₁, ho₁, rfl⟩ := hpost
  -- the distances
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 40)
    (b := 2) (body := distStep) (ID0 d W) (fun c => (nn d - c.nreg 40) * 4) (fun c h => h.wb)
    (fun c hc hlt => distStep_exec he c hc hlt)
    ⟨hw₁, hR₁, ho₁, by omega, fun v hv => by omega, fun a _ => by rw [hm₁]⟩
  have h40₂ : c₂.nreg 40 = nn d := by have := hI₂.r40; rw [hI₂.regs.2.2.1] at hn₂; omega
  have e₃ := Exec.constN (P := inp d) hI₂.wb 40 1 (by omega)
  -- the tree
  obtain ⟨c₄, k₄, e₄, hI₄, hn₄, hk₄⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 40)
    (b := 4) (body := treeStep) (IT0 d W) (fun c => (2 * nn d - c.nreg 40) * 5) (fun c h => h.wb)
    (fun c hc hlt => treeStep_exec he c hc hlt)
    ⟨e₃.wb_right, regs_of hI₂.regs fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)],
      hI₂.out, by config_simp; omega, fun i h1 h2 => by config_simp at h2; omega,
      fun v hv => hI₂.done v (by omega), fun a h1 _ => hI₂.zero a h1⟩
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := hI₄.regs
  have h40₄ : c₄.nreg 40 = 2 * nn d := by have := hI₄.r40; rw [g4] at hn₄; omega
  have hc₄ := hI₄.wb
  have hTour : IsTour (nn d) (tv d c₄.nmem) := fun i h1 h2 => by
    simp only [tv]; rw [hI₄.done i h1 (by omega), hI₄.done _ (by omega) (by omega),
      hI₄.done _ (by omega) (by omega)]; simp
  -- the source
  obtain ⟨c₅, k₅, e₅, hw₅, hpost⟩ : ∃ c₅ k₅, Exec (inp d) W (block [.storeN 8 0, .addN 40 2 8,
      .addN 41 4 40, .storeN 41 0, .divN 40 40 6]) c₄ c₅ k₅ ∧ WordsBounded W c₅ ∧
      (k₅ = 5 ∧ (∀ r < 40, c₅.nreg r = c₄.nreg r) ∧ c₅.nreg 40 = (nn d + src d) / 2 ∧
        c₅.output = c₄.output ∧
        c₅.nmem = upd (upd c₄.nmem (src d) 0) (2 * nn d + (nn d + src d)) 0) := by
    exec_block
    · config_simp; rw [g2, g8]; omega
    · config_simp; rw [g2, g8, g4]; omega
    refine ⟨‹_›, rfl, fun r hr => ?_, by config_simp; rw [g2, g8, g6], by config_simp,
      by config_simp; rw [g8, g0, g4, g2]⟩
    config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
  obtain ⟨rfl, hK₅, h40₅, ho₅, hm₅⟩ := hpost
  have hR₅ := regs_of ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ fun r hr => hK₅ r (by omega)
  have hexc : IsTourExc (nn d) (tv d c₅.nmem) (c₅.nreg 40) := by
    rw [h40₅]
    exact isTourExc_set hTour (by omega) fun a ha => by
      simp only [tv, hm₅, upd_apply]; split_ifs <;> first | omega | rfl
  obtain ⟨c₆, k₆, e₆, hw₆, hK₆, ho₆, hT₆, hf₆, hk₆⟩ := upd_exec he c₅ hw₅ hR₅
    (by rw [h40₅]; omega) hexc
  have hR₆ := regs_of hR₅ fun r hr => hK₆ r (Or.inl (by omega))
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ := hR₆
  obtain ⟨c₇, k₇, e₇, hw₇, hpost⟩ : ∃ c₇ k₇, Exec (inp d) W (block [.addN 48 4 1, .loadN 47 48])
      c₆ c₇ k₇ ∧ WordsBounded W c₇ ∧ (k₇ = 2 ∧ (∀ r < 40, c₇.nreg r = c₆.nreg r) ∧
        c₇.nreg 47 = tv d c₆.nmem 1 ∧ c₇.output = c₆.output ∧ c₇.nmem = c₆.nmem) := by
    exec_block
    · config_simp; rw [f4, f1]; omega
    refine ⟨‹_›, rfl, fun r hr => ?_, by config_simp; rw [f4, f1]; rfl, by config_simp,
      by config_simp⟩
    config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega
  obtain ⟨rfl, hK₇, h47₇, ho₇, hm₇⟩ := hpost
  -- the memory
  have hmem : ∀ a, (a < 2 * nn d + 1 ∨ 3 * nn d ≤ a) → c₇.nmem a =
      if a = 2 * nn d + (nn d + src d) then 0 else if a = src d then 0 else c₄.nmem a := by
    intro a ha; rw [hm₇, hf₆ a ha, hm₅]; simp only [upd_apply]
  have hdist : ∀ x < nn d, c₇.nmem x = if x = src d then 0 else inf d := by
    intro x hx; rw [hmem x (by omega)]
    split_ifs <;> first | omega | rfl | exact hI₄.dist x hx
  have hdn : ∀ x < nn d, c₇.nmem (nn d + x) = 0 := by
    intro x hx; rw [hmem _ (by omega)]
    split_ifs <;> first | omega | rfl | exact hI₄.zero _ (by omega) (by omega)
  refine ⟨c₇, 11 + (k₂ + (1 + (k₄ + (5 + (k₆ + 2))))), fun t c' k' et =>
    (Exec.seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ et))))))).cast (by omega),
    ⟨hw₇, regs_of ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8⟩ fun r hr => hK₇ r (by omega),
      by rw [ho₇, ho₆, ho₅, hI₄.out], by rw [hm₇]; exact hT₆, fun x hx => ?_,
      fun x hx => Or.inl (hdn x hx), fun x hx => by rw [hdist x hx]; split_ifs <;> omega,
      ⟨0, fun x hx h => by rw [hdn x hx] at h; omega, fun _ _ _ => Nat.zero_le _⟩,
      fun u hu h => by rw [hdn u hu] at h; omega, fun x hx h => ?_,
      by rw [hdist _ hsrc]; simp, by rw [h47₇, hm₇]⟩, hdn, ?_⟩
  · simp only [tv]; rw [hmem _ (by omega), hdn x hx, hdist x hx]
    by_cases hxs : x = src d
    · simp [hxs]
    · simp only [hxs, ite_false, show 2 * nn d + (nn d + x) ≠ 2 * nn d + (nn d + src d) by omega,
        show 2 * nn d + (nn d + x) ≠ src d by omega]
      exact hI₄.done _ (by omega) (by omega)
  · rw [hdist x hx] at h ⊢
    by_cases hxs : x = src d
    · subst hxs; simp; exact Reach.src
    · simp [hxs] at h
  · beta_reduce at hk₂ hk₄
    config_simp at hk₄
    rw [h40₁] at hk₂
    have := lg_mono (show (nn d + src d) / 2 ≤ 2 * nn d by omega)
    rw [h40₅] at hk₆
    omega

/-! ### The output -/

/-- The state of the output. -/
structure IO (d : List ℕ) (W : ℕ) (D : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  r55 : c.nreg 55 ≤ nn d
  mem : c.nmem = D
  out : c.output = (List.range (c.nreg 55)).map D

theorem outStep_exec (he : DEnc d W) {D : ℕ → ℕ} (c : Config) (hI : IO d W D c)
    (hlt : c.nreg 55 < c.nreg 2) :
    ∃ c' k, Exec (inp d) W outStep c c' k ∧ IO d W D c' ∧
      (nn d - c'.nreg 55) * 5 + k + 2 ≤ (nn d - c.nreg 55) * 5 := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI.regs
  rw [h2] at hlt
  unfold outStep
  exec_block
  · config_simp; rw [h1]; omega
  refine ⟨⟨‹_›, regs_of hI.regs fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega,
    by config_simp; rw [h1]; omega, by config_simp; exact hI.mem, ?_⟩, by config_simp; rw [h1]; omega⟩
  config_simp; rw [h1, hI.out, List.range_succ, List.map_append, hI.mem]; simp

/-! ### The main theorem -/

/-- The distances computed are the shortest walk lengths. -/
theorem IM.correct (he : DEnc d W) {c : Config} (hI : IM d W c) (hend : ¬ c.nreg 47 < c.nreg 3) :
    ∀ v ℓ, Reach d v ℓ → v < nn d ∧ c.nmem v ≤ ℓ := by
  have h3 := hI.regs.2.2.2.1
  rw [hI.r47, h3] at hend
  -- every vertex not done is at infinity
  have hinf : ∀ w < nn d, c.nmem (nn d + w) = 0 → c.nmem w = inf d := by
    intro w hw h
    have h1 := root_le hI.tour (l := nn d + w) (by omega) (by omega)
    have h2 := hI.leaf w hw
    rw [h] at h2; simp at h2
    have := hI.dle w hw
    omega
  intro v ℓ hr
  induction hr with
  | src => exact ⟨he.src_lt, by rw [hI.srcz]⟩
  | @step u ℓ j _ hu h1 h2 ih =>
    have hj := arc_lt he hu h2
    refine ⟨he.dst_lt j hj, ?_⟩
    by_cases hfin : c.nmem u < inf d
    · have hdone : c.nmem (nn d + u) = 1 := by
        rcases hI.done01 u hu with h | h
        · rw [hinf u hu h] at hfin; omega
        · exact h
      have := hI.relaxed u hu hdone j h1 h2
      omega
    · have := hI.dle _ (he.dst_lt j hj)
      omega

/-- **Dijkstra's algorithm on the machine.** -/
theorem dijkstra_runsWithin (he : DEnc d W) :
    ∃ D : ℕ → ℕ, (∀ v < nn d, D v ≤ inf d ∧ (D v < inf d → Reach d v (D v)) ∧
        ∀ ℓ, Reach d v ℓ → D v ≤ ℓ) ∧
      RunsWithin (compile prog 0 ++ [Instr.halt]) (inp d) W
        ((nn d + mm d + 1) * (36 * Nat.log 2 (nn d) + 143)) ((List.range (nn d)).map D) := by
  have hn := he.n_pos
  obtain ⟨c₁, k₁, e₁, hI₁, hdn₁, hk₁⟩ := init_exec he
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 47)
    (b := 3) (body := round) (IM d W) (fun c => pot d c.nmem) (fun c h => h.wb)
    (fun c hc hlt => round_exec he c hc hlt) hI₁
  have hcor := IM.correct he hI₂ hn₂
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hI₂.regs
  have e₃ := Exec.copyN (P := inp d) hI₂.wb 55 0
  obtain ⟨c₄, k₄, e₄, hI₄, hn₄, hk₄⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 55)
    (b := 2) (body := outStep) (IO d W c₂.nmem) (fun c => (nn d - c.nreg 55) * 5)
    (fun c h => h.wb) (fun c hc hlt => outStep_exec he c hc hlt)
    ⟨e₃.wb_right, regs_of hI₂.regs fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)],
      by config_simp; omega, rfl, by config_simp; rw [h0, hI₂.out]; rfl⟩
  have h55 : c₄.nreg 55 = nn d := by have := hI₄.r55; rw [hI₄.regs.2.2.1] at hn₄; omega
  have e : Exec (inp d) W prog initConfig c₄ (k₁ + (k₂ + (1 + k₄))) := by
    rw [prog_eq]; exact e₁ _ _ _ (.seq e₂ (.seq e₃ e₄))
  obtain ⟨k', hk', hr1, hr2⟩ := runsWithin_of_exec_output e (by rw [hI₄.out, h55])
  refine ⟨c₂.nmem, fun v hv => ⟨hI₂.dle v hv, fun h => hI₂.reach v hv h,
    fun ℓ hr => (hcor v ℓ hr).2⟩, k', ?_, hr1, hr2⟩
  -- the cost
  have hpot : pot d c₁.nmem = nn d * (23 * lg (2 * nn d) + 21) +
      (13 * lg (2 * nn d) + 18) * mm d := by
    unfold pot
    have hsum : (∑ w ∈ range (nn d), if c₁.nmem (nn d + w) = 0 then
        (23 * lg (2 * nn d) + 21) + (13 * lg (2 * nn d) + 18) * (off d (w + 1) - off d w)
        else 0) = ∑ w ∈ range (nn d),
        ((23 * lg (2 * nn d) + 21) + (13 * lg (2 * nn d) + 18) * (off d (w + 1) - off d w)) :=
      sum_congr rfl fun w hw => by simp [hdn₁ w (mem_range.1 hw)]
    rw [hsum, sum_add_distrib, ← mul_sum, sum_deg he _ le_rfl, he.off_last]
    simp [mul_comm]
  have hL : lg (2 * nn d) = Nat.log 2 (nn d) + 2 := by
    rw [lg_eq_log (by omega), show 2 * nn d = nn d * 2 by ring, Nat.log_mul_base (by norm_num)
      (by omega)]
  beta_reduce at hk₂ hk₄
  config_simp at hk₄
  rw [h0] at hk₄
  rw [hL] at hpot hk₁
  rw [hpot] at hk₂
  generalize Nat.log 2 (nn d) = X at *
  have e1 : (nn d + mm d + 1) * (36 * X + 143) = 36 * (nn d * X) + 36 * (mm d * X) + 36 * X +
      143 * nn d + 143 * mm d + 143 := by ring
  have e2 : nn d * (23 * (X + 2) + 21) + (13 * (X + 2) + 18) * mm d =
      23 * (nn d * X) + 67 * nn d + 13 * (mm d * X) + 44 * mm d := by ring
  rw [e1]; rw [e2] at hk₂
  omega

end Dijk

end PlanarFlow
