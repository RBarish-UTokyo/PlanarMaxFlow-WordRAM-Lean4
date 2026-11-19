module

public import PlanarFlow.Monge.FRInit

/-!
# FR-Dijkstra on the machine: the whole run

`frProg`: the constants, the vertices and their heap, the empty heap of the half blocks, all
the half blocks (empty triplet structures, range-minimum structures), the root, then the main
loop (`PlanarFlow.Monge.FR.mainLoop_exec`).

* `MSt.init`: the initial state of a run.
* `frProg_exec`: the run computes a run of Dijkstra's algorithm with the price function,
  closed under the arcs (`FRes`), within `frCost P` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-- **FR-Dijkstra with the bipartite Monge heaps and lazy extraction.** -/
def frProg : Stmt :=
  .seq setup <|
  .seq (.instr (.constN 192 0)) <|
  .seq (.whileLtN 192 100 initBody) <|
  .seq (.instr (.copyN 170 100)) <|
  .seq (.whileLtN 110 170 initWinBody) <|
  .seq gxSetup <|
  .seq (block [.copyN 208 241, .copyN 209 242, .copyN 199 243]) <|
  .seq tInit <|
  .seq bLevels <|
  .seq (block [.copyN 175 106, .addN 191 103 106, .loadR 176 191, .constR 175 0,
    .subR 175 175 176]) <|
  .seq decKey <|
  .seq gflag (.whileLtN 117 190 mBody)

variable {P : Prm} {I : Input}

/-- **The initial state of a run**: no vertex settled or present, every half block initialized,
the heap of the half blocks empty. -/
theorem MSt.init (hL : Lay P) {nm : ℕ → ℕ} {rm : ℕ → ℝ} (v : ℕ → ℕ) (d : ℕ → ℤ) (κ : ℝ)
    (hW : WinOK P.N (prV P nm) (keyV P rm) (wnV P nm) 0) (hsf : ∀ y < P.N, sfV P nm y = 0)
    (hpr : ∀ y < P.N, prV P nm y = 0)
    (hB : ∀ t k, 2 ^ t < P.b → k * 2 ^ t < P.b → InitB P nm rm t k) (hbh : BHE P nm rm) :
    MSt P 0 v d κ F2 F1 F2 (fun _ _ _ => False) nm rm := by
  have := hL.bN
  refine ⟨⟨hW, fun y hy => by rw [hpr y hy]; omega, fun y hy => by rw [hsf y hy]; omega,
      fun y hy h => by rw [hpr y hy] at h; omega⟩,
    ⟨fun i hi => by omega, fun y hy => by
        rw [hsf y hy]; exact ⟨fun h => by omega, fun ⟨i, hi, _⟩ => by omega⟩,
      fun i hi => by omega, fun y hy h => by rw [hpr y hy] at h; omega⟩,
    fun u hu h => by rw [hsf u hu] at h; omega, fun y hy h => by rw [hpr y hy] at h; omega,
    fun t k ht hk => ?_, ⟨fun y hy => by rw [hbh.pr y hy]; omega, hbh.win, hbh.wl,
      fun y hy h => by rw [hbh.pr y hy] at h; omega⟩⟩
  have hI := hB t k ht hk
  have hs1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hroot := (win_root hI.win hs1).1
  have h0 : tPr (tbQ P t k) nm (tWn (tbQ P t k) (2 ^ t) nm 1) = 0 := hI.pr _ hroot
  refine ⟨hI.ready, hI.leaf, fun ρ h => h.elim, ⟨fun _ => 0, Or.inl ⟨hI.flag, fun σ hσ => ?_,
    fun ρ h => h, ⟨Nat.min_le_left _ _, fun x hx => by rw [hI.pr x hx]; omega,
      fun x hx h => by rw [hI.pr x hx] at h; omega, fun ρ hρ => ?_, fun ρ h => ⟨h, id⟩,
      fun x y _ hy hx _ => by rw [hI.pr x (by omega)] at hx; omega,
      fun x hx h => by rw [hI.pr x hx] at h; omega,
      fun x hx h => by rw [hI.pr x hx] at h; omega, hI.win, hI.wl⟩⟩⟩, ?_, ?_⟩
  · obtain ⟨h1, h2, -⟩ := hσ
    unfold hbNc at h1; rw [hsf _ (by omega)] at h2; omega
  · refine ⟨fun ⟨_, h⟩ => absurd hρ h, fun ⟨x, hx, hp, _⟩ => ?_⟩
    rw [hI.pr x hx] at hp; omega
  · rw [hbh.pr _ (bid_lt ht hk), h0]; simp
  · intro h; rw [h0] at h; omega

/-- **The cost of the whole run.** -/
noncomputable def frCost (P : Prm) : ℕ :=
  12 + 1 + (P.N * 10 + 2) + 1 + (P.N * 25 + 2) + (4 * P.Lv + 3 * P.TB + 29) + 3 +
    (62 * 2 ^ P.TB + 8) + (∑ t ∈ Finset.range P.Lv, levC P t + 6) + 5 + decCost P.N + 10 +
    ((∑ y ∈ Finset.range P.N, vc P y) + Cx P * (2 * P.b * P.Lv) + 2)

set_option maxHeartbeats 1000000 in
/-- **The whole run of FR-Dijkstra with the bipartite Monge heaps.** From the inputs in the
registers `r100 … r109` and the memory (`Inp`, `Data`), with a Monge (crossing) dense distance
graph and a feasible price function, `frProg` stops within `frCost P` steps, keeping its input
and its output tape; it computes a run `(K, v, d)` of Dijkstra's algorithm with the price
function, closed under the arcs, with the settled flags of exactly the vertices `v i` and their
distances `d i` in the memory. -/
theorem frProg_exec (hL : Lay P) (hDc : Crossing P.b P.D) (hF : Feas P) (c : Config)
    (hc : WordsBounded P.W c) (hin : Inp P c) (hDa : Data P c) :
    ∃ c' k, Exec I P.W frProg c c' k ∧ k ≤ frCost P ∧ Data P c' ∧ c'.output = c.output ∧
      (∀ r < 100, c'.nreg r = c.nreg r) ∧ (∀ r < 100, c'.rreg r = c.rreg r) ∧
      ∃ K v d, FRes P K v d c'.nmem c'.rmem := by
  have hw := lay_w hL
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have hrN := hL.r_lt
  have htb := tb_ge P
  have hbw := bh_le_W hL
  have hbtb : P.tb ≤ P.bh := by unfold Prm.bh; omega
  unfold frProg
  -- the constants
  refine spec_seq ?_
  refine spec_use (setup_exec (I := I) hL c hc hin) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hG₁, hK₁, hR₁, hN₁, hM₁, hO₁⟩
  -- the vertices
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₁ 192 0 (by omega)) fun hw₂ => ?_
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂ at hw₂ ⊢
  have hG₂ : Glob P c₂ := hG₁.of fun r h1 h2 => by rw [← hc₂]; config_simp; upd_tac
  have h192 : c₂.nreg 192 = 0 := by rw [← hc₂]; config_simp
  refine spec_seq ?_
  refine spec_use (initLoop_exec (I := I) hL c₂ hw₂ hG₂ h192) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hG₃, hK₃, hR₃, hM₃, hO₃, hdone₃, hN₃⟩
  refine spec_seq ?_
  refine spec_instr (Exec.copyN hw₃ 170 100) fun hw₄ => ?_
  generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄ at hw₄ ⊢
  have hG₄ : Glob P c₄ := hG₃.of fun r h1 h2 => by rw [← hc₄]; config_simp; upd_tac
  have h170 : c₄.nreg 170 = P.N := by rw [← hc₄]; config_simp; exact hG₃.r100
  have e4N : c₄.nmem = c₃.nmem := by rw [← hc₄]
  refine spec_seq ?_
  refine spec_use (initWin_exec (I := I) hL c₄ hw₄ hG₄ h170
    (fun y hy => by rw [e4N]; exact (hdone₃ y hy).2.2)
    (fun y hy => by rw [e4N, (hdone₃ y hy).2.1]; omega)) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨hG₅, hK₅, hR₅, hM₅, hO₅, hN₅, hW₅⟩
  have hsf₅ : ∀ y < P.N, sfV P c₅.nmem y = 0 ∧ prV P c₅.nmem y = 0 := fun y hy => by
    unfold sfV prV; rw [hN₅ _ (Or.inl (by omega)), hN₅ _ (Or.inl (by omega)), e4N]
    exact ⟨(hdone₃ y hy).1, (hdone₃ y hy).2.1⟩
  have hDa₅ : Data P c₅ := hDa.of hL
    (fun a ha => by rw [hN₅ a (Or.inl (by omega)), e4N, hN₃ a ha, ← hc₂]; config_simp; rw [hN₁])
    (fun a ha => by rw [hM₅, ← hc₄]; config_simp; rw [hM₃, ← hc₂]; config_simp; rw [hM₁])
  -- the constants of the half blocks
  refine spec_seq ?_
  refine spec_use (gxSetup_exec (I := I) hL c₅ hw₅ hG₅) ?_
  intro c₆ k₆ hk₆ hw₆ ⟨hX₆, hK₆, hR₆, hN₆, hM₆, hO₆⟩
  have hG₆ : Glob P c₆ := hG₅.of fun r h1 h2 => hK₆ r (by omega)
  have hDa₆ : Data P c₆ := hDa₅.of hL (fun a _ => by rw [hN₆]) (fun a _ => by rw [hM₆])
  -- the empty heap of the half blocks
  refine spec_seq ?_
  exec_block
  generalize hc₇ : (Config.mk _ _ _ _ _ _ : Config) = c₇
  have hw₇ : WordsBounded P.W c₇ := hc₇ ▸ ‹_›
  have fK7 : ∀ r, r ≠ 208 → r ≠ 209 → r ≠ 199 → c₇.nreg r = c₆.nreg r := fun r h1 h2 h3 => by
    rw [← hc₇]; config_simp; upd_tac
  have hG₇ : Glob P c₇ := hG₆.of fun r h1 h2 => fK7 r (by omega) (by omega) (by omega)
  have hX₇ : GX P c₇ := hX₆.of fun r h1 h2 => fK7 r (by omega) (by omega) (by omega)
  have hT₇ : TCtx P.bh (2 ^ P.TB) c₇ := ⟨by rw [← hc₇]; config_simp; exact hX₆.r241,
    by rw [← hc₇]; config_simp; exact hX₆.r242⟩
  have e7N : c₇.nmem = c₆.nmem := by rw [← hc₇]
  have e7M : c₇.rmem = c₆.rmem := by rw [← hc₇]
  refine spec_seq ?_
  refine spec_use (tInit_exec (I := I) c₇ hw₇ hG₇ hT₇
    (by rw [← hc₇]; config_simp; exact hX₆.r243) Nat.one_le_two_pow hbw) ?_
  intro c₈ k₈ hk₈ hw₈ ⟨hpr₈, hW₈, hWl₈, hn₈, hrm₈, hK₈, hR₈, hO₈⟩
  have hG₈ : Glob P c₈ := hG₇.of fun r h1 h2 => hK₈ r (by omega)
  have hX₈ : GX P c₈ := hX₇.of fun r h1 h2 => hK₈ r (by omega)
  have hlo8 : ∀ a < P.tb, c₈.nmem a = c₅.nmem a := fun a ha => by
    rw [hn₈ a (Or.inl (by omega)), e7N, hN₆]
  have hDa₈ : Data P c₈ := hDa₆.of hL (fun a ha => by rw [hn₈ a (Or.inl (by omega)), e7N])
    (fun a _ => by rw [hrm₈, e7M])
  -- the half blocks
  refine spec_seq ?_
  refine spec_use (bLevels_exec (I := I) hL hDc c₈ hw₈ hG₈ hX₈ hDa₈ ⟨hpr₈, hW₈, hWl₈⟩) ?_
  intro c₉ k₉ hk₉ hw₉ ⟨hG₉, hX₉, hDa₉, hK₉, hR₉, hO₉, hB₉, hlo₉, hrm₉, hbh₉⟩
  have hlo : ∀ a < P.tb, c₉.nmem a = c₅.nmem a := fun a ha => by rw [hlo₉ a ha, hlo8 a ha]
  have hrm : c₉.rmem = c₅.rmem := by rw [hrm₉, hrm₈, e7M, hM₆]
  have hW₉ : WinOK P.N (prV P c₉.nmem) (keyV P c₉.rmem) (wnV P c₉.nmem) 0 :=
    (hW₅.congr_wn fun i h1 h2 => hlo _ (by omega)).congr
      (fun y hy => hlo _ (by omega)) (fun y hy => by unfold keyV; rw [hrm])
  have hsf₉ : ∀ y < P.N, sfV P c₉.nmem y = 0 ∧ prV P c₉.nmem y = 0 := fun y hy => by
    unfold sfV prV; rw [hlo _ (by omega), hlo _ (by omega)]; exact hsf₅ y hy
  have hMS : MSt P 0 (fun _ => 0) (fun _ => 0) ((-P.p P.r : ℤ) : ℝ) F2 F1 F2
      (fun _ _ _ => False) c₉.nmem c₉.rmem :=
    MSt.init hL _ _ _ hW₉ (fun y hy => (hsf₉ y hy).1) (fun y hy => (hsf₉ y hy).2) hB₉ hbh₉
  -- the root
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hG₉.r103, hG₉.r106]; omega
  generalize hc₁₀ : (Config.mk _ _ _ _ _ _ : Config) = c₁₀
  have hw₁₀ : WordsBounded P.W c₁₀ := hc₁₀ ▸ ‹_›
  have f175 : c₁₀.nreg 175 = P.r := by rw [← hc₁₀]; config_simp; exact hG₉.r106
  have r175 : c₁₀.rreg 175 = ((-P.p P.r : ℤ) : ℝ) := by
    rw [← hc₁₀]; config_simp; rw [hG₉.r103, hG₉.r106, hDa₉.pmem _ hrN]; push_cast; ring
  have fK10 : ∀ r, r ≠ 175 → r ≠ 191 → c₁₀.nreg r = c₉.nreg r := fun r h1 h2 => by
    rw [← hc₁₀]; config_simp; upd_tac
  have fR10 : ∀ r, r ≠ 175 → r ≠ 176 → c₁₀.rreg r = c₉.rreg r := fun r h1 h2 => by
    rw [← hc₁₀]; config_simp; upd_tac
  have e10N : c₁₀.nmem = c₉.nmem := by rw [← hc₁₀]
  have e10M : c₁₀.rmem = c₉.rmem := by rw [← hc₁₀]
  have e10O : c₁₀.output = c₉.output := by rw [← hc₁₀]
  have hG₁₀ : Glob P c₁₀ := hG₉.of fun r h1 h2 => fK10 r (by omega) (by omega)
  rw [← e10N, ← e10M] at hMS
  refine spec_seq ?_
  refine spec_use (decKey_exec (I := I) hL c₁₀ hw₁₀ hG₁₀ (by rw [f175]; exact hrN)
    hMS.hp.pr_le (by rw [f175]; exact hMS.hp.sf_le _ hrN) hMS.hp.win) ?_
  intro c₁₁ k₁₁ hk₁₁ hw₁₁ ⟨hp₁₁, hk11, hW₁₁, hK₁₁, hR₁₁, hO₁₁, hN₁₁, hM₁₁⟩
  rw [f175, r175] at hp₁₁ hk11
  rw [f175] at hN₁₁ hM₁₁
  have hD := decEff_of_dec hp₁₁ hk11 hW₁₁ (fun a ha => hN₁₁ a (by omega) (by omega))
    (fun a ha => hM₁₁ a (by omega))
  have hdo : DecDo P c₁₀.nmem c₁₀.rmem P.r ((-P.p P.r : ℤ) : ℝ) := by
    rw [e10N]; exact ⟨(hsf₉ _ hrN).1, Or.inl (hsf₉ _ hrN).2⟩
  have hMS₁₁ := hMS.dec hL hD (fun _ => Or.inl ⟨rfl, rfl⟩) (fun _ => le_rfl)
  have hroot₁₁ : prV P c₁₁.nmem P.r = 1 := hD.pr1 _ hrN hdo rfl
  have hG₁₁ : Glob P c₁₁ := hG₁₀.of fun r h1 h2 => hK₁₁ r (by omega)
  have hX₁₁ : GX P c₁₁ := hX₉.of fun r h1 h2 => by
    rw [hK₁₁ r (by omega), fK10 r (by omega) (by omega)]
  have hDa₁₁ : Data P c₁₁ := hDa₉.of hL
    (fun a ha => by rw [hN₁₁ a (by omega) (by omega), e10N])
    (fun a ha => by rw [hM₁₁ a (by omega), e10M])
  -- the flag
  refine spec_seq ?_
  refine spec_use (gflag_exec (I := I) hL c₁₁ hw₁₁ hG₁₁ hX₁₁ hMS₁₁.hp.win hMS₁₁.hp.pr_le
    hMS₁₁.bh) ?_
  intro c₁₂ k₁₂ hk₁₂ hw₁₂ ⟨h190, hK₁₂, hR₁₂, hN₁₂, hM₁₂, hO₁₂⟩
  have kN : ∀ r < 100, c₁₂.nreg r = c.nreg r := fun r hr => by
    rw [hK₁₂ r (by omega) (by omega) (by omega) (by omega), hK₁₁ r (by omega),
      fK10 r (by omega) (by omega), hK₉ r hr, hK₈ r (by omega), fK7 r (by omega) (by omega)
      (by omega), hK₆ r (by omega), hK₅ r (by omega), ← hc₄]
    config_simp
    rw [upd_other _ _ _ (by omega), hK₃ r (by omega) (by omega), ← hc₂]
    config_simp
    rw [upd_other _ _ _ (by omega), hK₁ r hr]
  have kR : ∀ r < 100, c₁₂.rreg r = c.rreg r := fun r hr => by
    rw [hR₁₂, hR₁₁ r (by omega), fR10 r (by omega) (by omega), hR₉ r hr, hR₈ r (by omega)
      (by omega), ← hc₇]
    config_simp
    rw [hR₆, hR₅ r (by omega), ← hc₄]
    config_simp
    rw [hR₃, ← hc₂]
    config_simp
    rw [hR₁]
  have kO : c₁₂.output = c.output := by
    rw [hO₁₂, hO₁₁, e10O, hO₉, hO₈, ← hc₇]
    config_simp
    rw [hO₆, hO₅, ← hc₄]
    config_simp
    rw [hO₃, ← hc₂]
    config_simp
    rw [hO₁]
  have hMI : MI P c (0, fun _ => 0, fun _ => 0, ((-P.p P.r : ℤ) : ℝ), fun _ _ _ => False) c₁₂ :=
    ⟨hw₁₂, hG₁₁.of fun r h1 h2 => hK₁₂ r (by omega) (by omega) (by omega) (by omega),
      hX₁₁.of fun r h1 h2 => hK₁₂ r (by omega) (by omega) (by omega) (by omega),
      hDa₁₁.of hL (fun a _ => by rw [hN₁₂]) (fun a _ => by rw [hM₁₂]), kN, kR, kO,
      by rw [hN₁₂, hM₁₂]; exact hMS₁₁, ⟨fun h => by omega, fun h => by omega,
        fun i j hi => by omega, fun k _ hk => by omega, fun k hk => by omega⟩,
      by rw [h190, hN₁₂], fun _ => by rw [hN₁₂]; exact hroot₁₁⟩
  -- the main loop
  refine spec_use (mainLoop_exec (I := I) hL hDc hF _ c₁₂ hMI) ?_
  intro c₁₃ k₁₃ hk₁₃ hw₁₃ ⟨hG₁₃, hX₁₃, hDa₁₃, hK₁₃, hR₁₃, hO₁₃, hres⟩
  refine ⟨?_, hDa₁₃, hO₁₃, hK₁₃, hR₁₃, hres⟩
  -- the cost
  have hpotS : potS P c₁₂.nmem = ∑ y ∈ Finset.range P.N, vc P y := by
    unfold potS
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' := Finset.mem_range.1 hy
    have : sfV P c₁₂.nmem y = 0 := by
      have h1 := hMS₁₁.gh.sf y hy'
      have h2 := hMS₁₁.hp.sf_le y hy'
      unfold sfV at h1 h2 ⊢; rw [hN₁₂]
      by_contra h; obtain ⟨i, hi, -⟩ := h1.1 (by omega); omega
    simp only [this, ↓reduceIte]
  have hpotN : potN P c₁₂.nmem = 0 := by
    unfold potN
    refine bSum_zero fun t k ht hk => ?_
    have : nst (tbQ P t k) (2 ^ t) c₁₂.nmem = 0 := by
      unfold nst
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro x hx
      have hx' := Finset.mem_range.1 hx
      have hQb := tbQ_le_bh ht hk
      have hQt : P.tb ≤ tbQ P t k := tb_le_tbQ
      unfold tPr
      rw [hN₁₂, hN₁₁ _ (by omega) (by omega), e10N]
      have := (hB₉ t k ht hk).pr x hx'
      unfold tPr at this; omega
    rw [this, Nat.mul_zero]
  have hpot : pot P (fun _ _ _ => False) c₁₂.nmem ≤
      ∑ y ∈ Finset.range P.N, vc P y + Cx P * (2 * P.b * P.Lv) := by
    unfold pot; rw [hpotS, hpotN]
    have := Nat.mul_le_mul_left (Cx P) (potX_le (P := P) (X := fun _ _ _ => False))
    omega
  simp only at hk₁₃
  unfold frCost
  omega

end FR

end Monge

end PlanarFlow
