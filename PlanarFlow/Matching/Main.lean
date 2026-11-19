module

public import PlanarFlow.Matching.Search

/-!
# Maximum bipartite matching on the machine: augmentation, phases, the main theorem

**`PlanarFlow.BM.matching_runsWithin`.** On a well-formed input (`PlanarFlow.BM.Enc`) with `n`
vertices and `m` arcs, the program halts within `80 (n + 1)(n + m + 1)` steps and prints the size
of a maximum matching: some matching has this size and none is larger.

Each phase costs `O(n + m)` and all but the last enlarge the matching, so there are at most
`n + 1` phases. For a plane bipartite graph without parallel edges, `m ≤ 2n` and the bound is
`O(n²)` (`PlanarFlow.BM.matching_runsWithin_sparse`).

## References

* C. Berge, *Two theorems in graph theory*, Proc. Nat. Acad. Sci. 43 (1957), 842–844.
* L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*, Canad. J. Math. 8 (1956),
  399–404.
* D. Kőnig, *Gráfok és mátrixok*, Mat. Fiz. Lapok 38 (1931), 116–119.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BM

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

variable {d : List ℕ} {W : ℕ}

lemma upd_eq_update (f : ℕ → ℕ) (i v : ℕ) : upd f i v = Function.update f i v := by
  funext a; simp only [upd_apply, Function.update_apply]

/-! ### The augmentation -/

/-- The state of the augmentation from the matching `μ₀` (of size `s`), after the search left
the memory `mb`. -/
structure IA (d : List ℕ) (W : ℕ) (μ₀ : ℕ → ℕ) (s : ℕ) (D : ℕ → Prop) (mb : ℕ → ℕ)
    (tail t found : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  r20 : c.nreg 20 = s
  r21 : c.nreg 21 = 1
  frame : ∀ a, nn d ≤ a → c.nmem a = mb a
  done : c.nreg 39 = 0 → Valid d c.nmem ∧ size d c.nmem = size d μ₀ + 1
  run : c.nreg 39 ≠ 0 → c.nreg 39 - 1 < nn d ∧ col d (c.nreg 39 - 1) = 0 ∧
    vs d mb (c.nreg 39 - 1) = 1 ∧ ValidExc d c.nmem (c.nreg 39 - 1) ∧
    size d c.nmem = size d μ₀ ∧
    ∀ v < nn d, vs d mb v = 1 → tmv d mb v < tmv d mb (c.nreg 39 - 1) → c.nmem v = μ₀ v

/-- The potential of the augmentation. -/
def potA (mb : ℕ → ℕ) (d : List ℕ) (c : Config) : ℕ :=
  if c.nreg 39 = 0 then 0 else (tmv d mb (c.nreg 39 - 1) + 1) * 11

theorem augBody_exec (he : Enc d W) {μ₀ : ℕ → ℕ} {s : ℕ} {D : ℕ → Prop} {mb : ℕ → ℕ}
    {tail t found : ℕ} (hbs : BS d μ₀ D mb tail t found) (c : Config)
    (hI : IA d W μ₀ s D mb tail t found c) (hlt : c.nreg 0 < c.nreg 39) :
    ∃ c' k, Exec (inp d) W augBody c c' k ∧ IA d W μ₀ s D mb tail t found c' ∧
      potA mb d c' + k + 2 ≤ potA mb d c := by
  have hc := hI.wb
  have hs := he.size
  obtain ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ := hI.regs
  rw [h0] at hlt
  obtain ⟨hbn, hcb, hvb, hE, hsz, hun⟩ := hI.run (by omega)
  generalize hb : c.nreg 39 - 1 = b at hbn hcb hvb hE hsz hun
  obtain ⟨hwn, hwv, harc, htw, -, -⟩ := hbs.bvis b hbn hcb hvb
  generalize hw : pa d mb b = w at hwn hwv harc htw
  have hcw := (he.arc_col _ _ harc).1
  have hwb : w ≠ b := fun e => by rw [e] at hcw; omega
  have hμw : c.nmem w = μ₀ w := hun w hwn hwv htw
  have hpar : c.nmem (c.nreg 8 + (c.nreg 39 - c.nreg 1)) = w := by
    rw [h8, h1, hb, hI.frame _ (by omega)]; exact hw
  have htmb : tmv d mb b < nn d := by
    have := hbs.tmlt b hbn hvb; have := hbs.tcnt; have := nvis_le (d := d) mb; omega
  have hb2 : c.nreg 39 = b + 1 := by omega
  unfold augBody
  exec_block
  · config_simp; rw [h8, h1, hb]; omega
  · config_simp; rw [h1, hb]; omega
  · config_simp; rw [hpar]; omega
  config_simp
  rw [hpar, h1, hb] at *
  obtain ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ := hI.regs
  have hmem : upd (upd c.nmem w (b + 1)) b (w + 1) =
      Function.update (Function.update c.nmem w (b + 1)) b (w + 1) := by
    rw [upd_eq_update, upd_eq_update]
  have hR' : ∀ c' : Config, (∀ r < 20, c'.nreg r = c.nreg r) → Regs d c' := fun c' h =>
    regs_of ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ h
  refine ⟨⟨‹_›, hR' _ fun r hr => by config_simp; simp (disch := omega) only [upd_other],
    by config_simp; exact hI.out, by config_simp; exact hI.r20, by config_simp; exact hI.r21,
    fun a ha => ?_, fun h39 => ?_, fun h39 => ?_⟩, ?_⟩
  · config_simp; rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
    exact hI.frame a ha
  · config_simp at h39
    rw [hmem]
    have hw0 : c.nmem w = 0 := h39
    refine ⟨flip_last he.toWf hE hbn harc hwb hw0, ?_⟩
    rw [size_flip hwn hcw hcb, hsz, hw0]; simp
  · config_simp at h39; config_simp
    rw [hmem]
    have hm0 : c.nmem w ≠ 0 := h39
    have hm0' : μ₀ w ≠ 0 := by rw [← hμw]; exact hm0
    obtain ⟨hb'n, -, hback, harcw, -⟩ := hE w hwn hwb hm0
    obtain ⟨hvb', htb'⟩ := hbs.wmat w hwn hcw hwv hm0'
    rw [← hμw] at hvb' htb'
    have hcb' := (he.arc_col _ _ (harcw hcw)).2
    have hb'b : c.nmem w - 1 ≠ b := fun e => by rw [e] at htb'; omega
    refine ⟨hb'n, hcb', hvb', flip_step he.toWf hE hbn harc hwb hm0 hb'b, ?_, fun v hv hvv htv => ?_⟩
    · rw [size_flip hwn hcw hcb, hsz]; simp [hm0]
    · have hvw : v ≠ w := fun e => by rw [e] at htv; omega
      have hvb : v ≠ b := fun e => by rw [e] at htv; omega
      rw [Function.update_of_ne hvb, Function.update_of_ne hvw]
      exact hun v hv hvv (by omega)
  · unfold potA
    config_simp
    simp only [show c.nreg 39 ≠ 0 by omega, ite_false]
    rw [show c.nreg 39 - 1 = b by omega]
    split_ifs with h39
    · omega
    · have hm0 : c.nmem w ≠ 0 := h39
      have hm0' : μ₀ w ≠ 0 := by rw [← hμw]; exact hm0
      obtain ⟨-, htb'⟩ := hbs.wmat w hwn hcw hwv hm0'
      rw [← hμw] at htb'
      omega

/-! ### A phase -/

/-- The state between phases. -/
structure IP (d : List ℕ) (W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : Regs d c
  out : c.output = []
  valid : Valid d c.nmem
  r20 : c.nreg 20 = size d c.nmem
  r21 : c.nreg 21 = 1 ∨ (c.nreg 21 = 0 ∧ ∀ M, IsMatching d M → M.card ≤ size d c.nmem)

/-- The cost of a phase. -/
def pcost (d : List ℕ) : ℕ := 80 * nn d + 30 * mm d + 20

/-- The potential of the phases. -/
def potP (d : List ℕ) (c : Config) : ℕ :=
  if c.nreg 21 = 0 then 0 else (nn d + 1 - c.nreg 20) * pcost d

lemma valid_congr {μ μ' : ℕ → ℕ} (h : ∀ v < nn d, μ' v = μ v) (hμ : Valid d μ) : Valid d μ' := by
  intro x hx hm
  rw [h x hx] at hm ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hμ x hx hm
  exact ⟨h1, by rw [h _ h1]; exact h2, h3, h4⟩

lemma size_congr {μ μ' : ℕ → ℕ} (h : ∀ v < nn d, μ' v = μ v) : size d μ' = size d μ := by
  unfold size; congr 1; ext v; simp only [mem_filter, mem_range]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> refine ⟨h1, h2, ?_⟩ <;> simp_all

theorem phase_exec (he : Enc d W) (c : Config) (hI : IP d W c) (hlt : c.nreg 0 < c.nreg 21) :
    ∃ c' k, Exec (inp d) W phase c c' k ∧ IP d W c' ∧ potP d c' + k + 2 ≤ potP d c := by
  have hc := hI.wb
  obtain ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ := hI.regs
  have h21 : c.nreg 21 = 1 := by
    rcases hI.r21 with h | ⟨h, -⟩
    · exact h
    · omega
  have hsn := size_le (d := d) c.nmem
  generalize hμ : c.nmem = μ at hsn
  have hvalid : Valid d μ := hμ ▸ hI.valid
  have hs20 : c.nreg 20 = size d μ := hμ ▸ hI.r20
  -- the start of the phase
  obtain ⟨c₁, k₁, e₁, hw₁, hpost⟩ : ∃ c₁ k₁, Exec (inp d) W (block [.copyN 22 0, .copyN 23 0,
      .copyN 24 0, .copyN 25 0]) c c₁ k₁ ∧ WordsBounded W c₁ ∧ (k₁ = 4 ∧
      (∀ r, r ≠ 22 → r ≠ 23 → r ≠ 24 → r ≠ 25 → c₁.nreg r = c.nreg r) ∧ c₁.nreg 22 = 0 ∧
      c₁.nreg 23 = 0 ∧ c₁.nreg 24 = 0 ∧ c₁.nreg 25 = 0 ∧ c₁.nmem = c.nmem ∧
      c₁.output = c.output) := by
    exec_block
    refine ⟨‹_›, rfl, fun r a b e f => ?_, by config_simp; exact h0, by config_simp; exact h0,
      by config_simp; exact h0, by config_simp; exact h0, by config_simp, by config_simp⟩
    config_simp; simp (disch := omega) only [upd_other]
  obtain ⟨rfl, hK₁, a22, a23, a24, a25, hm₁, ho₁⟩ := hpost
  have hR₁ := regs_of ⟨h0, h1, h2, h4, h5, h6, h8, h9, h10⟩ fun r hr =>
    hK₁ r (by omega) (by omega) (by omega) (by omega)
  -- the clear loop
  obtain ⟨c₂, k₂, e₂, hw₂, hR₂, h20₂, h21₂, ho₂, hbs₂, h25₂, hk₂⟩ := clear_exec he (μ := μ) c₁ hw₁
    hR₁ (fun v hv => by rw [hm₁, hμ]) a22 a23 a24 a25
  have e₃ := Exec.copyN (P := inp d) hw₂ 22 0
  have hR₃ : Regs d { c₂ with nreg := upd c₂.nreg 22 (c₂.nreg 0) } :=
    regs_of hR₂ fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]
  have hIB : IBo d W μ (size d μ) { c₂ with nreg := upd c₂.nreg 22 (c₂.nreg 0) } := by
    refine ⟨e₃.wb_right, hR₃, by config_simp; rw [ho₂, ho₁, hI.out], ?_, ?_,
      ⟨_, by config_simp; exact hbs₂, fun _ k hk => by config_simp at hk; rw [hR₂.1] at hk; omega⟩,
      by config_simp; rw [hR₂.1]; omega, fun h => by config_simp at h; exact absurd h25₂ h⟩
    · config_simp; rw [h20₂, hK₁ 20 (by omega) (by omega) (by omega) (by omega), hs20]
    · config_simp; rw [h21₂, hK₁ 21 (by omega) (by omega) (by omega) (by omega), h21]
  -- the search
  obtain ⟨c₄, k₄, e₄, hI₄, h22₄, hk₄⟩ := search_exec he hvalid _ hIB (by config_simp; exact hR₂.1)
  obtain ⟨D, hbs₄, hD₄⟩ := hI₄.bs
  obtain ⟨f0, f1, f2, f4, f5, f6, f8, f9, f10⟩ := hI₄.regs
  have hc₄ := hI₄.wb
  have hmate₄ := hbs₄.mate
  -- the end of the phase
  by_cases hfound : c₄.nreg 25 = 0
  · -- no free black vertex: the matching is maximum
    have hmax : ∀ M, IsMatching d M → M.card ≤ size d μ := fun M hM =>
      (hfound ▸ hbs₄).maximal he.toWf hvalid (fun k hk => hD₄ hfound k (by omega)) hM
    have e₅ : Exec (inp d) W finish c₄ _ (1 + 2) :=
      Exec.ifLtN_false (by rw [f0, hfound]; omega) (Exec.copyN hc₄ 21 0)
    refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ⟨e₅.wb_right,
      regs_of ⟨f0, f1, f2, f4, f5, f6, f8, f9, f10⟩ fun r hr => by
        config_simp; rw [upd_other _ _ _ (by omega)],
      by config_simp; exact hI₄.out, valid_congr hmate₄ hvalid,
      by config_simp; rw [hI₄.r20, size_congr hmate₄],
      Or.inr ⟨by config_simp; exact f0, fun M hM => by rw [size_congr hmate₄]; exact hmax M hM⟩⟩, ?_⟩
    unfold potP
    simp only [h21, show (1 : ℕ) ≠ 0 by omega, ite_false]
    config_simp; rw [f0]; simp only [ite_true]
    rw [hs20]
    have : pcost d ≤ (nn d + 1 - size d μ) * pcost d := Nat.le_mul_of_pos_left _ (by omega)
    unfold pcost at *
    omega
  · -- augmentation
    obtain ⟨hbn, hcb, hvb, hμb⟩ := hbs₄.fnd hfound
    have e₅ := Exec.copyN (P := inp d) hc₄ 39 25
    have hIA : IA d W μ (size d μ) D c₄.nmem (c₄.nreg 23) (c₄.nreg 24) (c₄.nreg 25)
        { c₄ with nreg := upd c₄.nreg 39 (c₄.nreg 25) } := by
      refine ⟨e₅.wb_right, regs_of ⟨f0, f1, f2, f4, f5, f6, f8, f9, f10⟩ fun r hr => by
          config_simp; rw [upd_other _ _ _ (by omega)], by config_simp; exact hI₄.out,
        by config_simp; exact hI₄.r20, by config_simp; exact hI₄.r21, fun a _ => rfl,
        fun h => by config_simp at h; omega, fun _ => ?_⟩
      config_simp
      refine ⟨hbn, hcb, hvb, validExc_of_valid (valid_congr hmate₄ hvalid) hbn
        (by rw [hmate₄ _ hbn]; exact hμb), size_congr hmate₄, fun v hv _ _ => hmate₄ v hv⟩
    obtain ⟨c₆, k₆, e₆, hI₆, hn₆, hk₆⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 0)
      (b := 39) (body := augBody) (IA d W μ (size d μ) D c₄.nmem (c₄.nreg 23) (c₄.nreg 24)
        (c₄.nreg 25)) (potA c₄.nmem d) (fun c h => h.wb)
      (fun c hc hlt => augBody_exec he hbs₄ c hc hlt) hIA
    have g0 := hI₆.regs.1
    have h39 : c₆.nreg 39 = 0 := by rw [g0] at hn₆; omega
    obtain ⟨hval₆, hsz₆⟩ := hI₆.done h39
    have e₇ := Exec.addN (P := inp d) hI₆.wb 20 20 1 (by
      rw [hI₆.r20, hI₆.regs.2.1]; have := he.size; omega)
    have e₈ : Exec (inp d) W finish c₄ _ (1 + (k₆ + 1) + 1) :=
      Exec.ifLtN_true (by rw [f0]; omega) (.seq e₅ (.seq e₆ e₇))
    refine ⟨_, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₈))), ⟨e₇.wb_right,
      regs_of hI₆.regs fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)],
      by config_simp; exact hI₆.out, by config_simp; exact hval₆,
      by config_simp; rw [hI₆.r20, hI₆.regs.2.1, hsz₆], Or.inl (by config_simp; exact hI₆.r21)⟩, ?_⟩
    -- the cost
    unfold potP
    simp only [h21, show (1 : ℕ) ≠ 0 by omega, ite_false]
    config_simp
    rw [hI₆.r21]
    simp only [show (1 : ℕ) ≠ 0 by omega, ite_false]
    rw [hI₆.r20, hI₆.regs.2.1, hs20]
    have hsz' : size d μ + 1 ≤ nn d := by rw [← hsz₆]; exact size_le _
    have htb : tmv d c₄.nmem (c₄.nreg 25 - 1) < nn d := by
      have := hbs₄.tmlt _ hbn hvb; have := hbs₄.tcnt; have := nvis_le (d := d) c₄.nmem; omega
    have hpA : potA c₄.nmem d { c₄ with nreg := upd c₄.nreg 39 (c₄.nreg 25) } ≤ 11 * nn d := by
      unfold potA; config_simp; simp only [hfound, ite_false]; omega
    beta_reduce at hk₆
    have hpc : (nn d + 1 - size d μ) * pcost d =
        (nn d + 1 - (size d μ + 1)) * pcost d + pcost d := by
      rw [← Nat.succ_mul]; congr 1; omega
    rw [hpc]
    unfold pcost at *
    omega

/-! ### The main theorem -/

theorem matching_exec (he : Enc d W) :
    ∃ c' k, Exec (inp d) W prog initConfig c' k ∧ c'.output = [size d c'.nmem] ∧
      Valid d c'.nmem ∧ (∀ M, IsMatching d M → M.card ≤ size d c'.nmem) ∧
      k + 1 ≤ 80 * (nn d + 1) * (nn d + mm d + 1) := by
  have hs := he.size
  have hw : WordsBounded W initConfig := ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩
  obtain ⟨c₁, k₁, e₁, hw₁, hpost⟩ : ∃ c₁ k₁, Exec (inp d) W setup initConfig c₁ k₁ ∧
      WordsBounded W c₁ ∧ (Regs d c₁ ∧ c₁.nreg 20 = 0 ∧ c₁.nreg 21 = 1 ∧
        c₁.nmem = (fun _ => 0) ∧ c₁.output = [] ∧ k₁ = 12) := by
    unfold setup
    exec_block
    any_goals first | omega | exact he.word_le _ |
      (config_simp; simp only [initConfig, inp, nn, word] at hs ⊢; omega)
    refine ⟨‹_›, ?_, by config_simp <;> rfl, by config_simp <;> rfl, by config_simp <;> rfl,
      by config_simp <;> rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp <;>
      simp [initConfig, inp, nn, word] <;> omega
  obtain ⟨hR₁, h20, h21, hm₁, ho₁, rfl⟩ := hpost
  have hval0 : Valid d c₁.nmem := fun x _ h => by rw [hm₁] at h; exact absurd rfl h
  have hsz0 : size d c₁.nmem = 0 := by
    unfold size; rw [hm₁]; simp
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := inp d) (W := W) (a := 0)
    (b := 21) (body := phase) (IP d W) (potP d) (fun c h => h.wb)
    (fun c hc hlt => phase_exec he c hc hlt)
    ⟨hw₁, hR₁, ho₁, hval0, by rw [h20, hsz0], Or.inl h21⟩
  have g0 := hI₂.regs.1
  have hmax : ∀ M, IsMatching d M → M.card ≤ size d c₂.nmem := by
    rcases hI₂.r21 with h | ⟨-, h⟩
    · rw [g0, h] at hn₂; omega
    · exact h
  have e₃ := Exec.outN (P := inp d) hI₂.wb 20
  refine ⟨_, _, .seq e₁ (.seq e₂ e₃), by config_simp; rw [hI₂.out, hI₂.r20]; rfl,
    by config_simp; exact hI₂.valid, by config_simp; exact hmax, ?_⟩
  beta_reduce at hk₂
  unfold potP at hk₂
  rw [h21] at hk₂
  simp only [show (1 : ℕ) ≠ 0 by omega, ite_false, h20, Nat.sub_zero] at hk₂
  unfold pcost at hk₂
  have : (nn d + 1) * (80 * nn d + 30 * mm d + 20) + 16 ≤ 80 * (nn d + 1) * (nn d + mm d + 1) := by
    nlinarith
  omega

/-- **Maximum bipartite matching on the machine.** -/
theorem matching_runsWithin (he : Enc d W) :
    ∃ k, (∃ M, IsMatching d M ∧ M.card = k) ∧ (∀ M, IsMatching d M → M.card ≤ k) ∧
      RunsWithin (compile prog 0 ++ [Instr.halt]) (inp d) W
        (80 * (nn d + 1) * (nn d + mm d + 1)) [k] := by
  obtain ⟨c', k, e, hout, hval, hmax, hk⟩ := matching_exec he
  obtain ⟨k', hk', h1, h2⟩ := runsWithin_of_exec_output e hout
  exact ⟨size d c'.nmem, ⟨toM d c'.nmem, toM_isMatching he.toWf hval, card_toM⟩, hmax,
    k', by omega, h1, h2⟩

/-- **Sparse graphs, such as plane bipartite graphs.** A simple plane bipartite graph on `n ≥ 3`
vertices has at most `2n - 4` edges; with `m ≤ 2n` arcs the maximum matching is found within
`80 (n + 1)(3n + 1)` steps. -/
theorem matching_runsWithin_sparse (he : Enc d W) (hm : mm d ≤ 2 * nn d) :
    ∃ k, (∃ M, IsMatching d M ∧ M.card = k) ∧ (∀ M, IsMatching d M → M.card ≤ k) ∧
      RunsWithin (compile prog 0 ++ [Instr.halt]) (inp d) W
        (80 * (nn d + 1) * (3 * nn d + 1)) [k] := by
  obtain ⟨k, h1, h2, h3⟩ := matching_runsWithin he
  refine ⟨k, h1, h2, RunsWithin.mono_steps h3 ?_⟩
  exact Nat.mul_le_mul_left _ (by omega)

end BM

end PlanarFlow
