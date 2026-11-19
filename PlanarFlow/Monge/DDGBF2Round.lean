module

public import PlanarFlow.Monge.DDGBF

/-!
# The levels of a Bellman–Ford round over a dense distance graph, against any reference

The one-matrix program `PlanarFlow.Monge.bfDDG` states its round invariant `RoundOK` with the
Bellman–Ford values `bfv b D` of the single dense distance graph `ddg b D`. To run rounds of
relaxations by *several* Monge matrices on the same values (Bellman–Ford over a union of dense
distance graphs, `PlanarFlow.Monge.bfDDG2_exec`), the invariant has to refer to the Bellman–Ford
values of the union instead. Here the invariant is stated for an arbitrary reference:

* `RoundG b D Q lo hi C E₀ E flag`: the state of a round of relaxations by the Monge matrix `D`
  after the arcs `C` have been processed, from the values `E₀` to the values `E`. Under the
  hypothesis `Q` (in the application: the union has a feasible potential), `lo` is a feasible
  potential of `D` below the values, `E₀ ≤ hi`, and the processed arcs satisfy their inequality
  against `hi` (in the application `lo = bf b` and `hi = bf k` of the union digraph). The
  statements `RoundG.start`, `RoundG.mono`, `RoundG.update` are those of `RoundOK`;
  `RoundOK.toG` shows that `RoundOK` is the instance `Q = HasPot b D`, `lo = bfv b D b`,
  `hi = bfv b D k`.
* `Frm b eb pb c c'`: the frame of the level loop of a round (the registers below `60` outside
  `20 … 30`, the real registers below `60` other than `20, 21`, the memory outside the row-minima
  scratch cells and the values at `eb … eb + b - 1`, the output).
* `updBody2_exec`, `half2_exec`, `blockBody2_exec`, `levelBF2_exec`: the specifications of the
  programs `updBody`, `half`, `blockBody`, `levelBF` of `PlanarFlow/Monge/DDGBF.lean` (the same
  programs) with the invariant `RoundG` and the frame `Frm`; their proofs follow those of
  `updBody_exec`, `half_exec`, `blockBody_exec`, `levelBF_exec`.
* `levels2_exec`: **the levels of one round** (`whileLtN 20 1 levelBF`, started with `r20 = 1`
  and the flag `r30 = 0`) relax every arc `i → j` (`i ≠ j`) of `D` in place, within
  `(levelCost b + 2) (log₂ b + 1) + 2` steps; at the end `RoundG` holds for all the arcs.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The invariant against a reference -/

/-- The state of a round of relaxations by `D` after the arcs `C` have been processed, from the
values `E₀` of the start of the round to the current values `E`, with `flag` recording whether
some value has decreased. Under `Q`, `lo` is a feasible potential of `D` below the values, the
start values are below `hi`, and the processed arcs satisfy their inequality against `hi`. -/
structure RoundG (b : ℕ) (D : ℕ → ℕ → ℤ) (Q : Prop) (lo hi : ℕ → ℤ) (C : ℕ → ℕ → Prop)
    (E₀ E : ℕ → ℤ) (flag : ℕ) : Prop where
  pot : Q → ∀ i j, i < b → j < b → i ≠ j → lo j ≤ lo i + D i j
  le : ∀ v < b, E v ≤ E₀ v
  chg : (flag = 0 ∧ ∀ v < b, E v = E₀ v) ∨ (flag = 1 ∧ ∃ v < b, E v < E₀ v)
  feas : flag = 0 → ∀ i j, i < b → j < b → i ≠ j → C i j → E j ≤ E i + D i j
  bf : Q → (∀ v < b, lo v ≤ E v ∧ E₀ v ≤ hi v) ∧
    ∀ i j, i < b → j < b → i ≠ j → C i j → E j ≤ hi i + D i j

variable {b : ℕ} {D : ℕ → ℕ → ℤ} {Q : Prop} {lo hi : ℕ → ℤ}

/-- `RoundOK` is the instance of `RoundG` with the reference values of `ddg b D`. -/
theorem RoundOK.toG {k : ℕ} {C : ℕ → ℕ → Prop} {E₀ E : ℕ → ℤ} {flag : ℕ}
    (h : RoundOK b D k C E₀ E flag) :
    RoundG b D (HasPot b D) (bfv b D b) (bfv b D k) C E₀ E flag :=
  ⟨fun hP _ _ hi hj hij => bfv_isPot hP hi hj hij, h.le, h.chg, h.feas, h.bf⟩

/-- The start of a round. -/
theorem RoundG.start {E : ℕ → ℤ}
    (hpot : Q → ∀ i j, i < b → j < b → i ≠ j → lo j ≤ lo i + D i j)
    (h : Q → ∀ v < b, lo v ≤ E v ∧ E v ≤ hi v) :
    RoundG b D Q lo hi (fun _ _ => False) E E 0 :=
  ⟨hpot, fun _ _ => le_rfl, Or.inl ⟨rfl, fun _ _ => rfl⟩, fun _ _ _ _ _ _ h => h.elim,
    fun hQ => ⟨h hQ, fun _ _ _ _ _ h => h.elim⟩⟩

/-- Fewer processed arcs. -/
theorem RoundG.mono {C C' : ℕ → ℕ → Prop} {E₀ E : ℕ → ℤ} {flag : ℕ}
    (h : RoundG b D Q lo hi C E₀ E flag)
    (hC : ∀ i j, i < b → j < b → i ≠ j → C' i j → C i j) : RoundG b D Q lo hi C' E₀ E flag :=
  ⟨h.pot, h.le, h.chg, fun hf i j hi hj hij hc => h.feas hf i j hi hj hij (hC i j hi hj hij hc),
    fun hP => ⟨(h.bf hP).1,
      fun i j hi hj hij hc => (h.bf hP).2 i j hi hj hij (hC i j hi hj hij hc)⟩⟩

/-- **One target lowered to the minimum over a set of sources.** -/
theorem RoundG.update {C : ℕ → ℕ → Prop} {E₀ E : ℕ → ℤ} {flag : ℕ}
    (h : RoundG b D Q lo hi C E₀ E flag)
    {S : ℕ → Prop} {t : ℕ} (ht : t < b) (hS : ∀ i, S i → i < b ∧ i ≠ t) {V : ℤ}
    (hV1 : ∀ i, S i → V ≤ E i + D i t) (hV2 : ∃ i, S i ∧ V = E i + D i t) :
    RoundG b D Q lo hi (fun i j => C i j ∨ (S i ∧ j = t)) E₀
      (fun v => if v = t ∧ V < E t then V else E v) (if V < E t then 1 else flag) := by
  obtain ⟨hpot, hle, hfl, hfe, hbf⟩ := h
  by_cases hV : V < E t
  · simp only [hV, and_true, ite_true]
    refine ⟨hpot, fun v hv => ?_, Or.inr ⟨rfl, t, ht, ?_⟩, fun h => absurd h one_ne_zero,
      fun hP => ?_⟩
    · split_ifs with e
      · subst e; exact hV.le.trans (hle v hv)
      · exact hle v hv
    · simp only [ite_true]; exact lt_of_lt_of_le hV (hle t ht)
    · obtain ⟨h1, h2⟩ := hbf hP
      obtain ⟨i₀, hi₀, hVi₀⟩ := hV2
      refine ⟨fun v hv => ⟨?_, (h1 v hv).2⟩, fun i j hi hj hij hc => ?_⟩
      · split_ifs with e
        · subst e
          have := hpot hP i₀ v (hS i₀ hi₀).1 hv (hS i₀ hi₀).2
          have := (h1 i₀ (hS i₀ hi₀).1).1
          omega
        · exact (h1 v hv).1
      · split_ifs with e
        · subst e
          rcases hc with hc | ⟨hc, -⟩
          · have := h2 i j hi hj hij hc; omega
          · have := hV1 i hc
            have := hle i hi
            have := (h1 i hi).2
            omega
        · rcases hc with hc | ⟨-, hc⟩
          · exact h2 i j hi hj hij hc
          · exact absurd hc e
  · simp only [hV, and_false, ite_false]
    refine ⟨hpot, hle, hfl, fun hf i j hi hj hij hc => ?_,
      fun hP => ⟨(hbf hP).1, fun i j hi hj hij hc => ?_⟩⟩
    · rcases hc with hc | ⟨hc, rfl⟩
      · exact hfe hf i j hi hj hij hc
      · have := hV1 i hc; omega
    · rcases hc with hc | ⟨hc, rfl⟩
      · exact (hbf hP).2 i j hi hj hij hc
      · have := hV1 i hc
        have := hle i hi
        have := ((hbf hP).1 i hi).2
        omega

/-- The flag of a round is `0` or `1`. -/
theorem RoundG.flag_le {C : ℕ → ℕ → Prop} {E₀ E : ℕ → ℤ} {flag : ℕ}
    (h : RoundG b D Q lo hi C E₀ E flag) : flag ≤ 1 := by
  rcases h.chg with ⟨h, -⟩ | ⟨h, -⟩ <;> omega

/-! ### The frame of the levels -/

/-- The frame of the level loop of a round with the values at `eb` and the row-minima scratch
cells above `pb`. -/
structure Frm (b eb pb : ℕ) (c c' : Config) : Prop where
  nreg : ∀ r < 60, (r < 20 ∨ 30 < r) → c'.nreg r = c.nreg r
  rreg : ∀ r < 60, r ≠ 20 → r ≠ 21 → c'.rreg r = c.rreg r
  nmem : ∀ a, pb + 5 * b + 1 < a → c'.nmem a = c.nmem a
  rmem : ∀ a, (pb + 5 * b + 1 < a ∧ a < eb) ∨ eb + b ≤ a → c'.rmem a = c.rmem a
  out : c'.output = c.output

/-- The empty frame. -/
theorem Frm.refl (b eb pb : ℕ) (c : Config) : Frm b eb pb c c :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

/-- Frames compose. -/
theorem Frm.trans {eb pb : ℕ} {c c' c'' : Config} (h : Frm b eb pb c c') (h' : Frm b eb pb c' c'') :
    Frm b eb pb c c'' :=
  ⟨fun r hr h1 => (h'.nreg r hr h1).trans (h.nreg r hr h1),
    fun r hr h1 h2 => (h'.rreg r hr h1 h2).trans (h.rreg r hr h1 h2),
    fun a ha => (h'.nmem a ha).trans (h.nmem a ha), fun a ha => (h'.rmem a ha).trans (h.rmem a ha),
    h'.out.trans h.out⟩

/-- A step changing only the registers `20 … 30` (and those from `60` on). -/
theorem Frm.of_regs {eb pb : ℕ} {c c' : Config}
    (hn : ∀ r < 60, (r < 20 ∨ 30 < r) → c'.nreg r = c.nreg r) (hr : c'.rreg = c.rreg)
    (hnm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem) (ho : c'.output = c.output) :
    Frm b eb pb c c' :=
  ⟨hn, fun r _ _ _ => by rw [hr], fun a _ => by rw [hnm], fun a _ => by rw [hrm], ho⟩

/-! ### The update of a half block -/

variable {P : Input} {W : ℕ} {Db eb pb : ℕ}

/-- The state of the update of a half block, started from `c₁` with the values `E₁`
(`IUp` with the invariant `RoundG`). -/
structure IUp2 (b eb : ℕ) (D : ℕ → ℕ → ℤ) (W : ℕ) (Q : Prop) (lo hi : ℕ → ℤ)
    (C : ℕ → ℕ → Prop) (E₀ E₁ : ℕ → ℤ) (r0 nr c1 nc : ℕ) (c₁ c : Config) : Prop where
  wb : WordsBounded W c
  nreg : ∀ r, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c.nreg r = c₁.nreg r
  rreg : ∀ r, r ≠ 20 → r ≠ 21 → c.rreg r = c₁.rreg r
  nmem : c.nmem = c₁.nmem
  rmem : ∀ a, (a < eb + r0 ∨ eb + r0 + nr ≤ a) → c.rmem a = c₁.rmem a
  out : c.output = c₁.output
  ρ : c.nreg 26 ≤ nr
  vals : ∃ E, Vals b eb E c ∧
    RoundG b D Q lo hi (fun i j => C i j ∨ HalfArcs r0 c1 nc (c.nreg 26) i j) E₀ E (c.nreg 30) ∧
    ∀ v < b, (v < r0 ∨ r0 + c.nreg 26 ≤ v) → E v = E₁ v

/-- One step of the update of a half block (`updBody_exec` with the invariant `RoundG`). -/
theorem updBody2_exec (hL : Lay b Db eb pb W) {C : ℕ → ℕ → Prop} {E₀ E₁ : ℕ → ℤ}
    {r0 nr c1 nc : ℕ} {c₁ : Config} (hE₁ : Env b Db eb pb D c₁) (h24 : c₁.nreg 24 = r0)
    (h60 : c₁.nreg 60 = nr) (hnc : 1 ≤ nc) (hnc' : nc ≤ c1) (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b)
    (hsep : r0 + nr ≤ c1 - nc ∨ c1 ≤ r0)
    (hrow : ∀ ρ < nr, c₁.rmem (pb + ρ + 1) = Vrow D E₁ r0 c1 nc ρ)
    (c : Config) (hI : IUp2 b eb D W Q lo hi C E₀ E₁ r0 nr c1 nc c₁ c)
    (hlt : c.nreg 26 < c.nreg 60) :
    ∃ c' k', Exec P W updBody c c' k' ∧ IUp2 b eb D W Q lo hi C E₀ E₁ r0 nr c1 nc c₁ c' ∧
      12 * (nr - c'.nreg 26) + k' + 2 ≤ 12 * (nr - c.nreg 26) := by
  have hc := hI.wb
  have hLw := hL.w
  have hpe := hL.pe
  have hed := hL.ed
  have g : ∀ r, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c.nreg r = c₁.nreg r := hI.nreg
  have g3 : c.nreg 3 = eb :=
    (g 3 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r3
  have g4 : c.nreg 4 = pb :=
    (g 4 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r4
  have g10 : c.nreg 10 = 1 :=
    (g 10 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r10
  have g24 : c.nreg 24 = r0 :=
    (g 24 (by omega) (by omega) (by omega) (by omega) (by omega)).trans h24
  rw [g 60 (by omega) (by omega) (by omega) (by omega) (by omega), h60] at hlt
  generalize hρ : c.nreg 26 = ρ at hlt
  have hρI := hI.ρ
  rw [hρ] at hρI
  obtain ⟨E, hV, hR, hE⟩ := hI.vals
  rw [hρ] at hR hE
  have hrowc : c.rmem (pb + ρ + 1) = Vrow D E₁ r0 c1 nc ρ := by
    rw [hI.rmem _ (Or.inl (by omega))]; exact hrow ρ hlt
  have htc : c.rmem (eb + (r0 + ρ)) = E (r0 + ρ) := hV _ (by omega)
  have hsrc : ∀ i, c1 - nc ≤ i → i < c1 → E i = E₁ i := fun i h1 h2 => hE i (by omega) (by omega)
  have hS : ∀ i, (c1 - nc ≤ i ∧ i < c1) → i < b ∧ i ≠ r0 + ρ := fun i hi => ⟨by omega, by omega⟩
  have hn0 : 0 < nc := hnc
  have hV1 : ∀ i, (c1 - nc ≤ i ∧ i < c1) → Vrow D E₁ r0 c1 nc ρ ≤ E i + D i (r0 + ρ) := by
    intro i hi
    have hle := lmin_le (blkR D E₁ r0 c1) ρ (j := c1 - 1 - i) (n := nc) (by omega)
    simp only [blkR] at hle
    have hle' := Int.cast_le.1 hle
    simp only [Vrow]
    rw [hsrc i hi.1 hi.2]
    simp only [blk] at hle' ⊢
    rw [show c1 - 1 - (c1 - 1 - i) = i by omega] at hle'
    exact hle'
  have hV2 : ∃ i, (c1 - nc ≤ i ∧ i < c1) ∧ Vrow D E₁ r0 c1 nc ρ = E i + D i (r0 + ρ) := by
    have hl := lmin_lt (blkR D E₁ r0 c1) ρ hn0
    refine ⟨c1 - 1 - lmin nc (blkR D E₁ r0 c1) ρ, ⟨by omega, by omega⟩, ?_⟩
    rw [hsrc _ (by omega) (by omega)]; rfl
  have hU := hR.update (S := fun i => c1 - nc ≤ i ∧ i < c1) (t := r0 + ρ) (by omega) hS hV1 hV2
  have hfin : ∀ c' : Config, WordsBounded W c' →
      (∀ r, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c'.nreg r = c.nreg r) →
      (∀ r, r ≠ 20 → r ≠ 21 → c'.rreg r = c.rreg r) → c'.nmem = c.nmem →
      c'.output = c.output → c'.nreg 26 = ρ + 1 →
      c'.nreg 30 = (if Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ) then 1 else c.nreg 30) →
      (∀ a, c'.rmem a = if a = eb + (r0 + ρ) ∧ Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ) then
        ((Vrow D E₁ r0 c1 nc ρ : ℤ) : ℝ) else c.rmem a) →
      IUp2 b eb D W Q lo hi C E₀ E₁ r0 nr c1 nc c₁ c' := by
    intro c' hw hn' hr' hnm ho h26 h30 hrm
    refine ⟨hw, fun r a1 a2 a3 a4 a5 => (hn' r a1 a2 a3 a4 a5).trans (g r a1 a2 a3 a4 a5),
      fun r a1 a2 => (hr' r a1 a2).trans (hI.rreg r a1 a2), hnm.trans hI.nmem, fun a ha => ?_,
      ho.trans hI.out, by omega, ?_⟩
    · rw [hrm a]; split_ifs with h
      · omega
      · exact hI.rmem a ha
    · refine ⟨fun v => if v = r0 + ρ ∧ Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ) then
        Vrow D E₁ r0 c1 nc ρ else E v, fun v hv => ?_, ?_, fun v hv hv' => ?_⟩
      · rw [hrm]
        by_cases h : v = r0 + ρ ∧ Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ)
        · have h' : eb + v = eb + (r0 + ρ) ∧ Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ) :=
            ⟨by rw [h.1], h.2⟩
          rw [ite_eq_left h']; beta_reduce; rw [ite_eq_left h]
        · have h' : ¬ (eb + v = eb + (r0 + ρ) ∧ Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ)) :=
            fun h'' => h ⟨by omega, h''.2⟩
          rw [ite_eq_right h']; beta_reduce; rw [ite_eq_right h]; exact hV v hv
      · rw [h30, h26]
        refine hU.mono fun i j hi hj hij hc => ?_
        rcases hc with hc | ⟨h1, h2, h3, h4⟩
        · exact Or.inl (Or.inl hc)
        · by_cases hj' : j = r0 + ρ
          · exact Or.inr ⟨⟨h1, h2⟩, hj'⟩
          · exact Or.inl (Or.inr ⟨h1, h2, h3, by omega⟩)
      · rw [h26] at hv'
        simp only
        split_ifs with h
        · omega
        · exact hE v hv (by omega)
  unfold updBody
  refine spec_seq ?_
  exec_block
  · rw [g24, hρ]; omega
  · config_simp; rw [g3, g24, hρ]; omega
  · config_simp; rw [g4, hρ]; omega
  · config_simp; rw [g4, hρ, g10]; omega
  have hcfg : ∀ x : ℝ, (x < c.rmem (c.nreg 3 + (c.nreg 24 + c.nreg 26)) ↔
      x < (E (r0 + ρ) : ℝ)) ∧ c.rmem (c.nreg 4 + c.nreg 26 + c.nreg 10) =
        (Vrow D E₁ r0 c1 nc ρ : ℝ) := fun x => by
    rw [g4, hρ, g10, g3, g24, hrowc, htc]; exact ⟨Iff.rfl, rfl⟩
  refine spec_seq ?_
  by_cases hcmp : Vrow D E₁ r0 c1 nc ρ < E (r0 + ρ)
  · refine spec_ifLtR_true (by
      config_simp; rw [(hcfg 0).2, (hcfg _).1]; exact_mod_cast hcmp) ?_
    exec_block
    · omega
    refine spec_instr (Exec.addN ‹_› _ _ _ ?_) fun hw => ?_
    · config_simp; rw [hρ, g10]; omega
    refine ⟨hfin _ hw (fun r a1 a2 a3 a4 a5 => ?_) (fun r a1 a2 => ?_) rfl rfl ?_ ?_ ?_, ?_⟩
    · config_simp; upd_tac
    · config_simp; upd_tac
    · config_simp; rw [hρ, g10]
    · config_simp; simp only [hcmp, ite_true]
    · intro a; config_simp; rw [upd_apply, (hcfg 0).2, g3, g24, hρ]
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd ⟨h1, hcmp⟩ h2
      · exact absurd h2.1 h1
      · rfl
    · config_simp; rw [hρ, g10]
      omega
  · refine spec_ifLtR_false (by
      config_simp; rw [(hcfg 0).2, (hcfg _).1]; exact_mod_cast hcmp) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ ?_) fun hw => ?_
    · config_simp; rw [hρ, g10]; omega
    refine ⟨hfin _ hw (fun r a1 a2 a3 a4 a5 => ?_) (fun r a1 a2 => ?_) rfl rfl ?_ ?_ ?_, ?_⟩
    · config_simp; upd_tac
    · config_simp; upd_tac
    · config_simp; rw [hρ, g10]
    · config_simp; simp only [hcmp, ite_false]
    · intro a; config_simp
      split_ifs with h1
      · exact absurd h1.2 hcmp
      · rfl
    · config_simp; rw [hρ, g10]
      omega

/-! ### A half block -/

/-- **A half block** (`half_exec` with the invariant `RoundG` and the memory frame). -/
theorem half2_exec (hD : Crossing b D) (hL : Lay b Db eb pb W) {C : ℕ → ℕ → Prop}
    {E₀ E : ℕ → ℤ} {r0 nr c1 nc : ℕ} (c : Config) (hc : WordsBounded W c)
    (hE : Env b Db eb pb D c) (hV : Vals b eb E c)
    (hR : RoundG b D Q lo hi C E₀ E (c.nreg 30))
    (h24 : c.nreg 24 = r0) (h25 : c.nreg 25 = c1) (h60 : c.nreg 60 = nr) (h61 : c.nreg 61 = nc)
    (hnr : 1 ≤ nr) (hnc : 1 ≤ nc) (hnc' : nc ≤ c1) (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b)
    (hsep : r0 + nr ≤ c1 - nc ∨ c1 ≤ r0) :
    ∃ c' k', Exec P W half c c' k' ∧ k' ≤ 532 * (nr + nc + 1) ∧
      (Env b Db eb pb D c' ∧
        (∃ E', Vals b eb E' c' ∧
          RoundG b D Q lo hi (fun i j => C i j ∨ HalfArcs r0 c1 nc nr i j) E₀ E' (c'.nreg 30)) ∧
        (∀ r < 60, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c'.nreg r = c.nreg r) ∧
        (∀ r < 60, r ≠ 20 → r ≠ 21 → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
        (∀ a, pb + 5 * b + 1 < a → c'.nmem a = c.nmem a) ∧
        (∀ a, (pb + 5 * b + 1 < a ∧ a < eb) ∨ eb + b ≤ a → c'.rmem a = c.rmem a)) := by
  have hLw := hL.w
  have hpe := hL.pe
  have hed := hL.ed
  unfold half
  refine spec_seq ?_
  refine spec_instr (Exec.copyN hc 62 4) fun hw₁ => ?_
  refine spec_seq ?_
  have hEa : Env b Db eb pb D { c with nreg := upd c.nreg 62 (c.nreg 4) } :=
    hE.of (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]) rfl (fun _ _ => rfl)
  have hTM : IsTotMono nr nc (blkR D E r0 c1) :=
    (isMonge_blk hD E hnc' hc1 hr hsep).cast.totMono
  refine spec_use (smawk_exec (entBF_exec (P := P) hL hEa hV (by config_simp; exact h24)
    (by config_simp; exact h25) hnc' hc1 hr) hTM (by omega) (by omega) (by omega) hw₁
    (by config_simp; exact h60) (by config_simp; exact h61)
    (by config_simp; exact hE.r4)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨⟨a1, a2, a3, a4, a5⟩, g60, g61, g62, hres⟩
  refine spec_seq ?_
  refine spec_instr (Exec.constN hw₂ 26 0 (by omega)) fun hw₃ => ?_
  have n₁ : ∀ r < 60, r ≠ 26 →
      ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config).nreg r = c.nreg r :=
    fun r hr h => by
      config_simp; rw [upd_other _ _ _ h, a1 r hr]; config_simp; rw [upd_other _ _ _ (by omega)]
  have hE₁ : Env b Db eb pb D ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config) :=
    hE.of (fun r hr => n₁ r (by omega) (by omega)) (a2 10 (by omega))
      (fun a ha => a4 a (Or.inr (by omega)))
  have hV₁ : Vals b eb E ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config) :=
    fun v hv => (a4 _ (Or.inr (by omega))).trans (hV v hv)
  refine spec_while (IUp2 b eb D W Q lo hi C E₀ E r0 nr c1 nc { c₂ with nreg := upd c₂.nreg 26 0 })
    (fun c => 12 * (nr - c.nreg 26)) (fun c h => h.wb)
    (fun c' hc' hlt' => updBody2_exec hL hE₁ (by rw [n₁ 24 (by omega) (by omega), h24])
      (by config_simp; rw [g60]) hnc hnc' hc1 hr hsep (fun ρ hρ => by
        config_simp; rw [show pb + ρ + 1 = pb + ρ + 1 from rfl, (hres ρ hρ).2]; rfl) c' hc' hlt')
    ⟨hw₃, fun _ _ _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, fun _ _ => rfl, rfl,
      by config_simp; omega, E, hV₁, ?_, fun _ _ _ => rfl⟩ ?_
  · rw [n₁ 30 (by omega) (by omega)]
    refine hR.mono fun i j _ _ _ hc => ?_
    rcases hc with hc | ⟨-, -, h3, h4⟩
    · exact hc
    · config_simp at h4; omega
  intro c₃ k₃ hI hn hk₃
  have h26 : c₃.nreg 26 = nr := by
    have := hI.ρ
    rw [hI.nreg 60 (by omega) (by omega) (by omega) (by omega) (by omega)] at hn
    config_simp at hn; rw [g60] at hn; omega
  obtain ⟨E', hV', hR', -⟩ := hI.vals
  rw [h26] at hR'
  have hK : 4 * nr + nc + 1 ≤ 5 * b + 1 := by omega
  refine ⟨?_, hE₁.of (fun r hr => hI.nreg r (by omega) (by omega) (by omega) (by omega)
      (by omega)) (hI.rreg 10 (by omega) (by omega)) (fun a ha => hI.rmem a (Or.inr (by omega))),
    ⟨E', hV', hR'⟩, fun r hr a b' d e f => ?_, fun r hr h1 h2 => ?_, ?_, fun a ha => ?_,
    fun a ha => ?_⟩
  · beta_reduce at hk₃
    config_simp at hk₃
    omega
  · rw [hI.nreg r a b' d e f]; exact n₁ r hr a
  · rw [hI.rreg r h1 h2]; config_simp; rw [a2 r hr]
  · rw [hI.out]; config_simp; rw [a5]
  · rw [congrFun hI.nmem a]; config_simp; rw [a3 a (Or.inr (by omega))]
  · rw [hI.rmem a (by omega)]; config_simp; rw [a4 a (Or.inr (by omega))]

/-! ### A block -/

/-- The state between the blocks of the level `s` of a round (`IB` with the invariant `RoundG`
and the frame `Frm` from `c₀`). -/
structure IB2 (b Db eb pb : ℕ) (D : ℕ → ℕ → ℤ) (W : ℕ) (Q : Prop) (lo hi : ℕ → ℤ)
    (E₀ : ℕ → ℤ) (s : ℕ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  env : Env b Db eb pb D c
  frm : Frm b eb pb c₀ c
  r20 : c.nreg 20 = s
  base : ∃ q, c.nreg 21 = 2 * s * q
  r22 : c.nreg 22 = c.nreg 21 + s
  basele : c.nreg 21 ≤ b + s
  vals : ∃ E, Vals b eb E c ∧ RoundG b D Q lo hi (Cov s (c.nreg 21)) E₀ E (c.nreg 30)

/-- A block of the level `s` (`blockBody_exec` with the invariant `RoundG` and the frame). -/
theorem blockBody2_exec (hD : Crossing b D) (hL : Lay b Db eb pb W) {E₀ : ℕ → ℤ} {s : ℕ}
    {c₀ : Config} (hs : 1 ≤ s) (hsb : s < b) (c : Config)
    (hI : IB2 b Db eb pb D W Q lo hi E₀ s c₀ c) (hlt : c.nreg 22 < c.nreg 1) :
    ∃ c' k', Exec P W blockBody c c' k' ∧ IB2 b Db eb pb D W Q lo hi E₀ s c₀ c' ∧
      (blockCost b s + 2) * ((b + s - c'.nreg 21) / (2 * s)) + k' + 2 ≤
        (blockCost b s + 2) * ((b + s - c.nreg 21) / (2 * s)) := by
  have hc := hI.wb
  have hE := hI.env
  have hLw := hL.w
  have hpe := hL.pe
  have hed := hL.ed
  rw [hI.r22, hE.r1] at hlt
  obtain ⟨q, hq⟩ := hI.base
  generalize hbase : c.nreg 21 = base at hq hlt
  obtain ⟨E, hV, hR⟩ := hI.vals
  rw [hbase] at hR
  have g20 := hI.r20
  have g22 : c.nreg 22 = base + s := by rw [hI.r22, hbase]
  unfold blockBody
  refine spec_seq ?_
  refine spec_instr (Exec.addN hc 23 22 20 (by rw [g22, g20]; omega)) fun hw₁ => ?_
  refine spec_seq ?_
  refine spec_use (minS_exec _ hw₁) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨h23, hn₂, hr₂, hnm₂, hrm₂, ho₂⟩
  config_simp at h23
  rw [g22, g20, hE.r1] at h23
  generalize hrend : min (base + s + s) b = rend at h23
  have hrend1 : base + s < rend := by rw [← hrend]; omega
  have hrend2 : rend ≤ b := by rw [← hrend]; omega
  have hrend3 : rend ≤ base + 2 * s := by rw [← hrend]; omega
  have e₂ : ∀ r, r ≠ 23 → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hn₂ r hr]; config_simp; rw [upd_other _ _ _ hr]
  have hE₂ : Env b Db eb pb D c₂ :=
    hE.of (fun r hr => e₂ r (by omega)) (by rw [hr₂]) (fun a _ => by rw [hrm₂])
  -- the first half: from `[base, base + s)` to `[base + s, rend)`
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (half2_exec (P := P) hD hL (C := Cov s base) (r0 := base + s) (c1 := base + s)
    (nr := rend - (base + s)) (nc := s) _ ‹_›
    (hE₂.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl))
    (fun v hv => by config_simp; rw [hrm₂]; exact hV v hv)
    (by config_simp; rw [e₂ 30 (by omega)]; exact hR)
    (by config_simp; rw [e₂ 22 (by omega), g22])
    (by config_simp; rw [e₂ 22 (by omega), g22])
    (by config_simp; rw [h23, e₂ 22 (by omega), g22])
    (by config_simp; rw [e₂ 20 (by omega), g20])
    (by omega) hs (by omega) (by omega) (by omega) (Or.inr le_rfl)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hE₃, ⟨E₃, hV₃, hR₃⟩, hn₃, hr₃, ho₃, hnm₃, hrm₃⟩
  have e₃ : ∀ r < 60, r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
      c₃.nreg r = c.nreg r := fun r hr a1 a2 a3 a4 a5 a6 a7 a8 => by
    rw [hn₃ r hr a4 a5 a6 a7 a8]; config_simp
    simp only [upd_apply]; split_ifs <;> first | omega | exact e₂ r a1
  have g23₃ : c₃.nreg 23 = rend := by
    rw [hn₃ 23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    config_simp; exact h23
  -- the second half: from `[base + s, rend)` to `[base, base + s)`
  refine spec_seq ?_
  exec_block
  refine spec_seq ?_
  refine spec_use (half2_exec (P := P) hD hL (r0 := base) (c1 := rend) (nr := s)
    (nc := rend - (base + s)) _ ‹_›
    (hE₃.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl))
    (fun v hv => by config_simp; exact hV₃ v hv)
    (by config_simp; exact hR₃)
    (by config_simp; rw [e₃ 21 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), hbase])
    (by config_simp; exact g23₃)
    (by config_simp; rw [e₃ 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), g20])
    (by config_simp; rw [g23₃, e₃ 22 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), g22])
    hs (by omega) (by omega) hrend2 (by omega) (Or.inl (by omega))) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨hE₄, ⟨E₄, hV₄, hR₄⟩, hn₄, hr₄, ho₄, hnm₄, hrm₄⟩
  have e₄ : ∀ r < 60, r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
      r ≠ 60 → r ≠ 61 → c₄.nreg r = c.nreg r := fun r hr a1 a2 a3 a4 a5 a6 a7 a8 _ _ => by
    rw [hn₄ r hr a4 a5 a6 a7 a8]; config_simp
    simp only [upd_apply]; split_ifs <;> first | omega | exact e₃ r hr a1 a2 a3 a4 a5 a6 a7 a8
  have g20₄ : c₄.nreg 20 = s := by
    rw [e₄ 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), g20]
  have g21₄ : c₄.nreg 21 = base := by
    rw [e₄ 21 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), hbase]
  -- the frame of the two halves
  have hF₄ : Frm b eb pb c c₄ := by
    refine ⟨fun r hr h => e₄ r hr (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), fun r hr h1 h2 => ?_,
      fun a ha => ?_, fun a ha => ?_, ?_⟩
    · rw [hr₄ r hr h1 h2]; config_simp; rw [hr₃ r hr h1 h2]; config_simp; rw [hr₂]
    · rw [hnm₄ a ha]; config_simp; rw [hnm₃ a ha]; config_simp; rw [hnm₂]
    · rw [hrm₄ a ha]; config_simp; rw [hrm₃ a ha]; config_simp; rw [hrm₂]
    · rw [ho₄]; config_simp; rw [ho₃]; config_simp; rw [ho₂]
  -- the next block
  exec_block
  · rw [g21₄, g20₄]; omega
  · config_simp; rw [g21₄, g20₄]; omega
  · config_simp; rw [g21₄, g20₄]; omega
  refine ⟨⟨‹_›, hE₄.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl),
    hI.frm.trans (hF₄.trans (Frm.of_regs (fun r hr h => ?_) rfl rfl rfl rfl)), ?_,
    ⟨q + 1, ?_⟩, ?_, ?_, ⟨E₄, fun v hv => by config_simp; exact hV₄ v hv, ?_⟩⟩, ?_⟩
  · config_simp; simp only [upd_apply]; split_ifs <;> omega
  · config_simp; exact g20₄
  · config_simp; rw [g21₄, g20₄, hq]; ring
  · config_simp; rw [g20₄]
  · config_simp; rw [g21₄, g20₄]; omega
  · config_simp; rw [g21₄, g20₄]
    refine hR₄.mono fun i j hi hj hij hc => ?_
    rw [show base + s + s = 2 * s * q + 2 * s by rw [hq]; ring] at hc
    rcases cov_step (by omega) hc with hc | hc
    · rw [← hq] at hc; exact Or.inl (Or.inl hc)
    · rw [← hq] at hc
      rcases hc with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
      · exact Or.inl (Or.inr ⟨by omega, by omega, by omega, by omega⟩)
      · exact Or.inr ⟨by omega, by omega, by omega, by omega⟩
  · -- the cost
    config_simp; rw [g21₄, g20₄]
    have hb1 := halfCost_le (b := b) (s := s) (nr := rend - (base + s)) (nc := s) (by omega)
      le_rfl hsb.le (by omega)
    have hb2 := halfCost_le (b := b) (s := s) (nr := s) (nc := rend - (base + s)) le_rfl
      (by omega) hsb.le hs
    have hμ : (b + s - base) / (2 * s) = (b + s - (base + s + s)) / (2 * s) + 1 := by
      rw [show b + s - base = b + s - (base + s + s) + 2 * s by omega,
        Nat.add_div_right _ (by omega)]
    rw [hμ, Nat.mul_add, Nat.mul_one]
    generalize (blockCost b s + 2) * ((b + s - (base + s + s)) / (2 * s)) = Y
    have hB : blockCost b s = 2 * (532 * (2 * s + 1)) + 14 := rfl
    rw [hB]
    generalize hx : rend - (base + s) = x at hb1 hb2 ⊢
    omega

/-! ### A level -/

/-- The state between the levels of a round (`IL` with the invariant `RoundG` and the frame
`Frm` from `c₀`). -/
structure IL2 (b Db eb pb : ℕ) (D : ℕ → ℕ → ℤ) (W : ℕ) (Q : Prop) (lo hi : ℕ → ℤ)
    (E₀ : ℕ → ℤ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  env : Env b Db eb pb D c
  frm : Frm b eb pb c₀ c
  pow : ∃ t, c.nreg 20 = 2 ^ t
  sle : c.nreg 20 ≤ 2 * b + 1
  vals : ∃ E, Vals b eb E c ∧ RoundG b D Q lo hi (Cov (c.nreg 20) 0) E₀ E (c.nreg 30)

/-- A level of a round (`levelBF_exec` with the invariant `RoundG` and the frame). -/
theorem levelBF2_exec (hD : Crossing b D) (hL : Lay b Db eb pb W) {E₀ : ℕ → ℤ}
    {c₀ : Config} (c : Config) (hI : IL2 b Db eb pb D W Q lo hi E₀ c₀ c)
    (hlt : c.nreg 20 < c.nreg 1) :
    ∃ c' k', Exec P W levelBF c c' k' ∧ IL2 b Db eb pb D W Q lo hi E₀ c₀ c' ∧
      (levelCost b + 2) * (Nat.log 2 b + 1 - Nat.log 2 (c'.nreg 20)) + k' + 2 ≤
        (levelCost b + 2) * (Nat.log 2 b + 1 - Nat.log 2 (c.nreg 20)) := by
  have hc := hI.wb
  have hE := hI.env
  have hLw := hL.w
  rw [hE.r1] at hlt
  obtain ⟨t, ht⟩ := hI.pow
  generalize hs : c.nreg 20 = s at ht hlt
  have hs1 : 1 ≤ s := by rw [ht]; exact Nat.one_le_two_pow
  obtain ⟨E, hV, hR⟩ := hI.vals
  rw [hs] at hR
  unfold levelBF
  refine spec_seq ?_
  exec_block
  · omega
  refine spec_seq ?_
  refine spec_while (IB2 b Db eb pb D W Q lo hi E₀ s c₀)
    (fun c => (blockCost b s + 2) * ((b + s - c.nreg 21) / (2 * s))) (fun c h => h.wb)
    (fun c' hc' hlt' => blockBody2_exec hD hL hs1 hlt c' hc' hlt')
    ⟨‹_›, hE.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl),
      hI.frm.trans (Frm.of_regs (fun r hr h => by config_simp; upd_tac) rfl rfl rfl rfl),
      by config_simp; exact hs,
      ⟨0, by config_simp; ring⟩, by config_simp; rw [hs], by config_simp; omega,
      ⟨E, hV, by config_simp; exact hR⟩⟩ ?_
  intro c₂ k₂ hI₂ hn₂ hk₂
  have hw₂ := hI₂.wb
  have g20 := hI₂.r20
  have hend : b ≤ c₂.nreg 21 + s := by
    rw [hI₂.r22, hI₂.env.r1] at hn₂; omega
  refine spec_instr (Exec.addN hw₂ 20 20 20 (by rw [g20]; omega)) fun hw₃ => ?_
  obtain ⟨E₂, hV₂, hR₂⟩ := hI₂.vals
  refine ⟨⟨hw₃, hI₂.env.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl),
    hI₂.frm.trans (Frm.of_regs (fun r hr h => by config_simp; upd_tac) rfl rfl rfl rfl),
    ⟨t + 1, by config_simp; rw [g20, ht, pow_succ]; ring⟩, by config_simp; rw [g20]; omega,
    ⟨E₂, hV₂, ?_⟩⟩, ?_⟩
  · config_simp; rw [g20]
    refine hR₂.mono fun i j hi hj hij hc => ?_
    exact cov_level ht hend hi hj (by rw [show s + s = 2 * s by ring] at hc; exact hc)
  · config_simp; rw [g20]
    beta_reduce at hk₂
    config_simp at hk₂
    rw [Nat.sub_zero] at hk₂
    have hl1 : Nat.log 2 (s + s) = Nat.log 2 s + 1 := by
      rw [show s + s = s * 2 by ring, Nat.log_mul_base (by norm_num) (by omega)]
    have hl2 : Nat.log 2 s ≤ Nat.log 2 b := Nat.log_mono_right hlt.le
    rw [hl1]
    have hb := blocks_le hs1 hlt
    have := mul_pred_add (a := levelCost b + 2) (x := Nat.log 2 b + 1 - Nat.log 2 s) (by omega)
    rw [show Nat.log 2 b + 1 - Nat.log 2 s - 1 = Nat.log 2 b + 1 - (Nat.log 2 s + 1) by omega]
      at this
    omega

/-! ### The levels of a round -/

/-- **The levels of one round of relaxations by `D`**: started with `r20 = 1`, the flag
`r30 = 0` and the values `E` (between `lo` and `hi` under `Q`, `lo` a feasible potential of `D`
under `Q`), the loop `whileLtN 20 1 levelBF` relaxes every arc `i → j` (`i ≠ j`) of `D` in place
within `(levelCost b + 2) (log₂ b + 1) + 2` steps. -/
theorem levels2_exec (hD : Crossing b D) (hL : Lay b Db eb pb W) {E : ℕ → ℤ} (c : Config)
    (hc : WordsBounded W c) (hE : Env b Db eb pb D c) (hV : Vals b eb E c)
    (h20 : c.nreg 20 = 1) (h30 : c.nreg 30 = 0)
    (hpot : Q → ∀ i j, i < b → j < b → i ≠ j → lo j ≤ lo i + D i j)
    (hS : Q → ∀ v < b, lo v ≤ E v ∧ E v ≤ hi v) :
    ∃ c' k, Exec P W (.whileLtN 20 1 levelBF) c c' k ∧
      k ≤ (levelCost b + 2) * (Nat.log 2 b + 1) + 2 ∧
      (Frm b eb pb c c' ∧ Env b Db eb pb D c' ∧
        ∃ E', Vals b eb E' c' ∧ RoundG b D Q lo hi (fun _ _ => True) E E' (c'.nreg 30)) := by
  refine spec_while (IL2 b Db eb pb D W Q lo hi E c)
    (fun c => (levelCost b + 2) * (Nat.log 2 b + 1 - Nat.log 2 (c.nreg 20))) (fun c h => h.wb)
    (fun c' hc' hlt' => levelBF2_exec hD hL c' hc' hlt')
    ⟨hc, hE, Frm.refl _ _ _ _, ⟨0, by rw [h20]; rfl⟩, by rw [h20]; omega,
      ⟨E, hV, by
        rw [h20, h30]
        exact (RoundG.start hpot hS).mono fun i j _ _ _ hc => not_cov_one_zero hc⟩⟩ ?_
  intro c₂ k₂ hI₂ hn₂ hk₂
  rw [hI₂.env.r1] at hn₂
  obtain ⟨E₂, hV₂, hR₂⟩ := hI₂.vals
  refine ⟨?_, hI₂.frm, hI₂.env, E₂, hV₂,
    hR₂.mono (C' := fun _ _ => True) fun i j hi hj hij _ => cov_all (by omega) hij hi hj⟩
  rw [h20, show Nat.log 2 1 = 0 from Nat.log_one_right 2, Nat.sub_zero] at hk₂
  exact hk₂

end Monge

end PlanarFlow
