module

public import PlanarFlow.Monge.PrepMath
public import PlanarFlow.NegSSSP.BFExecO

/-!
# Building the tables: the data in memory, and the bound `H`

The input of the pass `PlanarFlow.Monge.prepO` is the plain encoding of a dense distance graph
with missing arcs: the arc flags `finB X s t` at `Fb + s b + t` (natural memory) and the lengths
`D s t` at `Db + s b + t` (real memory) (`InP`). The pass writes the tables `tVal`, `tMul`,
`finB` at `Vb + 2 (s b + t)` (`TabOK`), using the scratch cells `Sb … Sb + 3b - 1` (natural
memory), within the layout `LayP`, changing only the registers `44 … 79` and the real registers
`40 … 46` (`FrP`).

* `hProg`: **the bound** `Hb b D = Σ |D s t| + b + 1` into the real register `40`
  (`hProg_exec`, within `10 b² + 10 b + 12` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP Finset

/-- The layout of the pass. -/
structure LayP (b Vb Db Fb Sb W : ℕ) : Prop where
  fs : Fb + b * b ≤ Sb
  sd : Sb + 3 * b ≤ Db
  dv : Db + b * b ≤ Vb
  w : Vb + 2 * (b * b) + 4 * b + 10 ≤ W

/-- The input of the pass. -/
structure InP (b Vb Db Fb Sb : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (c : Config) : Prop where
  r1 : c.nreg 1 = b
  r10 : c.nreg 10 = 1
  r40 : c.nreg 40 = Vb
  r41 : c.nreg 41 = Db
  r42 : c.nreg 42 = Fb
  r43 : c.nreg 43 = Sb
  fl : ∀ s t, s < b → t < b → c.nmem (Fb + s * b + t) = finB X s t
  dv : ∀ s t, s < b → t < b → c.rmem (Db + s * b + t) = D s t

/-- The frame of the pass. -/
structure FrP (b Vb Sb : ℕ) (c c' : Config) : Prop where
  nreg : ∀ r, (r < 44 ∨ 80 ≤ r) → c'.nreg r = c.nreg r
  rreg : ∀ r, (r < 40 ∨ 47 ≤ r) → c'.rreg r = c.rreg r
  nmem : ∀ a, (a < Sb ∨ (Sb + 3 * b ≤ a ∧ a < Vb) ∨ Vb + 2 * (b * b) ≤ a) → c'.nmem a = c.nmem a
  rmem : ∀ a, (a < Vb ∨ Vb + 2 * (b * b) ≤ a) → c'.rmem a = c.rmem a
  out : c'.output = c.output

theorem FrP.refl (b Vb Sb : ℕ) (c : Config) : FrP b Vb Sb c c :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem FrP.trans {b Vb Sb : ℕ} {c c' c'' : Config} (h : FrP b Vb Sb c c')
    (h' : FrP b Vb Sb c' c'') : FrP b Vb Sb c c'' :=
  ⟨fun r hr => (h'.nreg r hr).trans (h.nreg r hr), fun r hr => (h'.rreg r hr).trans (h.rreg r hr),
    fun a ha => (h'.nmem a ha).trans (h.nmem a ha), fun a ha => (h'.rmem a ha).trans (h.rmem a ha),
    h'.out.trans h.out⟩

variable {b Vb Db Fb Sb W : ℕ} {X : ℕ → ℕ → Prop} {D : ℕ → ℕ → ℤ} {P : Input}

/-- The input survives the frame. -/
theorem InP.of (hL : LayP b Vb Db Fb Sb W) {c c' : Config} (h : InP b Vb Db Fb Sb X D c)
    (hF : FrP b Vb Sb c c') : InP b Vb Db Fb Sb X D c' := by
  have := hL.fs; have := hL.sd; have := hL.dv
  refine ⟨(hF.nreg 1 (by omega)).trans h.r1, (hF.nreg 10 (by omega)).trans h.r10,
    (hF.nreg 40 (by omega)).trans h.r40, (hF.nreg 41 (by omega)).trans h.r41,
    (hF.nreg 42 (by omega)).trans h.r42, (hF.nreg 43 (by omega)).trans h.r43,
    fun s t hs ht => ?_, fun s t hs ht => ?_⟩
  · have := Nat.mul_le_mul_right b (show s + 1 ≤ b by omega)
    rw [hF.nmem _ (Or.inl (by rw [Nat.add_mul] at this; omega))]; exact h.fl s t hs ht
  · have := Nat.mul_le_mul_right b (show s + 1 ≤ b by omega)
    rw [hF.rmem _ (Or.inl (by rw [Nat.add_mul] at this; omega))]; exact h.dv s t hs ht

/-- The table entries of the pairs `Pr` are written. -/
def TabOK (b Vb : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (H : ℝ) (Pr : ℕ → ℕ → Prop)
    (c : Config) : Prop :=
  ∀ s t, s < b → t < b → s ≠ t → Pr s t →
    c.rmem (Vb + 2 * (s * b + t)) = tVal b X D H s t ∧
      c.rmem (Vb + 2 * (s * b + t) + 1) = tMul b X s t ∧ c.nmem (Vb + 2 * (s * b + t)) = finB X s t

/-- Fewer pairs. -/
theorem TabOK.mono {H : ℝ} {Pr Pr' : ℕ → ℕ → Prop} {c : Config} (h : TabOK b Vb X D H Pr c)
    (hP : ∀ s t, Pr' s t → Pr s t) : TabOK b Vb X D H Pr' c :=
  fun s t hs ht hst hp => h s t hs ht hst (hP s t hp)

/-- The tables survive a step not writing their region. -/
theorem TabOK.of {H : ℝ} {Pr : ℕ → ℕ → Prop} {c c' : Config} (h : TabOK b Vb X D H Pr c)
    (hn : ∀ a, Vb ≤ a → a < Vb + 2 * (b * b) → c'.nmem a = c.nmem a)
    (hr : ∀ a, Vb ≤ a → a < Vb + 2 * (b * b) → c'.rmem a = c.rmem a) :
    TabOK b Vb X D H Pr c' := by
  intro s t hs ht hst hp
  obtain ⟨-, -, h3⟩ := rowcol hs ht
  obtain ⟨e1, e2, e3⟩ := h s t hs ht hst hp
  exact ⟨(hr _ (by omega) (by omega)).trans e1, (hr _ (by omega) (by omega)).trans e2,
    (hn _ (by omega) (by omega)).trans e3⟩

/-- The table cells of distinct pairs are distinct. -/
lemma cellP_ne {s t s' t' : ℕ} (hs : s < b) (ht : t < b) (hs' : s' < b) (ht' : t' < b)
    (h : (s, t) ≠ (s', t')) : s * b + t ≠ s' * b + t' := by
  intro e
  obtain ⟨a1, a2, -⟩ := rowcol hs ht
  obtain ⟨b1, b2, -⟩ := rowcol hs' ht'
  rw [e] at a1 a2
  exact h (by rw [← a1, ← a2, b1, b2])

/-! ### The bound -/

/-- One length added in absolute value. -/
def hInner : Stmt :=
  .seq (block [.mulN 66 64 1, .addN 66 66 65, .addN 66 66 41, .loadR 45 66])
    (.seq (.ifLtR 45 46 (.instr (.subR 40 40 45)) (.instr (.addR 40 40 45)))
      (.instr (.addN 65 65 10)))

/-- One row of lengths. -/
def hOuter : Stmt :=
  .seq (.instr (.constN 65 0)) (.seq (.whileLtN 65 1 hInner)
    (block [.addR 40 40 42, .addN 64 64 10]))

/-- The bound `Hb b D` into the real register `40`. -/
def hProg : Stmt :=
  .seq (block [.constN 10 1, .constR 46 0, .constR 42 1, .constR 40 0, .constN 64 0]) <|
    .seq (.whileLtN 64 1 hOuter) (.instr (.addR 40 40 42))

/-- The state of the bound in row `s`. -/
structure IH (b Db W : ℕ) (D : ℕ → ℕ → ℤ) (s : ℕ) (acc : ℝ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  nreg : ∀ r, r ≠ 65 → r ≠ 66 → c.nreg r = c₀.nreg r
  rreg : ∀ r, r ≠ 40 → r ≠ 45 → c.rreg r = c₀.rreg r
  nmem : c.nmem = c₀.nmem
  rmem : c.rmem = c₀.rmem
  out : c.output = c₀.output
  le : c.nreg 65 ≤ b
  acc : c.rreg 40 = acc + ∑ t ∈ range (c.nreg 65), |(D s t : ℝ)|

theorem hInner_exec {s : ℕ} {acc : ℝ} {c₀ : Config} (hb : b + Db + b * b ≤ W)
    (h1 : c₀.nreg 1 = b) (h10 : c₀.nreg 10 = 1) (h41 : c₀.nreg 41 = Db) (h64 : c₀.nreg 64 = s)
    (hs : s < b) (h46 : c₀.rreg 46 = 0)
    (hdv : ∀ t < b, c₀.rmem (Db + s * b + t) = D s t) (c : Config) (hI : IH b Db W D s acc c₀ c)
    (hlt : c.nreg 65 < c.nreg 1) :
    ∃ c' k', Exec P W hInner c c' k' ∧ IH b Db W D s acc c₀ c' ∧
      10 * (b - c'.nreg 65) + k' + 2 ≤ 10 * (b - c.nreg 65) := by
  have hc := hI.wb
  have g1 : c.nreg 1 = b := (hI.nreg 1 (by omega) (by omega)).trans h1
  have g10 : c.nreg 10 = 1 := (hI.nreg 10 (by omega) (by omega)).trans h10
  have g41 : c.nreg 41 = Db := (hI.nreg 41 (by omega) (by omega)).trans h41
  have g64 : c.nreg 64 = s := (hI.nreg 64 (by omega) (by omega)).trans h64
  have g46 : c.rreg 46 = 0 := (hI.rreg 46 (by omega) (by omega)).trans h46
  rw [g1] at hlt
  generalize ht : c.nreg 65 = t at hlt
  have hsb : s * b + b ≤ b * b := by
    have := Nat.mul_le_mul_right b (show s + 1 ≤ b by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hx : c.rmem (s * b + t + Db) = D s t := by
    rw [hI.rmem, show s * b + t + Db = Db + s * b + t by ring]; exact hdv t hlt
  have hacc := hI.acc
  rw [ht] at hacc
  unfold hInner
  refine spec_seq ?_
  exec_block
  · rw [g64, g1]; omega
  · config_simp; rw [g64, g1, ht]; omega
  · config_simp; rw [g64, g1, ht, g41]; omega
  have hfin : ∀ c' : Config, WordsBounded W c' → (∀ r, r ≠ 65 → r ≠ 66 → c'.nreg r = c.nreg r) →
      (∀ r, r ≠ 40 → r ≠ 45 → c'.rreg r = c.rreg r) → c'.nmem = c.nmem → c'.rmem = c.rmem →
      c'.output = c.output → c'.nreg 65 = t + 1 →
      c'.rreg 40 = acc + ∑ t' ∈ range (t + 1), |(D s t' : ℝ)| → IH b Db W D s acc c₀ c' :=
    fun c' hw hn hr hnm hrm ho h65 h40 =>
      ⟨hw, fun r a b' => (hn r a b').trans (hI.nreg r a b'), fun r a b' => (hr r a b').trans
        (hI.rreg r a b'), hnm.trans hI.nmem, hrm.trans hI.rmem, ho.trans hI.out, by omega,
        by rw [h65]; exact h40⟩
  refine spec_seq ?_
  by_cases hneg : (D s t : ℝ) < 0
  · refine spec_ifLtR_true (by config_simp; rw [g64, g1, ht, g41, hx, g46]; exact hneg) ?_
    refine spec_instr (Exec.subR ‹_› _ _ _) fun hw₁ => ?_
    refine spec_instr (Exec.addN hw₁ 65 65 10 (by config_simp; rw [ht, g10]; omega)) fun hw => ?_
    refine ⟨hfin _ hw (fun r a b' => by config_simp; upd_tac)
      (fun r a b' => by config_simp; upd_tac)
      rfl rfl rfl (by config_simp; rw [ht, g10]) ?_, ?_⟩
    · config_simp; rw [g64, g1, ht, g41, hx, hacc, sum_range_succ, abs_of_neg hneg]; ring
    · config_simp; rw [ht, g10]; omega
  · refine spec_ifLtR_false (by config_simp; rw [g64, g1, ht, g41, hx, g46]; exact hneg) ?_
    refine spec_instr (Exec.addR ‹_› _ _ _) fun hw₁ => ?_
    refine spec_instr (Exec.addN hw₁ 65 65 10 (by config_simp; rw [ht, g10]; omega)) fun hw => ?_
    refine ⟨hfin _ hw (fun r a b' => by config_simp; upd_tac)
      (fun r a b' => by config_simp; upd_tac)
      rfl rfl rfl (by config_simp; rw [ht, g10]) ?_, ?_⟩
    · config_simp; rw [g64, g1, ht, g41, hx, hacc, sum_range_succ, abs_of_nonneg (not_lt.1 hneg)]
      ring
    · config_simp; rw [ht, g10]; omega

/-- The state of the bound before row `r64`. -/
structure IHo (b Db W : ℕ) (D : ℕ → ℕ → ℤ) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  nreg : ∀ r, r ≠ 64 → r ≠ 65 → r ≠ 66 → c.nreg r = c₀.nreg r
  rreg : ∀ r, r ≠ 40 → r ≠ 45 → c.rreg r = c₀.rreg r
  nmem : c.nmem = c₀.nmem
  rmem : c.rmem = c₀.rmem
  out : c.output = c₀.output
  le : c.nreg 64 ≤ b
  acc : c.rreg 40 = ∑ s ∈ range (c.nreg 64), (∑ t ∈ range b, |(D s t : ℝ)| + 1)

theorem hOuter_exec {c₀ : Config} (hb : b + Db + b * b ≤ W) (h1 : c₀.nreg 1 = b)
    (h10 : c₀.nreg 10 = 1) (h41 : c₀.nreg 41 = Db) (h46 : c₀.rreg 46 = 0) (h42 : c₀.rreg 42 = 1)
    (hdv : ∀ s t, s < b → t < b → c₀.rmem (Db + s * b + t) = D s t) (c : Config)
    (hI : IHo b Db W D c₀ c) (hlt : c.nreg 64 < c.nreg 1) :
    ∃ c' k', Exec P W hOuter c c' k' ∧ IHo b Db W D c₀ c' ∧
      (10 * b + 8) * (b - c'.nreg 64) + k' + 2 ≤ (10 * b + 8) * (b - c.nreg 64) := by
  have hc := hI.wb
  have g1 : c.nreg 1 = b := (hI.nreg 1 (by omega) (by omega) (by omega)).trans h1
  have g10 : c.nreg 10 = 1 := (hI.nreg 10 (by omega) (by omega) (by omega)).trans h10
  rw [g1] at hlt
  generalize hs : c.nreg 64 = s at hlt
  have hacc := hI.acc
  rw [hs] at hacc
  unfold hOuter
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 65 0 (by omega)) fun hw₁ => ?_
  refine spec_seq ?_
  refine spec_while (IH b Db W D s (c.rreg 40) { c with nreg := upd c.nreg 65 0 })
    (fun c => 10 * (b - c.nreg 65)) (fun c h => h.wb)
    (fun c' hc' hlt' => hInner_exec hb (by config_simp; exact g1) (by config_simp; exact g10)
      (by config_simp; rw [hI.nreg 41 (by omega) (by omega) (by omega), h41])
      (by config_simp; exact hs) hlt
      (by config_simp; rw [hI.rreg 46 (by omega) (by omega), h46])
      (fun t ht => by config_simp; rw [hI.rmem]; exact hdv s t hlt ht) c' hc' hlt')
    ⟨hw₁, fun _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl, by config_simp; omega,
      by config_simp; simp⟩ ?_
  intro c₂ k₂ hI₂ hn₂ hk₂
  have h65 : c₂.nreg 65 = b := by
    have := hI₂.le; rw [hI₂.nreg 1 (by omega) (by omega)] at hn₂; config_simp at hn₂; rw [g1] at hn₂
    omega
  have hw₂ := hI₂.wb
  have g42 : c₂.rreg 42 = 1 := by
    rw [hI₂.rreg 42 (by omega) (by omega)]; config_simp
    rw [hI.rreg 42 (by omega) (by omega), h42]
  exec_block
  · config_simp; rw [hI₂.nreg 64 (by omega) (by omega)]; config_simp; rw [hs]
    rw [hI₂.nreg 10 (by omega) (by omega)]; config_simp; rw [g10]; omega
  have e64 : c₂.nreg 64 = s := by rw [hI₂.nreg 64 (by omega) (by omega)]; config_simp; exact hs
  have e10 : c₂.nreg 10 = 1 := by rw [hI₂.nreg 10 (by omega) (by omega)]; config_simp; exact g10
  refine ⟨⟨‹_›, fun r a1 a2 a3 => ?_, fun r a1 a2 => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · config_simp; rw [upd_other _ _ _ a1, hI₂.nreg r a2 a3]; config_simp
    rw [upd_other _ _ _ a2]; exact hI.nreg r a1 a2 a3
  · config_simp; rw [upd_other _ _ _ a1, hI₂.rreg r a1 a2]; config_simp; exact hI.rreg r a1 a2
  · config_simp; rw [hI₂.nmem]; config_simp; exact hI.nmem
  · config_simp; rw [hI₂.rmem]; config_simp; exact hI.rmem
  · config_simp; rw [hI₂.out]; config_simp; exact hI.out
  · config_simp; rw [e64, e10]; omega
  · config_simp; rw [e64, e10, hI₂.acc, h65, g42, hacc, sum_range_succ]; ring
  · config_simp; rw [e64, e10]
    beta_reduce at hk₂; config_simp at hk₂
    have := mul_pred_add (a := 10 * b + 8) (x := b - s) (by omega)
    rw [show b - s - 1 = b - (s + 1) by omega] at this
    generalize (10 * b + 8) * (b - (s + 1)) = Y at this ⊢
    omega

/-- **The bound `Hb b D` into the real register `40`.** -/
theorem hProg_exec (hb : b + Db + b * b + 1 ≤ W) (c : Config) (hc : WordsBounded W c)
    (h1 : c.nreg 1 = b) (h41 : c.nreg 41 = Db)
    (hdv : ∀ s t, s < b → t < b → c.rmem (Db + s * b + t) = D s t) :
    ∃ c' k, Exec P W hProg c c' k ∧ k ≤ (10 * b + 8) * b + 10 ∧
      (c'.rreg 40 = Hb b D ∧ c'.nreg 10 = 1 ∧ c'.rreg 42 = 1 ∧ c'.rreg 46 = 0 ∧
        (∀ r, r ≠ 10 → r ≠ 64 → r ≠ 65 → r ≠ 66 → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 40 → r ≠ 42 → r ≠ 45 → r ≠ 46 → c'.rreg r = c.rreg r) ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold hProg
  refine spec_seq ?_
  exec_block
  · omega
  · omega
  refine spec_seq ?_
  refine spec_while (IHo b Db W D _) (fun c => (10 * b + 8) * (b - c.nreg 64)) (fun c h => h.wb)
    (fun c' hc' hlt' => hOuter_exec (by omega) (by config_simp; exact h1) (by config_simp)
      (by config_simp; exact h41) (by config_simp; simp) (by config_simp; simp)
      (fun s t hs ht => by config_simp; exact hdv s t hs ht) c' hc' hlt')
    ⟨‹_›, fun _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl, by config_simp; omega,
      by config_simp; simp⟩ ?_
  intro c₂ k₂ hI₂ hn₂ hk₂
  have h64 : c₂.nreg 64 = b := by
    have := hI₂.le
    rw [hI₂.nreg 1 (by omega) (by omega) (by omega)] at hn₂; config_simp at hn₂; rw [h1] at hn₂
    omega
  refine spec_instr (Exec.addR hI₂.wb 40 40 42) fun hw => ?_
  refine ⟨?_, ?_, ?_, ?_, ?_, fun r a1 a2 a3 a4 => ?_, fun r a1 a2 a3 a4 => ?_, ?_, ?_, ?_⟩
  · beta_reduce at hk₂; config_simp at hk₂; simp only [Nat.sub_zero] at hk₂; omega
  · config_simp
    rw [hI₂.acc, h64, hI₂.rreg 42 (by omega) (by omega)]; config_simp
    unfold Hb
    rw [sum_add_distrib, sum_const, card_range]; simp
  · config_simp; rw [hI₂.nreg 10 (by omega) (by omega) (by omega)]; config_simp
  · config_simp; rw [hI₂.rreg 42 (by omega) (by omega)]; config_simp; simp
  · config_simp; rw [hI₂.rreg 46 (by omega) (by omega)]; config_simp; simp
  · config_simp; rw [hI₂.nreg r a2 a3 a4]; config_simp; upd_tac
  · config_simp; rw [upd_other _ _ _ a1, hI₂.rreg r a1 a3]; config_simp; upd_tac
  · config_simp; rw [hI₂.nmem]
  · config_simp; rw [hI₂.rmem]
  · config_simp; rw [hI₂.out]

end Monge

end PlanarFlow
