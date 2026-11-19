module

public import PlanarFlow.Monge.CmpPlug
public import PlanarFlow.Monge.PrepO

/-!
# Building the tables with bounded comparisons and stores

`prepO_good`: every run of `PlanarFlow.Monge.prepO` from a configuration holding its input
(`InP`), started with the real memory bounded by `B` (`CmpAbs.MemB`), compares only reals
differing by at most `2 B` and stores only reals bounded by `B`, provided `Hb b D + W ≤ B` and
`1 ≤ B`; hence (`prepO_cmpOK`) it is compare-bounded (`ModNat.CmpOK`) and keeps the memory bounded
by `B`.

The bound `hProg` (the only real tests: a loaded length against `0`) passes the abstract
interpretation `CmpAbs.absS`; passes 1 and 2 have no real test and no real store. Pass 3 stores
the constants `0`, `1`, loaded lengths and the replacements `H ± κ` (`entP`), where `H = Hb b D`
stays in the real register `40` and `κ` in the real register `41` is the natural counter `55`
(`≤ W`), so `|H ± κ| ≤ H + W ≤ B`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP CmpAbs

variable {b Vb Db Fb Sb W B : ℕ} {X : ℕ → ℕ → Prop} {D : ℕ → ℕ → ℤ} {P : Input}

/-- The state of pass 3: the bound `H` in `r40`, `1` in `r42` and the natural `r10`. -/
def JP (H : ℝ) (c : Config) : Prop := c.rreg 40 = H ∧ c.rreg 42 = 1 ∧ c.nreg 10 = 1

/-- The state of the entries of a target: also `κ` (`r41`) is the counter `r55`. -/
def JE (H : ℝ) (c : Config) : Prop := JP H c ∧ c.rreg 41 = c.nreg 55

theorem levelP_keeps : keepsR 40 levelP = true ∧ keepsR 42 levelP = true ∧
    keepsN 10 levelP = true := by decide

theorem entP_keeps : keepsR 40 entP = true ∧ keepsR 42 entP = true ∧ keepsN 10 entP = true := by
  decide

/-- The entry block without its last two instructions keeps `κ` and its counter. -/
theorem entP_head_keeps : keepsR 41 (.seq (block [.subN 56 48 10, .subN 56 56 55, .addN 57 43 1,
    .addN 57 57 45, .loadN 57 57, .mulN 58 56 1, .addN 59 58 57, .addN 59 59 42, .loadN 59 59,
    .addN 60 58 45, .addN 61 60 42, .loadN 61 61, .addN 60 60 60, .addN 60 60 40, .storeN 60 61,
    .addN 62 60 10]) <|
  .ifLtN 59 10
     (.seq (block [.constR 43 0, .storeR 62 43, .addN 63 43 57, .loadN 63 63])
        (.seq (.ifLtN 55 63 (.instr (.subR 44 40 41)) (.instr (.addR 44 40 41)))
          (.instr (.storeR 60 44))))
     (block [.constR 43 1, .storeR 62 43, .addN 63 58 57, .addN 63 63 41, .loadR 44 63,
        .storeR 60 44])) = true ∧
  keepsN 55 (.seq (block [.subN 56 48 10, .subN 56 56 55, .addN 57 43 1,
    .addN 57 57 45, .loadN 57 57, .mulN 58 56 1, .addN 59 58 57, .addN 59 59 42, .loadN 59 59,
    .addN 60 58 45, .addN 61 60 42, .loadN 61 61, .addN 60 60 60, .addN 60 60 40, .storeN 60 61,
    .addN 62 60 10]) <|
  .ifLtN 59 10
     (.seq (block [.constR 43 0, .storeR 62 43, .addN 63 43 57, .loadN 63 63])
        (.seq (.ifLtN 55 63 (.instr (.subR 44 40 41)) (.instr (.addR 44 40 41)))
          (.instr (.storeR 60 44))))
     (block [.constR 43 1, .storeR 62 43, .addN 63 58 57, .addN 63 63 41, .loadR 44 63,
        .storeR 60 44])) = true := by decide

theorem pass12_noRS : noRS pass1 = true ∧ noRS pass2 = true ∧ noRS bpar = true := by decide

/-- The replacement `H ± κ`. -/
theorem pm_rreg {c d : Config} {k : ℕ}
    (e : Exec P W (.ifLtN 55 63 (.instr (.subR 44 40 41)) (.instr (.addR 44 40 41))) c d k) :
    (d.rreg 44 = c.rreg 40 - c.rreg 41 ∨ d.rreg 44 = c.rreg 40 + c.rreg 41) ∧
      d.rreg 40 = c.rreg 40 ∧ d.rreg 41 = c.rreg 41 := by
  cases e with
  | ifLtN_true _ e₁ =>
    cases e₁ with
    | instr _ he _ _ =>
      simp only [Instr.effect, Option.some.injEq] at he; subst he
      exact ⟨Or.inl (by config_simp), by config_simp, by config_simp⟩
  | ifLtN_false _ e₁ =>
    cases e₁ with
    | instr _ he _ _ =>
      simp only [Instr.effect, Option.some.injEq] at he; subst he
      exact ⟨Or.inr (by config_simp), by config_simp, by config_simp⟩

/-- **An entry**: bounded stores, and the state `JE` is kept. -/
theorem entP_good {H : ℝ} (hH0 : 0 ≤ H) (hB : H + W ≤ B) (hB1 : 1 ≤ B) (c : Config)
    (hJ : JE H c) :
    Good P W B (2 * B) entP c ∧ ∀ c' k, Exec P W entP c c' k → JE H c' := by
  obtain ⟨⟨j40, j42, j10⟩, j41⟩ := hJ
  obtain ⟨k41, k55⟩ := entP_head_keeps
  obtain ⟨e40, e42, e10⟩ := entP_keeps
  have hB' : (1 : ℝ) ≤ B := by exact_mod_cast hB1
  refine ⟨?_, fun c' k ex => ?_⟩
  · unfold entP
    refine Good.seq (good_noRS (by decide) c) fun c₁ k₁ e₁ => ?_
    have g40 : c₁.rreg 40 = H := (e₁.rreg_keep (by decide)).trans j40
    have g41 : c₁.rreg 41 = c₁.nreg 55 := by
      rw [e₁.rreg_keep (by decide), e₁.nreg_keep (by decide)]; exact j41
    have g55 : c₁.nreg 55 ≤ W := e₁.wb_right.1 55
    refine Good.seq (Good.ifLtN (fun _ => ?_) (fun _ => ?_)) fun _ _ _ =>
      good_noRS (by decide) _
    · refine Good.seq (good_abs' (m := 2) (n := 2) (A := []) (by decide) fun _ => regA_nil _)
        fun c₂ k₂ e₂ => ?_
      have h40 : c₂.rreg 40 = H := (e₂.rreg_keep (by decide)).trans g40
      have h41 : c₂.rreg 41 = c₂.nreg 55 := by
        rw [e₂.rreg_keep (by decide), e₂.nreg_keep (by decide)]; exact g41
      have h55 : c₂.nreg 55 ≤ W := e₂.wb_right.1 55
      refine Good.seq (good_noRS (by decide) c₂) fun c₃ k₃ e₃ => Good.instr fun _ => ?_
      obtain ⟨h44, -, -⟩ := pm_rreg e₃
      show |c₃.rreg 44| ≤ (B : ℝ)
      have hW : (c₂.nreg 55 : ℝ) ≤ W := by exact_mod_cast h55
      have h0 : (0 : ℝ) ≤ c₂.nreg 55 := Nat.cast_nonneg _
      rcases h44 with h | h <;> rw [h, h40, h41, abs_le] <;> constructor <;> linarith
    · refine good_cons (fun _ => trivial) fun c₂ he₂ => ?_
      simp only [Instr.effect, Option.some.injEq] at he₂; subst he₂
      refine good_cons (fun _ => ?_) fun c₃ _ =>
        good_abs' (m := 2) (n := 2) (A := []) (by decide) fun _ => regA_nil _
      show |(upd c₁.rreg 43 ((1 : ℤ) : ℝ)) 43| ≤ (B : ℝ)
      simp only [upd_same, Int.cast_one, abs_one]; exact hB'
  · -- the state after the entry
    have i40 := ex.rreg_keep e40; have i42 := ex.rreg_keep e42; have i10 := ex.nreg_keep e10
    unfold entP at ex
    cases ex with
    | seq e₁ e₂ =>
      cases e₂ with
      | seq e₃ e₄ =>
        have eh := Exec.seq e₁ e₃
        obtain ⟨h1, -⟩ := e₄.block_effs
        simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at h1
        subst h1
        refine ⟨⟨i40.trans j40, i42.trans j42, i10.trans j10⟩, ?_⟩
        config_simp
        rw [eh.rreg_keep k41, eh.nreg_keep k55, eh.rreg_keep (by decide),
          eh.nreg_keep (by decide), j41, j42, j10]
        push_cast; ring

/-- **Pass 3**: bounded stores, and the state `JP` is kept. -/
theorem pass3_good {H : ℝ} (hH0 : 0 ≤ H) (hB : H + W ≤ B) (hB1 : 1 ≤ B) (c : Config)
    (hJ : JP H c) : Good P W B (2 * B) pass3 c := by
  unfold pass3
  refine Good.seq (good_noRS (by decide) c) fun c₁ k₁ e₁ => ?_
  have hJ₁ : JP H c₁ := ⟨(e₁.rreg_keep (by decide)).trans hJ.1,
    (e₁.rreg_keep (by decide)).trans hJ.2.1, (e₁.nreg_keep (by decide)).trans hJ.2.2⟩
  refine Good.whileLtN (JP H) (fun c hJ _ => ⟨?_, fun c' k ex => ?_⟩) hJ₁
  · unfold p3Body
    refine Good.seq (good_noRS (by decide) c) fun c₂ k₂ e₂ => ?_
    refine Good.seq (good_noRS (by decide) c₂) fun c₃ k₃ e₃ => ?_
    have hJ₂ : JP H c₂ := ⟨(e₂.rreg_keep (by decide)).trans hJ.1,
      (e₂.rreg_keep (by decide)).trans hJ.2.1, (e₂.nreg_keep (by decide)).trans hJ.2.2⟩
    obtain ⟨h1, -⟩ := e₃.block_effs
    simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at h1
    subst h1
    refine Good.seq (Good.whileLtN (JE H) (fun c hJ _ => entP_good hH0 hB hB1 c hJ) ?_)
      fun _ _ _ => good_noRS (by decide) _
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · config_simp; exact hJ₂.1
    · config_simp; exact hJ₂.2.1
    · config_simp; exact hJ₂.2.2
    · config_simp; simp
  · exact ⟨(ex.rreg_keep (by decide)).trans hJ.1, (ex.rreg_keep (by decide)).trans hJ.2.1,
      (ex.nreg_keep (by decide)).trans hJ.2.2⟩

/-- **The tables with bounded comparisons and stores.** -/
theorem prepO_good (hL : LayP b Vb Db Fb Sb W) (hB : Hb b D + W ≤ B) (hB1 : 1 ≤ B) (c : Config)
    (hc : WordsBounded W c) (hI : InP b Vb Db Fb Sb X D c) :
    Good P W B (2 * B) prepO c := by
  have hw := hL.w; have hsd := hL.sd; have hdv := hL.dv
  have hH0 : 0 ≤ Hb b D := by
    unfold Hb; positivity
  unfold prepO
  refine good_seq_use (hProg_exec (P := P) (D := D) (by omega) c hc hI.r1 hI.r41 hI.dv)
    (good_abs' (m := 2) (n := 6) (A := []) (by decide) fun _ => regA_nil _) ?_
  rintro c₁ k₁ - - ⟨h40, h10, h42, -⟩
  refine Good.seq (good_noRS (by decide) c₁) fun c₂ k₂ e₂ => ?_
  have hJ : JP (Hb b D) c₂ := ⟨(e₂.rreg_keep (by decide)).trans h40,
    (e₂.rreg_keep (by decide)).trans h42, (e₂.nreg_keep (by decide)).trans h10⟩
  obtain ⟨k40, k42, k10⟩ := levelP_keeps
  refine Good.whileLtN (JP (Hb b D)) (fun c hJ _ => ⟨?_, fun c' k ex =>
    ⟨(ex.rreg_keep k40).trans hJ.1, (ex.rreg_keep k42).trans hJ.2.1,
      (ex.nreg_keep k10).trans hJ.2.2⟩⟩) hJ
  unfold levelP
  refine Good.seq (good_noRS pass12_noRS.1 c) fun c₃ k₃ e₃ => ?_
  refine Good.seq (good_noRS pass12_noRS.2.1 c₃) fun c₄ k₄ e₄ => ?_
  have hJ₄ : JP (Hb b D) c₄ :=
    ⟨(by rw [e₄.rreg_keep (by decide), e₃.rreg_keep (by decide)]; exact hJ.1),
      (by rw [e₄.rreg_keep (by decide), e₃.rreg_keep (by decide)]; exact hJ.2.1),
      (by rw [e₄.nreg_keep (by decide), e₃.nreg_keep (by decide)]; exact hJ.2.2)⟩
  exact Good.seq (pass3_good hH0 hB hB1 c₄ hJ₄) fun _ _ _ => good_noRS (by decide) _

/-- **The tables are compare-bounded**, from the real memory bounded by `B`. -/
theorem prepO_cmpOK (hL : LayP b Vb Db Fb Sb W) (hB : Hb b D + W ≤ B) (hB1 : 1 ≤ B) (c : Config)
    (hc : WordsBounded W c) (hI : InP b Vb Db Fb Sb X D c) (hM : MemB W B c) :
    ModNat.CmpOK P W (2 * B) prepO c :=
  (prepO_good hL hB hB1 c hc hI).toCmp hM

end Monge

end PlanarFlow
