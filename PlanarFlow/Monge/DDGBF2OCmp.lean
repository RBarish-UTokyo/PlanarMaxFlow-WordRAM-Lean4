module

public import PlanarFlow.Monge.CmpPlug
public import PlanarFlow.Monge.DDGBF2O

/-!
# Bellman–Ford over two matrices with missing arcs: bounded comparisons and stores

`bfDDG2O_good`: every run of `PlanarFlow.Monge.bfDDG2O` (from the configuration of
`bfDDG2O_exec`, the real memory bounded by `B`) compares only reals differing by at most `2 B`
and stores only reals bounded by `B`, when the lengths are bounded by `L`, the bounds `H₁`, `H₂`
of the tables are at least `b`, and `bfXm b L + L + Hᵢ + b ≤ B` (`bfXm b L = 2 bfΔ b L (b + 1)`,
`bfΔ b L = 2 b L (2 b + 1)`, the lower bound of the values).

* **The values stay bounded below** (`ELow`): a half block lowers the values at most by `L` (the
  update stores a row minimum, an entry `E s + D s t` of the copied matrix, or keeps the value),
  a block by `2 L`, a level by `2 b L`, the levels of a matrix by `bfΔ b L`, a round by
  `2 bfΔ b L`.
* **SMAWK calls the oracle at valid indices only**: SMAWK's realization lemma `smawk_exec` is
  generic in the oracle; with the *checked oracle* `entC B` (the oracle `entO`, then a check that
  stops the machine when the entry is not bounded by `B`), it gives a run of `smawk (entC B)`,
  hence (`CmpAbs.good_plug`, the oracle replaced in the abstract interpretation by a marker
  `mkO` that bounds `r70` by `B`) every run of `smawk entO` compares and stores only entries of
  the copied matrix, bounded by `B` (`smawk_good`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs CmpAbs

/-! ### Good runs with a postcondition -/

section GoodQ

variable {P : Input} {W B H : ℕ}

/-- `Good` with a property of the end of every run. -/
def GoodQ (P : Input) (W B H : ℕ) (s : Stmt) (c : Config) (Q : Config → Prop) : Prop :=
  Good P W B H s c ∧ ∀ c' k, Exec P W s c c' k → Q c'

theorem GoodQ.seq {s t : Stmt} {c : Config} {Q : Config → Prop} (hs : Good P W B H s c)
    (ht : ∀ c₁ k₁, Exec P W s c c₁ k₁ → GoodQ P W B H t c₁ Q) :
    GoodQ P W B H (.seq s t) c Q := by
  refine ⟨hs.seq fun c₁ k₁ e₁ => (ht c₁ k₁ e₁).1, fun c' k e => ?_⟩
  cases e with
  | seq e₁ e₂ => exact (ht _ _ e₁).2 _ _ e₂

theorem goodQ_use {s t : Stmt} {c : Config} {K : ℕ} {post : Config → Prop} {Q : Config → Prop}
    (h : ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ post c') (hs : Good P W B H s c)
    (ht : ∀ c' k, k ≤ K → WordsBounded W c' → post c' → GoodQ P W B H t c' Q) :
    GoodQ P W B H (.seq s t) c Q := by
  refine GoodQ.seq hs fun c₁ k₁ e₁ => ?_
  obtain ⟨c', k, e, hk, hp⟩ := h
  obtain ⟨rfl, rfl⟩ := Exec.det e e₁
  exact ht _ _ hk e.wb_right hp

theorem goodQ_ex {s t : Stmt} {c : Config} {Q : Config → Prop} (hs : Good P W B H s c)
    (h : ∃ c₁ k₁, Exec P W s c c₁ k₁ ∧ GoodQ P W B H t c₁ Q) : GoodQ P W B H (.seq s t) c Q := by
  refine GoodQ.seq hs fun c₁ k₁ e₁ => ?_
  obtain ⟨c₂, k₂, e₂, hg⟩ := h
  obtain ⟨rfl, rfl⟩ := Exec.det e₂ e₁
  exact hg

theorem goodQ_instr {i : Instr} {t : Stmt} {c c₁ : Config} {Q : Config → Prop}
    (h₁ : Exec P W (.instr i) c c₁ 1) (hst : noRS (.instr i) = true)
    (h : WordsBounded W c₁ → GoodQ P W B H t c₁ Q) : GoodQ P W B H (.seq (.instr i) t) c Q :=
  goodQ_ex (good_noRS hst c) ⟨c₁, 1, h₁, h h₁.wb_right⟩

theorem GoodQ.whileLtN {a b : ℕ} {body : Stmt} (I : Config → Prop)
    (hI : ∀ c, I c → c.nreg a < c.nreg b → GoodQ P W B H body c I)
    {c : Config} (hc : I c) : GoodQ P W B H (.whileLtN a b body) c I := by
  refine ⟨Good.whileLtN I (fun c h ht => ⟨(hI c h ht).1, (hI c h ht).2⟩) hc, fun c' k e => ?_⟩
  generalize hs : Stmt.whileLtN a b body = s at e
  induction e with
  | whileLtN_false => cases hs; exact hc
  | whileLtN_true ht e₁ _ _ ih₂ => cases hs; exact ih₂ ((hI _ hc ht).2 _ _ e₁) rfl
  | _ => cases hs

theorem GoodQ.mono {s : Stmt} {c : Config} {Q Q' : Config → Prop} (h : GoodQ P W B H s c Q)
    (hQ : ∀ c, Q c → Q' c) : GoodQ P W B H s c Q' := ⟨h.1, fun c' k e => hQ _ (h.2 c' k e)⟩

theorem GoodQ.noRS {s : Stmt} {c : Config} {Q : Config → Prop} (h : noRS s = true)
    (hQ : ∀ c' k, Exec P W s c c' k → Q c') : GoodQ P W B H s c Q := ⟨good_noRS h c, hQ⟩


theorem goodQ_useQ {s t : Stmt} {c : Config} {K : ℕ} {post Q₁ : Config → Prop}
    {Q : Config → Prop} (h : ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ post c')
    (hs : GoodQ P W B H s c Q₁)
    (ht : ∀ c' k, k ≤ K → WordsBounded W c' → post c' → Q₁ c' → GoodQ P W B H t c' Q) :
    GoodQ P W B H (.seq s t) c Q := by
  refine GoodQ.seq hs.1 fun c₁ k₁ e₁ => ?_
  obtain ⟨c', k, e, hk, hp⟩ := h
  obtain ⟨rfl, rfl⟩ := Exec.det e e₁
  exact ht _ _ hk e.wb_right hp (hs.2 _ _ e)

theorem GoodQ.seqQ {s t : Stmt} {c : Config} {Q₁ Q : Config → Prop} (hs : GoodQ P W B H s c Q₁)
    (ht : ∀ c₁ k₁, Exec P W s c c₁ k₁ → Q₁ c₁ → GoodQ P W B H t c₁ Q) :
    GoodQ P W B H (.seq s t) c Q :=
  GoodQ.seq hs.1 fun c₁ k₁ e₁ => ht c₁ k₁ e₁ (hs.2 _ _ e₁)

theorem GoodQ.and_run {s : Stmt} {c : Config} {Q R : Config → Prop} (h : GoodQ P W B H s c Q)
    (hr : ∃ c' k, Exec P W s c c' k ∧ R c') : GoodQ P W B H s c (fun c' => R c' ∧ Q c') := by
  refine ⟨h.1, fun c' k e => ⟨?_, h.2 c' k e⟩⟩
  obtain ⟨c'', k', e', hR⟩ := hr
  obtain ⟨rfl, rfl⟩ := Exec.det e' e
  exact hR

/-- No real store. -/
def noStR : Instr → Bool
  | .storeR _ _ => false
  | _ => true

/-- A statement without real stores keeps the real memory. -/
theorem _root_.WordRAM.Machine.Exec.rmem_keep {s : Stmt} {c d : Config} {k : ℕ}
    (e : Exec P W s c d k) (h : s.allI noStR = true) : d.rmem = c.rmem := by
  refine Exec.of_steps (R := fun c d => d.rmem = c.rmem) (fun _ => rfl)
    (fun _ _ _ h₁ h₂ => h₂.trans h₁) (fun i c c' _ hi he => ?_) e h
  cases i <;> simp only [Instr.effect, Option.some.injEq, noStR] at he hi <;>
    (try split_ifs at he) <;> (try simp only [Option.some.injEq, reduceCtorEq] at he) <;>
    first | (subst he; rfl) | simp at hi

end GoodQ

/-! ### The values bounded below -/

/-- The values at `eb` are at least `-X`. -/
def ELow (b eb X : ℕ) (c : Config) : Prop := ∀ v < b, -(X : ℝ) ≤ c.rmem (eb + v)

theorem ELow.mono {b eb X X' : ℕ} {c : Config} (h : ELow b eb X c) (hX : X ≤ X') :
    ELow b eb X' c := fun v hv => by
  have : (X : ℝ) ≤ X' := by exact_mod_cast hX
  linarith [h v hv]

theorem ELow.of {b eb X : ℕ} {c c' : Config} (h : ELow b eb X c)
    (hm : ∀ v < b, c'.rmem (eb + v) = c.rmem (eb + v)) : ELow b eb X c' :=
  fun v hv => by rw [hm v hv]; exact h v hv

variable {b : ℕ} {X : ℕ → ℕ → Prop} {D : ℕ → ℕ → ℤ} {Vb eb pb W B L : ℕ} {H : ℝ} {P : Input}

/-- **The entries of the copied matrix are bounded**: between `-(X + L)` and `L + H + b`, for
values in `[-X, 0]` and lengths bounded by `L`. -/
theorem blkO_bound {E : ℕ → ℤ} {Xl : ℕ} (hE : ∀ v < b, -(Xl : ℝ) ≤ E v ∧ (E v : ℝ) ≤ 0)
    (hDL : ∀ s t, s < b → t < b → X s t → |(D s t : ℝ)| ≤ L) (hHb : (b : ℝ) ≤ H)
    {r0 nr c1 nc ρ κ : ℕ} (hnc : nc ≤ c1) (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b) (hρ : ρ < nr)
    (hκ : κ < nc) :
    -((Xl : ℝ) + L) ≤ blkO X D H E r0 nr c1 nc ρ κ ∧
      blkO X D H E r0 nr c1 nc ρ κ ≤ L + H + b := by
  classical
  unfold blkO extA subMul subVal
  have hLn : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  have hX0 : (0 : ℝ) ≤ Xl := Nat.cast_nonneg Xl
  have hncb : (nc : ℝ) ≤ b := by exact_mod_cast hnc.trans hc1
  by_cases hF : Fb X r0 c1 (repR nr nc (Fb X r0 c1) ρ) κ
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hF), ite_eq_left_of_eq_true _ _ (eq_true hF)]
    have hrep : repR nr nc (Fb X r0 c1) ρ < nr := by
      by_cases hex : ∃ u, GRow nr nc (Fb X r0 c1) u
      · exact (repR_spec hex ρ).1.1
      · rw [repR_none hex] at hF ⊢; exact hρ
    have hD := hDL _ _ (by omega) (by omega) hF
    have hEv := hE (c1 - 1 - κ) (by omega)
    simp only [Drb, one_mul]
    rw [abs_le] at hD
    constructor <;> linarith [hD.1, hD.2, hEv.1, hEv.2]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hF), ite_eq_right_of_eq_false _ _ (eq_false hF)]
    have hw := wt_bound (n := nc) (F := Fb X r0 c1) (ρ := repR nr nc (Fb X r0 c1) ρ) hκ
    simp only [zero_mul, zero_add]
    constructor <;> linarith [hw.1, hw.2]

/-! ### The checked oracle -/

/-- The check of the entry `r70`: stop the machine (`halt` has no run) unless `|r70| ≤ B`,
then recompute the product `r82` of the oracle. -/
def chkO (B : ℕ) : Stmt :=
  .seq (.instr (.constR 82 B)) <| .seq (.ifLtR 82 70 (.instr .halt) .skip) <|
  .seq (.instr (.constR 82 (-(B : ℤ)))) <| .seq (.ifLtR 70 82 (.instr .halt) .skip) <|
  block [.loadR 82 84, .mulR 82 82 80]

/-- **The checked oracle.** -/
def entC (B : ℕ) : Stmt := .seq entO (chkO B)

/-- The marker of the oracle in the abstract interpretation: `r70` bounded by `B`, the scratch
real registers forgotten. -/
def mkO : Stmt := block [.constR 80 1, .constR 81 1, .constR 82 1, .loadR 70 0]

/-- A run of the check: the entry was bounded, and only `r82` was recomputed. -/
theorem chkO_inv {d d' : Config} {k : ℕ} (e : Exec P W (chkO B) d d' k) :
    d' = { d with rreg := upd d.rreg 82 (d.rmem (d.nreg 84) * d.rreg 80) } ∧
      |d.rreg 70| ≤ B := by
  unfold chkO at e
  cases e with
  | seq e₁ e₂ =>
    cases e₁ with
    | instr _ he _ _ =>
      simp only [Instr.effect, Option.some.injEq] at he; subst he
      cases e₂ with
      | seq e₃ e₄ =>
        cases e₃ with
        | ifLtR_true _ eh => cases eh with | instr hs => simp at hs
        | ifLtR_false h3 e₅ =>
          cases e₅
          cases e₄ with
          | seq e₆ e₇ =>
            cases e₆ with
            | instr _ he _ _ =>
              simp only [Instr.effect, Option.some.injEq] at he; subst he
              cases e₇ with
              | seq e₈ e₉ =>
                cases e₈ with
                | ifLtR_true _ eh => cases eh with | instr hs => simp at hs
                | ifLtR_false h8 e₁₀ =>
                  cases e₁₀
                  obtain ⟨h9, -⟩ := e₉.block_effs
                  simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at h9
                  subst h9
                  config_simp at h3; config_simp at h8
                  refine ⟨by config_simp, abs_le.2 ⟨by push_cast at h8; linarith,
                    by push_cast at h3; linarith⟩⟩

/-- A run of the check from a bounded entry. -/
theorem chkO_run {d : Config} (hw : WordsBounded W d) (h70 : |d.rreg 70| ≤ B) :
    ∃ d' k, Exec P W (chkO B) d d' k ∧
      d' = { d with rreg := upd d.rreg 82 (d.rmem (d.nreg 84) * d.rreg 80) } ∧ k ≤ 8 := by
  obtain ⟨h1, h2⟩ := abs_le.1 h70
  unfold chkO
  refine spec_seq ?_
  refine spec_instr (Exec.constR hw 82 B) fun hw₁ => ?_
  refine spec_seq ?_
  refine spec_ifLtR_false (by config_simp; push_cast; linarith) (spec_skip hw₁ ?_)
  refine spec_seq ?_
  refine spec_instr (Exec.constR hw₁ 82 _) fun hw₂ => ?_
  refine spec_seq ?_
  refine spec_ifLtR_false (by config_simp; push_cast; linarith) (spec_skip hw₂ ?_)
  exec_block
  refine ⟨?_, by omega⟩
  config_simp

/-- The effect of the oracle on the real registers. -/
theorem entO_eff {c d : Config} {k : ℕ} (e : Exec P W entO c d k) :
    d.rreg 82 = d.rmem (d.nreg 84) * d.rreg 80 ∧ d.rmem = c.rmem ∧
      ∀ r, r ≠ 70 → r ≠ 80 → r ≠ 81 → r ≠ 82 → d.rreg r = c.rreg r := by
  unfold entO at e
  obtain ⟨h, -⟩ := e.block_effs
  simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at h
  subst h
  refine ⟨by config_simp, by config_simp, fun r h1 h2 h3 h4 => ?_⟩
  config_simp; simp only [upd_apply]; split_ifs <;> first | rfl | omega

theorem entO_noRS : noRS entO = true := by decide

/-- **The hole of SMAWK is sound**: a run of the oracle from a configuration from which the
checked oracle runs ends with `|r70| ≤ B`, and the checked oracle ends at the same
configuration. -/
theorem holeOK_entO {m n : ℕ} : HoleOK P W B m n mkO entO (entC B) := by
  intro A A₁ hA c d k e _ hRA ⟨d', k', e'⟩
  have hA₁ : A₁ = put (put (put (put A 80 none) 81 none) 82 none) 70 (some 1) := by
    simp [mkO, absS, absI, block] at hA; exact hA.symm
  subst hA₁
  unfold entC at e'
  cases e' with
  | seq e₁ e₂ =>
    obtain ⟨rfl, rfl⟩ := Exec.det e₁ e
    obtain ⟨hd', h70⟩ := chkO_inv e₂
    obtain ⟨h82, -, hkeep⟩ := entO_eff e₁
    refine ⟨ExecG.of_noRS e₁ entO_noRS, fun r j h => ?_, ?_⟩
    · by_cases g1 : r = 70
      · subst g1; simp [get_put] at h; subst h; simpa using h70
      by_cases g2 : r = 80
      · subst g2; simp [get_put] at h
      by_cases g3 : r = 81
      · subst g3; simp [get_put] at h
      by_cases g4 : r = 82
      · subst g4; simp [get_put] at h
      simp only [get_put, g1, g2, g3, g4, ↓reduceIte] at h
      rw [hkeep r g1 g2 g3 g4]; exact hRA r j h
    · have : d' = _ := hd'
      rw [← h82, upd_eq_self] at this
      exact ⟨_, .seq e₁ (this ▸ e₂)⟩

/-- `smawk` with the oracle `entO`, the checked oracle and the marker. -/
theorem plug_smawk : Plug mkO entO (entC B) (smawk mkO) (smawk entO) (smawk (entC B)) := by
  unfold smawk downLevel upLevel reduce redCol redPop upRows upRow scanL
  repeat (first | exact Plug.hole | exact Plug.refl _ | apply Plug.seq | apply Plug.ifLtN |
    apply Plug.ifLtR | apply Plug.whileLtN | apply Plug.whileLtR)

/-- SMAWK with the marker passes the abstract interpretation. -/
theorem absS_smawk : (absS 2 4 (smawk mkO) []).isSome = true := by decide

/-- **SMAWK with bounded comparisons and stores**: at a call of a half block whose entries are
bounded by `B`, every run of `smawk entO` compares only entries and stores only entries. -/
theorem smawk_good (hL : LayO b Vb eb pb W) {E : ℕ → ℤ} {r0 nr c1 nc : ℕ} {c₀ : Config}
    (hE : EnvO b Vb eb pb X D H c₀) (hV : Vals b eb E c₀) (h24 : c₀.nreg 24 = r0)
    (h25 : c₀.nreg 25 = c1) (hnc : nc ≤ c1) (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b)
    (hsep : r0 + nr ≤ c1 - nc ∨ c1 ≤ r0)
    (hhb : ∀ ρ < nr, ∀ κ < nc, hbOf b (c1 - 1 - κ) (r0 + ρ) = (r0, nr, c1, nc))
    (hbnd : ∀ ρ < nr, ∀ κ < nc, |blkO X D H E r0 nr c1 nc ρ κ| ≤ B)
    (hTM : IsTotMono nr nc (blkO X D H E r0 nr c1 nc)) (hm : 0 < nr) (hn : 0 < nc)
    (hW : pb + 4 * nr + nc + 2 ≤ W) (hc : WordsBounded W c₀)
    (h60 : c₀.nreg 60 = nr) (h61 : c₀.nreg 61 = nc) (h62 : c₀.nreg 62 = pb) :
    Good P W B (2 * B) (smawk entO) c₀ := by
  have hent := entO_exec (P := P) hL hE hV h24 h25 hnc hc1 hr hsep hhb
  have hentC : EntSpecK P W (entC B) (blkO X D H E r0 nr c1 nc) (14 + 8) nr nc pb
      (4 * nr + nc + 1) c₀ := by
    intro c hc hA h70 h71
    obtain ⟨c', k, e, hk, h70', hn', hr', hnm', hrm', ho'⟩ := hent c hc hA h70 h71
    obtain ⟨d', k₂, e₂, rfl, hk₂⟩ := chkO_run (P := P) (B := B) e.wb_right
      (by rw [h70']; exact hbnd _ h70 _ h71)
    refine ⟨_, k + k₂, .seq e e₂, by omega, by config_simp; exact h70',
      fun r hr => by config_simp; exact hn' r hr,
      fun r hr h => by config_simp; rw [upd_other _ _ _ (by omega)]; exact hr' r hr h,
      by config_simp; exact hnm', by config_simp; exact hrm', by config_simp; exact ho'⟩
  obtain ⟨c', k, e', -⟩ := smawk_exec hentC hTM hm hn hW hc h60 h61 h62
  obtain ⟨A', hA'⟩ := Option.isSome_iff_exists.1 absS_smawk
  exact good_plug holeOK_entO plug_smawk hA' (fun _ => regA_nil _) ⟨c', k, e'⟩

/-- The effect of a step of the update on the real memory: at most the value of the target
`r3 + r24 + r26` is replaced by the row minimum at `r4 + r26 + r10`. -/
theorem updBodyO_eff {c d : Config} {k : ℕ} (e : Exec P W updBodyO c d k) (a : ℕ) :
    d.rmem a = c.rmem a ∨ (a = c.nreg 3 + (c.nreg 24 + c.nreg 26) ∧
      d.rmem a = c.rmem (c.nreg 4 + c.nreg 26 + c.nreg 10)) := by
  unfold updBodyO at e
  cases e with
  | seq e₁ e₂ =>
    obtain ⟨h1, -⟩ := e₁.block_effs
    simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at h1
    subst h1
    cases e₂ with
    | seq e₃ e₄ =>
      cases e₄ with
      | instr _ he _ _ =>
        simp only [Instr.effect, Option.some.injEq] at he; subst he
        cases e₃ with
        | ifLtN_true _ e₅ => cases e₅; left; config_simp
        | ifLtN_false _ e₅ =>
          cases e₅ with
          | ifLtR_true _ e₆ =>
            obtain ⟨h6, -⟩ := e₆.block_effs
            simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at h6
            subst h6
            config_simp
            by_cases ha : a = c.nreg 3 + (c.nreg 24 + c.nreg 26)
            · right; subst ha; refine ⟨rfl, ?_⟩; config_simp
            · left; rw [upd_other _ _ _ ha]
          | ifLtR_false _ e₆ => cases e₆; left; config_simp

theorem updBodyO_abs : (absS 2 2 updBodyO []).isSome = true := by decide

variable {Q : Prop} {lo hi : ℕ → ℤ}

/-- **A half block with bounded comparisons and stores**; it lowers the values by at most `L`. -/
theorem halfO_goodQ (hD : CrossingX b X D)
    (hH : ∀ s t, s < b → t < b → X s t → (D s t : ℝ) + b < H) (hL : LayO b Vb eb pb W)
    (hDL : ∀ s t, s < b → t < b → X s t → |(D s t : ℝ)| ≤ L) (hHb : (b : ℝ) ≤ H)
    {C : ℕ → ℕ → Prop}
    {E₀ E : ℕ → ℤ} {r0 nr c1 nc : ℕ} (c : Config) (hc : WordsBounded W c)
    (hE : EnvO b Vb eb pb X D H c) (hV : Vals b eb E c)
    (hR : RoundGX b X D Q lo hi C E₀ E (c.nreg 30))
    (h24 : c.nreg 24 = r0) (h25 : c.nreg 25 = c1) (h60 : c.nreg 60 = nr) (h61 : c.nreg 61 = nc)
    (hnr : 1 ≤ nr) (hnc : 1 ≤ nc) (hnc' : nc ≤ c1) (hc1 : c1 ≤ b) (hr : r0 + nr ≤ b)
    (hsep : r0 + nr ≤ c1 - nc ∨ c1 ≤ r0)
    (hhb : ∀ ρ < nr, ∀ κ < nc, hbOf b (c1 - 1 - κ) (r0 + ρ) = (r0, nr, c1, nc))
    {Xl : ℕ} (hlow : ELow b eb Xl c) (hB : ((Xl + L : ℕ) : ℝ) + H + b ≤ B) :
    GoodQ P W B (2 * B) halfO c (ELow b eb (Xl + L)) := by
  have hLw := hL.w
  have hpe := hL.pe
  have hed := hL.ed
  have hEb : ∀ v < b, -(Xl : ℝ) ≤ E v ∧ (E v : ℝ) ≤ 0 := fun v hv =>
    ⟨by rw [← hV v hv]; exact hlow v hv, by exact_mod_cast hR.nonpos v hv⟩
  have hBb : ∀ ρ < nr, ∀ κ < nc, |blkO X D H E r0 nr c1 nc ρ κ| ≤ B := fun ρ hρ κ hκ => by
    obtain ⟨h1, h2⟩ := blkO_bound hEb hDL hHb hnc' hc1 hr hρ hκ
    push_cast at hB
    rw [abs_le]; constructor <;> linarith
  unfold halfO
  refine goodQ_instr (Exec.copyN hc 62 4) (by decide) fun hw₁ => ?_
  have hEa : EnvO b Vb eb pb X D H { c with nreg := upd c.nreg 62 (c.nreg 4) } :=
    hE.of (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]) rfl (fun _ _ => rfl)
      (fun _ _ => rfl)
  have hTM : IsTotMono nr nc (blkO X D H E r0 nr c1 nc) :=
    blkO_totMono hD hH hR.nonpos hnc' hc1 hr hsep
  refine goodQ_use (smawk_exec (entO_exec (P := P) hL hEa hV (by config_simp; exact h24)
    (by config_simp; exact h25) hnc' hc1 hr hsep hhb) hTM (by omega) (by omega) (by omega) hw₁
    (by config_simp; exact h60) (by config_simp; exact h61)
    (by config_simp; exact hE.r4))
    (smawk_good hL hEa hV (by config_simp; exact h24) (by config_simp; exact h25) hnc' hc1 hr hsep
      hhb hBb hTM (by omega) (by omega) (by omega) hw₁ (by config_simp; exact h60)
      (by config_simp; exact h61) (by config_simp; exact hE.r4)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨⟨a1, a2, a3, a4, a5⟩, g60, g61, g62, hres⟩
  refine goodQ_instr (Exec.constN hw₂ 26 0 (by omega)) (by decide) fun hw₃ => ?_
  have n₁ : ∀ r < 60, r ≠ 26 →
      ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config).nreg r = c.nreg r :=
    fun r hr h => by
      config_simp; rw [upd_other _ _ _ h, a1 r hr]; config_simp; rw [upd_other _ _ _ (by omega)]
  have hE₁ : EnvO b Vb eb pb X D H ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config) :=
    hE.of (fun r hr => n₁ r (by omega) (by omega)) (a2 10 (by omega))
      (fun a ha => a4 a (Or.inr (by omega))) (fun a ha => a3 a (Or.inr (by omega)))
  have hV₁ : Vals b eb E ({ c₂ with nreg := upd c₂.nreg 26 0 } : Config) :=
    fun v hv => (a4 _ (Or.inr (by omega))).trans (hV v hv)
  set c₁ : Config := { c₂ with nreg := upd c₂.nreg 26 0 } with hc₁
  refine GoodQ.mono (GoodQ.whileLtN
    (fun c => IUpO b Vb eb X D W Q lo hi C E₀ E r0 nr c1 nc c₁ c ∧ ELow b eb (Xl + L) c)
    (fun c' hI hlt => ?_) ⟨⟨hw₃, fun _ _ _ _ _ _ => rfl, fun _ _ _ => rfl, rfl, fun _ _ => rfl,
      rfl, by rw [hc₁]; config_simp; omega, E, hV₁, ?_, fun _ _ _ => rfl⟩,
      fun v hv => by rw [hV₁ v hv]; exact (hEb v hv).1.trans' (by push_cast; linarith)⟩)
    fun _ h => h.2
  · obtain ⟨c'', k'', e'', hI'', -⟩ := updBodyO_exec (P := P) hH hL hE₁
      (by rw [n₁ 24 (by omega) (by omega), h24]) (by rw [n₁ 25 (by omega) (by omega), h25])
      (by rw [hc₁]; config_simp; rw [g60]) hnc hnc' hc1 hr hsep hR.nonpos (fun ρ hρ =>
        ⟨by rw [hc₁]; config_simp; exact (hres ρ hρ).1,
          by rw [hc₁]; config_simp; exact (hres ρ hρ).2⟩) c' hI.1 hlt
    refine ⟨good_abs' (m := 2) (n := 2) (A := []) updBodyO_abs (fun _ => regA_nil _),
      fun c₃ k₃ e₃ => ?_⟩
    obtain ⟨rfl, rfl⟩ := Exec.det e'' e₃
    refine ⟨hI'', fun v hv => ?_⟩
    have g : ∀ r, r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → c'.nreg r = c₁.nreg r := hI.1.nreg
    have g3 : c'.nreg 3 = eb :=
      (g 3 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r3
    have g4 : c'.nreg 4 = pb :=
      (g 4 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r4
    have g10 : c'.nreg 10 = 1 :=
      (g 10 (by omega) (by omega) (by omega) (by omega) (by omega)).trans hE₁.r10
    have g24 : c'.nreg 24 = r0 :=
      (g 24 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (by rw [n₁ 24 (by omega) (by omega), h24])
    have g60' : c'.nreg 60 = nr :=
      (g 60 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (by rw [hc₁]; config_simp; rw [g60])
    rw [g60'] at hlt
    rcases updBodyO_eff e'' (eb + v) with h | ⟨ha, h⟩
    · rw [h]; exact hI.2 v hv
    · rw [h, g4, g10]
      have hmin := (hres (c'.nreg 26) hlt).2
      rw [hI.1.rmem _ (Or.inl (by omega))]
      rw [hc₁]; config_simp
      rw [hmin]
      exact (blkO_bound hEb hDL hHb hnc' hc1 hr hlt (lmin_lt _ _ (by omega))).1.trans'
        (by push_cast; linarith)
  · rw [n₁ 30 (by omega) (by omega)]
    refine hR.mono fun i j _ _ _ _ hc => ?_
    rcases hc with hc | ⟨-, -, h3, h4⟩
    · exact hc
    · rw [hc₁] at h4; config_simp at h4; omega

/-! ### A block, a level, the levels of a matrix -/

/-- **A block with bounded comparisons and stores**; it lowers the values by at most `2 L` and
advances the block base by `2 s`. -/
theorem blockBodyO_goodQ (hD : CrossingX b X D)
    (hH : ∀ s t, s < b → t < b → X s t → (D s t : ℝ) + b < H) (hL : LayO b Vb eb pb W)
    (hDL : ∀ s t, s < b → t < b → X s t → |(D s t : ℝ)| ≤ L) (hHb : (b : ℝ) ≤ H)
    {E₀ : ℕ → ℤ} {s : ℕ}
    {c₀ : Config} (hs : 1 ≤ s) {T : ℕ} (hT : s = 2 ^ T) (hsb : s < b) (c : Config)
    (hI : IBO b Vb eb pb X D H W Q lo hi E₀ s c₀ c) (hlt : c.nreg 22 < c.nreg 1)
    {Xl : ℕ} (hlow : ELow b eb Xl c) (hB : ((Xl + 2 * L : ℕ) : ℝ) + H + b ≤ B) :
    GoodQ P W B (2 * B) blockBodyO c
      (fun c' => ELow b eb (Xl + 2 * L) c' ∧ c'.nreg 21 = c.nreg 21 + 2 * s) := by
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
  have hB1 : ((Xl + L : ℕ) : ℝ) + H + b ≤ B := by push_cast at hB ⊢; linarith [(Nat.cast_nonneg L : (0:ℝ) ≤ L)]
  have hB2 : ((Xl + L + L : ℕ) : ℝ) + H + b ≤ B := by push_cast at hB ⊢; linarith
  unfold blockBodyO
  refine goodQ_instr (Exec.addN hc 23 22 20 (by rw [g22, g20]; omega)) (by decide) fun hw₁ => ?_
  refine goodQ_use (minS_exec _ hw₁) (good_noRS (by decide) _) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨h23, hn₂, hr₂, hnm₂, hrm₂, ho₂⟩
  config_simp at h23
  rw [g22, g20, hE.r1] at h23
  generalize hrend : min (base + s + s) b = rend at h23
  have hrend1 : base + s < rend := by rw [← hrend]; omega
  have hrend2 : rend ≤ b := by rw [← hrend]; omega
  have hrend3 : rend ≤ base + 2 * s := by rw [← hrend]; omega
  have e₂ : ∀ r, r ≠ 23 → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hn₂ r hr]; config_simp; rw [upd_other _ _ _ hr]
  have hE₂ : EnvO b Vb eb pb X D H c₂ :=
    hE.of (fun r hr => e₂ r (by omega)) (by rw [hr₂]) (fun a _ => by rw [hrm₂])
      (fun a _ => by rw [hnm₂])
  -- the first half
  refine goodQ_ex (good_noRS (by decide) _) ?_
  exec_block
  have hwX := ‹WordsBounded W (Config.mk _ _ _ _ _ _)›
  generalize hcX : (Config.mk _ _ _ _ _ _ : Config) = cX at hwX ⊢
  have hEX : EnvO b Vb eb pb X D H cX := by
    rw [← hcX]; exact hE₂.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl)
      (fun _ _ => rfl)
  have hVX : Vals b eb E cX := fun v hv => by rw [← hcX]; config_simp; rw [hrm₂]; exact hV v hv
  have hRX : RoundGX b X D Q lo hi (Cov s base) E₀ E (cX.nreg 30) := by
    rw [← hcX]; config_simp; rw [e₂ 30 (by omega)]; exact hR
  have x24 : cX.nreg 24 = base + s := by rw [← hcX]; config_simp; rw [e₂ 22 (by omega), g22]
  have x25 : cX.nreg 25 = base + s := by rw [← hcX]; config_simp; rw [e₂ 22 (by omega), g22]
  have x60 : cX.nreg 60 = rend - (base + s) := by
    rw [← hcX]; config_simp; rw [h23, e₂ 22 (by omega), g22]
  have x61 : cX.nreg 61 = s := by rw [← hcX]; config_simp; rw [e₂ 20 (by omega), g20]
  have hlowX : ELow b eb Xl cX := hlow.of fun v hv => by rw [← hcX]; config_simp; rw [hrm₂]
  have hhbX : ∀ ρ < rend - (base + s), ∀ κ < s,
      hbOf b (base + s - 1 - κ) (base + s + ρ) = (base + s, rend - (base + s), base + s, s) :=
    fun ρ hρ κ hκ => by
      have := hbOf_first (b := b) hT hq (s := base + s - 1 - κ) (t := base + s + ρ) (by omega)
        (by omega) (by omega) (by rw [hrend]; omega)
      rwa [hrend] at this
  refine goodQ_useQ (halfO_exec (P := P) hD hH hL cX hwX hEX hVX hRX x24 x25 x60 x61
    (by omega) hs (by omega) (by omega) (by omega) (Or.inr le_rfl) hhbX)
    (halfO_goodQ (P := P) hD hH hL hDL hHb cX hwX hEX hVX hRX x24 x25 x60 x61
    (by omega) hs (by omega) (by omega) (by omega) (Or.inr le_rfl) hhbX hlowX hB1) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hE₃, ⟨E₃, hV₃, hR₃⟩, hn₃, hr₃, ho₃, hnm₃, hrm₃⟩ hlow₃
  have e₃ : ∀ r < 60, r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
      c₃.nreg r = c.nreg r := fun r hr a1 a2 a3 a4 a5 a6 a7 a8 => by
    rw [hn₃ r hr a4 a5 a6 a7 a8, ← hcX]; config_simp
    simp only [upd_apply]; split_ifs <;> first | omega | exact e₂ r a1
  have g23₃ : c₃.nreg 23 = rend := by
    rw [hn₃ 23 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), ← hcX]
    config_simp; exact h23
  -- the second half
  refine goodQ_ex (good_noRS (by decide) _) ?_
  exec_block
  have hwY := ‹WordsBounded W (Config.mk _ _ _ _ _ _)›
  generalize hcY : (Config.mk _ _ _ _ _ _ : Config) = cY at hwY ⊢
  have hEY : EnvO b Vb eb pb X D H cY := by
    rw [← hcY]; exact hE₃.of (fun r hr => by config_simp; upd_tac) rfl (fun _ _ => rfl)
      (fun _ _ => rfl)
  have hVY : Vals b eb E₃ cY := fun v hv => by rw [← hcY]; config_simp; exact hV₃ v hv
  have hRY : RoundGX b X D Q lo hi (fun i j => Cov s base i j ∨
      HalfArcs (base + s) (base + s) s (rend - (base + s)) i j) E₀ E₃ (cY.nreg 30) := by
    rw [← hcY]; config_simp; exact hR₃
  have y24 : cY.nreg 24 = base := by
    rw [← hcY]; config_simp; rw [e₃ 21 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), hbase]
  have y25 : cY.nreg 25 = rend := by rw [← hcY]; config_simp; exact g23₃
  have y60 : cY.nreg 60 = s := by
    rw [← hcY]; config_simp; rw [e₃ 20 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), g20]
  have y61 : cY.nreg 61 = rend - (base + s) := by
    rw [← hcY]; config_simp; rw [g23₃, e₃ 22 (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), g22]
  have hlowY : ELow b eb (Xl + L) cY := hlow₃.of fun v hv => by rw [← hcY]
  have hhbY : ∀ ρ < s, ∀ κ < rend - (base + s),
      hbOf b (rend - 1 - κ) (base + ρ) = (base, s, rend, rend - (base + s)) :=
    fun ρ hρ κ hκ => by
      have := hbOf_second (b := b) hT hq (s := rend - 1 - κ) (t := base + ρ) (by omega)
        (by omega) (by omega) (by rw [hrend]; omega)
      rwa [hrend] at this
  refine goodQ_useQ (halfO_exec (P := P) hD hH hL cY hwY hEY hVY hRY y24 y25 y60 y61
    hs (by omega) (by omega) hrend2 (by omega) (Or.inl (by omega)) hhbY)
    (halfO_goodQ (P := P) hD hH hL hDL hHb cY hwY hEY hVY hRY y24 y25 y60 y61
    hs (by omega) (by omega) hrend2 (by omega) (Or.inl (by omega)) hhbY hlowY hB2) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨hE₄, ⟨E₄, hV₄, hR₄⟩, hn₄, hr₄, ho₄, hnm₄, hrm₄⟩ hlow₄
  have e₄ : ∀ r < 60, r ≠ 23 → r ≠ 24 → r ≠ 25 → r ≠ 26 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 →
      r ≠ 60 → r ≠ 61 → c₄.nreg r = c.nreg r := fun r hr a1 a2 a3 a4 a5 a6 a7 a8 _ _ => by
    rw [hn₄ r hr a4 a5 a6 a7 a8, ← hcY]; config_simp
    simp only [upd_apply]; split_ifs <;> first | omega | exact e₃ r hr a1 a2 a3 a4 a5 a6 a7 a8
  have g20₄ : c₄.nreg 20 = s := by
    rw [e₄ 20 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), g20]
  have g21₄ : c₄.nreg 21 = base := by
    rw [e₄ 21 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega), hbase]
  refine GoodQ.noRS (by decide) fun c' k ex => ?_
  have hm := ex.rmem_keep (by decide)
  obtain ⟨h1, -⟩ := ex.block_effs
  simp only [blockEffs, Instr.effect, Option.bind_some, Option.some.injEq] at h1
  subst h1
  refine ⟨(hlow₄.of fun v hv => by rw [hm]).mono (by omega), ?_⟩
  config_simp; rw [g21₄, g20₄]; ring

/-- **A level with bounded comparisons and stores**; it lowers the values by at most `2 b L`
and doubles the level. -/
theorem levelBFO_goodQ (hD : CrossingX b X D)
    (hH : ∀ s t, s < b → t < b → X s t → (D s t : ℝ) + b < H) (hL : LayO b Vb eb pb W)
    (hDL : ∀ s t, s < b → t < b → X s t → |(D s t : ℝ)| ≤ L) (hHb : (b : ℝ) ≤ H)
    {E₀ : ℕ → ℤ} {c₀ : Config} (c : Config) (hI : ILO b Vb eb pb X D H W Q lo hi E₀ c₀ c)
    (hlt : c.nreg 20 < c.nreg 1) {Xl : ℕ} (hlow : ELow b eb Xl c)
    (hB : ((Xl + 2 * b * L : ℕ) : ℝ) + H + b ≤ B) :
    GoodQ P W B (2 * B) levelBFO c
      (fun c' => ELow b eb (Xl + 2 * b * L) c' ∧ c'.nreg 20 = 2 * c.nreg 20) := by
  have hc := hI.wb
  have hE := hI.env
  have hLw := hL.w
  rw [hE.r1] at hlt
  obtain ⟨t, ht⟩ := hI.pow
  generalize hs : c.nreg 20 = s at ht hlt
  have hs1 : 1 ≤ s := by rw [ht]; exact Nat.one_le_two_pow
  obtain ⟨E, hV, hR⟩ := hI.vals
  rw [hs] at hR
  unfold levelBFO
  refine goodQ_ex (good_noRS (by decide) _) ?_
  exec_block
  · omega
  refine GoodQ.seqQ (GoodQ.whileLtN (fun c => IBO b Vb eb pb X D H W Q lo hi E₀ s c₀ c ∧
      ELow b eb (Xl + L * c.nreg 21) c) (fun c' hI' hlt' => ?_) ⟨⟨‹_›, hE.of (fun r hr => by
        config_simp; upd_tac) rfl (fun _ _ => rfl) (fun _ _ => rfl),
      hI.frm.trans (Frm.of_regs (fun r hr h => by config_simp; upd_tac) rfl rfl rfl rfl),
      by config_simp; exact hs,
      ⟨0, by config_simp; ring⟩, by config_simp; rw [hs], by config_simp; omega,
      ⟨E, hV, by config_simp; exact hR⟩⟩,
      by config_simp; exact (hlow.of fun v hv => by config_simp).mono (by simp)⟩) ?_
  · -- a block
    have hb21 : c'.nreg 21 + s < b := by
      have := hI'.1.r22; rw [hI'.1.env.r1] at hlt'; omega
    have hle : Xl + L * c'.nreg 21 + 2 * L ≤ Xl + 2 * b * L := by
      nlinarith [Nat.mul_le_mul_left L (show c'.nreg 21 + 2 ≤ 2 * b by omega)]
    obtain ⟨c'', k'', e'', hI'', -⟩ := blockBodyO_exec (P := P) hD hH hL hs1 ht hlt c' hI'.1 hlt'
    refine ((blockBodyO_goodQ (P := P) hD hH hL hDL hHb hs1 ht hlt c' hI'.1 hlt' hI'.2 ?_).and_run
      ⟨c'', k'', e'', hI''⟩).mono fun c₂ ⟨h1, h2, h3⟩ => ⟨h1, h2.mono ?_⟩
    · have := (Nat.cast_le (α := ℝ)).2 hle
      push_cast at this hB ⊢; linarith
    · rw [h3]; nlinarith [Nat.mul_le_mul_left L (show 2 ≤ 2 * s by omega)]
  · intro c₂ k₂ _ ⟨hI₂, hlow₂⟩
    have hle : Xl + L * c₂.nreg 21 ≤ Xl + 2 * b * L := by
      nlinarith [Nat.mul_le_mul_left L (show c₂.nreg 21 ≤ 2 * b by have := hI₂.basele; omega)]
    refine GoodQ.noRS (by decide) fun c' k ex => ?_
    cases ex with
    | instr _ he _ _ =>
      simp only [Instr.effect, Option.some.injEq] at he; subst he
      exact ⟨(hlow₂.of fun v hv => by config_simp).mono hle, by config_simp; rw [hI₂.r20]; ring⟩

/-- **The levels of a matrix with bounded comparisons and stores** (`levelsO_exec`); they
lower the values by at most `bfΔ b L = 2 b L (2 b + 1)`. -/
theorem levelsO_goodQ (hD : CrossingX b X D)
    (hH : ∀ s t, s < b → t < b → X s t → (D s t : ℝ) + b < H) (hL : LayO b Vb eb pb W)
    (hDL : ∀ s t, s < b → t < b → X s t → |(D s t : ℝ)| ≤ L) (hHb : (b : ℝ) ≤ H)
    {E : ℕ → ℤ} (c : Config)
    (hc : WordsBounded W c) (hE : EnvO b Vb eb pb X D H c) (hV : Vals b eb E c)
    (h20 : c.nreg 20 = 1) (h30 : c.nreg 30 = 0)
    (htop : ∀ v < b, E v ≤ 0)
    (hpot : Q → ∀ i j, i < b → j < b → i ≠ j → X i j → lo j ≤ lo i + D i j)
    (hS : Q → ∀ v < b, lo v ≤ E v ∧ E v ≤ hi v) {X₀ : ℕ} (hlow : ELow b eb X₀ c)
    (hB : ((X₀ + 2 * b * L * (2 * b + 1) : ℕ) : ℝ) + H + b ≤ B) :
    GoodQ P W B (2 * B) (.whileLtN 20 1 levelBFO) c (ELow b eb (X₀ + 2 * b * L * (2 * b + 1))) := by
  refine (GoodQ.whileLtN (fun c' => ILO b Vb eb pb X D H W Q lo hi E c c' ∧
      ELow b eb (X₀ + 2 * b * L * c'.nreg 20) c') (fun c' hI hlt => ?_)
    ⟨⟨hc, hE, Frm.refl _ _ _ _, ⟨0, by rw [h20]; rfl⟩, by rw [h20]; omega,
      ⟨E, hV, by
        rw [h20, h30]
        exact (RoundGX.start htop hpot hS).mono fun i j _ _ _ _ hc => not_cov_one_zero hc⟩⟩,
      hlow.mono (by omega)⟩).mono fun c' ⟨hI, hl⟩ => hl.mono ?_
  · have hs := hI.1.sle
    have hsb : c'.nreg 20 < b := by rw [hI.1.env.r1] at hlt; exact hlt
    have hle : X₀ + 2 * b * L * c'.nreg 20 + 2 * b * L ≤ X₀ + 2 * b * L * (2 * b + 1) := by
      nlinarith [Nat.mul_le_mul_left (2 * b * L) (show c'.nreg 20 + 1 ≤ 2 * b + 1 by omega)]
    obtain ⟨c'', k'', e'', hI'', -⟩ := levelBFO_exec (P := P) hD hH hL c' hI.1 hlt
    refine ((levelBFO_goodQ (P := P) hD hH hL hDL hHb c' hI.1 hlt hI.2 ?_).and_run
      ⟨c'', k'', e'', hI''⟩).mono fun c₂ ⟨h1, h2, h3⟩ => ⟨h1, h2.mono ?_⟩
    · have := (Nat.cast_le (α := ℝ)).2 hle
      push_cast at this hB ⊢; linarith
    · have h1 : 1 ≤ c'.nreg 20 := by obtain ⟨t, ht⟩ := hI.1.pow; rw [ht]; exact Nat.one_le_two_pow
      rw [h3]; nlinarith [Nat.mul_le_mul_left (2 * b * L) h1]
  · nlinarith [Nat.mul_le_mul_left (2 * b * L) hI.sle]

/-! ### A round, the whole run -/

/-- The lowering of the values by the levels of one matrix. -/
def bfΔ (b L : ℕ) : ℕ := 2 * b * L * (2 * b + 1)

/-- The lower bound of the values along the whole run (`b + 1` rounds). -/
def bfXm (b L : ℕ) : ℕ := 2 * bfΔ b L * (b + 1)

section Round

variable {π : ℕ → ℕ} {X₁ X₂ : ℕ → ℕ → Prop} {D₁ D₂ : ℕ → ℕ → ℤ} {H₁ H₂ : ℝ}
  {Vb₁ Vb₂ eb₂ πb : ℕ}

/-- **A round with bounded comparisons and stores**; it lowers the values by at most
`2 bfΔ b L` and advances the round counter. -/
theorem round2O_goodQ (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁) (hD₂ : CrossingX b X₂ D₂)
    (hH₁ : ∀ s t, s < b → t < b → X₁ s t → (D₁ s t : ℝ) + b < H₁)
    (hH₂ : ∀ s t, s < b → t < b → X₂ s t → (D₂ s t : ℝ) + b < H₂)
    (hDL₁ : ∀ s t, s < b → t < b → X₁ s t → |(D₁ s t : ℝ)| ≤ L)
    (hDL₂ : ∀ s t, s < b → t < b → X₂ s t → |(D₂ s t : ℝ)| ≤ L)
    (hHb₁ : (b : ℝ) ≤ H₁) (hHb₂ : (b : ℝ) ≤ H₂)
    (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) {c₀ : Config} (c : Config)
    (hI : IK2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π W c₀ c) (hlt : c.nreg 14 < c.nreg 15)
    {Xr : ℕ} (hlow : ELow b eb Xr c) (hB₁ : ((Xr + 2 * bfΔ b L : ℕ) : ℝ) + H₁ + b ≤ B)
    (hB₂ : ((Xr + 2 * bfΔ b L : ℕ) : ℝ) + H₂ + b ≤ B) :
    GoodQ P W B (2 * B) round2O c
      (fun c' => ELow b eb (Xr + 2 * bfΔ b L) c' ∧ c'.nreg 14 = c.nreg 14 + 1) := by
  have hc := hI.wb
  have hE := hI.env
  have hl₁ := hL.lay₁
  have hl₂ := hL.lay₂
  have hpe := hL.pe
  have hee := hL.ee
  have hed := hL.ed
  have hdd := hL.dd
  have hw := hL.w
  have hpp := hL.pp
  have hpw := hL.pw
  have hB₁' : ((Xr + 2 * b * L * (2 * b + 1) : ℕ) : ℝ) + H₁ + b ≤ B := by
    have hle : Xr + 2 * b * L * (2 * b + 1) ≤ Xr + 2 * bfΔ b L :=
      Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by norm_num)) _
    have := (Nat.cast_le (α := ℝ)).2 hle
    linarith
  have hB₂' : ((Xr + 2 * b * L * (2 * b + 1) + 2 * b * L * (2 * b + 1) : ℕ) : ℝ) + H₂ + b ≤ B := by
    have e : ((Xr + 2 * b * L * (2 * b + 1) + 2 * b * L * (2 * b + 1) : ℕ) : ℝ) =
        ((Xr + 2 * bfΔ b L : ℕ) : ℝ) := by unfold bfΔ; push_cast; ring
    rw [e]; exact hB₂
  rw [hE.r15] at hlt
  generalize hk : c.nreg 14 = k at hlt
  obtain ⟨E, hV, hE0, hB, -, -⟩ := hI.vals
  rw [hk] at hB
  have hK : KeepO b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π k c₀ c := ⟨hE, hk, hI.out⟩
  unfold round2O
  -- phase 1
  refine goodQ_use (start1_exec c hc (by omega)) (good_noRS (by decide) _) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a30, a2, a3, a20, an, ar, anm, arm, ao⟩
  have hK₁ := hK.of hL (fun r hr h2 h3 => an r h2 h3 (by omega) (by omega)) (by rw [ar])
    (fun a _ => by rw [arm]) (fun a _ => by rw [anm]) ao
  refine goodQ_useQ (levelsO_exec (P := P) hD₁ hH₁ hl₁ (Q := HasPot2O b X₁ D₁ X₂ D₂ π)
    (lo := bfuO b X₁ D₁ X₂ D₂ π b) (hi := bfuO b X₁ D₁ X₂ D₂ π k) c₁ hw₁
    (hK₁.env.env₁ (by rw [a2, hE.r5]) (by rw [a3, hE.r6]))
    (fun v hv => by rw [arm]; exact hV v hv)
    a20 a30 hE0 (fun hP i j hi hj hij hx => (bfuO_feas hπ hP i j hi hj hij).1 hx) hB)
    (levelsO_goodQ (P := P) hD₁ hH₁ hl₁ hDL₁ hHb₁ (Q := HasPot2O b X₁ D₁ X₂ D₂ π)
    (lo := bfuO b X₁ D₁ X₂ D₂ π b) (hi := bfuO b X₁ D₁ X₂ D₂ π k) c₁ hw₁
    (hK₁.env.env₁ (by rw [a2, hE.r5]) (by rw [a3, hE.r6]))
    (fun v hv => by rw [arm]; exact hV v hv)
    a20 a30 hE0 (fun hP i j hi hj hij hx => (bfuO_feas hπ hP i j hi hj hij).1 hx) hB
    (hlow.of fun v hv => by rw [arm]) hB₁') ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hF₂, _, E₁, hV₁, hR₁⟩ hlow₂
  have hK₂ := hK₁.ofFrm hL (by omega) hF₂
  -- the copy to `e₂`
  refine goodQ_use (mid_exec c₂ hw₂) (good_noRS (by decide) _) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨b31, b30, b16, bn, br, bnm, brm, bo⟩
  have hK₃ := hK₂.of hL (fun r hr _ _ => bn r (by omega) (by omega) (by omega)) (by rw [br])
    (fun a _ => by rw [brm]) (fun a _ => by rw [bnm]) bo
  refine goodQ_use (cpToO_exec (P := P) hπ hL (E := E₁) c₃ hw₃ hK₃.env
    (fun v hv => by rw [brm]; exact hV₁ v hv) b16)
    (good_abs' (m := 2) (n := 2) (A := []) (by decide) fun _ => regA_nil _) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨cn, cr, cnm, crm, co, cV⟩
  have hK₄ := hK₃.of hL (fun r hr _ _ => cn r (by omega) (by omega) (by omega))
    (cr 10 (by omega)) (fun a ha => crm a (Or.inr (by omega))) (fun a _ => by rw [cnm]) co
  have hlow₄ : ELow b eb₂ (Xr + 2 * b * L * (2 * b + 1)) c₄ := fun v hv => by
    rw [cV v hv, ← hV₁ _ (hπ.lt v hv)]; exact hlow₂ _ (hπ.lt v hv)
  -- phase 2
  refine goodQ_use (start2_exec c₄ hw₄ (by omega)) (good_noRS (by decide) _) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨d2, d3, d20, dn, dr, dnm, drm, d_o⟩
  have hK₅ := hK₄.of hL (fun r hr h2 h3 => dn r h2 h3 (by omega)) (by rw [dr])
    (fun a _ => by rw [drm]) (fun a _ => by rw [dnm]) d_o
  have hS₂ : HasPot2O b X₁ D₁ X₂ D₂ π → ∀ v < b,
      bfuO b X₁ D₁ X₂ D₂ π b (π v) ≤ E₁ (π v) ∧ E₁ (π v) ≤ bfuO b X₁ D₁ X₂ D₂ π k (π v) :=
    fun hP v hv =>
    ⟨((hR₁.bf hP).1 (π v) (hπ.lt v hv)).1,
      (hR₁.le _ (hπ.lt v hv)).trans ((hR₁.bf hP).1 (π v) (hπ.lt v hv)).2⟩
  refine goodQ_useQ (levelsO_exec (P := P) hD₂ hH₂ hl₂ (Q := HasPot2O b X₁ D₁ X₂ D₂ π)
    (lo := fun v => bfuO b X₁ D₁ X₂ D₂ π b (π v)) (hi := fun v => bfuO b X₁ D₁ X₂ D₂ π k (π v))
    c₅ hw₅
    (hK₅.env.env₂ (by rw [d2, hK₄.env.r7]) (by rw [d3, hK₄.env.r8]))
    (fun v hv => by rw [drm]; exact cV v hv) d20
    (by rw [dn 30 (by omega) (by omega) (by omega), cn 30 (by omega) (by omega) (by omega), b30])
    (fun v hv => hR₁.nonpos _ (hπ.lt v hv))
    (fun hP i j hi hj hij hx => (bfuO_feas hπ hP i j hi hj hij).2 hx) hS₂)
    (levelsO_goodQ (P := P) hD₂ hH₂ hl₂ hDL₂ hHb₂ (Q := HasPot2O b X₁ D₁ X₂ D₂ π)
    (lo := fun v => bfuO b X₁ D₁ X₂ D₂ π b (π v)) (hi := fun v => bfuO b X₁ D₁ X₂ D₂ π k (π v))
    c₅ hw₅
    (hK₅.env.env₂ (by rw [d2, hK₄.env.r7]) (by rw [d3, hK₄.env.r8]))
    (fun v hv => by rw [drm]; exact cV v hv) d20
    (by rw [dn 30 (by omega) (by omega) (by omega), cn 30 (by omega) (by omega) (by omega), b30])
    (fun v hv => hR₁.nonpos _ (hπ.lt v hv))
    (fun hP i j hi hj hij hx => (bfuO_feas hπ hP i j hi hj hij).2 hx) hS₂
    (hlow₄.of fun v hv => by rw [drm]) hB₂') ?_
  intro c₆ k₆ hk₆ hw₆ ⟨hF₆, _, E₂, hV₂, hR₂⟩ hlow₆
  have hK₆ := hK₅.ofFrm hL (by omega) hF₆
  -- the copy back
  refine goodQ_instr (Exec.constN hw₆ 16 0 (by omega)) (by decide) fun hw₇ => ?_
  have hK₇ : KeepO b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π k c₀
      { c₆ with nreg := upd c₆.nreg 16 0 } :=
    hK₆.of hL (fun r hr _ _ => by config_simp; upd_tac) rfl (fun _ _ => rfl) (fun _ _ => rfl) rfl
  refine goodQ_use (cpBackO_exec (P := P) hπ hL (E₂ := E₂) _ hw₇ hK₇.env
    (fun v hv => by config_simp; exact hV₂ v hv) (by config_simp))
    (good_abs' (m := 2) (n := 2) (A := []) (by decide) fun _ => regA_nil _) ?_
  intro c₈ k₈ hk₈ hw₈ ⟨en, er, enm, erm, eo, eV⟩
  have hK₈ := hK₇.of hL (fun r hr _ _ => en r (by omega) (by omega) (by omega))
    (er 10 (by omega)) (fun a ha => erm a (Or.inr (by omega))) (fun a _ => by rw [enm]) eo
  have hlow₈ : ELow b eb (Xr + 2 * bfΔ b L) c₈ := fun v hv => by
    obtain ⟨i, hi, rfl⟩ := hπ.surj hv
    rw [eV i hi, ← hV₂ i hi]
    have := hlow₆ i hi
    unfold bfΔ; push_cast at this ⊢; linarith
  -- the flag
  refine goodQ_use (flag_exec c₈ hw₈) (good_noRS (by decide) _) ?_
  intro c₉ k₉ hk₉ hw₉ ⟨hfl, fn, fr, fnm, frm, fo⟩
  have g14 : c₉.nreg 14 = k := by rw [fn 14 (by omega)]; exact hK₈.r14
  have g10 : c₉.nreg 10 = 1 := by rw [fn 10 (by omega)]; exact hK₈.env.r10
  refine GoodQ.noRS (by decide) fun c' k' ex => ?_
  cases ex with
  | instr _ he _ _ =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    exact ⟨hlow₈.of fun v hv => by config_simp; rw [frm], by config_simp; rw [g14, g10]⟩

theorem initLoop_abs : (absS 2 2 (.whileLtN 12 1 initBody) [(10, 0)]).isSome = true := by decide

/-- **Bellman–Ford over the union with bounded comparisons and stores.** From the configuration
of `bfDDG2O_exec`, with the lengths bounded by `L`, the bounds of the tables at least `b` and
`bfXm b L + Hᵢ + b ≤ B`, every run of `bfDDG2O` started with the real memory bounded by `B`
compares only reals differing by at most `2 B` and stores only reals bounded by `B`. -/
theorem bfDDG2O_good (hπ : IsPermB b π) (hD₁ : CrossingX b X₁ D₁) (hD₂ : CrossingX b X₂ D₂)
    (hH₁ : ∀ s t, s < b → t < b → X₁ s t → (D₁ s t : ℝ) + b < H₁)
    (hH₂ : ∀ s t, s < b → t < b → X₂ s t → (D₂ s t : ℝ) + b < H₂)
    (hDL₁ : ∀ s t, s < b → t < b → X₁ s t → |(D₁ s t : ℝ)| ≤ L)
    (hDL₂ : ∀ s t, s < b → t < b → X₂ s t → |(D₂ s t : ℝ)| ≤ L)
    (hHb₁ : (b : ℝ) ≤ H₁) (hHb₂ : (b : ℝ) ≤ H₂)
    (hB₁ : ((bfXm b L : ℕ) : ℝ) + H₁ + b ≤ B) (hB₂ : ((bfXm b L : ℕ) : ℝ) + H₂ + b ≤ B)
    (hL : Lay2O b Vb₁ eb Vb₂ eb₂ πb pb W) (c : Config) (hc : WordsBounded W c)
    (h1 : c.nreg 1 = b) (h2 : c.nreg 2 = Vb₁) (h3 : c.nreg 3 = eb) (h4 : c.nreg 4 = pb)
    (h7 : c.nreg 7 = Vb₂) (h8 : c.nreg 8 = eb₂) (h9 : c.nreg 9 = πb)
    (hT₁ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₁ + 2 * (s * b + t)) = tVal b X₁ D₁ H₁ s t)
    (hM₁ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₁ + 2 * (s * b + t) + 1) = tMul b X₁ s t)
    (hF₁ : ∀ s t, s < b → t < b → s ≠ t → c.nmem (Vb₁ + 2 * (s * b + t)) = finB X₁ s t)
    (hT₂ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₂ + 2 * (s * b + t)) = tVal b X₂ D₂ H₂ s t)
    (hM₂ : ∀ s t, s < b → t < b → s ≠ t → c.rmem (Vb₂ + 2 * (s * b + t) + 1) = tMul b X₂ s t)
    (hF₂ : ∀ s t, s < b → t < b → s ≠ t → c.nmem (Vb₂ + 2 * (s * b + t)) = finB X₂ s t)
    (hπm : ∀ i < b, c.nmem (πb + i) = π i) :
    Good P W B (2 * B) bfDDG2O c := by
  have hw := hL.w
  unfold bfDDG2O
  refine (goodQ_ex (Q := fun _ => True) (good_noRS (by decide) _) ?_).1
  exec_block
  · omega
  · omega
  · config_simp; rw [h1]; omega
  · omega
  · omega
  have hwX := ‹WordsBounded W (Config.mk _ _ _ _ _ _)›
  generalize hcX : (Config.mk _ _ _ _ _ _ : Config) = cX at hwX ⊢
  have hII : II2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π W c cX := by
    rw [← hcX]
    exact ⟨by rw [hcX]; exact hwX, ⟨by config_simp; exact h1, by config_simp; exact h4,
      by config_simp; exact h2,
      by config_simp; exact h3, by config_simp; exact h7, by config_simp; exact h8,
      by config_simp; exact h9, by config_simp, by config_simp; rw [h1], by config_simp; simp,
      fun s t hs ht hst => by config_simp; exact hT₁ s t hs ht hst,
      fun s t hs ht hst => by config_simp; exact hM₁ s t hs ht hst,
      fun s t hs ht hst => by config_simp; exact hF₁ s t hs ht hst,
      fun s t hs ht hst => by config_simp; exact hT₂ s t hs ht hst,
      fun s t hs ht hst => by config_simp; exact hM₂ s t hs ht hst,
      fun s t hs ht hst => by config_simp; exact hF₂ s t hs ht hst,
      fun i hi => by config_simp; exact hπm i hi⟩,
      by config_simp; exact h3, by config_simp; omega, by config_simp, by config_simp,
      fun v hv => by config_simp at hv; omega, rfl⟩
  have hz : cX.rreg 10 = 0 := by rw [← hcX]; config_simp; simp
  refine goodQ_use (spec_while (Q := fun c' k => k ≤ 5 * b + 2 ∧
      (II2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π W c c' ∧ c'.nreg 12 = b))
    (II2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π W c)
    (fun c => 5 * (b - c.nreg 12))
    (fun c h => h.wb) (fun c' hc' hlt' => initBody2O_exec hL c' hc' hlt') hII
    (fun c₁ k₁ hI₁ hn₁ hk₁ => ⟨by have := Nat.sub_le b (cX.nreg 12); omega, hI₁,
      by have := hI₁.r12; rw [hI₁.env.r1] at hn₁; omega⟩))
    (good_abs' (m := 2) (n := 2) initLoop_abs fun _ r j h => by
      change (if (10 : ℕ) = r then some 0 else CmpAbs.get [] r) = some j at h
      split_ifs at h with hr
      · simp only [Option.some.injEq] at h; subst hr h; simp [hz]
      · simp [CmpAbs.get] at h) ?_
  intro c₁ k₁ _ _ ⟨hI₁, h12⟩
  refine (GoodQ.whileLtN (fun c' => IK2O b Vb₁ eb Vb₂ eb₂ πb pb X₁ D₁ H₁ X₂ D₂ H₂ π W c c' ∧
      ELow b eb (2 * bfΔ b L * c'.nreg 14) c') (fun c' hI hlt => ?_)
    ⟨⟨hI₁.wb, hI₁.env, by rw [hI₁.r14]; omega, by rw [hI₁.r30]; omega,
      ⟨fun _ => 0, fun v hv => by rw [hI₁.zero v (by omega)]; simp, fun _ _ => le_rfl,
        fun hP v hv => ?_,
        fun h => by rw [hI₁.r14] at h; omega, fun h => by rw [hI₁.r14] at h; omega⟩,
      hI₁.out⟩, fun v hv => by rw [hI₁.r14, hI₁.zero v (by omega)]; simp⟩).mono fun _ _ => trivial
  · have hk : c'.nreg 14 + 1 ≤ b + 1 := by
      have := hI.1.env.r15; omega
    have hle : 2 * bfΔ b L * c'.nreg 14 + 2 * bfΔ b L ≤ bfXm b L := by
      unfold bfXm; nlinarith [Nat.mul_le_mul_left (2 * bfΔ b L) hk]
    have hc₁ := (Nat.cast_le (α := ℝ)).2 hle
    obtain ⟨c'', k'', e'', hI'', -⟩ := round2O_exec (P := P) hπ hD₁ hD₂ hH₁ hH₂ hL c' hI.1 hlt
    refine ((round2O_goodQ (P := P) hπ hD₁ hD₂ hH₁ hH₂ hDL₁ hDL₂ hHb₁ hHb₂ hL c' hI.1 hlt hI.2
      (by linarith) (by linarith)).and_run ⟨c'', k'', e'', hI''⟩).mono
      fun c₂ ⟨h1, h2, h3⟩ => ⟨h1, h2.mono (by rw [h3]; ring_nf; omega)⟩
  · rw [hI₁.r14, bfuO_zero]
    exact ⟨by have := bfuO_card_le hP 0 hv; rwa [bfuO_zero] at this, le_rfl⟩

end Round

end Monge

end PlanarFlow
