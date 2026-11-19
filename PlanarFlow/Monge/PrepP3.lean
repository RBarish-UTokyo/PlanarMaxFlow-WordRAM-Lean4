module

public import PlanarFlow.Monge.PrepP2

/-!
# Building the tables: pass 3 of a level

For every target `t < b` (`r45`) and every source `s = c1 - 1 - κ` of its half block at the
level `sz` (`κ = r55`, and `κ` as a real in the real register `41`): the entry of the pair
`(s, t)` from the standing target `Rv` (at `Sb + b + t`), its first arc column `Lv` (at
`Sb + Rv`), the arc flags and the lengths, written at `Vb + 2 (s b + t)` (`entP_exec`,
`p3Body_exec`, `pass3_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP Finset

attribute [local instance] Classical.propDecidable

/-- The entry of the pair `(r48 - 1 - r55, r45)`. -/
def entP : Stmt :=
  .seq (block [.subN 56 48 10, .subN 56 56 55, .addN 57 43 1, .addN 57 57 45, .loadN 57 57,
     .mulN 58 56 1, .addN 59 58 57, .addN 59 59 42, .loadN 59 59, .addN 60 58 45, .addN 61 60 42,
     .loadN 61 61, .addN 60 60 60, .addN 60 60 40, .storeN 60 61, .addN 62 60 10]) <|
  .seq (.ifLtN 59 10
     (.seq (block [.constR 43 0, .storeR 62 43, .addN 63 43 57, .loadN 63 63])
        (.seq (.ifLtN 55 63 (.instr (.subR 44 40 41)) (.instr (.addR 44 40 41)))
          (.instr (.storeR 60 44))))
     (block [.constR 43 1, .storeR 62 43, .addN 63 58 57, .addN 63 63 41, .loadR 44 63,
        .storeR 60 44])) <|
  block [.addN 55 55 10, .addR 41 41 42]

variable {b Vb Db Fb Sb W : ℕ} {X : ℕ → ℕ → Prop} {D : ℕ → ℕ → ℤ} {P : Input}

/-- The cells of one entry. -/
structure EntW (b Vb : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (H : ℝ) (s t : ℕ) (c c' : Config) :
    Prop where
  nmem : ∀ a, c'.nmem a = if a = Vb + 2 * (s * b + t) then finB X s t else c.nmem a
  rmem : ∀ a, c'.rmem a = if a = Vb + 2 * (s * b + t) then tVal b X D H s t
    else if a = Vb + 2 * (s * b + t) + 1 then tMul b X s t else c.rmem a

/-- **One entry written.** -/
theorem TabOK.write {H : ℝ} {Pr : ℕ → ℕ → Prop} {s₀ t₀ : ℕ} {c c' : Config}
    (hs₀ : s₀ < b) (ht₀ : t₀ < b) (h : TabOK b Vb X D H Pr c) (hw : EntW b Vb X D H s₀ t₀ c c') :
    TabOK b Vb X D H (fun s t => Pr s t ∨ (s = s₀ ∧ t = t₀)) c' := by
  intro s t hs ht hst hp
  by_cases he : s = s₀ ∧ t = t₀
  · obtain ⟨rfl, rfl⟩ := he
    rw [hw.nmem, hw.rmem, hw.rmem]
    simp
  · rcases hp with hp | hp
    · have hne := cellP_ne (b := b) hs ht hs₀ ht₀ (fun e => he (Prod.mk.inj e))
      obtain ⟨e1, e2, e3⟩ := h s t hs ht hst hp
      rw [hw.nmem, hw.rmem, hw.rmem, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact ⟨e1, e2, e3⟩
    · exact absurd hp he

/-- **The entry of one pair.** -/
theorem entP_exec (hL : LayP b Vb Db Fb Sb W) {H : ℝ} {sz T t κ : ℕ} (hT : sz = 2 ^ T)
    (ht : t < b) (hκ : κ < (hbT b sz t).2.2.2) (c : Config) (hc : WordsBounded W c)
    (hI : InP b Vb Db Fb Sb X D c) (h40 : c.rreg 40 = H) (h41 : c.rreg 41 = (κ : ℝ))
    (h42 : c.rreg 42 = 1) (h45 : c.nreg 45 = t) (h48 : c.nreg 48 = (hbT b sz t).2.2.1)
    (h55 : c.nreg 55 = κ) (hR : c.nmem (Sb + b + t) = Rv b X sz t)
    (hLv : ∀ t' < b, c.nmem (Sb + t') = Lv b X sz t') :
    ∃ c' k, Exec P W entP c c' k ∧ k ≤ 30 ∧
      (EntW b Vb X D H ((hbT b sz t).2.2.1 - 1 - κ) t c c' ∧ c'.nreg 55 = κ + 1 ∧
        c'.rreg 41 = ((κ + 1 : ℕ) : ℝ) ∧ (∀ r, r < 55 ∨ 64 ≤ r → c'.nreg r = c.nreg r) ∧
        (∀ r, r ≠ 41 → r ≠ 43 → r ≠ 44 → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
  have hfs := hL.fs; have hsd := hL.sd; have hdv := hL.dv; have hw := hL.w
  have hsz : 0 < sz := by rw [hT]; exact Nat.two_pow_pos T
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hbT_mem (b := b) hsz ht (by omega)
  obtain ⟨-, hsb, hst, -⟩ := hbOf_eq_hbT (b := b) hT ht hκ
  obtain ⟨r1, r2⟩ := Rv_mem (X := X) hsz ht (by omega)
  generalize hsd' : (hbT b sz t).2.2.1 - 1 - κ = s at hsb hst
  generalize hRv : Rv b X sz t = t' at r1 r2 hR
  have ht' : t' < b := by omega
  have hsbb : s * b + b ≤ b * b := by
    have := Nat.mul_le_mul_right b (show s + 1 ≤ b by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have e56 : c.nreg 48 - c.nreg 10 - c.nreg 55 = s := by rw [h48, hI.r10, h55, ← hsd']
  have e57 : c.nmem (c.nreg 43 + c.nreg 1 + c.nreg 45) = t' := by rw [hI.r43, hI.r1, h45, hR]
  have hflag' : c.nmem (s * b + t' + Fb) = finB X s t' := by
    rw [show s * b + t' + Fb = Fb + s * b + t' by ring]; exact hI.fl s t' hsb ht'
  have hflag : c.nmem (s * b + t + Fb) = finB X s t := by
    rw [show s * b + t + Fb = Fb + s * b + t by ring]; exact hI.fl s t hsb ht
  unfold entP
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hI.r43, hI.r1]; omega
  · config_simp; rw [hI.r43, hI.r1, h45]; omega
  · config_simp; rw [e56, hI.r1]; omega
  · config_simp; rw [e57, e56, hI.r1]; omega
  · config_simp; rw [e57, e56, hI.r1, hI.r42]; omega
  · config_simp; rw [e56, hI.r1, h45]; omega
  · config_simp; rw [e56, hI.r1, h45, hI.r42]; omega
  · config_simp; rw [e56, hI.r1, h45]; omega
  · config_simp; rw [e56, hI.r1, h45, hI.r40]; omega
  · config_simp; rw [e56, hI.r1, h45, hI.r40, hI.r10]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded W c₁ := hc₁ ▸ ‹_›
  have g : ∀ r, r < 56 ∨ 63 ≤ r → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have g55 : c₁.nreg 55 = κ := by rw [g 55 (by omega), h55]
  have g57 : c₁.nreg 57 = t' := by rw [← hc₁]; config_simp; exact e57
  have g58 : c₁.nreg 58 = s * b := by rw [← hc₁]; config_simp; rw [e56, hI.r1]
  have g59 : c₁.nreg 59 = finB X s t' := by
    rw [← hc₁]; config_simp; rw [e57, e56, hI.r1, hI.r42, hflag']
  have g60 : c₁.nreg 60 = Vb + 2 * (s * b + t) := by
    rw [← hc₁]; config_simp; rw [e56, hI.r1, h45, hI.r40]; ring
  have g62 : c₁.nreg 62 = Vb + 2 * (s * b + t) + 1 := by
    rw [← hc₁]; config_simp; rw [e56, hI.r1, h45, hI.r40, hI.r10]; ring
  have gnm : ∀ a, c₁.nmem a = if a = Vb + 2 * (s * b + t) then finB X s t else c.nmem a :=
    fun a => by
      rw [← hc₁]; config_simp; rw [upd_apply, e56, hI.r1, h45, hI.r40, hI.r42, hflag]
      rw [show s * b + t + (s * b + t) + Vb = Vb + 2 * (s * b + t) by ring]
  have grm : c₁.rmem = c.rmem := by rw [← hc₁]
  have grr : c₁.rreg = c.rreg := by rw [← hc₁]
  have go : c₁.output = c.output := by rw [← hc₁]
  -- the values
  have hval := tVal_hbT (X := X) (D := D) (H := H) hT ht hκ
  have hmul := tMul_hbT (X := X) hT ht hκ
  rw [hsd', hRv] at hval hmul
  -- the last block
  have hlast : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 55 = κ → c₂.rreg 41 = (κ : ℝ) →
      c₂.rreg 42 = 1 → c₂.nreg 10 = 1 →
      ∃ c' k, Exec P W (block [.addN 55 55 10, .addR 41 41 42]) c₂ c' k ∧ k = 2 ∧
        c'.nreg 55 = κ + 1 ∧ c'.rreg 41 = ((κ + 1 : ℕ) : ℝ) ∧
        (∀ r, r ≠ 55 → c'.nreg r = c₂.nreg r) ∧ (∀ r, r ≠ 41 → c'.rreg r = c₂.rreg r) ∧
        c'.nmem = c₂.nmem ∧ c'.rmem = c₂.rmem ∧ c'.output = c₂.output := by
    intro c₂ hw₂ a55 a41 a42 a10
    have hW : c₂.nreg 55 + c₂.nreg 10 ≤ W := by rw [a55, a10]; omega
    exec_block
    · exact hW
    exact ⟨rfl, by config_simp; rw [a55, a10], by config_simp; rw [a41, a42]; push_cast; ring,
      fun r hr => by config_simp; rw [upd_other _ _ _ hr], fun r hr => by
        config_simp; rw [upd_other _ _ _ hr], rfl, rfl, rfl⟩
  refine spec_seq ?_
  by_cases hX : X s t'
  · have hf1 : finB X s t' = 1 := by
      unfold finB; rw [ite_eq_left_of_eq_true _ _ (eq_true hX)]
    rw [ite_eq_left_of_eq_true _ _ (eq_true hX)] at hval hmul
    have htest : ¬ c₁.nreg 59 < c₁.nreg 10 := by rw [g59, hf1, g 10 (by omega), hI.r10]; omega
    refine spec_ifLtN_false htest ?_
    exec_block
    · rw [g58, g57]; omega
    · config_simp; rw [g58, g57, g 41 (by omega), hI.r41]; omega
    · config_simp; rw [g55, g 10 (by omega), hI.r10]; omega
    refine ⟨by omega, ⟨fun a => ?_, fun a => ?_⟩, ?_, ?_, fun r hr => ?_, fun r h1 h2 h3 => ?_,
      ?_⟩
    · config_simp; exact gnm a
    · config_simp
      rw [upd_apply, upd_apply, g60, g62, g58, g57, g 41 (by omega), hI.r41, grm, hval, hmul]
      rw [show s * b + t' + Db = Db + s * b + t' by ring, hI.dv s t' hsb ht']
      simp only [upd_apply]
      split_ifs <;> first | omega | rfl | simp
    · config_simp; rw [g55, g 10 (by omega), hI.r10]
    · config_simp; rw [grr, h41, h42]; push_cast; ring
    · config_simp; simp only [upd_apply]
      split_ifs <;> first | omega | exact g r (by omega)
    · config_simp; simp only [upd_apply]
      split_ifs <;> first | omega | rw [grr]
    · config_simp; rw [go]
  · have hf0 : finB X s t' = 0 := by
      unfold finB; rw [ite_eq_right_of_eq_false _ _ (eq_false hX)]
    have htest : c₁.nreg 59 < c₁.nreg 10 := by rw [g59, hf0, g 10 (by omega), hI.r10]; omega
    refine spec_ifLtN_true htest ?_
    refine spec_seq ?_
    exec_block
    · rw [g 43 (by omega), hI.r43, g57]; omega
    generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
    have hw₂ : WordsBounded W c₂ := hc₂ ▸ ‹_›
    have g63 : c₂.nreg 63 = Lv b X sz t' := by
      rw [← hc₂]; config_simp; rw [g 43 (by omega), hI.r43, g57, gnm,
        ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact hLv t' ht'
    have c55 : c₂.nreg 55 = κ := by rw [← hc₂]; config_simp; exact g55
    have hfin : ∀ (v : ℝ), v = tVal b X D H s t → ∀ c₃ : Config, WordsBounded W c₃ →
        c₃.rreg 44 = v → c₃.nreg = c₂.nreg → (∀ r, r ≠ 44 → c₃.rreg r = c₂.rreg r) →
        c₃.nmem = c₂.nmem → c₃.rmem = c₂.rmem → c₃.output = c₂.output →
        ∃ c₄ k₄, Exec P W (.instr (.storeR 60 44)) c₃ c₄ k₄ ∧ k₄ = 1 ∧
          ∃ c' k, Exec P W (block [.addN 55 55 10, .addR 41 41 42]) c₄ c' k ∧ k = 2 ∧
          (EntW b Vb X D H s t c c' ∧ c'.nreg 55 = κ + 1 ∧ c'.rreg 41 = ((κ + 1 : ℕ) : ℝ) ∧
            (∀ r, r < 55 ∨ 64 ≤ r → c'.nreg r = c.nreg r) ∧
            (∀ r, r ≠ 41 → r ≠ 43 → r ≠ 44 → c'.rreg r = c.rreg r) ∧ c'.output = c.output) := by
      intro v hv c₃ hw₃ a44 an3 ar3 anm3 arm3 ao3
      have hw₄ := (Exec.storeR (P := P) hw₃ 60 44).wb_right
      obtain ⟨c', k, hex, hk, a55, a41, an, ar, anm, arm, ao⟩ := hlast _ hw₄
        (by config_simp; rw [an3, c55])
        (by config_simp; rw [ar3 41 (by omega), ← hc₂]; config_simp; rw [grr, h41])
        (by config_simp; rw [ar3 42 (by omega), ← hc₂]; config_simp; rw [grr, h42])
        (by config_simp; rw [an3, ← hc₂]; config_simp; rw [g 10 (by omega), hI.r10])
      refine ⟨_, 1, Exec.storeR hw₃ 60 44, rfl, c', k, hex, hk, ⟨fun a => ?_, fun a => ?_⟩, a55,
        a41, fun r hr => ?_, fun r h1 h2 h3 => ?_, ?_⟩
      · rw [anm]; config_simp; rw [anm3, ← hc₂]; exact gnm a
      · rw [arm]; config_simp
        rw [upd_apply, an3, a44, arm3, ← hc₂]; config_simp
        rw [upd_apply, g60, g62, grm, hmul, ite_eq_right_of_eq_false _ _ (eq_false hX), hv]
        split_ifs <;> first | omega | rfl | simp
      · rw [an r (by omega)]; config_simp; rw [an3, ← hc₂]; config_simp; simp only [upd_apply]
        split_ifs <;> first | omega | exact g r (by omega)
      · rw [ar r h1]; config_simp; rw [ar3 r h3, ← hc₂]; config_simp
        rw [upd_other _ _ _ h2, grr]
      · rw [ao]; config_simp; rw [ao3, ← hc₂, go]
    have e41 : c₂.rreg 41 = (κ : ℝ) := by rw [← hc₂]; config_simp; rw [grr, h41]
    have e40 : c₂.rreg 40 = H := by rw [← hc₂]; config_simp; rw [grr, h40]
    have e60 : c₂.nreg 60 = c₁.nreg 60 := by rw [← hc₂]; config_simp
    by_cases hlt : κ < Lv b X sz t'
    · have htest' : c₂.nreg 55 < c₂.nreg 63 := by rw [c55, g63]; exact hlt
      refine spec_seq ?_
      refine spec_ifLtN_true htest' ?_
      refine spec_instr (Exec.subR hw₂ 44 40 41) fun hw₃ => ?_
      obtain ⟨c₄, k₄, hex₄, hk₄, c', k, hex, hk, hp⟩ := hfin (H - κ) (by
        rw [hval, ite_eq_right_of_eq_false _ _ (eq_false hX),
          ite_eq_left_of_eq_true _ _ (eq_true hlt)]; ring) _ hw₃
        (by config_simp; rw [e40, e41]) rfl (fun r hr => by config_simp; rw [upd_other _ _ _ hr])
        rfl rfl rfl
      exact ⟨c₄, k₄, hex₄, c', k, hex, by omega, hp⟩
    · have htest' : ¬ c₂.nreg 55 < c₂.nreg 63 := by rw [c55, g63]; exact hlt
      refine spec_seq ?_
      refine spec_ifLtN_false htest' ?_
      refine spec_instr (Exec.addR hw₂ 44 40 41) fun hw₃ => ?_
      obtain ⟨c₄, k₄, hex₄, hk₄, c', k, hex, hk, hp⟩ := hfin (H + κ) (by
        rw [hval, ite_eq_right_of_eq_false _ _ (eq_false hX),
          ite_eq_right_of_eq_false _ _ (eq_false hlt)]) _ hw₃
        (by config_simp; rw [e40, e41]) rfl (fun r hr => by config_simp; rw [upd_other _ _ _ hr])
        rfl rfl rfl
      exact ⟨c₄, k₄, hex₄, c', k, hex, by omega, hp⟩

/-- Pass 3 at the target `r45`. -/
def p3Body : Stmt :=
  .seq bpar <| .seq (block [.constN 55 0, .constR 41 0]) <|
    .seq (.whileLtN 55 49 entP) (.instr (.addN 45 45 10))

/-- The pairs of the half block of `t` with the first `k` sources. -/
def SrcP (b sz t k : ℕ) (s : ℕ) : Prop := ∃ κ < k, s = (hbT b sz t).2.2.1 - 1 - κ

/-- The state of pass 3 at the target `t`, from `c₀`. -/
structure IE (b Vb Db Fb Sb W : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (H : ℝ) (sz t : ℕ)
    (Pr : ℕ → ℕ → Prop) (c₀ c : Config) : Prop where
  wb : WordsBounded W c
  inp : InP b Vb Db Fb Sb X D c
  frm : FrP b Vb Sb c₀ c
  regs : ∀ r, r < 55 ∨ 64 ≤ r → c.nreg r = c₀.nreg r
  le : c.nreg 55 ≤ (hbT b sz t).2.2.2
  r40 : c.rreg 40 = H
  r41 : c.rreg 41 = (c.nreg 55 : ℝ)
  r42 : c.rreg 42 = 1
  mem : ∀ a, (a < Vb ∨ Vb + 2 * (b * b) ≤ a) → c.nmem a = c₀.nmem a ∧ c.rmem a = c₀.rmem a
  tab : TabOK b Vb X D H (fun s' t' => Pr s' t' ∨ (t' = t ∧ SrcP b sz t (c.nreg 55) s')) c

/-- **Pass 3 at one target.** -/
theorem p3Body_exec (hL : LayP b Vb Db Fb Sb W) {H : ℝ} {sz T t : ℕ} (hT : sz = 2 ^ T)
    (hszb : sz ≤ b) {Pr : ℕ → ℕ → Prop} (c : Config) (hc : WordsBounded W c)
    (hI : InP b Vb Db Fb Sb X D c) (h44 : c.nreg 44 = sz) (h45 : c.nreg 45 = t) (ht : t < b)
    (h40 : c.rreg 40 = H) (h42 : c.rreg 42 = 1)
    (hR : 0 < (hbT b sz t).2.2.2 → c.nmem (Sb + b + t) = Rv b X sz t)
    (hLv : ∀ t' < b, c.nmem (Sb + t') = Lv b X sz t') (htab : TabOK b Vb X D H Pr c) :
    ∃ c' k, Exec P W p3Body c c' k ∧ k ≤ 32 * sz + 20 ∧
      (FrP b Vb Sb c c' ∧ c'.nreg 44 = sz ∧ c'.nreg 45 = t + 1 ∧ c'.rreg 40 = H ∧
        c'.rreg 42 = 1 ∧
        (∀ a, (a < Vb ∨ Vb + 2 * (b * b) ≤ a) → c'.nmem a = c.nmem a ∧ c'.rmem a = c.rmem a) ∧
        TabOK b Vb X D H (fun s' t' => Pr s' t' ∨ (t' = t ∧ SrcP b sz t (hbT b sz t).2.2.2 s'))
          c') := by
  have hw := hL.w; have hsd := hL.sd; have hdv := hL.dv; have hfs := hL.fs
  have hsz : 0 < sz := by rw [hT]; exact Nat.two_pow_pos T
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hbT_mem0 (b := b) hsz ht
  unfold p3Body
  refine spec_seq ?_
  refine spec_use (bpar_exec (P := P) c hc hI.r1 h44 h45 (by omega)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a46, a47, a48, a49, an, ar, anm, arm, ao⟩
  refine spec_seq ?_
  exec_block
  · omega
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded W c₂ := hc₂ ▸ ‹_›
  have hF₂ : FrP b Vb Sb c c₂ := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, fun a _ => ?_, fun a _ => ?_, ?_⟩
    · rw [← hc₂]; config_simp; rw [upd_other _ _ _ (by omega), an r (by omega)]
    · rw [← hc₂]; config_simp; rw [upd_other _ _ _ (by omega), ar]
    · rw [← hc₂]; config_simp; rw [anm]
    · rw [← hc₂]; config_simp; rw [arm]
    · rw [← hc₂]; config_simp; rw [ao]
  have hI₂ := hI.of hL hF₂
  have g49 : c₂.nreg 49 = (hbT b sz t).2.2.2 := by rw [← hc₂]; config_simp; exact a49
  have g48 : c₂.nreg 48 = (hbT b sz t).2.2.1 := by rw [← hc₂]; config_simp; exact a48
  have g45 : c₂.nreg 45 = t := by rw [← hc₂]; config_simp; rw [an 45 (by omega), h45]
  refine spec_seq ?_
  refine spec_while (IE b Vb Db Fb Sb W X D H sz t Pr c₂)
    (fun c => 32 * ((hbT b sz t).2.2.2 - c.nreg 55)) (fun c h => h.wb) ?_
    ⟨hw₂, hI₂, FrP.refl _ _ _ _, fun _ _ => rfl, by rw [← hc₂]; config_simp; omega,
      by rw [← hc₂]; config_simp; rw [ar, h40], by rw [← hc₂]; config_simp; simp,
      by rw [← hc₂]; config_simp; rw [ar, h42], fun _ _ => ⟨rfl, rfl⟩,
      (TabOK.of htab (fun a _ _ => by rw [← hc₂]; config_simp; rw [anm])
        (fun a _ _ => by rw [← hc₂]; config_simp; rw [arm])).mono fun s' t' h => by
          rcases h with h | ⟨-, κ', hκ', -⟩
          · exact h
          · rw [← hc₂] at hκ'; config_simp at hκ'; omega⟩ ?_
  · intro c₃ hI₃ hlt
    rw [hI₃.regs 49 (by omega), g49] at hlt
    generalize hκ : c₃.nreg 55 = κ at hlt
    have hr45 : c₃.nreg 45 = t := by rw [hI₃.regs 45 (by omega), g45]
    have hr48 : c₃.nreg 48 = (hbT b sz t).2.2.1 := by rw [hI₃.regs 48 (by omega), g48]
    obtain ⟨c₄, k, hex, hk, hW, h55, h41', hn, hr, ho⟩ := entP_exec (P := P) hL (H := H) hT ht hlt
      c₃ hI₃.wb hI₃.inp hI₃.r40 (by rw [hI₃.r41, hκ]) hI₃.r42 hr45 hr48 hκ
      (by rw [(hI₃.mem _ (Or.inl (by omega))).1, ← hc₂]; config_simp; rw [anm]; exact hR (by omega))
      (fun t' ht' => by
        rw [(hI₃.mem _ (Or.inl (by omega))).1, ← hc₂]; config_simp; rw [anm]; exact hLv t' ht')
    have hs := hbOf_eq_hbT (b := b) hT ht hlt
    obtain ⟨-, -, hcell⟩ := rowcol hs.2.1 ht
    have hF₄ : FrP b Vb Sb c₃ c₄ := by
      refine ⟨fun r hr' => hn r (by omega), fun r hr' => hr r (by omega) (by omega) (by omega),
        fun a ha => ?_, fun a ha => ?_, ho⟩
      · rw [hW.nmem, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      · rw [hW.rmem, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
          ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    refine ⟨c₄, k, hex, ⟨hex.wb_right, hI₃.inp.of hL hF₄, hI₃.frm.trans hF₄, fun r hr' => ?_,
      by omega, ?_, by rw [h41', h55], ?_, fun a ha => ?_, ?_⟩, ?_⟩
    · rw [hn r hr']; exact hI₃.regs r hr'
    · rw [hr 40 (by omega) (by omega) (by omega)]; exact hI₃.r40
    · rw [hr 42 (by omega) (by omega) (by omega)]; exact hI₃.r42
    · rw [hW.nmem, hW.rmem, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
        ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
      exact hI₃.mem a ha
    · refine (TabOK.write hs.2.1 ht hI₃.tab hW).mono fun s' t' h => ?_
      rcases h with h | ⟨h1, κ', hκ', hs'⟩
      · exact Or.inl (Or.inl h)
      · rw [h55] at hκ'
        rcases Nat.lt_or_ge κ' κ with h' | h'
        · exact Or.inl (Or.inr ⟨h1, κ', by rw [hκ]; exact h', hs'⟩)
        · exact Or.inr ⟨by rw [hs', show κ' = κ by omega], h1⟩
    · rw [h55]; omega
  · intro c₃ k₃ hI₃ hn hk₃
    have h55 : c₃.nreg 55 = (hbT b sz t).2.2.2 := by
      have := hI₃.le; rw [hI₃.regs 49 (by omega), g49] at hn; omega
    have hw₃ := hI₃.wb
    have hr45 : c₃.nreg 45 = t := by rw [hI₃.regs 45 (by omega), g45]
    have hr10 : c₃.nreg 10 = 1 := hI₃.inp.r10
    refine spec_instr (Exec.addN hw₃ 45 45 10 (by rw [hr45, hr10]; omega)) fun hw₄ => ?_
    have hF₄ : FrP b Vb Sb c₃ { c₃ with nreg := upd c₃.nreg 45 (c₃.nreg 45 + c₃.nreg 10) } :=
      ⟨fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)], fun _ _ => rfl,
        fun _ _ => rfl, fun _ _ => rfl, rfl⟩
    refine ⟨?_, hF₂.trans (hI₃.frm.trans hF₄), ?_, ?_, ?_, ?_, fun a ha => ?_, ?_⟩
    · beta_reduce at hk₃; rw [← hc₂] at hk₃; config_simp at hk₃; simp only [Nat.sub_zero] at hk₃
      omega
    · config_simp; rw [hI₃.regs 44 (by omega), ← hc₂]; config_simp; rw [an 44 (by omega), h44]
    · config_simp; rw [hr45, hr10]
    · config_simp; exact hI₃.r40
    · config_simp; exact hI₃.r42
    · config_simp
      obtain ⟨e1, e2⟩ := hI₃.mem a ha
      rw [e1, e2, ← hc₂]; config_simp; exact ⟨by rw [anm], by rw [arm]⟩
    · have := hI₃.tab
      rw [h55] at this
      exact this

end Monge

end PlanarFlow
