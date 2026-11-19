module

public import PlanarFlow.Monge.PrepH

/-!
# Building the tables: pass 1 of a level

For every target `t < b` (`r45`) at the level `sz` (`r44`): the half block of `t` (`bpar`), the
downward scan of the arc flags `finB X (c1 - 1 - κ) t`, `κ < nc`, giving `Lv b X sz t` at
`Sb + t` and `Gv b X sz t` at `Sb + 2b + t` (`p1Body_exec`, `pass1_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP Finset

attribute [local instance] Classical.propDecidable

/-- The half block of a target, without sources required. -/
lemma hbT_mem0 {b sz t : ℕ} (hsz : 0 < sz) (ht : t < b) :
    (hbT b sz t).1 ≤ t ∧ t < (hbT b sz t).1 + (hbT b sz t).2.1 ∧
      (hbT b sz t).2.2.2 ≤ (hbT b sz t).2.2.1 ∧ (hbT b sz t).2.2.1 ≤ b ∧
      (hbT b sz t).2.1 ≤ sz ∧ (hbT b sz t).2.2.2 ≤ sz := by
  obtain ⟨h1, h2, -⟩ := blk_of (t := t) hsz
  have hm := min_le_left (t / (sz + sz) * (sz + sz) + sz + sz) b
  have hm' := min_le_right (t / (sz + sz) * (sz + sz) + sz + sz) b
  unfold hbT
  split_ifs with h
  · simp only; omega
  · simp only; omega

/-- Pass 1 at the target `r45`. -/
def p1Body : Stmt :=
  .seq bpar <|
  .seq (block [.subN 56 48 10, .mulN 56 56 1, .addN 56 56 45, .addN 56 56 42, .constN 70 0,
    .copyN 71 49, .copyN 72 56, .copyN 73 1, .copyN 74 49]) <|
  .seq (.whileLtN 70 71 scanDBody) <|
  .seq (block [.addN 57 43 45, .storeN 57 74, .addN 57 57 1, .addN 57 57 1]) <|
  .seq (.ifLtN 74 49 (.instr (.constN 58 1)) (.instr (.constN 58 0))) <|
  block [.storeN 57 58, .addN 45 45 10]

variable {b Vb Db Fb Sb W : ℕ} {X : ℕ → ℕ → Prop} {D : ℕ → ℕ → ℤ} {P : Input}

/-- **Pass 1 at one target.** -/
theorem p1Body_exec (hL : LayP b Vb Db Fb Sb W) {sz t : ℕ} (hsz : 0 < sz) (hszb : sz ≤ b)
    (c : Config) (hc : WordsBounded W c) (hI : InP b Vb Db Fb Sb X D c) (h44 : c.nreg 44 = sz)
    (h45 : c.nreg 45 = t) (ht : t < b) :
    ∃ c' k, Exec P W p1Body c c' k ∧ k ≤ 7 * sz + 40 ∧
      (FrP b Vb Sb c c' ∧ c'.nreg 44 = sz ∧ c'.nreg 45 = t + 1 ∧
        c'.nmem (Sb + t) = Lv b X sz t ∧ c'.nmem (Sb + 2 * b + t) = Gv b X sz t ∧
        (∀ a, a ≠ Sb + t → a ≠ Sb + 2 * b + t → c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem ∧
        c'.rreg = c.rreg) := by
  have hfs := hL.fs; have hsd := hL.sd; have hdv := hL.dv; have hw := hL.w
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := hbT_mem0 (b := b) hsz ht
  generalize hH : hbT b sz t = hb at m1 m2 m3 m4 m5 m6
  obtain ⟨r0, nr, c1, nc⟩ := hb
  simp only at m1 m2 m3 m4 m5 m6
  have hcb : (c1 - 1) * b + b ≤ b * b ∨ c1 = 0 := by
    rcases Nat.eq_zero_or_pos c1 with h | h
    · exact Or.inr h
    · left; have := Nat.mul_le_mul_right b (show c1 - 1 + 1 ≤ b by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; exact this
  have hcb' : (c1 - 1) * b ≤ b * b := by
    rcases hcb with h | h
    · omega
    · rw [h]; simp
  unfold p1Body
  refine spec_seq ?_
  refine spec_use (bpar_exec (P := P) c hc hI.r1 h44 h45 (by omega)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a46, a47, a48, a49, an, ar, anm, arm, ao⟩
  rw [hH] at a46 a47 a48 a49
  simp only at a46 a47 a48 a49
  have e₁ : ∀ r, r < 46 ∨ 54 < r → c₁.nreg r = c.nreg r := an
  refine spec_seq ?_
  exec_block
  · config_simp; rw [a48, e₁ 10 (by omega), e₁ 1 (by omega), hI.r10, hI.r1]; omega
  · config_simp; rw [a48, e₁ 10 (by omega), e₁ 1 (by omega), hI.r10, hI.r1, e₁ 45 (by omega), h45]
    omega
  · config_simp
    rw [a48, e₁ 10 (by omega), e₁ 1 (by omega), hI.r10, hI.r1, e₁ 45 (by omega), h45,
      e₁ 42 (by omega), hI.r42]
    omega
  · omega
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded W c₂ := hc₂ ▸ ‹_›
  have g : ∀ r, (r < 46 ∨ 54 < r) → r ≠ 56 → r ≠ 70 → r ≠ 71 → r ≠ 72 → r ≠ 73 → r ≠ 74 →
      c₂.nreg r = c.nreg r := fun r h a1 a2 a3 a4 a5 a6 => by
    rw [← hc₂]; config_simp; simp only [upd_apply]
    split_ifs <;> first | omega | exact e₁ r h
  have hA : c₂.nreg 72 = (c1 - 1) * b + t + Fb := by
    rw [← hc₂]; config_simp
    rw [a48, e₁ 10 (by omega), e₁ 1 (by omega), hI.r10, hI.r1, e₁ 45 (by omega), h45,
      e₁ 42 (by omega), hI.r42]
  -- the scan
  refine spec_seq ?_
  refine spec_use (scanD_exec (P := P) (n := nc) (A := (c1 - 1) * b + t + Fb) (S := b)
    (f := fun j => finB X (c1 - 1 - j) t) c₂ hw₂
    (by rw [g 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hI.r10)
    (by rw [← hc₂]; config_simp) (by rw [← hc₂]; config_simp; exact a49) hA
    (by rw [← hc₂]; config_simp; rw [e₁ 1 (by omega)]; exact hI.r1)
    (by rw [← hc₂]; config_simp; exact a49)
    (fun j hj => by
      rw [← hc₂]; config_simp; rw [anm]
      have e : (c1 - 1) * b + t + Fb - j * b = Fb + (c1 - 1 - j) * b + t := by
        have : (c1 - 1) * b = (c1 - 1 - j) * b + j * b := by rw [← Nat.add_mul]; congr 1; omega
        omega
      rw [e]; exact hI.fl _ _ (by omega) ht)
    (fun j _ => finB_le _ _)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hres, sn, sr, snm, srm, so⟩
  generalize hLd : c₃.nreg 74 = L at hres
  -- the result is `Lv`
  have hLv : Lv b X sz t = L := by
    unfold Lv; rw [hH]; simp only
    refine lcol_of_scan ?_
    have e : ∀ j, Monge.Fb X r0 c1 (t - r0) j ↔ finB X (c1 - 1 - j) t = 1 := fun j => by
      unfold Monge.Fb finB; rw [show r0 + (t - r0) = t by omega]; split_ifs with h <;> simp [h]
    rcases hres with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · refine Or.inl ⟨h1, (e L).2 h2, fun j hj hF => ?_⟩
      have := h3 j hj
      rw [(e j).1 hF] at this
      omega
    · refine Or.inr ⟨h1, fun j hj hF => ?_⟩
      have := h2 j hj
      rw [(e j).1 hF] at this
      omega
  have hLn : L ≤ nc := by rcases hres with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  have g₃ : ∀ r, (r < 46 ∨ 54 < r) → r ≠ 56 → r ≠ 70 → r ≠ 71 → r ≠ 72 → r ≠ 73 → r ≠ 74 →
      r ≠ 75 → c₃.nreg r = c.nreg r := fun r h a1 a2 a3 a4 a5 a6 a7 => by
    rw [sn r a2 a4 a6 a7]; exact g r h a1 a2 a3 a4 a5 a6
  have f43 := g₃ 43 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have f45 := g₃ 45 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have f1 := g₃ 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have f10 := g₃ 10 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have f44 := g₃ 44 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have f49 : c₃.nreg 49 = nc := by
    rw [sn 49 (by omega) (by omega) (by omega) (by omega), ← hc₂]; config_simp; exact a49
  refine spec_seq ?_
  exec_block
  · rw [f43, f45, hI.r43, h45]; omega
  · config_simp; rw [f43, f45, hI.r43, h45, f1, hI.r1]; omega
  · config_simp; rw [f43, f45, hI.r43, h45, f1, hI.r1]; omega
  generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
  have hw₄ : WordsBounded W c₄ := hc₄ ▸ ‹_›
  have h57 : c₄.nreg 57 = Sb + 2 * b + t := by
    rw [← hc₄]; config_simp; rw [f43, f45, hI.r43, h45, f1, hI.r1]; ring
  have h74' : c₄.nreg 74 = L := by rw [← hc₄]; config_simp; exact hLd
  have h49' : c₄.nreg 49 = nc := by rw [← hc₄]; config_simp; exact f49
  have hnm₄ : ∀ a, c₄.nmem a = if a = Sb + t then L else c.nmem a := fun a => by
    rw [← hc₄]; config_simp; rw [upd_apply, f43, f45, hI.r43, h45, hLd, snm, ← hc₂]
    config_simp; rw [anm]
  have hfin : ∀ c' : Config, WordsBounded W c' → c'.nreg 58 = Gv b X sz t →
      (∀ r, r ≠ 58 → c'.nreg r = c₄.nreg r) → c'.rreg = c₄.rreg → c'.nmem = c₄.nmem →
      c'.rmem = c₄.rmem → c'.output = c₄.output →
      ∃ c'' k, Exec P W (block [.storeN 57 58, .addN 45 45 10]) c' c'' k ∧ k = 2 ∧
        (FrP b Vb Sb c c'' ∧ c''.nreg 44 = sz ∧ c''.nreg 45 = t + 1 ∧
          c''.nmem (Sb + t) = Lv b X sz t ∧ c''.nmem (Sb + 2 * b + t) = Gv b X sz t ∧
          (∀ a, a ≠ Sb + t → a ≠ Sb + 2 * b + t → c''.nmem a = c.nmem a) ∧ c''.rmem = c.rmem ∧
          c''.rreg = c.rreg) := by
    intro c' hw' h58 hn hr hnm hrm ho
    have e45 : c'.nreg 45 = t := by
      rw [hn 45 (by omega), ← hc₄]; config_simp; rw [f45, h45]
    have e10 : c'.nreg 10 = 1 := by
      rw [hn 10 (by omega), ← hc₄]; config_simp; rw [f10, hI.r10]
    have e57 : c'.nreg 57 = Sb + 2 * b + t := by rw [hn 57 (by omega), h57]
    have g₃' : ∀ r, (r < 44 ∨ 80 ≤ r) → c₃.nreg r = c.nreg r := fun r hr' =>
      g₃ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have hgen : ∀ r, (r < 44 ∨ 80 ≤ r) → c'.nreg r = c.nreg r := fun r hr' => by
      rw [hn r (by omega), ← hc₄]; config_simp; simp only [upd_apply]
      split_ifs <;> first | omega | exact g₃' r hr'
    exec_block
    · config_simp; rw [e45, e10]; omega
    refine ⟨rfl, ⟨fun r hr' => ?_, fun r _ => ?_, fun a ha => ?_, fun a _ => ?_, ?_⟩, ?_, ?_, ?_,
      ?_, fun a h1 h2 => ?_, ?_, ?_⟩
    · config_simp; rw [upd_other _ _ _ (by omega)]; exact hgen r hr'
    · config_simp; rw [hr, ← hc₄]; config_simp; rw [sr, ← hc₂]; config_simp; rw [ar]
    · config_simp; rw [upd_apply, e57, hnm, hnm₄]; split_ifs <;> omega
    · config_simp; rw [hrm, ← hc₄]; config_simp; rw [srm, ← hc₂]; config_simp; rw [arm]
    · config_simp; rw [ho, ← hc₄]; config_simp; rw [so, ← hc₂]; config_simp; rw [ao]
    · config_simp; rw [hn 44 (by omega), ← hc₄]; config_simp
      rw [f44, h44]
    · config_simp; rw [e45, e10]
    · config_simp; rw [upd_apply, e57, hnm, hnm₄, hLv]; split_ifs <;> omega
    · config_simp; rw [upd_apply, e57, h58]; simp
    · config_simp; rw [upd_apply, e57, hnm, hnm₄]; split_ifs <;> omega
    · config_simp; rw [hrm, ← hc₄]; config_simp; rw [srm, ← hc₂]; config_simp; rw [arm]
    · config_simp; rw [hr, ← hc₄]; config_simp; rw [sr, ← hc₂]; config_simp; rw [ar]
  have hG : Gv b X sz t = if L < nc then 1 else 0 := by
    unfold Gv; rw [hLv, hH]
  refine spec_seq ?_
  by_cases hlt : L < nc
  · have htest : c₄.nreg 74 < c₄.nreg 49 := by rw [h74', h49']; exact hlt
    refine spec_ifLtN_true htest ?_
    refine spec_instr (Exec.constN hw₄ 58 1 (by omega)) fun hw₅ => ?_
    obtain ⟨c'', k, hex, hk, hpost⟩ := hfin _ hw₅
      (by config_simp; rw [hG, ite_eq_left_of_eq_true _ _ (eq_true hlt)])
      (fun r hr => by config_simp; rw [upd_other _ _ _ hr]) rfl rfl rfl rfl
    exact ⟨c'', k, hex, by omega, hpost⟩
  · have htest : ¬ c₄.nreg 74 < c₄.nreg 49 := by rw [h74', h49']; exact hlt
    refine spec_ifLtN_false htest ?_
    refine spec_instr (Exec.constN hw₄ 58 0 (by omega)) fun hw₅ => ?_
    obtain ⟨c'', k, hex, hk, hpost⟩ := hfin _ hw₅
      (by config_simp; rw [hG, ite_eq_right_of_eq_false _ _ (eq_false hlt)])
      (fun r hr => by config_simp; rw [upd_other _ _ _ hr]) rfl rfl rfl rfl
    exact ⟨c'', k, hex, by omega, hpost⟩

/-- Pass 1 of a level: all the targets. -/
def pass1 : Stmt := .seq (.instr (.constN 45 0)) (.whileLtN 45 1 p1Body)

/-- The state of pass 1 from `c₀`. -/
structure IP1 (b Vb Db Fb Sb W : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (sz : ℕ) (c₀ c : Config) :
    Prop where
  wb : WordsBounded W c
  inp : InP b Vb Db Fb Sb X D c
  frm : FrP b Vb Sb c₀ c
  r44 : c.nreg 44 = sz
  le : c.nreg 45 ≤ b
  lv : ∀ t < c.nreg 45, c.nmem (Sb + t) = Lv b X sz t ∧ c.nmem (Sb + 2 * b + t) = Gv b X sz t
  nmem : ∀ a, (a < Sb ∨ Sb + 3 * b ≤ a) → c.nmem a = c₀.nmem a
  rmem : c.rmem = c₀.rmem
  rreg : c.rreg = c₀.rreg

/-- **Pass 1 of a level.** -/
theorem pass1_exec (hL : LayP b Vb Db Fb Sb W) {sz : ℕ} (hsz : 0 < sz) (hszb : sz ≤ b)
    (c : Config) (hc : WordsBounded W c) (hI : InP b Vb Db Fb Sb X D c) (h44 : c.nreg 44 = sz) :
    ∃ c' k, Exec P W pass1 c c' k ∧ k ≤ (7 * sz + 42) * b + 3 ∧
      (FrP b Vb Sb c c' ∧ InP b Vb Db Fb Sb X D c' ∧ c'.nreg 44 = sz ∧
        (∀ t < b, c'.nmem (Sb + t) = Lv b X sz t ∧ c'.nmem (Sb + 2 * b + t) = Gv b X sz t) ∧
        (∀ a, (a < Sb ∨ Sb + 3 * b ≤ a) → c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem ∧
        c'.rreg = c.rreg) := by
  have hw := hL.w
  unfold pass1
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 45 0 (by omega)) fun hw₁ => ?_
  have hF₁ : FrP b Vb Sb c { c with nreg := upd c.nreg 45 0 } :=
    ⟨fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)], fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl⟩
  refine spec_while (IP1 b Vb Db Fb Sb W X D sz c) (fun c => (7 * sz + 42) * (b - c.nreg 45))
    (fun c h => h.wb) ?_ ⟨hw₁, hI.of hL hF₁, hF₁, by config_simp; exact h44,
      by config_simp; omega, fun t ht => by config_simp at ht; omega, fun _ _ => rfl, rfl, rfl⟩ ?_
  · intro c₁ hI₁ hlt
    rw [hI₁.inp.r1] at hlt
    generalize ht : c₁.nreg 45 = t at hlt
    obtain ⟨c₂, k, hex, hk, hF, h44', h45', hL1, hG1, hnm, hrm, hrr⟩ :=
      p1Body_exec (P := P) hL hsz hszb c₁ hI₁.wb hI₁.inp hI₁.r44 ht hlt
    refine ⟨c₂, k, hex, ⟨hex.wb_right, hI₁.inp.of hL hF, hI₁.frm.trans hF, h44', by omega,
      fun t' ht' => ?_, fun a ha => ?_, by rw [hrm, hI₁.rmem], by rw [hrr, hI₁.rreg]⟩, ?_⟩
    · rw [h45'] at ht'
      rcases Nat.lt_or_ge t' t with h | h
      · rw [hnm _ (by omega) (by omega), hnm _ (by omega) (by omega)]
        exact hI₁.lv t' (by omega)
      · rw [show t' = t by omega]; exact ⟨hL1, hG1⟩
    · rw [hnm _ (by omega) (by omega)]; exact hI₁.nmem a ha
    · have := mul_pred_add (a := 7 * sz + 42) (x := b - t) (by omega)
      rw [show b - t - 1 = b - (t + 1) by omega] at this
      rw [h45']
      omega
  · intro c₂ k₂ hI₂ hn₂ hk₂
    have h45 : c₂.nreg 45 = b := by have := hI₂.le; rw [hI₂.inp.r1] at hn₂; omega
    refine ⟨?_, hI₂.frm, hI₂.inp, hI₂.r44, fun t ht => hI₂.lv t (by omega),
      fun a ha => hI₂.nmem a ha, by rw [hI₂.rmem], by rw [hI₂.rreg]⟩
    beta_reduce at hk₂; config_simp at hk₂; simp only [Nat.sub_zero] at hk₂; omega

end Monge

end PlanarFlow
