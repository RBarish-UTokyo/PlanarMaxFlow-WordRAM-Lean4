module

public import PlanarFlow.Monge.PrepP1

/-!
# Building the tables: pass 2 of a level

For every target `t < b` (`r45`) whose half block at the level `sz` has sources: the downward
scan of the genuine flags `Gv` from `t` to the first target of the half block, then (if none)
the upward scan from that first target, giving the standing target `Rv b X sz t` at
`Sb + b + t` (`p2Body_exec`, `pass2_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP Finset

attribute [local instance] Classical.propDecidable

/-- The upward scan of pass 2. -/
def p2Up : Stmt :=
  .seq (block [.addN 56 43 1, .addN 56 56 1, .addN 56 56 46, .constN 70 0, .copyN 71 47,
     .copyN 72 56, .copyN 73 10, .copyN 74 47]) <|
  .seq (.whileLtN 70 71 scanUBody) <|
  .ifLtN 74 47 (.instr (.addN 57 46 74)) (.instr (.copyN 57 45))

/-- Pass 2 at a target with sources. -/
def p2Main : Stmt :=
  .seq (block [.subN 55 45 46, .addN 56 43 1, .addN 56 56 1, .addN 56 56 45,
     .constN 70 0, .addN 71 55 10, .copyN 72 56, .copyN 73 10, .copyN 74 71]) <|
  .seq (.whileLtN 70 71 scanDBody) <|
  .seq (.ifLtN 74 71 (.instr (.subN 57 45 74)) p2Up) <|
  block [.addN 58 43 1, .addN 58 58 45, .storeN 58 57]

/-- Pass 2 at the target `r45`. -/
def p2Body : Stmt := .seq bpar (.seq (.ifLtN 49 10 .skip p2Main) (.instr (.addN 45 45 10)))

variable {b Vb Db Fb Sb W : ℕ} {X : ℕ → ℕ → Prop} {D : ℕ → ℕ → ℤ} {P : Input}

lemma Gv_le (sz t : ℕ) : Gv b X sz t ≤ 1 := by unfold Gv; split_ifs <;> omega

/-- The standing target of a target without a genuine row at or above it. -/
theorem p2Up_exec (hL : LayP b Vb Db Fb Sb W) {sz t : ℕ} (hsz : 0 < sz) (ht : t < b)
    (hnc : 0 < (hbT b sz t).2.2.2) (c : Config) (hc : WordsBounded W c)
    (h1 : c.nreg 1 = b) (h10 : c.nreg 10 = 1) (h43 : c.nreg 43 = Sb) (h45 : c.nreg 45 = t)
    (h46 : c.nreg 46 = (hbT b sz t).1) (h47 : c.nreg 47 = (hbT b sz t).2.1)
    (hG : ∀ t' < b, c.nmem (Sb + 2 * b + t') = Gv b X sz t')
    (hno : ∀ j < t - (hbT b sz t).1 + 1, ¬ GRow (hbT b sz t).2.1 (hbT b sz t).2.2.2
      (Monge.Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) (t - (hbT b sz t).1 - j)) :
    ∃ c' k, Exec P W p2Up c c' k ∧ k ≤ 7 * sz + 14 ∧
      (c'.nreg 57 = Rv b X sz t ∧ (∀ r, r < 55 ∨ 76 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hw := hL.w; have hsd := hL.sd; have hdv := hL.dv
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hbT_mem (b := b) hsz ht hnc
  unfold p2Up
  refine spec_seq ?_
  exec_block
  · rw [h43, h1]; omega
  · config_simp; rw [h43, h1]; omega
  · config_simp; rw [h43, h1, h46]; omega
  · omega
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded W c₂ := hc₂ ▸ ‹_›
  refine spec_seq ?_
  refine spec_use (scanU_exec (P := P) (n := (hbT b sz t).2.1) (A := Sb + b + b + (hbT b sz t).1)
    (S := 1) (f := fun u => Gv b X sz ((hbT b sz t).1 + u)) c₂ hw₂
    (by rw [← hc₂]; config_simp; exact h10) (by rw [← hc₂]; config_simp)
    (by rw [← hc₂]; config_simp; exact h47) (by rw [← hc₂]; config_simp; rw [h43, h1, h46])
    (by rw [← hc₂]; config_simp; exact h10) (by rw [← hc₂]; config_simp; exact h47)
    (fun u hu => by
      rw [← hc₂]; config_simp
      rw [show Sb + b + b + (hbT b sz t).1 + u * 1 = Sb + 2 * b + ((hbT b sz t).1 + u) by ring]
      exact hG _ (by omega))
    (fun u _ => Gv_le _ _) (by omega)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hres, sn, sr, snm, srm, so⟩
  have e : ∀ r, r < 55 ∨ 76 ≤ r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [sn r (by omega) (by omega) (by omega) (by omega), ← hc₂]; config_simp; upd_tac
  have e74 : c₃.nreg 47 = (hbT b sz t).2.1 := by rw [e 47 (by omega), h47]
  have hres' : (c₃.nreg 74 < (hbT b sz t).2.1 ∧ GRow (hbT b sz t).2.1 (hbT b sz t).2.2.2
      (Monge.Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) (c₃.nreg 74) ∧
      ∀ u' < c₃.nreg 74, ¬ GRow (hbT b sz t).2.1 (hbT b sz t).2.2.2
        (Monge.Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) u') ∨
      (c₃.nreg 74 = (hbT b sz t).2.1 ∧ ∀ u' < (hbT b sz t).2.1, ¬ GRow (hbT b sz t).2.1
        (hbT b sz t).2.2.2 (Monge.Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) u') := by
    rcases hres with ⟨h1', h2', h3'⟩ | ⟨h1', h2'⟩
    · refine Or.inl ⟨h1', ?_, fun u' hu' hg => ?_⟩
      · have := Gv_eq (X := X) hsz ht h1'; rw [h2'] at this
        by_contra hc'; rw [ite_eq_right_of_eq_false _ _ (eq_false hc')] at this; omega
      · have := Gv_eq (X := X) hsz ht (show u' < (hbT b sz t).2.1 by omega)
        rw [h3' u' hu', ite_eq_left_of_eq_true _ _ (eq_true hg)] at this; omega
    · refine Or.inr ⟨h1', fun u' hu' hg => ?_⟩
      have := Gv_eq (X := X) hsz ht hu'
      rw [h2' u' hu', ite_eq_left_of_eq_true _ _ (eq_true hg)] at this; omega
  have hRv := repR_of_scan_none hno hres'
  have hRv' : Rv b X sz t = (hbT b sz t).1 + (if c₃.nreg 74 < (hbT b sz t).2.1 then c₃.nreg 74
      else t - (hbT b sz t).1) := by unfold Rv; rw [hRv]
  by_cases hf : c₃.nreg 74 < c₃.nreg 47
  · refine spec_ifLtN_true hf ?_
    refine spec_instr (Exec.addN hw₃ 57 46 74 (by rw [e 46 (by omega), h46]; omega)) fun hw => ?_
    refine ⟨by omega, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · config_simp; rw [hRv', e 46 (by omega), h46]; rw [e74] at hf
      rw [ite_eq_left_of_eq_true _ _ (eq_true hf)]
    · config_simp; rw [upd_other _ _ _ (by omega)]; exact e r hr
    · rw [sr, ← hc₂]
    · rw [snm, ← hc₂]
    · rw [srm, ← hc₂]
    · rw [so, ← hc₂]
  · refine spec_ifLtN_false hf ?_
    refine spec_instr (Exec.copyN hw₃ 57 45) fun hw => ?_
    refine ⟨by omega, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_⟩
    · config_simp; rw [hRv', e 45 (by omega), h45]; rw [e74] at hf
      rw [ite_eq_right_of_eq_false _ _ (eq_false hf)]; omega
    · config_simp; rw [upd_other _ _ _ (by omega)]; exact e r hr
    · rw [sr, ← hc₂]
    · rw [snm, ← hc₂]
    · rw [srm, ← hc₂]
    · rw [so, ← hc₂]

/-- **Pass 2 at a target with sources.** -/
theorem p2Main_exec (hL : LayP b Vb Db Fb Sb W) {sz t : ℕ} (hsz : 0 < sz) (ht : t < b)
    (hnc : 0 < (hbT b sz t).2.2.2) (c : Config) (hc : WordsBounded W c)
    (h1 : c.nreg 1 = b) (h10 : c.nreg 10 = 1) (h43 : c.nreg 43 = Sb) (h45 : c.nreg 45 = t)
    (h46 : c.nreg 46 = (hbT b sz t).1) (h47 : c.nreg 47 = (hbT b sz t).2.1)
    (hG : ∀ t' < b, c.nmem (Sb + 2 * b + t') = Gv b X sz t') :
    ∃ c' k, Exec P W p2Main c c' k ∧ k ≤ 14 * sz + 40 ∧
      ((∀ a, c'.nmem a = if a = Sb + b + t then Rv b X sz t else c.nmem a) ∧
        (∀ r, r < 55 ∨ 76 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hw := hL.w; have hsd := hL.sd; have hdv := hL.dv
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8⟩ := hbT_mem (b := b) hsz ht hnc
  generalize hρ : t - (hbT b sz t).1 = ρ
  unfold p2Main
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h43, h1]; omega
  · config_simp; rw [h43, h1]; omega
  · config_simp; rw [h43, h1, h45]; omega
  · omega
  · config_simp; rw [h45, h46, h10]; omega
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂
  have hw₂ : WordsBounded W c₂ := hc₂ ▸ ‹_›
  have g : ∀ r, r < 55 ∨ 76 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [← hc₂]; config_simp; upd_tac
  have g71 : c₂.nreg 71 = ρ + 1 := by rw [← hc₂]; config_simp; rw [h45, h46, h10, ← hρ]
  refine spec_seq ?_
  refine spec_use (scanD_exec (P := P) (n := ρ + 1) (A := Sb + b + b + t) (S := 1)
    (f := fun j => Gv b X sz (t - j)) c₂ hw₂
    (by rw [g 10 (by omega)]; exact h10) (by rw [← hc₂]; config_simp) g71
    (by rw [← hc₂]; config_simp; rw [h43, h1, h45]) (by rw [← hc₂]; config_simp; exact h10)
    (by rw [← hc₂]; config_simp; rw [h45, h46, h10, ← hρ])
    (fun j hj => by
      rw [← hc₂]; config_simp
      rw [show Sb + b + b + t - j * 1 = Sb + 2 * b + (t - j) by omega]
      exact hG _ (by omega))
    (fun j _ => Gv_le _ _)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hres, sn, sr, snm, srm, so⟩
  have e : ∀ r, r < 55 ∨ 76 ≤ r → c₃.nreg r = c.nreg r := fun r hr => by
    rw [sn r (by omega) (by omega) (by omega) (by omega)]; exact g r hr
  have e71 : c₃.nreg 71 = ρ + 1 := by rw [sn 71 (by omega) (by omega) (by omega) (by omega), g71]
  have hgv : ∀ j < ρ + 1, (Gv b X sz (t - j) = 1 ↔ GRow (hbT b sz t).2.1 (hbT b sz t).2.2.2
      (Monge.Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) (ρ - j)) := fun j hj => by
    have := Gv_eq (X := X) hsz ht (u := ρ - j) (by omega)
    rw [show (hbT b sz t).1 + (ρ - j) = t - j by omega] at this
    rw [this]; split_ifs with h <;> simp [h]
  -- the standing target is in `r57`
  have h57 : ∃ c₄ k₄, Exec P W (.ifLtN 74 71 (.instr (.subN 57 45 74)) p2Up) c₃ c₄ k₄ ∧
      k₄ ≤ 7 * sz + 16 ∧ c₄.nreg 57 = Rv b X sz t ∧ (∀ r, r < 55 ∨ 76 ≤ r → c₄.nreg r = c.nreg r) ∧
      c₄.rreg = c₃.rreg ∧ c₄.nmem = c₃.nmem ∧ c₄.rmem = c₃.rmem ∧ c₄.output = c₃.output := by
    by_cases hf : c₃.nreg 74 < c₃.nreg 71
    · rw [e71] at hf
      have hf' : c₃.nreg 74 < c₃.nreg 71 := by rw [e71]; exact hf
      rcases hres with ⟨h1', h2', h3'⟩ | ⟨h1', -⟩
      · have hR := repR_of_scan_found (m := (hbT b sz t).2.1) (n := (hbT b sz t).2.2.2)
          (F := Monge.Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) (ρ := ρ) (j := c₃.nreg 74)
          (by omega) ((hgv _ h1').1 h2') (fun j hj => fun hg => by
            have := (hgv j (by omega)).2 hg; rw [h3' j hj] at this; omega)
        refine ⟨_, _, Exec.ifLtN_true hf' (Exec.subN hw₃ 57 45 74), by omega, ?_, fun r hr => ?_,
          rfl, rfl, rfl, rfl⟩
        · config_simp; rw [e 45 (by omega), h45]; unfold Rv; rw [← hρ] at hR; rw [hR]; omega
        · config_simp; rw [upd_other _ _ _ (by omega)]; exact e r hr
      · omega
    · have hf' : ¬ c₃.nreg 74 < c₃.nreg 71 := hf
      have hno : ∀ j < t - (hbT b sz t).1 + 1, ¬ GRow (hbT b sz t).2.1 (hbT b sz t).2.2.2
          (Monge.Fb X (hbT b sz t).1 (hbT b sz t).2.2.1) (t - (hbT b sz t).1 - j) := by
        rw [hρ]
        rcases hres with ⟨h1', -⟩ | ⟨-, h2'⟩
        · rw [e71] at hf; omega
        · intro j hj hg; have := (hgv j hj).2 hg; rw [h2' j hj] at this; omega
      obtain ⟨c₄, k₄, hex, hk₄, h57', hn, hr, hnm, hrm, ho⟩ := p2Up_exec (P := P) hL hsz ht hnc c₃
        hw₃ (by rw [e 1 (by omega), h1]) (by rw [e 10 (by omega), h10])
        (by rw [e 43 (by omega), h43]) (by rw [e 45 (by omega), h45])
        (by rw [e 46 (by omega), h46]) (by rw [e 47 (by omega), h47])
        (fun t' ht' => by rw [snm, ← hc₂]; exact hG t' ht') hno
      exact ⟨c₄, k₄ + 2, Exec.ifLtN_false hf' hex, by omega, h57', fun r hr' => by
        rw [hn r hr']; exact e r hr', hr, hnm, hrm, ho⟩
  obtain ⟨c₄, k₄, hex₄, hk₄, h57, hn₄, hr₄, hnm₄, hrm₄, ho₄⟩ := h57
  refine spec_seq ⟨c₄, k₄, hex₄, ?_⟩
  have hw₄ := hex₄.wb_right
  exec_block
  · rw [hn₄ 43 (by omega), h43, hn₄ 1 (by omega), h1]; omega
  · config_simp; rw [hn₄ 43 (by omega), h43, hn₄ 1 (by omega), h1, hn₄ 45 (by omega), h45]; omega
  refine ⟨by omega, fun a => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · config_simp
    rw [upd_apply, hn₄ 43 (by omega), h43, hn₄ 1 (by omega), h1, hn₄ 45 (by omega), h45, h57, hnm₄,
      snm, ← hc₂]
  · config_simp; rw [upd_other _ _ _ (by omega)]; exact hn₄ r hr
  · config_simp; rw [hr₄, sr, ← hc₂]
  · config_simp; rw [hrm₄, srm, ← hc₂]
  · config_simp; rw [ho₄, so, ← hc₂]

/-- **Pass 2 at one target.** -/
theorem p2Body_exec (hL : LayP b Vb Db Fb Sb W) {sz t : ℕ} (hsz : 0 < sz) (hszb : sz ≤ b)
    (c : Config) (hc : WordsBounded W c) (hI : InP b Vb Db Fb Sb X D c) (h44 : c.nreg 44 = sz)
    (h45 : c.nreg 45 = t) (ht : t < b) (hG : ∀ t' < b, c.nmem (Sb + 2 * b + t') = Gv b X sz t') :
    ∃ c' k, Exec P W p2Body c c' k ∧ k ≤ 14 * sz + 60 ∧
      (FrP b Vb Sb c c' ∧ c'.nreg 44 = sz ∧ c'.nreg 45 = t + 1 ∧
        (0 < (hbT b sz t).2.2.2 → c'.nmem (Sb + b + t) = Rv b X sz t) ∧
        (∀ a, a ≠ Sb + b + t → c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem ∧ c'.rreg = c.rreg) := by
  have hw := hL.w; have hsd := hL.sd; have hdv := hL.dv; have hfs := hL.fs
  unfold p2Body
  refine spec_seq ?_
  refine spec_use (bpar_exec (P := P) c hc hI.r1 h44 h45 (by omega)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a46, a47, a48, a49, an, ar, anm, arm, ao⟩
  have e10 : c₁.nreg 10 = 1 := by rw [an 10 (by omega)]; exact hI.r10
  have hpost : ∀ c₂ : Config, WordsBounded W c₂ → (∀ r, r < 55 ∨ 76 ≤ r → c₂.nreg r = c₁.nreg r) →
      c₂.rreg = c₁.rreg → (∀ a, a ≠ Sb + b + t → c₂.nmem a = c₁.nmem a) → c₂.rmem = c₁.rmem →
      c₂.output = c₁.output → (0 < (hbT b sz t).2.2.2 → c₂.nmem (Sb + b + t) = Rv b X sz t) →
      ∃ c' k, Exec P W (.instr (.addN 45 45 10)) c₂ c' k ∧ k = 1 ∧
        (FrP b Vb Sb c c' ∧ c'.nreg 44 = sz ∧ c'.nreg 45 = t + 1 ∧
          (0 < (hbT b sz t).2.2.2 → c'.nmem (Sb + b + t) = Rv b X sz t) ∧
          (∀ a, a ≠ Sb + b + t → c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem ∧
          c'.rreg = c.rreg) := by
    intro c₂ hw₂ hn hr hnm hrm ho hR
    have f45 : c₂.nreg 45 = t := by rw [hn 45 (by omega), an 45 (by omega), h45]
    have f10 : c₂.nreg 10 = 1 := by rw [hn 10 (by omega), e10]
    refine ⟨_, 1, Exec.addN hw₂ 45 45 10 (by rw [f45, f10]; omega), rfl,
      ⟨fun r hr' => ?_, fun r _ => ?_, fun a ha => ?_, fun a _ => ?_, ?_⟩, ?_, ?_, ?_,
      fun a ha => ?_, ?_, ?_⟩
    · config_simp; rw [upd_other _ _ _ (by omega), hn r (by omega), an r (by omega)]
    · config_simp; rw [hr, ar]
    · config_simp; rw [hnm a (by omega), anm]
    · config_simp; rw [hrm, arm]
    · config_simp; rw [ho, ao]
    · config_simp; rw [hn 44 (by omega), an 44 (by omega), h44]
    · config_simp; rw [f45, f10]
    · config_simp; exact hR
    · config_simp; rw [hnm a ha, anm]
    · config_simp; rw [hrm, arm]
    · config_simp; rw [hr, ar]
  refine spec_seq ?_
  by_cases hnc : 0 < (hbT b sz t).2.2.2
  · have hf : ¬ c₁.nreg 49 < c₁.nreg 10 := by rw [a49, e10]; omega
    refine spec_ifLtN_false hf ?_
    obtain ⟨c₂, k₂, hex, hk₂, hnm, hn, hr, hrm, ho⟩ := p2Main_exec (P := P) hL hsz ht hnc c₁ hw₁
      (by rw [an 1 (by omega), hI.r1]) e10 (by rw [an 43 (by omega), hI.r43])
      (by rw [an 45 (by omega), h45]) a46 a47 (fun t' ht' => by rw [anm]; exact hG t' ht')
    obtain ⟨c', k, hex', hk, hp⟩ := hpost c₂ hex.wb_right hn hr
      (fun a ha => by rw [hnm a, ite_eq_right_of_eq_false _ _ (eq_false ha)]) hrm ho
      (fun _ => by rw [hnm, ite_eq_left_of_eq_true _ _ (eq_true rfl)])
    exact ⟨c₂, k₂, hex, c', k, hex', by omega, hp⟩
  · have hf : c₁.nreg 49 < c₁.nreg 10 := by rw [a49, e10]; omega
    refine spec_ifLtN_true hf ?_
    refine spec_skip hw₁ ?_
    obtain ⟨c', k, hex', hk, hp⟩ := hpost c₁ hw₁ (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl rfl
      (fun h => absurd h hnc)
    exact ⟨c', k, hex', by omega, hp⟩

/-- Pass 2 of a level: all the targets. -/
def pass2 : Stmt := .seq (.instr (.constN 45 0)) (.whileLtN 45 1 p2Body)

/-- The state of pass 2 from `c₀`. -/
structure IP2 (b Vb Db Fb Sb W : ℕ) (X : ℕ → ℕ → Prop) (D : ℕ → ℕ → ℤ) (sz : ℕ) (c₀ c : Config) :
    Prop where
  wb : WordsBounded W c
  inp : InP b Vb Db Fb Sb X D c
  frm : FrP b Vb Sb c₀ c
  r44 : c.nreg 44 = sz
  le : c.nreg 45 ≤ b
  rv : ∀ t < c.nreg 45, 0 < (hbT b sz t).2.2.2 → c.nmem (Sb + b + t) = Rv b X sz t
  nmem : ∀ a, (a < Sb + b ∨ Sb + 2 * b ≤ a) → c.nmem a = c₀.nmem a
  rmem : c.rmem = c₀.rmem
  rreg : c.rreg = c₀.rreg

/-- **Pass 2 of a level.** -/
theorem pass2_exec (hL : LayP b Vb Db Fb Sb W) {sz : ℕ} (hsz : 0 < sz) (hszb : sz ≤ b)
    (c : Config) (hc : WordsBounded W c) (hI : InP b Vb Db Fb Sb X D c) (h44 : c.nreg 44 = sz)
    (hG : ∀ t' < b, c.nmem (Sb + 2 * b + t') = Gv b X sz t') :
    ∃ c' k, Exec P W pass2 c c' k ∧ k ≤ (14 * sz + 62) * b + 3 ∧
      (FrP b Vb Sb c c' ∧ InP b Vb Db Fb Sb X D c' ∧ c'.nreg 44 = sz ∧
        (∀ t < b, 0 < (hbT b sz t).2.2.2 → c'.nmem (Sb + b + t) = Rv b X sz t) ∧
        (∀ a, (a < Sb + b ∨ Sb + 2 * b ≤ a) → c'.nmem a = c.nmem a) ∧ c'.rmem = c.rmem ∧
        c'.rreg = c.rreg) := by
  have hw := hL.w
  unfold pass2
  refine spec_seq ?_
  refine spec_instr (Exec.constN hc 45 0 (by omega)) fun hw₁ => ?_
  have hF₁ : FrP b Vb Sb c { c with nreg := upd c.nreg 45 0 } :=
    ⟨fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)], fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl, rfl⟩
  refine spec_while (IP2 b Vb Db Fb Sb W X D sz c) (fun c => (14 * sz + 62) * (b - c.nreg 45))
    (fun c h => h.wb) ?_ ⟨hw₁, hI.of hL hF₁, hF₁, by config_simp; exact h44,
      by config_simp; omega, fun t ht => by config_simp at ht; omega, fun _ _ => rfl, rfl, rfl⟩ ?_
  · intro c₁ hI₁ hlt
    rw [hI₁.inp.r1] at hlt
    generalize ht : c₁.nreg 45 = t at hlt
    obtain ⟨c₂, k, hex, hk, hF, h44', h45', hR, hnm, hrm, hrr⟩ :=
      p2Body_exec (P := P) hL hsz hszb c₁ hI₁.wb hI₁.inp hI₁.r44 ht hlt
        (fun t' ht' => by rw [hI₁.nmem _ (Or.inr (by omega))]; exact hG t' ht')
    refine ⟨c₂, k, hex, ⟨hex.wb_right, hI₁.inp.of hL hF, hI₁.frm.trans hF, h44', by omega,
      fun t' ht' hnc => ?_, fun a ha => ?_, by rw [hrm, hI₁.rmem], by rw [hrr, hI₁.rreg]⟩, ?_⟩
    · rw [h45'] at ht'
      rcases Nat.lt_or_ge t' t with h | h
      · rw [hnm _ (by omega)]; exact hI₁.rv t' (by omega) hnc
      · rw [show t' = t by omega]; exact hR (by rw [show t' = t by omega] at hnc; exact hnc)
    · rw [hnm _ (by omega)]; exact hI₁.nmem a ha
    · have := mul_pred_add (a := 14 * sz + 62) (x := b - t) (by omega)
      rw [show b - t - 1 = b - (t + 1) by omega] at this
      rw [h45']
      omega
  · intro c₂ k₂ hI₂ hn₂ hk₂
    have h45 : c₂.nreg 45 = b := by have := hI₂.le; rw [hI₂.inp.r1] at hn₂; omega
    refine ⟨?_, hI₂.frm, hI₂.inp, hI₂.r44, fun t ht => hI₂.rv t (by omega),
      fun a ha => hI₂.nmem a ha, by rw [hI₂.rmem], by rw [hI₂.rreg]⟩
    beta_reduce at hk₂; config_simp at hk₂; simp only [Nat.sub_zero] at hk₂; omega

end Monge

end PlanarFlow
