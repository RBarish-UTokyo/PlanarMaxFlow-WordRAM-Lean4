module

public import PlanarFlow.Monge.FRCmpAct

/-!
# FR-Dijkstra: bounded comparisons of the whole run

`frProg_good`: from the inputs of `PlanarFlow.Monge.FR.frProg_exec`, bounded by `L`
(`PlanarFlow.Monge.FR.XB`), `frProg` is good (`PlanarFlow.Monge.FR.FG`): every execution started
with every real memory cell bounded by `BB P L = (N + 2) L` compares reals differing by at most
`6 BB P L`, and stores reals bounded by `BB P L`. The stored reals that are not copies of
loaded ones are the distance `κ + p x = dK` of a settled vertex (`hdr_good`, bounded by
`MRun.dist_le`), the key `d x + len e - p y` of an explicit arc (`arcBody_good`), and the items of
the triplets (`PlanarFlow/Monge/FRCmpAct.lean`). The proofs follow the realization lemmas of
`PlanarFlow/Monge/FRSettle.lean`, `FRLoop.lean`, `FRProg.lean` (their runs are the runs, by
`WordRAM.Machine.Exec.det`); the other parts pass the abstract interpretation.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap CmpAbs

variable {P : Prm} {I : Input} {L : ℕ}

/-- **The header of the settling is good**: the stored distance is `κ + p x`. -/
theorem hdr_good {c : Config} {x : ℕ} {κ : ℝ} (hG : Glob P c) (hDa : Data P c)
    (h180 : c.nreg 180 = x) (hx : x < P.N) (hκ : c.rreg 180 = κ)
    (hκB : |κ + (P.p x : ℝ)| ≤ (P.N * L : ℝ)) : FG I P L hdr c := by
  unfold hdr
  refine good_cons (fun _ => trivial) fun c₁ h₁ => ?_
  refine good_cons (fun _ => trivial) fun c₂ h₂ => ?_
  refine good_cons (fun _ => trivial) fun c₃ h₃ => ?_
  refine good_cons (fun _ => trivial) fun c₄ h₄ => ?_
  refine good_cons (fun _ => trivial) fun c₅ h₅ => ?_
  refine good_cons (fun _ => trivial) fun c₆ h₆ => ?_
  refine Good.seq (Good.instr fun _ => ?_) fun _ _ _ => fg_abs0 (by decide)
  simp only [Instr.effect, Option.some.injEq] at h₁ h₂ h₃ h₄ h₅ h₆
  subst h₁ h₂ h₃ h₄ h₅ h₆
  simp only [StOK, upd_apply]
  norm_num
  rw [hκ, hG.r103, h180, hDa.pmem x hx]
  have h0 : (0 : ℝ) ≤ 2 * L := by positivity
  exact hκB.trans (le_trans (le_add_of_nonneg_right h0) (BB_ge (P := P) L))

/-- **One explicit arc is good**: the new key `d x + len e - p y` is bounded. -/
theorem arcBody_good (hL : Lay P) (hXB : XB P L) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ}
    {X : ℕ → ℕ → ℕ → Prop} {x : ℕ} {c₀ : Config} (hx : x < P.N)
    (hκB : |κ + (P.p x : ℝ)| ≤ (P.N * L : ℝ))
    (c : Config) (hI : AI P K v d κ X x c₀ c) (hlt : c.nreg 185 < c.nreg 186) :
    FG I P L arcBody c := by
  obtain ⟨hc, hG, hDa, h180, h186, hlo, hhi, hkN, hkR, hO, hdx, hiN, hS⟩ := hI
  have htb := tb_ge P
  have hw := lay_w hL
  have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6; have := hL.m1
  rw [h186] at hlt
  generalize he : c.nreg 185 = e at hlo hhi hlt hS
  have hm : e < P.m := by
    have := off_mono' hL (x + 1) P.N (by omega) le_rfl; rw [hL.off_last] at this; omega
  have hdst := dst_lt' hL hx hlt
  unfold arcBody
  refine good_seq_ex (fg_abs0 (by decide)) ?_
  exec_block
  · rw [hG.r104, hG.r100]; omega
  · config_simp; rw [hG.r104, hG.r100, hG.r110]; omega
  · config_simp; rw [hG.r104, hG.r100, hG.r110, he]; omega
  · config_simp; rw [hG.r108, h180]; omega
  · config_simp; rw [hG.r105, he]; omega
  · config_simp; rw [hG.r103, hG.r104, hG.r100, hG.r110, he]
    rw [show P.ob + P.N + 1 + e = P.ob + P.N + 1 + e from rfl, hDa.emem e hm]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f175 : c₁.nreg 175 = P.dst e := by
    rw [← hc₁]; config_simp; rw [hG.r104, hG.r100, hG.r110, he]; exact hDa.emem e hm
  have r175 : c₁.rreg 175 = dV P c.rmem x + P.len e - P.p (P.dst e) := by
    rw [← hc₁]; config_simp
    rw [hG.r108, h180, hG.r105, he, hG.r103, hG.r104, hG.r100, hG.r110, hDa.emem e hm,
      hDa.lmem e hm, hDa.pmem _ hdst]
    unfold dV; rw [Nat.add_comm P.db x]
  refine Good.seq (fg_abs (A := [(175, 1)]) (by decide) fun _ => regA_one ?_)
    fun _ _ _ => fg_abs0 (by decide)
  rw [r175, hdx]
  have h1 := hXB.len e hm
  have h2 := hXB.p (P.dst e) hdst
  have h1' : |(P.len e : ℝ)| ≤ L := by exact_mod_cast h1
  have h2' : |(P.p (P.dst e) : ℝ)| ≤ L := by exact_mod_cast h2
  have h3 := abs_sub (κ + P.p x + P.len e) (P.p (P.dst e) : ℝ)
  have h4 := abs_add_le (κ + P.p x) (P.len e : ℝ)
  calc |κ + P.p x + P.len e - P.p (P.dst e)|
      ≤ P.N * L + 2 * L := by linarith
    _ ≤ _ := BB_ge L

/-- **The explicit arcs are good.** -/
theorem arcs_good (hL : Lay P) (hXB : XB P L) (hF : Feas P) {K : ℕ} {v : ℕ → ℕ} {d : ℕ → ℤ}
    {κ : ℝ} {X : ℕ → ℕ → ℕ → Prop} {x i : ℕ} (hx : x < P.N) (hi : i < K) (hvi : v i = x)
    (hκB : |κ + (P.p x : ℝ)| ≤ (P.N * L : ℝ))
    (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c) (hDa : Data P c)
    (h180 : c.nreg 180 = x) (hdx : dV P c.rmem x = κ + P.p x)
    (hS : MSt P K v d κ F2 F1 (arcEx x (P.off x)) X c.nmem c.rmem) :
    FG I P L (.seq (block [.addN 187 104 180, .loadN 185 187, .addN 187 187 110,
      .loadN 186 187]) (.whileLtN 185 186 arcBody)) c := by
  have htb := tb_ge P
  have hw := lay_w hL
  have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have hmono := off_mono' hL x (x + 1) (by omega) (by omega)
  refine good_seq_ex (fg_abs0 (by decide)) ?_
  exec_block
  · rw [hG.r104, h180]; omega
  · config_simp; rw [hG.r104, h180, hG.r110]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f185 : c₁.nreg 185 = P.off x := by
    rw [← hc₁]; config_simp; rw [hG.r104, h180]; exact hDa.omem x hx.le
  have f186 : c₁.nreg 186 = P.off (x + 1) := by
    rw [← hc₁]; config_simp; rw [hG.r104, h180, hG.r110, Nat.add_assoc]
    exact hDa.omem (x + 1) hx
  have fK : ∀ r, r ≠ 185 → r ≠ 186 → r ≠ 187 → c₁.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fR : c₁.rreg = c.rreg := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have hI₁ : AI P K v d κ X x c c₁ :=
    ⟨hw₁, hG.of fun r h1 h2 => fK r (by omega) (by omega) (by omega),
      hDa.of hL (fun _ _ => by rw [fN]) (fun _ _ => by rw [fM]),
      by rw [fK 180 (by omega) (by omega) (by omega), h180], f186, by rw [f185],
      by rw [f185]; exact hmono, fun r hr => fK r (by omega) (by omega) (by omega),
      fun r _ => by rw [fR], fO, by rw [fM]; exact hdx, fun a _ => by rw [fN],
      by rw [f185, fN, fM]; exact hS⟩
  exact Good.whileLtN (AI P K v d κ X x c) (fun c' hI hlt =>
    ⟨arcBody_good hL hXB hx hκB c' hI hlt, fun c₂ k₂ e₂ => by
      obtain ⟨c'', k'', e'', hI'', -⟩ := arcBody_exec (I := I) hL hF hx hi hvi c' hI hlt
      obtain ⟨rfl, rfl⟩ := Exec.det e'' e₂
      exact hI''⟩) hI₁


/-- **One level of the settling is good.** -/
theorem lvl_good (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D) (hF : Feas P) {K : ℕ}
    {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {X : ℕ → ℕ → ℕ → Prop} {x t₀ : ℕ} {c₀ : Config}
    (hx : x < P.b) (hDB : ∀ i < K, |(d i : ℝ)| ≤ (P.N * L : ℝ))
    (c : Config) (hI : LI P K v d κ X x c₀ t₀ c) (hlt : c.nreg 182 < c.nreg 101) :
    FG I P L lvl c := by
  obtain ⟨hc, hG, hX, hDa, h180, h182, h181, h284, h285, htle, hkN, hkR, hO, hsx, hdx, hS⟩ := hI
  rw [h182, hG.r101] at hlt
  have ht := hlt
  have hLv := lt_Lv' ht
  have hs1 : 1 ≤ 2 ^ t₀ := Nat.one_le_two_pow
  have hw := hL.wx
  have hw0 := hL.w
  have hbN := hL.bN
  have hbTB := lt_two_pow_TB P
  have hbw := bh_le_W hL
  have hdvx : x / 2 ^ t₀ * 2 ^ t₀ ≤ x := Nat.div_mul_le_self x _
  have hdx' : x / 2 ^ t₀ ≤ x := Nat.div_le_self x _
  have hlt2 := Nat.lt_div_mul_add (a := x) (b := 2 ^ t₀) (by omega)
  have hsib : sib (x / 2 ^ t₀) * 2 ^ t₀ ≤ x + 2 ^ t₀ := by
    have := Nat.mul_le_mul_right (2 ^ t₀) (sib_le (x / 2 ^ t₀))
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  unfold lvl
  refine good_seq_ex (fg_abs0 (by decide)) ?_
  exec_block
  · config_simp; rw [h180, h182]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f183 : c₁.nreg 183 = x / 2 ^ t₀ := by rw [← hc₁]; config_simp; rw [h180, h182]
  have f189 : c₁.nreg 189 = x / 2 ^ t₀ % 2 := by
    rw [← hc₁]; config_simp; rw [h180, h182, hG.r111]
  have f260 : c₁.nreg 260 = x - x / 2 ^ t₀ * 2 ^ t₀ := by
    rw [← hc₁]; config_simp; rw [h180, h182]
  have fK : ∀ r, r ≠ 183 → r ≠ 189 → r ≠ 260 → c₁.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fR : c₁.rreg = c.rreg := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have k110 : c₁.nreg 110 = 1 := (fK 110 (by omega) (by omega) (by omega)).trans hG.r110
  refine good_seq_ex (fg_abs0 (by decide)) ?_
  obtain ⟨c₂, k₂, e₂, hk₂, g183, gK, gR, gN, gM, gO⟩ : ∃ c₂ k₂, Exec I P.W
      (.ifLtN 189 110 (.instr (.addN 183 183 110)) (.instr (.subN 183 183 110))) c₁ c₂ k₂ ∧
      k₂ ≤ 3 ∧ c₂.nreg 183 = sib (x / 2 ^ t₀) ∧ (∀ r, r ≠ 183 → c₂.nreg r = c₁.nreg r) ∧
      c₂.rreg = c₁.rreg ∧ c₂.nmem = c₁.nmem ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases hp : x / 2 ^ t₀ % 2 = 0
    · refine spec_ifLtN_true (by rw [f189, k110]; omega) ?_
      refine spec_instr (Exec.addN hw₁ 183 183 110 (by rw [f183, k110]; omega)) fun _ =>
        ⟨by omega, ?_, fun r hr => by config_simp; upd_tac, rfl, rfl, rfl, rfl⟩
      config_simp; rw [f183, k110]; unfold sib; simp [hp]
    · refine spec_ifLtN_false (by rw [f189, k110]; omega) ?_
      refine spec_instr (Exec.subN hw₁ 183 183 110) fun _ =>
        ⟨by omega, ?_, fun r hr => by config_simp; upd_tac, rfl, rfl, rfl, rfl⟩
      config_simp; rw [f183, k110]; unfold sib; simp [hp]
  refine ⟨c₂, k₂, e₂, ?_⟩
  have hw₂ := e₂.wb_right
  have l182 : c₂.nreg 182 = 2 ^ t₀ := by
    rw [gK 182 (by omega), fK 182 (by omega) (by omega) (by omega), h182]
  refine good_seq_instr (Exec.mulN hw₂ 187 183 182 (by rw [g183, l182]; omega)) (fun _ => trivial)
    fun hw₃ => ?_
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃ at hw₃ ⊢
  have f187 : c₃.nreg 187 = sib (x / 2 ^ t₀) * 2 ^ t₀ := by
    rw [← hc₃]; config_simp; rw [g183, l182]
  have k3 : ∀ r, r ≠ 183 → r ≠ 187 → r ≠ 189 → r ≠ 260 → c₃.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => by
      rw [← hc₃]; config_simp; rw [upd_other _ _ _ h2, gK r h1, fK r h1 h3 h4]
  have e3N : c₃.nmem = c.nmem := by rw [← hc₃]; config_simp; rw [gN, fN]
  have e3M : c₃.rmem = c.rmem := by rw [← hc₃]; config_simp; rw [gM, fM]
  have e3R : c₃.rreg = c.rreg := by rw [← hc₃]; config_simp; rw [gR, fR]
  have e3O : c₃.output = c.output := by rw [← hc₃]; config_simp; rw [gO, fO]
  have g3 : c₃.nreg 183 = sib (x / 2 ^ t₀) := by rw [← hc₃]; config_simp; exact g183
  have g3' : c₃.nreg 260 = x - x / 2 ^ t₀ * 2 ^ t₀ := by
    rw [← hc₃]; config_simp; rw [gK 260 (by omega)]; exact f260
  have hG₃ : Glob P c₃ := hG.of fun r h1 h2 => k3 r (by omega) (by omega) (by omega) (by omega)
  have hX₃ : GX P c₃ := hX.of fun r h1 h2 => k3 r (by omega) (by omega) (by omega) (by omega)
  have hDa₃ : Data P c₃ := hDa.of hL (fun a _ => by rw [e3N]) (fun a _ => by rw [e3M])
  have hLvb : P.Lv * P.b < 2 ^ P.TB := by have := lt_two_pow_TB P; rw [Nat.mul_comm]; exact this
  have hlvb : (t₀ + 1) * P.b ≤ P.Lv * P.b := Nat.mul_le_mul_right _ hLv
  have hl8 : 8 * P.b * P.Lv * (t₀ + 1) ≤ 8 * P.b * P.Lv * P.Lv := Nat.mul_le_mul_left _ hLv
  have hl32 : 32 * P.b * (t₀ + 1) ≤ 32 * P.b * P.Lv := Nat.mul_le_mul_left _ hLv
  have hbhW : P.bh ≤ P.W := by unfold Prm.rb at hw; omega
  have hbhe : P.bh = P.tb + 32 * P.b * P.Lv := rfl
  have h8e : 8 * P.b * P.Lv * (t₀ + 1) = 8 * P.b * P.Lv * t₀ + 8 * P.b * P.Lv := by ring
  have h32e : 32 * P.b * (t₀ + 1) = 32 * P.b * t₀ + 32 * P.b := by ring
  have hbe' : (t₀ + 1) * P.b = t₀ * P.b + P.b := by ring
  have hTBW : 2 ^ P.TB ≤ P.W := by omega
  refine Good.seq ?_ fun _ _ _ => fg_abs0 (by decide)
  by_cases hk : sib (x / 2 ^ t₀) * 2 ^ t₀ < P.b
  · generalize hk₀ : sib (x / 2 ^ t₀) = k₀ at hk g3 f187
    have hsk : sib k₀ = x / 2 ^ t₀ := by rw [← hk₀, sib_sib]
    have hnc0 : hbNc P.b (2 ^ t₀) k₀ ≤ 2 ^ t₀ := hbNc_le
    have hσx : x - x / 2 ^ t₀ * 2 ^ t₀ < hbNc P.b (2 ^ t₀) k₀ := by
      unfold hbNc; rw [hsk]; omega
    have hsrc : sib k₀ * 2 ^ t₀ + (x - x / 2 ^ t₀ * 2 ^ t₀) = x := by rw [hsk]; omega
    have hB := hS.blk t₀ k₀ ht hk
    refine good_ifLtN_true (by rw [f187, hG₃.r101]; exact hk) ?_
    refine good_seq_use (ctxW_exec (I := I) (s := 2 ^ t₀) (k := k₀) (LB := P.rb + 8 * P.b * P.Lv * t₀)
      (m := 4 * P.Lv) hL c₃ hw₃ hG₃
      (by rw [k3 182 (by omega) (by omega) (by omega) (by omega)]; exact h182) g3
      (by rw [k3 181 (by omega) (by omega) (by omega) (by omega)]; exact h181) hX₃.r245
      (by omega) (by omega) hk hs1 ht.le
      (by have := rbB_le_W hL ht hk; unfold rbB at this; omega)) (fg_abs0 (by decide)) ?_
    intro c₄ k₄ hk₄ hw₄ ⟨hH₄, h189₄, hK₄, hR₄, hN₄, hM₄, hO₄⟩
    have k4 : ∀ r, (r < 120 ∨ 126 ≤ r) → r ≠ 189 → r ≠ 183 → r ≠ 187 → r ≠ 260 →
        c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 h5 => by
      rw [hK₄ r h1 h2]; exact k3 r h3 h4 h2 h5
    have hG₄ : Glob P c₄ := hG.of fun r h1 h2 => k4 r (by omega) (by omega) (by omega) (by omega)
      (by omega)
    refine good_seq_use (tctx_exec (I := I) (TB := P.tb + 32 * P.b * t₀) c₄ hw₄ hG₄ hH₄
      (by rw [k4 284 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h284)
      (by have := tbQ_le_bh ht hk; unfold tbQ at this; omega)) (fg_abs0 (by decide)) ?_
    intro c₅ k₅ hk₅ hw₅ ⟨hT₅, hF₅, hN₅, hM₅⟩
    have k5 : ∀ r, r ≠ 208 → r ≠ 209 → c₅.nreg r = c₄.nreg r := fun r h1 h2 => hF₅.n r (by omega)
    have e5N : c₅.nmem = c.nmem := by rw [hN₅, hN₄, e3N]
    have e5M : c₅.rmem = c.rmem := by rw [hM₅, hM₄, e3M]
    have hG₅ : Glob P c₅ := hG₄.of fun r h1 h2 => k5 r (by omega) (by omega)
    have hX₅ : GX P c₅ := hX.of fun r h1 h2 => by
      rw [k5 r (by omega) (by omega)]; exact k4 r (by omega) (by omega) (by omega) (by omega)
        (by omega)
    have hDa₅ : Data P c₅ := hDa.of hL (fun a _ => by rw [e5N]) (fun a _ => by rw [e5M])
    have hH₅ : HCtx P (rbB P t₀ k₀) (2 ^ t₀) k₀ c₅ := hH₄.of fun r h1 h2 => k5 r (by omega)
      (by omega)
    have hT₅' : TCtx (tbQ P t₀ k₀) (2 ^ t₀) c₅ := by unfold tbQ; exact hT₅
    -- the entries of the half block
    have hA : AntiM (hbNr P.b (2 ^ t₀) k₀) (hbNc P.b (2 ^ t₀) k₀)
        (fun ρ σ => hbe P c₅.rmem t₀ k₀ σ + hbF P.b P.D P.p (2 ^ t₀) k₀ ρ σ) := by
      have h := (antiM_hbF hDc P.p hk).add_col (hbe P c₅.rmem t₀ k₀)
      exact fun ρ ρ' σ σ' h1 h2 h3 h4 => h ρ ρ' σ σ' h1 (lt_of_lt_of_le h2 (Nat.min_le_left _ _))
        h3 h4
    have hna : ¬ hbAct P (pend x t₀) c₅.nmem t₀ k₀ (x - x / 2 ^ t₀ * 2 ^ t₀) := fun h =>
      h.2.2 ⟨hsrc, le_rfl⟩
    have hκ : ∀ ρ < hbNr P.b (2 ^ t₀) k₀, κ ≤ hbe P c₅.rmem t₀ k₀ (x - x / 2 ^ t₀ * 2 ^ t₀) +
        hbF P.b P.D P.p (2 ^ t₀) k₀ ρ (x - x / 2 ^ t₀ * 2 ^ t₀) := by
      intro ρ hρ
      have hρs : ρ < 2 ^ t₀ := lt_of_lt_of_le hρ (Nat.min_le_left _ _)
      have hyb : k₀ * 2 ^ t₀ + ρ < P.b := by unfold hbNr at hρ; omega
      have hne : x ≠ k₀ * 2 ^ t₀ + ρ := by
        rw [← hsrc]; exact src_ne_tgt (by omega) hρs
      have hfe := hF x (k₀ * 2 ^ t₀ + ρ) (P.D x (k₀ * 2 ^ t₀ + ρ)) (Or.inl ⟨hx, hyb, hne, rfl⟩)
      unfold hbe; rw [hsrc, e5M, hdx, hbF_live hyb, hsrc]
      have : ((P.p (k₀ * 2 ^ t₀ + ρ) : ℤ) : ℝ) ≤ P.p x + P.D x (k₀ * 2 ^ t₀ + ρ) := by
        exact_mod_cast hfe
      push_cast; linarith
    obtain ⟨own, hrep⟩ := hB.rep
    rw [← e5N, ← e5M] at hrep
    have hEB : ∀ σ, hbAct P (pend x t₀) c₅.nmem t₀ k₀ σ → |hbe P c₅.rmem t₀ k₀ σ| ≤ (P.N * L : ℝ) :=
      fun σ hσ => by
        unfold hbe; rw [e5N] at hσ; rw [e5M]
        exact hS.dV_le hDB (src_lt_N hL hσ.1) hσ.2.1
    have heA : |hbe P c₅.rmem t₀ k₀ (x - x / 2 ^ t₀ * 2 ^ t₀)| ≤ (P.N * L : ℝ) := by
      unfold hbe; rw [hsrc, e5M]; exact hS.dV_le hDB (by have := hL.bN; omega) hsx
    exact blkStep_good hL hXB (κ := κ) ht hk c₅ hw₅ ⟨hG₅, hH₅, hDa₅⟩
        hT₅' (by rw [k5 260 (by omega) (by omega), hK₄ 260 (by omega) (by omega)]; exact g3')
        (by rw [e5N]; exact hB.ready (by omega))
        (fun σ _ => rfl) hA hna hσx hκ (hrep.imp id fun h => ⟨h.1, h.2.1⟩) hEB heA
  · refine good_ifLtN_false (by rw [f187, hG₃.r101]; exact hk) ?_
    exact Good.skip


/-- **Settling a vertex is good**: its stored distance `κ + p x = dK` is bounded. -/
theorem settle_good (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D) (hF : Feas P) {K : ℕ}
    {v : ℕ → ℕ} {d : ℕ → ℤ} {κ : ℝ} {xe : ℕ → Prop} {X : ℕ → ℕ → ℕ → Prop} {dK : ℤ}
    (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c) (hX : GX P c) (hDa : Data P c)
    (hS : MSt P K v d κ F2 xe F2 X c.nmem c.rmem) (hx : c.nreg 180 < P.N)
    (hsx : sfV P c.nmem (c.nreg 180) = 0) (hxe : ∀ y, xe y → y = c.nreg 180)
    (hκ : c.rreg 180 = κ) (hdK : κ = ((dK - P.p (c.nreg 180) : ℤ) : ℝ))
    (hDB : ∀ i < K, |(d i : ℝ)| ≤ (P.N * L : ℝ)) (hdKB : |(dK : ℝ)| ≤ (P.N * L : ℝ)) :
    FG I P L settle c := by
  have hw := lay_w hL
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have htb := tb_ge P
  generalize hx' : c.nreg 180 = x at hx hsx hxe hdK ⊢
  have hκB : |κ + (P.p x : ℝ)| ≤ (P.N * L : ℝ) := by
    rw [hdK]; push_cast; simpa using hdKB
  unfold settle
  refine good_seq_ex (hdr_good hG hDa hx' hx hκ hκB) ?_
  exec_block
  · rw [hG.r109, hx']; omega
  · config_simp; rw [hG.r103, hx']; omega
  · config_simp; rw [hG.r108, hx']; omega
  · config_simp; rw [hG.r107, hx']; omega
  · config_simp; rw [hG.r100, hx']; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f170 : c₁.nreg 170 = (P.N + x) / 2 := by
    rw [← hc₁]; config_simp; rw [hG.r100, hx', hG.r111]
  have fK : ∀ r, r ≠ 170 → r ≠ 187 → c₁.nreg r = c.nreg r := fun r h1 h2 => by
    rw [← hc₁]; config_simp; upd_tac
  have fR : ∀ r, r ≠ 181 → c₁.rreg r = c.rreg r := fun r h1 => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : ∀ a, c₁.nmem a =
      if a = P.sb + x then 1 else if a = P.wb + x then 0 else c.nmem a := fun a => by
    rw [← hc₁]; config_simp; rw [hG.r109, hx', hG.r107, hG.r117, hG.r110]
    simp only [upd_apply]
  have fM : ∀ a, c₁.rmem a = if a = P.db + x then κ + P.p x else c.rmem a := fun a => by
    rw [← hc₁]; config_simp; rw [hG.r103, hx', hG.r108, hDa.pmem x hx, hκ]
    simp only [upd_apply]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => fK r (by omega) (by omega)
  have epr : ∀ y, y ≠ x → prV P c₁.nmem y = prV P c.nmem y := fun y hy => by
    unfold prV; rw [fN]; split_ifs <;> first | rfl | omega
  have ekey : ∀ y, y ≠ x → keyV P c₁.rmem y = keyV P c.rmem y := fun y hy => by
    unfold keyV; rw [fM]; split_ifs <;> first | rfl | omega
  have hW₁ : WinOK P.N (prV P c₁.nmem) (keyV P c₁.rmem) (wnV P c₁.nmem) ((P.N + x) / 2) :=
    (hS.hp.win.set epr ekey).congr_wn fun i h1 h2 => by
      unfold wnV; rw [fN]; split_ifs <;> first | rfl | omega
  have hpr₁ : ∀ y < P.N, prV P c₁.nmem y ≤ 1 := fun y hy => by
    by_cases hyx : y = x
    · subst hyx; unfold prV; rw [fN]; split_ifs <;> omega
    · rw [epr y hyx]; exact hS.hp.pr_le y hy
  refine good_seq_use (hpUp_exec (I := I) hL c₁ hw₁ hG₁ (by rw [f170]; omega) hpr₁
    (by rw [f170]; exact hW₁)) (fg_abs0 (by decide)) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hW₂, hK₂, hR₂, hO₂, hN₂, hM₂⟩
  rw [f170] at hk₂
  have hlg : lg ((P.N + x) / 2) ≤ lg P.N := lg_mono (by omega)
  have hW₂' : WinOK P.N (prV P c₂.nmem) (keyV P c₂.rmem) (wnV P c₂.nmem) 0 :=
    hW₂.congr (fun y hy => by unfold prV; rw [hN₂ _ (Or.inl (by omega))])
      (fun y hy => by unfold keyV; rw [hM₂])
  have hS₂ := hS.header hL (dK := dK) (nm₂ := c₂.nmem) (rm₂ := c₂.rmem) hx hsx hxe
    (by rw [hN₂ _ (Or.inl (by omega)), fN]; simp only [↓reduceIte])
    (by rw [hN₂ _ (Or.inl (by omega)), fN]; split_ifs <;> first | rfl | omega)
    (by rw [hM₂, fM]; simp only [↓reduceIte]; rw [hdK]; push_cast; ring)
    (fun a h1 h2 h3 => by rw [hN₂ a h3, fN]; split_ifs <;> first | rfl | omega)
    (fun a h1 => by rw [hM₂, fM]; split_ifs <;> first | rfl | omega) hW₂'
  have g180 : c₂.nreg 180 = x := by rw [hK₂ 180 (by omega), fK 180 (by omega) (by omega), hx']
  have hG₂ : Glob P c₂ := hG₁.of fun r h1 h2 => hK₂ r (by omega)
  have hX₂ : GX P c₂ := hX.of fun r h1 h2 => by
    rw [hK₂ r (by omega)]; exact fK r (by omega) (by omega)
  have hDa₂ : Data P c₂ := hDa.of hL
    (fun a ha => by rw [hN₂ a (Or.inl (by omega)), fN]; split_ifs <;> first | rfl | omega)
    (fun a ha => by rw [hM₂, fM]; split_ifs <;> first | rfl | omega)
  have hxs₂ : sfV P c₂.nmem x = 1 := by
    unfold sfV; rw [hN₂ _ (Or.inl (by omega)), fN]; simp only [↓reduceIte]
  have hdx₂ : dV P c₂.rmem x = κ + P.p x := by
    unfold dV; rw [hM₂, fM]; simp only [↓reduceIte]
  have hhi₂ : ∀ a, P.tb ≤ a → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hN₂ a (Or.inr (by omega)), fN]; split_ifs <;> first | rfl | omega
  have hpot₂ : potN P c₂.nmem = potN P c.nmem := potN_congr fun t k ht hk y hy => by
    have := tb_le_tbQ (P := P) (t := t) (k := k); unfold tPr; exact hhi₂ _ (by omega)
  -- the levels
  obtain ⟨c₃, k₃, e₃, hk₃, hG₃, hDa₃, h180₃, hK₃, hR₃, hO₃, hX₃, hdx₃, hS₃⟩ : ∃ c₃ k₃,
      Exec I P.W (.ifLtN 180 101 lvls .skip) c₂ c₃ k₃ ∧
      k₃ + potN P c₃.nmem ≤ (if x < P.b then P.Lv * lvC P + 7 else 2) + potN P c₂.nmem ∧
      Glob P c₃ ∧ Data P c₃ ∧ c₃.nreg 180 = x ∧ (∀ r < 100, c₃.nreg r = c₂.nreg r) ∧
      (∀ r < 100, c₃.rreg r = c₂.rreg r) ∧ c₃.output = c₂.output ∧ GX P c₃ ∧
      dV P c₃.rmem x = κ + P.p x ∧
      MSt P (K + 1) (Function.update v K x) (Function.update d K dK) κ F2 F1
        (arcEx x (P.off x)) X c₃.nmem c₃.rmem := by
    by_cases hxb : x < P.b
    · refine spec_ifLtN_true (by rw [g180, hG₂.r101]; exact hxb) ?_
      unfold lvls
      refine spec_seq ?_
      exec_block
      · exact Nat.zero_le _
      generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
      have hw₄ : WordsBounded P.W c₄ := hc₄ ▸ ‹_›
      have fK4 : ∀ r, r ≠ 181 → r ≠ 182 → r ≠ 284 → r ≠ 285 → c₄.nreg r = c₂.nreg r :=
        fun r h1 h2 h3 h4 => by rw [← hc₄]; config_simp; upd_tac
      have hI₄ : LI P (K + 1) (Function.update v K x) (Function.update d K dK) κ X x c₂ 0 c₄ :=
        ⟨hw₄, hG₂.of fun r h1 h2 => fK4 r (by omega) (by omega) (by omega) (by omega),
          hX₂.of fun r h1 h2 => fK4 r (by omega) (by omega) (by omega) (by omega),
          hDa₂.of hL (fun a _ => by rw [← hc₄]) (fun a _ => by rw [← hc₄]),
          by rw [fK4 180 (by omega) (by omega) (by omega) (by omega)]; exact g180,
          by rw [← hc₄]; config_simp; rw [hG₂.r110]; rfl,
          by rw [← hc₄]; config_simp; rw [hX₂.r246]; ring,
          by rw [← hc₄]; config_simp; rw [hX₂.r240]; ring,
          by rw [← hc₄]; config_simp; ring, Nat.zero_le _,
          fun r hr => fK4 r (by omega) (by omega) (by omega) (by omega),
          fun r _ => by rw [← hc₄], by rw [← hc₄], by rw [← hc₄]; exact hxs₂,
          by rw [← hc₄]; exact hdx₂, by rw [← hc₄]; exact hS₂⟩
      obtain ⟨t₁, c₅, k₅, e₅, hI₅, hn₅, hk₅⟩ := whileLtN_ghost_pot (P' := I) (W := P.W)
        (a := 182) (b := 101) (body := lvl)
        (LI P (K + 1) (Function.update v K x) (Function.update d K dK) κ X x c₂)
        (fun t c => potN P c.nmem + (P.Lv - t) * lvC P) (fun _ _ h => h.wb)
        (fun t c hI hlt => by
          obtain ⟨c', k', e, h1, h2⟩ := lvl_exec hL hDc hF hxb c hI hlt
          exact ⟨t + 1, c', k', e, h1, h2⟩) hI₄
      refine ⟨c₅, k₅, e₅, ?_⟩
      rw [hI₅.r182, hI₅.glob.r101] at hn₅
      have hS₅ := hI₅.si.pend_end (Or.inl hn₅)
      have e4N : c₄.nmem = c₂.nmem := by rw [← hc₄]
      refine ⟨?_, hI₅.glob, hI₅.data, hI₅.r180, hI₅.keepN, hI₅.keepR, hI₅.out, hI₅.gx, hI₅.dx,
        hS₅⟩
      rw [iteT hxb, ← e4N]
      have : (P.Lv - 0) * lvC P = P.Lv * lvC P := by rw [Nat.sub_zero]
      rw [this] at hk₅
      omega
    · refine spec_ifLtN_false (by rw [g180, hG₂.r101]; exact hxb) ?_
      refine spec_skip hw₂ ⟨?_, hG₂, hDa₂, g180, fun _ _ => rfl, fun _ _ => rfl, rfl, hX₂,
        hdx₂, hS₂.pend_end (Or.inr hxb)⟩
      rw [iteF hxb]
  have hdB' : ∀ i < K + 1, |((Function.update d K dK i : ℤ) : ℝ)| ≤ (P.N * L : ℝ) := by
    intro i hi
    rcases Nat.lt_or_ge i K with h | h
    · rw [Function.update_of_ne (by omega)]; exact hDB i h
    · rw [show i = K by omega, Function.update_self]; exact hdKB
  refine good_seq_ex ?_ ⟨c₃, k₃, e₃, ?_⟩
  · by_cases hxb : x < P.b
    · refine good_ifLtN_true (by rw [g180, hG₂.r101]; exact hxb) ?_
      unfold lvls
      refine good_seq_ex (fg_abs0 (by decide)) ?_
      exec_block
      · exact Nat.zero_le _
      generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄
      have hw₄ : WordsBounded P.W c₄ := hc₄ ▸ ‹_›
      have fK4 : ∀ r, r ≠ 181 → r ≠ 182 → r ≠ 284 → r ≠ 285 → c₄.nreg r = c₂.nreg r :=
        fun r h1 h2 h3 h4 => by rw [← hc₄]; config_simp; upd_tac
      have hI₄ : LI P (K + 1) (Function.update v K x) (Function.update d K dK) κ X x c₂ 0 c₄ :=
        ⟨hw₄, hG₂.of fun r h1 h2 => fK4 r (by omega) (by omega) (by omega) (by omega),
          hX₂.of fun r h1 h2 => fK4 r (by omega) (by omega) (by omega) (by omega),
          hDa₂.of hL (fun a _ => by rw [← hc₄]) (fun a _ => by rw [← hc₄]),
          by rw [fK4 180 (by omega) (by omega) (by omega) (by omega)]; exact g180,
          by rw [← hc₄]; config_simp; rw [hG₂.r110]; rfl,
          by rw [← hc₄]; config_simp; rw [hX₂.r246]; ring,
          by rw [← hc₄]; config_simp; rw [hX₂.r240]; ring,
          by rw [← hc₄]; config_simp; ring, Nat.zero_le _,
          fun r hr => fK4 r (by omega) (by omega) (by omega) (by omega),
          fun r _ => by rw [← hc₄], by rw [← hc₄], by rw [← hc₄]; exact hxs₂,
          by rw [← hc₄]; exact hdx₂, by rw [← hc₄]; exact hS₂⟩
      exact good_whileLtN_ghost (fun t c => LI P (K + 1) (Function.update v K x)
          (Function.update d K dK) κ X x c₂ t c)
        (fun t c hI hlt => ⟨lvl_good hL hXB hDc hF hxb hdB' c hI hlt, by
          obtain ⟨c', k', e, h1, -⟩ := lvl_exec (I := I) hL hDc hF hxb c hI hlt
          exact ⟨c', k', e, t + 1, h1⟩⟩) hI₄
    · refine good_ifLtN_false (by rw [g180, hG₂.r101]; exact hxb) ?_
      exact Good.skip
  · exact arcs_good hL hXB hF hx (i := K) (by omega) (Function.update_self ..) hκB c₃ e₃.wb_right
      hG₃ hDa₃ h180₃ hdx₃ hS₃


/-- **Settling the root of the heap of the vertices is good.** -/
theorem vPop_good (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D) (hF : Feas P) {K : ℕ} {v : ℕ → ℕ}
    {d : ℕ → ℤ} {κ : ℝ} {X : ℕ → ℕ → ℕ → Prop} (c : Config) (hc : WordsBounded P.W c)
    (hG : Glob P c) (hX : GX P c) (hDa : Data P c) (hS : MSt P K v d κ F2 F1 F2 X c.nmem c.rmem)
    (hR : MRun P K v d) (h180 : c.nreg 180 = wnV P c.nmem 1)
    (hpx : prV P c.nmem (wnV P c.nmem 1) = 1) (hk180 : c.rreg 180 = keyV P c.rmem (wnV P c.nmem 1))
    (hb : ∀ w < 2 ^ P.TB, tPr P.bh c.nmem w = 1 → keyV P c.rmem (wnV P c.nmem 1) ≤
      tKey P.bh c.rmem w) :
    FG I P L settle c := by
  have hw := lay_w hL
  have hW := hS.hp.win
  have hx := (hW.under 1 le_rfl (by omega)).1
  have hmin := (win_root hW (by omega)).2
  generalize hxv : wnV P c.nmem 1 = x at hx hpx hmin h180 hk180 hb ⊢
  have hsx : sfV P c.nmem x = 0 := hS.hp.pr_sf x hx hpx
  have hnv : ∀ j < K, v j ≠ x := fun j hj e => by
    have := (hS.gh.sf x hx).2 ⟨j, hj, e⟩; omega
  -- the raised state
  have hS' := hS.raise (hS.kmin x hx hpx) (fun z hz hpz => (hmin z hz hpz).2) hb
  have hleast := hS.least hL (κ' := keyV P c.rmem x) (fun z hz hpz => (hmin z hz hpz).2) hb
  -- the key of `x` is justified
  obtain ⟨dK, hdK, hroot, hpar⟩ : ∃ dK : ℤ, keyV P c.rmem x = ((dK - P.p x : ℤ) : ℝ) ∧
      (K = 0 → x = P.r ∧ dK = 0) ∧
      (0 < K → ∃ i < K, ∃ ℓ, IsArc P (v i) x ℓ ∧ dK = d i + ℓ) := by
    rcases hS.gh.just x hx hpx with ⟨rfl, hk⟩ | ⟨i, hi, ℓ, ha, hk⟩
    · refine ⟨0, by rw [hk]; push_cast; ring, fun _ => ⟨rfl, rfl⟩, fun hK => ?_⟩
      exact absurd (hR.root hK) (hnv 0 hK)
    · exact ⟨d i + ℓ, by rw [hk], fun hK => by omega, fun _ => ⟨i, hi, ℓ, ha, rfl⟩⟩
  have hR' := hR.ext hnv hroot hpar fun i hi y ℓ ha hy => by
    have := hleast i hi y ℓ ha hy
    rw [hdK] at this; exact_mod_cast this
  have hv' : ∀ j < K + 1, Function.update v K x j < P.N := fun j hj => by
    rcases Nat.lt_or_ge j K with h | h
    · rw [Function.update_of_ne (by omega)]; exact hS.gh.vlt j h
    · rw [show j = K by omega, Function.update_self]; exact hx
  have hDB' := hR'.dist_le_real hL hXB hv'
  exact settle_good (dK := dK) hL hXB hDc hF c hc hG hX hDa hS' (by rw [h180]; exact hx)
    (by rw [h180]; exact hsx) (fun _ h => h.elim) hk180 (by rw [h180]; exact hdK)
    (fun j hj => by have := hDB' j (by omega); rwa [Function.update_of_ne (by omega)] at this)
    (by have := hDB' K (by omega); rwa [Function.update_self] at this)


/-- **Popping the item of a half block is good.** -/
theorem bPop_good (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D) (hF : Feas P) {K : ℕ} {v : ℕ → ℕ}
    {d : ℕ → ℤ} {κ : ℝ} {X : ℕ → ℕ → ℕ → Prop} (c : Config) (hc : WordsBounded P.W c)
    (hG : Glob P c) (hX : GX P c) (hDa : Data P c) (hS : MSt P K v d κ F2 F1 F2 X c.nmem c.rmem)
    (hR : MRun P K v d) (h290 : c.nreg 290 = tWn P.bh (2 ^ P.TB) c.nmem 1)
    (hpw : tPr P.bh c.nmem (tWn P.bh (2 ^ P.TB) c.nmem 1) = 1)
    (hv : ∀ y < P.N, prV P c.nmem y = 1 →
      tKey P.bh c.rmem (tWn P.bh (2 ^ P.TB) c.nmem 1) ≤ keyV P c.rmem y) :
    FG I P L bPop c := by
  have hDB := hR.dist_le_real hL hXB hS.gh.vlt
  have hw := lay_w hL
  have hbw := bh_le_W hL
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have htb := tb_ge P
  obtain ⟨hwl, hmin⟩ := win_root hS.bh.win Nat.one_le_two_pow
  generalize hwv : tWn P.bh (2 ^ P.TB) c.nmem 1 = w at hwl hmin h290 hpw hv ⊢
  have hK0 := hS.leaf_pos hL hwl hpw
  obtain ⟨t, k, ht, hk, rfl⟩ := hS.bh.leaf w hwl hpw
  generalize hκ' : tKey P.bh c.rmem (bid P t k) = κ' at hv ⊢
  have hs1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hb : ∀ w' < 2 ^ P.TB, tPr P.bh c.nmem w' = 1 → κ' ≤ tKey P.bh c.rmem w' :=
    fun w' h1 h2 => hκ' ▸ (hmin w' h1 h2).2
  have hB := hS.blk t k ht hk
  have hroot : tPr (tbQ P t k) c.nmem (tWn (tbQ P t k) (2 ^ t) c.nmem 1) = 1 := by
    have := hB.sync; rw [hpw] at this; split_ifs at this with h
    exact h
  have hkey0 := hB.key hroot
  rw [hκ'] at hkey0
  -- the popped key is at least the old one
  have hκκ : κ ≤ κ' := by
    obtain ⟨own, h0 | ⟨-, hT, hκo⟩⟩ := hB.rep
    · exact absurd hroot (h0.2.2.2.no_start (win_root h0.2.2.2.win hs1).1)
    obtain ⟨-, -, hXm, hmr, hown, hkey, -⟩ := hT.item hs1 (win_root hT.mem.win hs1).1 hroot
    rw [hkey0, hkey, ← hown]; exact hκo _ hmr hXm
  have hS' := hS.raise hκκ hv hb
  have hleast := hS.least hL hv hb
  -- the context of the half block
  unfold bPop
  refine good_seq_use (bload_exec (I := I) hL c hc hG hX ht hk h290 hB.leaf) (fg_abs0 (by decide)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hH₁, hT₁, h182, h183, h284, h285, h181, hK₁, hR₁, hN₁, hM₁, hO₁⟩
  have k1 : ∀ r, (r < 120 ∨ (126 ≤ r ∧ r < 181) ∨ (184 ≤ r ∧ r < 189) ∨ (197 ≤ r ∧ r < 208) ∨
      (210 ≤ r ∧ r < 284) ∨ 286 ≤ r) → c₁.nreg r = c.nreg r := fun r hr => hK₁ r (by omega)
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => k1 r (by omega)
  have hX₁ : GX P c₁ := hX.of fun r h1 h2 => k1 r (by omega)
  have hDa₁ : Data P c₁ := hDa.of hL (fun a _ => by rw [hN₁]) (fun a _ => by rw [hM₁])
  rw [← hN₁, ← hM₁] at hS'
  rw [← hN₁] at hroot
  rw [← hN₁, ← hM₁] at hkey0
  have hB' := hS'.blk t k ht hk
  obtain ⟨own, h0 | ⟨hf, hT, hκo⟩⟩ := hB'.rep
  · exact absurd hroot (h0.2.2.2.no_start (win_root h0.2.2.2.win hs1).1)
  have hrw := (win_root hT.mem.win hs1).1
  obtain ⟨-, -, hXm, hmr, hown, hkey, -⟩ := hT.item hs1 hrw hroot
  have hnc : 0 < hbNc P.b (2 ^ t) k := lt_of_le_of_lt (Nat.zero_le _)
    (hT.heap.ok.lt _ (hT.heap.ok.act _ hmr))
  -- the extraction
  have heB : ∀ σ, hbAct P F2 c₁.nmem t k σ → |hbe P c₁.rmem t k σ| ≤ (P.N * L : ℝ) :=
    fun σ hσ => by unfold hbe; exact hS'.dV_le hDB (src_lt_N hL hσ.1) hσ.2.1
  obtain ⟨c₂, k₂, e₂, hk₂, hnst₂, h254, h250, hT₂, hf₂, hp₂, hkey₂, hW₂, hWl₂, hn₂, hr₂, hF₂⟩ :=
    extStep_exec hL (I := I) (κ := κ') (κ' := κ') ht hk c₁ hw₁ ⟨hG₁, hH₁, hDa₁⟩ hT₁ hX₁ h285
      h183 (hB'.ready hnc) hT (fun σ _ => rfl) hrw hroot le_rfl (le_of_eq hkey0.symm)
      hS'.bh.pr hS'.bh.win hS'.bh.wl
  refine good_seq_ex (extStep_good hL hXB ht hk c₁ hw₁ ⟨hG₁, hH₁, hDa₁⟩ hT₁ (hB'.ready hnc) hT
    (fun σ _ => rfl) hrw hroot le_rfl (le_of_eq hkey0.symm) heB) ⟨c₂, k₂, e₂, ?_⟩
  have hw₂ := e₂.wb_right
  generalize hm : tMin (tbQ P t k) c₁.nmem (tWn (tbQ P t k) (2 ^ t) c₁.nmem 1) = m at *
  have hS₂ := hS'.extract hL ht hk hmr hT₂ hκo (by rw [hf₂]; exact hf) hp₂ hkey₂ hW₂ hWl₂
    (fun a h1 h2 => hn₂ a (by omega) h2) hr₂
  have k2 : ∀ r, ¬ (ExN r ∨ BSn r) → c₂.nreg r = c₁.nreg r := hF₂.n
  have hG₂ : Glob P c₂ := hG₁.of fun r h1 h2 => k2 r (by simp only [ExN, BSn, TPn]; omega)
  have hX₂ : GX P c₂ := hX₁.of fun r h1 h2 => k2 r (by simp only [ExN, BSn, TPn]; omega)
  have hQb := tbQ_le_bh ht hk
  have hQt : P.tb ≤ tbQ P t k := tb_le_tbQ
  have hlo2 : ∀ a < P.hb, c₂.nmem a = c₁.nmem a := fun a ha =>
    hn₂ a (Or.inl (by unfold Prm.hb at ha; omega)) (Or.inl (by unfold Prm.hb at ha; omega))
  have hlo2r : ∀ a < P.hb, c₂.rmem a = c₁.rmem a := fun a ha =>
    hr₂ a (Or.inl (by unfold Prm.hb at ha; omega)) (by unfold Prm.hb at ha; omega)
  have hhb : P.hb = P.wb + 3 * P.N := rfl
  have hDa₂ : Data P c₂ := hDa₁.of hL (fun a _ => hlo2 a (by omega)) (fun a _ => hlo2r a (by omega))
  have h122 : c₂.nreg 122 = k * 2 ^ t := by
    rw [k2 122 (by simp only [ExN, BSn, TPn]; omega)]; exact hH₁.r122
  have hy : k * 2 ^ t + m < P.b := by unfold hbNr at hmr; omega
  -- the potential so far
  have hpotS : potS P c₂.nmem = potS P c.nmem := by
    rw [← hN₁]; exact potS_congr fun y hy => hlo2 _ (by omega)
  have hpotN := potN_step (nm := c₁.nmem) (nm' := c₂.nmem) ht hk fun a h1 h2 =>
    hn₂ a (by omega) (Or.inl h2)
  have hN1p : potN P c₁.nmem = potN P c.nmem := by rw [hN₁]
  have hLDn : LD t * nst (tbQ P t k) (2 ^ t) c₂.nmem ≤
      LD t * nst (tbQ P t k) (2 ^ t) c₁.nmem + LD t := by
    have := Nat.mul_le_mul_left (LD t) hnst₂; rw [Nat.mul_add, Nat.mul_one] at this; exact this
  have hpotX := potX_step ht hk hmr hXm
  have hCx : Cx P * potX P X = Cx P * potX P (fun t' k' ρ => X t' k' ρ ∨
      (t' = t ∧ k' = k ∧ ρ = m)) + Cx P := by rw [← hpotX, Nat.mul_add, Nat.mul_one]
  have hcx : extCost t + LD t + 49 * P.TB + 100 ≤ Cx P := by
    have := lt_Lv' ht
    unfold Cx; have := extCost_mono (show t ≤ P.Lv by omega)
    have := LD_mono (show t ≤ P.Lv by omega); omega
  -- the target of the item
  refine good_seq_ex (fg_abs0 (by decide)) ?_
  exec_block
  · rw [h122, h254]; omega
  · config_simp; rw [hG₂.r107, h122, h254]; omega
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
  have hw₃ : WordsBounded P.W c₃ := hc₃ ▸ ‹_›
  have f180 : c₃.nreg 180 = k * 2 ^ t + m := by rw [← hc₃]; config_simp; rw [h122, h254]
  have f192 : c₃.nreg 192 = sfV P c₂.nmem (k * 2 ^ t + m) := by
    rw [← hc₃]; config_simp; rw [hG₂.r107, h122, h254]; rfl
  have r180 : c₃.rreg 180 = κ' := by rw [← hc₃]; config_simp; rw [h250, ← hkey0]
  have fK : ∀ r, r ≠ 180 → r ≠ 192 → c₃.nreg r = c₂.nreg r := fun r h1 h2 => by
    rw [← hc₃]; config_simp; upd_tac
  have fR : ∀ r, r ≠ 180 → c₃.rreg r = c₂.rreg r := fun r h1 => by
    rw [← hc₃]; config_simp; upd_tac
  have e3N : c₃.nmem = c₂.nmem := by rw [← hc₃]
  have e3M : c₃.rmem = c₂.rmem := by rw [← hc₃]
  have e3O : c₃.output = c₂.output := by rw [← hc₃]
  have hG₃ : Glob P c₃ := hG₂.of fun r h1 h2 => fK r (by omega) (by omega)
  have hX₃ : GX P c₃ := hX₂.of fun r h1 h2 => fK r (by omega) (by omega)
  have hDa₃ : Data P c₃ := hDa₂.of hL (fun a _ => by rw [e3N]) (fun a _ => by rw [e3M])
  rw [← e3N, ← e3M] at hS₂
  have kN : ∀ r < 100, c₃.nreg r = c.nreg r := fun r hr => by
    rw [fK r (by omega) (by omega), k2 r (by simp only [ExN, BSn, TPn]; omega)]
    exact k1 r (by omega)
  have kR : ∀ r < 100, c₃.rreg r = c.rreg r := fun r hr => by
    rw [fR r (by omega), hF₂.r r (by simp only [ExR, TPr]; omega), hR₁]
  have kO : c₃.output = c.output := by rw [e3O, hF₂.o, hO₁]
  have hsf2 : sfV P c₂.nmem (k * 2 ^ t + m) ≤ 1 := by
    rw [← e3N]; exact hS₂.hp.sf_le _ (by have := hL.bN; omega)
  by_cases hys : sfV P c₂.nmem (k * 2 ^ t + m) = 0
  · -- settle the target
    refine good_ifLtN_true (by rw [f192, hys, hG₃.r110]; omega) ?_
    -- its distance, through the owner of its row
    have hact := hT.heap.ok.act _ hmr
    obtain ⟨ha1, ha2, -⟩ := hact
    have hu : sib k * 2 ^ t + own m < P.N := by unfold hbNc at ha1; have := hL.bN; omega
    obtain ⟨i, hi, hvi⟩ := (hS'.gh.sf _ hu).1 ha2
    have hdi := hS'.gh.dist i hi
    have hne : sib k * 2 ^ t + own m ≠ k * 2 ^ t + m :=
      src_ne_tgt (lt_of_lt_of_le ha1 hbNc_le) (lt_of_lt_of_le hmr (Nat.min_le_left _ _))
    have hval : κ' = ((d i + P.D (v i) (k * 2 ^ t + m) - P.p (k * 2 ^ t + m) : ℤ) : ℝ) := by
      rw [hkey0, hkey, ← hown]
      unfold hbe; rw [hbF_live hy, ← hvi, hdi]; push_cast; ring
    have hys' : sfV P c.nmem (k * 2 ^ t + m) = 0 := by
      unfold sfV at hys ⊢; rw [← hN₁, ← hlo2 _ (by have := hL.bN; omega)]; exact hys
    have hnv : ∀ j < K, v j ≠ k * 2 ^ t + m := fun j hj e => by
      have := (hS.gh.sf _ (by have := hL.bN; omega)).2 ⟨j, hj, e⟩; omega
    have hR' := hR.ext (dK := d i + P.D (v i) (k * 2 ^ t + m)) hnv (fun h => by omega)
      (fun _ => ⟨i, hi, _, Or.inl ⟨by rw [hvi]; unfold hbNc at ha1; omega, hy,
        by rw [hvi]; exact hne, rfl⟩, rfl⟩)
      (fun i' hi' y ℓ ha hy' => by
        have := hleast i' hi' y ℓ ha hy'
        rw [hval] at this; exact_mod_cast this)
    have hv' : ∀ j < K + 1, Function.update v K (k * 2 ^ t + m) j < P.N := fun j hj => by
      rcases Nat.lt_or_ge j K with h | h
      · rw [Function.update_of_ne (by omega)]; exact hS.gh.vlt j h
      · rw [show j = K by omega, Function.update_self]; have := hL.bN; omega
    have hDB' := hR'.dist_le_real hL hXB hv'
    exact settle_good (dK := d i + P.D (v i) (k * 2 ^ t + m)) hL hXB hDc hF c₃ hw₃ hG₃ hX₃
        hDa₃ hS₂ (by rw [f180]; have := hL.bN; omega) (by rw [f180, e3N]; exact hys)
        (fun y h => h.trans f180.symm) r180 (by rw [f180, hval]) hDB
        (by have := hDB' K (by omega); rwa [Function.update_self] at this)
  · refine good_ifLtN_false (by rw [f192, hG₃.r110]; omega) ?_
    exact Good.skip


/-- **One round of the main loop is good.** -/
theorem mBody_good (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D) (hF : Feas P)
    {c₀ : Config} (g : GS) (c : Config) (hI : MI P c₀ g c) (hlt : c.nreg 117 < c.nreg 190) :
    FG I P L mBody c := by
  obtain ⟨K, v, d, κ, X⟩ := g
  obtain ⟨hc, hG, hX, hDa, hkN, hkR, hO, hS, hR, h190, -⟩ := hI
  simp only at hS hR h190 ⊢
  have hw := lay_w hL
  have hbw := bh_le_W hL
  have hW := hS.hp.win
  have hx := (hW.under 1 le_rfl (by omega)).1
  have hminV := (win_root hW (by omega)).2
  obtain ⟨hwl, hminB⟩ := win_root hS.bh.win Nat.one_le_two_pow
  have hpx1 := hS.hp.pr_le _ hx
  have hpw1 := hS.bh.pr _ hwl
  rw [hG.r117, h190] at hlt
  have hx' : c.nmem (P.wb + P.N + 1) < P.N := hx
  have hwl' : c.nmem (P.bh + 8 * 2 ^ P.TB + 2) < 2 ^ P.TB := by
    have := hwl; unfold tWn at this; simpa using this
  unfold mBody
  refine good_seq_ex (fg_abs0 (by decide)) ?_
  exec_block
  · rw [hG.r114, hG.r110]; omega
  · config_simp; rw [hG.r109, hG.r114, hG.r110]; omega
  · config_simp; rw [hX.r242, hG.r111]; omega
  · config_simp; rw [hX.r242, hG.r111, hG.r118]; omega
  · config_simp; rw [hX.r242, hG.r111, hG.r118, hX.r241]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f180 : c₁.nreg 180 = wnV P c.nmem 1 := by
    rw [← hc₁]; config_simp; rw [hG.r114, hG.r110]; rfl
  have f192 : c₁.nreg 192 = prV P c.nmem (wnV P c.nmem 1) := by
    rw [← hc₁]; config_simp; rw [hG.r109, hG.r114, hG.r110]; rfl
  have r180 : c₁.rreg 180 = keyV P c.rmem (wnV P c.nmem 1) := by
    rw [← hc₁]; config_simp; rw [hG.r109, hG.r114, hG.r110]; rfl
  have f290 : c₁.nreg 290 = tWn P.bh (2 ^ P.TB) c.nmem 1 := by
    rw [← hc₁]; config_simp; rw [hX.r242, hG.r111]; rfl
  have f193 : c₁.nreg 193 = tPr P.bh c.nmem (tWn P.bh (2 ^ P.TB) c.nmem 1) := by
    rw [← hc₁]; config_simp; rw [hX.r242, hG.r111, hG.r118, hX.r241]
    unfold tPr tWn; congr 1; ring
  have r190 : c₁.rreg 190 = tKey P.bh c.rmem (tWn P.bh (2 ^ P.TB) c.nmem 1) := by
    rw [← hc₁]; config_simp; rw [hX.r242, hG.r111, hG.r118, hX.r241]
    unfold tKey tWn; congr 1; ring
  have fK : ∀ r, r ≠ 180 → r ≠ 191 → r ≠ 192 → r ≠ 193 → r ≠ 290 → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 h5 => by rw [← hc₁]; config_simp; upd_tac
  have fR : ∀ r, r ≠ 180 → r ≠ 190 → c₁.rreg r = c.rreg r := fun r h1 h2 => by
    rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => fK r (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have hX₁ : GX P c₁ := hX.of fun r h1 h2 => fK r (by omega) (by omega) (by omega) (by omega)
    (by omega)
  have hDa₁ : Data P c₁ := hDa.of hL (fun a _ => by rw [fN]) (fun a _ => by rw [fM])
  have hS₁ : MSt P K v d κ F2 F1 F2 X c₁.nmem c₁.rmem := by rw [fN, fM]; exact hS
  have hxN : wnV P c.nmem 1 < P.N := hx
  have hb180 : MemB P.W (BB P L) c₁ → |c₁.rreg 190 - c₁.rreg 180| ≤ ((6 * BB P L : ℕ) : ℝ) := by
    intro hM
    rw [r190, r180, ← fM]
    have h1 := hM (P.wb + wnV P c.nmem 1) (by omega)
    have h2 := hM (P.bh + 8 * tWn P.bh (2 ^ P.TB) c.nmem 1) (by omega)
    unfold keyV tKey
    calc |c₁.rmem (P.bh + 8 * tWn P.bh (2 ^ P.TB) c.nmem 1) - c₁.rmem (P.wb + wnV P c.nmem 1)|
        ≤ |c₁.rmem (P.bh + 8 * tWn P.bh (2 ^ P.TB) c.nmem 1)| +
          |c₁.rmem (P.wb + wnV P c.nmem 1)| := abs_sub _ _
      _ ≤ ((6 * BB P L : ℕ) : ℝ) := by push_cast; have := Nat.cast_nonneg (α := ℝ) (BB P L); linarith
  refine Good.seq ?_ fun _ _ _ => fg_abs0 (by decide)
  by_cases hpv : prV P c.nmem (wnV P c.nmem 1) = 1
  · by_cases hpb : tPr P.bh c.nmem (tWn P.bh (2 ^ P.TB) c.nmem 1) = 1
    · refine good_ifLtN_false (by rw [f192, hG₁.r110, hpv]; omega) ?_
      refine good_ifLtN_false (by rw [f193, hG₁.r110, hpb]; omega) ?_
      refine Good.ifLtR hb180 (fun hlt' => ?_) (fun hlt' => ?_)
      · rw [r190, r180] at hlt'
        exact bPop_good hL hXB hDc hF c₁ hw₁ hG₁ hX₁ hDa₁ hS₁ hR (by rw [f290, fN])
          (by rw [fN]; exact hpb)
          (fun y hy hpy => by
            rw [fN, fM]; rw [fN] at hpy
            exact hlt'.le.trans (hminV y hy hpy).2)
      · rw [r190, r180] at hlt'
        exact vPop_good hL hXB hDc hF c₁ hw₁ hG₁ hX₁ hDa₁ hS₁ hR (by rw [f180, fN])
          (by rw [fN]; exact hpv) (by rw [r180, fN, fM])
          (fun w hw hpw => by
            rw [fN, fM]; rw [fN] at hpw
            exact (not_lt.1 hlt').trans (hminB w hw hpw).2)
    · refine good_ifLtN_false (by rw [f192, hG₁.r110, hpv]; omega) ?_
      refine good_ifLtN_true (by rw [f193, hG₁.r110]; omega) ?_
      exact vPop_good hL hXB hDc hF c₁ hw₁ hG₁ hX₁ hDa₁ hS₁ hR (by rw [f180, fN])
        (by rw [fN]; exact hpv) (by rw [r180, fN, fM])
        (fun w hw hpw => by
          rw [fN] at hpw
          exact absurd (hminB w hw hpw).1 hpb)
  · have hpb : tPr P.bh c.nmem (tWn P.bh (2 ^ P.TB) c.nmem 1) = 1 := by omega
    refine good_ifLtN_true (by rw [f192, hG₁.r110]; omega) ?_
    exact bPop_good hL hXB hDc hF c₁ hw₁ hG₁ hX₁ hDa₁ hS₁ hR (by rw [f290, fN])
      (by rw [fN]; exact hpb)
      (fun y hy hpy => by
        rw [fN] at hpy
        exact absurd (hminV y hy hpy).1 hpv)

/-- **The main loop is good.** -/
theorem mainLoop_good (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D) (hF : Feas P)
    {c₀ : Config} (g : GS) (c : Config) (hI : MI P c₀ g c) :
    FG I P L (.whileLtN 117 190 mBody) c :=
  good_whileLtN_ghost (MI P c₀) (fun g c hI hlt => ⟨mBody_good hL hXB hDc hF g c hI hlt, by
    obtain ⟨c', k, e, g', h1, -⟩ := mBody_exec (I := I) hL hDc hF g c hI hlt
    exact ⟨c', k, e, g', h1⟩⟩) hI


set_option maxHeartbeats 1000000 in
/-- **FR-Dijkstra is good**: from the inputs of `frProg_exec`, bounded by `L`, every execution
started with the real memory bounded by `BB P L = (N + 2) L` has its real comparisons bounded by
`6 BB P L` (and its stored reals by `BB P L`). -/
theorem frProg_good (hL : Lay P) (hXB : XB P L) (hDc : Crossing P.b P.D) (hF : Feas P)
    (c : Config) (hc : WordsBounded P.W c) (hin : Inp P c) (hDa : Data P c) :
    FG I P L frProg c := by
  have hw := lay_w hL
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have hrN := hL.r_lt
  have htb := tb_ge P
  have hbw := bh_le_W hL
  have hbtb : P.tb ≤ P.bh := by unfold Prm.bh; omega
  unfold frProg
  -- the constants
  refine good_seq_use (setup_exec (I := I) hL c hc hin) (fg_abs0 (by decide)) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hG₁, hK₁, hR₁, hN₁, hM₁, hO₁⟩
  -- the vertices
  refine good_seq_instr (Exec.constN hw₁ 192 0 (by omega)) (fun _ => trivial) fun hw₂ => ?_
  generalize hc₂ : (Config.mk _ _ _ _ _ _ : Config) = c₂ at hw₂ ⊢
  have hG₂ : Glob P c₂ := hG₁.of fun r h1 h2 => by rw [← hc₂]; config_simp; upd_tac
  have h192 : c₂.nreg 192 = 0 := by rw [← hc₂]; config_simp
  refine good_seq_use (initLoop_exec (I := I) hL c₂ hw₂ hG₂ h192) (fg_abs0 (by decide)) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hG₃, hK₃, hR₃, hM₃, hO₃, hdone₃, hN₃⟩
  refine good_seq_instr (Exec.copyN hw₃ 170 100) (fun _ => trivial) fun hw₄ => ?_
  generalize hc₄ : (Config.mk _ _ _ _ _ _ : Config) = c₄ at hw₄ ⊢
  have hG₄ : Glob P c₄ := hG₃.of fun r h1 h2 => by rw [← hc₄]; config_simp; upd_tac
  have h170 : c₄.nreg 170 = P.N := by rw [← hc₄]; config_simp; exact hG₃.r100
  have e4N : c₄.nmem = c₃.nmem := by rw [← hc₄]
  refine good_seq_use (initWin_exec (I := I) hL c₄ hw₄ hG₄ h170
    (fun y hy => by rw [e4N]; exact (hdone₃ y hy).2.2)
    (fun y hy => by rw [e4N, (hdone₃ y hy).2.1]; omega)) (fg_abs0 (by decide)) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨hG₅, hK₅, hR₅, hM₅, hO₅, hN₅, hW₅⟩
  have hsf₅ : ∀ y < P.N, sfV P c₅.nmem y = 0 ∧ prV P c₅.nmem y = 0 := fun y hy => by
    unfold sfV prV; rw [hN₅ _ (Or.inl (by omega)), hN₅ _ (Or.inl (by omega)), e4N]
    exact ⟨(hdone₃ y hy).1, (hdone₃ y hy).2.1⟩
  have hDa₅ : Data P c₅ := hDa.of hL
    (fun a ha => by rw [hN₅ a (Or.inl (by omega)), e4N, hN₃ a ha, ← hc₂]; config_simp; rw [hN₁])
    (fun a ha => by rw [hM₅, ← hc₄]; config_simp; rw [hM₃, ← hc₂]; config_simp; rw [hM₁])
  -- the constants of the half blocks
  refine good_seq_use (gxSetup_exec (I := I) hL c₅ hw₅ hG₅) (fg_abs0 (by decide)) ?_
  intro c₆ k₆ hk₆ hw₆ ⟨hX₆, hK₆, hR₆, hN₆, hM₆, hO₆⟩
  have hG₆ : Glob P c₆ := hG₅.of fun r h1 h2 => hK₆ r (by omega)
  have hDa₆ : Data P c₆ := hDa₅.of hL (fun a _ => by rw [hN₆]) (fun a _ => by rw [hM₆])
  -- the empty heap of the half blocks
  refine good_seq_ex (fg_abs0 (by decide)) ?_
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
  refine good_seq_use (tInit_exec (I := I) c₇ hw₇ hG₇ hT₇
    (by rw [← hc₇]; config_simp; exact hX₆.r243) Nat.one_le_two_pow hbw) (fg_abs0 (by decide)) ?_
  intro c₈ k₈ hk₈ hw₈ ⟨hpr₈, hW₈, hWl₈, hn₈, hrm₈, hK₈, hR₈, hO₈⟩
  have hG₈ : Glob P c₈ := hG₇.of fun r h1 h2 => hK₈ r (by omega)
  have hX₈ : GX P c₈ := hX₇.of fun r h1 h2 => hK₈ r (by omega)
  have hlo8 : ∀ a < P.tb, c₈.nmem a = c₅.nmem a := fun a ha => by
    rw [hn₈ a (Or.inl (by omega)), e7N, hN₆]
  have hDa₈ : Data P c₈ := hDa₆.of hL (fun a ha => by rw [hn₈ a (Or.inl (by omega)), e7N])
    (fun a _ => by rw [hrm₈, e7M])
  -- the half blocks
  refine good_seq_use (bLevels_exec (I := I) hL hDc c₈ hw₈ hG₈ hX₈ hDa₈ ⟨hpr₈, hW₈, hWl₈⟩) (fg_abs0 (by decide)) ?_
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
  refine good_seq_ex (fg_abs0 (by decide)) ?_
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
  refine good_seq_use (decKey_exec (I := I) hL c₁₀ hw₁₀ hG₁₀ (by rw [f175]; exact hrN)
    hMS.hp.pr_le (by rw [f175]; exact hMS.hp.sf_le _ hrN) hMS.hp.win)
    (fg_abs (A := [(175, 1)]) (by decide) fun _ => regA_one (by
      rw [r175]
      have h1 := hXB.p P.r hrN
      have h1' : |(P.p P.r : ℝ)| ≤ L := by exact_mod_cast h1
      push_cast; rw [abs_neg]
      exact h1'.trans (by unfold BB; push_cast; nlinarith))) ?_
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
  refine good_seq_use (gflag_exec (I := I) hL c₁₁ hw₁₁ hG₁₁ hX₁₁ hMS₁₁.hp.win hMS₁₁.hp.pr_le
    hMS₁₁.bh) (fg_abs0 (by decide)) ?_
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
  exact mainLoop_good hL hXB hDc hF _ c₁₂ hMI


end FR

end Monge

end PlanarFlow
