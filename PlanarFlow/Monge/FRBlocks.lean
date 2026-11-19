module

public import PlanarFlow.Monge.FRActivate

/-!
# FR-Dijkstra on the machine: the half blocks in the memory and the heap of the half blocks

* The triplet structure of the half block `k` of the level `2 ^ t` is at `tbQ P t k`
  (`16 · 2 ^ t` cells, `32 b` cells for a level); the heap of the half blocks is a tournament
  (`PlanarFlow.Monge.FR.WinOK`, the same records as the triplets) over `2 ^ TB > b Lv` leaves at
  `bh`, the leaf of the half block `(t, k)` being `bid P t k = t b + k`; its record holds the
  presence of the half block (it has a triplet) and its item (the key of the root of its heap
  over the triplets), and the parameters of the half block.
* The range-minimum structure of the half block `(t, k)` (`PlanarFlow.Monge.FR.QReady`) is at
  `rbB P t k = rb + 8 b Lv t + 4 Lv (k 2 ^ t)` (`8 b Lv` cells for a level).
* `GX`: the registers `r240 … r247` of these structures.
* `ctxW_exec`: the registers of a half block (`PlanarFlow.Monge.FR.HCtx`), within `16` steps.
* `bsync_exec`: **offering the item of the current half block to the heap of the half blocks**
  (`49 TB + 30` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Heap

/-- The base of the triplet structure of the half block `k` of the level `2 ^ t`. -/
def tbQ (P : Prm) (t k : ℕ) : ℕ := P.tb + 32 * P.b * t + 16 * (k * 2 ^ t)

/-- The base of the range-minimum structure of the half block `k` of the level `2 ^ t`. -/
def rbB (P : Prm) (t k : ℕ) : ℕ := P.rb + 8 * P.b * P.Lv * t + 4 * P.Lv * (k * 2 ^ t)

/-- The leaf of the half block `k` of the level `2 ^ t` in the heap of the half blocks. -/
def bid (P : Prm) (t k : ℕ) : ℕ := t * P.b + k

/-- The registers of the structures of the half blocks. -/
structure GX (P : Prm) (c : Config) : Prop where
  r240 : c.nreg 240 = P.tb
  r241 : c.nreg 241 = P.bh
  r242 : c.nreg 242 = P.bh + 8 * 2 ^ P.TB
  r243 : c.nreg 243 = 2 ^ P.TB
  r244 : c.nreg 244 = 32 * P.b
  r245 : c.nreg 245 = 4 * P.Lv
  r246 : c.nreg 246 = P.rb
  r247 : c.nreg 247 = 8 * P.b * P.Lv

theorem GX.of {P : Prm} {c c' : Config} (h : GX P c)
    (hr : ∀ r, 240 ≤ r → r < 248 → c'.nreg r = c.nreg r) : GX P c' :=
  ⟨(hr 240 (by omega) (by omega)).trans h.r240, (hr 241 (by omega) (by omega)).trans h.r241,
    (hr 242 (by omega) (by omega)).trans h.r242, (hr 243 (by omega) (by omega)).trans h.r243,
    (hr 244 (by omega) (by omega)).trans h.r244, (hr 245 (by omega) (by omega)).trans h.r245,
    (hr 246 (by omega) (by omega)).trans h.r246, (hr 247 (by omega) (by omega)).trans h.r247⟩

variable {P : Prm} {I : Input}

/-! ### The registers of a half block -/

lemma sib_le (k : ℕ) : sib k ≤ k + 1 := by unfold sib; split_ifs <;> omega

/-- **The registers of the half block `r183` of the level `r182`** (level base `r181`, stride
`m = r w`). -/
theorem ctxW_exec (hL : Lay P) {s k LB w m : ℕ} (c : Config) (hc : WordsBounded P.W c)
    (hG : Glob P c) (h182 : c.nreg 182 = s) (h183 : c.nreg 183 = k) (h181 : c.nreg 181 = LB)
    (hwm : c.nreg w = m) (hw1 : w ≠ 121) (hw2 : w ≠ 122) (hks : k * s < P.b)
    (hs1 : 1 ≤ s) (hs : s ≤ P.b) (hLB : LB + m * (k * s) ≤ P.W) :
    ∃ c' k', Exec I P.W (ctxW w) c c' k' ∧ k' ≤ 16 ∧
      (HCtx P (LB + m * (k * s)) s k c' ∧ c'.nreg 189 = sib k ∧
        (∀ r, (r < 120 ∨ 126 ≤ r) → r ≠ 189 → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧
        c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hw := hL.w
  have hb := hL.b_pos
  have hkb : k < P.b := lt_of_le_of_lt (Nat.le_mul_of_pos_right k hs1) hks
  have hsk : sib k * s ≤ 2 * P.b := by
    have := Nat.mul_le_mul_right s (sib_le k)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  have ew : ∀ f : ℕ → ℕ, ∀ a b, upd (upd f 121 a) 122 b w = f w := fun f a b => by
    rw [upd_other _ _ _ hw2, upd_other _ _ _ hw1]
  unfold ctxW
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h183, h182]; omega
  · config_simp; rw [ew, h183, h182, hwm]
    have : m * (k * s) ≤ P.W := by omega
    nlinarith
  · config_simp; rw [ew, h183, h182, hwm, h181]; nlinarith
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f189 : c₁.nreg 189 = k % 2 := by rw [← hc₁]; config_simp; rw [h183, hG.r111]
  have f121 : c₁.nreg 121 = s := by rw [← hc₁]; config_simp; exact h182
  have f122 : c₁.nreg 122 = k * s := by rw [← hc₁]; config_simp; rw [h183, h182]
  have f120 : c₁.nreg 120 = LB + m * (k * s) := by
    rw [← hc₁]; config_simp; rw [ew, h183, h182, hwm, h181]; ring
  have fK : ∀ r, r ≠ 120 → r ≠ 121 → r ≠ 122 → r ≠ 189 → c₁.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => by rw [← hc₁]; config_simp; upd_tac
  have k110 : c₁.nreg 110 = 1 := (fK 110 (by omega) (by omega) (by omega) (by omega)).trans hG.r110
  have k183 : c₁.nreg 183 = k := (fK 183 (by omega) (by omega) (by omega) (by omega)).trans h183
  have k182 : c₁.nreg 182 = s := (fK 182 (by omega) (by omega) (by omega) (by omega)).trans h182
  have k101 : c₁.nreg 101 = P.b :=
    (fK 101 (by omega) (by omega) (by omega) (by omega)).trans hG.r101
  refine spec_seq ?_
  obtain ⟨c₂, k₂, e₂, hk₂, g189, gK, gR, gN, gM, gO⟩ : ∃ c₂ k₂, Exec I P.W
      (.ifLtN 189 110 (.instr (.addN 189 183 110)) (.instr (.subN 189 183 110))) c₁ c₂ k₂ ∧
      k₂ ≤ 3 ∧ c₂.nreg 189 = sib k ∧ (∀ r, r ≠ 189 → c₂.nreg r = c₁.nreg r) ∧ c₂.rreg = c₁.rreg ∧
      c₂.nmem = c₁.nmem ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases hp : k % 2 = 0
    · refine spec_ifLtN_true (by rw [f189, k110]; omega) ?_
      refine spec_instr (Exec.addN hw₁ 189 183 110 (by rw [k183, k110]; omega)) fun _ =>
        ⟨by omega, ?_, fun r hr => by config_simp; upd_tac, rfl, rfl, rfl, rfl⟩
      config_simp; rw [k183, k110]; unfold sib; simp [hp]
    · refine spec_ifLtN_false (by rw [f189, k110]; omega) ?_
      refine spec_instr (Exec.subN hw₁ 189 183 110) fun _ =>
        ⟨by omega, ?_, fun r hr => by config_simp; upd_tac, rfl, rfl, rfl, rfl⟩
      config_simp; rw [k183, k110]; unfold sib; simp [hp]
  refine ⟨c₂, k₂, e₂, ?_⟩
  have hw₂ := e₂.wb_right
  have l182 : c₂.nreg 182 = s := (gK 182 (by omega)).trans k182
  have l101 : c₂.nreg 101 = P.b := (gK 101 (by omega)).trans k101
  have l122 : c₂.nreg 122 = k * s := (gK 122 (by omega)).trans f122
  have l121 : c₂.nreg 121 = s := (gK 121 (by omega)).trans f121
  have l120 : c₂.nreg 120 = LB + m * (k * s) := (gK 120 (by omega)).trans f120
  refine spec_seq ?_
  exec_block
  · rw [g189, l182]; omega
  generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
  have hw₃ : WordsBounded P.W c₃ := hc₃ ▸ ‹_›
  have m123 : c₃.nreg 123 = sib k * s := by rw [← hc₃]; config_simp; rw [g189, l182]
  have m124 : c₃.nreg 124 = P.b - sib k * s := by rw [← hc₃]; config_simp; rw [g189, l182, l101]
  have m125 : c₃.nreg 125 = P.b - k * s := by rw [← hc₃]; config_simp; rw [l101, l122]
  have mK : ∀ r, r ≠ 123 → r ≠ 124 → r ≠ 125 → c₃.nreg r = c₂.nreg r := fun r h1 h2 h3 => by
    rw [← hc₃]; config_simp; upd_tac
  have m121 : c₃.nreg 121 = s := (mK 121 (by omega) (by omega) (by omega)).trans l121
  have mN : c₃.nmem = c₂.nmem := by rw [← hc₃]
  have mM : c₃.rmem = c₂.rmem := by rw [← hc₃]
  have mR : c₃.rreg = c₂.rreg := by rw [← hc₃]
  have mO : c₃.output = c₂.output := by rw [← hc₃]
  -- the two minima
  have hmin : ∀ (r : ℕ) (x : ℕ) (c' : Config), WordsBounded P.W c' → c'.nreg 121 = s →
      c'.nreg r = x → r ≠ 121 →
      ∃ c'' k', Exec I P.W (.ifLtN 121 r (.instr (.copyN r 121)) .skip) c' c'' k' ∧ k' ≤ 2 ∧
        c''.nreg r = min s x ∧ (∀ r', r' ≠ r → c''.nreg r' = c'.nreg r') ∧ c''.rreg = c'.rreg ∧
        c''.nmem = c'.nmem ∧ c''.rmem = c'.rmem ∧ c''.output = c'.output := by
    intro r x c' hw' h121 hr hne
    by_cases hlt : s < x
    · refine spec_ifLtN_true (by rw [h121, hr]; exact hlt) ?_
      refine spec_instr (Exec.copyN hw' r 121) fun _ =>
        ⟨by omega, by config_simp; rw [h121]; omega,
          fun r' h => by config_simp; rw [upd_other _ _ _ h], rfl, rfl, rfl, rfl⟩
    · refine spec_ifLtN_false (by rw [h121, hr]; exact hlt) ?_
      exact spec_skip hw' ⟨by omega, by rw [hr]; omega, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  refine spec_seq ?_
  obtain ⟨c₄, k₄, e₄, hk₄, n124, nK, nR, nN, nM, nO⟩ := hmin 124 _ c₃ hw₃ m121 m124 (by omega)
  refine ⟨c₄, k₄, e₄, ?_⟩
  obtain ⟨c₅, k₅, e₅, hk₅, o125, oK, oR, oN, oM, oO⟩ := hmin 125 _ c₄ e₄.wb_right
    ((nK 121 (by omega)).trans m121) ((nK 125 (by omega)).trans m125) (by omega)
  refine ⟨c₅, k₅, e₅, by omega, ⟨(oK 120 (by omega)).trans ((nK 120 (by omega)).trans
      ((mK 120 (by omega) (by omega) (by omega)).trans l120)),
    (oK 121 (by omega)).trans ((nK 121 (by omega)).trans m121),
    (oK 122 (by omega)).trans ((nK 122 (by omega)).trans
      ((mK 122 (by omega) (by omega) (by omega)).trans l122)),
    (oK 123 (by omega)).trans ((nK 123 (by omega)).trans m123),
    (oK 124 (by omega)).trans (by rw [n124]; rfl), o125⟩, ?_, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [oK 189 (by omega), nK 189 (by omega), mK 189 (by omega) (by omega) (by omega)]; exact g189
  · rw [oK r (by omega), nK r (by omega), mK r (by omega) (by omega) (by omega), gK r h2]
    exact fK r (by omega) (by omega) (by omega) h2
  · rw [oR, nR, mR, gR]; rw [← hc₁]
  · rw [oN, nN, mN, gN]; rw [← hc₁]
  · rw [oM, nM, mM, gM]; rw [← hc₁]
  · rw [oO, nO, mO, gO]; rw [← hc₁]

/-! ### The layout -/

lemma lt_two_pow_TB (P : Prm) : P.b * P.Lv < 2 ^ P.TB := by
  unfold Prm.TB; exact Nat.lt_pow_succ_log_self (by norm_num) _

lemma two_pow_TB_le (hL : Lay P) : 2 ^ P.TB ≤ 2 * (P.b * P.Lv) := by
  have hb := hL.b_pos
  have : 1 ≤ P.b * P.Lv := Nat.one_le_iff_ne_zero.2 (by unfold Prm.Lv; positivity)
  unfold Prm.TB
  rw [pow_succ]
  have := Nat.pow_log_le_self 2 (show P.b * P.Lv ≠ 0 by omega)
  omega

lemma lt_Lv' {t : ℕ} (h : 2 ^ t < P.b) : t + 1 ≤ P.Lv := by
  unfold Prm.Lv
  have := Nat.le_log_of_pow_le (b := 2) (by norm_num) h.le
  omega

/-- The leaf of a half block is a leaf of the heap of the half blocks. -/
lemma bid_lt {t k : ℕ} (ht : 2 ^ t < P.b) (hk : k * 2 ^ t < P.b) : bid P t k < 2 ^ P.TB := by
  have h1 := lt_Lv' ht
  have hk' : k < P.b := lt_of_le_of_lt (Nat.le_mul_of_pos_right k Nat.one_le_two_pow) hk
  have := lt_two_pow_TB P
  have : (t + 1) * P.b ≤ P.Lv * P.b := Nat.mul_le_mul_right _ h1
  unfold bid; nlinarith

lemma bid_inj {t k t' k' : ℕ} (hk : k < P.b) (hk' : k' < P.b) (h : bid P t k = bid P t' k') :
    t = t' ∧ k = k' := by
  unfold bid at h
  have h1 : (t * P.b + k) / P.b = t := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk, Nat.zero_add]
  have h2 : (t' * P.b + k') / P.b = t' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hk', Nat.zero_add]
  have : t = t' := by rw [← h1, ← h2, h]
  subst this
  exact ⟨rfl, by omega⟩

/-! ### Offering the item of a half block -/

/-- **Offer the item of the current half block** (the root of its heap over the triplets) to its
leaf `r285 + r183` of the heap of the half blocks, and recompute the path of that leaf. -/
def bsync : Stmt :=
  .seq (block [.addN 280 209 111, .loadN 280 280, .mulN 281 280 118, .addN 281 281 208,
    .loadN 282 281, .loadR 280 281, .addN 283 285 183, .mulN 286 283 118, .addN 286 286 241]) <|
  .seq (.ifLtN 282 110 (.instr (.storeN 286 117)) (block [.storeN 286 110, .storeR 286 280])) <|
  .seq (block [.copyN 208 241, .copyN 209 242, .addN 210 243 283, .divN 210 210 111]) tUp

/-- The registers changed by `bsync`. -/
def BSn (r : ℕ) : Prop := (208 ≤ r ∧ r < 220) ∨ (280 ≤ r ∧ r < 284) ∨ r = 286

/-- **Offering the item of a half block**: the leaf `x` of the half block becomes present
exactly when the half block has a triplet, with its item as key; the tournaments of the heap of
the half blocks are recomputed. -/
theorem bsync_exec (hL : Lay P) {Q T x : ℕ} (c : Config) (hc : WordsBounded P.W c)
    (hG : Glob P c) (hX : GX P c) (hT : TCtx Q (2 ^ T) c)
    (hx : c.nreg 285 + c.nreg 183 = x) (hxl : x < 2 ^ P.TB) (hQ : Q + 16 * 2 ^ T ≤ P.bh)
    (hWb : WinOK (2 ^ T) (tPr Q c.nmem) (tKey Q c.rmem) (tWn Q (2 ^ T) c.nmem) 0)
    (hprb : ∀ y < 2 ^ T, tPr Q c.nmem y ≤ 1) (hpr : ∀ y < 2 ^ P.TB, tPr P.bh c.nmem y ≤ 1)
    (hW : WinOK (2 ^ P.TB) (tPr P.bh c.nmem) (tKey P.bh c.rmem) (tWn P.bh (2 ^ P.TB) c.nmem) 0)
    (hWl : WinOK (2 ^ P.TB) (tPr P.bh c.nmem) (fun x => (x : ℝ)) (tWl P.bh (2 ^ P.TB) c.nmem) 0) :
    ∃ c' k', Exec I P.W bsync c c' k' ∧ k' ≤ 49 * P.TB + 30 ∧
      (∀ y < 2 ^ P.TB, tPr P.bh c'.nmem y = if y = x then
        (if tPr Q c.nmem (tWn Q (2 ^ T) c.nmem 1) = 1 then 1 else 0) else tPr P.bh c.nmem y) ∧
      (tPr Q c.nmem (tWn Q (2 ^ T) c.nmem 1) = 1 →
        tKey P.bh c'.rmem x = tKey Q c.rmem (tWn Q (2 ^ T) c.nmem 1)) ∧
      WinOK (2 ^ P.TB) (tPr P.bh c'.nmem) (tKey P.bh c'.rmem) (tWn P.bh (2 ^ P.TB) c'.nmem) 0 ∧
      WinOK (2 ^ P.TB) (tPr P.bh c'.nmem) (fun x => (x : ℝ)) (tWl P.bh (2 ^ P.TB) c'.nmem) 0 ∧
      (∀ a, (a < P.bh ∨ P.bh + 12 * 2 ^ P.TB ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ a, a < P.bh + 8 * 2 ^ P.TB → a ≠ P.bh + 8 * x → c'.nmem a = c.nmem a) ∧
      (∀ a, a ≠ P.bh + 8 * x → c'.rmem a = c.rmem a) ∧ TCtx P.bh (2 ^ P.TB) c' ∧
      Fr BSn (fun r => r = 210 ∨ r = 211 ∨ r = 280) c c' := by
  have hw := hL.wx
  have hs1 : 1 ≤ 2 ^ T := Nat.one_le_two_pow
  have hsB : 1 ≤ 2 ^ P.TB := Nat.one_le_two_pow
  have g208 := hT.r208; have g209 := hT.r209
  obtain ⟨hr, -⟩ := win_root hWb hs1
  generalize hwv : tWn Q (2 ^ T) c.nmem 1 = w at hr ⊢
  have ew : c.nmem (c.nreg 209 + c.nreg 111) = w := by
    rw [g209, hG.r111, ← hwv]; unfold tWn; congr 1
  have e8 : w * 8 + Q = Q + 8 * w := by ring
  have e8x : x * 8 + P.bh = P.bh + 8 * x := by ring
  have hbw : P.bh + 16 * 2 ^ P.TB ≤ P.W := by unfold Prm.rb at hw; omega
  unfold bsync
  refine spec_seq ?_
  exec_block
  · rw [g209, hG.r111]; omega
  · config_simp; rw [ew, hG.r118]; omega
  · config_simp; rw [ew, hG.r118, g208]; omega
  · config_simp; rw [hx]; omega
  · config_simp; rw [hx, hG.r118]; omega
  · config_simp; rw [hx, hG.r118, hX.r241]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f282 : c₁.nreg 282 = tPr Q c.nmem w := by
    rw [← hc₁]; config_simp; rw [ew, hG.r118, g208, e8]; rfl
  have r280 : c₁.rreg 280 = tKey Q c.rmem w := by
    rw [← hc₁]; config_simp; rw [ew, hG.r118, g208, e8]; rfl
  have f286 : c₁.nreg 286 = P.bh + 8 * x := by
    rw [← hc₁]; config_simp; rw [hx, hG.r118, hX.r241, e8x]
  have f283 : c₁.nreg 283 = x := by rw [← hc₁]; config_simp; exact hx
  have fK : ∀ r, ¬ ((280 ≤ r ∧ r < 284) ∨ r = 286) → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; config_simp; upd_tac
  have fR : ∀ r, r ≠ 280 → c₁.rreg r = c.rreg r := fun r hr => by
    rw [← hc₁]; config_simp; rw [upd_other _ _ _ hr]
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  -- after the write of the leaf
  have post : ∀ (c₂ : Config) (k₂ : ℕ), WordsBounded P.W c₂ → k₂ ≤ 4 →
      c₂.nreg = c₁.nreg → c₂.output = c.output →
      (∀ r, r ≠ 280 → c₂.rreg r = c.rreg r) →
      (∀ a, a ≠ P.bh + 8 * x → c₂.nmem a = c.nmem a) →
      (∀ a, a ≠ P.bh + 8 * x → c₂.rmem a = c.rmem a) →
      tPr P.bh c₂.nmem x = (if tPr Q c.nmem w = 1 then 1 else 0) →
      (tPr Q c.nmem w = 1 → tKey P.bh c₂.rmem x = tKey Q c.rmem w) →
      ∃ c' k', Exec I P.W (.seq (block [.copyN 208 241, .copyN 209 242, .addN 210 243 283,
          .divN 210 210 111]) tUp) c₂ c' k' ∧ 9 + k₂ + k' ≤ 49 * P.TB + 30 ∧
        (∀ y < 2 ^ P.TB, tPr P.bh c'.nmem y = if y = x then
          (if tPr Q c.nmem w = 1 then 1 else 0) else tPr P.bh c.nmem y) ∧
        (tPr Q c.nmem w = 1 → tKey P.bh c'.rmem x = tKey Q c.rmem w) ∧
        WinOK (2 ^ P.TB) (tPr P.bh c'.nmem) (tKey P.bh c'.rmem) (tWn P.bh (2 ^ P.TB) c'.nmem) 0 ∧
        WinOK (2 ^ P.TB) (tPr P.bh c'.nmem) (fun x => (x : ℝ)) (tWl P.bh (2 ^ P.TB) c'.nmem) 0 ∧
        (∀ a, (a < P.bh ∨ P.bh + 12 * 2 ^ P.TB ≤ a) → c'.nmem a = c.nmem a) ∧
        (∀ a, a < P.bh + 8 * 2 ^ P.TB → a ≠ P.bh + 8 * x → c'.nmem a = c.nmem a) ∧
        (∀ a, a ≠ P.bh + 8 * x → c'.rmem a = c.rmem a) ∧ TCtx P.bh (2 ^ P.TB) c' ∧
        Fr BSn (fun r => r = 210 ∨ r = 211 ∨ r = 280) c c' := by
    intro c₂ k₂ hw₂ hk₂ hN2 hO2 hR2 hn2 hr2 hp2 hk2
    have k2 : ∀ r, ¬ ((280 ≤ r ∧ r < 284) ∨ r = 286) → c₂.nreg r = c.nreg r := fun r hr => by
      rw [hN2]; exact fK r hr
    refine spec_seq ?_
    exec_block
    · config_simp; rw [k2 243 (by omega), hX.r243, hN2, f283]; omega
    generalize hc₃ : (Config.mk _ _ _ _ _ _ : Config) = c₃
    have hw₃ : WordsBounded P.W c₃ := hc₃ ▸ ‹_›
    have k3 : ∀ r, ¬ ((208 ≤ r ∧ r < 211) ∨ (280 ≤ r ∧ r < 284) ∨ r = 286) →
        c₃.nreg r = c.nreg r := fun r hr => by
      rw [← hc₃]; config_simp; rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
        upd_other _ _ _ (by omega)]; exact k2 r (by omega)
    have f210 : c₃.nreg 210 = (2 ^ P.TB + x) / 2 := by
      rw [← hc₃]; config_simp; rw [k2 243 (by omega), hX.r243, hN2, f283, fK 111 (by omega),
        hG.r111]
    have t208 : c₃.nreg 208 = P.bh := by
      rw [← hc₃]; config_simp; rw [k2 241 (by omega), hX.r241]
    have t209 : c₃.nreg 209 = P.bh + 8 * 2 ^ P.TB := by
      rw [← hc₃]; config_simp; rw [k2 242 (by omega), hX.r242]
    have hT₃ : TCtx P.bh (2 ^ P.TB) c₃ := ⟨t208, t209⟩
    have hG₃ : Glob P c₃ := hG.of fun r h1 h2 => k3 r (by omega)
    have N3 : c₃.nmem = c₂.nmem := by rw [← hc₃]
    have M3 : c₃.rmem = c₂.rmem := by rw [← hc₃]
    have hpr₃ : ∀ y < 2 ^ P.TB, tPr P.bh c₃.nmem y = if y = x then
        (if tPr Q c.nmem w = 1 then 1 else 0) else tPr P.bh c.nmem y := fun y hy => by
      rw [N3]
      by_cases e : y = x
      · subst e; rw [iteT rfl, hp2]
      · rw [iteF e]; unfold tPr; exact hn2 _ (by omega)
    obtain ⟨hW₃, hWl₃⟩ := winOK_rec (nm' := c₃.nmem) (rm' := c₃.rmem) hW hWl
      (fun a h1 h2 h3 h4 => by rw [N3]; exact hn2 a h1)
      (fun a h1 => by rw [M3]; exact hr2 a h1) hxl
    refine spec_use (tUp_exec (I := I) c₃ hw₃ hG₃ hT₃ hbw (by rw [f210]; omega)
      (fun y hy => by rw [hpr₃ y hy]; split_ifs <;> first | omega | exact hpr y hy)
      (by rw [f210]; exact hW₃) (by rw [f210]; exact hWl₃)) ?_
    intro c₄ k₄ hk₄ hw₄ ⟨hW₄, hWl₄, hK₄, hR₄, hO₄, hN₄, hM₄⟩
    have hs4 : ∀ a, a < P.bh + 8 * 2 ^ P.TB → c₄.nmem a = c₃.nmem a := fun a ha =>
      hN₄ a (Or.inl ha)
    refine ⟨?_, fun y hy => ?_, fun h => ?_, ?_, ?_, fun a ha => ?_, fun a h1 h2 => ?_,
      fun a ha => ?_, hT₃.of fun r h1 h2 => hK₄ r (by omega), ⟨fun r hr => ?_, fun r hr => ?_,
        by rw [hO₄, ← hc₃]; exact hO2⟩⟩
    · rw [f210] at hk₄
      have := lg_lt_pow (show (2 ^ P.TB + x) / 2 < 2 ^ P.TB by omega)
      unfold tUpCost at hk₄
      omega
    · unfold tPr; rw [hs4 _ (by omega)]; exact hpr₃ y hy
    · rw [hM₄, M3]; exact hk2 h
    · refine hW₄.congr (fun y hy => ?_) (fun y hy => by unfold tKey; rw [hM₄])
      unfold tPr; rw [hs4 _ (by omega)]
    · refine hWl₄.congr (fun y hy => ?_) (fun _ _ => rfl)
      unfold tPr; rw [hs4 _ (by omega)]
    · rw [hN₄ a (by omega), N3]; exact hn2 a (by omega)
    · rw [hs4 a h1, N3]; exact hn2 a h2
    · rw [hM₄, M3]; exact hr2 a ha
    · simp only [BSn] at hr
      rw [hK₄ r (by omega)]; exact k3 r (by omega)
    · rw [hR₄ r (by omega) (by omega), ← hc₃]; config_simp; exact hR2 r (by omega)
  refine spec_seq ?_
  by_cases hp : tPr Q c.nmem w < 1
  · refine spec_ifLtN_true (by rw [f282, fK 110 (by omega), hG.r110]; exact hp) ?_
    refine spec_instr (Exec.storeN hw₁ 286 117) fun hw₂ => ?_
    obtain ⟨c', k', ex, hk, rest⟩ := post _ 2 hw₂ (by omega) (by config_simp)
      (by config_simp; rw [fO]) (fun r hr => by config_simp; rw [fR r hr])
      (fun a ha => by config_simp; rw [f286, upd_other _ _ _ ha, fN])
      (fun a _ => by config_simp; rw [fM])
      (by unfold tPr at hp ⊢; config_simp; rw [f286, upd_same, fK 117 (by omega), hG.r117,
        iteF (by omega)])
      (fun h => absurd h (by omega))
    exact ⟨c', k', ex, by omega, rest⟩
  · refine spec_ifLtN_false (by rw [f282, fK 110 (by omega), hG.r110]; exact hp) ?_
    exec_block
    obtain ⟨c', k', ex, hk, rest⟩ := post _ 4 ‹_› (by omega) (by config_simp)
      (by config_simp; rw [fO]) (fun r hr => by config_simp; rw [fR r hr])
      (fun a ha => by config_simp; rw [f286, upd_other _ _ _ ha, fN])
      (fun a ha => by config_simp; rw [f286, upd_other _ _ _ ha, fM])
      (by
        have h1 : tPr Q c.nmem w = 1 := by have := hprb w hr; omega
        unfold tPr at h1 ⊢; config_simp; rw [f286, upd_same, fK 110 (by omega), hG.r110, iteT h1])
      (fun h => by unfold tKey; config_simp; rw [f286, upd_same, r280]; rfl)
    exact ⟨c', k', ex, by omega, rest⟩

/-! ### The range-minimum structures of the half blocks -/

section rmreg

variable {t k : ℕ}

lemma rb_le_rbB : P.rb ≤ rbB P t k := by unfold rbB; omega

/-- **The range-minimum structure of a half block fits below the word bound.** -/
lemma rbB_le_W (hL : Lay P) (ht : 2 ^ t < P.b) (hk : k * 2 ^ t < P.b) :
    rbB P t k + 4 * (t + 2) * 2 ^ t ≤ P.W := by
  have hw := hL.wx
  have h1 := lt_Lv' ht
  have h3 : 4 * (t + 2) * 2 ^ t ≤ 4 * P.Lv * 2 ^ t + 4 * 2 ^ t := by
    have := Nat.mul_le_mul_right (2 ^ t) h1; nlinarith
  have h4 : 4 * P.Lv * (k * 2 ^ t) + 4 * P.Lv * 2 ^ t ≤ 8 * P.b * P.Lv := by
    have := Nat.mul_le_mul_left (4 * P.Lv) (show k * 2 ^ t + 2 ^ t ≤ 2 * P.b by omega)
    nlinarith
  have h5 : 8 * P.b * P.Lv * t + 8 * P.b * P.Lv ≤ 8 * P.b * P.Lv * P.Lv := by
    have := Nat.mul_le_mul_left (8 * P.b * P.Lv) h1; nlinarith
  unfold rbB; nlinarith

/-- **The parameters of the range-minimum structure of a half block with a source** fit. -/
lemma rmLay_rbB (hL : Lay P) (ht : 2 ^ t < P.b) (hk : k * 2 ^ t < P.b)
    (hnc : 0 < hbNc P.b (2 ^ t) k) : RM.RMLay (rmp P (rbB P t k) (2 ^ t) k) := by
  have hT := rmp_T (P := P) (B := rbB P t k) (k := k) (rfl : 2 ^ t = 2 ^ t)
  have hs := rmp_s (P := P) (B := rbB P t k) (k := k) (rfl : 2 ^ t = 2 ^ t)
  have hW := rbB_le_W hL ht hk
  have := hL.m1; have := hL.m2; have := hL.m3; have := hL.m4; have := hL.m5; have := hL.m6
  have := hL.w; have := hL.bN
  have hsb : sib k * 2 ^ t + hbNc P.b (2 ^ t) k ≤ P.b := by unfold hbNc at hnc ⊢; omega
  have hA : (sib k * 2 ^ t + hbNc P.b (2 ^ t) k) * P.b ≤ P.b * P.b :=
    Nat.mul_le_mul_right _ hsb
  have hr : hbNr P.b (2 ^ t) k + k * 2 ^ t ≤ P.b := by unfold hbNr; omega
  have := Nat.one_le_two_pow (n := t)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show 1 ≤ hbNr _ _ _; unfold hbNr; omega
  · rw [hs]; show hbNr _ _ _ ≤ _; unfold hbNr; omega
  · rw [hT, hs]; exact hW
  · show P.Db + sib k * 2 ^ t * P.b + k * 2 ^ t + hbNc P.b (2 ^ t) k * P.b +
      hbNr P.b (2 ^ t) k ≤ P.W
    nlinarith
  · show P.pb + k * 2 ^ t + hbNr P.b (2 ^ t) k ≤ P.W; omega
  · show 2 * hbNc P.b (2 ^ t) k + 2 ≤ P.W; omega

end rmreg

/-! ### The context of a half block -/

/-- The registers of the triplet structure of the current half block (level base `r284`). -/
def tctx : Stmt :=
  block [.addN 208 122 122, .mulN 208 208 118, .addN 208 208 284, .mulN 209 121 118,
    .addN 209 209 208]

/-- **The context of the half block of the leaf `r290`** of the heap of the half blocks: its
parameters from the record of the leaf, then the context `ctxW 245` (stride `4 Lv`) and
`tctx`. -/
def bload : Stmt :=
  .seq (block [.mulN 191 290 118, .addN 191 191 241, .addN 196 191 110, .loadN 182 196,
    .addN 196 196 110, .loadN 181 196, .addN 196 196 110, .loadN 284 196, .addN 196 196 110,
    .loadN 183 196, .addN 196 196 110, .loadN 285 196]) (.seq (ctxW 245) tctx)

theorem tctx_exec {B s k TB : ℕ} (c : Config) (hc : WordsBounded P.W c) (hG : Glob P c)
    (hH : HCtx P B s k c) (h284 : c.nreg 284 = TB) (hw : TB + 16 * (k * s) + 16 * s ≤ P.W) :
    ∃ c' k', Exec I P.W tctx c c' k' ∧ k' ≤ 5 ∧ TCtx (TB + 16 * (k * s)) s c' ∧
      Fr (fun r => r = 208 ∨ r = 209) (fun _ => False) c c' ∧ c'.nmem = c.nmem ∧
      c'.rmem = c.rmem := by
  have g122 := hH.r122; have g121 := hH.r121
  unfold tctx
  exec_block
  · rw [g122]; omega
  · config_simp; rw [g122, hG.r118]; omega
  · config_simp; rw [g122, hG.r118, h284]; omega
  · config_simp; rw [g121, hG.r118]; omega
  · config_simp; rw [g121, hG.r118, g122, h284]; omega
  refine ⟨by omega, ⟨?_, ?_⟩, ⟨fun r hr => ?_, fun _ _ => rfl, rfl⟩, rfl, rfl⟩
  · config_simp; rw [g122, hG.r118, h284]; ring
  · config_simp; rw [g121, hG.r118, g122, h284]; ring
  · beta_reduce at hr; config_simp; upd_tac

/-- The parameters of a half block in the record of its leaf. -/
structure LeafP (P : Prm) (nm : ℕ → ℕ) (t k : ℕ) : Prop where
  sz : nm (P.bh + 8 * bid P t k + 1) = 2 ^ t
  lb : nm (P.bh + 8 * bid P t k + 2) = P.rb + 8 * P.b * P.Lv * t
  tb : nm (P.bh + 8 * bid P t k + 3) = P.tb + 32 * P.b * t
  idx : nm (P.bh + 8 * bid P t k + 4) = k
  off : nm (P.bh + 8 * bid P t k + 5) = t * P.b

/-- **The context of the half block of a leaf.** -/
theorem bload_exec (hL : Lay P) {t k : ℕ} (c : Config) (hc : WordsBounded P.W c)
    (hG : Glob P c) (hX : GX P c) (ht : 2 ^ t < P.b) (hk : k * 2 ^ t < P.b)
    (h290 : c.nreg 290 = bid P t k) (hP : LeafP P c.nmem t k) :
    ∃ c' k', Exec I P.W bload c c' k' ∧ k' ≤ 33 ∧ HCtx P (rbB P t k) (2 ^ t) k c' ∧
      TCtx (tbQ P t k) (2 ^ t) c' ∧ c'.nreg 182 = 2 ^ t ∧ c'.nreg 183 = k ∧
      c'.nreg 284 = P.tb + 32 * P.b * t ∧ c'.nreg 285 = t * P.b ∧
      c'.nreg 181 = P.rb + 8 * P.b * P.Lv * t ∧
      (∀ r, ¬ ((120 ≤ r ∧ r < 126) ∨ (181 ≤ r ∧ r < 184) ∨ r = 189 ∨ r = 191 ∨ r = 196 ∨
        (208 ≤ r ∧ r < 210) ∨ r = 284 ∨ r = 285) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hw := hL.wx
  have hw0 := hL.w
  have hxl := bid_lt ht hk
  have hbw : P.bh + 16 * 2 ^ P.TB ≤ P.W := by unfold Prm.rb at hw; omega
  have hs1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hLv := lt_Lv' ht
  have e8 : bid P t k * 8 + P.bh = P.bh + 8 * bid P t k := by ring
  have hkb : k < P.b := lt_of_le_of_lt (Nat.le_mul_of_pos_right k hs1) hk
  unfold bload
  refine spec_seq ?_
  exec_block
  · rw [h290, hG.r118]; omega
  · config_simp; rw [h290, hG.r118, hX.r241]; omega
  · config_simp; rw [h290, hG.r118, hX.r241, hG.r110]; omega
  · config_simp; rw [h290, hG.r118, hX.r241, hG.r110]; omega
  · config_simp; rw [h290, hG.r118, hX.r241, hG.r110]; omega
  · config_simp; rw [h290, hG.r118, hX.r241, hG.r110]; omega
  · config_simp; rw [h290, hG.r118, hX.r241, hG.r110]; omega
  generalize hc₁ : (Config.mk _ _ _ _ _ _ : Config) = c₁
  have hw₁ : WordsBounded P.W c₁ := hc₁ ▸ ‹_›
  have f182 : c₁.nreg 182 = 2 ^ t := by
    rw [← hc₁]; config_simp; rw [h290, hG.r118, hX.r241, hG.r110, e8]; exact hP.sz
  have f181 : c₁.nreg 181 = P.rb + 8 * P.b * P.Lv * t := by
    rw [← hc₁]; config_simp; rw [h290, hG.r118, hX.r241, hG.r110, e8]; exact hP.lb
  have f284 : c₁.nreg 284 = P.tb + 32 * P.b * t := by
    rw [← hc₁]; config_simp; rw [h290, hG.r118, hX.r241, hG.r110, e8]; exact hP.tb
  have f183 : c₁.nreg 183 = k := by
    rw [← hc₁]; config_simp; rw [h290, hG.r118, hX.r241, hG.r110, e8]; exact hP.idx
  have f285 : c₁.nreg 285 = t * P.b := by
    rw [← hc₁]; config_simp; rw [h290, hG.r118, hX.r241, hG.r110, e8]; exact hP.off
  have fK : ∀ r, ¬ ((181 ≤ r ∧ r < 184) ∨ r = 191 ∨ r = 196 ∨ r = 284 ∨ r = 285) →
      c₁.nreg r = c.nreg r := fun r hr => by rw [← hc₁]; config_simp; upd_tac
  have fN : c₁.nmem = c.nmem := by rw [← hc₁]
  have fM : c₁.rmem = c.rmem := by rw [← hc₁]
  have fR : c₁.rreg = c.rreg := by rw [← hc₁]
  have fO : c₁.output = c.output := by rw [← hc₁]
  have hG₁ : Glob P c₁ := hG.of fun r h1 h2 => fK r (by omega)
  have hlb : P.rb + 8 * P.b * P.Lv * t + 4 * P.Lv * (k * 2 ^ t) ≤ P.W := by
    have := rbB_le_W hL ht hk; unfold rbB at this; omega
  have f245 : c₁.nreg 245 = 4 * P.Lv := (fK 245 (by omega)).trans hX.r245
  refine spec_seq ?_
  refine spec_use (ctxW_exec (I := I) hL c₁ hw₁ hG₁ f182 f183 f181 f245 (by omega) (by omega) hk
    hs1 ht.le hlb) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hH₂, h189, hK₂, hR₂, hN₂, hM₂, hO₂⟩
  have hG₂ : Glob P c₂ := hG₁.of fun r h1 h2 => hK₂ r (by omega) (by omega)
  have htb : P.tb + 32 * P.b * t + 16 * (k * 2 ^ t) + 16 * 2 ^ t ≤ P.W := by
    have : 32 * P.b * t + 32 * P.b ≤ 32 * P.b * P.Lv := by
      have := Nat.mul_le_mul_left (32 * P.b) hLv; rw [Nat.mul_add, Nat.mul_one] at this; omega
    unfold Prm.rb Prm.bh at hw; omega
  refine spec_use (tctx_exec (I := I) c₂ hw₂ hG₂ hH₂
    (by rw [hK₂ 284 (by omega) (by omega), f284]) htb) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨hT₃, hF₃, hN₃, hM₃⟩
  have k3 : ∀ r, r ≠ 208 → r ≠ 209 → c₃.nreg r = c₂.nreg r := fun r h1 h2 =>
    hF₃.n r (by omega)
  refine ⟨by omega, hH₂.of fun r h1 h2 => k3 r (by omega) (by omega), ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · unfold tbQ; exact hT₃
  · rw [k3 182 (by omega) (by omega), hK₂ 182 (by omega) (by omega), f182]
  · rw [k3 183 (by omega) (by omega), hK₂ 183 (by omega) (by omega), f183]
  · rw [k3 284 (by omega) (by omega), hK₂ 284 (by omega) (by omega), f284]
  · rw [k3 285 (by omega) (by omega), hK₂ 285 (by omega) (by omega), f285]
  · rw [k3 181 (by omega) (by omega), hK₂ 181 (by omega) (by omega), f181]
  · rw [k3 r (by omega) (by omega), hK₂ r (by omega) (by omega)]; exact fK r (by omega)
  · funext r; rw [hF₃.r r (fun h => h), hR₂, fR]
  · rw [hN₃, hN₂, fN]
  · rw [hM₃, hM₂, fM]
  · rw [hF₃.o, hO₂, fO]

/-! ### The regions of a half block -/

section region

variable {t k : ℕ}

/-- The triplet structure of a half block lies below the heap of the half blocks. -/
lemma tbQ_le_bh (ht : 2 ^ t < P.b) (hk : k * 2 ^ t < P.b) : tbQ P t k + 16 * 2 ^ t ≤ P.bh := by
  have h1 := lt_Lv' ht
  have : 32 * P.b * t + 32 * P.b ≤ 32 * P.b * P.Lv := by
    have := Nat.mul_le_mul_left (32 * P.b) h1; rw [Nat.mul_add, Nat.mul_one] at this; omega
  unfold tbQ Prm.bh; omega

lemma tb_le_tbQ : P.tb ≤ tbQ P t k := by unfold tbQ; omega

lemma bh_le_W (hL : Lay P) : P.bh + 16 * 2 ^ P.TB ≤ P.W := by
  have := hL.wx; unfold Prm.rb at this; omega

lemma wb_le_tb : P.wb ≤ P.tb := by unfold Prm.tb Prm.hb; omega

/-- The triplet structures of two half blocks are disjoint. -/
lemma tbQ_disj {t' k' : ℕ} (ht : 2 ^ t < P.b) (hk : k * 2 ^ t < P.b) (ht' : 2 ^ t' < P.b)
    (hk' : k' * 2 ^ t' < P.b) (hne : ¬ (t = t' ∧ k = k')) :
    tbQ P t k + 16 * 2 ^ t ≤ tbQ P t' k' ∨ tbQ P t' k' + 16 * 2 ^ t' ≤ tbQ P t k := by
  unfold tbQ
  rcases Nat.lt_trichotomy t t' with h | rfl | h
  · left
    have : 32 * P.b * t + 32 * P.b ≤ 32 * P.b * t' := by
      have := Nat.mul_le_mul_left (32 * P.b) (show t + 1 ≤ t' by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    omega
  · have hkk : k ≠ k' := fun h => hne ⟨rfl, h⟩
    rcases Nat.lt_or_gt_of_ne hkk with h | h
    · left
      have : k * 2 ^ t + 2 ^ t ≤ k' * 2 ^ t := by
        have := Nat.mul_le_mul_right (2 ^ t) (show k + 1 ≤ k' by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      omega
    · right
      have : k' * 2 ^ t + 2 ^ t ≤ k * 2 ^ t := by
        have := Nat.mul_le_mul_right (2 ^ t) (show k' + 1 ≤ k by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      omega
  · right
    have : 32 * P.b * t' + 32 * P.b ≤ 32 * P.b * t := by
      have := Nat.mul_le_mul_left (32 * P.b) (show t' + 1 ≤ t by omega)
      rw [Nat.mul_add, Nat.mul_one] at this; omega
    omega

end region

/-! ### Activating a source in a half block and offering its item -/

/-- **The activation of the source `a = r260` in the half block `k` of the level `2 ^ t`**
(its context set), followed by the offer of its item to the heap of the half blocks. -/
theorem blkStep_exec (hL : Lay P) {t k a : ℕ} {e : ℕ → ℝ} {Act : ℕ → Prop} {own : ℕ → ℕ}
    {X : ℕ → Prop} {κ : ℝ} (ht : 2 ^ t < P.b) (hk : k * 2 ^ t < P.b) (c : Config)
    (hc : WordsBounded P.W c) (hE : Env P (rbB P t k) (2 ^ t) k c)
    (hT : TCtx (tbQ P t k) (2 ^ t) c) (hX : GX P c) (h260 : c.nreg 260 = a)
    (h285 : c.nreg 285 = t * P.b) (h183 : c.nreg 183 = k)
    (hR : QReady P (rbB P t k) (2 ^ t) k c.nmem)
    (he : ∀ σ < hbNc P.b (2 ^ t) k, e σ = c.rmem (P.db + (sib k * 2 ^ t + σ)))
    (hA : AntiM (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k)
      (fun ρ σ => e σ + hbF P.b P.D P.p (2 ^ t) k ρ σ))
    (hna : ¬ Act a) (ha : a < hbNc P.b (2 ^ t) k)
    (hκ : ∀ ρ < hbNr P.b (2 ^ t) k, κ ≤ e a + hbF P.b P.D P.p (2 ^ t) k ρ a)
    (hpre : (tFlag (tbQ P t k) t c.nmem = 0 ∧ (∀ σ, ¬ Act σ) ∧ (∀ ρ, ¬ X ρ) ∧
        BM P t k e own X (fun ρ => ρ < hbNr P.b (2 ^ t) k) (tbQ P t k) c.nmem c.rmem) ∨
      (tFlag (tbQ P t k) t c.nmem = 1 ∧ TRep (2 ^ t) (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k)
        (hbF P.b P.D P.p (2 ^ t) k) e Act own X κ (tbQ P t k) c.nmem c.rmem))
    (hbpr : ∀ y < 2 ^ P.TB, tPr P.bh c.nmem y ≤ 1)
    (hbW : WinOK (2 ^ P.TB) (tPr P.bh c.nmem) (tKey P.bh c.rmem) (tWn P.bh (2 ^ P.TB) c.nmem) 0)
    (hbWl : WinOK (2 ^ P.TB) (tPr P.bh c.nmem) (fun x => (x : ℝ))
      (tWl P.bh (2 ^ P.TB) c.nmem) 0) :
    ∃ c' k', Exec I P.W (.seq act bsync) c c' k' ∧
      k' + LD t * nst (tbQ P t k) (2 ^ t) c'.nmem ≤
        LD t * nst (tbQ P t k) (2 ^ t) c.nmem + actCost t + 49 * P.TB + 39 ∧
      tFlag (tbQ P t k) t c'.nmem = 1 ∧
      (∃ own', TRep (2 ^ t) (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k)
        (hbF P.b P.D P.p (2 ^ t) k) e (fun σ => Act σ ∨ σ = a) own' X κ (tbQ P t k)
          c'.nmem c'.rmem ∧ ∀ ρ, own' ρ = a ∨ own' ρ = own ρ) ∧
      (∀ y < 2 ^ P.TB, tPr P.bh c'.nmem y = if y = bid P t k then
        (if tPr (tbQ P t k) c'.nmem (tWn (tbQ P t k) (2 ^ t) c'.nmem 1) = 1 then 1 else 0)
        else tPr P.bh c.nmem y) ∧
      (tPr (tbQ P t k) c'.nmem (tWn (tbQ P t k) (2 ^ t) c'.nmem 1) = 1 →
        tKey P.bh c'.rmem (bid P t k) =
          tKey (tbQ P t k) c'.rmem (tWn (tbQ P t k) (2 ^ t) c'.nmem 1)) ∧
      WinOK (2 ^ P.TB) (tPr P.bh c'.nmem) (tKey P.bh c'.rmem) (tWn P.bh (2 ^ P.TB) c'.nmem) 0 ∧
      WinOK (2 ^ P.TB) (tPr P.bh c'.nmem) (fun x => (x : ℝ)) (tWl P.bh (2 ^ P.TB) c'.nmem) 0 ∧
      (∀ x, (x < tbQ P t k ∨ tbQ P t k + 16 * 2 ^ t ≤ x) →
        (x < P.bh ∨ P.bh + 12 * 2 ^ P.TB ≤ x ∨
          (x < P.bh + 8 * 2 ^ P.TB ∧ x ≠ P.bh + 8 * bid P t k)) → c'.nmem x = c.nmem x) ∧
      (∀ x, (x < tbQ P t k ∨ tbQ P t k + 8 * 2 ^ t ≤ x) → x ≠ P.bh + 8 * bid P t k →
        c'.rmem x = c.rmem x) ∧
      Fr (fun r => AcN r ∨ BSn r) (fun r => AcR r ∨ r = 280) c c' := by
  have hw0 := hL.w
  have hBt : rbB P t k + 8 * 2 ^ t ≤ P.W := by
    have := rbB_le_W hL ht hk
    have := Nat.mul_le_mul_right (2 ^ t) (show 8 ≤ 4 * (t + 2) by omega)
    omega
  have hQB : tbQ P t k + 16 * 2 ^ t ≤ rbB P t k := by
    have := tbQ_le_bh ht hk; have := rb_le_rbB (P := P) (t := t) (k := k)
    unfold Prm.rb at this; omega
  have hQb := tbQ_le_bh ht hk
  have hbw := bh_le_W hL
  have hxl := bid_lt ht hk
  have hQt : P.tb ≤ tbQ P t k := tb_le_tbQ
  have hwt : P.wb ≤ P.tb := wb_le_tb
  have hAS : AS P (rbB P t k) (tbQ P t k) t k a e c c :=
    ⟨hc, hE, hT, h260, hk, hBt, by omega, by omega, hQB, hR, he, Fr.refl c,
      fun _ _ => rfl, fun _ _ => rfl⟩
  refine spec_seq ?_
  obtain ⟨c₁, k₁, ex₁, hk₁, hAS₁, hf₁, own', hTR₁, hown'⟩ :=
    act_exec hL (I := I) c hAS hA hna ha hκ hpre
  refine ⟨c₁, k₁, ex₁, ?_⟩
  have hM₁ := hTR₁.mem
  have hX₁ : GX P c₁ := hX.of fun r h1 h2 => hAS₁.fr.n r (by simp only [AcN, TPn]; omega)
  have hbn : ∀ x, (x < tbQ P t k ∨ tbQ P t k + 16 * 2 ^ t ≤ x) → c₁.nmem x = c.nmem x :=
    hAS₁.nm
  have hbr : ∀ x, (x < tbQ P t k ∨ tbQ P t k + 8 * 2 ^ t ≤ x) → c₁.rmem x = c.rmem x :=
    hAS₁.rm
  have bpr : ∀ y < 2 ^ P.TB, tPr P.bh c₁.nmem y = tPr P.bh c.nmem y := fun y hy => by
    unfold tPr; exact hbn _ (Or.inr (by omega))
  have bkey : ∀ y < 2 ^ P.TB, tKey P.bh c₁.rmem y = tKey P.bh c.rmem y := fun y hy => by
    unfold tKey; exact hbr _ (Or.inr (by omega))
  have bwn : ∀ i, 1 ≤ i → i < 2 * 2 ^ P.TB → tWn P.bh (2 ^ P.TB) c₁.nmem i =
      tWn P.bh (2 ^ P.TB) c.nmem i := fun i h1 h2 => by
    unfold tWn; exact hbn _ (Or.inr (by omega))
  have bwl : ∀ i, 1 ≤ i → i < 2 * 2 ^ P.TB → tWl P.bh (2 ^ P.TB) c₁.nmem i =
      tWl P.bh (2 ^ P.TB) c.nmem i := fun i h1 h2 => by
    unfold tWl; exact hbn _ (Or.inr (by omega))
  obtain ⟨c₂, k₂, ex₂, hk₂, hp₂, hkey₂, hW₂, hWl₂, hn₂, hn₂', hr₂, hT₂, hF₂⟩ :=
    bsync_exec hL (I := I) (x := bid P t k) c₁ hAS₁.wb hAS₁.env.g hX₁ hAS₁.tc
      (by rw [hAS₁.fr.n 285 (by simp only [AcN, TPn]; omega),
        hAS₁.fr.n 183 (by simp only [AcN, TPn]; omega), h285, h183]; rfl) hxl hQb
      hM₁.win hM₁.pr01 (fun y hy => by rw [bpr y hy]; exact hbpr y hy)
      ((hbW.congr_wn bwn).congr (fun y hy => bpr y hy) (fun y hy => bkey y hy))
      ((hbWl.congr_wn bwl).congr (fun y hy => bpr y hy) (fun _ _ => rfl))
  refine ⟨c₂, k₂, ex₂, ?_⟩
  -- the half block is untouched by `bsync`
  have qn : ∀ x, x < tbQ P t k + 16 * 2 ^ t → c₂.nmem x = c₁.nmem x := fun x hx =>
    hn₂ x (Or.inl (by omega))
  have qr : ∀ x, x < tbQ P t k + 8 * 2 ^ t → c₂.rmem x = c₁.rmem x := fun x hx =>
    hr₂ x (by omega)
  have hTR₂ : TRep (2 ^ t) (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k) (hbF P.b P.D P.p (2 ^ t) k)
      e (fun σ => Act σ ∨ σ = a) own' X κ (tbQ P t k) c₂.nmem c₂.rmem :=
    ⟨hTR₁.heap, hM₁.congr_mem (fun x _ h2 => qn x (by omega)) (fun x _ h2 => qr x (by omega))⟩
  have hroot : tWn (tbQ P t k) (2 ^ t) c₂.nmem 1 = tWn (tbQ P t k) (2 ^ t) c₁.nmem 1 := by
    unfold tWn; exact qn _ (by have := Nat.one_le_two_pow (n := t); omega)
  have hr0 := (win_root hM₁.win Nat.one_le_two_pow).1
  have hpr0 : tPr (tbQ P t k) c₂.nmem (tWn (tbQ P t k) (2 ^ t) c₁.nmem 1) =
      tPr (tbQ P t k) c₁.nmem (tWn (tbQ P t k) (2 ^ t) c₁.nmem 1) := by
    unfold tPr; exact qn _ (by omega)
  have hkey0 : tKey (tbQ P t k) c₂.rmem (tWn (tbQ P t k) (2 ^ t) c₁.nmem 1) =
      tKey (tbQ P t k) c₁.rmem (tWn (tbQ P t k) (2 ^ t) c₁.nmem 1) := by
    unfold tKey; exact qr _ (by omega)
  refine ⟨?_, by unfold tFlag; rw [qn _ (by omega)]; exact hf₁, ⟨own', hTR₂, hown'⟩,
    fun y hy => ?_, fun h => ?_, hW₂, hWl₂, fun x h1 h2 => ?_, fun x h1 h2 => ?_, ?_⟩
  · have hn₂st : nst (tbQ P t k) (2 ^ t) c₂.nmem = nst (tbQ P t k) (2 ^ t) c₁.nmem := by
      unfold nst; congr 1; ext y
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> unfold tPr at h2 ⊢
      · rw [← qn _ (by omega)]; exact h2
      · rw [qn _ (by omega)]; exact h2
    rw [hn₂st]
    omega
  · rw [hp₂ y hy, hroot, hpr0, bpr y hy]
  · rw [hroot] at h ⊢; rw [hpr0] at h; rw [hkey₂ h, hkey0]
  · rcases h2 with hx | hx | ⟨hx1, hx2⟩
    · rw [hn₂ x (Or.inl hx), hbn x h1]
    · rw [hn₂ x (Or.inr hx), hbn x h1]
    · rw [hn₂' x hx1 hx2, hbn x h1]
  · rw [hr₂ x h2, hbr x h1]
  · exact hAS₁.fr.trans hF₂ (fun r h => Or.inl h) (fun r h => Or.inr h) (fun r h => Or.inl h)
      (fun r h => by clear * - h; simp only [AcR, TPr] at h ⊢; omega)

/-! ### Extracting the item of a half block and offering the next one -/

/-- **The extraction of the item of the half block `k` of the level `2 ^ t`** (its context set),
followed by the offer of its next item to the heap of the half blocks. -/
theorem extStep_exec (hL : Lay P) {t k : ℕ} {e : ℕ → ℝ} {Act : ℕ → Prop} {own : ℕ → ℕ}
    {X : ℕ → Prop} {κ κ' : ℝ} (ht : 2 ^ t < P.b) (hk : k * 2 ^ t < P.b) (c : Config)
    (hc : WordsBounded P.W c) (hE : Env P (rbB P t k) (2 ^ t) k c)
    (hT : TCtx (tbQ P t k) (2 ^ t) c) (hX : GX P c)
    (h285 : c.nreg 285 = t * P.b) (h183 : c.nreg 183 = k)
    (hR : QReady P (rbB P t k) (2 ^ t) k c.nmem)
    (hTR : TRep (2 ^ t) (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k) (hbF P.b P.D P.p (2 ^ t) k) e
      Act own X κ (tbQ P t k) c.nmem c.rmem)
    (he : ∀ σ, Act σ → e σ = c.rmem (P.db + (sib k * 2 ^ t + σ)))
    {x : ℕ} (hx : x < 2 ^ t) (hpx : tPr (tbQ P t k) c.nmem x = 1) (hκ : κ ≤ κ')
    (hval : tKey (tbQ P t k) c.rmem (tWn (tbQ P t k) (2 ^ t) c.nmem 1) ≤ κ')
    (hbpr : ∀ y < 2 ^ P.TB, tPr P.bh c.nmem y ≤ 1)
    (hbW : WinOK (2 ^ P.TB) (tPr P.bh c.nmem) (tKey P.bh c.rmem) (tWn P.bh (2 ^ P.TB) c.nmem) 0)
    (hbWl : WinOK (2 ^ P.TB) (tPr P.bh c.nmem) (fun x => (x : ℝ))
      (tWl P.bh (2 ^ P.TB) c.nmem) 0) :
    ∃ c' k', Exec I P.W (.seq ext bsync) c c' k' ∧ k' ≤ extCost t + 49 * P.TB + 30 ∧
      nst (tbQ P t k) (2 ^ t) c'.nmem ≤ nst (tbQ P t k) (2 ^ t) c.nmem + 1 ∧
      c'.nreg 254 = tMin (tbQ P t k) c.nmem (tWn (tbQ P t k) (2 ^ t) c.nmem 1) ∧
      c'.rreg 250 = tKey (tbQ P t k) c.rmem (tWn (tbQ P t k) (2 ^ t) c.nmem 1) ∧
      TRep (2 ^ t) (hbNr P.b (2 ^ t) k) (hbNc P.b (2 ^ t) k) (hbF P.b P.D P.p (2 ^ t) k) e Act
        own (fun ρ => X ρ ∨ ρ = tMin (tbQ P t k) c.nmem (tWn (tbQ P t k) (2 ^ t) c.nmem 1)) κ'
        (tbQ P t k) c'.nmem c'.rmem ∧
      tFlag (tbQ P t k) t c'.nmem = tFlag (tbQ P t k) t c.nmem ∧
      (∀ y < 2 ^ P.TB, tPr P.bh c'.nmem y = if y = bid P t k then
        (if tPr (tbQ P t k) c'.nmem (tWn (tbQ P t k) (2 ^ t) c'.nmem 1) = 1 then 1 else 0)
        else tPr P.bh c.nmem y) ∧
      (tPr (tbQ P t k) c'.nmem (tWn (tbQ P t k) (2 ^ t) c'.nmem 1) = 1 →
        tKey P.bh c'.rmem (bid P t k) =
          tKey (tbQ P t k) c'.rmem (tWn (tbQ P t k) (2 ^ t) c'.nmem 1)) ∧
      WinOK (2 ^ P.TB) (tPr P.bh c'.nmem) (tKey P.bh c'.rmem) (tWn P.bh (2 ^ P.TB) c'.nmem) 0 ∧
      WinOK (2 ^ P.TB) (tPr P.bh c'.nmem) (fun x => (x : ℝ)) (tWl P.bh (2 ^ P.TB) c'.nmem) 0 ∧
      (∀ x, (x < tbQ P t k ∨ tbQ P t k + 12 * 2 ^ t ≤ x) →
        (x < P.bh ∨ P.bh + 12 * 2 ^ P.TB ≤ x ∨
          (x < P.bh + 8 * 2 ^ P.TB ∧ x ≠ P.bh + 8 * bid P t k)) → c'.nmem x = c.nmem x) ∧
      (∀ x, (x < tbQ P t k ∨ tbQ P t k + 8 * 2 ^ t ≤ x) → x ≠ P.bh + 8 * bid P t k →
        c'.rmem x = c.rmem x) ∧
      Fr (fun r => ExN r ∨ BSn r) (fun r => ExR r ∨ r = 280) c c' := by
  have hBt : rbB P t k + 8 * 2 ^ t ≤ P.W := by
    have := rbB_le_W hL ht hk
    have := Nat.mul_le_mul_right (2 ^ t) (show 8 ≤ 4 * (t + 2) by omega)
    omega
  have hQB : tbQ P t k + 16 * 2 ^ t ≤ rbB P t k := by
    have := tbQ_le_bh ht hk; have := rb_le_rbB (P := P) (t := t) (k := k)
    unfold Prm.rb at this; omega
  have hQb := tbQ_le_bh ht hk
  have hbw := bh_le_W hL
  have hxl := bid_lt ht hk
  have hQt : P.tb ≤ tbQ P t k := tb_le_tbQ
  have hwt : P.wb ≤ P.tb := wb_le_tb
  refine spec_seq ?_
  refine spec_use (ext_exec hL (I := I) c hc hE hT hBt (by omega) (by omega)
    hQB hR
    hTR he hx hpx hκ hval) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨hTR₁, hn₁, h254, h250, hF₁, hbn, hbr⟩
  have hM₁ := hTR₁.mem
  have kk : ∀ r, ¬ ExN r → c₁.nreg r = c.nreg r := hF₁.n
  have hX₁ : GX P c₁ := hX.of fun r h1 h2 => kk r (by simp only [ExN, TPn]; omega)
  have hG₁ : Glob P c₁ := hE.g.of fun r h1 h2 => kk r (by simp only [ExN, TPn]; omega)
  have hT₁ : TCtx (tbQ P t k) (2 ^ t) c₁ :=
    hT.of fun r h1 h2 => kk r (by simp only [ExN, TPn]; omega)
  have bpr : ∀ y < 2 ^ P.TB, tPr P.bh c₁.nmem y = tPr P.bh c.nmem y := fun y hy => by
    unfold tPr; exact hbn _ (Or.inr (by omega))
  have bkey : ∀ y < 2 ^ P.TB, tKey P.bh c₁.rmem y = tKey P.bh c.rmem y := fun y hy => by
    unfold tKey; exact hbr _ (Or.inr (by omega))
  have bwn : ∀ i, 1 ≤ i → i < 2 * 2 ^ P.TB → tWn P.bh (2 ^ P.TB) c₁.nmem i =
      tWn P.bh (2 ^ P.TB) c.nmem i := fun i h1 h2 => by
    unfold tWn; exact hbn _ (Or.inr (by omega))
  have bwl : ∀ i, 1 ≤ i → i < 2 * 2 ^ P.TB → tWl P.bh (2 ^ P.TB) c₁.nmem i =
      tWl P.bh (2 ^ P.TB) c.nmem i := fun i h1 h2 => by
    unfold tWl; exact hbn _ (Or.inr (by omega))
  refine spec_use (bsync_exec hL (I := I) (x := bid P t k) c₁ hw₁ hG₁ hX₁ hT₁
      (by rw [kk 285 (by simp only [ExN, TPn]; omega), kk 183 (by simp only [ExN, TPn]; omega),
        h285, h183]; rfl) hxl hQb
      hM₁.win hM₁.pr01 (fun y hy => by rw [bpr y hy]; exact hbpr y hy)
      ((hbW.congr_wn bwn).congr (fun y hy => bpr y hy) (fun y hy => bkey y hy))
      ((hbWl.congr_wn bwl).congr (fun y hy => bpr y hy) (fun _ _ => rfl))) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨hp₂, hkey₂, hW₂, hWl₂, hn₂, hn₂', hr₂, hT₂, hF₂⟩
  have qn : ∀ x, x < tbQ P t k + 16 * 2 ^ t → c₂.nmem x = c₁.nmem x := fun x hx =>
    hn₂ x (Or.inl (by omega))
  have qr : ∀ x, x < tbQ P t k + 8 * 2 ^ t → c₂.rmem x = c₁.rmem x := fun x hx =>
    hr₂ x (by omega)
  have hroot : tWn (tbQ P t k) (2 ^ t) c₂.nmem 1 = tWn (tbQ P t k) (2 ^ t) c₁.nmem 1 := by
    unfold tWn; exact qn _ (by have := Nat.one_le_two_pow (n := t); omega)
  have hr0 := (win_root hM₁.win Nat.one_le_two_pow).1
  have hpr0 : tPr (tbQ P t k) c₂.nmem (tWn (tbQ P t k) (2 ^ t) c₁.nmem 1) =
      tPr (tbQ P t k) c₁.nmem (tWn (tbQ P t k) (2 ^ t) c₁.nmem 1) := by
    unfold tPr; exact qn _ (by omega)
  have hkey0 : tKey (tbQ P t k) c₂.rmem (tWn (tbQ P t k) (2 ^ t) c₁.nmem 1) =
      tKey (tbQ P t k) c₁.rmem (tWn (tbQ P t k) (2 ^ t) c₁.nmem 1) := by
    unfold tKey; exact qr _ (by omega)
  have hn₂st : nst (tbQ P t k) (2 ^ t) c₂.nmem = nst (tbQ P t k) (2 ^ t) c₁.nmem := by
    unfold nst; congr 1; ext y
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> unfold tPr at h2 ⊢
    · rw [← qn _ (by omega)]; exact h2
    · rw [qn _ (by omega)]; exact h2
  refine ⟨by unfold extCost at *; omega, by rw [hn₂st]; exact hn₁,
    by rw [hF₂.n 254 (by simp only [BSn]; omega)]; exact h254,
    by rw [hF₂.r 250 (by omega)]; exact h250,
    ⟨hTR₁.heap, hM₁.congr_mem (fun x _ h2 => qn x (by omega)) (fun x _ h2 => qr x (by omega))⟩,
    by unfold tFlag; rw [qn _ (by omega), hbn _ (Or.inr le_rfl)], fun y hy => ?_, fun h => ?_,
    hW₂, hWl₂, fun x h1 h2 => ?_, fun x h1 h2 => ?_, ?_⟩
  · rw [hp₂ y hy, hroot, hpr0, bpr y hy]
  · rw [hroot] at h ⊢; rw [hpr0] at h; rw [hkey₂ h, hkey0]
  · rcases h2 with hx | hx | ⟨hx1, hx2⟩
    · rw [hn₂ x (Or.inl hx), hbn x h1]
    · rw [hn₂ x (Or.inr hx), hbn x h1]
    · rw [hn₂' x hx1 hx2, hbn x h1]
  · rw [hr₂ x h2, hbr x h1]
  · exact hF₁.trans hF₂ (fun r h => Or.inl h) (fun r h => Or.inr h) (fun r h => Or.inl h)
      (fun r h => by clear * - h; simp only [ExR, TPr] at h ⊢; omega)

end FR

end Monge

end PlanarFlow
