module

public import PlanarFlow.BKMNW.MsCutC

/-!
# The cut map of the path on the machine, part D: the root flags and the ranks

* **`vpMk`** (loop over the darts): `VP'[VL[i]] := 1` when `LF[i] ≠ 0` (the labels of the
  vertices of the path); `vpMk_exec`;
* **`rkLoop`** (loop over the darts): `RE[i] :=` the number of `j < i` with `LF[j] = 0`,
  `RK[i] :=` the number of `j < i` with `TF[j] ≠ 0`, the totals in `r8245`, `r8246`;
  `rkLoop_exec`.

Registers `8233 … 8246` (inputs `8233 = LFb`, `8234 = VLb`, `8235 = VPb'`, `8236 = m`,
`8242 = TFb`, `8243 = REb`, `8244 = RKb`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-! ### The marks of the vertices of the path -/

def vpRd : Stmt := block [.addN 8240 8233 8237, .loadN 8241 8240]
def vpSt : Stmt := block [.addN 8240 8234 8237, .loadN 8241 8240, .addN 8240 8235 8241,
  .storeN 8240 8238]
def vpInc : Stmt := block [.addN 8237 8237 8238]
def vpBody : Stmt := .seq vpRd (.seq (.ifLtN 8239 8241 vpSt .skip) vpInc)

/-- **The marks of the vertices of the path.** -/
def vpMk : Stmt :=
  .seq (block [.constN 8238 1, .constN 8239 0, .constN 8237 0]) (.whileLtN 8237 8236 vpBody)

theorem vpInc_exec (d : Config) (hd : WordsBounded W d) {i : ℕ} (s37 : d.nreg 8237 = i)
    (s38 : d.nreg 8238 = 1) (hw : i + 1 ≤ W) :
    ∃ d' k, Exec P W vpInc d d' k ∧ k = 1 ∧ d'.nreg 8237 = i + 1 ∧
      (∀ x, x ≠ 8237 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧
      d'.rmem = d.rmem ∧ d'.output = d.output := by
  unfold vpInc
  exec_block
  all_goals try ((try config_simp); (try simp only [s37, s38]); omega)
  refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [s37, s38]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem vpBody_exec (c : Config) (hc : WordsBounded W c) {LFb VLb VPb m i : ℕ}
    (r33 : c.nreg 8233 = LFb) (r34 : c.nreg 8234 = VLb) (r35 : c.nreg 8235 = VPb)
    (r37 : c.nreg 8237 = i) (r38 : c.nreg 8238 = 1) (r39 : c.nreg 8239 = 0) (hi : i < m)
    (hvl : c.nmem (VLb + i) ≤ m) (w1 : LFb + m ≤ W) (w2 : VLb + m ≤ W) (w3 : VPb + m + 1 ≤ W) :
    ∃ c' k, Exec P W vpBody c c' k ∧ k ≤ 9 ∧ c'.nreg 8237 = i + 1 ∧
      c'.nmem = (if 0 < c.nmem (LFb + i) then upd c.nmem (VPb + c.nmem (VLb + i)) 1
        else c.nmem) ∧
      (∀ x, x ≠ 8237 → x ≠ 8240 → x ≠ 8241 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a41, aR, am, ar, arm, ao⟩ : ∃ c₁ k₁, Exec P W vpRd c c₁ k₁ ∧
      k₁ = 2 ∧ c₁.nreg 8241 = c.nmem (LFb + i) ∧
      (∀ x, x ≠ 8240 → x ≠ 8241 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold vpRd
    exec_block
    all_goals try ((try config_simp); (try simp only [r33, r37]); omega)
    refine ⟨rfl, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals first
      | (simp only [r33, r37]; done)
      | (simp only [upd_apply]; split_ifs <;> omega)
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 8240 → x ≠ 8241 → c₁.nreg x = c.nreg x := aR
  by_cases hs : 0 < c.nmem (LFb + i)
  · obtain ⟨c₂, k₂, e₂, hk₂, bR, bm, br, brm, bo⟩ : ∃ c₂ k₂, Exec P W vpSt c₁ c₂ k₂ ∧
        k₂ = 4 ∧ (∀ x, x ≠ 8240 → x ≠ 8241 → c₂.nreg x = c₁.nreg x) ∧
        c₂.nmem = upd c.nmem (VPb + c.nmem (VLb + i)) 1 ∧
        c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
      have s34 : c₁.nreg 8234 = VLb := by rw [q _ (by omega) (by omega), r34]
      have s35 : c₁.nreg 8235 = VPb := by rw [q _ (by omega) (by omega), r35]
      have s37 : c₁.nreg 8237 = i := by rw [q _ (by omega) (by omega), r37]
      have s38 : c₁.nreg 8238 = 1 := by rw [q _ (by omega) (by omega), r38]
      unfold vpSt
      exec_block
      all_goals try ((try config_simp); (try simp only [s34, s35, s37, s38, am]); omega)
      refine ⟨rfl, fun x a b => ?_, ?_, rfl, rfl, rfl⟩
      all_goals config_simp
      all_goals first
        | (simp only [s34, s35, s37, s38, am]; done)
        | (simp only [upd_apply]; split_ifs <;> omega)
    obtain ⟨c₃, k₃, e₃, hk₃, d37, dR, dm, dr, drm, dout⟩ := vpInc_exec (P := P) c₂ e₂.wb_right
      (by rw [bR _ (by omega) (by omega), q _ (by omega) (by omega), r37])
      (by rw [bR _ (by omega) (by omega), q _ (by omega) (by omega), r38]) (by omega)
    have t : c₁.nreg 8239 < c₁.nreg 8241 := by
      rw [a41, q _ (by omega) (by omega), r39]; exact hs
    refine ⟨c₃, k₁ + ((k₂ + 1) + k₃), .seq e₁ (.seq (.ifLtN_true t e₂) e₃), by omega, d37,
      by rw [dm, bm, iteT hs], fun x h1 h2 h3 => ?_, by rw [dr, br, ar], by rw [drm, brm, arm],
      by rw [dout, bo, ao]⟩
    rw [dR x h1, bR x h2 h3, q x h2 h3]
  · obtain ⟨c₃, k₃, e₃, hk₃, d37, dR, dm, dr, drm, dout⟩ := vpInc_exec (P := P) c₁ hw₁
      (by rw [q _ (by omega) (by omega), r37]) (by rw [q _ (by omega) (by omega), r38])
      (by omega)
    have t : ¬ c₁.nreg 8239 < c₁.nreg 8241 := by
      rw [a41, q _ (by omega) (by omega), r39]; exact hs
    refine ⟨c₃, k₁ + ((0 + 2) + k₃), .seq e₁ (.seq (.ifLtN_false t (.skip hw₁)) e₃),
      by omega, d37, by rw [dm, am, iteF hs], fun x h1 h2 h3 => ?_, by rw [dr, ar],
      by rw [drm, arm], by rw [dout, ao]⟩
    rw [dR x h1, q x h2 h3]

/-- **The marks of the vertices of the path**: from `VP'` zero on `[1, m]`, labels
`VL[i] = vl i ∈ [1, m]`, flags `LF[i] = lf i`, within `11 m + 5` steps
`VP'[l] = [∃ i < m, 0 < lf i ∧ vl i = l]` for `1 ≤ l ≤ m`; memory outside
`[VPb + 1, VPb + m]`, registers outside `8237 … 8241`, reals and output kept. -/
theorem vpMk_exec (c : Config) (hc : WordsBounded W c) {LFb VLb VPb m : ℕ} {vl lf : ℕ → ℕ}
    (r33 : c.nreg 8233 = LFb) (r34 : c.nreg 8234 = VLb) (r35 : c.nreg 8235 = VPb)
    (r36 : c.nreg 8236 = m) (hvl : ∀ i < m, c.nmem (VLb + i) = vl i ∧ 1 ≤ vl i ∧ vl i ≤ m)
    (hlf : ∀ i < m, c.nmem (LFb + i) = lf i)
    (hz : ∀ l, 1 ≤ l → l ≤ m → c.nmem (VPb + l) = 0)
    (dL : LFb + m ≤ VPb + 1 ∨ VPb + m + 1 ≤ LFb) (dV : VLb + m ≤ VPb + 1 ∨ VPb + m + 1 ≤ VLb)
    (w1 : LFb + m ≤ W) (w2 : VLb + m ≤ W) (w3 : VPb + m + 1 ≤ W) :
    ∃ c' k, Exec P W vpMk c c' k ∧ k ≤ 11 * m + 5 ∧
      (∀ l, 1 ≤ l → l ≤ m → c'.nmem (VPb + l) = if ∃ i < m, 0 < lf i ∧ vl i = l then 1 else 0) ∧
      (∀ a, (a ≤ VPb ∨ VPb + m < a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 8237 ∨ 8241 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold vpMk
  obtain ⟨c₁, k₁, e₁, hk₁, g8, g9, g7, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 8238 1, .constN 8239 0, .constN 8237 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 8238 = 1 ∧ c₁.nreg 8239 = 0 ∧ c₁.nreg 8237 = 0 ∧
      (∀ x, (x < 8237 ∨ 8239 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i d =>
    (∀ x, (x < 8237 ∨ 8241 < x) → d.nreg x = c.nreg x) ∧ d.nreg 8238 = 1 ∧ d.nreg 8239 = 0 ∧
    (∀ l, 1 ≤ l → l ≤ m → d.nmem (VPb + l) = if ∃ i' < i, 0 < lf i' ∧ vl i' = l then 1 else 0) ∧
    (∀ a, (a ≤ VPb ∨ VPb + m < a) → d.nmem a = c.nmem a) ∧
    d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h37, j1, j2, j3, j4, j5, j6, j7, j8⟩ := lnRange (P := P)
    (a := 8237) (b := 8236) (body := vpBody) J (B := 9) c₁ e₁.wb_right g7
    (by rw [gn₁ _ (by omega), r36]) (Nat.zero_le m)
    ⟨fun x hx => gn₁ x (by omega), g8, g9, fun l h1 h2 => by rw [gm₁, hz l h1 h2]; simp,
      fun a _ => by rw [gm₁], gr₁, grm₁, go₁⟩
    (fun i d hlo hhi hw h37 h36 ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ => by
      obtain ⟨ev, ev1, ev2⟩ := hvl i hhi
      have e1 : d.nmem (VLb + i) = vl i := by rw [j5 _ (by omega), ev]
      have e2 : d.nmem (LFb + i) = lf i := by rw [j5 _ (by omega), hlf i hhi]
      obtain ⟨d', k, ex, hk, h37', hm, hR, hr, hrm, ho⟩ := vpBody_exec (P := P) d hw
        (by rw [j1 _ (by omega), r33]) (by rw [j1 _ (by omega), r34])
        (by rw [j1 _ (by omega), r35]) h37 j2 j3 hhi (by rw [e1]; exact ev2) w1 w2 w3
      rw [e1, e2] at hm
      have hiff : ∀ l, (∃ i' < i + 1, 0 < lf i' ∧ vl i' = l) ↔
          (∃ i' < i, 0 < lf i' ∧ vl i' = l) ∨ (0 < lf i ∧ vl i = l) := fun l => by
        constructor
        · rintro ⟨i', hi', h⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
          · exact Or.inl ⟨i', hi', h⟩
          · exact Or.inr h
        · rintro (⟨i', hi', h⟩ | h)
          · exact ⟨i', by omega, h⟩
          · exact ⟨i, by omega, h⟩
      refine ⟨d', k, ex, hk, h37', by rw [hR _ (by omega) (by omega) (by omega)]; exact h36,
        fun x hx => by rw [hR x (by omega) (by omega) (by omega), j1 x hx],
        by rw [hR _ (by omega) (by omega) (by omega), j2],
        by rw [hR _ (by omega) (by omega) (by omega), j3], fun l h1 h2 => ?_, fun a ha => ?_,
        by rw [hr, j6],
        by rw [hrm, j7], by rw [ho, j8]⟩
      · rw [hm]
        by_cases hs : 0 < lf i
        · rw [iteT hs]
          by_cases hl : vl i = l
          · subst hl; rw [upd_same, iteT ((hiff _).2 (Or.inr ⟨hs, rfl⟩))]
          · rw [upd_other _ _ _ (by omega), j4 l h1 h2]; simp only [hiff, hl, and_false, or_false]
        · rw [iteF hs, j4 l h1 h2]; simp only [hiff, hs, false_and, or_false]
      · rw [hm]
        split_ifs
        · rw [upd_other _ _ _ (by omega)]; exact j5 a ha
        · exact j5 a ha)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by norm_num at hk₂; omega, j4, j5, j1, j6, j7, j8⟩

/-! ### The ranks -/

def rkA : Stmt :=
  block [.addN 8240 8243 8237, .storeN 8240 8245, .addN 8240 8244 8237, .storeN 8240 8246,
    .addN 8240 8233 8237, .loadN 8241 8240]
def rkIncE : Stmt := block [.addN 8245 8245 8238]
def rkB : Stmt := block [.addN 8240 8242 8237, .loadN 8241 8240]
def rkIncT : Stmt := block [.addN 8246 8246 8238]
def rkBody : Stmt :=
  .seq rkA (.seq (.ifLtN 8241 8238 rkIncE .skip) (.seq rkB
    (.seq (.ifLtN 8239 8241 rkIncT .skip) vpInc)))

/-- **The ranks.** -/
def rkLoop : Stmt :=
  .seq (block [.constN 8238 1, .constN 8239 0, .constN 8237 0, .constN 8245 0, .constN 8246 0])
    (.whileLtN 8237 8236 rkBody)

theorem rkIncE_exec (d : Config) (hd : WordsBounded W d) (s38 : d.nreg 8238 = 1)
    (hw : d.nreg 8245 + 1 ≤ W) :
    ∃ d' k, Exec P W (.ifLtN 8241 8238 rkIncE .skip) d d' k ∧ k ≤ 2 ∧
      d'.nreg 8245 = d.nreg 8245 + (if d.nreg 8241 < 1 then 1 else 0) ∧
      (∀ x, x ≠ 8245 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  by_cases h : d.nreg 8241 < 1
  · have t : d.nreg 8241 < d.nreg 8238 := by rw [s38]; exact h
    obtain ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ : ∃ d' k, Exec P W rkIncE d d' k ∧ k = 1 ∧
        d'.nreg 8245 = d.nreg 8245 + 1 ∧ (∀ x, x ≠ 8245 → d'.nreg x = d.nreg x) ∧
        d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
      unfold rkIncE
      exec_block
      all_goals try ((try config_simp); (try simp only [s38]); omega)
      refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; simp only [s38]
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
    exact ⟨d', k + 1, .ifLtN_true t ex, by omega, by rw [h1, iteT h], h2, h3, h4, h5, h6⟩
  · have t : ¬ d.nreg 8241 < d.nreg 8238 := by rw [s38]; exact h
    exact ⟨d, 0 + 2, .ifLtN_false t (.skip hd), by omega, by rw [iteF h]; rfl,
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem rkIncT_exec (d : Config) (hd : WordsBounded W d) (s38 : d.nreg 8238 = 1)
    (s39 : d.nreg 8239 = 0) (hw : d.nreg 8246 + 1 ≤ W) :
    ∃ d' k, Exec P W (.ifLtN 8239 8241 rkIncT .skip) d d' k ∧ k ≤ 2 ∧
      d'.nreg 8246 = d.nreg 8246 + (if 0 < d.nreg 8241 then 1 else 0) ∧
      (∀ x, x ≠ 8246 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  by_cases h : 0 < d.nreg 8241
  · have t : d.nreg 8239 < d.nreg 8241 := by rw [s39]; exact h
    obtain ⟨d', k, ex, hk, h1, h2, h3, h4, h5, h6⟩ : ∃ d' k, Exec P W rkIncT d d' k ∧ k = 1 ∧
        d'.nreg 8246 = d.nreg 8246 + 1 ∧ (∀ x, x ≠ 8246 → d'.nreg x = d.nreg x) ∧
        d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
      unfold rkIncT
      exec_block
      all_goals try ((try config_simp); (try simp only [s38]); omega)
      refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; simp only [s38]
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
    exact ⟨d', k + 1, .ifLtN_true t ex, by omega, by rw [h1, iteT h], h2, h3, h4, h5, h6⟩
  · have t : ¬ d.nreg 8239 < d.nreg 8241 := by rw [s39]; exact h
    exact ⟨d, 0 + 2, .ifLtN_false t (.skip hd), by omega, by rw [iteF h]; rfl,
      fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem rkBody_exec (c : Config) (hc : WordsBounded W c) {LFb TFb REb RKb m i cE cT : ℕ}
    (r33 : c.nreg 8233 = LFb) (r42 : c.nreg 8242 = TFb) (r43 : c.nreg 8243 = REb)
    (r44 : c.nreg 8244 = RKb) (r37 : c.nreg 8237 = i) (r38 : c.nreg 8238 = 1)
    (r39 : c.nreg 8239 = 0) (r45 : c.nreg 8245 = cE) (r46 : c.nreg 8246 = cT) (hi : i < m)
    (hcE : cE ≤ i) (hcT : cT ≤ i)
    (dE1 : REb + i ≠ LFb + i) (dE2 : RKb + i ≠ LFb + i) (dE3 : REb + i ≠ TFb + i)
    (dE4 : RKb + i ≠ TFb + i)
    (w1 : LFb + m ≤ W) (w2 : TFb + m ≤ W) (w3 : REb + m ≤ W) (w4 : RKb + m ≤ W) (w5 : m + 1 ≤ W) :
    ∃ c' k, Exec P W rkBody c c' k ∧ k ≤ 15 ∧ c'.nreg 8237 = i + 1 ∧
      c'.nreg 8245 = cE + (if c.nmem (LFb + i) < 1 then 1 else 0) ∧
      c'.nreg 8246 = cT + (if 0 < c.nmem (TFb + i) then 1 else 0) ∧
      c'.nmem = upd (upd c.nmem (REb + i) cE) (RKb + i) cT ∧
      (∀ x, x ≠ 8237 → x ≠ 8240 → x ≠ 8241 → x ≠ 8245 → x ≠ 8246 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hLF : upd (upd c.nmem (REb + i) cE) (RKb + i) cT (LFb + i) = c.nmem (LFb + i) := by
    rw [upd_other _ _ _ (Ne.symm dE2), upd_other _ _ _ (Ne.symm dE1)]
  have hTF : upd (upd c.nmem (REb + i) cE) (RKb + i) cT (TFb + i) = c.nmem (TFb + i) := by
    rw [upd_other _ _ _ (Ne.symm dE4), upd_other _ _ _ (Ne.symm dE3)]
  obtain ⟨c₁, k₁, e₁, hk₁, a41, aR, am, ar, arm, ao⟩ : ∃ c₁ k₁, Exec P W rkA c c₁ k₁ ∧
      k₁ = 6 ∧ c₁.nreg 8241 = c.nmem (LFb + i) ∧
      (∀ x, x ≠ 8240 → x ≠ 8241 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = upd (upd c.nmem (REb + i) cE) (RKb + i) cT ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold rkA
    exec_block
    all_goals try ((try config_simp); (try simp only [r33, r43, r44, r37, r45, r46, hLF]); omega)
    refine ⟨rfl, ?_, fun x a b => ?_, ?_, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals first
      | (simp only [r33, r43, r44, r37, r45, r46, hLF]; done)
      | (simp only [upd_apply]; split_ifs <;> omega)
  have q1 : ∀ x, x ≠ 8240 → x ≠ 8241 → c₁.nreg x = c.nreg x := aR
  obtain ⟨c₂, k₂, e₂, hk₂, b45, bR, bm, br, brm, bo⟩ := rkIncE_exec (P := P) c₁ e₁.wb_right
    (by rw [q1 _ (by omega) (by omega), r38]) (by rw [q1 _ (by omega) (by omega), r45]; omega)
  have q2 : ∀ x, x ≠ 8240 → x ≠ 8241 → x ≠ 8245 → c₂.nreg x = c.nreg x := fun x h1 h2 h3 => by
    rw [bR x h3, q1 x h1 h2]
  obtain ⟨c₃, k₃, e₃, hk₃, d41, dR, dm, dr, drm, dout⟩ : ∃ c₃ k₃, Exec P W rkB c₂ c₃ k₃ ∧
      k₃ = 2 ∧ c₃.nreg 8241 = c.nmem (TFb + i) ∧
      (∀ x, x ≠ 8240 → x ≠ 8241 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have s42 : c₂.nreg 8242 = TFb := by rw [q2 _ (by omega) (by omega) (by omega), r42]
    have s37 : c₂.nreg 8237 = i := by rw [q2 _ (by omega) (by omega) (by omega), r37]
    have hw₂ := e₂.wb_right
    unfold rkB
    exec_block
    all_goals try ((try config_simp); (try simp only [s42, s37, bm, am, hTF]); omega)
    refine ⟨rfl, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    all_goals first
      | (simp only [s42, s37, bm, am, hTF]; done)
      | (simp only [upd_apply]; split_ifs <;> omega)
  have q3 : ∀ x, x ≠ 8240 → x ≠ 8241 → x ≠ 8245 → c₃.nreg x = c.nreg x := fun x h1 h2 h3 => by
    rw [dR x h1 h2, q2 x h1 h2 h3]
  obtain ⟨c₄, k₄, e₄, hk₄, f46, fR, fm, fr, frm, fo⟩ := rkIncT_exec (P := P) c₃ e₃.wb_right
    (by rw [q3 _ (by omega) (by omega) (by omega), r38])
    (by rw [q3 _ (by omega) (by omega) (by omega), r39])
    (by rw [q3 _ (by omega) (by omega) (by omega), r46]; omega)
  obtain ⟨c₅, k₅, e₅, hk₅, g37, gR, gm, gr, grm, go⟩ := vpInc_exec (P := P) c₄ e₄.wb_right
    (by rw [fR _ (by omega), q3 _ (by omega) (by omega) (by omega), r37])
    (by rw [fR _ (by omega), q3 _ (by omega) (by omega) (by omega), r38]) (by omega)
  refine ⟨c₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega,
    g37, ?_, ?_, by rw [gm, fm, dm, bm, am], fun x h1 h2 h3 h45 h46 => ?_,
    by rw [gr, fr, dr, br, ar],
    by rw [grm, frm, drm, brm, arm], by rw [go, fo, dout, bo, ao]⟩
  · rw [gR _ (by omega), fR _ (by omega), dR _ (by omega) (by omega), b45, a41,
      q1 _ (by omega) (by omega), r45]
  · rw [gR _ (by omega), f46, d41, q3 _ (by omega) (by omega) (by omega), r46]
  · rw [gR x h1, fR x h46, q3 x h2 h3 h45]

/-- **The ranks**: for flags `LF[i] = lf i ≤ 1`, `TF[i] = tf i` (`i < m`), within
`17 m + 7` steps `RE[i] = #{j < i | lf j = 0}`, `RK[i] = #{j < i | 0 < tf j}` and the totals in
`r8245`, `r8246`; memory outside `RE`, `RK`, registers outside `8237 … 8241`, `8245`, `8246`,
reals and output kept. -/
theorem rkLoop_exec (c : Config) (hc : WordsBounded W c) {LFb TFb REb RKb m : ℕ}
    {lf tf : ℕ → ℕ} (r33 : c.nreg 8233 = LFb) (r36 : c.nreg 8236 = m)
    (r42 : c.nreg 8242 = TFb) (r43 : c.nreg 8243 = REb) (r44 : c.nreg 8244 = RKb)
    (hlf : ∀ i < m, c.nmem (LFb + i) = lf i ∧ lf i ≤ 1) (htf : ∀ i < m, c.nmem (TFb + i) = tf i)
    (dE : REb + m ≤ RKb ∨ RKb + m ≤ REb)
    (dL : (LFb + m ≤ REb ∨ REb + m ≤ LFb) ∧ (LFb + m ≤ RKb ∨ RKb + m ≤ LFb))
    (dT : (TFb + m ≤ REb ∨ REb + m ≤ TFb) ∧ (TFb + m ≤ RKb ∨ RKb + m ≤ TFb))
    (w1 : LFb + m ≤ W) (w2 : TFb + m ≤ W) (w3 : REb + m ≤ W) (w4 : RKb + m ≤ W) (w5 : m + 1 ≤ W) :
    ∃ c' k, Exec P W rkLoop c c' k ∧ k ≤ 17 * m + 7 ∧
      (∀ i < m, c'.nmem (REb + i) = ((range i).filter fun j => lf j = 0).card ∧
        c'.nmem (RKb + i) = ((range i).filter fun j => 0 < tf j).card) ∧
      c'.nreg 8245 = ((range m).filter fun j => lf j = 0).card ∧
      c'.nreg 8246 = ((range m).filter fun j => 0 < tf j).card ∧
      (∀ a, (a < REb ∨ REb + m ≤ a) → (a < RKb ∨ RKb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 8237 ∨ 8241 < x) → x ≠ 8245 → x ≠ 8246 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold rkLoop
  obtain ⟨c₁, k₁, e₁, hk₁, g8, g9, g7, g45, g46, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 8238 1, .constN 8239 0, .constN 8237 0, .constN 8245 0,
        .constN 8246 0]) c c₁ k₁ ∧ k₁ = 5 ∧
      c₁.nreg 8238 = 1 ∧ c₁.nreg 8239 = 0 ∧ c₁.nreg 8237 = 0 ∧ c₁.nreg 8245 = 0 ∧
      c₁.nreg 8246 = 0 ∧
      (∀ x, (x < 8237 ∨ 8239 < x) → x ≠ 8245 → x ≠ 8246 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  let J : ℕ → Config → Prop := fun i d =>
    (∀ x, (x < 8237 ∨ 8241 < x) → x ≠ 8245 → x ≠ 8246 → d.nreg x = c.nreg x) ∧
    d.nreg 8238 = 1 ∧ d.nreg 8239 = 0 ∧
    d.nreg 8245 = ((range i).filter fun j => lf j = 0).card ∧
    d.nreg 8246 = ((range i).filter fun j => 0 < tf j).card ∧
    (∀ i' < i, d.nmem (REb + i') = ((range i').filter fun j => lf j = 0).card ∧
      d.nmem (RKb + i') = ((range i').filter fun j => 0 < tf j).card) ∧
    (∀ a, (a < REb ∨ REb + i ≤ a) → (a < RKb ∨ RKb + i ≤ a) → d.nmem a = c.nmem a) ∧
    d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h37, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10⟩ := lnRange (P := P)
    (a := 8237) (b := 8236) (body := rkBody) J (B := 15) c₁ e₁.wb_right g7
    (by rw [gn₁ _ (by omega) (by omega) (by omega), r36]) (Nat.zero_le m)
    ⟨fun x hx h1 h2 => gn₁ x (by omega) h1 h2, g8, g9, by rw [g45]; simp, by rw [g46]; simp,
      fun i' hi' => absurd hi' (by omega), fun a _ _ => by rw [gm₁], gr₁, grm₁, go₁⟩
    (fun i d hlo hhi hw h37 h36 ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9, j10⟩ => by
      have hcE := cnt_le_self (fun j => lf j = 0) i
      have hcT := cnt_le_self (fun j => 0 < tf j) i
      obtain ⟨d', k, ex, hk, h37', h45, h46, hm, hR, hr, hrm, ho⟩ := rkBody_exec (P := P) d hw
        (by rw [j1 _ (by omega) (by omega) (by omega), r33])
        (by rw [j1 _ (by omega) (by omega) (by omega), r42])
        (by rw [j1 _ (by omega) (by omega) (by omega), r43])
        (by rw [j1 _ (by omega) (by omega) (by omega), r44]) h37 j2 j3 j4 j5 hhi hcE hcT
        (by omega) (by omega) (by omega) (by omega) w1 w2 w3 w4 w5
      have e1 : d.nmem (LFb + i) = lf i := by rw [j7 _ (by omega) (by omega), (hlf i hhi).1]
      have e2 : d.nmem (TFb + i) = tf i := by rw [j7 _ (by omega) (by omega), htf i hhi]
      have hl1 := (hlf i hhi).2
      refine ⟨d', k, ex, hk, h37', by
          rw [hR _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h36,
        fun x hx h1 h2 => by rw [hR x (by omega) (by omega) (by omega) h1 h2, j1 x hx h1 h2],
        by rw [hR _ (by omega) (by omega) (by omega) (by omega) (by omega), j2],
        by rw [hR _ (by omega) (by omega) (by omega) (by omega) (by omega), j3], ?_, ?_,
        fun i' hi' => ?_,
        fun a ha ha' => ?_, by rw [hr, j8], by rw [hrm, j9], by rw [ho, j10]⟩
      · rw [h45, e1, cnt_succ]
        by_cases h0 : lf i = 0 <;> simp [h0] <;> omega
      · rw [h46, e2, cnt_succ]
      · rw [hm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
        · refine ⟨?_, ?_⟩
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact (j6 i' hi').1
          · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact (j6 i' hi').2
        · refine ⟨?_, ?_⟩
          · rw [upd_other _ _ _ (by omega), upd_same]
          · rw [upd_same]
      · rw [hm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact j7 a (by omega) (by omega))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by norm_num at hk₂; omega, j6, j4, j5,
    fun a ha ha' => j7 a ha ha', j1, j8, j9, j10⟩

end MsEnc

end BKMNW

end PlanarFlow
