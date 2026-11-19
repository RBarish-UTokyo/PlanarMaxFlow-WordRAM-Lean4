module

public import PlanarFlow.BKMNW.PrWalk

/-!
# The walk to the next non-loop dart on the machine

`pdW`: for every `i < n` (`n = r8700`), with `SG` at `B + n` (a permutation `f` of `[0, n)`), the
flags `NL` at `B + 10 n` (`fl (Q x)`), it writes at `B + 12 n + i`

* `i` if `Q i` fails,
* `f^[wlk f Q i] i` otherwise (walk `y := SG[i]`, then `y := SG[y]` while `NL[y] = 0`).

**`pdW_exec`**: within `19 n + 20` steps (the walks are amortised by `sum_wlk_le`), memory outside
`[B + 12 n, B + 13 n)`, the registers outside `8778`, `8811 … 8817`, the reals and the output kept.
Registers: `8811 = SGb`, `8812 = NLb`, `8813 = Tb`, the counter `8814`, the address `8815`, the flag
`8816`, the dart `8817`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv OrbLab

variable {P : Input} {W : ℕ}

/-- `t := NL[i]`. -/
def wRd : Stmt := block [.addN 8815 8812 8814, .loadN 8816 8815]

/-- `y := i` (a loop). -/
def wLp : Stmt := block [.copyN 8817 8814]

/-- `y := SG[i]`, `t := NL[y]`. -/
def wSt0 : Stmt := block [.addN 8815 8811 8814, .loadN 8817 8815, .addN 8815 8812 8817,
  .loadN 8816 8815]

/-- `y := SG[y]`, `t := NL[y]`. -/
def wStY : Stmt := block [.addN 8815 8811 8817, .loadN 8817 8815, .addN 8815 8812 8817,
  .loadN 8816 8815]

/-- `T[i] := y`, `i := i + 1`. -/
def wWr : Stmt := block [.addN 8815 8813 8814, .storeN 8815 8817, .addN 8814 8814 8704]

/-- The body of the walk loop at the dart `i`. -/
def wBody : Stmt := .seq wRd (.seq (.ifLtN 8816 8704 wLp (.seq wSt0 (.whileLtN 8816 8704 wStY))) wWr)

/-- **The walk loop.** -/
def pdW : Stmt := .seq (setB 8811 1) (.seq (setB 8812 10) (.seq (setB 8813 12)
  (.seq (block [.constN 8814 0]) (.whileLtN 8814 8700 wBody))))

/-- The registers written by the walk body. -/
def wR (x : ℕ) : Prop := 8814 ≤ x ∧ x ≤ 8817

section Blocks

theorem wRd_exec (c : Config) (hc : WordsBounded W c) {NLb i : ℕ} (r12 : c.nreg 8812 = NLb)
    (r14 : c.nreg 8814 = i) (hw : NLb + i ≤ W) :
    ∃ c' t, Exec P W wRd c c' t ∧ t = 2 ∧ c'.nreg 8816 = c.nmem (NLb + i) ∧
      (∀ x, x ≠ 8815 → x ≠ 8816 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wRd
  exec_block
  · config_simp; rw [r12, r14]; omega
  refine ⟨rfl, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [r12, r14]
  · config_simp; simp (disch := omega) only [upd_other]

theorem wLp_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W wLp c c' t ∧ t = 1 ∧ c'.nreg 8817 = c.nreg 8814 ∧
      (∀ x, x ≠ 8817 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wLp
  exec_block
  refine ⟨rfl, ?_, fun x h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp
  · config_simp; simp (disch := omega) only [upd_other]

theorem wSt0_exec (c : Config) (hc : WordsBounded W c) {SGb NLb i : ℕ} (r11 : c.nreg 8811 = SGb)
    (r12 : c.nreg 8812 = NLb) (r14 : c.nreg 8814 = i) (hw : SGb + i ≤ W)
    (hw' : NLb + c.nmem (SGb + i) ≤ W) :
    ∃ c' t, Exec P W wSt0 c c' t ∧ t = 4 ∧ c'.nreg 8817 = c.nmem (SGb + i) ∧
      c'.nreg 8816 = c.nmem (NLb + c.nmem (SGb + i)) ∧
      (∀ x, x ≠ 8815 → x ≠ 8816 → x ≠ 8817 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wSt0
  exec_block
  · config_simp; rw [r11, r14]; omega
  · config_simp; rw [r11, r12, r14]; omega
  refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [r11, r14]
  · config_simp; rw [r11, r12, r14]
  · config_simp; simp (disch := omega) only [upd_other]

theorem wStY_exec (c : Config) (hc : WordsBounded W c) {SGb NLb y : ℕ} (r11 : c.nreg 8811 = SGb)
    (r12 : c.nreg 8812 = NLb) (r17 : c.nreg 8817 = y) (hw : SGb + y ≤ W)
    (hw' : NLb + c.nmem (SGb + y) ≤ W) :
    ∃ c' t, Exec P W wStY c c' t ∧ t = 4 ∧ c'.nreg 8817 = c.nmem (SGb + y) ∧
      c'.nreg 8816 = c.nmem (NLb + c.nmem (SGb + y)) ∧
      (∀ x, x ≠ 8815 → x ≠ 8816 → x ≠ 8817 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wStY
  exec_block
  · config_simp; rw [r11, r17]; omega
  · config_simp; rw [r11, r12, r17]; omega
  refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; rw [r11, r17]
  · config_simp; rw [r11, r12, r17]
  · config_simp; simp (disch := omega) only [upd_other]

theorem wWr_exec (c : Config) (hc : WordsBounded W c) {Tb i : ℕ} (r13 : c.nreg 8813 = Tb)
    (r14 : c.nreg 8814 = i) (r04 : c.nreg 8704 = 1) (hw : Tb + i ≤ W) (hw' : i + 1 ≤ W) :
    ∃ c' t, Exec P W wWr c c' t ∧ t = 3 ∧ c'.nreg 8814 = i + 1 ∧
      c'.nmem = upd c.nmem (Tb + i) (c.nreg 8817) ∧
      (∀ x, x ≠ 8815 → x ≠ 8814 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold wWr
  exec_block
  · config_simp; rw [r13, r14]; omega
  · config_simp; rw [r14, r04]; omega
  refine ⟨rfl, ?_, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; rw [r14, r04]
  · config_simp; rw [r13, r14]
  · config_simp; simp (disch := omega) only [upd_other]

end Blocks

section Loop

variable {f : ℕ → ℕ} {Q : ℕ → Prop} [DecidablePred Q] {n : ℕ}

/-- The value written at the dart `x`. -/
noncomputable def wv (f : ℕ → ℕ) (Q : ℕ → Prop) [DecidablePred Q] (x : ℕ) : ℕ :=
  if Q x then f^[wlk f Q x] x else x

/-- The memory read by the walk. -/
structure WMem (f : ℕ → ℕ) (Q : ℕ → Prop) [DecidablePred Q] (n SGb NLb : ℕ) (mem : ℕ → ℕ) :
    Prop where
  sg : ∀ x < n, mem (SGb + x) = f x
  nl : ∀ x < n, mem (NLb + x) = fl (Q x)

/-- **The inner walk**: from `y = f^[j] i` (`1 ≤ j ≤ wlk i`), the loop ends at `f^[wlk i] i`
within `6 (wlk i - j) + 2` steps. -/
theorem inner_walk (hp : PermOn f n) {SGb NLb i : ℕ} (hi : i < n) (hq : Q i)
    (hW : SGb + n ≤ W) (hW' : NLb + n ≤ W) :
    ∀ k j (c : Config), wlk f Q i - j = k → 1 ≤ j → j ≤ wlk f Q i → WordsBounded W c →
      WMem f Q n SGb NLb c.nmem → c.nreg 8811 = SGb → c.nreg 8812 = NLb →
      c.nreg 8704 = 1 → c.nreg 8817 = f^[j] i → c.nreg 8816 = fl (Q (f^[j] i)) →
      ∃ c' t, Exec P W (.whileLtN 8816 8704 wStY) c c' t ∧ t ≤ 6 * k + 2 ∧
        c'.nreg 8817 = f^[wlk f Q i] i ∧
        (∀ x, x ≠ 8815 → x ≠ 8816 → x ≠ 8817 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  intro k
  induction k with
  | zero =>
    intro j c hk hj1 hj2 hc hm r11 r12 r04 r17 r16
    have hj : j = wlk f Q i := by omega
    subst hj
    have hQ := wlk_spec hp hi hq
    have : ¬ c.nreg 8816 < c.nreg 8704 := by
      rw [r16, r04]; unfold fl; rw [ppIteT hQ]; omega
    exact ⟨c, 2, .whileLtN_false this hc, by omega, r17, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ k ih =>
    intro j c hk hj1 hj2 hc hm r11 r12 r04 r17 r16
    have hlt : j < wlk f Q i := by omega
    have hnq := wlk_min hp hi hq (by omega) hlt
    have ht : c.nreg 8816 < c.nreg 8704 := by
      rw [r16, r04]; unfold fl; rw [ppIteF hnq]; omega
    have hy := OrbLab.iter_lt hp hi j
    have hy1 := OrbLab.iter_lt hp hi (j + 1)
    have hsg : c.nmem (SGb + f^[j] i) = f^[j + 1] i := by
      rw [hm.sg _ hy, Function.iterate_succ_apply']
    obtain ⟨c₁, t₁, e₁, ht₁, s17, s16, sR, sm, srr, srm, so⟩ := wStY_exec (P := P) c hc r11 r12
      r17 (by omega) (by rw [hsg]; omega)
    rw [hsg] at s17 s16
    rw [hm.nl _ hy1] at s16
    obtain ⟨c', t', e', ht', v17, vR, vm, vrr, vrm, vo⟩ := ih (j + 1) c₁ (by omega) (by omega)
      (by omega) e₁.wb_right (by rw [sm]; exact hm)
      (by rw [sR _ (by omega) (by omega) (by omega)]; exact r11)
      (by rw [sR _ (by omega) (by omega) (by omega)]; exact r12)
      (by rw [sR _ (by omega) (by omega) (by omega)]; exact r04) s17 s16
    exact ⟨c', t₁ + 2 + t', .whileLtN_true ht e₁ e', by omega, v17,
      fun x h1 h2 h3 => by rw [vR x h1 h2 h3, sR x h1 h2 h3], by rw [vm, sm],
      by rw [vrr, srr], by rw [vrm, srm], by rw [vo, so]⟩

/-- The cost of the body at the dart `i`. -/
noncomputable def wCost (f : ℕ → ℕ) (Q : ℕ → Prop) [DecidablePred Q] (i : ℕ) : ℕ :=
  6 * (if Q i then wlk f Q i - 1 else 0) + 16

/-- **The body at the dart `i`.** -/
theorem wBody_exec (hp : PermOn f n) {SGb NLb Tb i : ℕ} (hi : i < n)
    (hW : SGb + n ≤ W) (hW' : NLb + n ≤ W) (hW'' : Tb + n + 1 ≤ W) (c : Config)
    (hc : WordsBounded W c) (hm : WMem f Q n SGb NLb c.nmem) (r11 : c.nreg 8811 = SGb)
    (r12 : c.nreg 8812 = NLb) (r13 : c.nreg 8813 = Tb) (r04 : c.nreg 8704 = 1)
    (r14 : c.nreg 8814 = i) :
    ∃ c' t, Exec P W wBody c c' t ∧ t ≤ wCost f Q i ∧ c'.nreg 8814 = i + 1 ∧
      c'.nmem = upd c.nmem (Tb + i) (wv f Q i) ∧
      (∀ x, ¬ wR x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a16, aR, am, arr, arm, ao⟩ := wRd_exec (P := P) c hc r12 r14
    (by omega)
  rw [hm.nl i hi] at a16
  have k1 : ∀ x, ¬ wR x → c₁.nreg x = c.nreg x := fun x hx =>
    aR x (by unfold wR at hx; omega) (by unfold wR at hx; omega)
  have q04 : c₁.nreg 8704 = 1 := by rw [k1 _ (by unfold wR; omega)]; exact r04
  have q14 : c₁.nreg 8814 = i := by rw [aR _ (by omega) (by omega)]; exact r14
  have q11 : c₁.nreg 8811 = SGb := by rw [k1 _ (by unfold wR; omega)]; exact r11
  have q12 : c₁.nreg 8812 = NLb := by rw [k1 _ (by unfold wR; omega)]; exact r12
  have q13 : c₁.nreg 8813 = Tb := by rw [k1 _ (by unfold wR; omega)]; exact r13
  -- the branch
  obtain ⟨c₂, t₂, e₂, ht₂, b17, b14, bR, bm, brr, brm, bo⟩ : ∃ c₂ t₂,
      Exec P W (.ifLtN 8816 8704 wLp (.seq wSt0 (.whileLtN 8816 8704 wStY))) c₁ c₂ t₂ ∧
      t₂ + 7 ≤ wCost f Q i ∧ c₂.nreg 8817 = wv f Q i ∧ c₂.nreg 8814 = i ∧
      (∀ x, ¬ wR x → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases hq : Q i
    · have hnt : ¬ c₁.nreg 8816 < c₁.nreg 8704 := by
        rw [a16, q04]; unfold fl; rw [ppIteT hq]; omega
      have hf1 : f i < n := hp.lt i hi
      have hsg : c₁.nmem (SGb + i) = f^[1] i := by rw [am, hm.sg i hi]; rfl
      obtain ⟨d₁, s₁, f₁, hs₁, s17, s16, sR, sm, srr, srm, so⟩ := wSt0_exec (P := P) c₁
        e₁.wb_right q11 q12 q14 (by omega) (by rw [hsg]; simp only [Function.iterate_one]; omega)
      rw [hsg] at s17 s16
      rw [am, hm.nl _ (by simpa using hf1)] at s16
      have hw1 := wlk_pos (f := f) (Q := Q) i
      obtain ⟨d₂, s₂, f₂, hs₂, v17, vR, vm, vrr, vrm, vo⟩ := inner_walk (P := P) hp hi hq hW hW'
        (wlk f Q i - 1) 1 d₁ rfl le_rfl hw1 f₁.wb_right (by rw [sm, am]; exact hm)
        (by rw [sR _ (by omega) (by omega) (by omega)]; exact q11)
        (by rw [sR _ (by omega) (by omega) (by omega)]; exact q12)
        (by rw [sR _ (by omega) (by omega) (by omega)]; exact q04) s17 s16
      refine ⟨d₂, s₁ + s₂ + 2, .ifLtN_false hnt (.seq f₁ f₂), ?_, ?_, ?_, fun x hx => ?_,
        by rw [vm, sm], by rw [vrr, srr], by rw [vrm, srm], by rw [vo, so]⟩
      · unfold wCost; rw [ppIteT hq]; omega
      · unfold wv; rw [ppIteT hq]; exact v17
      · rw [vR _ (by omega) (by omega) (by omega), sR _ (by omega) (by omega) (by omega), q14]
      · unfold wR at hx
        rw [vR _ (by omega) (by omega) (by omega), sR _ (by omega) (by omega) (by omega)]
    · have ht : c₁.nreg 8816 < c₁.nreg 8704 := by
        rw [a16, q04]; unfold fl; rw [ppIteF hq]; omega
      obtain ⟨d₁, s₁, f₁, hs₁, s17, sR, sm, srr, srm, so⟩ := wLp_exec (P := P) c₁ e₁.wb_right
      refine ⟨d₁, s₁ + 1, .ifLtN_true ht f₁, ?_, ?_, ?_, fun x hx => ?_, sm, srr, srm, so⟩
      · unfold wCost; omega
      · unfold wv; rw [ppIteF hq, s17, q14]
      · rw [sR _ (by omega), q14]
      · unfold wR at hx; exact sR _ (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, v14, vm, vR, vrr, vrm, vo⟩ := wWr_exec (P := P) (Tb := Tb) c₂ e₂.wb_right
    (by rw [bR _ (by unfold wR; omega)]; exact q13) b14
    (by rw [bR _ (by unfold wR; omega)]; exact q04) (by omega) (by omega)
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, v14, ?_, fun x hx => ?_,
    by rw [vrr, brr, arr], by rw [vrm, brm, arm], by rw [vo, bo, ao]⟩
  · rw [vm, bm, am, b17]
  · unfold wR at hx
    rw [vR _ (by omega) (by omega), bR _ (by unfold wR; omega), k1 _ (by unfold wR; omega)]

/-- **The walk loop over all darts.** -/
theorem wLoop_exec (hp : PermOn f n) {SGb NLb Tb : ℕ} (hW : SGb + n ≤ W) (hW' : NLb + n ≤ W)
    (hW'' : Tb + n + 1 ≤ W) (hd1 : SGb + n ≤ Tb ∨ Tb + n ≤ SGb)
    (hd2 : NLb + n ≤ Tb ∨ Tb + n ≤ NLb) (c : Config)
    (hc : WordsBounded W c) (hm : WMem f Q n SGb NLb c.nmem) (r11 : c.nreg 8811 = SGb)
    (r12 : c.nreg 8812 = NLb) (r13 : c.nreg 8813 = Tb) (r04 : c.nreg 8704 = 1)
    (r00 : c.nreg 8700 = n) (r14 : c.nreg 8814 = 0) :
    ∃ c' t, Exec P W (.whileLtN 8814 8700 wBody) c c' t ∧ t ≤ 24 * n + 2 ∧
      (∀ x < n, c'.nmem (Tb + x) = wv f Q x) ∧
      (∀ a, ¬ (Tb ≤ a ∧ a < Tb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ wR x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i d =>
    (∀ x < i, d.nmem (Tb + x) = wv f Q x) ∧
      (∀ a, ¬ (Tb ≤ a ∧ a < Tb + n) → d.nmem a = c.nmem a) ∧
      (∀ x, ¬ wR x → d.nreg x = c.nreg x) ∧
      d.rreg = c.rreg ∧ d.rmem = c.rmem ∧ d.output = c.output
  obtain ⟨c', k, e, hk, hw, h14, j1, j2, j3, j4, j5, j6⟩ := lnRangeV (P := P) (a := 8814)
    (b := 8700) (body := wBody) J (lo := 0) (hi := n) (wCost f Q) c hc r14 r00 (Nat.zero_le n)
    ⟨fun x hx => absurd hx (Nat.not_lt_zero _), fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩
    (fun i d _ hin hw hci hbn ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have hmd : WMem f Q n SGb NLb d.nmem :=
        ⟨fun x hx => by rw [j2 _ (by omega)]; exact hm.sg x hx,
          fun x hx => by rw [j2 _ (by omega)]; exact hm.nl x hx⟩
      obtain ⟨d', t, e, ht, v14, vm, vR, vrr, vrm, vo⟩ := wBody_exec (P := P) hp hin hW hW'
        hW'' d hw hmd (by rw [j3 _ (by unfold wR; omega)]; exact r11)
        (by rw [j3 _ (by unfold wR; omega)]; exact r12)
        (by rw [j3 _ (by unfold wR; omega)]; exact r13)
        (by rw [j3 _ (by unfold wR; omega)]; exact r04) hci
      refine ⟨d', t, e, ht, v14, by rw [vR _ (by unfold wR; omega)]; exact hbn,
        fun x hx => ?_, fun a ha => ?_, fun x hx => by rw [vR x hx, j3 x hx],
        by rw [vrr, j4], by rw [vrm, j5], by rw [vo, j6]⟩
      · rw [vm, upd_apply]
        by_cases hxi : x = i
        · subst hxi; simp
        · have : Tb + x ≠ Tb + i := by omega
          simp only [this, ↓reduceIte]; exact j1 x (by omega)
      · rw [vm, upd_apply]
        have : a ≠ Tb + i := by omega
        simp only [this, ↓reduceIte]; exact j2 a ha)
  refine ⟨c', k, e, ?_, j1, j2, j3, j4, j5, j6⟩
  have hs := sum_wlk_le (Q := Q) hp
  have e1 : ∑ i ∈ Ico 0 n, (wCost f Q i + 2) =
      6 * ∑ x ∈ range n, (if Q x then wlk f Q x - 1 else 0) + 18 * n := by
    rw [Nat.Ico_zero_eq_range]
    unfold wCost
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
    ring
  omega

end Loop

/-- **The walk program**: the bases `SGb = B + n`, `NLb = B + 10 n`, `Tb = B + 12 n`. -/
theorem pdW_exec {f : ℕ → ℕ} {Q : ℕ → Prop} [DecidablePred Q] {n B : ℕ} (hp : PermOn f n)
    (c : Config) (hc : WordsBounded W c) (r00 : c.nreg 8700 = n) (r04 : c.nreg 8704 = 1)
    (r30 : c.nreg 8730 = B) (hm : WMem f Q n (B + 1 * n) (B + 10 * n) c.nmem)
    (hW : B + 13 * n + 13 ≤ W) :
    ∃ c' t, Exec P W pdW c c' t ∧ t ≤ 24 * n + 20 ∧
      (∀ x < n, c'.nmem (B + 12 * n + x) = wv f Q x) ∧
      (∀ a, ¬ (B + 12 * n ≤ a ∧ a < B + 12 * n + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ wR x → x ≠ 8778 → x ≠ 8811 → x ≠ 8812 → x ≠ 8813 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, v1, f1, m1, rr1, rm1, o1⟩ := setB_exec (P := P) (r := 8811) (k := 1) (n := n) (B := B)
    c hc (by omega) r00 r30 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, v2, f2, m2, rr2, rm2, o2⟩ := setB_exec (P := P) (r := 8812) (k := 10) (n := n) (B := B)
    c₁ e₁.wb_right (by omega) (by rw [f1 _ (by omega) (by omega)]; exact r00)
    (by rw [f1 _ (by omega) (by omega)]; exact r30) (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, v3, f3, m3, rr3, rm3, o3⟩ := setB_exec (P := P) (r := 8813) (k := 12) (n := n) (B := B)
    c₂ e₂.wb_right (by omega)
    (by rw [f2 _ (by omega) (by omega), f1 _ (by omega) (by omega)]; exact r00)
    (by rw [f2 _ (by omega) (by omega), f1 _ (by omega) (by omega)]; exact r30) (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, v4, f4, m4, rr4, rm4, o4⟩ := cst_exec (P := P) (r := 8814) (v := 0)
    c₃ e₃.wb_right (Nat.zero_le _)
  have K : ∀ x, x ≠ 8811 → x ≠ 8812 → x ≠ 8813 → x ≠ 8814 → x ≠ 8778 → c₄.nreg x = c.nreg x :=
    fun x a b c' d e => by rw [f4 x d, f3 x c' e, f2 x b e, f1 x a e]
  obtain ⟨c₅, t₅, e₅, ht₅, j1, j2, j3, j4, j5, j6⟩ := wLoop_exec (P := P) (f := f) (Q := Q)
    (SGb := B + 1 * n) (NLb := B + 10 * n) (Tb := B + 12 * n) hp (by omega) (by omega)
    (by omega) (by omega) (by omega) c₄ e₄.wb_right (by rw [m4, m3, m2, m1]; exact hm)
    (by rw [f4 _ (by omega), f3 _ (by omega) (by omega), f2 _ (by omega) (by omega)]; exact v1)
    (by rw [f4 _ (by omega), f3 _ (by omega) (by omega)]; exact v2)
    (by rw [f4 _ (by omega)]; exact v3)
    (by rw [K _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r04)
    (by rw [K _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r00) v4
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
    by omega, j1, fun a ha => by rw [j2 a ha, m4, m3, m2, m1], fun x hx a b c' d => ?_,
    by rw [j4, rr4, rr3, rr2, rr1], by rw [j5, rm4, rm3, rm2, rm1],
    by rw [j6, o4, o3, o2, o1]⟩
  rw [j3 x hx, K x b c' d (by unfold wR at hx; omega) a]

end Pp

end BKMNW

end PlanarFlow
