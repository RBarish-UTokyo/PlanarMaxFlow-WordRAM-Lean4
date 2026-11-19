module

public import PlanarFlow.BKMNW.PpSoM

/-!
# The sort of the slots on the machine

`so`: zero the counts (`B + 84 n`, `KM + 1` words), one stable counting-sort pass `csPass` of the
items `IT` (`B + 21 n`) into `SO` (`B + 28 n`), `SRT[i] = SO[i] mod 7 n` (`B + 35 n`), and the
inverse `POS[SRT[i]] = i` (`B + 42 n`) by a scatter. **`so_exec`**: `SRT = srtF`, `POS ∘ SRT = id`.
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

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv Feas
  PlanarSeparator.Piece

variable {P : Input} {W : ℕ}

/-- The counts zero. -/
def soA : Stmt := .seq (block [.addN 8741 8709 8704]) (stageM 84 vbZero)

/-- The registers of the counting sort pass. -/
def csSet : Stmt := block [.copyN 1260 8741, .copyN 1261 8703, .constN 8778 21,
  .mulN 8778 8700 8778, .addN 1262 8778 8730, .constN 8778 28, .mulN 8778 8700 8778,
  .addN 1263 8778 8730, .constN 8778 84, .mulN 8778 8700 8778, .addN 1264 8778 8730,
  .copyN 1272 8703, .constN 1001 1, .constN 0 0]

/-- `SRT[i] := SO[i] mod 7 n`. -/
def soB : Stmt := .seq (block [.copyN 8741 8703, .constN 8778 28, .mulN 8778 8700 8778,
  .addN 8728 8778 8730]) (stageM 35 vbMod)

/-- `POS[SRT[i]] := i`. -/
def soC : Stmt := .seq (block [.constN 8778 35, .mulN 8778 8700 8778, .addN 8748 8778 8730,
  .constN 8778 42, .mulN 8778 8700 8778, .addN 8742 8778 8730]) scatL

/-- **The sort of the slots.** -/
def so : Stmt := .seq soA (.seq csSet (.seq csPass (.seq soB soC)))

/-- The registers `so` may write. -/
def wso (x : ℕ) : Prop :=
  wscr x ∨ x = 8741 ∨ x = 8728 ∨ x = 8748 ∨ x = 0 ∨ x = 1001 ∨ (1260 ≤ x ∧ x ≤ 1272)

lemma getD_Lit {G KM : ℕ} {kap : ℕ → ℕ} {i : ℕ} (hi : i < G) :
    (Lit G kap).getD i 0 = itF G kap i := by
  unfold Lit; rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

set_option maxHeartbeats 1000000 in
theorem so_exec (c : Config) (hc : WordsBounded W c) {n B KM : ℕ} {kap : ℕ → ℕ}
    (hn : 0 < n) (hk : ∀ s < 7 * n, kap s ≤ KM)
    (r00 : c.nreg 8700 = n) (r03 : c.nreg 8703 = 7 * n) (r04 : c.nreg 8704 = 1)
    (r09 : c.nreg 8709 = KM) (r30 : c.nreg 8730 = B)
    (hit : ∀ s < 7 * n, c.nmem (B + 21 * n + s) = itF (7 * n) kap s)
    (hW : B + 100 * n + KM + (KM + 1) * (7 * n) + 100 ≤ W) :
    ∃ c' t, Exec P W so c c' t ∧ t ≤ 300 * n + 20 * KM + 100 ∧
      (∀ i < 7 * n, c'.nmem (B + 35 * n + i) = srtF (7 * n) KM kap i) ∧
      (∀ i < 7 * n, c'.nmem (B + 42 * n + srtF (7 * n) KM kap i) = i) ∧
      (∀ a, ¬ (B + 28 * n ≤ a ∧ a < B + 49 * n) → ¬ (B + 84 * n ≤ a ∧ a < B + 84 * n + KM + 1) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ wso x → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hG : 0 < 7 * n := by omega
  have h7 : 7 * n ≤ (KM + 1) * (7 * n) := Nat.le_mul_of_pos_left _ (by omega)
  -- β
  obtain ⟨c₁, t₁, e₁, ht₁, v1, f1, m1, rr1, rm1, o1⟩ : ∃ c₁ t₁,
      Exec P W (block [.addN 8741 8709 8704]) c c₁ t₁ ∧ t₁ = 1 ∧ c₁.nreg 8741 = KM + 1 ∧
      (∀ x, x ≠ 8741 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧
      c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    · config_simp; rw [r09, r04]; omega
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [r09, r04]
    · config_simp; simp (disch := omega) only [upd_other]
  -- the counts
  obtain ⟨c₂, t₂, e₂, ht₂, a2, m2, f2, rr2, rm2, o2⟩ := stageM_exec (P := P) c₁ e₁.wb_right
    (n := n) (k := 84) (m := KM + 1) (B := B) (B' := 1) (vb := vbZero) (fun _ => 0)
    (by rw [f1 _ (by omega)]; exact r00) (by rw [f1 _ (by omega)]; exact r30) v1
    (by rw [f1 _ (by omega)]; exact r04) (by omega) (by omega)
    (fun i hi c' hw _ _ _ => vbZero_exec c' hw)
  have g2 : ∀ x, x ≠ 8741 → ¬ wscr x → c₂.nreg x = c.nreg x := fun x h1 h2 => by
    rw [f2 x h2, f1 x h1]
  -- the registers of the pass
  obtain ⟨c₃, t₃, e₃, ht₃, s60, s61, s62, s63, s64, s72, s1001, s0, f3, m3, rr3, rm3, o3⟩ :
      ∃ c₃ t₃, Exec P W csSet c₂ c₃ t₃ ∧ t₃ = 14 ∧ c₃.nreg 1260 = KM + 1 ∧
        c₃.nreg 1261 = 7 * n ∧ c₃.nreg 1262 = B + 21 * n ∧ c₃.nreg 1263 = B + 28 * n ∧
        c₃.nreg 1264 = B + 84 * n ∧ c₃.nreg 1272 = 7 * n ∧ c₃.nreg 1001 = 1 ∧ c₃.nreg 0 = 0 ∧
        (∀ x, ¬ wso x → x ≠ 8778 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
        c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have q41 : c₂.nreg 8741 = KM + 1 := by rw [f2 _ (by unfold wscr pscr; omega)]; exact v1
    have q03 : c₂.nreg 8703 = 7 * n := by rw [g2 _ (by omega) (by unfold wscr pscr; omega)]; exact r03
    have q00 : c₂.nreg 8700 = n := by rw [g2 _ (by omega) (by unfold wscr pscr; omega)]; exact r00
    have q30 : c₂.nreg 8730 = B := by rw [g2 _ (by omega) (by unfold wscr pscr; omega)]; exact r30
    have hw₂ := e₂.wb_right
    unfold csSet
    exec_block
    all_goals try omega
    all_goals try (config_simp; rw [q00]; omega)
    all_goals try (config_simp; rw [q00, q30]; omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx h78 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; rw [q41])
    all_goals try (config_simp; rw [q03])
    all_goals try (config_simp; rw [q00, q30]; ring)
    all_goals try config_simp
    unfold wso at hx; simp (disch := omega) only [upd_other]
  -- the pass
  have hLW : ∀ x ∈ Lit (7 * n) kap, x ≤ W := fun x hx => by
    obtain ⟨s, hs, rfl⟩ := (mem_Lit hG).1 hx
    have : kap s * (7 * n) ≤ KM * (7 * n) := Nat.mul_le_mul_right _ (hk s hs)
    unfold itF; nlinarith
  have hCs : CsL (KM + 1) (7 * n) (B + 21 * n) (B + 28 * n) (B + 84 * n) (7 * n)
      (Lit (7 * n) kap) W c₃ :=
    { one := s1001, r0 := s0, rb := s60, rk := s61, rIn := s62, rOut := s63, rCnt := s64,
      rq := s72, len := by simp [Lit],
      inp := fun i hi => by
        rw [m3, m2 _ (by omega), m1, hit i hi, getD_Lit (KM := KM) hi]
      hβ := by omega, nd := Lit_nodup hG, hLW := hLW,
      d1 := Or.inl (by omega), d2 := Or.inl (by omega), d3 := Or.inl (by omega),
      wIn := by omega, wOut := by omega, wCnt := by omega }
  obtain ⟨c₄, t₄, e₄, hw₄, so4, m4, f4, o4, rr4, rm4, ht₄⟩ := csPass_exec (P := P) e₃.wb_right hCs
    (fun t ht => by rw [m3, a2 t ht])
  have hso : ∀ p < 7 * n, c₄.nmem (B + 28 * n + p) = (soF (7 * n) KM kap).getD p 0 := so4
  have g4 : ∀ x, ¬ wso x → x ≠ 8778 → c₄.nreg x = c.nreg x := fun x h1 h2 => by
    rw [f4 x (by unfold csW; unfold wso at h1; omega), f3 x h1 h2,
      g2 x (by unfold wso at h1; omega) (fun h => h1 (Or.inl h))]
  have q00 : c₄.nreg 8700 = n := by rw [g4 _ (by unfold wso wscr pscr; omega) (by omega)]; exact r00
  have q03 : c₄.nreg 8703 = 7 * n := by
    rw [g4 _ (by unfold wso wscr pscr; omega) (by omega)]; exact r03
  have q04 : c₄.nreg 8704 = 1 := by rw [g4 _ (by unfold wso wscr pscr; omega) (by omega)]; exact r04
  have q30 : c₄.nreg 8730 = B := by rw [g4 _ (by unfold wso wscr pscr; omega) (by omega)]; exact r30
  -- SRT
  obtain ⟨c₅, t₅, e₅, ht₅, v41, v28, f5, m5, rr5, rm5, o5⟩ : ∃ c₅ t₅,
      Exec P W (block [.copyN 8741 8703, .constN 8778 28, .mulN 8778 8700 8778,
        .addN 8728 8778 8730]) c₄ c₅ t₅ ∧ t₅ = 4 ∧ c₅.nreg 8741 = 7 * n ∧
      c₅.nreg 8728 = B + 28 * n ∧ (∀ x, x ≠ 8741 → x ≠ 8778 → x ≠ 8728 → c₅.nreg x = c₄.nreg x) ∧
      c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    exec_block
    all_goals try omega
    all_goals try (config_simp; rw [q00]; omega)
    all_goals try (config_simp; rw [q00, q30]; omega)
    refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [q03]
    · config_simp; rw [q00, q30]; ring
    · config_simp; simp (disch := omega) only [upd_other]
  obtain ⟨c₆, t₆, e₆, ht₆, a6, m6, f6, rr6, rm6, o6⟩ := stageM_exec (P := P) c₅ e₅.wb_right
    (n := n) (k := 35) (m := 7 * n) (B := B) (B' := 3) (vb := vbMod) (srtF (7 * n) KM kap)
    (by rw [f5 _ (by omega) (by omega) (by omega)]; exact q00)
    (by rw [f5 _ (by omega) (by omega) (by omega)]; exact q30) v41
    (by rw [f5 _ (by omega) (by omega) (by omega)]; exact q04) (by omega) (by omega)
    (fun i hi c' hw h40 hfr hm => by
      obtain ⟨c'', t, e, post⟩ := vbMod_exec (P := P) (Ab := B + 28 * n) (G := 7 * n) c' hw h40
        (by rw [hfr _ (by unfold wscr pscr; omega)]; exact v28)
        (by rw [hfr _ (by unfold wscr pscr; omega), f5 _ (by omega) (by omega) (by omega)]
            exact q03) (by omega)
      rw [hm _ (by omega), m5, hso i hi] at post
      exact ⟨c'', t, e, post⟩)
  -- POS
  have q41₆ : c₆.nreg 8741 = 7 * n := by rw [f6 _ (by unfold wscr pscr; omega)]; exact v41
  have g6 : ∀ x, x ≠ 8741 → x ≠ 8778 → x ≠ 8728 → ¬ wscr x → c₆.nreg x = c₄.nreg x :=
    fun x h1 h2 h3 h4 => by rw [f6 x h4, f5 x h1 h2 h3]
  obtain ⟨c₇, t₇, e₇, ht₇, v48, v42, f7, m7, rr7, rm7, o7⟩ : ∃ c₇ t₇,
      Exec P W (block [.constN 8778 35, .mulN 8778 8700 8778, .addN 8748 8778 8730,
        .constN 8778 42, .mulN 8778 8700 8778, .addN 8742 8778 8730]) c₆ c₇ t₇ ∧ t₇ = 6 ∧
      c₇.nreg 8748 = B + 35 * n ∧ c₇.nreg 8742 = B + 42 * n ∧
      (∀ x, x ≠ 8748 → x ≠ 8778 → x ≠ 8742 → c₇.nreg x = c₆.nreg x) ∧
      c₇.nmem = c₆.nmem ∧ c₇.rreg = c₆.rreg ∧ c₇.rmem = c₆.rmem ∧ c₇.output = c₆.output := by
    have p00 : c₆.nreg 8700 = n := by
      rw [g6 _ (by omega) (by omega) (by omega) (by unfold wscr pscr; omega)]; exact q00
    have p30 : c₆.nreg 8730 = B := by
      rw [g6 _ (by omega) (by omega) (by omega) (by unfold wscr pscr; omega)]; exact q30
    have hw₆ := e₆.wb_right
    exec_block
    all_goals try omega
    all_goals try (config_simp; rw [p00]; omega)
    all_goals try (config_simp; rw [p00, p30]; omega)
    refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [p00, p30]; ring
    · config_simp; rw [p00, p30]; ring
    · config_simp; simp (disch := omega) only [upd_other]
  obtain ⟨c₈, t₈, e₈, ht₈, a8, m8, f8, rr8, rm8, o8⟩ := scatL_exec (P := P) c₇ e₇.wb_right
    (m := 7 * n) (Ab := B + 35 * n) (Ob := B + 42 * n) (srtF (7 * n) KM kap)
    (by rw [f7 _ (by omega) (by omega) (by omega)]; exact q41₆)
    (by rw [f7 _ (by omega) (by omega) (by omega),
      g6 _ (by omega) (by omega) (by omega) (by unfold wscr pscr; omega)]; exact q04) v42 v48
    (fun i hi => by rw [m7]; exact a6 i hi) (fun i _ => srtF_lt hG hk i)
    (fun i hi j hj e => srtF_inj hG hk hi hj e) (by omega) (by omega) (by omega)
  have ex : Exec P W so c c₈ ((t₁ + t₂) + (t₃ + (t₄ + ((t₅ + t₆) + (t₇ + t₈))))) := by
    unfold so soA soB soC
    exact .seq (.seq e₁ e₂) (.seq e₃ (.seq e₄ (.seq (.seq e₅ e₆) (.seq e₇ e₈))))
  refine ⟨c₈, _, ex, ?_,
    fun i hi => ?_, a8, fun a h1 h2 => ?_, fun x hx => ?_,
    by rw [rr8, rr7, rr6, rr5, rr4, rr3, rr2, rr1],
    by rw [rm8, rm7, rm6, rm5, rm4, rm3, rm2, rm1],
    by rw [o8, o7, o6, o5, o4, o3, o2, o1]⟩
  · have : (KM + 1) * (7 * n) + 0 ≥ 0 := Nat.zero_le _
    omega
  · rw [m8 _ (by omega), m7, a6 i hi]
  · rw [m8 _ (by omega), m7, m6 _ (by omega), m5, m4 _ (by omega), m3, m2 _ (by omega), m1]
  · unfold wso wscr pscr at hx
    rw [f8 x (by omega) (by omega) (by omega), f7 x (by omega) (by omega) (by omega),
      g6 x (by omega) (by omega) (by omega) (by unfold wscr pscr; omega),
      g4 x (by unfold wso wscr pscr; omega) (by omega)]

end Pp

end BKMNW

end PlanarFlow
