module

public import PlanarFlow.Klein.ProgPivot
public import PlanarFlow.Klein.CmpRun
public import PlanarFlow.Klein.PivotBnd

/-!
# One pivot on the machine, with bounded comparisons

The proofs of `PlanarFlow/Klein/ProgPivot.lean` replayed as runs whose real comparisons are
bounded (`DynTree.ORunC`): `sel_orunC`, `val_orunC`, `z_orunC` (the forest unchanged, its values
at most `V`, `2 V ≤ H`), `pivCore_orunC`, `piv_orunC` (from a forest with values at most `U`, the
four new values of the two edges changing trees at most `Tb`, and `2 (5 U + 2 |c| + 4 Tb) ≤ H`:
every forest along the sixteen operations is bounded by `5 U + 2 |c| + 4 Tb`,
`Klein.pivot_allV`), which also give **the bound `max (U + |c|) Tb` of the values after the
pivot** (`Klein.pivot_vbnd`).
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {S : Finset D} {ℓ : D → ℤ} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ}
  {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

section
variable {P : Input} {W B H : ℕ}

theorem sel_orunC (hW : B + 16 * (n + 1) ≤ W) (hWa : 8 * nD + n ≤ W)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {c : Config} (hc : WordsBounded W c) {Fo : Forest}
    {G : List VT} (hS : LCTE B n Fo G c) {V : ℝ} (hV : VBnd V n Fo) (hH : 2 * V ≤ H) {b : D}
    (h196 : c.nreg 196 = ιe b)
    (hpar : Fo.par (ιe b) = ιf (M.face b)) (hfb : M.face b ≠ M.face (M.rev b)) :
    ∃ c' G', ORunC P W H B n (selS B nD) c Fo G c' [] G' 1 21 ∧ c'.nreg 114 = σ b ∧
      c'.rreg 110 = c.rreg 195 ∧ LoFr c c' ∧ MemFrame B n (mem c) (mem c') := by
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hen := hL.dual.e_lt b
  -- the node and a dart of its edge
  obtain ⟨c₁, k₁, e₁, hk₁, h110, h111, r110, hg₁⟩ : ∃ c' k, Exec P W (block [.copyN 110 196,
      .copyR 110 195, .constN 111 (iED nD), .addN 111 111 110, .readIn 111 111]) c c' k ∧
      k = 5 ∧ c'.nreg 110 = ιe b ∧ c'.nreg 111 = P.data.getD (iED nD + ιe b) 0 ∧
      c'.rreg 110 = c.rreg 195 ∧ GFr 110 112 c c' := by
    exec_block
    · unfold iED; omega
    · config_simp; rw [h196]; unfold iED; omega
    · exact hP _
    · refine ⟨rfl, by config_simp; exact h196, by config_simp; rw [h196], by config_simp, ?_⟩
      gfr_tac
  have o₁ := ORunC.ofGFr (H := H) e₁ hS hg₁ (by omega) (by rfl)
  -- the parent of the node
  obtain ⟨c₂, G₂, o₂, p₂, -, hm₂, hf₂⟩ := regParent_orunC (P := P) hW e₁.wb_right
    (hS.congr (fun a _ _ => by rw [hg₁.2.1, hg₁.2.2.1]; exact ⟨rfl, rfl⟩) (hg₁.1 151
      (by omega)).1) hV hH h110 hen
  rw [hpar] at p₂
  -- the face of that dart and its reverse
  obtain ⟨c₃, k₃, e₃, hk₃, h112, h113, h114, hg₃⟩ : ∃ c' k, Exec P W (block [.constN 112 (iNF nD),
      .addN 112 112 111, .readIn 112 112, .constN 113 (iRV nD), .addN 113 113 111,
      .readIn 113 113, .copyN 114 111]) c₂ c' k ∧ k = 7 ∧
      c'.nreg 112 = P.data.getD (iNF nD + c₂.nreg 111) 0 ∧
      c'.nreg 113 = P.data.getD (iRV nD + c₂.nreg 111) 0 ∧ c'.nreg 114 = c₂.nreg 111 ∧
      GFr 112 115 c₂ c' := by
    have h111' : c₂.nreg 111 = P.data.getD (iED nD + ιe b) 0 := by
      rw [(hf₂.1 111 (by omega))]; exact h111
    have hlt : c₂.nreg 111 < nD := by
      rw [h111']; rcases hK.ed b with h | h <;> rw [h] <;> exact hσ _
    have hc₂ : WordsBounded W c₂ := o₂.1.2.wb
    exec_block
    · unfold iNF; omega
    · config_simp; unfold iNF; omega
    · exact hP _
    · unfold iRV; omega
    · config_simp; unfold iRV; omega
    · exact hP _
    · refine ⟨rfl, by config_simp, by config_simp, by config_simp, ?_⟩
      gfr_tac
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte hg₃ (by omega) (by rfl)
  -- the orientation
  have h111₂ : c₂.nreg 111 = P.data.getD (iED nD + ιe b) 0 := by
    rw [(hf₂.1 111 (by omega))]; exact h111
  have h195₃ : c₃.nreg 195 = ιf (M.face b) := by rw [(hg₃.1 195 (by omega)).1]; exact p₂
  have hfb' : ιf (M.face b) ≠ ιf (M.face (M.rev b)) := fun h => hfb (hL.dual.f_inj h)
  have hbr : ∃ c₄ k₄, Exec P W (.ifLtN 195 112 (.instr (.copyN 114 113))
      (.ifLtN 112 195 (.instr (.copyN 114 113)) .skip)) c₃ c₄ k₄ ∧ k₄ ≤ 4 ∧
      c₄.nreg 114 = σ b ∧ GFr 114 115 c₃ c₄ := by
    rcases hK.ed b with h | h
    · -- the dart itself: its face is the parent
      have e112 : c₃.nreg 112 = ιf (M.face b) := by rw [h112, h111₂, h, hK.nf]
      refine ⟨c₃, 2 + 2, .ifLtN_false (by omega) (.ifLtN_false (by omega) (.skip e₃.wb_right)),
        by omega, by rw [h114, h111₂, h], ⟨fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl⟩⟩
    · -- the reverse: its face is not the parent
      have e112 : c₃.nreg 112 = ιf (M.face (M.rev b)) := by rw [h112, h111₂, h, hK.nf]
      have e113 : c₃.nreg 113 = σ b := by rw [h113, h111₂, h, hK.rv, M.rev_rev]
      rcases Nat.lt_or_gt_of_ne (show c₃.nreg 195 ≠ c₃.nreg 112 by rw [h195₃, e112]; exact hfb')
        with hl | hl
      · refine ⟨{ c₃ with nreg := upd c₃.nreg 114 (c₃.nreg 113) }, _,
          .ifLtN_true hl (Exec.copyN e₃.wb_right 114 113), by omega,
          by config_simp; exact e113, ?_⟩
        gfr_tac
      · refine ⟨{ c₃ with nreg := upd c₃.nreg 114 (c₃.nreg 113) }, _,
          .ifLtN_false (by omega) (.ifLtN_true hl (Exec.copyN e₃.wb_right 114 113)),
          by omega, by config_simp; exact e113, ?_⟩
        gfr_tac
  obtain ⟨c₄, k₄, e₄, hk₄, h114₄, hg₄⟩ := hbr
  have o₄ := ORunC.ofGFr (H := H) e₄ o₃.1.2.lcte hg₄ (by omega) (by rfl)
  refine ⟨c₄, G₂, (o₁.seq (o₂.seq (o₃.seq o₄))).mono (by omega) (by omega), h114₄, ?_, ?_, ?_⟩
  · rw [(hg₄.1 110 (by omega)).2, (hg₃.1 110 (by omega)).2, (hf₂.2.1 110 (by omega)), r110]
  · exact ((hg₁.loFr le_rfl).trans (RegFr.loFr hf₂)).trans ((hg₃.loFr (by omega)).trans
      (hg₄.loFr (by omega)))
  · exact (hg₁.memFrame.trans B n hm₂).trans B n (hg₃.memFrame.trans B n hg₄.memFrame)

theorem val_orunC (hW : B + 16 * (n + 1) ≤ W) {c : Config} (hc : WordsBounded W c) {Fo : Forest}
    {G : List VT} (hS : LCTE B n Fo G c) {V : ℝ} (hV : VBnd V n Fo) (hH : 2 * V ≤ H) {u w : ℕ}
    (h126 : c.nreg 126 = u)
    (h119 : c.nreg 119 = w) (hu : u < n) (hw : w < n) :
    ∃ c' G', ORunC P W H B n (valS B) c Fo G c' [] G' 8 4 ∧
      c'.rreg 116 = Fo.val u ∧ c'.rreg 117 = Fo.val2 u ∧ c'.rreg 118 = Fo.val w ∧
      c'.rreg 119 = Fo.val2 w ∧ (∀ r, r < 160 → c'.nreg r = c.nreg r) ∧
      (∀ r, (r < 116 ∨ 119 < r) → r < 160 → c'.rreg r = c.rreg r) ∧ c'.output = c.output ∧
      MemFrame B n (mem c) (mem c') := by
  obtain ⟨c₁, G₁, o₁, v₁, m₁, f₁⟩ := regVal_orunC (P := P) hW hc hS hV hH false h126 hu
  have e₂ := Exec.copyR (P := P) o₁.1.2.wb 116 195
  have o₂ := ORunC.ofGFr (H := H) e₂ o₁.1.2.lcte (lo := 116) (hi := 117) (by gfr_tac) (by omega) (by rfl)
  obtain ⟨c₃, G₃, o₃, v₃, m₃, f₃⟩ := regVal_orunC (P := P) hW e₂.wb_right o₂.1.2.lcte hV hH true
    (by config_simp; rw [f₁.1 126 (by omega)]; exact h126) hu
  have e₄ := Exec.copyR (P := P) o₃.1.2.wb 117 195
  have o₄ := ORunC.ofGFr (H := H) e₄ o₃.1.2.lcte (lo := 117) (hi := 118) (by gfr_tac) (by omega) (by rfl)
  obtain ⟨c₅, G₅, o₅, v₅, m₅, f₅⟩ := regVal_orunC (P := P) hW e₄.wb_right o₄.1.2.lcte hV hH false
    (by config_simp; rw [f₃.1 119 (by omega)]; config_simp; rw [f₁.1 119 (by omega)]; exact h119)
    hw
  have e₆ := Exec.copyR (P := P) o₅.1.2.wb 118 195
  have o₆ := ORunC.ofGFr (H := H) e₆ o₅.1.2.lcte (lo := 118) (hi := 119) (by gfr_tac) (by omega) (by rfl)
  obtain ⟨c₇, G₇, o₇, v₇, m₇, f₇⟩ := regVal_orunC (P := P) hW e₆.wb_right o₆.1.2.lcte hV hH true
    (by config_simp; rw [f₅.1 119 (by omega)]; config_simp; rw [f₃.1 119 (by omega)];
        config_simp; rw [f₁.1 119 (by omega)]; exact h119) hw
  have e₈ := Exec.copyR (P := P) o₇.1.2.wb 119 195
  have o₈ := ORunC.ofGFr (H := H) e₈ o₇.1.2.lcte (lo := 119) (hi := 120) (by gfr_tac) (by omega) (by rfl)
  refine ⟨_, G₇, (o₁.seq (o₂.seq (o₃.seq (o₄.seq (o₅.seq (o₆.seq (o₇.seq o₈))))))).mono
    (by omega) (by omega), ?_, ?_, ?_, ?_, fun r hr => ?_, fun r hr hr' => ?_, ?_, ?_⟩
  · config_simp
    rw [f₇.2.1 116 (by omega)]; config_simp
    rw [f₅.2.1 116 (by omega)]; config_simp
    rw [f₃.2.1 116 (by omega)]; config_simp
    exact v₁
  · config_simp
    rw [f₇.2.1 117 (by omega)]; config_simp
    rw [f₅.2.1 117 (by omega)]; config_simp
    exact v₃
  · config_simp
    rw [f₇.2.1 118 (by omega)]; config_simp
    exact v₅
  · config_simp; exact v₇
  · config_simp
    rw [f₇.1 r (by omega)]; config_simp
    rw [f₅.1 r (by omega)]; config_simp
    rw [f₃.1 r (by omega)]; config_simp
    exact f₁.1 r (by omega)
  · have h1 : r ≠ 116 := by omega
    have h2 : r ≠ 117 := by omega
    have h3 : r ≠ 118 := by omega
    have h4 : r ≠ 119 := by omega
    simp only [upd_other _ _ _ h4]
    rw [f₇.2.1 r (by omega)]; simp only [upd_other _ _ _ h3]
    rw [f₅.2.1 r (by omega)]; simp only [upd_other _ _ _ h2]
    rw [f₃.2.1 r (by omega)]; simp only [upd_other _ _ _ h1]
    rw [f₁.2.1 r (by omega)]
  · rw [f₇.2.2, f₅.2.2, f₃.2.2, f₁.2.2]
  · have g₂ : MemFrame B n (mem c₁) (mem _) := (show GFr 116 117 c₁ _ by gfr_tac).memFrame
    have g₄ : MemFrame B n (mem c₃) (mem _) := (show GFr 117 118 c₃ _ by gfr_tac).memFrame
    have g₆ : MemFrame B n (mem c₅) (mem _) := (show GFr 118 119 c₅ _ by gfr_tac).memFrame
    have g₈ : MemFrame B n (mem c₇) (mem _) := (show GFr 119 120 c₇ _ by gfr_tac).memFrame
    exact ((((((m₁.trans B n g₂).trans B n m₃).trans B n g₄).trans B n m₅).trans B n g₆).trans
      B n m₇).trans B n g₈

theorem z_orunC (hW : B + 16 * (n + 1) ≤ W) (hL : Layout M n ιv ιg ιf ιe) {c : Config}
    (hc : WordsBounded W c) {Fo : Forest} {G : List VT} (hS : LCTE B n Fo G c) {V : ℝ}
    (hV : VBnd V n Fo) (hH : 2 * V ≤ H) {b : D}
    (h118 : c.nreg 118 = ιe b) (h116 : c.nreg 116 = ιf (M.face b))
    (h117 : c.nreg 117 = ιf (M.face (M.rev b))) :
    ∃ c' G', ORunC P W H B n (zS B) c Fo G c' [] G' 1 5 ∧ c'.nreg 128 = cutNode Fo ιf ιe M b ∧
      (∀ r, r < 128 → c'.nreg r = c.nreg r) ∧ (∀ r, r < 128 → c'.rreg r = c.rreg r) ∧
      c'.output = c.output ∧ MemFrame B n (mem c) (mem c') := by
  obtain ⟨c₁, G₁, o₁, p₁, -, m₁, f₁⟩ := regParent_orunC (P := P) hW hc hS hV hH h118 (hL.dual.e_lt b)
  have e₂ := Exec.copyN (P := P) o₁.1.2.wb 128 117
  set c₂ := { c₁ with nreg := upd c₁.nreg 128 (c₁.nreg 117) } with hc₂
  have g₂ : GFr 128 129 c₁ c₂ := by rw [hc₂]; gfr_tac
  have o₂ := ORunC.ofGFr (H := H) e₂ o₁.1.2.lcte g₂ (by omega) (by rfl)
  have q195 : c₂.nreg 195 = Fo.par (ιe b) := by rw [hc₂]; config_simp; exact p₁
  have q116 : c₂.nreg 116 = ιf (M.face b) := by
    rw [hc₂]; config_simp; rw [f₁.1 116 (by omega)]; exact h116
  have q128 : c₂.nreg 128 = ιf (M.face (M.rev b)) := by
    rw [hc₂]; config_simp; rw [f₁.1 117 (by omega)]; exact h117
  have hbr : ∃ c₃ k₃, Exec P W (.ifLtN 195 116 (.instr (.copyN 128 116))
      (.ifLtN 116 195 (.instr (.copyN 128 116)) .skip)) c₂ c₃ k₃ ∧ k₃ ≤ 4 ∧
      c₃.nreg 128 = cutNode Fo ιf ιe M b ∧ GFr 128 129 c₂ c₃ := by
    by_cases hp : Fo.par (ιe b) = ιf (M.face b)
    · refine ⟨c₂, 2 + 2, .ifLtN_false (by omega) (.ifLtN_false (by omega)
        (.skip e₂.wb_right)), by omega, ?_, ⟨fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl⟩⟩
      rw [q128]; unfold cutNode; rw [ite_eq_left hp]
    · have hne : c₂.nreg 195 ≠ c₂.nreg 116 := by rw [q195, q116]; exact hp
      have hval : cutNode Fo ιf ιe M b = ιf (M.face b) := by unfold cutNode; rw [ite_eq_right hp]
      rcases Nat.lt_or_gt_of_ne hne with hl | hl
      · refine ⟨{ c₂ with nreg := upd c₂.nreg 128 (c₂.nreg 116) }, _,
          .ifLtN_true hl (Exec.copyN e₂.wb_right 128 116), by omega, ?_, by gfr_tac⟩
        config_simp; rw [q116, hval]
      · refine ⟨{ c₂ with nreg := upd c₂.nreg 128 (c₂.nreg 116) }, _,
          .ifLtN_false (by omega) (.ifLtN_true hl (Exec.copyN e₂.wb_right 128 116)), by omega,
          ?_, by gfr_tac⟩
        config_simp; rw [q116, hval]
  obtain ⟨c₃, k₃, e₃, hk₃, h128, g₃⟩ := hbr
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) (by rfl)
  refine ⟨c₃, G₁, (o₁.seq (o₂.seq o₃)).mono ?_ ?_, h128, fun r hr => ?_,
    fun r hr => ?_, ?_, (m₁.trans B n g₂.memFrame).trans B n g₃.memFrame⟩
  · omega
  · omega
  · rw [(g₃.1 r (by omega)).1, (g₂.1 r (by omega)).1, f₁.1 r (by omega)]
  · rw [(g₃.1 r (by omega)).2, (g₂.1 r (by omega)).2, f₁.2.1 r (by omega)]
  · rw [g₃.2.2.2, g₂.2.2.2, f₁.2.2]

theorem pivCore_orunC (hW : B + 16 * (n + 1) ≤ W) (hWa : 8 * nD + n ≤ W) (hB : n + 2 * nD ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hM : M.IsPlane) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {c : Config} (hc : WordsBounded W c) {Fo : Forest}
    {G : List VT} (hS : LCTE B n Fo G c) {φ wt : D → ℤ} {fe : F} {Lo : ℝ} {T : DTree M.dual}
    {val : D → ℤ} (hSt : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val)
    (hKM : KMem M σ ιv T wt φ c) (h101 : c.nreg 101 = ιf fe) {b : D} {cv : ℤ}
    (h114 : c.nreg 114 = σ b) (h110 : c.rreg 110 = cv)
    (hy : M.head b ≠ T.root) (hna : ¬ T.Anc (M.head b) (M.dual.face b)) (hbT : ¬ T.InT b)
    {U Tb : ℝ} (hU : VBnd U n Fo)
    (ht₁ : |((wt (T.par (M.head b)) - φ (T.par (M.head b)) - cv : ℤ) : ℝ)| ≤ Tb)
    (ht₂ : |((wt (M.rev (T.par (M.head b))) + φ (T.par (M.head b)) + cv : ℤ) : ℝ)| ≤ Tb)
    (ht₃ : |(φ b : ℝ)| ≤ Tb) (ht₄ : |(φ (M.rev b) : ℝ)| ≤ Tb)
    (hH : 2 * (5 * U + 2 * |(cv : ℝ)| + 4 * Tb) ≤ H) :
    ∃ c' G' os, ORunC P W H B n (pivCoreS B nD) c Fo G c' os G' 25 76 ∧
      (∃ v₁ v₂ w₁ w₂ : ℤ, Fo.val (ιe (T.par (M.head b))) = v₁ ∧
        Fo.val2 (ιe (T.par (M.head b))) = v₂ ∧ Fo.val (ιg b) = w₁ ∧ Fo.val2 (ιg b) = w₂ ∧
        os = pivotOps (ιf (M.face (T.par (M.head b)))) (ιf (M.face (M.rev (T.par (M.head b)))))
          (ιe (T.par (M.head b))) (ιe b)
          (cutNode (runOpsE n Fo (pivotPre (ιf (M.face (T.par (M.head b))))
            (ιf (M.face (M.rev (T.par (M.head b))))) (cv))).1 ιf ιe M b)
          (ιf fe) (ιv (M.head b)) (ιg (T.par (M.head b))) (ιg b) (ιv (M.tail b)) (cv)
          (wt (T.par (M.head b)) - φ (T.par (M.head b)) - cv - v₁)
          (wt (M.rev (T.par (M.head b))) + φ (T.par (M.head b)) + cv - v₂)
          (φ b - w₁) (φ (M.rev b) - w₂)) ∧
      os.length = 16 ∧ (runOpsE n Fo os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ fe (Lo - |(cv : ℝ)|) (runOpsE n Fo os).1
        (T.reparent (M.head b) b hy (dual_face_rev b) hna)
        (pivotVal T φ wt val (M.head b) (cv)) ∧
      VBnd (max (U + |(cv : ℝ)|) Tb) n (runOpsE n Fo os).1 ∧
      KMem M σ ιv (T.reparent (M.head b) b hy (dual_face_rev b) hna) wt φ c' ∧ LoFr c c' ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → a ≠ aTP + ιv (M.head b) →
        c'.nmem a = c.nmem a) := by
  classical
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  set y := M.head b with hydef
  set a := T.par y with hadef
  obtain ⟨⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩ := hSt.int (ιe a)
  obtain ⟨⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩⟩ := hSt.int (ιg b)
  obtain ⟨kv, kout, kS⟩ := pivot_ops_stored hM hL hSt hy (dual_face_rev b) hna hbT wt (cv)
    hv₁ hv₂ hw₁ hw₂
  have kv' := kv
  rw [pivotOps_split, validOpsE_append_iff] at kv'
  -- the bounds of the forests along the operations
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU _ (hL.dual.e_lt b)).1
  have hv1b : |(v₁ : ℝ)| ≤ U := by have := (hU _ (hL.dual.e_lt a)).1; rwa [hv₁] at this
  have hv2b : |(v₂ : ℝ)| ≤ U := by have := (hU _ (hL.dual.e_lt a)).2; rwa [hv₂] at this
  have hw1b : |(w₁ : ℝ)| ≤ U := by have := (hU _ (hL.prim.e_lt b)).1; rwa [hw₁] at this
  have hw2b : |(w₂ : ℝ)| ≤ U := by have := (hU _ (hL.prim.e_lt b)).2; rwa [hw₂] at this
  have sub_le : ∀ x y : ℤ, |((x - y : ℤ) : ℝ)| ≤ |(x : ℝ)| + |(y : ℝ)| := fun x y => by
    push_cast; exact abs_sub _ _
  have d1 := sub_le (wt a - φ a - cv) v₁
  have d2 := sub_le (wt (M.rev a) + φ a + cv) v₂
  have d3 := sub_le (φ b) w₁
  have d4 := sub_le (φ (M.rev b)) w₂
  set Vp : ℝ := 5 * U + 2 * |(cv : ℝ)| + 4 * Tb with hVp
  have hAll : AllV Vp n Fo (pivotOps (ιf (M.face a)) (ιf (M.face (M.rev a))) (ιe a) (ιe b)
      (cutNode (runOpsE n Fo (pivotPre (ιf (M.face a)) (ιf (M.face (M.rev a))) cv)).1 ιf ιe M b)
      (ιf fe) (ιv y) (ιg a) (ιg b) (ιv (M.tail b)) cv (wt a - φ a - cv - v₁)
      (wt (M.rev a) + φ a + cv - v₂) (φ b - w₁) (φ (M.rev b) - w₂)) :=
    (pivot_allV hU _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).mono (by rw [hVp]; linarith)
  have hAllFo : VBnd Vp n Fo := hAll.vbnd
  rw [pivotOps_split] at hAll
  have hA1 := hAll.left
  have hA2 := hAll.right
  -- the selected dart and the operands
  obtain ⟨c₂, k₂, e₂, hk₂, q115, q116, q117, q118, q119, q120, q121, g₂⟩ :=
    rd1_exec hWa hP hK hc h114
  have o₂ := ORunC.ofGFr (H := H) e₂ hS g₂ (by omega) (by rfl)
  have hKM₂ := hKM.congr g₂.memFrame hB hL
  obtain ⟨c₃, k₃, e₃, hk₃, q122, q123, q124, q125, q126, q127, g₃⟩ :=
    rd2_exec hWa hP hL hK e₂.wb_right hKM₂ q120 hy
  have o₃ := ORunC.ofGFr (H := H) e₃ o₂.1.2.lcte g₃ (by omega) (by rfl)
  have hKM₃ := hKM₂.congr g₃.memFrame hB hL
  have p114 : c₃.nreg 114 = σ b := by
    rw [(g₃.1 114 (by omega)).1, (g₂.1 114 (by omega)).1, h114]
  have p115 : c₃.nreg 115 = σ (M.rev b) := by rw [(g₃.1 115 (by omega)).1, q115]
  obtain ⟨c₄, k₄, e₄, hk₄, t111, t112, t113, t114, t115, g₄, n₄⟩ :=
    rd3_exec hWa e₃.wb_right hKM₃ q122 q123 p114 p115
  have o₄ := ORunC.ofGFr (H := H) e₄ o₃.1.2.lcte g₄ (by omega) (by rfl)
  -- the values of the isolated nodes
  obtain ⟨c₅, G₅, o₅, u116, u117, u118, u119, n₅, r₅, out₅, m₅⟩ := val_orunC (P := P) hW
    e₄.wb_right o₄.1.2.lcte hAllFo hH (u := ιe a) (w := ιg b) (by rw [n₄ 126 (by omega), q126])
    (by rw [n₄ 119 (by omega), (g₃.1 119 (by omega)).1, q119]) (hL.dual.e_lt _)
    (hL.prim.e_lt _)
  -- the amounts
  obtain ⟨c₆, k₆, e₆, hk₆, a120, a121, a122, a123, a124, g₆, n₆⟩ := amt_exec (P := P) o₅.1.2.wb
  have o₆ := ORunC.ofGFr (H := H) e₆ o₅.1.2.lcte g₆ (by omega) (by rfl)
  -- the registers before the operations
  simp only [runOpsE] at u116 u117 u118 u119
  have R5 : c₅.rreg 110 = cv := by
    rw [r₅ 110 (by omega) (by omega), (g₄.1 110 (by omega)).2,
      (g₃.1 110 (by omega)).2, (g₂.1 110 (by omega)).2, h110]
  have R110 : c₆.rreg 110 = cv := by rw [(g₆.1 110 (by omega)).2, R5]
  have N : ∀ r, r < 130 → c₆.nreg r = c₃.nreg r := fun r hr => by
    rw [n₆, n₅ r (by omega), n₄ r hr]
  have N2 : ∀ r, r < 122 → c₆.nreg r = c₂.nreg r := fun r hr => by
    rw [N r (by omega), (g₃.1 r (by omega)).1]
  have R101 : c₆.nreg 101 = ιf fe := by
    rw [N2 101 (by omega), (g₂.1 101 (by omega)).1, h101]
  set zr : ℕ → ℤ := fun r => if r = 110 then cv else if r = 120 then -cv else
    if r = 121 then wt a - φ a - cv - v₁ else
    if r = 122 then wt (M.rev a) + φ a + cv - v₂ else
    if r = 123 then φ b - w₁ else φ (M.rev b) - w₂ with hzr
  have Z110 : c₆.rreg 110 = (zr 110 : ℝ) := by rw [R110]; simp [hzr]
  have Z120 : c₆.rreg 120 = (zr 120 : ℝ) := by rw [a120, R5]; simp [hzr]
  have Z121 : c₆.rreg 121 = (zr 121 : ℝ) := by
    rw [a121, R5, r₅ 111 (by omega) (by omega), r₅ 113 (by omega) (by omega), u116, t111,
      t113, hv₁]
    simp [hzr, hadef, hydef]
  have Z122 : c₆.rreg 122 = (zr 122 : ℝ) := by
    rw [a122, R5, r₅ 112 (by omega) (by omega), r₅ 113 (by omega) (by omega), u117, t112,
      t113, hv₂]
    simp [hzr, hadef, hydef]
  have Z123 : c₆.rreg 123 = (zr 123 : ℝ) := by
    rw [a123, r₅ 114 (by omega) (by omega), u118, t114, hw₁]; simp [hzr]
  have Z124 : c₆.rreg 124 = (zr 124 : ℝ) := by
    rw [a124, r₅ 115 (by omega) (by omega), u119, t115, hw₂]; simp [hzr]
  -- the first three operations
  have hA : opsA.map (ROp.eop c₆ zr) = pivotPre (ιf (M.face a)) (ιf (M.face (M.rev a)))
      (cv) := by
    simp only [opsA, List.map, ROp.eop, pivotPre, N 124 (by omega), N 125 (by omega), q124, q125]
    simp [hzr, hadef, hydef]
  obtain ⟨c₇, G₇, o₇, m₇, f₇⟩ := ropsS_orunC (P := P) hW zr hH opsA e₆.wb_right o₆.1.2.lcte
    (by simp only [opsA, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      ROp.Ok]; exact ⟨by omega, ⟨by omega, by omega, Z120⟩, by omega, by omega, Z110⟩)
    (by rw [hA]; exact kv'.1) (by rw [hA]; exact hA1)
  rw [hA] at o₇
  -- the cut face
  have W7 : ∀ r, r < 160 → c₇.nreg r = c₆.nreg r := fun r hr => f₇.1 r (by omega)
  obtain ⟨c₈, G₈, o₈, z128, n₈, r₈, out₈, m₈⟩ := z_orunC (P := P) hW hL o₇.1.2.wb o₇.1.2.lcte
    hA2.vbnd hH (b := b)
    (by rw [W7 118 (by omega), N2 118 (by omega), q118])
    (by rw [W7 116 (by omega), N2 116 (by omega), q116])
    (by rw [W7 117 (by omega), N2 117 (by omega), q117])
  -- the thirteen other operations
  have M8 : ∀ r, r < 128 → c₈.nreg r = c₆.nreg r := fun r hr => by rw [n₈ r hr, W7 r (by omega)]
  have Q8 : ∀ r, r < 128 → c₈.rreg r = c₆.rreg r := fun r hr => by
    rw [r₈ r hr, f₇.2.1 r (by omega)]
  have hB' : opsB.map (ROp.eop c₈ zr) = [.cut (cutNode (runOpsE n Fo (pivotPre (ιf (M.face a))
      (ιf (M.face (M.rev a))) (cv))).1 ιf ιe M b), .cut (ιe b), .add (ιe a) (zr 121),
      .add2 (ιe a) (zr 122), .link (ιe a) (ιf (M.face (M.rev a))), .link (ιf (M.face a)) (ιe a),
      .evert (ιf fe), .cut (ιv y), .cut (ιg a), .add (ιg b) (zr 123), .add2 (ιg b) (zr 124),
      .link (ιg b) (ιv (M.tail b)), .link (ιv y) (ιg b)] := by
    simp only [opsB, List.map, ROp.eop, z128, M8 118 (by omega), M8 126 (by omega),
      M8 125 (by omega), M8 124 (by omega), M8 101 (by omega), M8 120 (by omega),
      M8 127 (by omega), M8 119 (by omega), M8 121 (by omega), R101, N2 118 (by omega),
      N 126 (by omega), N 125 (by omega), N 124 (by omega), N2 120 (by omega),
      N 127 (by omega), N2 119 (by omega), N2 121 (by omega), q118, q126, q125, q124, q120,
      q127, q119, q121]
    rfl
  obtain ⟨c₉, G₉, o₉, m₉, f₉⟩ := ropsS_orunC (P := P) hW zr hH opsB o₈.1.2.wb o₈.1.2.lcte
    (by
      simp only [opsB, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
        ROp.Ok]
      exact ⟨by omega, by omega, ⟨by omega, by omega, (Q8 121 (by omega)).trans Z121⟩,
        ⟨by omega, by omega, (Q8 122 (by omega)).trans Z122⟩, ⟨by omega, by omega⟩,
        ⟨by omega, by omega⟩, by omega, by omega, by omega,
        ⟨by omega, by omega, (Q8 123 (by omega)).trans Z123⟩,
        ⟨by omega, by omega, (Q8 124 (by omega)).trans Z124⟩, ⟨by omega, by omega⟩,
        ⟨by omega, by omega⟩⟩)
    (by rw [hB']; exact kv'.2) (by rw [hB']; exact hA2)
  rw [hB'] at o₉
  -- the new parent dart
  have W9 : ∀ r, r < 128 → c₉.nreg r = c₆.nreg r := fun r hr => by
    rw [f₉.1 r (by omega), M8 r hr]
  have hyn := hL.prim.f_lt y
  obtain ⟨c₁₀, k₁₀, e₁₀, hk₁₀, sm₁₀, sr₁₀, so₁₀, sf₁₀⟩ := st_exec (P := P) hWa o₉.1.2.wb
    (by rw [W9 120 (by omega), N2 120 (by omega), q120]) hyn
  have o₁₀ : ORunC P W H B n stS c₉ _ G₉ c₁₀ [] G₉ 0 k₁₀ := ORunC.glue e₁₀ o₉.1.2.lcte
    (fun a' ha' _ => by
      rw [sm₁₀, sr₁₀, upd_other _ _ _ (by unfold aTP; omega)]; exact ⟨rfl, rfl⟩)
    (sf₁₀ 151 (by omega)).1 (by rfl)
  have hos : pivotPre (ιf (M.face a)) (ιf (M.face (M.rev a))) (cv) ++
      [.cut (cutNode (runOpsE n Fo (pivotPre (ιf (M.face a))
      (ιf (M.face (M.rev a))) (cv))).1 ιf ιe M b), .cut (ιe b), .add (ιe a) (zr 121),
      .add2 (ιe a) (zr 122), .link (ιe a) (ιf (M.face (M.rev a))), .link (ιf (M.face a)) (ιe a),
      .evert (ιf fe), .cut (ιv y), .cut (ιg a), .add (ιg b) (zr 123), .add2 (ιg b) (zr 124),
      .link (ιg b) (ιv (M.tail b)), .link (ιv y) (ιg b)] = pivotOps (ιf (M.face a))
        (ιf (M.face (M.rev a))) (ιe a) (ιe b) (cutNode (runOpsE n Fo (pivotPre (ιf (M.face a))
          (ιf (M.face (M.rev a))) (cv))).1 ιf ιe M b) (ιf fe) (ιv y) (ιg a) (ιg b)
        (ιv (M.tail b)) (cv) (wt a - φ a - cv - v₁) (wt (M.rev a) + φ a + cv - v₂)
        (φ b - w₁) (φ (M.rev b) - w₂) := by
    rw [pivotOps_split]; simp [hzr]
  have o := o₂.seq (o₃.seq (o₄.seq (o₅.seq (o₆.seq (o₇.seq (o₈.seq (o₉.seq o₁₀)))))))
  simp only [List.nil_append, List.append_nil] at o
  rw [hos] at o
  -- the memory
  have hmf : MemFrame B n (mem c) (mem c₉) :=
    ((((((g₂.memFrame.trans B n g₃.memFrame).trans B n g₄.memFrame).trans B n
      m₅).trans B n g₆.memFrame).trans B n m₇).trans B n m₈).trans B n m₉
  have p114' : c₉.nreg 114 = σ b := by rw [W9 114 (by omega), N2 114 (by omega),
    (g₂.1 114 (by omega)).1, h114]
  refine ⟨c₁₀, G₉, _, o.mono ?_ ?_, ⟨v₁, v₂, w₁, w₂, hv₁, hv₂, hw₁, hw₂, rfl⟩, ?_, kout, kS,
    pivot_vbnd hM hL hSt hy (dual_face_rev b) hna hbT wt cv hv₁ hv₂ hw₁ hw₂ hU ht₁ ht₂ ht₃ ht₄,
    ⟨fun x hx => ?_, fun d => ?_, fun d => ?_⟩, ?_, fun a' ha' => ?_, fun a' ha' hne => ?_⟩
  · simp only [opsA, opsB, List.length_cons, List.length_nil]; omega
  · omega
  · simp [pivotOps]
  · -- the parent darts
    rw [DTree.reparent_par, sm₁₀]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy, hxy, upd_same, p114']
    · rw [ite_eq_right hxy,
        upd_other _ _ _ (fun h => hxy (hL.prim.f_inj (by unfold aTP at h; omega)))]
      have hx' : x ≠ T.root := hx
      have h := (hmf (aTP + ιv x) (Or.inl (by have := hL.prim.f_lt x; unfold aTP; omega))).1
      exact h.trans (hKM.tp x hx')
  · rw [sr₁₀]
    exact ((hmf (aWT + σ d) (Or.inl (by have := hσ d; unfold aWT; omega))).2).trans (hKM.wt d)
  · rw [sr₁₀]
    exact ((hmf (aPH nD + σ d) (Or.inl (by have := hσ d; unfold aPH; omega))).2).trans
      (hKM.ph d)
  · have l₅ : LoFr c₄ c₅ := ⟨fun r hr => ⟨n₅ r (by omega), r₅ r (by omega) (by omega)⟩, out₅⟩
    have l₈ : LoFr c₇ c₈ := ⟨fun r hr => ⟨n₈ r (by omega), r₈ r (by omega)⟩, out₈⟩
    have l₁₀ : LoFr c₉ c₁₀ := ⟨fun r hr => sf₁₀ r (by omega), so₁₀⟩
    exact ((((((((g₂.loFr (by omega)).trans (g₃.loFr (by omega))).trans
      (g₄.loFr (by omega))).trans l₅).trans (g₆.loFr (by omega))).trans (RegFr.loFr f₇)).trans
      l₈).trans (RegFr.loFr f₉)).trans l₁₀
  · rw [sr₁₀]; exact (hmf a' ha').2
  · rw [sm₁₀, upd_other _ _ _ hne]; exact (hmf a' ha').1

theorem piv_orunC (hW : B + 16 * (n + 1) ≤ W) (hWa : 8 * nD + n ≤ W) (hB : n + 2 * nD ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ W) (hM : M.IsPlane) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) {c : Config} (hc : WordsBounded W c) {Fo : Forest}
    {G : List VT} (hS : LCTE B n Fo G c) {φ wt : D → ℤ} {fe : F} {Lo : ℝ} {T : DTree M.dual}
    {val : D → ℤ} (hSt : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val)
    (hKM : KMem M σ ιv T wt φ c) (h101 : c.nreg 101 = ιf fe) {b : D}
    (h196 : c.nreg 196 = ιe b) (h195 : c.rreg 195 = val b)
    (hpar : Fo.par (ιe b) = ιf (M.face b)) (hfb : M.face b ≠ M.face (M.rev b))
    (hy : M.head b ≠ T.root) (hna : ¬ T.Anc (M.head b) (M.dual.face b)) (hbT : ¬ T.InT b)
    {U Tb : ℝ} (hU : VBnd U n Fo)
    (ht₁ : |((wt (T.par (M.head b)) - φ (T.par (M.head b)) - val b : ℤ) : ℝ)| ≤ Tb)
    (ht₂ : |((wt (M.rev (T.par (M.head b))) + φ (T.par (M.head b)) + val b : ℤ) : ℝ)| ≤ Tb)
    (ht₃ : |(φ b : ℝ)| ≤ Tb) (ht₄ : |(φ (M.rev b) : ℝ)| ≤ Tb)
    (hH : 2 * (5 * U + 2 * |(val b : ℝ)| + 4 * Tb) ≤ H) :
    ∃ c' G' os, ORunC P W H B n (pivS B nD) c Fo G c' os G' 26 97 ∧
      (∃ v₁ v₂ w₁ w₂ : ℤ, Fo.val (ιe (T.par (M.head b))) = v₁ ∧
        Fo.val2 (ιe (T.par (M.head b))) = v₂ ∧ Fo.val (ιg b) = w₁ ∧ Fo.val2 (ιg b) = w₂ ∧
        os = pivotOps (ιf (M.face (T.par (M.head b)))) (ιf (M.face (M.rev (T.par (M.head b)))))
          (ιe (T.par (M.head b))) (ιe b)
          (cutNode (runOpsE n Fo (pivotPre (ιf (M.face (T.par (M.head b))))
            (ιf (M.face (M.rev (T.par (M.head b))))) (val b))).1 ιf ιe M b)
          (ιf fe) (ιv (M.head b)) (ιg (T.par (M.head b))) (ιg b) (ιv (M.tail b)) (val b)
          (wt (T.par (M.head b)) - φ (T.par (M.head b)) - val b - v₁)
          (wt (M.rev (T.par (M.head b))) + φ (T.par (M.head b)) + val b - v₂)
          (φ b - w₁) (φ (M.rev b) - w₂)) ∧
      os.length = 16 ∧ (runOpsE n Fo os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ fe (Lo - |(val b : ℝ)|) (runOpsE n Fo os).1
        (T.reparent (M.head b) b hy (dual_face_rev b) hna)
        (pivotVal T φ wt val (M.head b) (val b)) ∧
      VBnd (max (U + |(val b : ℝ)|) Tb) n (runOpsE n Fo os).1 ∧
      KMem M σ ιv (T.reparent (M.head b) b hy (dual_face_rev b) hna) wt φ c' ∧ LoFr c c' ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → c'.rmem a = c.rmem a) ∧
      (∀ a, (a < B ∨ B + 16 * (n + 1) ≤ a) → a ≠ aTP + ιv (M.head b) →
        c'.nmem a = c.nmem a) := by
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU _ (hL.dual.e_lt b)).1
  have hTb : 0 ≤ Tb := (abs_nonneg _).trans ht₃
  obtain ⟨c₁, G₁, o₁, s114, s110, sfr, sm⟩ := sel_orunC (σ := σ) hW hWa hP hL hK hc hS
    (hU.mono (show U ≤ 5 * U + 2 * |(val b : ℝ)| + 4 * Tb by
      have := abs_nonneg (val b : ℝ); linarith)) hH h196 hpar hfb
  obtain ⟨c₂, G₂, os, o₂, hos, hlen, hout, hSt', hVB, hKM₂, lf₂, rm₂, nm₂⟩ := pivCore_orunC hW hWa
    hB hP hM hL hK o₁.1.2.wb o₁.1.2.lcte hSt (hKM.congr sm hB hL)
    (by rw [(sfr.1 101 (by omega)).1, h101]) s114 (cv := val b) (by rw [s110, h195]) hy hna hbT
    hU ht₁ ht₂ ht₃ ht₄ hH
  refine ⟨c₂, G₂, os, (o₁.seq o₂).mono (by omega) (by omega), hos, hlen, hout, hSt', hVB, hKM₂,
    sfr.trans lf₂, fun a ha => (rm₂ a ha).trans (sm a ha).2,
    fun a ha hne => (nm₂ a ha hne).trans (sm a ha).1⟩

end

end Klein

end PlanarFlow
