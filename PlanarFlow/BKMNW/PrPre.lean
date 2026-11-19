module

public import PlanarFlow.BKMNW.PrPrint

/-!
# The preprocessing of the maximum-flow program with loops, as one run

`MEncL d W`: `MEnc d W` (`PpEnc.lean`) **without `loopless`** (loops allowed in the input).
**`pre_execL`**: from a configuration with zero memory, `zP a p ; ppALB ; ppBB ; r8903 := 0`
writes the index arrays of `lpreMapX (map wf) (pe _) _` at `F₀ = B + 84 n + 2 (K + n) + 1`
(`B = zB a p d`), the registers `6700 … 6707`, keeps the memory below `B` zero, and prints the
positions `POS[3 x]` (an invalid slot, e.g. of a loop, has its position in `[N, 7 n)`).
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

/-- **A maximum-flow instance in the drawing's encoding, loops allowed**, for the word bound `W`. -/
structure MEncL (d : List ℕ) (W : ℕ) : Prop where
  wf : Wf d
  plane : (map wf).IsPlane
  rotT : ∀ i < nd d, ∀ j < nd d, tl d i = tl d j → ∃ k, (rotW d)^[k] i = j
  faceT : ∀ i < nd d, ∀ j < nd d, fc d i = fc d j → ∃ k, (nx d)^[k] i = j
  disj : ∀ v < nv d, bp d v = 0 ∨ bn d v = 0
  word_le : ∀ i, word d i ≤ W

lemma bigN_le_zb {d : List ℕ} (wf : Wf d) : bigN (map wf) (fun i => cp d i) ≤ zb d := by
  rw [bigN_eq_sumL wf]
  unfold zb
  exact Finset.sum_le_sum fun x _ => by
    have := fl_le_one (tl d (rv d x) ≠ tl d x)
    calc fl (tl d (rv d x) ≠ tl d x) * cp d x ≤ 1 * cp d x := Nat.mul_le_mul_right _ this
      _ = cp d x := one_mul _

/-- The preprocessing with the test register. -/
def preL (a p : ℕ) : Stmt := .seq (zP a p) (.seq ppALB (.seq ppBB (block [.constN 8903 0])))

set_option maxHeartbeats 2000000 in
theorem pre_execL {a p : ℕ} {d : List ℕ} {W : ℕ} (h : MEncL d W) (hn : 0 < nd d)
    (hW1 : 100000 ≤ W) (hW2 : 2 * zb d + 7 * nd d + 20 ≤ W)
    (hW3 : (7 * nd d + zb d + 1) ^ p ≤ W)
    (hW4 : 10 * zB a p d + 300 * nd d + 4 * nv d + (2 * (nv d + nd d) + 1) * (7 * nd d) + 300 ≤ W)
    (c : Config) (hc : WordsBounded W c) (hm : ∀ x, c.nmem x = 0) :
    ∃ c' t, Exec (inp d) W (preL a p) c c' t ∧ t ≤ 2409 * nd d + 50 * nv d + p + 721 ∧
      let n := nd d
      let N := ∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s)
      let F₀ := zB a p d + 84 * n + 2 * (nv d + nd d) + 1
      ∃ pos : ℕ → ℕ, Sorted (map h.wf) (fun v => v.val) (nv d) N (srtD h.wf) pos ∧
      (∀ s < 7 * n, ¬ ValidS (map h.wf) s → N ≤ pos s ∧ pos s < 7 * n) ∧
      (∀ i < N, c'.nmem (F₀ + i) = pos (revS (map h.wf) (srtD h.wf i))) ∧
      (∀ i < N, c'.nmem (F₀ + 7 * n + i) = pos (rotS (map h.wf) (srtD h.wf i))) ∧
      (∀ i < N, c'.nmem (F₀ + 14 * n + i) =
        capS (map h.wf) (fun i => cp d i) (srcF d) (snkF d) (srtD h.wf i)) ∧
      (∀ i < N, c'.nmem (F₀ + 21 * n + i) = krS (map h.wf) (srcF d) (snkF d) (srtD h.wf i)) ∧
      (∀ i < N, c'.nmem (F₀ + 28 * n + i) =
        keyS (map h.wf) (fun v => v.val) (nv d) (srtD h.wf i)) ∧
      (∀ i < N, c'.nmem (F₀ + 35 * n + i) = pos (rtS (map h.wf) (srtD h.wf i))) ∧
      c'.nreg 6700 = N ∧ c'.nreg 6701 = F₀ ∧ c'.nreg 6702 = F₀ + 7 * n ∧
      c'.nreg 6703 = F₀ + 14 * n ∧ c'.nreg 6704 = F₀ + 21 * n ∧ c'.nreg 6705 = 1 ∧
      c'.nreg 6706 = bigN (map h.wf) (fun i => cp d i) ∧ c'.nreg 6707 = F₀ + 42 * n + 2 ∧
      c'.nmem (F₀ + 42 * n + 2 - 1) = F₀ + 28 * n ∧
      c'.nmem (F₀ + 42 * n + 2 - 1 - 1) = F₀ + 35 * n ∧
      c'.nreg 8903 = 0 ∧
      c'.output = c.output ++ (List.range n).map (fun x => pos (3 * x)) ∧
      MemZ (zB a p d - 1) c' ∧ N ≤ 7 * n := by
  have hwd := h.word_le
  have hrot : (map h.wf).RotTrans := map_rotTrans h.wf h.rotT
  have hZle : bigN (map h.wf) (fun i => cp d i) ≤ zb d := bigN_le_zb h.wf
  have hbig : ∑ x ∈ range (nd d), fl (tl d (rv d x) ≠ tl d x) * cp d x ≤ W := by
    rw [← bigN_eq_sumL h.wf]; omega
  obtain ⟨c₀, t₀, e₀, ht₀, r30, m0, -, -, o0⟩ := zP_exec (P := inp d) (d := d) rfl hwd a p
    c hc (by omega) (by omega) (by omega) hW3
  have hB1 : 1 ≤ zB a p d := by unfold zB; omega
  obtain ⟨c₁, t₁, e₁, ht₁, hS, mA, r00, r03, r04, r05, r06, r08, r09, r30', r31, -, -, o1⟩ :=
    ppAL_execB (P := inp d) (d := d) rfl h.wf hrot hwd c₀ e₀.wb_right r30 hbig (by nlinarith)
  obtain ⟨c₂, t₂, e₂, ht₂, pos, hsort, hinv, a1, a2, a3, a4, a5, a6, w0, w1, w2, w3, w4, w5, w6,
    w7, m1, m2, o2, mB, hN7⟩ := ppBL_execB (P := inp d) (d := d) rfl hwd h.wf hrot hn c₁
      e₁.wb_right hS r00 r03 r04 r05 r06 r08 r09 r30' r31 (by nlinarith)
  obtain ⟨c₃, t₃, e₃, ht₃, v03, f3, m3, o3⟩ : ∃ c₃ t₃,
      Exec (inp d) W (block [.constN 8903 0]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 8903 = 0 ∧
      (∀ x, x ≠ 8903 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧
      c₃.output = c₂.output := by
    have hw := e₂.wb_right
    exec_block
    · omega
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl⟩
    · config_simp
    · config_simp; simp (disch := omega) only [upd_other]
  refine ⟨c₃, t₀ + (t₁ + (t₂ + t₃)), .seq e₀ (.seq e₁ (.seq e₂ e₃)), by omega, pos, hsort, hinv,
    fun i hi => by rw [m3]; exact a1 i hi, fun i hi => by rw [m3]; exact a2 i hi,
    fun i hi => by rw [m3]; exact a3 i hi, fun i hi => by rw [m3]; exact a4 i hi,
    fun i hi => by rw [m3]; exact a5 i hi, fun i hi => by rw [m3]; exact a6 i hi,
    by rw [f3 _ (by omega)]; exact w0, by rw [f3 _ (by omega)]; exact w1,
    by rw [f3 _ (by omega)]; exact w2, by rw [f3 _ (by omega)]; exact w3,
    by rw [f3 _ (by omega)]; exact w4, by rw [f3 _ (by omega)]; exact w5,
    by rw [f3 _ (by omega)]; exact w6, by rw [f3 _ (by omega)]; exact w7,
    by rw [m3]; exact m1, by rw [m3]; exact m2, v03, by rw [o3, o2, o1, o0],
    fun x hx => ?_, hN7⟩
  rw [m3, mB x (by omega), mA x (by omega), m0]; exact hm x

end Pp

end BKMNW

end PlanarFlow
