module

public import PlanarFlow.BKMNW.PpPD

/-!
# From the per-dart arrays of the input to the arrays of the value blocks

For `M = Feas.map wf` without loops, the arrays written by `pd1` and `pd2` (`PD1`, `PD2`) are the
per-dart arrays the value blocks of the slot functions read (`RotArrs`, `CapArrs`, `KeyArrs`, the
flags `NL`), with the capacities `cp`, the sources `srcF`, the sinks `snkF`, the vertex numbers
`Fin.val` (`K = nv`), and the total capacity `bigN = ∑ cp` (`bigN_map`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine Feas OrbLab

lemma fl_congr {p q : Prop} (h : p ↔ q) : fl p = fl q := by rw [propext h]

variable {d : List ℕ} (wf : Wf d) (hl : ∀ i < nd d, tl d (rv d i) ≠ tl d i)
include wf

lemma nx_surj {x : ℕ} (hx : x < nd d) : ∃ y < nd d, nx d y = x := by
  obtain ⟨p, hp, e⟩ := OrbLab.iter_period (nx_permOn wf) hx
  refine ⟨(nx d)^[p - 1] x, OrbLab.iter_lt (nx_permOn wf) hx _, ?_⟩
  rw [← Function.iterate_succ_apply' (nx d), show (p - 1).succ = p by omega, e]

include hl

theorem rotArrs_of (hrot : (map wf).RotTrans) {c : Config} {B : ℕ}
    (h1 : PD1 d B c.nmem) (h2 : PD2 d B c.nmem) (r11 : c.nreg 8711 = B + 1 * nd d)
    (r12 : c.nreg 8712 = B + 2 * nd d) (r13 : c.nreg 8713 = B + 3 * nd d)
    (r14 : c.nreg 8714 = B + 4 * nd d) :
    RotArrs (map wf) c (B + 1 * nd d) (B + 2 * nd d) (B + 3 * nd d) (B + 4 * nd d) where
  bsg := r11
  bpi := r12
  bcv := r13
  bcf := r14
  sg x hx := by rw [h1.fsg x hx, sgI_map wf hl hx]; rfl
  pi x hx := by
    obtain ⟨y, hy, rfl⟩ := nx_surj wf hx
    rw [h2.fpi y hy, piI_map wf hl hy]
  cv x hx := by
    rw [h2.fcv x hx]; apply fl_congr; rw [cvI_map wf hl hrot hx]; omega
  cf x hx := by
    rw [h2.fcf x hx]; apply fl_congr; rw [cfI_map wf hl hx]; omega
  sg_lt x hx := by rw [sgI_map wf hl hx]; exact wf.nx_lt _ (wf.rv_lt x hx)
  pi_lt x hx := piI_lt_map wf hl hx

theorem capArrs_of {c : Config} {B : ℕ} (h1 : PD1 d B c.nmem)
    (r16 : c.nreg 8716 = B + 6 * nd d) (r17 : c.nreg 8717 = B + 7 * nd d)
    (r18 : c.nreg 8718 = B + 8 * nd d) :
    CapArrs (map wf) (fun i => cp d i) (srcF d) (snkF d) c (B + 6 * nd d) (B + 7 * nd d)
      (B + 8 * nd d) where
  bcp := r16
  bts := r17
  btt := r18
  cp x hx := by rw [h1.fcp x hx, xt_cp hx]
  ts x hx := by rw [h1.fts x hx]; exact fl_congr (tlIn_src wf hx).symm
  tt x hx := by rw [h1.ftt x hx]; exact fl_congr (tlIn_snk wf hx).symm

theorem keyArrs_of {c : Config} {B : ℕ} (h1 : PD1 d B c.nmem) (h2 : PD2 d B c.nmem)
    (r15 : c.nreg 8715 = B + 5 * nd d) (r19 : c.nreg 8719 = B + 9 * nd d) :
    KeyArrs (map wf) (fun v => v.val) (nv d) c (B + 5 * nd d) (B + 9 * nd d) where
  bfl := r15
  bvt := r19
  fl x hx := by rw [h2.ffl x hx, flI_map wf hl hx]
  vt x hx := by rw [h1.fvt x hx, xt_tl wf hx]
  fl_lt x hx := by rw [flI_map wf hl hx]; exact olab_lt (nx_permOn wf) hx
  vt_lt x hx := by rw [xt_tl wf hx]; exact wf.tl_lt x hx

lemma nl_of {mem : ℕ → ℕ} {B : ℕ} (h1 : PD1 d B mem) {x : ℕ} (hx : x < nd d) :
    mem (B + 10 * nd d + x) = fl (IsNl (map wf) x) := by
  rw [h1.fnl x hx]; apply fl_congr
  exact ⟨fun _ => (isNl_map wf hl).2 hx, fun _ => hl x hx⟩

lemma bigN_map : bigN (map wf) (fun i => cp d i) =
    ∑ x ∈ range (nd d), fl (tl d (rv d x) ≠ tl d x) * cp d x := by
  unfold bigN
  have e1 : ∀ x ∈ range (nd d), fl (tl d (rv d x) ≠ tl d x) * cp d x = cp d x := by
    intro x hx
    have : fl (tl d (rv d x) ≠ tl d x) = 1 := by
      unfold fl; rw [ppIteT (hl x (mem_range.1 hx))]
    rw [this, one_mul]
  rw [sum_congr rfl e1, ← Fin.sum_univ_eq_sum_range (fun x => cp d x)]
  rw [Finset.sum_coe_sort (nlDarts (map wf)) (fun x : Fin (nd d) => cp d x), nlDarts_map wf hl]

end Pp

end BKMNW

end PlanarFlow
