module

public import PlanarFlow.BKMNW.PpPrB

/-!
# The maximum-flow pipeline from the drawing's encoding (conditional on the max-flow program)

`mfFull sepL stepP = ppA ; ppB ; mfProg sepL stepP ; prB` from the encoding `d` of a plane map
without loops (`MEnc d W`, `PlanarFlow/Spec.lean`'s `Feas` words, capacities `cp`, sources
`bp ≠ 0`, sinks `bn ≠ 0`):

1. `ppA ; ppB` (`PpPP.lean`) writes the index arrays of the preprocessed map with explicit pendant
   darts `LP M hrot` sorted by tails, and prints `p = [POS[3 x] | x < n]`, the position of the dart
   `old x` in the sorted order;
2. `mfProg` (the program of `mfMain_cMachXGE`) computes the flow (no output, `noEmit_mfProg`);
3. `prB` prints `Z` and the root's flow array `q` (`FL[i] = Z + f(en i)`).

**`mf_pipeline`**: assuming `MfMainSpec sepL stepP C C₀ R` (the max-flow program's theorem,
`PpHyp.lean`) and that `sepL`, `stepP` print nothing, the whole program runs within
`ppHead C C₀ n + 31200 n + 50 K + 3000` steps (`n = nd`, `K = nv`; `ppHead = O(n log³ n)`) and
prints `p ++ Z :: q` with `|p| = n`; the flow `x ↦ q[p[x]] - Z` is a maximum flow from the
sources to the sinks.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv Feas
  Orbit CombMap PlanarSeparator.StDart NegSSSP.Driver

/-- **The whole maximum-flow program**: preprocessing, max flow, print. -/
def mfFull (sepL stepP : Stmt) : Stmt := .seq ppA (.seq ppB (.seq (mfProg sepL stepP) prB))

/-- The headline cost of the max-flow program on `n` darts (`O(n log³ n)`). -/
def ppHead (C C₀ n : ℕ) : ℕ :=
  (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C * n * lg n ^ 3 +
    (100000 + 11) ^ 2 * 28 * C₀ * n * lg n

/-- **The word bound of the pipeline**: `W ≥ 100000`, twice the total capacity, the counting sort
(`(2(K + n) + 1) 7 n`), and the room of the max-flow program (`R` per call, at most `7 n`
darts). -/
def PipeRoom (R : ℕ → ℕ) (d : List ℕ) (W : ℕ) : Prop :=
  100000 ≤ W ∧ 2 * (∑ x ∈ range (nd d), cp d x) ≤ W ∧
    300 * nd d + 4 * nv d + (2 * (nv d + nd d) + 1) * (7 * nd d) + 300 ≤ W ∧
    240 * nd d + 2 * nv d + 300 + (14 * nd d + 1) * (770 * nd d + 80 + R (7 * nd d)) ≤ W

lemma srcF_snkF_disjoint {d : List ℕ} {W : ℕ} (h : MEnc d W) : Disjoint (srcF d) (snkF d) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  simp only [srcF, snkF, Finset.mem_filter, mem_univ, true_and] at hv hv'
  rcases h.disj v v.2 with e | e
  · exact hv e
  · exact hv' e

lemma bigN_eq_sum {d : List ℕ} (wf : Wf d) (hl : ∀ i < nd d, tl d (rv d i) ≠ tl d i) :
    bigN (map wf) (fun i => cp d i) = ∑ x ∈ range (nd d), cp d x := by
  rw [bigN_map wf hl]
  refine sum_congr rfl fun x hx => ?_
  unfold fl; rw [ppIteT (hl x (mem_range.1 hx)), one_mul]

set_option maxHeartbeats 4000000 in
/-- **The maximum-flow pipeline (conditional on the max-flow program's theorem)**: from the encoding `d`
of a plane map without loops, with transitive rotations and faces, disjoint sources and sinks, the
program `mfFull sepL stepP` runs within `ppHead C C₀ n + 31200 n + 50 K + 3000` steps
(`n = nd d` darts, `K = nv d` vertices) and prints `p ++ Z :: q` with `|p| = n`; the flow
`x ↦ q[p[x]] - Z` is a maximum flow of the instance (capacities `ucap d`, sources `srcF d`, sinks
`snkF d`). Hypotheses: `MfMainSpec sepL stepP C C₀ R` (the theorem of the max-flow program with
the separator `sepL` and the node step `stepP`, `PpHyp.lean`), `sepL` and `stepP` print nothing,
`R` monotone, and the word bound `PipeRoom R d W`. -/
theorem mf_pipeline {sepL stepP : Stmt} {C C₀ : ℕ} {R : ℕ → ℕ}
    (hspec : MfMainSpec sepL stepP C C₀ R) (hE1 : Stmt.noEmit sepL = true)
    (hE2 : Stmt.noEmit stepP = true) (hRm : Monotone R) {d : List ℕ} {W : ℕ} (h : MEnc d W)
    (hn : 0 < nd d) (hroom : PipeRoom R d W) :
    ∃ (p : List ℕ) (Z : ℕ) (q : List ℕ), p.length = nd d ∧
      RunsWithin (compile (mfFull sepL stepP) 0 ++ [Instr.halt]) (inp d) W
        (ppHead C C₀ (nd d) + 31200 * nd d + 50 * nv d + 3000) (p ++ Z :: q) ∧
      IsMax (map h.wf) (ucap d) (srcF d) (snkF d)
        (fun x => ((q.getD (p.getD x 0) 0 : ℕ) : ℤ) - Z) := by
  obtain ⟨hW1, hW2, hW3, hW4⟩ := hroom
  have wf := h.wf
  have hl := h.loopless
  have hwd := h.word_le
  have hrot : (map h.wf).RotTrans := map_rotTrans h.wf h.rotT
  have hface : (map h.wf).FaceTrans := map_faceTrans h.wf h.faceT
  have hZs := bigN_eq_sum h.wf hl
  have hbig : ∑ x ∈ range (nd d), fl (tl d (rv d x) ≠ tl d x) * cp d x ≤ W := by
    rw [← bigN_map h.wf hl, hZs]; omega
  -- the preprocessing
  obtain ⟨c₁, t₁, e₁, ht₁, hS, r00, r03, r04, r05, r06, r08, r09, r30, r31, -, -, o1⟩ :=
    ppA_exec (P := inp d) (d := d) rfl h.wf hl hrot hwd initConfig (wordsBounded_initConfig W) hbig
      (by nlinarith)
  obtain ⟨c₂, t₂, e₂, ht₂, pos, hsort, a1, a2, a3, a4, a5, a6, w0, w1, w2, w3, w4, w5, w6, w7,
    m1, m2, o2, hN7⟩ := ppB_exec (P := inp d) (d := d) rfl hwd h.wf hl hrot hn c₁ e₁.wb_right hS r00 r03
      r04 r05 r06 r08 r09 r30 r31 hW3
  have hx0 : (⟨0, hn⟩ : Fin (nd d)) ∈ nlDarts (map h.wf) := by
    rw [nlDarts_map h.wf hl]; exact mem_univ _
  have : Nonempty (TDart (map h.wf) ⊕ (PVert (map h.wf) × Bool)) := ⟨.inl (old ⟨_, hx0⟩)⟩
  obtain ⟨hcard, hsurj, hgid, hts, hrev, hsig, hcap, hkr, hkey, hrt⟩ :=
    sortConv (M := map h.wf) hrot (fun i => cp d i) (srcF d) (snkF d) hsort
  have hne : (nlDarts (map h.wf)).Nonempty := ⟨_, hx0⟩
  have G := @hspec _ _ _ _ _ _ _ _ _ (map h.wf) h.plane hrot hface (pe (map h.wf))
    (pe_tail (map h.wf) hrot) (fun i => (cp d i : ℤ)) (fun _ => Nat.cast_nonneg _) (srcF d) (snkF d)
    (srcF_snkF_disjoint h) hne _ (enS (M := map h.wf) (srtD h.wf))
    (enS (M := map h.wf) (srtD h.wf) 0) _ _ hcard hsurj hgid
    (νX_injective (M := map h.wf) (hrot := hrot) (vn := fun v => v.val) (K := nv d)
      Fin.val_injective (fun v => v.2)) (qpar_νX (map h.wf) (fun v => v.val) (nv d)) hts
  unfold MfMainGoal at G
  have hZ2 : 2 * bigN (map h.wf) (fun i => cp d i) ≤ W := by rw [hZs]; exact hW2
  have hRN : R (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s)) ≤ R (7 * nd d) := hRm hN7
  have hmul : (2 * (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s)) + 1) *
      (110 * (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s)) + 80 +
        R (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s))) ≤
      (14 * nd d + 1) * (770 * nd d + 80 + R (7 * nd d)) :=
    Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨hpiece, c₃, t₃, e₃, ht₃, hout, hmax⟩ := G (I := inp d) hW1 hZ2 (by omega) c₂ e₂.wb_right
    w0 w1 w2 w3 w4 w5 w6 w7 m1 m2
    (fun i hi => by rw [a1 i hi]; exact hrev i hi)
    (fun i hi => by rw [a2 i hi]; exact hsig i hi)
    (fun i hi => by rw [a3 i hi]; exact ⟨hcap i hi, capS_le_bigN h.wf hl _⟩)
    (fun i hi => by rw [a4 i hi]; exact hkr i hi)
    (fun i hi => by rw [a5 i hi]; exact hkey i hi)
    (fun i hi hc => by rw [a6 i hi]; exact hrt i hi hc)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have o3 : c₃.output = c₂.output := Exec.output_eq (s := mfProg sepL stepP) e₃
    (noEmit_mfProg hE1 hE2)
  obtain ⟨m, en', hL, -, hf⟩ := hout
  obtain ⟨hmN, hen⟩ := lay_en_eq (M := map h.wf) hrot hsort (x := (_, [], _)) hpiece rfl hL
  subst hmN
  have hfr : frB d = 84 * nd d + 2 * (nv d + nd d) + 1 + 42 * nd d + 2 + 5 := by
    unfold frB; ring
  have hN : c₃.nmem (frB d) = ∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s) := by
    rw [hfr, hL.hm]
  have hZ : c₃.nmem (frB d + 3) = bigN (map h.wf) (fun i => cp d i) := by
    rw [hfr, hL.hz]
  obtain ⟨c₄, t₄, e₄, ht₄, o4⟩ := prB_exec (P := inp d) (d := d) rfl hwd c₃ e₃.wb_right hN hZ
    (by rw [hfr]; omega)
  have ht₃' : t₃ ≤ 95 * (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s)) + 200 +
      (ppHead C C₀ (nd d) + 2000 * (2 * (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s)) + 1) +
        2) := by
    unfold ppHead; simpa only [Fintype.card_fin] using ht₃
  refine ⟨(List.range (nd d)).map (fun x => pos (3 * x)), bigN (map h.wf) (fun i => cp d i),
    (List.range (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s))).map
      (fun i => c₃.nmem (frB d + 4 + 6 * (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s)) + i)),
    by simp, ?_, ?_⟩
  · -- the run
    have ex : Exec (inp d) W (mfFull sepL stepP) initConfig c₄ (t₁ + (t₂ + (t₃ + t₄))) :=
      .seq e₁ (.seq e₂ (.seq e₃ e₄))
    obtain ⟨k, hk, rest⟩ := runsWithin_of_exec_output ex (by rw [o4, o3, o2, o1])
    exact ⟨k, by omega, rest⟩
  · -- the maximum flow
    convert hmax using 1
    · funext x; rfl
    funext x
    have hx : x ∈ nlDarts (map h.wf) := by rw [nlDarts_map h.wf hl]; exact mem_univ _
    rw [nlRunX_eq h.plane hrot hface _ _ _ _ _ _ _ hpiece x hx]
    obtain ⟨hpN, hpe⟩ := enS_pos_enc hrot hsort (Sum.inl (old ⟨x, hx⟩))
    have henc : enc (map h.wf) (Sum.inl (old ⟨x, hx⟩)) = 3 * x.val := rfl
    rw [henc] at hpN hpe
    have hp : ((List.range (nd d)).map (fun x => pos (3 * x))).getD x 0 = pos (3 * x) := by
      simp [x.2]
    have hq : ((List.range (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s))).map
        (fun i => c₃.nmem (frB d + 4 + 6 * (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s)) +
          i))).getD (pos (3 * x)) 0 =
        c₃.nmem (frB d + 4 + 6 * (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s)) +
          pos (3 * x)) := by
      simp [hpN]
    rw [hp, hq]
    have hlt := hpN
    have hv := hf (pos (3 * x)) hlt
    rw [fext_mem _ (hL.en_mem _ hlt)] at hv
    have e : en' (pos (3 * x)) = Sum.inl (old ⟨x, hx⟩) := by rw [hen _ hlt, hpe]
    rw [hfr, hv, add_sub_cancel_left]
    exact congrArg _ (Subtype.ext e)

end Pp

end BKMNW

end PlanarFlow
