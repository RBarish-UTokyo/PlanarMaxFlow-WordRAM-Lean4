module

public import PlanarFlow.BKMNW.PqPrB
public import PlanarFlow.BKMNW.PpPipe

/-!
# The maximum-flow pipeline against `MfMainSpecS` (scaled chain, zero area)

`mf_pipeline` (`PpPipe.lean`) rests on `MfMainSpec` (the conclusion of `mfMain_cMachXGE`, costs
`cMach`, no zero memory). Here the pipeline is re-proved from **`MfMainSpecS`** (`PqSpec.lean`: a
hypothesis only on the separator and node-step programs, against `mfMain_cMachSGEPX`), whose
in-place subroutine calls need the memory `≤ Wz` zero with `Wz ≥ WZ N Z`. The preprocessing runs
at the base `B = zB a p d = a (7 n + zb d + 1) ^ p + 1` (`PqZ.lean`, `PqPP.lean`), so the memory
below `B` stays zero, and `Wz = B - 1` works whenever `WZ N Z ≤ a (N + Z + 1) ^ p`.

* `nlRunNX_eq`: the algorithm on a dart that is not a loop is the root call's flow `arunLN`;
* `noEmit_mfProgS`;
* **`mfFullS a p sepL sepX fixP c2sP s2cP retP frmP = zP a p ; ppAB ; ppBB ; mfProgS … ; prBB a p`**;
* `ppHeadS C C₀ n` (the headline with `machKS C`), `PipeRoomS R a p d W` (the word bound);
* **`mf_pipelineS`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv Feas
  NegSSSP.Driver CombMap Orbit PlanarSeparator.StDart

set_option synthInstance.maxHeartbeats 400000 in
/-- **The algorithm with subroutines depending on the call, on a dart that is not a loop, is the
flow of the root call** (`nlRunX_eq` for `nlRunNX`). -/
theorem nlRunNX_eq {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) (e : PVert M → TDart M) (he : ∀ w, (tnlMap M).tail (e w) = w)
    (u : D → ℤ) (S T : Finset V) (τ : ADec (lpreMapX M e he)) (NF : NFam (lpreMapX M e he))
    (hτ : τ.piece = univ) (x : D) (hx : x ∈ nlDarts M) :
    nlRunNX M e he u S T τ NF x =
      arunLN (lpreMapX M e he) NF (preCap (hrot := nlMap_rotTrans) (fun y => u y.1) (nlTerm M S)
        (nlTerm M T)) (preTerm (hrot := nlMap_rotTrans) (nlTerm M S))
        (preTerm (hrot := nlMap_rotTrans) (nlTerm M T)) τ [] (rotPerm (lpreMapX M e he))
        ⟨.inl (old ⟨x, hx⟩), by rw [hτ, pdarts_univ_nil]; exact mem_univ _⟩ := by
  have hne : Nonempty (SDart (nlDarts M)) := ⟨⟨x, hx⟩⟩
  have hP := nlMap_isPlane hM hrot hface hx
  have hT := triMap_isPlane hP nlMap_rotTrans nlMap_faceTrans
  have hL : (lpreMapX M e he).IsPlane := CombMap.pendant_isPlane he hT
  have hLr : (lpreMapX M e he).RotTrans :=
    CombMap.pendant_rotTrans he (triMap_rotTrans nlMap_rotTrans)
  have hLf : (lpreMapX M e he).FaceTrans :=
    CombMap.pendant_faceTrans he (triMap_faceTrans nlMap_rotTrans)
  have hNe : Nonempty (TDart M ⊕ (PVert M × Bool)) := ⟨.inl (old ⟨x, hx⟩)⟩
  have hroot : PieceInv (lpreMapX M e he) τ.piece [] (rotPerm (lpreMapX M e he)) := by
    rw [hτ]; exact pieceInv_root hL hLr hLf hNe
  have hcond : PieceInv (lpreMapX M e he) τ.piece [] (rotPerm (lpreMapX M e he)) ∧
      (∀ d, d ∈ τ.piece) ∧ Nonempty (TDart M ⊕ (PVert M × Bool)) :=
    ⟨hroot, fun d => by rw [hτ]; exact mem_univ _, hNe⟩
  unfold nlRunNX nlExt
  rw [ppDiteT hx]
  unfold runLN
  rw [ppDiteT hcond]
  beta_reduce
  unfold Emb.ext
  have hm : (Sum.inl (old ⟨x, hx⟩) : TDart M ⊕ (PVert M × Bool)) ∈
      pdarts (lpreMapX M e he) τ.piece [] := by rw [hτ, pdarts_univ_nil]; exact mem_univ _
  exact (Emb.inj (rootEmb hcond.1 ⟨Classical.choice hcond.2.2, mem_pdarts_nil hcond.2.1 _⟩)).extend_apply _ _ (⟨_, hm⟩ : SDart (pdarts (lpreMapX M e he) τ.piece []))

/-- **The max-flow program with the node-step programs prints nothing** when its seven
subroutine programs print nothing. -/
theorem noEmit_mfProgS {sepL sepX fixP c2sP s2cP retP frmP : Stmt}
    (h1 : Stmt.noEmit sepL = true) (h2 : Stmt.noEmit sepX = true) (h3 : Stmt.noEmit fixP = true)
    (h4 : Stmt.noEmit c2sP = true) (h5 : Stmt.noEmit s2cP = true) (h6 : Stmt.noEmit retP = true)
    (h7 : Stmt.noEmit frmP = true) :
    Stmt.noEmit (mfProgS sepL sepX fixP c2sP s2cP retP frmP) = true := by
  have a1 : Stmt.noEmit rfProg = true := by decide +kernel
  have a2 : Stmt.noEmit rxProg = true := by decide +kernel
  have a3 : Stmt.noEmit mtProg = true := by decide +kernel
  have a4 : Stmt.noEmit mlProg = true := by decide +kernel
  have a5 : Stmt.noEmit spPre = true := by decide +kernel
  have a6 : Stmt.noEmit spSet = true := by decide +kernel
  have b1 : Stmt.noEmit spFlags = true := by decide +kernel
  have a7 : Stmt.noEmit spChL = true := by decide +kernel
  have b2 : Stmt.noEmit spGlR = true := by decide +kernel
  have b3 : Stmt.noEmit sfChild = true := by decide +kernel
  have b4 : Stmt.noEmit spRec = true := by decide +kernel
  have a8 : Stmt.noEmit (sepD0 100000) = true := by decide +kernel
  have a9 : Stmt.noEmit sepSm = true := by decide +kernel
  have a10 : Stmt.noEmit njProg = true := by decide +kernel
  have a11 : Stmt.noEmit peekB = true := by decide +kernel
  have a12 : Stmt.noEmit popB = true := by decide +kernel
  have a13 : Stmt.noEmit pushB = true := by decide +kernel
  have a14 : Stmt.noEmit coB = true := by decide +kernel
  have a15 : Stmt.noEmit coPost = true := by decide +kernel
  have c1 : Stmt.noEmit sgA = true := by decide +kernel
  have c2 : Stmt.noEmit sgB = true := by decide +kernel
  have c3 : Stmt.noEmit npSgK = true := by decide +kernel
  have c4 : Stmt.noEmit sgC = true := by decide +kernel
  have c5 : Stmt.noEmit sgM = true := by decide +kernel
  have c6 : Stmt.noEmit sgD = true := by decide +kernel
  have c7 : Stmt.noEmit rsP = true := by decide +kernel
  have c8 : Stmt.noEmit cntP = true := by decide +kernel
  have c9 : Stmt.noEmit stA = true := by decide +kernel
  have c10 : Stmt.noEmit stH = true := by decide +kernel
  have c11 : Stmt.noEmit stI = true := by decide +kernel
  have c12 : Stmt.noEmit stJ = true := by decide +kernel
  simp only [mfProgS, Stmt.noEmit, driver, body, splitSX, spFront, sepPX, nodeSF, stepX, segP,
    stepPO, segBodyP, holeBodyP, a1, a2, a3, a4, a5, a6, b1, a7, b2, b3, b4, a8, a9, a10, a11,
    a12, a13, a14, a15, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, h1, h2, h3, h4, h5, h6,
    h7, Bool.and_self]

/-- **The whole maximum-flow program, scaled chain**: the base, the preprocessing at the base, the
max-flow program with the node-step programs, the print. -/
def mfFullS (a p : ℕ) (sepL sepX fixP c2sP s2cP retP frmP : Stmt) : Stmt :=
  .seq (zP a p) (.seq ppAB (.seq ppBB (.seq (mfProgS sepL sepX fixP c2sP s2cP retP frmP)
    (prBB a p))))

/-- The headline cost of the max-flow program with the scaled costs on `n` darts
(`O(n log³ n)`, constant `machKS C = 10¹⁵ · machK C`). -/
def ppHeadS (C C₀ n : ℕ) : ℕ :=
  (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machKS C * n * lg n ^ 3 +
    (100000 + 11) ^ 2 * 28 * C₀ * n * lg n

/-- **The word bound of the pipeline at the base `zB a p d`**: `W ≥ 100000`, the capacities,
the power of the base, the preprocessing (counting sort `(2(K+n)+1) 7n`) above the base, and the
room of the max-flow program (`R (7n) (zb d)` per call) above the base, and `(7n + 2)(zb + 1)`
(the words of the push-back programs, `(N + 2)(Z + 1) ≤ W`). -/
def PipeRoomS (R : ℕ → ℕ → ℕ) (a p : ℕ) (d : List ℕ) (W : ℕ) : Prop :=
  100000 ≤ W ∧ 2 * zb d + 7 * nd d + 20 ≤ W ∧ (7 * nd d + 2) * (zb d + 1) ≤ W ∧
    (7 * nd d + zb d + 1) ^ p ≤ W ∧
    10 * zB a p d + 300 * nd d + 4 * nv d + (2 * (nv d + nd d) + 1) * (7 * nd d) + 300 ≤ W ∧
    zB a p d + 240 * nd d + 2 * nv d + 300 +
      (14 * nd d + 1) * (770 * nd d + 80 + R (7 * nd d) (zb d)) ≤ W

set_option maxHeartbeats 4000000 in
/-- **The run of the maximum-flow program against `MfMainSpecS`**, from any configuration with zero memory
(see `mf_pipelineS`).: from the encoding `d` of a plane map without
loops, with transitive rotations and faces and disjoint sources and sinks, the program
`mfFullS a p sepL sepX fixP c2sP s2cP retP frmP` runs within
`ppHeadS C C₀ n + 31200 n + 50 K + 2 p + 3200` steps (`n = nd d`, `K = nv d`) and prints
`p ++ Z :: q` with `|p| = n`; `x ↦ q[p[x]] - Z` is a maximum flow. Hypotheses: `MfMainSpecS`
(the separator and node-step programs), `1 ≤ C`, the seven programs print nothing, `R` monotone,
the zero area asked by the subroutines at most `a (N + Z + 1) ^ p`, the word bound
`PipeRoomS R a p d W`. -/
theorem mf_execS {sepL sepX fixP c2sP s2cP retP frmP : Stmt} {C C₀ : ℕ}
    {R WZ : ℕ → ℕ → ℕ} {a p : ℕ}
    (hspec : MfMainSpecS sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ) (hC : 1 ≤ C)
    (hE1 : Stmt.noEmit sepL = true) (hE2 : Stmt.noEmit sepX = true)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true) (hE6 : Stmt.noEmit retP = true)
    (hE7 : Stmt.noEmit frmP = true)
    (hRm : ∀ N N' Z Z', N ≤ N' → Z ≤ Z' → R N Z ≤ R N' Z')
    (hWZ : ∀ N Z, WZ N Z ≤ a * (N + Z + 1) ^ p)
    {d : List ℕ} {W : ℕ} (h : MEnc d W) (hn : 0 < nd d) (hroom : PipeRoomS R a p d W)
    (c : Config) (hc : WordsBounded W c) (hm : ∀ x, c.nmem x = 0) :
    ∃ (pp : List ℕ) (Z : ℕ) (q : List ℕ), pp.length = nd d ∧
      (∃ c' t, Exec (inp d) W (mfFullS a p sepL sepX fixP c2sP s2cP retP frmP) c c' t ∧
        t + 1 ≤ ppHeadS C C₀ (nd d) + 31200 * nd d + 50 * nv d + 2 * p + 3200 ∧
        c'.output = c.output ++ (pp ++ Z :: q)) ∧
      IsMax (map h.wf) (ucap d) (srcF d) (snkF d)
        (fun x => ((q.getD (pp.getD x 0) 0 : ℕ) : ℤ) - Z) := by
  obtain ⟨hW1, hW2, hW6, hW3, hW4, hW5⟩ := hroom
  have wf := h.wf
  have hl := h.loopless
  have hwd := h.word_le
  have hrot : (map h.wf).RotTrans := map_rotTrans h.wf h.rotT
  have hface : (map h.wf).FaceTrans := map_faceTrans h.wf h.faceT
  have hZs := bigN_eq_sum h.wf hl
  have hZb : bigN (map h.wf) (fun i => cp d i) = zb d := hZs
  have hbig : ∑ x ∈ range (nd d), fl (tl d (rv d x) ≠ tl d x) * cp d x ≤ W := by
    rw [← bigN_map h.wf hl, hZb]; omega
  -- the base
  obtain ⟨c₀, t₀, e₀, ht₀, r30, m0, -, -, o0⟩ := zP_exec (P := inp d) (d := d) rfl hwd a p
    c hc (by omega) (by omega) (by omega) hW3
  set B := zB a p d with hB
  have hB1 : 1 ≤ B := by rw [hB]; unfold zB; omega
  -- the preprocessing
  obtain ⟨c₁, t₁, e₁, ht₁, hS, mA, r00, r03, r04, r05, r06, r08, r09, r30', r31, -, -, o1⟩ :=
    ppA_execB (P := inp d) (d := d) rfl h.wf hl hrot hwd c₀ e₀.wb_right r30 hbig (by nlinarith)
  obtain ⟨c₂, t₂, e₂, ht₂, pos, hsort, a1, a2, a3, a4, a5, a6, w0, w1, w2, w3, w4, w5, w6, w7,
    m1, m2, o2, mB, hN7⟩ := ppB_execB (P := inp d) (d := d) rfl hwd h.wf hl hrot hn c₁
      e₁.wb_right hS r00 r03 r04 r05 r06 r08 r09 r30' r31 (by nlinarith)
  have hz : MemZ (B - 1) c₂ := fun x hx => by
    rw [mB x (by omega), mA x (by omega), m0]; exact hm x
  have hx0 : (⟨0, hn⟩ : Fin (nd d)) ∈ nlDarts (map h.wf) := by
    rw [nlDarts_map h.wf hl]; exact mem_univ _
  have : Nonempty (TDart (map h.wf) ⊕ (PVert (map h.wf) × Bool)) := ⟨.inl (old ⟨_, hx0⟩)⟩
  obtain ⟨hcard, hsurj, hgid, hts, hrev, hsig, hcap, hkr, hkey, hrt⟩ :=
    sortConv (M := map h.wf) hrot (fun i => cp d i) (srcF d) (snkF d) hsort
  have hne : (nlDarts (map h.wf)).Nonempty := ⟨_, hx0⟩
  have hu : ∀ x : Fin (nd d), (0 : ℤ) ≤ (cp d x : ℤ) := fun _ => Nat.cast_nonneg _
  have Hs := @hspec _ _ _ _ _ _ _ _ _ (map h.wf) h.plane hrot hface (pe (map h.wf))
    (pe_tail (map h.wf) hrot) (fun i => (cp d i : ℤ)) hu (srcF d) (snkF d)
    (srcF_snkF_disjoint h) hne _ (enS (M := map h.wf) (srtD h.wf))
    (enS (M := map h.wf) (srtD h.wf) 0) _ _ hcard hsurj hgid
    (νX_injective (M := map h.wf) (hrot := hrot) (vn := fun v => v.val) (K := nv d)
      Fin.val_injective (fun v => v.2)) (qpar_νX (map h.wf) (fun v => v.val) (nv d)) hts
  have G : MfMainGoalS (map h.wf) (pe (map h.wf)) (pe_tail (map h.wf) hrot)
      (fun i => (cp d i : ℤ)) (srcF d) (snkF d) (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s))
      (enS (M := map h.wf) (srtD h.wf)) (enS (M := map h.wf) (srtD h.wf) 0) (gidS pos)
      (νX (map h.wf) (fun v => v.val) (nv d)) sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ :=
    mfMainGoalS_of_sub h.plane hrot hface (pe (map h.wf)) (pe_tail (map h.wf) hrot)
    (u := fun i => (cp d i : ℤ)) hu
    (srcF_snkF_disjoint h) hx0 _ _ hcard hsurj hgid
    (νX_injective (M := map h.wf) (hrot := hrot) (vn := fun v => v.val) (K := nv d)
      Fin.val_injective (fun v => v.2)) hC Hs
  unfold MfMainGoalS at G
  set N := ∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s) with hNdef
  have hZ2 : 2 * bigN (map h.wf) (fun i => cp d i) ≤ W := by rw [hZb]; omega
  have hWZ' : WZ N (bigN (map h.wf) (fun i => cp d i)) ≤ B - 1 := by
    refine (hWZ _ _).trans ?_
    rw [hB, hZb]; unfold zB
    have : (N + zb d + 1) ^ p ≤ (7 * nd d + zb d + 1) ^ p := Nat.pow_le_pow_left (by omega) p
    have := Nat.mul_le_mul_left a this
    omega
  have hNZ : (N + 2) * (bigN (map h.wf) (fun i => cp d i) + 1) ≤ W := by
    rw [hZb]; exact (Nat.mul_le_mul_right _ (by omega)).trans hW6
  have hRN : R N (bigN (map h.wf) (fun i => cp d i)) ≤ R (7 * nd d) (zb d) :=
    hRm _ _ _ _ hN7 (by rw [hZb])
  have hmul : (2 * N + 1) * (110 * N + 80 + R N (bigN (map h.wf) (fun i => cp d i))) ≤
      (14 * nd d + 1) * (770 * nd d + 80 + R (7 * nd d) (zb d)) :=
    Nat.mul_le_mul (by omega) (by omega)
  obtain ⟨hpiece, NF, c₃, t₃, e₃, ht₃, -, hout, hmax⟩ := G (I := inp d) (Wz := B - 1) hW1 hZ2 hNZ hWZ'
    (by omega) (by omega) c₂ e₂.wb_right hz w0 w1 w2 w3 w4 w5 w6 w7 m1 m2
    (fun i hi => by rw [a1 i hi]; exact hrev i hi)
    (fun i hi => by rw [a2 i hi]; exact hsig i hi)
    (fun i hi => by rw [a3 i hi]; exact ⟨hcap i hi, capS_le_bigN h.wf hl _⟩)
    (fun i hi => by rw [a4 i hi]; exact hkr i hi)
    (fun i hi => by rw [a5 i hi]; exact hkey i hi)
    (fun i hi hc => by rw [a6 i hi]; exact hrt i hi hc)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have o3 : c₃.output = c₂.output := Exec.output_eq
    (s := mfProgS sepL sepX fixP c2sP s2cP retP frmP) e₃
    (noEmit_mfProgS hE1 hE2 hE3 hE4 hE5 hE6 hE7)
  obtain ⟨m, en', hL, -, hf⟩ := hout
  obtain ⟨hmN, hen⟩ := lay_en_eq (M := map h.wf) hrot hsort (x := (_, [], _)) hpiece rfl hL
  subst hmN
  have hfr : B + frB d = B + 84 * nd d + 2 * (nv d + nd d) + 1 + 42 * nd d + 2 + 5 := by
    unfold frB; ring
  have hN : c₃.nmem (B + frB d) = N := by rw [hfr, hL.hm]
  have hZ : c₃.nmem (B + frB d + 3) = bigN (map h.wf) (fun i => cp d i) := by
    rw [hfr, hL.hz]
  obtain ⟨c₄, t₄, e₄, ht₄, o4⟩ := prBB_exec (P := inp d) (d := d) rfl hwd a p c₃ e₃.wb_right hN
    hZ (by omega) hW3 (by unfold frB; omega)
  have ht₃' : t₃ ≤ 95 * N + 200 + (ppHeadS C C₀ (nd d) + 2000 * (2 * N + 1) + 2) := by
    unfold ppHeadS; simpa only [Fintype.card_fin] using ht₃
  refine ⟨(List.range (nd d)).map (fun x => pos (3 * x)), bigN (map h.wf) (fun i => cp d i),
    (List.range N).map (fun i => c₃.nmem (B + frB d + 4 + 6 * N + i)), by simp, ?_, ?_⟩
  · -- the run
    refine ⟨c₄, t₀ + (t₁ + (t₂ + (t₃ + t₄))), .seq e₀ (.seq e₁ (.seq e₂ (.seq e₃ e₄))),
      by omega, ?_⟩
    rw [o4, o3, o2, o1, o0, List.append_assoc]
  · -- the maximum flow
    convert hmax using 1
    · funext x; rfl
    funext x
    have hx : x ∈ nlDarts (map h.wf) := by rw [nlDarts_map h.wf hl]; exact mem_univ _
    rw [nlRunNX_eq h.plane hrot hface _ _ _ _ _ _ _ hpiece x hx]
    obtain ⟨hpN, hpe⟩ := enS_pos_enc hrot hsort (Sum.inl (old ⟨x, hx⟩))
    have henc : enc (map h.wf) (Sum.inl (old ⟨x, hx⟩)) = 3 * x.val := rfl
    rw [henc] at hpN hpe
    have hp : ((List.range (nd d)).map (fun x => pos (3 * x))).getD x 0 = pos (3 * x) := by
      simp [x.2]
    have hq : ((List.range N).map (fun i => c₃.nmem (B + frB d + 4 + 6 * N + i))).getD
        (pos (3 * x)) 0 = c₃.nmem (B + frB d + 4 + 6 * N + pos (3 * x)) := by
      simp [hpN]
    rw [hp, hq]
    have hlt := hpN
    have hv := hf (pos (3 * x)) hlt
    rw [fext_mem _ (hL.en_mem _ hlt)] at hv
    have e : en' (pos (3 * x)) = Sum.inl (old ⟨x, hx⟩) := by rw [hen _ hlt, hpe]
    rw [hfr, hv, add_sub_cancel_left]
    exact congrArg _ (Subtype.ext e)

/-- **The maximum-flow pipeline against `MfMainSpecS`**: from the encoding `d` of a plane map without
loops, with transitive rotations and faces and disjoint sources and sinks, the program
`mfFullS a p sepL sepX fixP c2sP s2cP retP frmP` runs within
`ppHeadS C C₀ n + 31200 n + 50 K + 2 p + 3200` steps (`n = nd d`, `K = nv d`) and prints
`pp ++ Z :: q` with `|pp| = n`; `x ↦ q[pp[x]] - Z` is a maximum flow. Hypotheses: `MfMainSpecS`
(the separator and node-step programs), `1 ≤ C`, the seven programs print nothing, `R` monotone,
the zero area asked by the subroutines at most `a (N + Z + 1) ^ p`, the word bound
`PipeRoomS R a p d W`. -/
theorem mf_pipelineS {sepL sepX fixP c2sP s2cP retP frmP : Stmt} {C C₀ : ℕ}
    {R WZ : ℕ → ℕ → ℕ} {a p : ℕ}
    (hspec : MfMainSpecS sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ) (hC : 1 ≤ C)
    (hE1 : Stmt.noEmit sepL = true) (hE2 : Stmt.noEmit sepX = true)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true) (hE6 : Stmt.noEmit retP = true)
    (hE7 : Stmt.noEmit frmP = true)
    (hRm : ∀ N N' Z Z', N ≤ N' → Z ≤ Z' → R N Z ≤ R N' Z')
    (hWZ : ∀ N Z, WZ N Z ≤ a * (N + Z + 1) ^ p)
    {d : List ℕ} {W : ℕ} (h : MEnc d W) (hn : 0 < nd d) (hroom : PipeRoomS R a p d W) :
    ∃ (pp : List ℕ) (Z : ℕ) (q : List ℕ), pp.length = nd d ∧
      RunsWithin (compile (mfFullS a p sepL sepX fixP c2sP s2cP retP frmP) 0 ++ [Instr.halt])
        (inp d) W (ppHeadS C C₀ (nd d) + 31200 * nd d + 50 * nv d + 2 * p + 3200) (pp ++ Z :: q) ∧
      IsMax (map h.wf) (ucap d) (srcF d) (snkF d)
        (fun x => ((q.getD (pp.getD x 0) 0 : ℕ) : ℤ) - Z) := by
  obtain ⟨pp, Z, q, hl, ⟨c', t, ex, ht, ho⟩, hmax⟩ := mf_execS hspec hC hE1 hE2 hE3 hE4 hE5 hE6
    hE7 hRm hWZ h hn hroom initConfig (wordsBounded_initConfig W) (fun _ => rfl)
  obtain ⟨k, hk, rest⟩ := runsWithin_of_exec_output (out := pp ++ Z :: q) ex (by rw [ho]; rfl)
  exact ⟨pp, Z, q, hl, ⟨k, by omega, rest⟩, hmax⟩

end Pp

end BKMNW

end PlanarFlow
