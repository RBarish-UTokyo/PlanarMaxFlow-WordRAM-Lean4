module

public import PlanarFlow.BKMNW.ThSpecS
public import PlanarFlow.BKMNW.PrFinal

/-!
# The maximum-flow pipeline and theorem against `MfMainSpecS'`

`PqPipe.lean`, `PrPipe.lean`, `PrTop.lean`, `PrFinal.lean` restated for the program `mfProgS'`
(the parts with their start vertices, `segP' sepX`) and the hypothesis `MfMainSpecS'`
(the proofs are the originals with `mfMainGoalS_of_sub'`):

* `noEmit_mfProgS'`, `mfFullS'`, **`mf_execS'`**, **`mf_pipelineS'`** (`MfMainSpecS'`, `1 ≤ C`,
  the seven programs print nothing, `R` monotone, `WZ N Z ≤ a (N + Z + 1)^p`, `MEnc d W`,
  `0 < nd d`, `PipeRoomS R a p d W` ⟹ `RunsWithin (compile (mfFullS' …) 0 ++ [halt]) (inp d) W
  (ppHeadS C C₀ n + 31200 n + 50 K + 2p + 3200) (pp ++ Z :: q)` and a maximum flow);
* `mfFullL'`, `mf_execL'`, `mfTopL'`, **`mf_pipelineTL'`** (every input size, loops allowed);
* **`maxFlowMachine_of_spec'`**: `MfMainSpecS' sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ`, the
  seven programs print nothing, `R` monotone with `R N Z ≤ r (N + Z + 1)^q`,
  `WZ N Z ≤ a (N + Z + 1)^p`, `1 ≤ C` ⟹ **`MaxFlowMachine'`** (time `cMF C C₀ p · (n + K + 1) ·
  (⌊log₂ n⌋ + 1)³`).
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

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs MfDrv Feas NegSSSP.Driver
  Orbit PlanarSeparator.StDart

/-- **The max-flow program with the node-step programs prints nothing** when its seven
subroutine programs print nothing. -/
theorem noEmit_mfProgS' {sepL sepX fixP c2sP s2cP retP frmP : Stmt}
    (h1 : Stmt.noEmit sepL = true) (h2 : Stmt.noEmit sepX = true) (h3 : Stmt.noEmit fixP = true)
    (h4 : Stmt.noEmit c2sP = true) (h5 : Stmt.noEmit s2cP = true) (h6 : Stmt.noEmit retP = true)
    (h7 : Stmt.noEmit frmP = true) :
    Stmt.noEmit (mfProgS' sepL sepX fixP c2sP s2cP retP frmP) = true := by
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
  have c13 : Stmt.noEmit sgC3 = true := by decide +kernel
  simp only [mfProgS', Stmt.noEmit, driver, body, splitSX, spFront, sepPX, nodeSF, stepX, segP',
    stepPO, segBodyP, holeBodyP, a1, a2, a3, a4, a5, a6, b1, a7, b2, b3, b4, a8, a9, a10, a11,
    a12, a13, a14, a15, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, h1, h2, h3, h4, h5, h6,
    h7, Bool.and_self]

/-- **The whole maximum-flow program, scaled chain**: the base, the preprocessing at the base, the
max-flow program with the node-step programs, the print. -/
def mfFullS' (a p : ℕ) (sepL sepX fixP c2sP s2cP retP frmP : Stmt) : Stmt :=
  .seq (zP a p) (.seq ppAB (.seq ppBB (.seq (mfProgS' sepL sepX fixP c2sP s2cP retP frmP)
    (prBB a p))))


set_option maxHeartbeats 4000000 in
/-- **The run of the maximum-flow program against `MfMainSpecS'`**, from any configuration with zero memory
(see `mf_pipelineS'`).: from the encoding `d` of a plane map without
loops, with transitive rotations and faces and disjoint sources and sinks, the program
`mfFullS' a p sepL sepX fixP c2sP s2cP retP frmP` runs within
`ppHeadS C C₀ n + 31200 n + 50 K + 2 p + 3200` steps (`n = nd d`, `K = nv d`) and prints
`p ++ Z :: q` with `|p| = n`; `x ↦ q[p[x]] - Z` is a maximum flow. Hypotheses: `MfMainSpecS'`
(the separator and node-step programs), `1 ≤ C`, the seven programs print nothing, `R` monotone,
the zero area asked by the subroutines at most `a (N + Z + 1) ^ p`, the word bound
`PipeRoomS R a p d W`. -/
theorem mf_execS' {sepL sepX fixP c2sP s2cP retP frmP : Stmt} {C C₀ : ℕ}
    {R WZ : ℕ → ℕ → ℕ} {a p : ℕ}
    (hspec : MfMainSpecS' sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ) (hC : 1 ≤ C)
    (hE1 : Stmt.noEmit sepL = true) (hE2 : Stmt.noEmit sepX = true)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true) (hE6 : Stmt.noEmit retP = true)
    (hE7 : Stmt.noEmit frmP = true)
    (hRm : ∀ N N' Z Z', N ≤ N' → Z ≤ Z' → R N Z ≤ R N' Z')
    (hWZ : ∀ N Z, WZ N Z ≤ a * (N + Z + 1) ^ p)
    {d : List ℕ} {W : ℕ} (h : MEnc d W) (hn : 0 < nd d) (hroom : PipeRoomS R a p d W)
    (c : Config) (hc : WordsBounded W c) (hm : ∀ x, c.nmem x = 0) :
    ∃ (pp : List ℕ) (Z : ℕ) (q : List ℕ), pp.length = nd d ∧
      (∃ c' t, Exec (inp d) W (mfFullS' a p sepL sepX fixP c2sP s2cP retP frmP) c c' t ∧
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
  have G : MfMainGoalS' (map h.wf) (pe (map h.wf)) (pe_tail (map h.wf) hrot)
      (fun i => (cp d i : ℤ)) (srcF d) (snkF d) (∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s))
      (enS (M := map h.wf) (srtD h.wf)) (enS (M := map h.wf) (srtD h.wf) 0) (gidS pos)
      (νX (map h.wf) (fun v => v.val) (nv d)) sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ :=
    mfMainGoalS_of_sub' h.plane hrot hface (pe (map h.wf)) (pe_tail (map h.wf) hrot)
    (u := fun i => (cp d i : ℤ)) hu
    (srcF_snkF_disjoint h) hx0 _ _ hcard hsurj hgid
    (νX_injective (M := map h.wf) (hrot := hrot) (vn := fun v => v.val) (K := nv d)
      Fin.val_injective (fun v => v.2)) hC Hs
  unfold MfMainGoalS' at G
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
    (s := mfProgS' sepL sepX fixP c2sP s2cP retP frmP) e₃
    (noEmit_mfProgS' hE1 hE2 hE3 hE4 hE5 hE6 hE7)
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

/-- **The maximum-flow pipeline against `MfMainSpecS'`**: from the encoding `d` of a plane map without
loops, with transitive rotations and faces and disjoint sources and sinks, the program
`mfFullS' a p sepL sepX fixP c2sP s2cP retP frmP` runs within
`ppHeadS C C₀ n + 31200 n + 50 K + 2 p + 3200` steps (`n = nd d`, `K = nv d`) and prints
`pp ++ Z :: q` with `|pp| = n`; `x ↦ q[pp[x]] - Z` is a maximum flow. Hypotheses: `MfMainSpecS'`
(the separator and node-step programs), `1 ≤ C`, the seven programs print nothing, `R` monotone,
the zero area asked by the subroutines at most `a (N + Z + 1) ^ p`, the word bound
`PipeRoomS R a p d W`. -/
theorem mf_pipelineS' {sepL sepX fixP c2sP s2cP retP frmP : Stmt} {C C₀ : ℕ}
    {R WZ : ℕ → ℕ → ℕ} {a p : ℕ}
    (hspec : MfMainSpecS' sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ) (hC : 1 ≤ C)
    (hE1 : Stmt.noEmit sepL = true) (hE2 : Stmt.noEmit sepX = true)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true) (hE6 : Stmt.noEmit retP = true)
    (hE7 : Stmt.noEmit frmP = true)
    (hRm : ∀ N N' Z Z', N ≤ N' → Z ≤ Z' → R N Z ≤ R N' Z')
    (hWZ : ∀ N Z, WZ N Z ≤ a * (N + Z + 1) ^ p)
    {d : List ℕ} {W : ℕ} (h : MEnc d W) (hn : 0 < nd d) (hroom : PipeRoomS R a p d W) :
    ∃ (pp : List ℕ) (Z : ℕ) (q : List ℕ), pp.length = nd d ∧
      RunsWithin (compile (mfFullS' a p sepL sepX fixP c2sP s2cP retP frmP) 0 ++ [Instr.halt])
        (inp d) W (ppHeadS C C₀ (nd d) + 31200 * nd d + 50 * nv d + 2 * p + 3200) (pp ++ Z :: q) ∧
      IsMax (map h.wf) (ucap d) (srcF d) (snkF d)
        (fun x => ((q.getD (pp.getD x 0) 0 : ℕ) : ℤ) - Z) := by
  obtain ⟨pp, Z, q, hl, ⟨c', t, ex, ht, ho⟩, hmax⟩ := mf_execS' hspec hC hE1 hE2 hE3 hE4 hE5 hE6
    hE7 hRm hWZ h hn hroom initConfig (wordsBounded_initConfig W) (fun _ => rfl)
  obtain ⟨k, hk, rest⟩ := runsWithin_of_exec_output (out := pp ++ Z :: q) ex (by rw [ho]; rfl)
  exact ⟨pp, Z, q, hl, ⟨k, by omega, rest⟩, hmax⟩


/-- **The whole maximum-flow program, loops allowed.** -/
def mfFullL' (a p : ℕ) (sepL sepX fixP c2sP s2cP retP frmP : Stmt) : Stmt :=
  .seq (preL a p) (.ifLtN 8903 6700 (.seq (mfProgS' sepL sepX fixP c2sP s2cP retP frmP) (prBBL a p))
      (block [.constN 8902 0, .outN 8902]))

set_option maxHeartbeats 4000000 in
/-- **The run of the maximum-flow program, loops allowed**, from any configuration with zero memory
(`mf_execS'` for `MEncL`). -/
theorem mf_execL' {sepL sepX fixP c2sP s2cP retP frmP : Stmt} {C C₀ : ℕ}
    {R WZ : ℕ → ℕ → ℕ} {a p : ℕ}
    (hspec : MfMainSpecS' sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ) (hC : 1 ≤ C)
    (hE1 : Stmt.noEmit sepL = true) (hE2 : Stmt.noEmit sepX = true)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true) (hE6 : Stmt.noEmit retP = true)
    (hE7 : Stmt.noEmit frmP = true)
    (hRm : ∀ N N' Z Z', N ≤ N' → Z ≤ Z' → R N Z ≤ R N' Z')
    (hWZ : ∀ N Z, WZ N Z ≤ a * (N + Z + 1) ^ p)
    {d : List ℕ} {W : ℕ} (h : MEncL d W) (hn : 0 < nd d) (hroom : PipeRoomS R a p d W)
    (c : Config) (hc : WordsBounded W c) (hm : ∀ x, c.nmem x = 0) :
    ∃ (pp : List ℕ) (Z : ℕ) (q : List ℕ), pp.length = nd d ∧
      (∃ c' t, Exec (inp d) W (mfFullL' a p sepL sepX fixP c2sP s2cP retP frmP) c c' t ∧
        t + 1 ≤ ppHeadS C C₀ (nd d) + 31200 * nd d + 50 * nv d + 2 * p + 3200 ∧
        c'.output = c.output ++ (pp ++ Z :: q)) ∧
      IsMax (map h.wf) (ucap d) (srcF d) (snkF d)
        (fun x => ((q.getD (pp.getD x 0) 0 : ℕ) : ℤ) - Z) := by
  obtain ⟨hW1, hW2, hW6, hW3, hW4, hW5⟩ := hroom
  have wf := h.wf
  have hwd := h.word_le
  have hrot : (map h.wf).RotTrans := map_rotTrans h.wf h.rotT
  have hface : (map h.wf).FaceTrans := map_faceTrans h.wf h.faceT
  have hZle : bigN (map h.wf) (fun i => cp d i) ≤ zb d := bigN_le_zb h.wf
  set B := zB a p d with hB
  obtain ⟨c₂', t₂, e₂, ht₂, pos, hsort, hinv, a1, a2, a3, a4, a5, a6, w0', w1', w2', w3', w4',
    w5', w6', w7', m1', m2'', v03, o2, hz, hN7⟩ := pre_execL (a := a) (p := p) h hn hW1 hW2 hW3
      hW4 c hc hm
  set N := ∑ s ∈ range (7 * nd d), fl (ValidS (map h.wf) s) with hNdef
  have hpp : ((List.range (nd d)).map (fun x => pos (3 * x))).length = nd d := by simp
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · -- every dart is a loop: the zero flow
    have hnl : ∀ x : Fin (nd d), x ∉ nlDarts (map h.wf) := fun x hx => by
      have hv := valid_of_nl hx
      obtain ⟨i, hi, -⟩ := hsort.all _ hv
      omega
    obtain ⟨c₃, t₃, e₃, ht₃, o3⟩ : ∃ c₃ t₃,
        Exec (inp d) W (block [.constN 8902 0, .outN 8902]) c₂' c₃ t₃ ∧ t₃ = 2 ∧
        c₃.output = c₂'.output ++ [0] := by
      have hw := e₂.wb_right
      exec_block
      all_goals try omega
      refine ⟨rfl, ?_⟩
      config_simp
    have hne : ¬ c₂'.nreg 8903 < c₂'.nreg 6700 := by
      rw [v03, w0']; omega
    refine ⟨(List.range (nd d)).map (fun x => pos (3 * x)), 0, [], hpp,
      ⟨c₃, t₂ + (t₃ + 2),
        .seq e₂ (.ifLtN_false hne e₃), ?_, ?_⟩, ?_⟩
    · unfold ppHeadS; omega
    · rw [o3, o2]; simp
    · have hE : IsEmpty (SDart (nlDarts (map h.wf))) := ⟨fun y => hnl y.1 y.2⟩
      have := isMax_nlExt hrot (u := ucap d) (S := srcF d) (T := snkF d)
        (fun i => Nat.cast_nonneg _) (f := fun _ => 0)
        (isMax_of_isEmpty _ _ _ _)
      convert this using 1
      funext x
      simp [nlExt, hnl x]
  · -- the max-flow program and the print
    obtain ⟨x₀, hx0⟩ := exists_nl_of_valid (hsort.valid 0 hNpos)
    have : Nonempty (TDart (map h.wf) ⊕ (PVert (map h.wf) × Bool)) := ⟨.inl (old ⟨_, hx0⟩)⟩
    obtain ⟨hcard, hsurj, hgid, hts, hrev, hsig, hcap, hkr, hkey, hrt⟩ :=
      sortConv (M := map h.wf) hrot (fun i => cp d i) (srcF d) (snkF d) hsort
    have hne : (nlDarts (map h.wf)).Nonempty := ⟨_, hx0⟩
    have hu : ∀ x : Fin (nd d), (0 : ℤ) ≤ (cp d x : ℤ) := fun _ => Nat.cast_nonneg _
    have Hs := @hspec _ _ _ _ _ _ _ _ _ (map h.wf) h.plane hrot hface (pe (map h.wf))
      (pe_tail (map h.wf) hrot) (fun i => (cp d i : ℤ)) hu (srcF d) (snkF d)
      (srcF_snkF_disjointL h) hne _ (enS (M := map h.wf) (srtD h.wf))
      (enS (M := map h.wf) (srtD h.wf) 0) _ _ hcard hsurj hgid
      (νX_injective (M := map h.wf) (hrot := hrot) (vn := fun v => v.val) (K := nv d)
        Fin.val_injective (fun v => v.2)) (qpar_νX (map h.wf) (fun v => v.val) (nv d)) hts
    have G : MfMainGoalS' (map h.wf) (pe (map h.wf)) (pe_tail (map h.wf) hrot)
        (fun i => (cp d i : ℤ)) (srcF d) (snkF d) N
        (enS (M := map h.wf) (srtD h.wf)) (enS (M := map h.wf) (srtD h.wf) 0) (gidS pos)
        (νX (map h.wf) (fun v => v.val) (nv d)) sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ :=
      mfMainGoalS_of_sub' h.plane hrot hface (pe (map h.wf)) (pe_tail (map h.wf) hrot)
      (u := fun i => (cp d i : ℤ)) hu
      (srcF_snkF_disjointL h) hx0 _ _ hcard hsurj hgid
      (νX_injective (M := map h.wf) (hrot := hrot) (vn := fun v => v.val) (K := nv d)
        Fin.val_injective (fun v => v.2)) hC Hs
    unfold MfMainGoalS' at G
    have hZ2 : 2 * bigN (map h.wf) (fun i => cp d i) ≤ W := by omega
    have hWZ' : WZ N (bigN (map h.wf) (fun i => cp d i)) ≤ B - 1 := by
      refine (hWZ _ _).trans ?_
      rw [hB]; unfold zB
      have : (N + bigN (map h.wf) (fun i => cp d i) + 1) ^ p ≤ (7 * nd d + zb d + 1) ^ p :=
        Nat.pow_le_pow_left (by omega) p
      have := Nat.mul_le_mul_left a this
      omega
    have hNZ : (N + 2) * (bigN (map h.wf) (fun i => cp d i) + 1) ≤ W :=
      (Nat.mul_le_mul (by omega) (by omega)).trans hW6
    have hRN : R N (bigN (map h.wf) (fun i => cp d i)) ≤ R (7 * nd d) (zb d) :=
      hRm _ _ _ _ hN7 hZle
    have hmul : (2 * N + 1) * (110 * N + 80 + R N (bigN (map h.wf) (fun i => cp d i))) ≤
        (14 * nd d + 1) * (770 * nd d + 80 + R (7 * nd d) (zb d)) :=
      Nat.mul_le_mul (by omega) (by omega)
    obtain ⟨hpiece, NF, c₃, t₃, e₃, ht₃, -, hout, hmax⟩ := G (I := inp d) (Wz := B - 1) hW1 hZ2
      hNZ hWZ' (by omega) (by omega) c₂' e₂.wb_right hz w0' w1' w2' w3' w4' w5' w6' w7' m1' m2''
      (fun i hi => by rw [a1 i hi]; exact hrev i hi)
      (fun i hi => by rw [a2 i hi]; exact hsig i hi)
      (fun i hi => by
        rw [a3 i hi]; exact ⟨hcap i hi, capS_le_bigNL h.wf (hsort.valid i hi)⟩)
      (fun i hi => by rw [a4 i hi]; exact hkr i hi)
      (fun i hi => by rw [a5 i hi]; exact hkey i hi)
      (fun i hi hc => by rw [a6 i hi]; exact hrt i hi hc)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have o3 : c₃.output = c₂'.output := Exec.output_eq
      (s := mfProgS' sepL sepX fixP c2sP s2cP retP frmP) e₃
      (noEmit_mfProgS' hE1 hE2 hE3 hE4 hE5 hE6 hE7)
    obtain ⟨m, en', hL, -, hf⟩ := hout
    obtain ⟨hmN, hen⟩ := lay_en_eq (M := map h.wf) hrot hsort (x := (_, [], _)) hpiece rfl hL
    subst hmN
    have hfr : B + frB d = B + 84 * nd d + 2 * (nv d + nd d) + 1 + 42 * nd d + 2 + 5 := by
      unfold frB; ring
    have hN : c₃.nmem (B + frB d) = N := by rw [hfr, hL.hm]
    have hZ : c₃.nmem (B + frB d + 3) = bigN (map h.wf) (fun i => cp d i) := by
      rw [hfr, hL.hz]
    obtain ⟨c₄, t₄, e₄, ht₄, o4⟩ := prBBL_exec (P := inp d) (d := d) rfl hwd a p c₃ e₃.wb_right
      hN hZ hN7 (by omega) hW3 (by unfold frB; omega)
    have ht₃' : t₃ ≤ 95 * N + 200 + (ppHeadS C C₀ (nd d) + 2000 * (2 * N + 1) + 2) := by
      unfold ppHeadS; simpa only [Fintype.card_fin] using ht₃
    have hlt : c₂'.nreg 8903 < c₂'.nreg 6700 := by
      rw [v03, w0']; exact hNpos
    refine ⟨(List.range (nd d)).map (fun x => pos (3 * x)), bigN (map h.wf) (fun i => cp d i),
      (List.range N).map (fun i => c₃.nmem (B + frB d + 4 + 6 * N + i)) ++
        List.replicate (7 * nd d - N) (bigN (map h.wf) (fun i => cp d i)), hpp, ?_, ?_⟩
    · -- the run
      refine ⟨c₄, t₂ + ((t₃ + t₄) + 1), .seq e₂ (.ifLtN_true hlt (.seq e₃ e₄)), by omega, ?_⟩
      rw [o4, o3, o2, List.append_assoc]
    · -- the maximum flow
      refine isMax_of_eq hmax (fun x => ?_)
      by_cases hx : x ∈ nlDarts (map h.wf)
      · rw [nlRunNX_eq h.plane hrot hface _ _ _ _ _ _ _ hpiece x hx]
        obtain ⟨hpN, hpe⟩ := enS_pos_enc hrot hsort (Sum.inl (old ⟨x, hx⟩))
        have henc : enc (map h.wf) (Sum.inl (old ⟨x, hx⟩)) = 3 * x.val := rfl
        rw [henc] at hpN hpe
        have hp : ((List.range (nd d)).map (fun x => pos (3 * x))).getD x 0 = pos (3 * x) := by
          simp [x.2]
        have hq : ((List.range N).map (fun i => c₃.nmem (B + frB d + 4 + 6 * N + i)) ++
            List.replicate (7 * nd d - N) (bigN (map h.wf) (fun i => cp d i))).getD
            (pos (3 * x)) 0 = c₃.nmem (B + frB d + 4 + 6 * N + pos (3 * x)) := by
          rw [List.getD_append _ _ _ _ (by simpa using hpN)]
          simp [hpN]
        rw [hp, hq]
        have hv := hf (pos (3 * x)) hpN
        rw [fext_mem _ (hL.en_mem _ hpN)] at hv
        have e : en' (pos (3 * x)) = Sum.inl (old ⟨x, hx⟩) := by rw [hen _ hpN, hpe]
        rw [hfr, hv, add_sub_cancel_left]
        exact congrArg _ (Subtype.ext e)
      · have h3 : 3 * x.val < 7 * nd d := by have := x.2; omega
        have hvx : ¬ ValidS (map h.wf) (3 * x.val) := by
          rintro (⟨-, h'⟩ | ⟨h', -⟩ | ⟨h', -⟩)
          · rw [show 3 * x.val / 3 = x.val by omega] at h'
            exact hx ((isNl_fin _).1 h')
          · have := x.2; omega
          · have := x.2; omega
        obtain ⟨hp1, hp2⟩ := hinv _ h3 hvx
        have hp : ((List.range (nd d)).map (fun x => pos (3 * x))).getD x 0 = pos (3 * x) := by
          simp [x.2]
        have hq : ((List.range N).map (fun i => c₃.nmem (B + frB d + 4 + 6 * N + i)) ++
            List.replicate (7 * nd d - N) (bigN (map h.wf) (fun i => cp d i))).getD
            (pos (3 * x)) 0 = bigN (map h.wf) (fun i => cp d i) := by
          rw [List.getD_append_right _ _ _ _ (by simpa using hp1)]
          simp only [List.length_map, List.length_range]
          have hlt' : pos (3 * x.val) - N < 7 * nd d - N := by omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hlt']
        rw [hp, hq, sub_self, nlRunNX_loop _ _ _ _ _ _ _ hx]


/-- **The maximum-flow program for every input size, loops allowed.** -/
def mfTopL' (a p : ℕ) (sepL sepX fixP c2sP s2cP retP frmP : Stmt) : Stmt :=
  .seq (block [.constN 8900 0, .constN 8778 2, .readIn 8901 8778])
    (.ifLtN 8900 8901 (mfFullL' a p sepL sepX fixP c2sP s2cP retP frmP)
      (block [.constN 8902 0, .outN 8902]))

set_option maxHeartbeats 1000000 in
/-- **The maximum-flow pipeline against `MfMainSpecS'`, every input size, loops allowed**:
`mf_pipelineT` for `MEncL` (no `loopless`), within `ppHeadS C C₀ n + 31200 n + 50 K + 2 p + 3210`
steps. -/
theorem mf_pipelineTL' {sepL sepX fixP c2sP s2cP retP frmP : Stmt} {C C₀ : ℕ}
    {R WZ : ℕ → ℕ → ℕ} {a p : ℕ}
    (hspec : MfMainSpecS' sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ) (hC : 1 ≤ C)
    (hE1 : Stmt.noEmit sepL = true) (hE2 : Stmt.noEmit sepX = true)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true) (hE6 : Stmt.noEmit retP = true)
    (hE7 : Stmt.noEmit frmP = true)
    (hRm : ∀ N N' Z Z', N ≤ N' → Z ≤ Z' → R N Z ≤ R N' Z')
    (hWZ : ∀ N Z, WZ N Z ≤ a * (N + Z + 1) ^ p)
    {d : List ℕ} {W : ℕ} (h : MEncL d W) (hroom : PipeRoomS R a p d W) :
    ∃ (pp : List ℕ) (Z : ℕ) (q : List ℕ), pp.length = nd d ∧
      RunsWithin (compile (mfTopL' a p sepL sepX fixP c2sP s2cP retP frmP) 0 ++ [Instr.halt])
        (inp d) W (ppHeadS C C₀ (nd d) + 31200 * nd d + 50 * nv d + 2 * p + 3210) (pp ++ Z :: q) ∧
      IsMax (map h.wf) (ucap d) (srcF d) (snkF d)
        (fun x => ((q.getD (pp.getD x 0) 0 : ℕ) : ℤ) - Z) := by
  have hW1 := hroom.1
  have e2 : d.getD 2 0 = nd d := rfl
  obtain ⟨c₁, t₁, e₁, ht₁, v0, v1, m1, o1⟩ : ∃ c₁ t₁,
      Exec (inp d) W (block [.constN 8900 0, .constN 8778 2, .readIn 8901 8778]) initConfig c₁ t₁ ∧
      t₁ = 3 ∧ c₁.nreg 8900 = 0 ∧ c₁.nreg 8901 = nd d ∧ c₁.nmem = initConfig.nmem ∧
      c₁.output = initConfig.output := by
    have hw := wordsBounded_initConfig W
    exec_block
    all_goals try omega
    all_goals try (config_simp; exact h.word_le 2)
    refine ⟨rfl, ?_, ?_, rfl, rfl⟩
    all_goals config_simp
    rfl
  rcases Nat.eq_zero_or_pos (nd d) with hn | hn
  · have : IsEmpty (Fin (nd d)) := ⟨fun x => by have := x.2; omega⟩
    obtain ⟨c₂, t₂, e₂, ht₂, o2⟩ : ∃ c₂ t₂,
        Exec (inp d) W (block [.constN 8902 0, .outN 8902]) c₁ c₂ t₂ ∧ t₂ = 2 ∧
        c₂.output = c₁.output ++ [0] := by
      have hw := e₁.wb_right
      exec_block
      all_goals try omega
      refine ⟨rfl, ?_⟩
      config_simp
    have ex : Exec (inp d) W (mfTopL' a p sepL sepX fixP c2sP s2cP retP frmP) initConfig c₂
        (t₁ + (t₂ + 2)) := .seq e₁ (.ifLtN_false (by omega) e₂)
    obtain ⟨k, hk, rest⟩ := runsWithin_of_exec_output (out := [] ++ 0 :: []) ex
      (by rw [o2, o1]; rfl)
    exact ⟨[], 0, [], by simp [hn], ⟨k, by omega, rest⟩, isMax_of_isEmpty _ _ _ _⟩
  · obtain ⟨pp, Z, q, hl, ⟨c', t, ex, ht, ho⟩, hmax⟩ := mf_execL' hspec hC hE1 hE2 hE3 hE4 hE5
      hE6 hE7 hRm hWZ h hn hroom c₁ e₁.wb_right (fun x => by rw [m1]; rfl)
    have ex' : Exec (inp d) W (mfTopL' a p sepL sepX fixP c2sP s2cP retP frmP) initConfig c'
        (t₁ + (t + 1)) := .seq e₁ (.ifLtN_true (by omega) ex)
    obtain ⟨k, hk, rest⟩ := runsWithin_of_exec_output (out := pp ++ Z :: q) ex'
      (by rw [ho, o1]; rfl)
    exact ⟨pp, Z, q, hl, ⟨k, by omega, rest⟩, hmax⟩


/-- **The maximum-flow theorem from the specification of the seven programs with the primed node-step
specifications** (`MfMainSpecS'`): as `maxFlowMachine_of_spec`. -/
theorem maxFlowMachine_of_spec' {sepL sepX fixP c2sP s2cP retP frmP : Stmt} {C C₀ : ℕ}
    {R WZ : ℕ → ℕ → ℕ} {a p r q : ℕ}
    (hspec : MfMainSpecS' sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ) (hC : 1 ≤ C)
    (hE1 : Stmt.noEmit sepL = true) (hE2 : Stmt.noEmit sepX = true)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true) (hE6 : Stmt.noEmit retP = true)
    (hE7 : Stmt.noEmit frmP = true)
    (hRm : ∀ N N' Z Z', N ≤ N' → Z ≤ Z' → R N Z ≤ R N' Z')
    (hR : ∀ N Z, R N Z ≤ r * (N + Z + 1) ^ q)
    (hWZ : ∀ N Z, WZ N Z ≤ a * (N + Z + 1) ^ p) :
    MaxFlowMachine' := by
  refine ⟨compile (mfTopL' a p sepL sepX fixP c2sP s2cP retP frmP) 0 ++ [Instr.halt],
    20 * (r + a) + 1000000 + cMF C C₀ p, p + q + 4, fun d W he hW => ?_⟩
  have h : MEncL d W := ⟨he.wf, he.plane, he.rotT, he.faceT, he.disj, he.word_le⟩
  have hpw : pipeW r a p q d ≤ W := by
    unfold pipeW
    have e : nd d + nv d + zb d + 2 = size' d := rfl
    rw [e]
    exact le_trans (Nat.mul_le_mul_right _ (by omega)) hW
  obtain ⟨pp, Z, q', hl, hrun, hmax⟩ := mf_pipelineTL' hspec hC hE1 hE2 hE3 hE4 hE5 hE6 hE7 hRm
    hWZ h (pipeRoomS_of_pow hR hpw)
  refine ⟨pp, Z, q', hl, (isSTFlow'_iff he.wf _).2 hmax.1, fun g hg => ?_,
    runsWithin_mono hrun ?_⟩
  · rw [stValue'_eq, stValue'_eq]
    exact hmax.2 g ((isSTFlow'_iff he.wf g).1 hg)
  · refine (ppBound C C₀ p (nd d) (nv d)).trans ?_
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))

end Pp

end BKMNW

end PlanarFlow
