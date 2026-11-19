module

public import PlanarFlow.BKMNW.PrPre

/-!
# The maximum-flow pipeline for inputs with loops

`MEncL d W`: `MEnc d W` (`PpEnc.lean`) **without `loopless`** (loops allowed in the input).

* **`mfFullL a p … = zP a p ; ppALB ; ppBB ; (if 0 < N then mfProgS … ; prBBL a p else print 0)`**
  (`N` the number of valid slots, `r6700` after `ppBB`; `N = 0` exactly when every dart is a
  loop, and then the zero flow is printed: `Z = 0`, `q = []`);
* **`mf_execL`**: the run from any configuration with zero memory, `0 < nd d`;
* **`mfTopL`**, **`mf_pipelineTL`**: every input size (`nd d = 0` prints `[0]`), within
  `ppHeadS C C₀ n + 31200 n + 50 K + 2 p + 3210` steps; `x ↦ q[pp[x]] - Z` is a maximum flow
  (loops carry `0`).
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
  NegSSSP.Driver CombMap Orbit PlanarSeparator.StDart

lemma srcF_snkF_disjointL {d : List ℕ} {W : ℕ} (h : MEncL d W) :
    Disjoint (srcF d) (snkF d) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  simp only [srcF, snkF, Finset.mem_filter, mem_univ, true_and] at hv hv'
  rcases h.disj v v.2 with e | e
  · exact hv e
  · exact hv' e

/-- A valid slot comes from a dart that is not a loop. -/
lemma exists_nl_of_valid {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F]
    [DecidableEq F] {M : CombMap (Fin n) V F} {s : ℕ} (hv : ValidS M s) :
    ∃ x : Fin n, x ∈ nlDarts M := by
  rcases hv with ⟨-, h⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩
  · exact ⟨_, h.2⟩
  · exact ⟨_, h.2⟩
  · exact ⟨_, h.2⟩

/-- A dart that is not a loop gives a valid slot. -/
lemma valid_of_nl {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    {M : CombMap (Fin n) V F} {x : Fin n} (hx : x ∈ nlDarts M) : ValidS M (3 * x.val) := by
  refine Or.inl ⟨by omega, ?_⟩
  rw [show 3 * x.val / 3 = x.val by omega]; exact (isNl_fin M).2 hx

/-- The algorithm is `0` on a loop. -/
lemma nlRunNX_loop {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (e : PVert M → TDart M)
    (he : ∀ w, (tnlMap M).tail (e w) = w) (u : D → ℤ) (S T : Finset V)
    (τ : ADec (lpreMapX M e he)) (NF : NFam (lpreMapX M e he)) {x : D} (hx : x ∉ nlDarts M) :
    nlRunNX M e he u S T τ NF x = 0 := by
  unfold nlRunNX nlExt
  rw [ppDiteF hx]

/-- A maximum flow pointwise equal to another function. -/
lemma isMax_of_eq {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {M : CombMap D V F} {u : D → ℤ} {S T : Finset V} {G f : D → ℤ} (hmax : IsMax M u S T G)
    (h : ∀ x, f x = G x) : IsMax M u S T f := by
  have : f = G := funext h
  rw [this]; exact hmax

/-- **The whole maximum-flow program, loops allowed.** -/
def mfFullL (a p : ℕ) (sepL sepX fixP c2sP s2cP retP frmP : Stmt) : Stmt :=
  .seq (preL a p) (.ifLtN 8903 6700 (.seq (mfProgS sepL sepX fixP c2sP s2cP retP frmP) (prBBL a p))
      (block [.constN 8902 0, .outN 8902]))

set_option maxHeartbeats 4000000 in
/-- **The run of the maximum-flow program, loops allowed**, from any configuration with zero memory
(`mf_execS` for `MEncL`). -/
theorem mf_execL {sepL sepX fixP c2sP s2cP retP frmP : Stmt} {C C₀ : ℕ}
    {R WZ : ℕ → ℕ → ℕ} {a p : ℕ}
    (hspec : MfMainSpecS sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ) (hC : 1 ≤ C)
    (hE1 : Stmt.noEmit sepL = true) (hE2 : Stmt.noEmit sepX = true)
    (hE3 : Stmt.noEmit fixP = true) (hE4 : Stmt.noEmit c2sP = true)
    (hE5 : Stmt.noEmit s2cP = true) (hE6 : Stmt.noEmit retP = true)
    (hE7 : Stmt.noEmit frmP = true)
    (hRm : ∀ N N' Z Z', N ≤ N' → Z ≤ Z' → R N Z ≤ R N' Z')
    (hWZ : ∀ N Z, WZ N Z ≤ a * (N + Z + 1) ^ p)
    {d : List ℕ} {W : ℕ} (h : MEncL d W) (hn : 0 < nd d) (hroom : PipeRoomS R a p d W)
    (c : Config) (hc : WordsBounded W c) (hm : ∀ x, c.nmem x = 0) :
    ∃ (pp : List ℕ) (Z : ℕ) (q : List ℕ), pp.length = nd d ∧
      (∃ c' t, Exec (inp d) W (mfFullL a p sepL sepX fixP c2sP s2cP retP frmP) c c' t ∧
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
    have G : MfMainGoalS (map h.wf) (pe (map h.wf)) (pe_tail (map h.wf) hrot)
        (fun i => (cp d i : ℤ)) (srcF d) (snkF d) N
        (enS (M := map h.wf) (srtD h.wf)) (enS (M := map h.wf) (srtD h.wf) 0) (gidS pos)
        (νX (map h.wf) (fun v => v.val) (nv d)) sepL sepX fixP c2sP s2cP retP frmP C C₀ R WZ :=
      mfMainGoalS_of_sub h.plane hrot hface (pe (map h.wf)) (pe_tail (map h.wf) hrot)
      (u := fun i => (cp d i : ℤ)) hu
      (srcF_snkF_disjointL h) hx0 _ _ hcard hsurj hgid
      (νX_injective (M := map h.wf) (hrot := hrot) (vn := fun v => v.val) (K := nv d)
        Fin.val_injective (fun v => v.2)) hC Hs
    unfold MfMainGoalS at G
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

end Pp

end BKMNW

end PlanarFlow
