module

public import PlanarFlow.BKMNW.MsCutJ

/-!
# The cut map of the path on the machine, part K: the ranks kept, surjectivity, the piece

* **`cutProg_RE`**: after `cutProg`, the scratch still holds the flags `TF = tfF`, the ranks of the
  copies `RE = reF lf` and of the roots `RK = rkF lf rt m` (at `Z + 2m`, `Z + 3m`, `Z + 4m`);
* **`cutKin_specX`**: `cutKin_spec` with, in addition, `r8228 = nE`, `r8230 = nE + nT` and the
  ranks `RE[i] = cE i`, `RK[i] = cT i` (`i < m`) at the end of `cutKin`;
* `cutTail_surj`, `cutFace_surj` (the hypotheses `htS`, `hfS` of `StEnc.cmProg_kin` on the cut);
* `cutIx_mem_piece` (the piece is the darts numbered below `nE + nT`), `cutIx_inl`.
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

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab NsStep
  CombMap

universe w

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The ranks after `cutProg`.** -/
theorem cutProg_RE (c : Config) (hc : WordsBounded W c) {m RVb RTb LFb TAb Z RVo RTo : ℕ}
    (hI : CpIn c m RVb RTb LFb TAb Z RVo RTo) {rv rt lf ta : ℕ → ℕ}
    (hrv : ∀ i < m, c.nmem (RVb + i) = rv i ∧ rv i < m)
    (hrt : ∀ i < m, c.nmem (RTb + i) = rt i) (prt : PermOn rt m)
    (hlf : ∀ i < m, c.nmem (LFb + i) = lf i ∧ lf i ≤ 1)
    (hta : ∀ i < m, c.nmem (TAb + i) = ta i) (pta : PermOn ta m)
    (dRV : RVb + m ≤ Z) (dRT : RTb + m ≤ Z) (dLF : LFb + m ≤ Z) (dTA : TAb + m ≤ Z)
    (dO1 : Z + 6 * m ≤ RVo) (dO2 : RVo + 5 * m ≤ RTo) (hw : RTo + 5 * m + 1 ≤ W) :
    ∃ c' t, Exec P W cutProg c c' t ∧
      (∀ i < m, c'.nmem (Z + 2 * m + i) = tfF lf rt m i ∧ c'.nmem (Z + 3 * m + i) = reF lf i ∧
        c'.nmem (Z + 4 * m + i) = rkF lf rt m i) := by
  obtain ⟨c₁, k₁, e₁, hk₁, vTF, vR, vTI, hV, h00, h01, h02, hM, hRg, hr, hrm, ho⟩ :=
    cutPre_exec (P := P) c hc hI hrv hrt prt hlf hta pta dRV dRT dLF dTA (by omega)
  have hnE : reF lf m ≤ m := cnt_le_self _ m
  have hnT : rkF lf rt m m ≤ m := cnt_le_self _ m
  have hA : WrArr c₁ LFb (Z + 2 * m) (Z + 3 * m) (Z + 4 * m) TAb (Z + 5 * m) RVb RTb (reF lf m)
      (rkF lf rt m m) m W lf (tfF lf rt m) (reF lf) (rkF lf rt m) ta (tiF ta m) rv rt := by
    refine ⟨fun i hi => by rw [hM _ (by omega)]; exact hlf i hi,
      fun i hi => ⟨vTF i hi, by unfold tfF; split_ifs <;> omega⟩,
      fun i hi => ⟨(vR i hi).1, (cnt_le_self _ i).trans hi.le⟩,
      fun i hi => ⟨(vR i hi).2, (cnt_le_self _ i).trans hi.le⟩,
      fun i hi => ⟨by rw [hM _ (by omega)]; exact hta i hi, pta.lt i hi⟩,
      fun i hi => ⟨?_, (tiF_spec pta hi).1⟩,
      fun i hi => by rw [hM _ (by omega)]; exact hrv i hi,
      fun i hi => ⟨by rw [hM _ (by omega)]; exact hrt i hi, prt.lt i hi⟩,
      by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
    obtain ⟨h1, h2⟩ := tiF_spec pta hi
    have := vTI _ h1
    rwa [h2] at this
  have hO : WrOut LFb (Z + 2 * m) (Z + 3 * m) (Z + 4 * m) TAb (Z + 5 * m) RVb RTb m RVo RTo
      (reF lf m + 4 * rkF lf rt m m) := by
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> omega
  obtain ⟨c₂, k₂, e₂, hk₂, hW, fm, fR, fr, frm, fo⟩ := cutWr_exec (P := P) c₁ e₁.wb_right hV
    h00 h01 h02 hA hO
    (fun i hi h0 => cnt_lt _ hi h0)
    (fun i hi j hj h1 h2 e => cnt_inj (fun j => lf j = 0) h1 h2 e)
    (fun i hi h0 => cnt_lt _ hi h0)
    (fun i hi j hj h1 h2 e => cnt_inj (fun j => 0 < tfF lf rt m j) h1 h2 e)
    (by omega) (by omega) (by omega) (by omega)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, fun i hi => ⟨?_, ?_, ?_⟩⟩
  · rw [fm _ (by omega) (by omega)]; exact vTF i hi
  · rw [fm _ (by omega) (by omega)]; exact (vR i hi).1
  · rw [fm _ (by omega) (by omega)]; exact (vR i hi).2

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

set_option maxHeartbeats 2000000 in
/-- **`cutKin_spec` with the counts and the ranks.** -/
theorem cutKin_specX {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (h' : EnumOK M.dual en m)
    (Pa : SPath M) (d₀ : CutD M Pa.darts)
    (hQ : EnumOK (cutMap Pa.rev_mem_darts').dual (cutEn M Pa.darts en m d₀)
      (nEc Pa.darts en m + 4 * nTc M Pa.darts en m))
    (hQ' : EnumOK (cutMap Pa.rev_mem_darts').dual.dual (cutEn M Pa.darts en m d₀)
      (nEc Pa.darts en m + 4 * nTc M Pa.darts en m))
    (c : Config) (hc : WordsBounded W c) {RVb RTb LFb TAb Z RVo RTo S β : ℕ}
    (hI : CpIn c m RVb RTb LFb TAb Z RVo RTo) (r58 : c.nreg 8258 = S) (r59 : c.nreg 8259 = β)
    (hrv : ∀ i < m, c.nmem (RVb + i) < m ∧ en (c.nmem (RVb + i)) = M.rev (en i))
    (hrt : ∀ i < m, c.nmem (RTb + i) < m ∧ en (c.nmem (RTb + i)) = M.rot (en i))
    (hlf : ∀ i < m, c.nmem (LFb + i) = if en i ∈ Pa.darts then 1 else 0)
    (hta : ∀ i < m, c.nmem (TAb + i) = ixOf en m (tour M Pa.darts (en i)))
    (dRV : RVb + m ≤ Z) (dRT : RTb + m ≤ Z) (dLF : LFb + m ≤ Z) (dTA : TAb + m ≤ Z)
    (dO1 : Z + 6 * m ≤ RVo) (dO2 : RVo + 5 * m ≤ RTo) (dO3 : RTo + 5 * m ≤ S)
    (dO4 : S + 15 * m ≤ β) (hw : β + 60 * m + 1 ≤ W) :
    ∃ c' t, Exec P W cutKin c c' t ∧
      t ≤ cutCost m + 8 + (140 * (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) + 150) ∧
      StEnc.KInM (cutMap Pa.rev_mem_darts') (StEnc.enEq hQ) (StEnc.ιF _ hQ) (StEnc.ιG _ hQ)
        (StEnc.ιV _ hQ') (StEnc.ιE _ hQ) c'.nmem β ∧
      c'.nreg 8228 = nEc Pa.darts en m ∧
      c'.nreg 8230 = nEc Pa.darts en m + nTc M Pa.darts en m ∧
      (∀ i < m, c'.nmem (Z + 3 * m + i) = cE Pa.darts en i ∧
        c'.nmem (Z + 4 * m + i) = cT M Pa.darts en i) ∧
      (∀ a, (a < Z ∨ β + 12 * (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) + 1 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ CpScr r → ¬ StEnc.SmScr r → (r < 7700 ∨ 7704 < r) → r ≠ 8260 → r ≠ 8261 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hnE : nEc Pa.darts en m ≤ m := cnt_le_self _ m
  have hnT : nTc M Pa.darts en m ≤ m := cnt_le_self _ m
  obtain ⟨c₁, k₁, e₁, hk₁, hW, h28, h30, hM, hR, hr, hrm, ho⟩ := cutProg_spec (P := P) h h' Pa c hc
    hI hrv hrt hlf hta dRV dRT dLF dTA dO1 dO2 (by omega)
  -- the ranks, from a second run of `cutProg`
  have hL : ∀ e ∈ Pa.darts, M.rev e ∈ Pa.darts := Pa.rev_mem_darts'
  have erv : ∀ i < m, c.nmem (RVb + i) = ixOf en m (M.rev (en i)) := fun i hi =>
    ix_unique h (hrv i hi).1 (hrv i hi).2
  have ert : ∀ i < m, c.nmem (RTb + i) = ixOf en m (M.rot (en i)) := fun i hi =>
    ix_unique h (hrt i hi).1 (hrt i hi).2
  have prt : PermOn (fun i => c.nmem (RTb + i)) m :=
    ⟨fun x hx => (hrt x hx).1, fun x hx y hy e => h.inj x hx y hy (M.rot_injective (by
      rw [← (hrt x hx).2, ← (hrt y hy).2]; exact congrArg en e))⟩
  have pta : PermOn (fun i => c.nmem (TAb + i)) m :=
    ⟨fun x hx => by rw [hta x hx]; exact ixOf_lt h _, fun x hx y hy e => by
      rw [hta x hx, hta y hy] at e
      have e' := congrArg en e
      rw [en_ixOf h, en_ixOf h] at e'
      exact h.inj x hx y hy (tour_injective hL e')⟩
  obtain ⟨c₁', k₁', e₁', hRE⟩ := cutProg_RE (P := P) c hc hI
    (rv := fun i => c.nmem (RVb + i)) (rt := fun i => c.nmem (RTb + i))
    (lf := fun i => c.nmem (LFb + i)) (ta := fun i => c.nmem (TAb + i))
    (fun i hi => ⟨rfl, (hrv i hi).1⟩) (fun i hi => rfl) prt
    (fun i hi => ⟨rfl, by rw [hlf i hi]; split_ifs <;> omega⟩) (fun i hi => rfl) pta
    dRV dRT dLF dTA dO1 dO2 (by omega)
  obtain ⟨rfl, -⟩ := Exec.det e₁' e₁
  have hRE' : ∀ i < m, c₁'.nmem (Z + 3 * m + i) = cE Pa.darts en i ∧
      c₁'.nmem (Z + 4 * m + i) = cT M Pa.darts en i := fun i hi => by
    obtain ⟨-, a2, a3⟩ := hRE i hi
    refine ⟨by rw [a2]; exact reF_eq hlf hi.le, by rw [a3]; exact rkF_eq h' hlf ert hi.le⟩
  have g : ∀ r, 8256 ≤ r → r ≤ 8259 → c₁'.nreg r = c.nreg r := fun r h1 h2 =>
    hR r (by simp only [CpScr]; omega)
  obtain ⟨c₂, k₂, e₂, hk₂, s0, s1, s2, s3, s4, sR, sm, sr, srm, so⟩ := cjSet_exec (P := P) c₁'
    e₁.wb_right h28 h30 (by rw [g _ (by omega) (by omega), hI.r56])
    (by rw [g _ (by omega) (by omega), hI.r57]) (by rw [g _ (by omega) (by omega), r58])
    (by rw [g _ (by omega) (by omega), r59]) (by omega)
  have hRV : ∀ i < (nEc Pa.darts en m + 4 * nTc M Pa.darts en m), c₂.nmem (RVo + i) =
      rvI (cutMap Pa.rev_mem_darts').dual (cutEn M Pa.darts en m d₀)
        (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) i := fun i hi => by
    rw [sm]
    have e := cutIx_cutEn h d₀ hi
    unfold rvI
    rw [ixOf_cutEn Pa.rev_mem_darts' h]
    conv_lhs => rw [← e]
    exact (hW _).1
  have hRT : ∀ i < (nEc Pa.darts en m + 4 * nTc M Pa.darts en m), c₂.nmem (RTo + i) =
      ixOf (cutEn M Pa.darts en m d₀) (nEc Pa.darts en m + 4 * nTc M Pa.darts en m)
        ((cutMap Pa.rev_mem_darts').dual.rot (cutEn M Pa.darts en m d₀ i)) := fun i hi => by
    rw [sm, ixOf_cutEn Pa.rev_mem_darts' h, rot_dual_cut Pa.rev_mem_darts']
    have e := cutIx_cutEn h d₀ hi
    conv_lhs => rw [← e]
    exact (hW _).2
  obtain ⟨c₃, k₃, e₃, hk₃, hK, hz, hm₃, hR₃, hr₃, hrm₃, ho₃⟩ := StEnc.smP_kin (P := P) hQ hQ' c₂
    e₂.wb_right s0 s1 s2 s3 s4 hRV hRT (by omega) (by omega) (by omega) (by omega)
  have hK' := kInM_congr (A := (cutMap Pa.rev_mem_darts').dual.dual)
    (B := cutMap Pa.rev_mem_darts') rfl rfl rfl hK
  have nS : ∀ r, 8228 ≤ r → r ≤ 8230 → ¬ StEnc.SmScr r := fun r h1 h2 => by
    simp only [StEnc.SmScr]; omega
  refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, hK', ?_, ?_, fun i hi => ?_,
    fun a ha => ?_, fun r h1 h2 h3 h4 h5 => ?_, by rw [hr₃, sr, hr], by rw [hrm₃, srm, hrm],
    by rw [ho₃, so, ho]⟩
  · rw [hR₃ _ (nS _ le_rfl (by omega)), sR _ (by omega) (by omega) (by omega), h28]
  · rw [hR₃ _ (nS _ (by omega) le_rfl), sR _ (by omega) (by omega) (by omega), h30]
  · rw [hm₃ _ (by omega) (by omega), hm₃ _ (by omega) (by omega), sm]; exact hRE' i hi
  · rw [hm₃ a (by omega) (by omega), sm, hM a (by omega)]
  · rw [hR₃ r h2, sR r h3 h4 h5, hR r h1]

/-! ### Surjectivity of the tails and faces of the cut -/

section Surj

variable {L : List D} (hL : ∀ e ∈ L, M.rev e ∈ L)

theorem cutTail_surj (hf : ∀ f : F, ∃ d, M.face d = f) : Surjective (cutTail hL) := by
  rintro (f | t)
  · obtain ⟨d, rfl⟩ := hf f
    by_cases hd : d ∈ L
    · exact ⟨.inr (.inr (.inl ⟨d, tail_mem_cutS hd⟩)), rfl⟩
    · exact ⟨.inl ⟨d, hd⟩, rfl⟩
  · exact ⟨.inr (.inl t), rfl⟩

theorem cutFace_surj (ht : ∀ v : V, ∃ d, M.tail d = v) (t₀ : CutT M L) :
    Surjective (cutFace hL) := by
  rintro (⟨v, hv⟩ | t | u)
  · obtain ⟨d, rfl⟩ := ht v
    refine ⟨.inl ⟨d, not_mem_of_tail hL hv⟩, ?_⟩
    simp [cutFace, hv]
  · exact ⟨.inr (.inl t), rfl⟩
  · exact ⟨.inr (.inr (.inr (.inl t₀))), rfl⟩

end Surj

/-! ### The piece and the lengths by numbers -/

lemma cutIx_mem_piece {L : List D} {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (d : CutD M L) :
    d ∈ cutPiece M L ↔ cutIx M L en m d < nEc L en m + nTc M L en m := by
  rw [mem_cutPiece]
  rcases d with ⟨e, he⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ <;> simp only [inPiece, cutIx]
  · have := cE_lt h he; simp; omega
  · have := cT_lt h ht; simp; omega
  all_goals (simp; try omega)

end MsEnc

end BKMNW

end PlanarFlow
