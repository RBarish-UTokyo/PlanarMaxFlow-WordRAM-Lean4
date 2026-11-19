module

public import PlanarFlow.BKMNW.MsCutH

/-!
# The cut map of the path on the machine, part I: what `cutProg` computes on a map

**`cutProg_spec`**: on the index arrays of an MSSP call (`RV`, `RT` of `M` in the order `en`),
with the path flags `LF` and the tour array `TA` written by `fcProg` (`fcProg_spec`), within
`cutCost m = 178 m + 95` steps `cutProg` writes, for **every dart `d` of the cut map**
`cutMap hL` along the path (`hL = P.rev_mem_darts'`), at its number `cutIx d`:

* `RV'[cutIx d] = cutIx (cutRev d)` (the reverse) and `RT'[cutIx d] = cutIx (cutNext d)` (the next
  dart along the face);

and `r8228 = nE`, `r8230 = nE + nT` (`nD = nE + 4 nT` darts). These are exactly the arrays
`rvI Q en' nD`, `ixOf en' nD ∘ Q.rot` of the map `Q = (cutMap hL).dual` in the order
`en' = cutEn` (`cutProg_Q`), the input of the map encoder `StEnc.smP_kin`, whose output is
Klein's encoding of `Q.dual = cutMap hL` (`dual_dual'`).
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

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

variable {P : Input} {W : ℕ}

/-- The ranks of the copies from the flags of the path. -/
lemma reF_eq {en : ℕ → D} {m : ℕ} {L : List D} {lf : ℕ → ℕ}
    (hlf : ∀ i < m, lf i = if en i ∈ L then 1 else 0) {i : ℕ} (hi : i ≤ m) :
    reF lf i = cE L en i := by
  unfold reF cE
  congr 1
  refine Finset.filter_congr fun j hj => ?_
  have := hlf j (by have := mem_range.1 hj; omega)
  by_cases h : en j ∈ L <;> simp [h, this]

/-- The flag of a dart leaving the path from the vertex labels. -/
lemma tfF_pos_iff {en : ℕ → D} {m : ℕ} (h' : EnumOK M.dual en m) {L : List D} {lf rt : ℕ → ℕ}
    (hlf : ∀ i < m, lf i = if en i ∈ L then 1 else 0)
    (hrt : ∀ i < m, rt i = ixOf en m (M.rot (en i))) {j : ℕ} (hj : j < m) :
    0 < tfF lf rt m j ↔ M.tail (en j) ∈ cutS M L := by
  have eq : ∀ x < m, phiI M.dual en m x = rt x := fun x hx => (hrt x hx).symm
  have hlab : ∀ i < m, olab rt i = labI M.dual en m i := fun i hi => by
    unfold labI; rw [StEnc.olab_congr (phi_permOn h') eq hi]
  unfold tfF
  rw [mem_cutS]
  constructor
  · intro hp
    split_ifs at hp with hc
    · obtain ⟨i', hi', hl, he⟩ := hc
      refine ⟨en i', ?_, ?_⟩
      · have := hlf i' hi'; by_contra hn; simp [hn] at this; omega
      · have e : labI M.dual en m i' = labI M.dual en m j := by
          rw [← hlab i' hi', ← hlab j hj]; omega
        exact (face_eq_iff h' hi' hj).2 e
    · omega
  · rintro ⟨e, he, hte⟩
    obtain ⟨i', hi', rfl⟩ := h'.surj e
    have hex : ∃ i' < m, 0 < lf i' ∧ olab rt i' + 1 = olab rt j + 1 := by
      refine ⟨i', hi', by rw [hlf i' hi', iteT he]; omega, ?_⟩
      have := (face_eq_iff h' hi' hj).1 hte
      rw [hlab i' hi', hlab j hj, this]
    rw [iteT hex]; omega

lemma rkF_eq {en : ℕ → D} {m : ℕ} (h' : EnumOK M.dual en m) {L : List D} {lf rt : ℕ → ℕ}
    (hlf : ∀ i < m, lf i = if en i ∈ L then 1 else 0)
    (hrt : ∀ i < m, rt i = ixOf en m (M.rot (en i))) {i : ℕ} (hi : i ≤ m) :
    rkF lf rt m i = cT M L en i := by
  unfold rkF cT
  congr 1
  exact Finset.filter_congr fun j hj => tfF_pos_iff h' hlf hrt (by have := mem_range.1 hj; omega)

set_option maxHeartbeats 1000000 in
/-- **The cut map of the path on the machine** (see the module docstring). -/
theorem cutProg_spec {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (h' : EnumOK M.dual en m)
    (Pa : SPath M) (c : Config) (hc : WordsBounded W c) {RVb RTb LFb TAb Z RVo RTo : ℕ}
    (hI : CpIn c m RVb RTb LFb TAb Z RVo RTo)
    (hrv : ∀ i < m, c.nmem (RVb + i) < m ∧ en (c.nmem (RVb + i)) = M.rev (en i))
    (hrt : ∀ i < m, c.nmem (RTb + i) < m ∧ en (c.nmem (RTb + i)) = M.rot (en i))
    (hlf : ∀ i < m, c.nmem (LFb + i) = if en i ∈ Pa.darts then 1 else 0)
    (hta : ∀ i < m, c.nmem (TAb + i) = ixOf en m (tour M Pa.darts (en i)))
    (dRV : RVb + m ≤ Z) (dRT : RTb + m ≤ Z) (dLF : LFb + m ≤ Z) (dTA : TAb + m ≤ Z)
    (dO1 : Z + 6 * m ≤ RVo) (dO2 : RVo + 5 * m ≤ RTo) (hw : RTo + 5 * m + 1 ≤ W) :
    ∃ c' t, Exec P W cutProg c c' t ∧ t ≤ cutCost m ∧
      (∀ d : CutD M Pa.darts,
        c'.nmem (RVo + cutIx M Pa.darts en m d) =
          cutIx M Pa.darts en m (cutRev Pa.rev_mem_darts' d) ∧
        c'.nmem (RTo + cutIx M Pa.darts en m d) =
          cutIx M Pa.darts en m (cutNext Pa.rev_mem_darts' d)) ∧
      c'.nreg 8228 = nEc Pa.darts en m ∧ c'.nreg 8230 = nEc Pa.darts en m + nTc M Pa.darts en m ∧
      (∀ a, (a < Z ∨ RTo + 5 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ CpScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set L := Pa.darts with hLd
  have hL : ∀ e ∈ L, M.rev e ∈ L := Pa.rev_mem_darts'
  set rv : ℕ → ℕ := fun i => c.nmem (RVb + i) with hrvd
  set rt : ℕ → ℕ := fun i => c.nmem (RTb + i) with hrtd
  set lf : ℕ → ℕ := fun i => c.nmem (LFb + i) with hlfd
  set ta : ℕ → ℕ := fun i => c.nmem (TAb + i) with htad
  have erv : ∀ i < m, rv i = ixOf en m (M.rev (en i)) := fun i hi =>
    ix_unique h (hrv i hi).1 (hrv i hi).2
  have ert : ∀ i < m, rt i = ixOf en m (M.rot (en i)) := fun i hi =>
    ix_unique h (hrt i hi).1 (hrt i hi).2
  have prt : PermOn rt m :=
    ⟨fun x hx => (hrt x hx).1, fun x hx y hy e => h.inj x hx y hy (M.rot_injective (by
      rw [← (hrt x hx).2, ← (hrt y hy).2]; exact congrArg en e))⟩
  have eta : ∀ i < m, ta i = ixOf en m (tour M L (en i)) := hta
  have pta : PermOn ta m :=
    ⟨fun x hx => by rw [eta x hx]; exact ixOf_lt h _, fun x hx y hy e => by
      rw [eta x hx, eta y hy] at e
      have e' := congrArg en e
      rw [en_ixOf h, en_ixOf h] at e'
      exact h.inj x hx y hy (tour_injective hL e')⟩
  have hlf' : ∀ i < m, lf i = if en i ∈ L then 1 else 0 := hlf
  obtain ⟨c', t, ex, ht, hW, h28, h30, hM, hR, hr, hrm, ho⟩ := cutProg_run (P := P) c hc hI
    (rv := rv) (rt := rt) (lf := lf) (ta := ta) (fun i hi => ⟨rfl, (hrv i hi).1⟩)
    (fun i hi => rfl) prt (fun i hi => ⟨rfl, by rw [hlf' i hi]; split_ifs <;> omega⟩)
    (fun i hi => rfl) pta dRV dRT dLF dTA dO1 dO2 hw
  have eE : reF lf m = nEc L en m := reF_eq hlf' le_rfl
  have eT : rkF lf rt m m = nTc M L en m := rkF_eq h' hlf' ert le_rfl
  rw [eE, eT] at hW
  refine ⟨c', t, ex, ht, fun d => ?_, by rw [h28, eE], by rw [h30, eE, eT], hM, hR, hr, hrm,
    ho⟩
  rcases d with ⟨e, he⟩ | ⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, hs⟩
  · -- a copy
    have hi := ixOf_lt h e
    have hen := en_ixOf h e
    have h0 : lf (ixOf en m e) = 0 := by rw [hlf' _ hi, hen, iteF he]
    obtain ⟨v1, v2⟩ := hW.e _ hi h0
    rw [reF_eq hlf' hi.le] at v1 v2
    refine ⟨?_, ?_⟩
    · show c'.nmem (RVo + cE L en (ixOf en m e)) = cE L en (ixOf en m (M.rev e))
      rw [v1, erv _ hi, hen, reF_eq hlf' (ixOf_lt h _).le]
    · rw [cutIx_next_E hL h]
      show c'.nmem (RTo + cE L en (ixOf en m e)) = _
      rw [v2]
      have hT := tfF_pos_iff h' hlf' ert hi
      rw [hen] at hT
      by_cases ht' : M.tail e ∈ cutS M L
      · rw [iteT (hT.2 ht'), iteT ht', rkF_eq h' hlf' ert (pta.lt _ hi).le, eta _ hi, hen]
      · rw [iteF (fun h1 => ht' (hT.1 h1)), iteF ht', ert _ hi, hen,
          reF_eq hlf' (ixOf_lt h _).le]
  all_goals
    have hi := ixOf_lt h s
    have hen := en_ixOf h s
    have ht0 : 0 < tfF lf rt m (ixOf en m s) := (tfF_pos_iff h' hlf' ert hi).2 (by rw [hen]; exact hs)
    have ek : rkF lf rt m (ixOf en m s) = cT M L en (ixOf en m s) := rkF_eq h' hlf' ert hi.le
  · -- a pendant dart
    obtain ⟨v1, v2⟩ := hW.t1 _ hi ht0
    rw [ek] at v1 v2
    refine ⟨by rw [cutIx_rev_1 hL]; exact v1, ?_⟩
    rw [cutIx_next_1 hL]
    show c'.nmem (RTo + (nEc L en m + cT M L en (ixOf en m s))) = _
    rw [v2, hlf' _ hi, hen]
    by_cases hsL : s ∈ L
    · simp only [hsL, ↓reduceIte, Nat.lt_one_iff, one_ne_zero, zero_lt_one]
      rw [rkF_eq h' hlf' ert (pta.lt _ hi).le, eta _ hi, hen]
    · simp only [hsL, ↓reduceIte, lt_irrefl]
      rw [reF_eq hlf' hi.le]
  · -- a reverse pendant dart
    obtain ⟨v1, v2⟩ := hW.t2 _ hi ht0
    rw [ek] at v1 v2
    refine ⟨by rw [cutIx_rev_2 hL]; exact v1, ?_⟩
    rw [cutIx_next_2 hL]
    show c'.nmem (RTo + (nEc L en m + nTc M L en m + cT M L en (ixOf en m s))) = _
    rw [v2]
    set s' := ((tourT hL).symm ⟨s, hs⟩).1 with hs'
    have hs'i := ixOf_lt h s'
    have e1 : ta (ixOf en m s') = ixOf en m s := by
      rw [eta _ hs'i, en_ixOf h, hs', tour_symm hL]
    have e2 : tiF ta m (ixOf en m s) = ixOf en m s' := by rw [← e1, tiF_ta pta hs'i]
    rw [e2, rkF_eq h' hlf' ert hs'i.le]
  · -- a ring dart
    obtain ⟨v1, v2⟩ := hW.t3 _ hi ht0
    rw [ek] at v1 v2
    refine ⟨by rw [cutIx_rev_3 hL]; exact v1, ?_⟩
    rw [cutIx_next_3 hL]
    show c'.nmem (RTo + (nEc L en m + 2 * nTc M L en m + cT M L en (ixOf en m s))) = _
    rw [v2, rkF_eq h' hlf' ert (pta.lt _ hi).le, eta _ hi, hen]
  · -- a reverse ring dart
    obtain ⟨v1, v2⟩ := hW.t4 _ hi ht0
    rw [ek] at v1 v2
    exact ⟨by rw [cutIx_rev_4 hL]; exact v1, by rw [cutIx_next_4 hL]; exact v2⟩

end MsEnc

end BKMNW

end PlanarFlow
