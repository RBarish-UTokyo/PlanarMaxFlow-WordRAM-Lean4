module

public import PlanarFlow.BKMNW.MsTourD
public import PlanarFlow.BKMNW.StMapF

/-!
# The corner order on the machine, part E: what `fcProg` computes on a map

The corners of FixConservationOnPath (`fixCorner M P s`, the face of the `s`-th dart of the walk
around the path) taken at their **first** positions around the path, in increasing order, are the
list **`fixCornerL M P`** (a function of `M` and `P`: no choice). `fixCornerL_spec`: the positions
increase, lie below the period `fixPer M P`, their faces lie along the path, are pairwise distinct
and cover the faces along the path (the hypotheses of `exists_fixCornersInj`).

**`fcProg_spec`**: on the index arrays of an MSSP call (`RV`, `RT`, the path, as in
`MsCall.MsIn`), within `fcCost m k = 96 m + 11 k + 60` steps, `fcProg` writes

* the period `fixPer M P` (`r8156`) and the walk `TR[s] = ixOf ((tour M P.darts)^[s] (P.d 0))`;
* the labels of the faces `FL[i] = labI M en m i + 1` and the flags `LF[i] = [en i ∈ P.darts]`;
* the number of corners `|fixCornerL M P|` (`r8157`), their positions `CS[r]`, their darts
  `CD[r] = ixOf ((tour M P.darts)^[CS[r]] (P.d 0))` (a dart of the face of the corner, the query
  darts of the MSSP call), and, for every dart `i` of a face along the path, the number
  `CN'[FL[i]] = r` of the corner of its face.
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

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-! ### The corners at their first positions -/

variable (M) in
/-- The position `s` of the walk around `P` is the first position of a face along the path. -/
def cornerQ (P : SPath M) (s : ℕ) : Bool :=
  decide (fixCorner M P s ∈ P.faces ∧ ∀ s' < s, fixCorner M P s' ≠ fixCorner M P s)

variable (M) in
/-- **The corners at their first positions**, in increasing order. -/
noncomputable def fixCornerL (P : SPath M) : List ℕ :=
  (List.range (fixPer M P)).filter (cornerQ M P)

lemma mem_fixCornerL {P : SPath M} {s : ℕ} :
    s ∈ fixCornerL M P ↔ s < fixPer M P ∧ fixCorner M P s ∈ P.faces ∧
      ∀ s' < s, fixCorner M P s' ≠ fixCorner M P s := by
  simp [fixCornerL, cornerQ]

/-- **The corners at their first positions**: increasing, below the period, along the path,
pairwise distinct, covering the faces along the path. -/
theorem fixCornerL_spec (hrot : M.RotTrans) (P : SPath M) :
    (∀ r r', r < r' → r' < (fixCornerL M P).length →
      (fixCornerL M P).getD r 0 < (fixCornerL M P).getD r' 0) ∧
    (∀ r < (fixCornerL M P).length, (fixCornerL M P).getD r 0 < fixPer M P) ∧
    (∀ r < (fixCornerL M P).length, fixCorner M P ((fixCornerL M P).getD r 0) ∈ P.faces) ∧
    (∀ r < (fixCornerL M P).length, ∀ r' < (fixCornerL M P).length,
      fixCorner M P ((fixCornerL M P).getD r 0) = fixCorner M P ((fixCornerL M P).getD r' 0) →
        r = r') ∧
    (∀ x ∈ P.faces, ∃ r < (fixCornerL M P).length,
      fixCorner M P ((fixCornerL M P).getD r 0) = x) := by
  classical
  set L := fixCornerL M P with hL
  have hsort : L.Pairwise (· < ·) := List.Pairwise.filter _ List.pairwise_lt_range
  have hmem : ∀ r < L.length, L.getD r 0 ∈ L := fun r hr => by
    rw [List.getD_eq_getElem _ _ hr]; exact List.getElem_mem hr
  have hmono : ∀ r r', r < r' → r' < L.length → L.getD r 0 < L.getD r' 0 := by
    intro r r' h1 h2
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ h2]
    exact List.pairwise_iff_getElem.1 hsort r r' (by omega) h2 h1
  refine ⟨hmono, fun r hr => (mem_fixCornerL.1 (hmem r hr)).1,
    fun r hr => (mem_fixCornerL.1 (hmem r hr)).2.1, fun r hr r' hr' he => ?_, fun x hx => ?_⟩
  · by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact (mem_fixCornerL.1 (hmem r' hr')).2.2 _ (hmono r r' h hr') he
    · exact (mem_fixCornerL.1 (hmem r hr)).2.2 _ (hmono r' r h hr) he.symm
  · rcases Nat.eq_zero_or_pos P.k with h0 | hk
    · simp [SPath.faces, SPath.darts, h0] at hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
    obtain ⟨n, hn⟩ := fix_horb hrot P hk ⟨e, tail_mem_cutS he⟩
    have hfe : fixCorner M P n = M.face e := by rw [fixCorner_eq P hk, hn]
    have hex : ∃ n, fixCorner M P n = M.face e := ⟨n, hfe⟩
    set n₀ := Nat.find hex
    have hn₀ : fixCorner M P n₀ = M.face e := Nat.find_spec hex
    have hlt : n₀ < fixPer M P := by
      have h1 : n₀ ≤ n % fixPer M P := Nat.find_min' hex (by rw [fixCorner_mod, hfe])
      have := Nat.mod_lt n (fixPer_pos P); omega
    have hin : n₀ ∈ L := mem_fixCornerL.2 ⟨hlt, by rw [hn₀]; exact hx,
      fun s' hs' h => Nat.find_min hex hs' (h.trans hn₀)⟩
    obtain ⟨r, hr, hr'⟩ := List.mem_iff_getElem.1 hin
    exact ⟨r, hr, by rw [List.getD_eq_getElem _ _ hr, hr', hn₀]⟩

/-! ### The arrays of the map -/

section Arrays

variable {en : ℕ → D} {m : ℕ}

lemma ix_unique (h : EnumOK M en m) {i : ℕ} (hi : i < m) {d : D} (e : en i = d) :
    i = ixOf en m d := by rw [← e, ixOf_en h hi]

lemma rot_rev (x : D) : M.rot (M.rev x) = M.next x := by
  rw [CombMap.rot, M.rev_rev]

/-- The face permutation on the indices from the arrays. -/
lemma nx_eq (h : EnumOK M en m) {rv rt : ℕ → ℕ}
    (hrv : ∀ i < m, rv i < m ∧ en (rv i) = M.rev (en i))
    (hrt : ∀ i < m, rt i < m ∧ en (rt i) = M.rot (en i)) {i : ℕ} (hi : i < m) :
    phiI M en m i = rt (rv i) := by
  obtain ⟨h1, h2⟩ := hrv i hi
  obtain ⟨h3, h4⟩ := hrt _ h1
  unfold phiI
  rw [← ix_unique h h3 (by rw [h4, h2, rot_rev])]

lemma mkSet_iff (h : EnumOK M en m) {P : SPath M} {rv pm : ℕ → ℕ}
    (hrv : ∀ i < m, rv i < m ∧ en (rv i) = M.rev (en i))
    (hpm : ∀ j < P.k, pm j < m ∧ en (pm j) = P.d j) {i : ℕ} (hi : i < m) :
    mkSet pm rv P.k i ↔ en i ∈ P.darts := by
  rw [P.mem_darts]
  constructor
  · rintro ⟨j, hj, rfl | rfl⟩
    · exact ⟨j, hj, Or.inl (hpm j hj).2⟩
    · exact ⟨j, hj, Or.inr (by rw [(hrv _ (hpm j hj).1).2, (hpm j hj).2])⟩
  · rintro ⟨j, hj, e | e⟩
    · exact ⟨j, hj, Or.inl (h.inj i hi _ (hpm j hj).1 (by rw [e, (hpm j hj).2]))⟩
    · refine ⟨j, hj, Or.inr (h.inj i hi _ (hrv _ (hpm j hj).1).1 ?_)⟩
      rw [e, (hrv _ (hpm j hj).1).2, (hpm j hj).2]

lemma en_taF (h : EnumOK M en m) {P : SPath M} {rv rt pm : ℕ → ℕ}
    (hrv : ∀ i < m, rv i < m ∧ en (rv i) = M.rev (en i))
    (hrt : ∀ i < m, rt i < m ∧ en (rt i) = M.rot (en i))
    (hpm : ∀ j < P.k, pm j < m ∧ en (pm j) = P.d j) {i : ℕ} (hi : i < m) :
    taF rv rt pm P.k i < m ∧ en (taF rv rt pm P.k i) = tour M P.darts (en i) := by
  unfold taF
  by_cases hs : mkSet pm rv P.k i
  · have hL := (mkSet_iff h hrv hpm hi).1 hs
    rw [iteT hs, tour_of_mem hL]
    exact ⟨(hrt _ (hrv i hi).1).1, by rw [(hrt _ (hrv i hi).1).2, (hrv i hi).2, rot_rev]⟩
  · have hL : en i ∉ P.darts := fun h' => hs ((mkSet_iff h hrv hpm hi).2 h')
    rw [iteF hs, tour_of_not_mem hL]
    exact hrt i hi

lemma taF_permOn (h : EnumOK M en m) {P : SPath M} {rv rt pm : ℕ → ℕ}
    (hrv : ∀ i < m, rv i < m ∧ en (rv i) = M.rev (en i))
    (hrt : ∀ i < m, rt i < m ∧ en (rt i) = M.rot (en i))
    (hpm : ∀ j < P.k, pm j < m ∧ en (pm j) = P.d j) : PermOn (taF rv rt pm P.k) m where
  lt x hx := (en_taF h hrv hrt hpm hx).1
  inj x hx y hy e := by
    have e' := congrArg en e
    rw [(en_taF h hrv hrt hpm hx).2, (en_taF h hrv hrt hpm hy).2] at e'
    exact h.inj x hx y hy (tour_injective P.rev_mem_darts' e')

lemma en_taF_iter (h : EnumOK M en m) {P : SPath M} {rv rt pm : ℕ → ℕ}
    (hrv : ∀ i < m, rv i < m ∧ en (rv i) = M.rev (en i))
    (hrt : ∀ i < m, rt i < m ∧ en (rt i) = M.rot (en i))
    (hpm : ∀ j < P.k, pm j < m ∧ en (pm j) = P.d j) {i : ℕ} (hi : i < m) :
    ∀ s, en ((taF rv rt pm P.k)^[s] i) = (tour M P.darts)^[s] (en i)
  | 0 => rfl
  | s + 1 => by
    rw [iterate_succ_apply', iterate_succ_apply',
      (en_taF h hrv hrt hpm (OrbLab.iter_lt (taF_permOn h hrv hrt hpm) hi s)).2,
      en_taF_iter h hrv hrt hpm hi s]

end Arrays

/-! ### The program on a map -/

/-- `fcProg` uses natural words only. -/
theorem fcProg_natOnly : Klein.natOnly fcProg = true := by decide +kernel

variable {P : Input} {W : ℕ}

/-- **The corner order on the machine** (see the module docstring). -/
theorem fcProg_spec (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) (c : Config) (hc : WordsBounded W c) {RVb RTb Pb S : ℕ}
    (r50 : c.nreg 8150 = m) (r51 : c.nreg 8151 = RVb) (r52 : c.nreg 8152 = RTb)
    (r53 : c.nreg 8153 = Pa.k) (r54 : c.nreg 8154 = Pb) (r55 : c.nreg 8155 = S)
    (hrv : ∀ i < m, c.nmem (RVb + i) < m ∧ en (c.nmem (RVb + i)) = M.rev (en i))
    (hrt : ∀ i < m, c.nmem (RTb + i) < m ∧ en (c.nmem (RTb + i)) = M.rot (en i))
    (hpd : ∀ j < Pa.k, c.nmem (Pb + j) < m ∧ en (c.nmem (Pb + j)) = Pa.d j)
    (dRV : RVb + m ≤ S ∨ S + 10 * m ≤ RVb) (dRT : RTb + m ≤ S ∨ S + 10 * m ≤ RTb)
    (dP : Pb + Pa.k ≤ S ∨ S + 10 * m ≤ Pb)
    (hW : S + 10 * m + 2 ≤ W) (wRV : RVb + m ≤ W) (wRT : RTb + m ≤ W) (wP : Pb + Pa.k ≤ W)
    (wk : Pa.k + 1 ≤ W) :
    ∃ c' u, Exec P W fcProg c c' u ∧ u ≤ fcCost m Pa.k ∧
      c'.nreg 8156 = fixPer M Pa ∧
      (∀ s < fixPer M Pa, c'.nmem (S + 6 * m + s) =
        ixOf en m ((tour M Pa.darts)^[s] (Pa.d 0))) ∧
      (∀ i < m, c'.nmem (S + m + i) = labI M en m i + 1) ∧
      (∀ i < m, c'.nmem (S + 2 * m + i) = if en i ∈ Pa.darts then 1 else 0) ∧
      (∀ i < m, c'.nmem (S + 5 * m + i) = ixOf en m (tour M Pa.darts (en i))) ∧
      c'.nreg 8157 = (fixCornerL M Pa).length ∧
      (∀ r < (fixCornerL M Pa).length,
        c'.nmem (S + 8 * m + r) = (fixCornerL M Pa).getD r 0 ∧
        c'.nmem (S + 7 * m + r) =
          ixOf en m ((tour M Pa.darts)^[(fixCornerL M Pa).getD r 0] (Pa.d 0))) ∧
      (∀ i < m, M.face (en i) ∈ Pa.faces → ∃ r < (fixCornerL M Pa).length,
        c'.nmem (S + 9 * m - 1 + (labI M en m i + 1)) = r ∧
        fixCorner M Pa ((fixCornerL M Pa).getD r 0) = M.face (en i)) ∧
      (∀ a, (a < S ∨ S + 10 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ FcScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set rv : ℕ → ℕ := fun i => c.nmem (RVb + i) with hrvd
  set rt : ℕ → ℕ := fun i => c.nmem (RTb + i) with hrtd
  set pm : ℕ → ℕ := fun j => c.nmem (Pb + j) with hpmd
  have hrv' : ∀ i < m, rv i < m ∧ en (rv i) = M.rev (en i) := hrv
  have hrt' : ∀ i < m, rt i < m ∧ en (rt i) = M.rot (en i) := hrt
  have hpm' : ∀ j < Pa.k, pm j < m ∧ en (pm j) = Pa.d j := hpd
  have pTA := taF_permOn h hrv' hrt' hpm'
  have eNX : ∀ x < m, phiI M en m x = rt (rv x) := fun x hx => nx_eq h hrv' hrt' hx
  have pNX : PermOn (fun i => rt (rv i)) m := StEnc.permOn_congr (phi_permOn h) eNX
  have hx0 := (hpm' 0 hk).1
  obtain ⟨c', u, per, ex, hu, h56, hper, hperm, hfix, hmin, hTR, hFL, hLF, hTA, h57, hSel, hM,
    hR, hrr, hrm, ho⟩ := fcProg_run (P := P) c hc r50 r51 r52 r53 r54 r55 (rv := rv) (rt := rt)
    (pm := pm) hk (fun i hi => ⟨rfl, (hrv i hi).1⟩) (fun i hi => ⟨rfl, (hrt i hi).1⟩)
    (fun j hj => ⟨rfl, (hpd j hj).1⟩) pNX pTA dRV dRT dP hW wRV wRT wP wk
  set ta := taF rv rt pm Pa.k with hta
  -- the walk is the walk around the path
  have enW : ∀ s, en (ta^[s] (pm 0)) = (tour M Pa.darts)^[s] (Pa.d 0) := fun s => by
    rw [en_taF_iter h hrv' hrt' hpm' hx0 s, (hpm' 0 hk).2]
  have wlt : ∀ s, ta^[s] (pm 0) < m := fun s => OrbLab.iter_lt pTA hx0 s
  have ixW : ∀ s, ta^[s] (pm 0) = ixOf en m ((tour M Pa.darts)^[s] (Pa.d 0)) := fun s =>
    ix_unique h (wlt s) (enW s)
  have faceW : ∀ s, M.face (en (ta^[s] (pm 0))) = fixCorner M Pa s := fun s => by
    rw [enW]; rfl
  -- the period
  have hperEq : per = fixPer M Pa := by
    have hp : IsPeriodicPt (tour M Pa.darts) per (Pa.d 0) := by
      unfold IsPeriodicPt IsFixedPt
      rw [← (hpm' 0 hk).2, ← en_taF_iter h hrv' hrt' hpm' hx0 per, hfix]
    have hle : fixPer M Pa ≤ per := hp.minimalPeriod_le hper
    have hpos := fixPer_pos Pa
    by_contra hne
    have hlt : fixPer M Pa < per := lt_of_le_of_ne hle (Ne.symm hne)
    have hq : (tour M Pa.darts)^[fixPer M Pa] (Pa.d 0) = Pa.d 0 :=
      isPeriodicPt_minimalPeriod _ _
    refine hmin _ hpos hlt (h.inj _ (wlt _) _ hx0 ?_)
    rw [enW, (hpm' 0 hk).2, hq]
  subst hperEq
  -- the labels
  have eFL : ∀ i < m, flF rv rt i = labI M en m i + 1 := fun i hi => by
    unfold flF labI; rw [StEnc.olab_congr (phi_permOn h) eNX hi]
  have eLF : ∀ i < m, mkSet pm rv Pa.k i ↔ en i ∈ Pa.darts := fun i hi =>
    mkSet_iff h hrv' hpm' hi
  -- the selection is the list of the corners
  have hsel : ∀ s, qsel (fun s => ta^[s] (pm 0)) (flF rv rt) (fpF rv rt pm m Pa.k) s =
      cornerQ M Pa s := by
    intro s
    have e1 : fpF rv rt pm m Pa.k (flF rv rt (ta^[s] (pm 0))) = 1 ↔
        fixCorner M Pa s ∈ Pa.faces := by
      unfold fpF
      rw [eFL _ (wlt s)]
      constructor
      · intro hx
        split_ifs at hx with hc'
        · obtain ⟨i, hi, hiL, hil⟩ := hc'
          rw [eFL i hi] at hil
          have hf : M.face (en i) = M.face (en (ta^[s] (pm 0))) :=
            (face_eq_iff h hi (wlt s)).2 (by omega)
          rw [← faceW s, ← hf]
          exact SPath.face_mem _ ((eLF i hi).1 hiL)
      · intro hx
        obtain ⟨e, he, hfe⟩ := List.mem_map.1 (List.mem_toFinset.1 hx)
        obtain ⟨i, hi, rfl⟩ := h.surj e
        have hex : ∃ i < m, mkSet pm rv Pa.k i ∧ flF rv rt i = labI M en m (ta^[s] (pm 0)) + 1 := by
          refine ⟨i, hi, (eLF i hi).2 he, ?_⟩
          rw [eFL i hi]
          have := (face_eq_iff h hi (wlt s)).1 (by rw [faceW]; exact hfe)
          omega
        rw [iteT hex]
    have e2 : ∀ s', flF rv rt (ta^[s'] (pm 0)) ≠ flF rv rt (ta^[s] (pm 0)) ↔
        fixCorner M Pa s' ≠ fixCorner M Pa s := fun s' => by
      rw [eFL _ (wlt s'), eFL _ (wlt s), ← faceW s', ← faceW s]
      have := face_eq_iff h (wlt s') (wlt s)
      constructor
      · intro h1 h2; exact h1 (by rw [this.1 h2])
      · intro h1 h2; exact h1 (this.2 (by omega))
    rw [Bool.eq_iff_iff, qsel_iff, cornerQ, decide_eq_true_iff, e1]
    exact and_congr_right fun _ => forall₂_congr fun s' _ => e2 s'
  have hselL : selL (fun s => ta^[s] (pm 0)) (flF rv rt) (fpF rv rt pm m Pa.k) (fixPer M Pa) =
      fixCornerL M Pa := by
    unfold selL fixCornerL
    exact List.filter_congr fun s _ => hsel s
  rw [hselL] at h57 hSel
  obtain ⟨-, -, -, -, hcov⟩ := fixCornerL_spec hrot Pa
  refine ⟨c', u, ex, hu, h56, fun s hs => by rw [hTR s hs, ixW], fun i hi => by
      rw [hFL i hi, eFL i hi],
    fun i hi => by rw [hLF i hi]; exact if_congr (eLF i hi) rfl rfl,
    fun i hi => by
      rw [hTA i hi]
      exact ix_unique h (en_taF h hrv' hrt' hpm' hi).1 (en_taF h hrv' hrt' hpm' hi).2, h57,
    fun r hr => ⟨(hSel r hr).1, by rw [(hSel r hr).2.1, ixW]⟩, fun i hi hf => ?_,
    hM, hR, hrr, hrm, ho⟩
  obtain ⟨r, hr, hre⟩ := hcov _ hf
  refine ⟨r, hr, ?_, hre⟩
  have h3 := (hSel r hr).2.2
  rw [eFL _ (wlt _)] at h3
  have hl : labI M en m (ta^[(fixCornerL M Pa).getD r 0] (pm 0)) = labI M en m i :=
    (face_eq_iff h (wlt _) hi).1 (by rw [faceW, hre])
  rw [hl] at h3
  exact h3

end MsEnc

end BKMNW

end PlanarFlow
