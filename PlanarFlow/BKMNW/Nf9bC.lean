module

public import PlanarFlow.BKMNW.Nf9bB

/-!
# The data of the stage loop on a frame of any map and its hypotheses

`mkX`/`mkX_good` (`Nf7cP`) and `mkX_corners`, `mkX_card`, `mkX_et` (`Nf7dC`) for
the frame `MFr` of an arbitrary map `M`, with an **arbitrary MSSP subroutine** `mssp` meeting
`MSSPSpecAt` and an arbitrary natural matrix `Dm` holding its answers at the corners:

* `ddg_val`: at the corners of the path, the answers of any `mssp` meeting `MSSPSpecAt` are values
  in `[0, absSum c]`;
* **`mkY M en πj c f₀ mssp Dm q Q : SLx M`** (corners `β x = face (en (bt x))` of the walk,
  `K = 16 fpB`, `B = fpB`, `L = 8 fpB`, the layout of the prologue and of step 2);
* **`mkY_good`**, `mkY_corners`, **`mkY_card`**, **`mkY_et`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace F9b

open Finset Function Equiv Orbit CombMap OrbLab MfDrv NcFz SPath

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The answers of an MSSP subroutine at the corners** are values in `[0, absSum c]`. -/
theorem ddg_val (P : SPath M) {mssp : List D → (D → ℤ) → F → F → Option ℤ}
    (hmssp : MSSPSpecAt M mssp P) {c f₀ : D → ℤ} (hf₀ : IsPseudo M c f₀) {i : ℕ}
    (hi : fixCorner M P i ∈ P.faces) (j : ℕ) :
    ∃ a, 0 ≤ a ∧ a ≤ absSum c ∧
      mssp P.darts (c - f₀) (fixCorner M P i) (fixCorner M P j) = some a := by
  classical
  have hnn : ∀ e, 0 ≤ (c - f₀) e := fun e => by
    simp only [Pi.sub_apply]; linarith [hf₀.le_cap e]
  obtain ⟨a, ha⟩ := fixDDG_some P hmssp (fun e _ => hnn e) hi j
  have hD := hmssp (c - f₀) (fun e _ => hnn e) _ hi
  obtain ⟨h0, h1⟩ := hD.le_sum_len (fun x => hnn x.1) ha
  have h2 : ∑ x : {e // e ∉ P.darts}, (c - f₀) x.1 ≤ ∑ e, (c - f₀) e := by
    rw [← Finset.sum_subtype (univ.filter fun e => e ∉ P.darts) (by simp)]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun e _ _ => hnn e
  have h3 : ∑ e, (c - f₀) e = ∑ e, c e := by
    simp only [Pi.sub_apply, sum_sub_distrib, sum_univ_antisymm hf₀.antisymm, sub_zero]
  have h4 : ∑ e, c e ≤ absSum c := sum_le_sum fun e _ => le_abs_self _
  exact ⟨a, h0, h1.trans (h2.trans (h3 ▸ h4)), ha⟩

open Classical in
/-- **The data of the stage loop on a frame of any map.** -/
noncomputable def mkY (M : CombMap D V F) (en : ℕ → D) (πj : SPath M) (c f₀ : D → ℤ)
    (mssp : List D → (D → ℤ) → F → F → Option ℤ) (Dm : ℕ → ℕ → ℕ) (q : FpIn) (Q : ℕ) :
    SLx M where
  P := πj
  c := c
  f₀ := f₀
  mssp := mssp
  fr := frRef _
  b := q.cw.cnt
  β := fun x => M.face (en (q.cw.bt x))
  idx := fun y => if h : ∃ x < q.cw.cnt, M.face (en (q.cw.bt x)) = y then Classical.choose h else 0
  Dm := Dm
  K := q.K
  B := fpB q.AS q.m q.k
  L := 8 * fpB q.AS q.m q.k
  CWb := Q
  CRb := Q + q.k
  F0b := Q + q.k + q.k + q.k + q.k + q.k
  DVb := Q + q.k + q.k + q.k + q.k + q.k + q.k
  FWb := Q + q.k + q.k
  ETb := Q + q.k + q.k + q.k + q.k + q.k + q.k + q.k
  SIb := lySI (Q + 15 * q.k) q.cw.cnt q.k
  PWb := Q + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k
  PRb := Q + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k + q.k
  ELb := Q + q.k + q.k + q.k
  SH := shOf q.cw.cnt q.k (8 * fpB q.AS q.m q.k)
  Ob := lyOb (Q + 15 * q.k) q.cw.cnt q.k
  p := lyP (Q + 15 * q.k) q.cw.cnt q.k

variable {en : ℕ → D} {m Z d : ℕ} {cap f₀ : D → ℤ} {mem : ℕ → ℕ}
  {segs : List (SPath M)} {lo hi Gb j : ℕ}

section Good

variable (hL : MFr M en m Z cap f₀ d mem) (hS : SegsL M en m segs lo hi Gb mem)
  (hj : j < segs.length) {πj : SPath M} (hk : πj.k = (cIn d m Gb segs j Z mem).k)
  (hd : ∀ l < πj.k, πj.d l = (segs[j]).d l)
include hL hS hj hk hd

/-- The corners of `mkY` and their indices. -/
lemma mkY_corners (hrot : M.RotTrans) (hft : M.FaceTrans) (hk0 : 0 < πj.k)
    (mssp : List D → (D → ℤ) → F → F → Option ℤ) (Dm : ℕ → ℕ → ℕ) (Q : ℕ) :
    let q := cIn d m Gb segs j Z mem
    let X := mkY M en πj cap f₀ mssp Dm q Q
    (∀ y < q.cw.cnt, X.β y ∈ πj.faces) ∧
    (∀ y < q.cw.cnt, ∀ y' < q.cw.cnt, X.β y = X.β y' → y = y') ∧
    (∀ f ∈ πj.faces, X.idx f < q.cw.cnt ∧ X.β (X.idx f) = f) ∧
    (∀ i < m, M.face (en i) ∈ πj.faces → X.idx (M.face (en i)) = q.ix i) := by
  classical
  intro q X
  obtain ⟨c1, -, c3, c4, c5⟩ := cIn_corners hL hS hj hk hd hrot hft hk0
  have c3' : ∀ y < q.cw.cnt, ∀ y' < q.cw.cnt, X.β y = X.β y' → y = y' := c3
  have c4' : ∀ f ∈ πj.faces, ∃ y < q.cw.cnt, X.β y = f := c4
  have hidx : ∀ y ∈ πj.faces, X.idx y < q.cw.cnt ∧ X.β (X.idx y) = y := fun y hy => by
    have h := c4' y hy
    show (if h : ∃ x < q.cw.cnt, X.β x = y then Classical.choose h else 0) < q.cw.cnt ∧
      X.β (if h : ∃ x < q.cw.cnt, X.β x = y then Classical.choose h else 0) = y
    rw [dif_pos h]
    exact Classical.choose_spec h
  refine ⟨fun y hy => (c1 y hy).2.2.2, c3', hidx, fun i hi hf => ?_⟩
  have h5 := c5 i hi hf
  exact c3' _ (hidx _ hf).1 _ h5.1 ((hidx _ hf).2.trans h5.2.symm)

/-- **The number of corners is the number of faces along the path.** -/
theorem mkY_card (hrot : M.RotTrans) (hft : M.FaceTrans) (hk0 : 0 < πj.k) :
    (cIn d m Gb segs j Z mem).cw.cnt = πj.faces.card := by
  classical
  obtain ⟨c1, c2, c3, -⟩ := mkY_corners hL hS hj hk hd hrot hft hk0 (fun _ _ _ _ => none)
    (fun _ _ => 0) 0
  set q := cIn d m Gb segs j Z mem
  set X := mkY M en πj cap f₀ (fun _ _ _ _ => none) (fun _ _ => 0) q 0
  have h1 : ((range q.cw.cnt).image X.β).card = q.cw.cnt := by
    rw [card_image_of_injOn (fun a ha b hb e => c2 a (mem_range.1 ha) b (mem_range.1 hb) e),
      card_range]
  have h2 : (range q.cw.cnt).image X.β = πj.faces := by
    ext f
    simp only [mem_image, mem_range]
    exact ⟨fun ⟨a, ha, e⟩ => e ▸ c1 a ha, fun hf => ⟨X.idx f, (c3 f hf).1, (c3 f hf).2⟩⟩
  rw [← h2, h1]

/-- **The arc ends of `mkY` are the corner numbers of the prologue.** -/
theorem mkY_et (hrot : M.RotTrans) (hft : M.FaceTrans) (hk0 : 0 < πj.k)
    (mssp : List D → (D → ℤ) → F → F → Option ℤ) (Dm : ℕ → ℕ → ℕ) (Q : ℕ) :
    let q := cIn d m Gb segs j Z mem
    let X := mkY M en πj cap f₀ mssp Dm q Q
    ∀ l < q.k, X.ET (2 * l) = q.ix (q.PD l) ∧ X.ET (2 * l + 1) = q.ix (q.RV (q.PD l)) ∧
      X.EH (2 * l) = q.ix (q.RV (q.PD l)) ∧ X.EH (2 * l + 1) = q.ix (q.PD l) := by
  intro q X l hl'
  obtain ⟨-, -, -, c4⟩ := mkY_corners hL hS hj hk hd hrot hft hk0 mssp Dm Q
  have hlk : l < πj.k := hk ▸ hl'
  obtain ⟨hPD, hv⟩ := cIn_pdv hL hS hj hk hd hlk
  have hr := hL.rv _ hPD
  have hRV : q.RV (q.PD l) = mem (d + 4 + m + q.PD l) := rfl
  have hvr : en (mem (d + 4 + m + q.PD l)) = M.rev (πj.d l) := by rw [hr.2, hv]
  have hdl : M.face (πj.d l) ∈ πj.faces := πj.face_mem (by
    rw [SPath.mem_darts]; exact ⟨l, hlk, Or.inl rfl⟩)
  have hdr : M.face (M.rev (πj.d l)) ∈ πj.faces := πj.face_mem (by
    rw [SPath.mem_darts]; exact ⟨l, hlk, Or.inr rfl⟩)
  have e0 : dartAt πj (2 * l) = πj.d l := by simp [dartAt]
  have e1 : dartAt πj (2 * l + 1) = M.rev (πj.d l) := by
    simp only [dartAt]
    rw [if_neg (by omega), show (2 * l + 1) / 2 = l by omega]
  have hA : X.idx (M.face (πj.d l)) = q.ix (q.PD l) := by
    have := c4 _ hPD (by rw [hv]; exact hdl)
    rwa [hv] at this
  have hB : X.idx (M.face (M.rev (πj.d l))) = q.ix (q.RV (q.PD l)) := by
    have := c4 _ hr.1 (by rw [hvr]; exact hdr)
    rwa [hvr, ← hRV] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · show X.idx (M.face (dartAt πj (2 * l))) = _
    rw [e0, hA]
  · show X.idx (M.face (dartAt πj (2 * l + 1))) = _
    rw [e1, hB]
  · show X.idx (M.face (M.rev (dartAt πj (2 * l)))) = _
    rw [e0, hB]
  · show X.idx (M.face (M.rev (dartAt πj (2 * l + 1)))) = _
    rw [e1, M.rev_rev, hA]

/-- The corner words of the walk are frame indices. -/
lemma cIn_bt_lt (hk0 : 0 < (cIn d m Gb segs j Z mem).k) {y : ℕ}
    (hy : y < (cIn d m Gb segs j Z mem).cw.cnt) : (cIn d m Gb segs j Z mem).cw.bt y < m := by
  obtain ⟨-, -, -, -, -, -, hSG, hNX, hPD⟩ := cIn_pre hL hS hj
  set q := cIn d m Gb segs j Z mem
  have h0 : ∀ a, q.MK0 a ≤ 1 := fun a => by
    simp only [FpIn.MK0]; split_ifs
    · exact fmk2_le_one
    · omega
  have hI := cwRun_inv (fun n => q.lab (q.tt n)) q.tt q.MK0 h0 q.m
  have := (hI.st_lt y hy).2
  change q.cw.bt y = q.tt (q.cw.st y) at this
  rw [this]
  exact q.tt_lt hSG hNX (hPD 0 hk0) _

set_option maxHeartbeats 4000000 in
/-- **The hypotheses of the stage loop hold for `mkY`**, for any MSSP subroutine meeting
`MSSPSpecAt` whose answers at the corners are held by `Dm`. -/
theorem mkY_good (hpl : M.IsPlane) (hrot : M.RotTrans) (hft : M.FaceTrans) (hk0 : 0 < πj.k)
    (hf₀ : IsPseudo M cap f₀) {mssp : List D → (D → ℤ) → F → F → Option ℤ}
    (hmssp : MSSPSpecAt M mssp πj) {Dm : ℕ → ℕ → ℕ}
    (hDm : ∀ i < (cIn d m Gb segs j Z mem).cw.cnt, ∀ i' < (cIn d m Gb segs j Z mem).cw.cnt,
      ∀ a, mssp πj.darts (cap - f₀) (M.face (en ((cIn d m Gb segs j Z mem).cw.bt i)))
        (M.face (en ((cIn d m Gb segs j Z mem).cw.bt i'))) = some a → 0 ≤ a → (Dm i i' : ℤ) = a)
    {Q W : ℕ}
    (hl2 : (mkY M en πj cap f₀ mssp Dm (cIn d m Gb segs j Z mem) Q).SH +
      (mkY M en πj cap f₀ mssp Dm (cIn d m Gb segs j Z mem) Q).WN < Q)
    (hl14 : (mkY M en πj cap f₀ mssp Dm (cIn d m Gb segs j Z mem) Q).p +
      (mkY M en πj cap f₀ mssp Dm (cIn d m Gb segs j Z mem) Q).LG ≤ W)
    (hw1 : 16 * (mkY M en πj cap f₀ mssp Dm (cIn d m Gb segs j Z mem) Q).K + 1 ≤ W)
    (hw2 : (mkY M en πj cap f₀ mssp Dm (cIn d m Gb segs j Z mem) Q).Mo +
      3 * (mkY M en πj cap f₀ mssp Dm (cIn d m Gb segs j Z mem) Q).K ≤ W) :
    (mkY M en πj cap f₀ mssp Dm (cIn d m Gb segs j Z mem) Q).Good W := by
  classical
  set q := cIn d m Gb segs j Z mem with hq
  set X := mkY M en πj cap f₀ mssp Dm q Q with hX
  obtain ⟨c1, c2, c3, c4, c5⟩ := cIn_corners hL hS hj hk hd hrot hft hk0
  have hk0' : 0 < q.k := hk ▸ hk0
  have c3' : ∀ y < q.cw.cnt, ∀ y' < q.cw.cnt, X.β y = X.β y' → y = y' := c3
  have c4' : ∀ f ∈ πj.faces, ∃ y < q.cw.cnt, X.β y = f := c4
  have hβF : ∀ y < q.cw.cnt, X.β y = fixCorner M πj (q.cw.st y) := fun y hy => (c1 y hy).2.1
  have hβm : ∀ y < q.cw.cnt, X.β y ∈ πj.faces := fun y hy => (c1 y hy).2.2.2
  have hidx : ∀ y ∈ πj.faces, X.idx y < q.cw.cnt ∧ X.β (X.idx y) = y := fun y hy => by
    have h := c4' y hy
    show (if h : ∃ x < q.cw.cnt, X.β x = y then Classical.choose h else 0) < q.cw.cnt ∧
      X.β (if h : ∃ x < q.cw.cnt, X.β x = y then Classical.choose h else 0) = y
    rw [dif_pos h]
    exact Classical.choose_spec h
  -- the answers at the corners
  have hsome : ∀ i < q.cw.cnt, ∀ i' < q.cw.cnt, ∃ a, 0 ≤ a ∧ a ≤ absSum cap ∧
      mssp πj.darts (cap - f₀) (X.β i) (X.β i') = some a := fun i hi i' hi' => by
    rw [hβF i hi, hβF i' hi']
    exact ddg_val πj hmssp hf₀ (by rw [← hβF i hi]; exact hβm i hi) _
  have hdm : ∀ i < q.cw.cnt, ∀ i' < q.cw.cnt, (X.Dm i i' : ℤ) =
      (mssp πj.darts (cap - f₀) (X.β i) (X.β i')).getD 0 := fun i hi i' hi' => by
    obtain ⟨a, ha0, -, ha⟩ := hsome i hi i' hi'
    rw [ha, Option.getD_some]
    exact hDm i hi i' hi' a ha ha0
  -- sizes and bounds
  have hAS : ((q.AS : ℕ) : ℤ) = absSum cap := cIn_as hL
  have hcard : Fintype.card D = m := hL.card
  have hc0 : ∀ e : D, 0 ≤ cap e := fun e => by
    obtain ⟨i, hi, he⟩ := hL.surj e
    rw [← he, ← (hL.cp i hi).1]; positivity
  have hbk : q.cw.cnt ≤ 2 * q.k := by
    have h1 : ((range q.cw.cnt).image X.β).card = q.cw.cnt := by
      rw [card_image_of_injOn (fun a ha b hb e => c3' a (mem_range.1 ha) b (mem_range.1 hb) e),
        card_range]
    have h2 : (range q.cw.cnt).image X.β ⊆ πj.faces := fun y hy => by
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hy; exact hβm a (mem_range.1 ha)
    have := card_le_card h2
    have := πj.card_faces_le
    omega
  have hAS0 : (0 : ℤ) ≤ q.AS := by positivity
  have hqm : q.m = m := rfl
  have hfpB : ((fpB q.AS q.m q.k : ℕ) : ℤ) =
      ((q.k : ℤ) + 2) * (2 * (q.AS + m * (4 * q.AS + 1))) + 12 * q.AS + 4 := by
    unfold fpB; rw [hqm]; push_cast; ring
  have hY : (0 : ℤ) ≤ (m : ℤ) * (4 * q.AS + 1) := by positivity
  have hASB : (q.AS : ℤ) ≤ fpB q.AS q.m q.k := by rw [hfpB]; nlinarith
  have hWf : X.Wf = wfOf q.cw.cnt q.k := by
    unfold SLx.Wf SLx.lb wfOf lySb
    simp only [hX, mkY]; rw [hk]
  refine
    { plane := hpl
      c_nn := hc0
      pseudo := hf₀
      mssp_spec := hmssp
      fr_spec := frRef_spec _
      k_pos := hk0
      β_mem := hβm
      idx_lt := fun y hy => (hidx y hy).1
      β_idx := fun y hy => (hidx y hy).2
      inj := c3'
      dsome := fun i hi i' hi' => by
        obtain ⟨a, -, -, ha⟩ := hsome i hi i' hi'; exact ⟨a, ha⟩
      dm := hdm
      cross := ?_
      dmL := fun i hi i' hi' => ?_
      bf0 := fun e => ?_
      bdv := fun v => ?_
      bc := ?_
      bst := ?_
      hK := le_of_eq rfl
      hL := le_of_eq rfl
      l1 := ?_
      l2 := hl2
      l3 := ?_
      l4 := ?_
      l5 := ?_
      l6 := ?_
      l7 := ?_
      l8 := ?_
      l9 := ?_
      l10 := ?_
      l11 := ?_
      l12 := ?_
      l13 := ?_
      l14 := hl14
      w1 := hw1
      w2 := hw2 }
  · have hcr := crossing_fixPath hpl hrot πj hmssp hf₀ (b := q.cw.cnt) (s := q.cw.st) c2
      (fun i hi => (c1 i hi).2.2.1) (fun i hi => by rw [← hβF i hi]; exact hβm i hi)
    intro i i' j' j'' h1 h2 h3 h4 h5
    change i' < q.cw.cnt at h3
    change j'' < q.cw.cnt at h4
    have := hcr i i' j' j'' h1 h2 h3 h4 h5
    simp only at this ⊢
    rw [hdm i (by omega) j'' h4, hdm i' h3 j' (by omega), hdm i (by omega) j' (by omega),
      hdm i' h3 j'' h4, hβF i (by omega), hβF i' h3, hβF j' (by omega), hβF j'' h4]
    exact this
  · obtain ⟨a, ha0, ha1, ha⟩ := hsome i hi i' hi'
    have e := hDm i hi i' hi' a ha ha0
    rw [← hAS] at ha1
    have h2 : ((X.Dm i i' : ℕ) : ℤ) ≤ 8 * fpB q.AS q.m q.k := by
      have : ((X.Dm i i' : ℕ) : ℤ) = a := e
      linarith
    exact_mod_cast h2
  · have h1 := abs_le_of_pseudo hf₀ e
    have h2 := abs_le_absSum cap e
    have h3 := abs_le_absSum cap (M.rev e)
    rw [← hAS] at h2 h3
    show |f₀ e| ≤ ((fpB q.AS q.m q.k : ℕ) : ℤ)
    rw [hfpB]; nlinarith
  · have h1 := abs_div_le_sum hc0 hf₀ v
    have h2 : ∑ y : D, cap y ≤ absSum cap := sum_le_sum fun y _ => le_abs_self _
    rw [← hAS] at h2
    show |M.div f₀ v| ≤ ((fpB q.AS q.m q.k : ℕ) : ℤ)
    linarith
  · show 4 * absSum cap + 1 ≤ ((fpB q.AS q.m q.k : ℕ) : ℤ)
    rw [← hAS, hfpB]; nlinarith
  · show 2 * (absSum cap + (4 * absSum cap + 1)) + (πj.k : ℤ) * Bst D cap ≤
      ((fpB q.AS q.m q.k : ℕ) : ℤ)
    unfold Bst
    rw [← hAS, hfpB, hcard, hk]
    nlinarith
  · have e : X.SH = X.WN + 1 := by
      unfold SLx.WN SLx.Mo
      rw [hWf]
      simp only [hX, mkY]
      unfold shOf moOf
      ring
    omega
  all_goals
    simp only [hX, mkY]
    try rw [hk]
    try simp only [lySI, lyOb, lyS, lyA, lyOm, lyP, lyT, lySb]
    try omega

end Good

end F9b

end BKMNW

end PlanarFlow
