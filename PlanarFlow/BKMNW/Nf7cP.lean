module

public import PlanarFlow.BKMNW.Nf7cO

/-!
# The data of the stage loop at a node call and its hypotheses

* **`mkX`**: the `SLx (pmap hP)` of a node call: the part `πj`, the capacities `U`, the flow
  `f₀`, Klein's MSSP and `frRef`, the corners of the prologue (`β x = face (en (bt x))`,
  `idx` its inverse on the faces along the path), the matrix of the MSSP call, `K = 16 fpB`,
  `B = fpB`, `L = 8 fpB`, the layout of the prologue and of step 2;
* `mkX_card`: `b = #πj.faces`; **`mkX_good`**: `(mkX …).Good W` from the frame, the corners
  (`callIn_corners`), the pseudoflow `f₀`, and the layout/word hypotheses.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep SPath
  WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Call

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ}

open Classical in
/-- **The data of the stage loop at a node call.** -/
noncomputable def mkX (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (πj : SPath (pmap hP)) (f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ) (q : FpIn)
    (Q : ℕ) : SLx (pmap hP) where
  P := πj
  c := fun y => u y.1
  f₀ := f₀
  mssp := Klein.msspPlaneK (pmap hP)
  fr := frRef _
  b := q.cw.cnt
  β := fun x => if h : q.cw.bt x < m then (pmap hP).face (vDart hl h) else (pmap hP).face (πj.d 0)
  idx := fun y => if h : ∃ x < q.cw.cnt, (if h : q.cw.bt x < m then (pmap hP).face (vDart hl h)
      else (pmap hP).face (πj.d 0)) = y then Classical.choose h else 0
  Dm := fun i j => MsCall.msW (pmap hP) πj ((fun y => u y.1) - f₀)
    (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm (q.cw.bt i))
    (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm (q.cw.bt j))
  K := q.K
  B := fpB q.AS m q.k
  L := 8 * fpB q.AS m q.k
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
  SH := shOf q.cw.cnt q.k (8 * fpB q.AS m q.k)
  Ob := lyOb (Q + 15 * q.k) q.cw.cnt q.k
  p := lyP (Q + 15 * q.k) q.cw.cnt q.k

/-- The corner words of the walk are frame indices. -/
lemma callIn_bt_lt {π : HSep M} {lo hi Gb j : ℕ} (hL : Lay M gid u S T Z x m en d mem)
    (hS : SegsOut M en m π lo hi Gb mem) (hj : j < π.segs.length)
    (hk0 : 0 < (callIn d m Gb π j Z mem).k) {y : ℕ} (hy : y < (callIn d m Gb π j Z mem).cw.cnt) :
    (callIn d m Gb π j Z mem).cw.bt y < m := by
  obtain ⟨-, -, -, -, -, -, hSG, hNX, hPD⟩ := callIn_pre hL hS hj
  set q := callIn d m Gb π j Z mem
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
/-- **The hypotheses of the stage loop hold for `mkX`.** -/
theorem mkX_good (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hpl : (pmap hP).IsPlane) (hrot : (pmap hP).RotTrans)
    (hface : (pmap hP).FaceTrans) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb mem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z mem).k) (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
    (hk0 : 0 < πj.k) {f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hf₀ : IsPseudo (pmap hP) (fun y => u y.1) f₀) {Q W : ℕ}
    (hl2 : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem) Q).SH +
      (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem) Q).WN < Q)
    (hl14 : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem) Q).p +
      (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem) Q).LG ≤ W)
    (hw1 : 16 * (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem) Q).K + 1 ≤ W)
    (hw2 : (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem) Q).Mo +
      3 * (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem) Q).K ≤ W) :
    (mkX hP hl hm πj f₀ (callIn d m Gb π j Z mem) Q).Good W := by
  classical
  set q := callIn d m Gb π j Z mem with hq
  obtain ⟨c1, c2, c3, c4, c5⟩ := callIn_corners hl hP hS hj hk hd hrot hk0
  have hk0' : 0 < q.k := hk ▸ hk0
  have c3' : ∀ y < q.cw.cnt, ∀ y' < q.cw.cnt, (mkX hP hl hm πj f₀ q Q).β y =
      (mkX hP hl hm πj f₀ q Q).β y' → y = y' := c3
  have c4' : ∀ f ∈ πj.faces, ∃ y < q.cw.cnt, (mkX hP hl hm πj f₀ q Q).β y = f := c4
  have hbt : ∀ y < q.cw.cnt, q.cw.bt y < m := fun y hy => callIn_bt_lt hl hS hj hk0' hy
  set ℓ : SDart (pdarts M x.1.piece x.2.1) → ℤ := (fun y => u y.1) - f₀ with hℓ
  have hnn : ∀ e, 0 ≤ ℓ e := fun e => by
    simp only [hℓ, Pi.sub_apply]; linarith [hf₀.le_cap e]
  have hmssp : MSSPSpecAt (pmap hP) (Klein.msspPlaneK (pmap hP)) πj :=
    fun ℓ' hnn' y hy => Klein.msspPlaneK_spec hpl hrot hface πj ℓ' hnn' y hy
  -- the corner of `x` is the face of the frame dart `bt x`
  have hβE : ∀ y < q.cw.cnt, (mkX hP hl hm πj f₀ q Q).β y = (pmap hP).face
      (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm (q.cw.bt y)) := fun y hy => by
    show (if h : q.cw.bt y < m then (pmap hP).face (vDart hl h) else (pmap hP).face (πj.d 0)) = _
    rw [dif_pos (hbt y hy)]
    congr 1
    exact Subtype.ext (layEn_val (hbt y hy)).symm
  have hβF : ∀ y < q.cw.cnt, (mkX hP hl hm πj f₀ q Q).β y = fixCorner (pmap hP) πj (q.cw.st y) :=
    fun y hy => (c1 y hy).1
  have hβm : ∀ y < q.cw.cnt, (mkX hP hl hm πj f₀ q Q).β y ∈ πj.faces := fun y hy => (c1 y hy).2.2
  have hidx : ∀ y ∈ πj.faces, (mkX hP hl hm πj f₀ q Q).idx y < q.cw.cnt ∧
      (mkX hP hl hm πj f₀ q Q).β ((mkX hP hl hm πj f₀ q Q).idx y) = y := fun y hy => by
    have h := c4' y hy
    show (if h : ∃ x < q.cw.cnt, (mkX hP hl hm πj f₀ q Q).β x = y then Classical.choose h
      else 0) < q.cw.cnt ∧ (mkX hP hl hm πj f₀ q Q).β (if h : ∃ x < q.cw.cnt,
        (mkX hP hl hm πj f₀ q Q).β x = y then Classical.choose h else 0) = y
    rw [dif_pos h]
    exact Classical.choose_spec h
  -- the answers of the MSSP call
  have hsome : ∀ i < q.cw.cnt, ∀ i' < q.cw.cnt, ∃ a, 0 ≤ a ∧
      Klein.msspPlaneK (pmap hP) πj.darts ℓ ((mkX hP hl hm πj f₀ q Q).β i)
        ((mkX hP hl hm πj f₀ q Q).β i') = some a := fun i hi i' hi' => by
    rw [hβF i hi, hβF i' hi']
    exact MsCall.msOut_some hpl hrot hface πj ℓ hnn (by rw [← hβF i hi]; exact hβm i hi) _
  have hdm : ∀ i < q.cw.cnt, ∀ i' < q.cw.cnt, ((mkX hP hl hm πj f₀ q Q).Dm i i' : ℤ) =
      (Klein.msspPlaneK (pmap hP) πj.darts ℓ ((mkX hP hl hm πj f₀ q Q).β i)
        ((mkX hP hl hm πj f₀ q Q).β i')).getD 0 := fun i hi i' hi' => by
    obtain ⟨a, ha0, ha⟩ := hsome i hi i' hi'
    rw [ha, Option.getD_some]
    show ((MsCall.msW (pmap hP) πj ℓ _ _ : ℕ) : ℤ) = a
    rw [hβE i hi, hβE i' hi'] at ha
    exact MsCall.msW_of_some ha0 ha
  -- sizes and bounds
  have hAS : ((q.AS : ℕ) : ℤ) = absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) :=
    callIn_as hl
  have hcard : Fintype.card (SDart (pdarts M x.1.piece x.2.1)) = m := hl.card_sdart
  have hc0 : ∀ e : SDart (pdarts M x.1.piece x.2.1), 0 ≤ u e.1 := fun e => by
    obtain ⟨i, hi, he⟩ := hl.en_surj e.1 e.2
    rw [← he, ← (hl.cp i hi).1]; positivity
  have hbk : q.cw.cnt ≤ 2 * q.k := by
    have h1 : ((range q.cw.cnt).image (mkX hP hl hm πj f₀ q Q).β).card = q.cw.cnt := by
      rw [card_image_of_injOn (fun a ha b hb e => c3' a (mem_range.1 ha) b (mem_range.1 hb) e),
        card_range]
    have h2 : (range q.cw.cnt).image (mkX hP hl hm πj f₀ q Q).β ⊆ πj.faces := fun y hy => by
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hy; exact hβm a (mem_range.1 ha)
    have := card_le_card h2
    have := πj.card_faces_le
    omega
  have hAS0 : (0 : ℤ) ≤ q.AS := by positivity
  have hfpB : ((fpB q.AS m q.k : ℕ) : ℤ) =
      ((q.k : ℤ) + 2) * (2 * (q.AS + m * (4 * q.AS + 1))) + 12 * q.AS + 4 := by
    unfold fpB; push_cast; ring
  have hY : (0 : ℤ) ≤ (m : ℤ) * (4 * q.AS + 1) := by positivity
  have hASB : (q.AS : ℤ) ≤ fpB q.AS m q.k := by rw [hfpB]; nlinarith
  have hWf : (mkX hP hl hm πj f₀ q Q).Wf = wfOf q.cw.cnt q.k := by
    unfold SLx.Wf SLx.lb wfOf lySb
    simp only [mkX]; rw [hk]
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
        obtain ⟨a, -, ha⟩ := hsome i hi i' hi'; exact ⟨a, ha⟩
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
      (fun i hi => (c1 i hi).2.1) (fun i hi => by rw [← hβF i hi]; exact hβm i hi)
    intro i i' j' j'' h1 h2 h3 h4 h5
    change i' < q.cw.cnt at h3
    change j'' < q.cw.cnt at h4
    have := hcr i i' j' j'' h1 h2 h3 h4 h5
    simp only at this ⊢
    rw [hdm i (by omega) j'' h4, hdm i' h3 j' (by omega), hdm i (by omega) j' (by omega),
      hdm i' h3 j'' h4, hβF i (by omega), hβF i' h3, hβF j' (by omega), hβF j'' h4]
    exact this
  · have h1 := msW_le hpl hrot hface πj hf₀ (t := layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm
      (q.cw.bt i)) (t' := layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm (q.cw.bt i'))
      (by rw [← hβE i hi]; exact hβm i hi)
    rw [← hAS] at h1
    have h2 : ((mkX hP hl hm πj f₀ q Q).Dm i i' : ℤ) ≤ 8 * fpB q.AS m q.k := by
      have : ((mkX hP hl hm πj f₀ q Q).Dm i i' : ℤ) ≤ q.AS := h1
      linarith
    exact_mod_cast h2
  · have h1 := abs_le_of_pseudo hf₀ e
    have h2 := abs_le_absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) e
    have h3 := abs_le_absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) ((pmap hP).rev e)
    rw [← hAS] at h2 h3
    show |f₀ e| ≤ ((fpB q.AS m q.k : ℕ) : ℤ)
    rw [hfpB]; nlinarith
  · have h1 := abs_div_le_sum hc0 hf₀ v
    have h2 : ∑ y : SDart (pdarts M x.1.piece x.2.1), u y.1 ≤
        absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) :=
      sum_le_sum fun y _ => le_abs_self _
    rw [← hAS] at h2
    show |(pmap hP).div f₀ v| ≤ ((fpB q.AS m q.k : ℕ) : ℤ)
    linarith
  · show 4 * absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) + 1 ≤
      ((fpB q.AS m q.k : ℕ) : ℤ)
    rw [← hAS, hfpB]; nlinarith
  · show 2 * (absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) +
      (4 * absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) + 1)) +
      (πj.k : ℤ) * Bst (SDart (pdarts M x.1.piece x.2.1)) (fun y => u y.1) ≤
      ((fpB q.AS m q.k : ℕ) : ℤ)
    unfold Bst
    rw [← hAS, hfpB, hcard, hk]
    nlinarith
  · have e : (mkX hP hl hm πj f₀ q Q).SH = (mkX hP hl hm πj f₀ q Q).WN + 1 := by
      unfold SLx.WN SLx.Mo
      rw [hWf]
      simp only [mkX]
      unfold shOf moOf
      ring
    omega
  all_goals
    simp only [mkX]
    try rw [hk]
    try simp only [lySI, lyOb, lyS, lyA, lyOm, lyP, lyT, lySb]
    try omega

end Call

end BKMNW

end PlanarFlow
