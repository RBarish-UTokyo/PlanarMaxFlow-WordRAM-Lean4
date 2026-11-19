module

public import PlanarFlow.BKMNW.Nf7dB

/-!
# The data of the stage loop at a node call: corners, arc ends, the image of step 2

* `SLx.frImgB0` (the image input of step 2, prices/lengths/root `0`, meets `FrImgB`),
  **`SLx.img_of_st2`**: the image written by step 2 (`ImgAt` of `img0`, `ZeroAt` of the rest of the
  zero area) is the stage loop's `SLx.Img`;
* **`mkX_card`** (`b = #πj.faces`), **`mkX_et`** (the arc ends `ET`, `EH` of `mkX` are the corner
  numbers `ix` of the prologue), `mkX_bt` (the corner darts).
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
  WordRAM WordRAM.Machine WordRAM.Programs

section Img

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- The image input of step 2 meets `FrImgB`. -/
lemma SLx.frImgB0 {X : SLx M} {W : ℕ} (hG : X.Good W) :
    MsCall.FrImgB X.b X.Dm (fun _ => 0) 0 (2 * X.P.k) X.ET X.EH (fun _ => 0) X.L where
  b_pos := SLx.b_pos hG
  r_lt := SLx.b_pos hG
  et _ ha := SLx.ET_lt hG ha
  eh _ ha := SLx.EH_lt hG ha
  dm := hG.dmL
  pm _ _ := by simp
  lz _ _ := by simp

/-- **The image of step 2 is the stage loop's resident image.** -/
theorem SLx.img_of_st2 {X : SLx M} {W Wz : ℕ} (hG : X.Good W) {nm : ℕ → ℕ}
    (hI : ImgAt nm (img0 X.b X.Dm X.ET X.EH X.P.k) X.L (lySb X.b X.P.k) (wfOf X.b X.P.k) X.SH)
    (hZ : ZeroAt nm Wz (lySb X.b X.P.k) (wfOf X.b X.P.k) X.SH) (hWz : X.SH + X.WN ≤ Wz)
    (hWf : X.Wf = wfOf X.b X.P.k) : X.Img nm := by
  have hB := SLx.frImgB0 hG
  refine ⟨fun _ => 0, 0, fun _ => 0, hB, fun a ha => ?_⟩
  have hL := MsCall.frPrm_lay hB
  have esb := SLx.prm_sb hG (fun _ => 0) 0 (fun _ => 0)
  have eW := SLx.prm_W hG (fun _ => 0) 0 (fun _ => 0)
  have e : (FrFix.frCfgN (X.prm (fun _ => 0) 0 (fun _ => 0)) X.L).nmem a =
      if a < (X.prm (fun _ => 0) 0 (fun _ => 0)).sb then
        FrFix.frNM (X.prm (fun _ => 0) 0 (fun _ => 0)) a
      else if (X.prm (fun _ => 0) 0 (fun _ => 0)).W + 1 ≤ a ∧
          a < (X.prm (fun _ => 0) 0 (fun _ => 0)).W + 1 + (X.prm (fun _ => 0) 0 (fun _ => 0)).sb then
        FrFix.frRS (X.prm (fun _ => 0) 0 (fun _ => 0)) X.L
          (a - ((X.prm (fun _ => 0) 0 (fun _ => 0)).W + 1)) else 0 :=
    FrFix.frCfgN_nmem hL a
  have e0 : X.prm (fun _ => 0) 0 (fun _ => 0) = img0 X.b X.Dm X.ET X.EH X.P.k := rfl
  rw [esb, eW] at e
  rw [e]
  have hsb : X.lb + 2 * X.P.k = lySb X.b X.P.k := by unfold SLx.lb lySb; omega
  have h2sb := X.two_sb_le
  have hWN : 2 * X.Wf + 1 ≤ X.WN := by unfold SLx.WN; omega
  have hl1 := hG.l1
  rw [hsb] at h2sb ⊢
  rw [hWf] at hWN h2sb ⊢
  by_cases h1 : a < lySb X.b X.P.k
  · rw [if_pos h1, e0]
    exact ⟨(hI a h1).1, (hI a h1).2.1⟩
  rw [if_neg h1]
  by_cases h2 : wfOf X.b X.P.k + 1 ≤ a ∧ a < wfOf X.b X.P.k + 1 + lySb X.b X.P.k
  · rw [if_pos h2, e0]
    obtain ⟨-, -, i3, i4⟩ := hI (a - (wfOf X.b X.P.k + 1)) (by omega)
    rw [show wfOf X.b X.P.k + 1 + (a - (wfOf X.b X.P.k + 1)) = a by omega] at i3
    rw [show X.SH + (wfOf X.b X.P.k + 1) + (a - (wfOf X.b X.P.k + 1)) = X.SH + a by omega] at i4
    exact ⟨i3, i4⟩
  rw [if_neg h2]
  refine ⟨hZ a (by omega) h1 (by omega) h2 (by omega), hZ (X.SH + a) (by omega) (by omega)
    (by omega) (by omega) (by omega)⟩

end Img

section Call

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ}

/-- The corners of `mkX` and their indices: `β` injective on `[0, b)` onto the faces along the path,
`idx` its inverse there. -/
lemma mkX_corners (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hrot : (pmap hP).RotTrans) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb mem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z mem).k) (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
    (hk0 : 0 < πj.k) (f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ) (Q : ℕ) :
    let q := callIn d m Gb π j Z mem
    let X := mkX hP hl hm πj f₀ q Q
    (∀ y < q.cw.cnt, X.β y ∈ πj.faces) ∧
    (∀ y < q.cw.cnt, ∀ y' < q.cw.cnt, X.β y = X.β y' → y = y') ∧
    (∀ f ∈ πj.faces, X.idx f < q.cw.cnt ∧ X.β (X.idx f) = f) ∧
    (∀ i (hi : i < m), (pmap hP).face (vDart hl hi) ∈ πj.faces →
      X.idx ((pmap hP).face (vDart hl hi)) = q.ix i) := by
  classical
  intro q X
  obtain ⟨c1, -, c3, c4, c5⟩ := callIn_corners hl hP hS hj hk hd hrot hk0
  have c3' : ∀ y < q.cw.cnt, ∀ y' < q.cw.cnt, X.β y = X.β y' → y = y' := c3
  have c4' : ∀ f ∈ πj.faces, ∃ y < q.cw.cnt, X.β y = f := c4
  have hidx : ∀ y ∈ πj.faces, X.idx y < q.cw.cnt ∧ X.β (X.idx y) = y := fun y hy => by
    have h := c4' y hy
    show (if h : ∃ x < q.cw.cnt, X.β x = y then Classical.choose h else 0) < q.cw.cnt ∧
      X.β (if h : ∃ x < q.cw.cnt, X.β x = y then Classical.choose h else 0) = y
    rw [dif_pos h]
    exact Classical.choose_spec h
  refine ⟨fun y hy => (c1 y hy).2.2, c3', hidx, fun i hi hf => ?_⟩
  have h5 := c5 i hi hf
  exact c3' _ (hidx _ hf).1 _ h5.1 ((hidx _ hf).2.trans h5.2.symm)

/-- **The number of corners is the number of faces along the path.** -/
theorem mkX_card (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hrot : (pmap hP).RotTrans) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb mem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z mem).k) (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
    (hk0 : 0 < πj.k) : (callIn d m Gb π j Z mem).cw.cnt = πj.faces.card := by
  classical
  obtain ⟨c1, c2, c3, -⟩ := mkX_corners hP hl hm hrot hS hj hk hd hk0 (fun _ => 0) 0
  set q := callIn d m Gb π j Z mem
  set X := mkX hP hl hm πj (fun _ => 0) q 0
  have h1 : ((range q.cw.cnt).image X.β).card = q.cw.cnt := by
    rw [card_image_of_injOn (fun a ha b hb e => c2 a (mem_range.1 ha) b (mem_range.1 hb) e),
      card_range]
  have h2 : (range q.cw.cnt).image X.β = πj.faces := by
    ext f
    simp only [mem_image, mem_range]
    exact ⟨fun ⟨a, ha, e⟩ => e ▸ c1 a ha, fun hf => ⟨X.idx f, (c3 f hf).1, (c3 f hf).2⟩⟩
  rw [← h2, h1]

/-- **The arc ends of `mkX` are the corner numbers of the prologue.** -/
theorem mkX_et (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hrot : (pmap hP).RotTrans) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb mem) (hj : j < π.segs.length) {πj : SPath (pmap hP)}
    (hk : πj.k = (callIn d m Gb π j Z mem).k) (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
    (hk0 : 0 < πj.k) (f₀ : SDart (pdarts M x.1.piece x.2.1) → ℤ) (Q : ℕ) :
    let q := callIn d m Gb π j Z mem
    let X := mkX hP hl hm πj f₀ q Q
    ∀ l < q.k, X.ET (2 * l) = q.ix (q.PD l) ∧ X.ET (2 * l + 1) = q.ix (q.RV (q.PD l)) ∧
      X.EH (2 * l) = q.ix (q.RV (q.PD l)) ∧ X.EH (2 * l + 1) = q.ix (q.PD l) := by
  intro q X l hl'
  obtain ⟨-, -, -, c4⟩ := mkX_corners hP hl hm hrot hS hj hk hd hk0 f₀ Q
  have hlk : l < πj.k := hk ▸ hl'
  obtain ⟨hPD, hv⟩ := callIn_pdv hl hP hS hj hk hd hlk
  have hr := hl.rv _ hPD
  have hRV : q.RV (q.PD l) = mem (d + 4 + m + q.PD l) := rfl
  have hvr : vDart hl hr.1 = (pmap hP).rev (πj.d l) := Subtype.ext (by
    show en _ = M.rev (πj.d l).1
    rw [hr.2, ← hv]; rfl)
  have hdl : (pmap hP).face (πj.d l) ∈ πj.faces := πj.face_mem (by
    rw [SPath.mem_darts]; exact ⟨l, hlk, Or.inl rfl⟩)
  have hdr : (pmap hP).face ((pmap hP).rev (πj.d l)) ∈ πj.faces := πj.face_mem (by
    rw [SPath.mem_darts]; exact ⟨l, hlk, Or.inr rfl⟩)
  have e0 : dartAt πj (2 * l) = πj.d l := by simp [dartAt]
  have e1 : dartAt πj (2 * l + 1) = (pmap hP).rev (πj.d l) := by
    simp only [dartAt]
    rw [if_neg (by omega), show (2 * l + 1) / 2 = l by omega]
  have hA : X.idx ((pmap hP).face (πj.d l)) = q.ix (q.PD l) := by
    have := c4 _ hPD (by rw [hv]; exact hdl)
    rwa [hv] at this
  have hB : X.idx ((pmap hP).face ((pmap hP).rev (πj.d l))) = q.ix (q.RV (q.PD l)) := by
    have := c4 _ hr.1 (by rw [hvr]; exact hdr)
    rwa [hvr, ← hRV] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · show X.idx ((pmap hP).face (dartAt πj (2 * l))) = _
    rw [e0, hA]
  · show X.idx ((pmap hP).face (dartAt πj (2 * l + 1))) = _
    rw [e1, hB]
  · show X.idx ((pmap hP).face ((pmap hP).rev (dartAt πj (2 * l)))) = _
    rw [e0, hB]
  · show X.idx ((pmap hP).face ((pmap hP).rev (dartAt πj (2 * l + 1)))) = _
    rw [e1, (pmap hP).rev_rev, hA]

end Call

end BKMNW

end PlanarFlow
