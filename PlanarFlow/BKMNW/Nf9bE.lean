module

public import PlanarFlow.BKMNW.Nf9bC

/-!
# The two frames of the frozen fix and the stage data on the map with pendant edges

The setting of `FixFrameSpec`: a base map `M₀` (frame at `d`: `m`, `RV`, `SG`, numbering
`en`), the map with pendant edges `M₀.pendant e he` (frame `MFr` at `d'`, numbering `en'` with
`en' i = inl (en i)` for `i < m`), the parts of a separator of `M₀` on the base numbering.

* **`PCtx`**: these hypotheses bundled (`PCtx.congr`: they depend only on the memory below the
  heap top);
* `take_map_k_lift`, **`cIn_lift`** (the prologue input of the lifted parts is that of the parts),
  **`msspP_lift`**, `dartAt_lift`, `PCtx.segsL'`, `PCtx.rvE` (the pendant `RV` on base indices is the
  base `RV`);
* **`mkP`**: the data of the stage loop on the map with pendant edges, with the MSSP subroutine
  `msspP (msspPlaneK M₀)` (the MSSP of the base map, as `fixFrozen` uses it) and the matrix
  **`DmY`** of its answers at the corners; **`mkP_good`**, `mkP_corners`, `mkP_et`, `mkP_card`.
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
  [Fintype F] [DecidableEq F] {M₀ : CombMap D V F} {e : V → D} {he : ∀ v, M₀.tail (e v) = v}

/-! ### The context -/

/-- **The hypotheses of `FixFrameSpec` on the two frames** (memory `mem`). -/
structure PCtx (M₀ : CombMap D V F) (e : V → D) (he : ∀ v, M₀.tail (e v) = v) (en : ℕ → D)
    (en' : ℕ → D ⊕ (V × Bool)) (m m' Z' d d' : ℕ) (cap f₀ : D ⊕ (V × Bool) → ℤ)
    (segs : List (SPath M₀)) (lo hi Gb j : ℕ) (mem : ℕ → ℕ) : Prop where
  pl : M₀.IsPlane
  rot : M₀.RotTrans
  ft : M₀.FaceTrans
  enum : NsStep.EnumOK M₀ en m
  hen : ∀ i < m, en' i = .inl (en i)
  bm : mem d = m
  brv : ∀ i < m, mem (d + 4 + m + i) < m ∧ en (mem (d + 4 + m + i)) = M₀.rev (en i)
  bsg : ∀ i < m, mem (d + 4 + 2 * m + i) < m ∧ en (mem (d + 4 + 2 * m + i)) = M₀.next (M₀.rev (en i))
  fr : MFr (M₀.pendant e he) en' m' Z' cap f₀ d' mem
  mm : m ≤ m'
  m0 : 0 < m
  sl : SegsL M₀ en m segs lo hi Gb mem
  hj : j < segs.length
  pseudo : IsPseudo (M₀.pendant e he) cap f₀
  capnn : ∀ y, 0 ≤ cap y

variable {en : ℕ → D} {en' : ℕ → D ⊕ (V × Bool)} {m m' Z' d d' : ℕ}
  {cap f₀ : D ⊕ (V × Bool) → ℤ} {segs : List (SPath M₀)} {lo hi Gb j : ℕ} {mem : ℕ → ℕ}

/-- The context depends only on the memory of the frames and the parts. -/
lemma PCtx.congr (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem)
    {mem' : ℕ → ℕ} {A0 Wz : ℕ} (hfr : d' + 4 + 7 * m' ≤ A0) (hb : d + 4 + 3 * m ≤ A0)
    (hhi : hi ≤ A0) (hwd : Wz < d) (hwd' : Wz < d') (hwl : Wz < lo)
    (he' : ∀ a, Wz < a → a < A0 → mem' a = mem a) :
    PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem' := by
  obtain ⟨h1, h2, h3, h4⟩ := H.sl
  have hs : ∀ a, Gb ≤ a → a < hi → mem' a = mem a := fun a h0 ha => he' a (by omega) (by omega)
  refine ⟨H.pl, H.rot, H.ft, H.enum, H.hen, ?_, fun i hi' => ?_, fun i hi' => ?_,
    H.fr.congr fun a h0 ha => he' a (by omega) (by omega), H.mm, H.m0, ?_, H.hj, H.pseudo,
    H.capnn⟩
  · rw [he' _ (by omega) (by have := H.m0; omega)]; exact H.bm
  · rw [he' _ (by omega) (by omega)]; exact H.brv i hi'
  · rw [he' _ (by omega) (by omega)]; exact H.bsg i hi'
  · refine ⟨h1, by rw [hs _ le_rfl (by omega)]; exact h2, h3, fun j' hj' => ?_⟩
    obtain ⟨g1, g2, g3, g4, g5⟩ := h4 j' hj'
    have hs1 : ((segs.take j').map SPath.k).sum + (segs[j']).k ≤ (segs.map SPath.k).sum := by
      have e : segs.take (j' + 1) = segs.take j' ++ [segs[j']] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj']; rfl
      have := sum_take_le_sum (segs.map SPath.k) (j' + 1)
      rw [← List.map_take, e, List.map_append, List.sum_append] at this
      simpa using this
    refine ⟨by rw [hs _ (by omega) (by omega)]; exact g1, by rw [hs _ (by omega) (by omega)]; exact g2,
      fun l hl => ?_, by rw [hs _ (by omega) (by omega)]; exact g4,
      by rw [hs _ (by omega) (by omega)]; exact g5⟩
    rw [hs _ (by omega) (by omega)]; exact g3 l hl

/-! ### The lifted parts -/

lemma take_map_k_lift (segs : List (SPath M₀)) (j : ℕ) :
    ((segs.map (fun π : SPath M₀ => π.lift e he)).take j).map SPath.k = (segs.take j).map SPath.k := by
  rw [← List.map_take]; exact map_k_lift _

/-- **The prologue input of the lifted parts is that of the parts.** -/
lemma cIn_lift (d m Gb : ℕ) (segs : List (SPath M₀)) (j Z : ℕ) (mem : ℕ → ℕ) :
    cIn d m Gb (segs.map (fun π : SPath M₀ => π.lift e he)) j Z mem = cIn d m Gb segs j Z mem := by
  unfold cIn
  rw [List.length_map, take_map_k_lift, map_k_lift]

/-- MSSP of the map with pendant edges along a lifted path. -/
lemma msspP_lift (mssp : List D → (D → ℤ) → F → F → Option ℤ) (π : SPath M₀)
    (ℓ : D ⊕ (V × Bool) → ℤ) :
    msspP mssp (π.lift e he).darts ℓ = mssp π.darts (fun d => ℓ (.inl d)) := by
  have hfm : (π.lift e he).darts.filterMap Sum.getLeft? = π.darts := by
    rw [SPath.lift_darts]; simp [List.filterMap_map, Function.comp_def]
  simp only [msspP, hfm]

lemma dartAt_lift (π : SPath M₀) (a : ℕ) : dartAt (π.lift e he) a = .inl (dartAt π a) := by
  unfold dartAt
  split_ifs <;> rfl

/-- The lifted parts are parts of the map with pendant edges. -/
lemma PCtx.segsL' (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem) :
    SegsL (M₀.pendant e he) en' m' (segs.map (fun π : SPath M₀ => π.lift e he)) lo hi Gb mem :=
  segsL_lift H.sl H.mm H.hen

lemma PCtx.hj' (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem) :
    j < (segs.map (fun π : SPath M₀ => π.lift e he)).length := by rw [List.length_map]; exact H.hj

lemma PCtx.getLift (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem) :
    (segs.map (fun π : SPath M₀ => π.lift e he))[j]'H.hj' = (segs[j]'H.hj).lift e he := by
  simp only [List.getElem_map]

/-- The pendant numbering is injective on the base indices. -/
lemma PCtx.en_inj (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem) {i i' : ℕ}
    (hi : i < m) (hi' : i' < m) (h : en i = en i') : i = i' :=
  H.enum.inj i hi i' hi' h

/-- **The pendant `RV` on base indices is the base `RV`.** -/
lemma PCtx.rvE (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem) {i : ℕ}
    (hi : i < m) : mem (d' + 4 + m' + i) = mem (d + 4 + m + i) := by
  have h1 := H.fr.rv i (by have := H.mm; omega)
  have h2 := H.brv i hi
  apply H.fr.en_inj h1.1 (by have := H.mm; omega)
  rw [h1.2, H.hen i hi, H.hen _ h2.1, h2.2]; rfl

/-! ### The data of the stage loop on the map with pendant edges -/

/-- The lengths of the MSSP call on the base map. -/
def ℓ0 (cap f₀ : D ⊕ (V × Bool) → ℤ) : D → ℤ := fun d => (cap - f₀) (.inl d)

/-- **The answers of MSSP on the base map at the corners of the pendant walk.** -/
noncomputable def DmY (M₀ : CombMap D V F) (e : V → D) (he : ∀ v, M₀.tail (e v) = v)
    (en' : ℕ → D ⊕ (V × Bool)) (π : SPath M₀) (cap f₀ : D ⊕ (V × Bool) → ℤ) (q : FpIn)
    (i i' : ℕ) : ℕ :=
  ((Klein.msspPlaneK M₀ π.darts (ℓ0 cap f₀) ((M₀.pendant e he).face (en' (q.cw.bt i)))
    ((M₀.pendant e he).face (en' (q.cw.bt i')))).getD 0).toNat

/-- **The data of the stage loop of the frozen fix.** -/
noncomputable def mkP (M₀ : CombMap D V F) (e : V → D) (he : ∀ v, M₀.tail (e v) = v)
    (en' : ℕ → D ⊕ (V × Bool)) (π : SPath M₀) (cap f₀ : D ⊕ (V × Bool) → ℤ) (q : FpIn) (Q : ℕ) :
    SLx (M₀.pendant e he) :=
  mkY (M₀.pendant e he) en' (π.lift e he) cap f₀ (msspP (Klein.msspPlaneK M₀))
    (DmY M₀ e he en' π cap f₀ q) q Q

variable (H : PCtx M₀ e he en en' m m' Z' d d' cap f₀ segs lo hi Gb j mem)
include H

lemma PCtx.hk : ((segs[j]'H.hj).lift e he).k =
    (cIn d' m' Gb (segs.map (fun π : SPath M₀ => π.lift e he)) j Z' mem).k := by
  rw [cIn_k H.hj', H.getLift]

lemma PCtx.hd : ∀ l < ((segs[j]'H.hj).lift e he).k,
    ((segs[j]'H.hj).lift e he).d l = ((segs.map (fun π : SPath M₀ => π.lift e he))[j]'H.hj').d l :=
  fun l _ => by rw [H.getLift]

/-- The corners of `mkP` and their indices. -/
lemma mkP_corners (hk0 : 0 < (segs[j]'H.hj).k) (Q : ℕ) :
    let q := cIn d' m' Gb segs j Z' mem
    let X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q Q
    (∀ y < q.cw.cnt, X.β y ∈ ((segs[j]'H.hj).lift e he).faces) ∧
    (∀ y < q.cw.cnt, ∀ y' < q.cw.cnt, X.β y = X.β y' → y = y') ∧
    (∀ f ∈ ((segs[j]'H.hj).lift e he).faces, X.idx f < q.cw.cnt ∧ X.β (X.idx f) = f) ∧
    (∀ i < m', (M₀.pendant e he).face (en' i) ∈ ((segs[j]'H.hj).lift e he).faces →
      X.idx ((M₀.pendant e he).face (en' i)) = q.ix i) := by
  intro q X
  have h := mkY_corners H.fr H.segsL' H.hj' H.hk H.hd (pendant_rotTrans he H.rot)
    (pendant_faceTrans he H.ft) hk0 (msspP (Klein.msspPlaneK M₀))
    (DmY M₀ e he en' (segs[j]'H.hj) cap f₀ q) Q
  rw [cIn_lift] at h
  exact h

/-- **The number of corners is the number of faces along the part.** -/
lemma mkP_card (hk0 : 0 < (segs[j]'H.hj).k) :
    (cIn d' m' Gb segs j Z' mem).cw.cnt = (segs[j]'H.hj).faces.card := by
  have h := mkY_card H.fr H.segsL' H.hj' H.hk H.hd (pendant_rotTrans he H.rot)
    (pendant_faceTrans he H.ft) hk0
  rw [cIn_lift, SPath.lift_faces] at h
  exact h

/-- The arc ends of `mkP` are the corner numbers of the prologue. -/
lemma mkP_et (hk0 : 0 < (segs[j]'H.hj).k) (Q : ℕ) :
    let q := cIn d' m' Gb segs j Z' mem
    let X := mkP M₀ e he en' (segs[j]'H.hj) cap f₀ q Q
    ∀ l < q.k, X.ET (2 * l) = q.ix (q.PD l) ∧ X.ET (2 * l + 1) = q.ix (q.RV (q.PD l)) ∧
      X.EH (2 * l) = q.ix (q.RV (q.PD l)) ∧ X.EH (2 * l + 1) = q.ix (q.PD l) := by
  intro q X
  have h := mkY_et H.fr H.segsL' H.hj' H.hk H.hd (pendant_rotTrans he H.rot)
    (pendant_faceTrans he H.ft) hk0 (msspP (Klein.msspPlaneK M₀))
    (DmY M₀ e he en' (segs[j]'H.hj) cap f₀ q) Q
  rw [cIn_lift] at h
  exact h

set_option maxHeartbeats 4000000 in
/-- **The hypotheses of the stage loop hold for `mkP`.** -/
theorem mkP_good (hk0 : 0 < (segs[j]'H.hj).k) {Q W : ℕ}
    (hl2 : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem) Q).SH +
      (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem) Q).WN < Q)
    (hl14 : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem) Q).p +
      (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem) Q).LG ≤ W)
    (hw1 : 16 * (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem) Q).K + 1 ≤ W)
    (hw2 : (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem) Q).Mo +
      3 * (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem) Q).K ≤ W) :
    (mkP M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem) Q).Good W := by
  have hmssp : MSSPSpecAt (M₀.pendant e he) (msspP (Klein.msspPlaneK M₀))
      ((segs[j]'H.hj).lift e he) :=
    msspP_spec (fun ℓ hnn x hx => Klein.msspPlaneK_spec H.pl H.rot H.ft (segs[j]'H.hj) ℓ hnn x hx)
  have h := mkY_good H.fr H.segsL' H.hj' H.hk H.hd (pendant_isPlane he H.pl)
    (pendant_rotTrans he H.rot) (pendant_faceTrans he H.ft) hk0 H.pseudo hmssp
    (Dm := DmY M₀ e he en' (segs[j]'H.hj) cap f₀ (cIn d' m' Gb segs j Z' mem)) (Q := Q) (W := W)
    (by
      rw [cIn_lift]
      intro i hi i' hi' a ha ha0
      rw [msspP_lift] at ha
      unfold DmY
      have ha' : Klein.msspPlaneK M₀ (segs[j]'H.hj).darts (ℓ0 cap f₀)
          ((M₀.pendant e he).face (en' ((cIn d' m' Gb segs j Z' mem).cw.bt i)))
          ((M₀.pendant e he).face (en' ((cIn d' m' Gb segs j Z' mem).cw.bt i'))) = some a := ha
      rw [ha', Option.getD_some, Int.toNat_of_nonneg ha0])
    (by rw [cIn_lift]; exact hl2) (by rw [cIn_lift]; exact hl14) (by rw [cIn_lift]; exact hw1)
    (by rw [cIn_lift]; exact hw2)
  rw [cIn_lift] at h
  exact h

end F9b

end BKMNW

end PlanarFlow
