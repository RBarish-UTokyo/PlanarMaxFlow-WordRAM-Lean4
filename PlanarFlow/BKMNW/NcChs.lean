module

public import PlanarFlow.BKMNW.StChoiceC
public import PlanarFlow.BKMNW.NpMach

/-!
# The machine's s-t flow choices tied to the frame of a call

`StChoiceC.lean` defines the choices `stChs I enF mF fb` for a *given* family of dart orders
`enF`. Here the order is the frame's own: the darts of the piece map by increasing `gid` (`GOrd`,
unique by `gOrd_unique`), so the choices are a function of the call and of `gid` alone.

* **`gOrd_exists`**: a `gid`-increasing order of the piece map exists when `gid` is injective on
  its darts and it has a dart (`Finset.orderEmbOfFin` on the image of `gid`);
* `enumOK_dual` (`EnumOK` of the dual from `RotTrans` and a dart at every vertex),
  `pmap_tail_surj`, **`dtree_nonempty`** (a plane map with transitive rotations, numbered, has a
  dual tree: the canonical run of the encoders builds one, `stE_can`);
* **`stChsG gid I fb`**: at the call `x`, `stChoiceOf` of the `gid`-order when it exists (and a
  dual tree exists), `fb x h` otherwise; **`stChsG_eq`**: on plane piece maps with transitive
  rotations and `gid` injective, the fallback is not used;
* **`stChsG_OK`**: the choices are valid (`StChoice.OK`) at every plane piece map with transitive
  rotations, when `gid` is injective on its darts;
* **`stChsG_lay`**: at a call with a frame `Lay … x m en d mem` (`0 < m`), the choices **are**
  `stChoiceOf` of the frame order `layEn … en m`; **`lay_plane`** (from `CallOk` and the frame:
  the piece map is plane, with transitive rotations and faces);
* **`stCallZ_lay`**: `stCallZ` at a frame (the reverse and rotation arrays `RV = d + 4 + m`,
  `SG = d + 4 + 2 m` of the frame) writes `max 0 (Z + (stChsG gid I fb x h).flow cp X Y (en i))`;
* **`nSpecOn_machNF_G`**: the family `machNF gid I (stChsG gid I fb) pch` meets `NSpecOn` with no
  hypothesis on the choices (only `gid` injective and the push-back).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine STFlow NsStep MfDrv StCall

universe w

/-! ### Dual orders and dual trees -/

section Gen

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

/-- **`EnumOK` of the dual**: from transitive rotations and a dart at every vertex. -/
theorem enumOK_dual (h : EnumOK M en m) (hrot : M.RotTrans) (hV : ∀ v, ∃ d, M.tail d = v) :
    EnumOK M.dual en m where
  inj := h.inj
  surj := h.surj
  fsurj := hV
  ft := fun d d' e => hrot d d' e

/-- **A numbered plane map with transitive rotations has a dual tree** (the canonical run of the
encoders builds one). -/
theorem dtree_nonempty (hM : M.IsPlane) (hrot : M.RotTrans) (h : EnumOK M en m) (hm : 0 < m)
    (hV : ∀ v, ∃ d, M.tail d = v) : Nonempty (STFlow.DTree M) := by
  obtain ⟨d⟩ : Nonempty D := ⟨en 0⟩
  obtain ⟨C, T₀, -⟩ := stE_can (P := (⟨[], fun _ => 0⟩ : Input)) hM h (enumOK_dual h hrot hV) hm
    (cp := fun _ => 0) (fun _ => le_rfl) (X := univ) (Y := univ) ⟨d, mem_univ _⟩ ⟨d, mem_univ _⟩
  exact ⟨T₀⟩

end Gen

/-! ### The `gid`-order of a call -/

section Call

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- Every vertex of a piece map is the tail of a dart. -/
lemma pmap_tail_surj {x : MCall M} (h : PieceInv M x.1.piece x.2.1 x.2.2)
    (v : SVert x.2.2 (pdarts M x.1.piece x.2.1)) : ∃ d, (pmap h).tail d = v :=
  Quotient.inductionOn v fun y => ⟨y, rfl⟩

/-- The faces of a piece map are transitive. -/
lemma pmap_faceTrans {x : MCall M} (h : PieceInv M x.1.piece x.2.1 x.2.2) :
    (pmap h).FaceTrans :=
  subMap_faceTrans _ _ _

/-- A plane piece map has a dart. -/
lemma pmap_card_pos {x : MCall M} (h : PieceInv M x.1.piece x.2.1 x.2.2)
    (hpl : (pmap h).IsPlane) : 0 < (pdarts M x.1.piece x.2.1).card := by
  obtain ⟨v⟩ := hpl.nonempty
  obtain ⟨y, -⟩ := pmap_tail_surj h v
  exact Finset.card_pos.2 ⟨y.1, y.2⟩

/-- **A `gid`-increasing order of the piece map exists** when `gid` is injective on its darts and
it has a dart. -/
theorem gOrd_exists (gid : D → ℕ) (x : MCall M) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    (hinj : ∀ a ∈ pdarts M x.1.piece x.2.1, ∀ b ∈ pdarts M x.1.piece x.2.1, gid a = gid b → a = b)
    (hpos : 0 < (pdarts M x.1.piece x.2.1).card) : ∃ en, GOrd gid x h en := by
  classical
  have hcard : ((pdarts M x.1.piece x.2.1).image gid).card = (pdarts M x.1.piece x.2.1).card :=
    card_image_of_injOn fun a ha b hb e => hinj a ha b hb e
  let e := ((pdarts M x.1.piece x.2.1).image gid).orderEmbOfFin hcard
  have he : ∀ i : Fin (pdarts M x.1.piece x.2.1).card,
      ∃ y ∈ pdarts M x.1.piece x.2.1, gid y = e i := fun i =>
    Finset.mem_image.1 (((pdarts M x.1.piece x.2.1).image gid).orderEmbOfFin_mem hcard i)
  let en0 : Fin (pdarts M x.1.piece x.2.1).card → SDart (pdarts M x.1.piece x.2.1) :=
    fun i => ⟨(he i).choose, (he i).choose_spec.1⟩
  have hen0 : ∀ i, gid (en0 i).1 = e i := fun i => (he i).choose_spec.2
  let en : ℕ → SDart (pdarts M x.1.piece x.2.1) := fun i =>
    if hi : i < (pdarts M x.1.piece x.2.1).card then en0 ⟨i, hi⟩ else en0 ⟨0, hpos⟩
  have enl : ∀ i (hi : i < (pdarts M x.1.piece x.2.1).card), en i = en0 ⟨i, hi⟩ := fun i hi => by
    simp only [en, hi, ↓reduceDIte]
  refine ⟨en, hpos, ⟨fun i hi j hj eij => ?_, fun y => ?_, fun f => ?_, pmap_faceTrans h⟩,
    fun i j hij hj => ?_, fun i hi => ?_⟩
  · rw [enl i hi, enl j hj] at eij
    have := congrArg (fun z : SDart (pdarts M x.1.piece x.2.1) => gid z.1) eij
    simp only [hen0] at this
    exact congrArg Fin.val (e.injective this)
  · have hm : gid y.1 ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin]; simpa using ⟨y.1, y.2, rfl⟩
    obtain ⟨i, hi⟩ := hm
    refine ⟨i.1, i.2, ?_⟩
    rw [enl i.1 i.2]
    apply Subtype.ext
    exact hinj _ (en0 i).2 _ y.2 (by rw [hen0]; exact hi)
  · exact Quotient.inductionOn f fun y => ⟨y, rfl⟩
  · have hi : i < (pdarts M x.1.piece x.2.1).card := lt_trans hij hj
    rw [enl i hi, enl j hj, hen0, hen0]
    exact e.strictMono (show (⟨i, hi⟩ : Fin _) < ⟨j, hj⟩ from hij)
  · have hi' : ¬ i < (pdarts M x.1.piece x.2.1).card := by omega
    simp only [en, hi', hpos, ↓reduceDIte]

lemma stChoiceOf_congr {D' V' F' : Type w} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'} {en en' : ℕ → D'}
    {m m' : ℕ} (h : EnumOK M' en m) (h' : EnumOK M' en' m') (e : en = en') (em : m = m')
    (I : Input) [i₁ : Nonempty (STFlow.DTree M')] :
    stChoiceOf h I = stChoiceOf h' I := by
  subst e em; rfl

open Classical in
/-- **The machine's s-t flow choices at every call, from the `gid`-order of the call** (see the
module docstring). -/
noncomputable def stChsG (gid : D → ℕ) (I : Input)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h)) :
    (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h) :=
  fun x h =>
    if hx : ∃ en, GOrd gid x h en then
      if hT : Nonempty (STFlow.DTree (pmap h)) then
        @stChoiceOf _ _ _ _ _ _ _ _ _ (pmap h) hx.choose _ hx.choose_spec.enum I hT
      else fb x h
    else fb x h

/-- **The fallback is not used** at a plane piece map with transitive rotations when `gid` is
injective on its darts. -/
theorem stChsG_eq (gid : D → ℕ) (I : Input)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h))
    (x : MCall M) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hpl : (pmap h).IsPlane)
    (hrot : (pmap h).RotTrans)
    (hinj : ∀ a ∈ pdarts M x.1.piece x.2.1, ∀ b ∈ pdarts M x.1.piece x.2.1, gid a = gid b → a = b) :
    ∃ (hx : ∃ en, GOrd gid x h en) (hT : Nonempty (STFlow.DTree (pmap h))),
      stChsG gid I fb x h =
        @stChoiceOf _ _ _ _ _ _ _ _ _ (pmap h) hx.choose _ hx.choose_spec.enum I hT := by
  have hpos := pmap_card_pos h hpl
  have hx := gOrd_exists gid x h hinj hpos
  have hT := dtree_nonempty hpl hrot hx.choose_spec.enum hpos (pmap_tail_surj h)
  refine ⟨hx, hT, ?_⟩
  unfold stChsG
  simp only [hx, hT, ↓reduceDIte]

/-- **The choices are valid** at every plane piece map with transitive rotations, `gid`
injective on its darts. -/
theorem stChsG_OK (gid : D → ℕ) (I : Input)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h))
    (x : MCall M) (h : PieceInv M x.1.piece x.2.1 x.2.2) (hpl : (pmap h).IsPlane)
    (hrot : (pmap h).RotTrans)
    (hinj : ∀ a ∈ pdarts M x.1.piece x.2.1, ∀ b ∈ pdarts M x.1.piece x.2.1, gid a = gid b → a = b) :
    (stChsG gid I fb x h).OK := by
  obtain ⟨hx, hT, e⟩ := stChsG_eq gid I fb x h hpl hrot hinj
  rw [e]
  exact stChoiceOf_OK hpl hx.choose_spec.enum
    (enumOK_dual hx.choose_spec.enum hrot (pmap_tail_surj h)) (pmap_card_pos h hpl) I

/-- **The family of the machine meets `NSpecOn`** with the choices `stChsG` (no hypothesis on
the choices). -/
theorem nSpecOn_machNF_G (gid : D → ℕ) (I : Input)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h))
    (pch : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      PushFn (Orbit.SDart (pdarts M x.1.piece x.2.1)) (Orbit.SVert x.2.2 (pdarts M x.1.piece x.2.1)))
    (Reach : MCall M → Prop) (hgid : Injective gid)
    (hpush : ∀ x, Reach x → ∀ h, (pmap h).IsPlane → PushSpec (pmap h) (pch x h)) :
    NSpecOn M (machNF gid I (stChsG gid I fb) pch) Reach :=
  fun x hx h hpl hrot hface _ hu => implG_spec hpl hu (hpush x hx h hpl)
    (Klein.msspPlaneK_spec hpl hrot hface) (frRef_spec _) (negLay_spec _ _ _ _)
    (STFlow.StChoice.spec hpl (stChsG_OK gid I fb x h hpl hrot
      fun a _ b _ e => hgid e))

/-! ### At a frame -/

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ}

/-- **The piece map of a call with a frame of at least one dart is plane, with transitive
rotations and faces.** -/
theorem lay_plane (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hok : CallOk M S T x)
    (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m) :
    (pmap hP).IsPlane ∧ (pmap hP).RotTrans ∧ (pmap hP).FaceTrans :=
  hP.isPlane hok.2.2.1.hConn (hl.en_mem 0 hm)

/-- **At a frame, the choices are those of the frame order.** -/
theorem stChsG_lay (I : Input)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h))
    (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m)
    (hft : (pmap hP).FaceTrans) [hT : Nonempty (STFlow.DTree (pmap hP))] :
    stChsG gid I fb x hP = stChoiceOf (lay_enumOK hP hl hm hft) I := by
  have hc := lay_card hP hl hm hft
  have hg := lay_gOrd hP hl hm hft hc
  have hx : ∃ en', GOrd gid x hP en' := ⟨_, hg⟩
  unfold stChsG
  simp only [hx, hT, ↓reduceDIte]
  exact stChoiceOf_congr _ _ (gOrd_unique hx.choose_spec hg) hc.symm I

/-- **The s-t flow of the choices at a frame.** -/
theorem stChsG_flow_lay (I : Input)
    (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h))
    (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hok : CallOk M S T x)
    (hl : Lay M gid u S T Z x m en d mem) (hm : 0 < m) :
    ∃ (hT : Nonempty (STFlow.DTree (pmap hP))),
      (stChsG gid I fb x hP).flow =
        (stChoiceOf (lay_enumOK hP hl hm (lay_plane hP hok hl hm).2.2) I).flow := by
  obtain ⟨hpl, hrot, hft⟩ := lay_plane hP hok hl hm
  have hT := dtree_nonempty hpl hrot (lay_enumOK hP hl hm hft) hm (pmap_tail_surj hP)
  exact ⟨hT, by rw [stChsG_lay I fb hP hl hm hft]⟩

set_option maxHeartbeats 1000000 in
/-- **`stCallZ` at a frame** writes the s-t flow of the choices `stChsG` (input `P` of the run):
the reverse and rotation arrays are the frame's `RV = d + 4 + m`, `SG = d + 4 + 2 m`; the
capacity and the two flag arrays are given in the frame order. -/
theorem stCallZ_lay (fb : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → StChoice (pmap h))
    (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hok : CallOk M S T x) (hm : 0 < m)
    {P : Input} {W : ℕ} {cp : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hcp : ∀ d, 0 ≤ cp d)
    {X Y : Finset (SVert x.2.2 (pdarts M x.1.piece x.2.1))} (hXY : Disjoint X Y)
    (hXn : ∃ d, (pmap hP).tail d ∈ X) (hYn : ∃ d, (pmap hP).tail d ∈ Y) (c : Config)
    (hl : Lay M gid u S T Z x m en d c.nmem)
    (hc : WordsBounded W c) {Cb Xb Yb ib Ob Zo p Wz : ℕ}
    (r00 : c.nreg 9100 = m) (r01 : c.nreg 9101 = d + 4 + m) (r02 : c.nreg 9102 = d + 4 + 2 * m)
    (r03 : c.nreg 9103 = Cb) (r04 : c.nreg 9104 = Xb) (r05 : c.nreg 9105 = Yb)
    (r07 : c.nreg 9107 = ib) (r08 : c.nreg 9108 = Ob) (r09 : c.nreg 9109 = Zo)
    (r10 : c.nreg 9110 = p)
    (hC : ∀ i < m, c.nmem (Cb + i) =
      (cp (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i)).toNat)
    (hX : ∀ i < m, c.nmem (Xb + i) =
      flagX (pmap hP) (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm) X i)
    (hY : ∀ i < m, c.nmem (Yb + i) =
      flagX (pmap hP) (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm) Y i)
    (hz : MemZ Wz c) (oD : Wz < d) (oC : Wz < Cb) (oX : Wz < Xb) (oY : Wz < Yb)
    (wD : d + 4 + 3 * m ≤ W) (wC : Cb + m ≤ W) (wX : Xb + m ≤ W) (wY : Yb + m ≤ W)
    (hWc : stWc (pmap hP) cp X Y m ≤ Wz)
    (hib : pstWN (101 * m + 45) (stHb (pmap hP) cp X Y m) < ib) (hib0 : 339 * m + 128 ≤ ib)
    (hibz : ib + pstWN (101 * m + 45) (stHb (pmap hP) cp X Y m) ≤ Wz)
    (hO : Wz < Ob) (hOp : Ob + m ≤ p)
    (hpW : p + 3 * (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
      (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) m (4 * m + 1) + 3) ≤ W)
    (hZW : Zo + Wz ≤ W) :
    ∃ c' t, Exec P W stCallZ c c' t ∧
      t ≤ stCostZ m (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
        (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) m (4 * m + 1) + 3) ∧
      MemZ Wz c' ∧
      (∀ i < m, (c'.nmem (Ob + i) : ℤ) = max 0 ((Zo : ℤ) + (stChsG gid P fb x hP).flow cp X Y
        (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i))) ∧
      (∀ a, Wz < a → (a < Ob ∨ Ob + m ≤ a) →
        (a < p ∨ p + 3 * (4 * pcoreB (SVert x.2.2 (pdarts M x.1.piece x.2.1))
          (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M)) m (4 * m + 1) + 3) ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ StScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨hpl, hrot, hft⟩ := lay_plane hP hok hl hm
  have he := lay_enumOK hP hl hm hft
  have hT := dtree_nonempty hpl hrot he hm (pmap_tail_surj hP)
  have hflow := stChsG_lay (I := P) fb hP hl hm hft
  rw [hflow]
  exact stCallZ_exec hpl hrot he (enumOK_dual he hrot (pmap_tail_surj hP)) hm hcp hXY hXn hYn c
    hc r00 r01 r02 r03 r04 r05 r07 r08 r09 r10 (fun i hi => lay_rv hP hl hm hft hi)
    (fun i hi => lay_rt hP hl hm hft hi) hC hX hY hz (by omega) (by omega) oC oX oY
    (by omega) (by omega) wC wX wY hWc hib hib0 hibz hO hOp hpW hZW

end Call

end NcStep

end BKMNW

end PlanarFlow
