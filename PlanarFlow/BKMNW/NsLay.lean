module

public import PlanarFlow.BKMNW.NsRun
public import PlanarFlow.BKMNW.MfFrame

/-!
# The negSSSP step of a call from the max-flow frame's dart order

The frame of a max-flow call (`Lay`, `MfFrame.lean`) numbers the `m` darts of its piece map
`pmap hP` by `en` (increasing global numbers) and holds the arrays `RV` (index of the reverse) at
`d + 4 + m` and `SG` (index of the rotation `σ`) at `d + 4 + 2 m`. This file shows that they are
exactly the inputs of `negStep_exec` for the piece map with the dart order `layEn`:

* `layEn` (the darts of `en` as darts of the piece map), **`lay_enumOK`** (`EnumOK` from `Lay`,
  given `FaceTrans` of the piece map, e.g. from `NegPre`), **`lay_rv`**, **`lay_rt`** (the frame's
  `RV`, `SG` arrays are `rvI`, `ixOf ∘ rot` of the piece map);
so `negStep_exec` applies at a max-flow call with the identifiers
`nsIds (pmap hP) (lay_enumOK …) (layEn … 0)` (`gd (en i) = i` in the frame order, `gv` the orbit
label of the face permutation, `G = m`), `RVb = d + 4 + m`, `RTb = d + 4 + 2 m`; the lengths
`LN = ℓ + K` of the call remain an input array.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset Function Equiv Orbit CombMap NegSSSP NegSSSP.Frame OrbLab WordRAM WordRAM.Machine
  MfDrv

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The darts of the frame order as darts of the piece map. -/
noncomputable def layEn (B : Finset D) (en : ℕ → D) (m : ℕ) (hen : ∀ i < m, en i ∈ B)
    (hm : 0 < m) (i : ℕ) : SDart B :=
  if hi : i < m then ⟨en i, hen i hi⟩ else ⟨en 0, hen 0 hm⟩

lemma layEn_val {B : Finset D} {en : ℕ → D} {m : ℕ} {hen : ∀ i < m, en i ∈ B} {hm : 0 < m}
    {i : ℕ} (hi : i < m) : (layEn B en m hen hm i).1 = en i := by
  unfold layEn; simp only [hi, ↓reduceDIte]

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ}

/-- **The frame's dart order is a dart order of the piece map.** -/
theorem lay_enumOK (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hft : (pmap hP).FaceTrans) :
    EnumOK (pmap hP) (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm) m where
  inj i hi j hj e := hl.en_inj hi hj (by
    have := congrArg Subtype.val e
    rwa [layEn_val hi, layEn_val hj] at this)
  surj y := by
    obtain ⟨i, hi, e⟩ := hl.en_surj y.1 y.2
    exact ⟨i, hi, Subtype.ext (by rw [layEn_val hi, e])⟩
  fsurj f := Quotient.inductionOn f fun y => ⟨y, rfl⟩
  ft := hft

/-- The index of a dart given by the frame. -/
lemma ixOf_lay (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hft : (pmap hP).FaceTrans) {j : ℕ} (hj : j < m)
    {y : SDart (pdarts M x.1.piece x.2.1)} (e : en j = y.1) :
    ixOf (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm) m y = j := by
  have h := lay_enumOK hP hl hm hft
  have : layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm j = y :=
    Subtype.ext (by rw [layEn_val hj, e])
  rw [← this, ixOf_en h hj]

/-- **The frame's `RV` array is the reverse of the piece map.** -/
theorem lay_rv (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hft : (pmap hP).FaceTrans) {i : ℕ} (hi : i < m) :
    mem (d + 4 + m + i) =
      rvI (pmap hP) (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm) m i := by
  obtain ⟨h1, h2⟩ := hl.rv i hi
  unfold rvI
  rw [ixOf_lay hP hl hm hft h1 (by rw [h2, pmap_rev, layEn_val hi])]

/-- **The frame's `SG` array is the rotation of the piece map.** -/
theorem lay_rt (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hft : (pmap hP).FaceTrans) {i : ℕ} (hi : i < m) :
    mem (d + 4 + 2 * m + i) = ixOf (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm) m
      ((pmap hP).rot (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i)) := by
  obtain ⟨h1, h2⟩ := hl.sg i hi
  rw [ixOf_lay hP hl hm hft h1 (by
    rw [h2]
    unfold pmap
    rw [subMap_rot, layEn_val hi])]

end NsStep

end BKMNW

end PlanarFlow
