module

public import PlanarFlow.BKMNW.NpStep
public import PlanarFlow.BKMNW.NpDiv
public import PlanarFlow.BKMNW.NfStage
public import PlanarFlow.BKMNW.FRFixPath

/-!
# The prologue of `fixP`: the frame side

FixConservationOnPath on the part `j` of a node call (`FixPSpecN`) works on the piece map
`pmap h` and the path `πj = (segsP h π.segs _)[j]`. The program sees the frame (`Lay`: the
darts `en i`, `i < m`, the reverse `RV`, the rotation `SG`, the capacities `CP`, the flow `FL`)
and the parts of the separator (`SegsAt`: the frame indices of the darts of `π.segs[j]`).

* **`segsP_get`**: the darts of `πj` are those of `π.segs[j]` (as darts of the piece map);
* `nxF` (the face walk `NX[i] = SG[RV[i]]` as an index array), `Lay.nx_iter`,
  **`Lay.permOn_nx`**, **`Lay.face_eq_iff`** (two darts of the frame have the same face of the
  piece map iff their `olab` labels for `NX` agree);
* `tnF` (the walk `tour` around the path as an index array, from the marks `ON` of the darts of
  the path), **`Lay.tn_iter`** (its iterates are those of `tour (pmap h) πj.darts`);
* `card_sdart` (the piece map has `m` darts), so `fixPer ≤ m`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab MfDrv

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### The parts of the separator in the piece map -/

/-- **The darts of a part of the separator in the piece map** are those of the part. -/
theorem segsP_get {P : Finset D} {Hs : List (Finset V)} {σ : Perm D} (h : PieceInv M P Hs σ) :
    ∀ (L : List (SPath M)) (hL : ∀ π ∈ L, SegIn M P Hs π) (j : ℕ) (πj : SPath (pmap h)),
      (segsP h L hL)[j]? = some πj →
      ∃ hj : j < L.length, πj.k = L[j].k ∧ ∀ l < πj.k, (πj.d l).1 = L[j].d l
  | [], _, j, πj, e => by simp [segsP] at e
  | π :: L, hL, 0, πj, e => by
      simp only [segsP, List.getElem?_cons_zero, Option.some.injEq] at e
      subst e
      exact ⟨by simp, rfl, fun l hl => by
        simp [SPath.toPiece, SPath.pdart, show l < π.k from hl]⟩
  | π :: L, hL, j + 1, πj, e => by
      simp only [segsP, List.getElem?_cons_succ] at e
      obtain ⟨hj, h1, h2⟩ := segsP_get h L _ j πj e
      exact ⟨by simp; omega, h1, h2⟩

namespace MfDrv

variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-! ### The faces of the piece map from the frame -/

/-- The face walk of the frame as an index array: `NX[i] = SG[RV[i]]`. -/
def nxF (d m : ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ := mem (d + 4 + 2 * m + mem (d + 4 + m + i))

/-- The iterates of the face walk follow the powers of `σ * rev`. -/
lemma Lay.nx_iter {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) :
    ∀ t i, i < m → (nxF d m mem)^[t] i < m ∧
      en ((nxF d m mem)^[t] i) = ((x.2.2 * revPerm M) ^ t) (en i)
  | 0, i, hi => ⟨hi, by simp⟩
  | t + 1, i, hi => by
    obtain ⟨h1, h2⟩ := Lay.nx_iter hL t i hi
    rw [Function.iterate_succ_apply']
    obtain ⟨g1, g2⟩ := hL.rv _ h1
    obtain ⟨k1, k2⟩ := hL.sg _ g1
    refine ⟨k1, ?_⟩
    show en (mem (d + 4 + 2 * m + mem (d + 4 + m + (nxF d m mem)^[t] i))) = _
    rw [k2, g2, h2, pow_succ', Perm.mul_apply, Perm.mul_apply]
    rfl

/-- **The index array of the face walk is a permutation of `[0, m)`.** -/
lemma Lay.permOn_nx {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) : PermOn (nxF d m mem) m where
  lt i hi := ((hL.nx_iter 1 i hi).1)
  inj i hi j hj e := by
    have h1 := (hL.nx_iter 1 i hi).2
    have h2 := (hL.nx_iter 1 j hj).2
    simp only [Function.iterate_one] at h1 h2
    rw [e, h2] at h1
    exact hL.en_inj hi hj (Equiv.injective _ h1.symm)

/-- **Two darts of the frame have the same face in the piece map iff their labels agree.** -/
lemma Lay.face_eq_iff {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) {i j : ℕ}
    (hi : i < m) (hj : j < m) :
    (pmap h).face (vDart hL hi) = (pmap h).face (vDart hL hj) ↔
      olab (nxF d m mem) i = olab (nxF d m mem) j := by
  show Quotient.mk _ (vDart hL hi) = Quotient.mk _ (vDart hL hj) ↔ _
  rw [sVert_eq_iff, olab_eq_iff hL.permOn_nx hi hj]
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := hs.exists_nat_pow_eq
    refine ⟨t, hL.en_inj (hL.nx_iter t i hi).1 hj ?_⟩
    rw [(hL.nx_iter t i hi).2]; exact ht
  · rintro ⟨t, ht⟩
    refine ⟨(t : ℤ), ?_⟩
    have := (hL.nx_iter t i hi).2
    rw [ht] at this
    simp only [vDart, zpow_natCast]
    exact this.symm

/-! ### The walk around the path from the frame -/

/-- The walk around the path as an index array: `NX` on the marked darts (`ON[i] = 1`), `SG`
elsewhere. -/
def tnF (d m : ℕ) (mem : ℕ → ℕ) (onm : ℕ → ℕ) (i : ℕ) : ℕ :=
  if onm i = 1 then nxF d m mem i else sgF d m mem i

/-- One step of the walk. -/
lemma Lay.tn_one {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    {Ld : List (SDart (pdarts M x.1.piece x.2.1))} {onm : ℕ → ℕ}
    (hon : ∀ i (hi : i < m), onm i = 1 ↔ vDart hL hi ∈ Ld) {i : ℕ} (hi : i < m) :
    tnF d m mem onm i < m ∧ en (tnF d m mem onm i) = (tour (pmap h) Ld (vDart hL hi)).1 := by
  unfold tnF
  by_cases h1 : onm i = 1
  · have hm := (hon i hi).1 h1
    simp only [h1, ↓reduceIte, tour, hm]
    obtain ⟨a1, a2⟩ := hL.nx_iter 1 i hi
    simp only [Function.iterate_one, pow_one] at a1 a2
    refine ⟨a1, ?_⟩
    rw [a2]
    rfl
  · have hm : vDart hL hi ∉ Ld := fun e => h1 ((hon i hi).2 e)
    simp only [h1, ↓reduceIte, tour, hm]
    obtain ⟨a1, a2⟩ := hL.sg i hi
    refine ⟨a1, ?_⟩
    show en (mem (d + 4 + 2 * m + i)) = _
    rw [a2]
    show _ = ((pmap h).rot (vDart hL hi)).1
    unfold pmap
    rw [subMap_rot]
    rfl

/-- **The iterates of the walk** are those of `tour` around the path. -/
lemma Lay.tn_iter {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    {Ld : List (SDart (pdarts M x.1.piece x.2.1))} {onm : ℕ → ℕ}
    (hon : ∀ i (hi : i < m), onm i = 1 ↔ vDart hL hi ∈ Ld) {i : ℕ} (hi : i < m) :
    ∀ t, (tnF d m mem onm)^[t] i < m ∧
      en ((tnF d m mem onm)^[t] i) = ((tour (pmap h) Ld)^[t] (vDart hL hi)).1
  | 0 => ⟨hi, rfl⟩
  | t + 1 => by
    obtain ⟨h1, h2⟩ := Lay.tn_iter hL h hon hi t
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    obtain ⟨g1, g2⟩ := hL.tn_one h hon h1
    refine ⟨g1, ?_⟩
    rw [g2]
    congr 2
    exact Subtype.ext h2

/-- The dart of the piece map at an index is determined by `en`. -/
lemma vDart_eq_of_en {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) {i : ℕ} (hi : i < m)
    {y : SDart (pdarts M x.1.piece x.2.1)} (e : en i = y.1) : vDart hL hi = y :=
  Subtype.ext e

/-- **The piece map has `m` darts.** -/
lemma Lay.card_sdart {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) :
    Fintype.card (SDart (pdarts M x.1.piece x.2.1)) = m := by
  rw [Fintype.card_coe]
  have : pdarts M x.1.piece x.2.1 = (range m).image en := by
    ext y
    simp only [mem_image, mem_range]
    constructor
    · intro hy; obtain ⟨i, hi, e⟩ := hL.en_surj y hy; exact ⟨i, hi, e⟩
    · rintro ⟨i, hi, rfl⟩; exact hL.en_mem i hi
  rw [this, card_image_of_injOn (fun i hi j hj e => hL.en_inj (mem_range.1 hi) (mem_range.1 hj) e),
    card_range]

end MfDrv

end BKMNW

end PlanarFlow
