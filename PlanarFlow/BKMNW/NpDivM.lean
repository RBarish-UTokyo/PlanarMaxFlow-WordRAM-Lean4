module

public import PlanarFlow.BKMNW.NpCntM
public import PlanarFlow.BKMNW.OrbLab

/-!
# The vertices of a piece map and the net outflow, from the frame (math of `dvP`)

The frame of a call (`Lay`) holds the rotation of the piece map as an index array `SG`
(`SG[i] < m`, `en SG[i] = σ (en i)`). The vertices of the piece map are the orbits of `σ`, so the
least index of the orbit of `i` under `SG` (`OrbLab.olab`) identifies the vertex of the dart
`en i`, and the net outflow of a flow at a vertex is the sum of the flow array over the darts of
its orbit:

* `sgF` (the index array), `Lay.sg_iter`, **`Lay.permOn_sg`** (`SG` is a permutation of
  `[0, m)`), **`Lay.vert_eq_iff`** (two darts of the frame have the same vertex in the piece map
  iff their labels are equal);
* `vDart` (the dart `en i` of the piece map), **`Lay.div_eq_sum`** (the net outflow at the vertex
  of `en i` is the sum of `g` over the indices of the same label).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap OrbLab

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- The rotation of the frame as an index array. -/
def sgF (d m : ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ := mem (d + 4 + 2 * m + i)

/-- The iterates of the index array follow the powers of the rotation. -/
lemma Lay.sg_iter {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) :
    ∀ t i, i < m → (sgF d m mem)^[t] i < m ∧ en ((sgF d m mem)^[t] i) = (x.2.2 ^ t) (en i)
  | 0, i, hi => ⟨hi, by simp⟩
  | t + 1, i, hi => by
    obtain ⟨h1, h2⟩ := Lay.sg_iter hL t i hi
    rw [Function.iterate_succ_apply']
    obtain ⟨g1, g2⟩ := hL.sg _ h1
    refine ⟨g1, ?_⟩
    show en (mem (d + 4 + 2 * m + (sgF d m mem)^[t] i)) = _
    rw [g2, h2, pow_succ', Perm.mul_apply]

/-- **The index array of the rotation is a permutation of `[0, m)`.** -/
lemma Lay.permOn_sg {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) : PermOn (sgF d m mem) m where
  lt i hi := (hL.sg i hi).1
  inj i hi j hj e := by
    have h1 := (hL.sg i hi).2
    have h2 := (hL.sg j hj).2
    unfold sgF at e
    rw [e, h2] at h1
    exact hL.en_inj hi hj (x.2.2.injective h1.symm)

/-- The dart `en i` of the piece map. -/
def vDart {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) {i : ℕ} (hi : i < m) :
    SDart (pdarts M x.1.piece x.2.1) := ⟨en i, hL.en_mem i hi⟩

/-- **Two darts of the frame have the same vertex in the piece map iff their labels agree.** -/
lemma Lay.vert_eq_iff {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2) {i j : ℕ}
    (hi : i < m) (hj : j < m) :
    (pmap h).tail (vDart hL hi) = (pmap h).tail (vDart hL hj) ↔
      olab (sgF d m mem) i = olab (sgF d m mem) j := by
  rw [pmap_tail, pmap_tail, sVert_eq_iff, olab_eq_iff hL.permOn_sg hi hj]
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := hs.exists_nat_pow_eq
    refine ⟨t, hL.en_inj (hL.sg_iter t i hi).1 hj ?_⟩
    rw [(hL.sg_iter t i hi).2]; exact ht
  · rintro ⟨t, ht⟩
    refine ⟨(t : ℤ), ?_⟩
    have := (hL.sg_iter t i hi).2
    rw [ht] at this
    simp only [vDart, zpow_natCast]
    exact this.symm

/-- **The net outflow at the vertex of `en i`** is the sum of `g` over the darts with the same
label. -/
lemma Lay.div_eq_sum {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z x m en d mem) (h : PieceInv M x.1.piece x.2.1 x.2.2)
    (g : SDart (pdarts M x.1.piece x.2.1) → ℤ) {i : ℕ} (hi : i < m) :
    (pmap h).div g ((pmap h).tail (vDart hL hi)) =
      ∑ j ∈ (range m).filter (fun j => olab (sgF d m mem) j = olab (sgF d m mem) i),
        fext g (en j) := by
  classical
  unfold CombMap.div
  symm
  refine Finset.sum_bij' (fun j hj => vDart hL (mem_range.1 (mem_filter.1 hj).1))
    (fun y _ => Classical.choose (hL.en_surj y.1 y.2)) (fun j hj => ?_) (fun y hy => ?_)
    (fun j hj => ?_) (fun y hy => ?_) (fun j hj => ?_)
  · obtain ⟨h1, h2⟩ := mem_filter.1 hj
    simp only [mem_filter, mem_univ, true_and]
    exact (hL.vert_eq_iff h (mem_range.1 h1) hi).2 h2
  · obtain ⟨h1, h2⟩ := Classical.choose_spec (hL.en_surj y.1 y.2)
    simp only [mem_filter, mem_univ, true_and] at hy
    refine mem_filter.2 ⟨mem_range.2 h1, ?_⟩
    have e : vDart hL h1 = y := Subtype.ext h2
    rw [← (hL.vert_eq_iff h h1 hi), e, hy]
  · obtain ⟨h1, -⟩ := mem_filter.1 hj
    have hj' := mem_range.1 h1
    obtain ⟨g1, g2⟩ := Classical.choose_spec (hL.en_surj (vDart hL hj').1 (vDart hL hj').2)
    exact hL.en_inj g1 hj' g2
  · obtain ⟨h1, h2⟩ := Classical.choose_spec (hL.en_surj y.1 y.2)
    exact Subtype.ext h2
  · simp only [vDart]
    exact fext_mem g _

end MfDrv

end BKMNW

end PlanarFlow
