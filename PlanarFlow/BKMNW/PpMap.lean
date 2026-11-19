module

public import PlanarFlow.BKMNW.MfMainG

/-!
# The preprocessed map with explicit pendant darts

`lpreMap M` (`Loops.lean`) is `preMap (nlMap M) nlE`, i.e. the triangulated loop-free map
`(nlMap M).triMap` with a pendant edge at every vertex, drawn just before the dart
`triE (nlE M) w`. Both choices of these darts are made by `Quotient.out`:

* at a vertex `w` of `nlMap M` (a class of darts), `nlE M w = w.out`;
* at the centre `x` of a face, `triE … (.inr x) = down x.out`.

The rotation of `lpreMap M` (the array `SIG` of the max-flow program, and `RT`) depends on these
darts, and no statement can say which dart `Quotient.out` picks in a class of more than one
element. So **no program can be proved to write the index arrays of `lpreMap M`**: the input
conventions of `mfMain_cMachXGE` can only be met for the preprocessed map with *explicit*
pendant darts.

This file defines that map and the run on it:

* `PVert M`: the vertices of the triangulated loop-free map (vertices of `nlMap M` and centres of
  its faces);
* **`lpreMapX M e he`**: the triangulated loop-free map with a pendant edge at every vertex `w`,
  drawn just before the dart `e w` (`he : tail (e w) = w`);
* **`lpreMap_eq_X`**: `lpreMap M = lpreMapX M (triE … (nlE M)) …` (definitionally): the current
  map is the instance with the choices of `Quotient.out`;
* `nlRunX`: `nlRun` on `lpreMapX`.

The proofs of the max-flow chain (`maxflow_cost_of`, `decS_balDecA_lpre`, `mfMain_cMachXGE`, …)
use `nlE` and `triE` only through `nlE_tail` and `triE_tail`, so they hold verbatim for
`lpreMapX M e he` with any `he`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap PlanarSeparator.StDart

universe w

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

/-! ### Conditionals -/

lemma ppIteT {α : Type*} {p : Prop} {_ : Decidable p} (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

lemma ppIteF {α : Type*} {p : Prop} {_ : Decidable p} (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

lemma ppDiteT {α : Type*} {p : Prop} {_ : Decidable p} (h : p) (a : p → α) (b : ¬ p → α) :
    (if hp : p then a hp else b hp) = a h := by simp [h]

lemma ppDiteF {α : Type*} {p : Prop} {_ : Decidable p} (h : ¬ p) (a : p → α) (b : ¬ p → α) :
    (if hp : p then a hp else b hp) = b h := by simp [h]

variable (M : CombMap D V F)

/-- The vertices of the triangulated loop-free map: the vertices of `nlMap M` and the centres of
its faces. -/
abbrev PVert := SVert (nlRot M) (nlDarts M) ⊕ ((nlMap M).toSep nlMap_rotTrans).Face

/-- The darts of the triangulated loop-free map. -/
abbrev TDart := PlanarSeparator.StDart (SDart (nlDarts M))

/-- The triangulated loop-free map. -/
noncomputable abbrev tnlMap := (nlMap M).triMap nlMap_rotTrans

/-- **The preprocessed map with explicit pendant darts**: the triangulated loop-free map with a
pendant edge at every vertex `w`, drawn just before the dart `e w` leaving `w`. -/
noncomputable abbrev lpreMapX (e : PVert M → TDart M) (he : ∀ w, (tnlMap M).tail (e w) = w) :=
  (tnlMap M).pendant e he

/-- **The preprocessed map of the library is the instance with the choices of
`Quotient.out`.** -/
theorem lpreMap_eq_X :
    lpreMap M = lpreMapX M (triE nlMap_rotTrans (nlE M)) (triE_tail (nlE_tail (M := M))) := rfl

/-- **The algorithm on the preprocessed map with explicit pendant darts**: `nlRun` with
`lpreMapX M e he` in place of `lpreMap M`. -/
noncomputable def nlRunX (e : PVert M → TDart M) (he : ∀ w, (tnlMap M).tail (e w) = w)
    (u : D → ℤ) (S T : Finset V) (τ : ADec (lpreMapX M e he)) (O : PlaneOracles.{w}) : D → ℤ :=
  nlExt M fun x => runL (lpreMapX M e he) (preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)) τ O
    (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) (.inl (old x))

/-- `nlRun` is the instance of `nlRunX` with the choices of `Quotient.out`. -/
theorem nlRun_eq_X (u : D → ℤ) (S T : Finset V) (τ : ADec (lpreMap M)) (O : PlaneOracles.{w}) :
    nlRun M u S T τ O =
      nlRunX M (triE nlMap_rotTrans (nlE M)) (triE_tail (nlE_tail (M := M))) u S T τ O := rfl

end Pp

end BKMNW

end PlanarFlow
