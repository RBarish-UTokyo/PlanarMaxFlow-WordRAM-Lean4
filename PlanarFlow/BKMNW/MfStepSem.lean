module

public import PlanarFlow.BKMNW.MfRoot

/-!
# The step `sepStep` of a node call, unrolled into the calls of its subroutines

At a node call `x = (.node l r π, Hs, σ)` the flow of the recursion is (`arunL`, `cflow`)

  `sepStep Oi U Sv Tv Hp univ L f₀`

on the piece map `pmap h` (`Oi = impl …` the implemented subroutines of the piece map, `Hp` its
holes `pholes`, `L = segsP …` the parts of the separator, `f₀` the sum of the children's flows).
This file unrolls `sepStep` into the sequence of the calls of its subroutines, so that a machine
program can run them one at a time:

* `sHoles Hs L j` (the holes of the step on the part `j`: the holes and the later parts),
  `segStep`, **`sst`** (the flow before the part `j`), **`sepStep_eq_sst`**;
* `hStep`, **`hst`** (the flow before the hole `i` of the loop of lines 10–12),
  **`holeLoop_eq_hst`** (when every hole is touched, the test of `holeLoop` always passes);
* `SCtx` (the data of one `sepStep`), `SCtx.seg`, `SCtx.hole`, `SCtx.c2s`, `SCtx.ret` (the
  intermediate flows), **`SCtx.seg_succ`** (the part `j` is FixConservationOnPath, the hole loop
  of `c2s`/`s2c`, and the two push-backs), **`SCtx.hole_succ`**;
* `SCond`, `stOr`, **`xCtx`** (the data at a node call), **`cflow_node_eq`**
  (`cflow x = (xCtx …).seg L.length`), `touch_pmap`, `sHoles_touch` (on a piece map every hole of
  the step is touched).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap

universe w

/-! ### The folds -/

section Fold

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'}

/-- **The holes of the step on the part `j`**: the holes and the later parts. -/
def sHoles (Hs : List (Finset V')) (L : List (SPath M')) (j : ℕ) : List (Finset V') :=
  Hs ++ (L.drop (j + 1)).map SPath.verts

lemma length_sHoles (Hs : List (Finset V')) (L : List (SPath M')) (j : ℕ) :
    (sHoles Hs L j).length = Hs.length + (L.length - (j + 1)) := by
  simp [sHoles]

lemma sHoles_cons_succ (Hs : List (Finset V')) (π : SPath M') (L : List (SPath M')) (j : ℕ) :
    sHoles Hs (π :: L) (j + 1) = sHoles Hs L j := by
  simp [sHoles]

/-- One part of `sepStep`. -/
noncomputable def segStep (O : NodeOracles M') (U : D' → ℤ) (S T : Finset V')
    (Hs : List (Finset V')) (P : Finset D') (L : List (SPath M')) (j : ℕ) (g : D' → ℤ) :
    D' → ℤ :=
  match L[j]? with
  | some π => nodeStep O U S T (sHoles Hs L j) P π g
  | none => g

/-- **The flow before the part `j`** of `sepStep`. -/
noncomputable def sst (O : NodeOracles M') (U : D' → ℤ) (S T : Finset V')
    (Hs : List (Finset V')) (P : Finset D') (L : List (SPath M')) (f : D' → ℤ) :
    ℕ → D' → ℤ
  | 0 => f
  | j + 1 => segStep O U S T Hs P L j (sst O U S T Hs P L f j)

lemma sst_cons (O : NodeOracles M') (U : D' → ℤ) (S T : Finset V') (Hs : List (Finset V'))
    (P : Finset D') (π : SPath M') (L : List (SPath M')) (f : D' → ℤ) :
    ∀ j, sst O U S T Hs P (π :: L) f (j + 1) =
      sst O U S T Hs P L (nodeStep O U S T (Hs ++ L.map SPath.verts) P π f) j
  | 0 => by simp [sst, segStep, sHoles]
  | j + 1 => by
    rw [sst, sst_cons O U S T Hs P π L f j, sst]
    simp only [segStep, List.getElem?_cons_succ, sHoles_cons_succ]

/-- **`sepStep` is the fold of its parts.** -/
theorem sepStep_eq_sst (O : NodeOracles M') (U : D' → ℤ) (S T : Finset V')
    (Hs : List (Finset V')) (P : Finset D') :
    ∀ (L : List (SPath M')) (f : D' → ℤ), sepStep O U S T Hs P L f = sst O U S T Hs P L f L.length
  | [], f => rfl
  | π :: L, f => by
    rw [sepStep, sepStep_eq_sst O U S T Hs P L, List.length_cons, sst_cons]

/-- One hole of the loop of lines 10–12, the test passed. -/
noncomputable def hStep (O : NodeOracles M') (U : D' → ℤ) (π : SPath M')
    (Hl : List (Finset V')) (i : ℕ) (g : D' → ℤ) : D' → ℤ :=
  match Hl[i]? with
  | some H => O.s2c U (O.c2s U g π H) π H
  | none => g

/-- **The flow before the hole `i`** of the loop of lines 10–12. -/
noncomputable def hst (O : NodeOracles M') (U : D' → ℤ) (π : SPath M')
    (Hl : List (Finset V')) (g : D' → ℤ) : ℕ → D' → ℤ
  | 0 => g
  | i + 1 => hStep O U π Hl i (hst O U π Hl g i)

lemma hst_cons (O : NodeOracles M') (U : D' → ℤ) (π : SPath M') (H : Finset V')
    (Hl : List (Finset V')) (g : D' → ℤ) :
    ∀ i, hst O U π (H :: Hl) g (i + 1) = hst O U π Hl (O.s2c U (O.c2s U g π H) π H) i
  | 0 => by simp [hst, hStep]
  | i + 1 => by
    rw [hst, hst_cons O U π H Hl g i, hst]
    simp only [hStep, List.getElem?_cons_succ]

/-- **The loop over the holes, all touched, is the fold of its holes.** -/
theorem holeLoop_eq_hst (O : NodeOracles M') (U : D' → ℤ) (P : Finset D') (π : SPath M') :
    ∀ (Hl : List (Finset V')) (g : D' → ℤ), (∀ H ∈ Hl, ∃ v ∈ H, Touch M' P v) →
      holeLoop O U P π Hl g = hst O U π Hl g Hl.length
  | [], g, _ => rfl
  | H :: Hl, g, hT => by
    have h1 : ∃ v ∈ H, Touch M' P v := hT H (List.mem_cons_self ..)
    have h2 : ∀ H' ∈ Hl, ∃ v ∈ H', Touch M' P v := fun H' h => hT H' (List.mem_cons_of_mem _ h)
    rw [holeLoop, List.length_cons, hst_cons]
    simp only [h1, ↓reduceIte]
    exact holeLoop_eq_hst O U P π Hl _ h2

/-! ### The data of one `sepStep` and its intermediate flows -/

/-- **The data of one `sepStep`**: the subroutines, the capacities, the terminals, the holes, the
piece, the parts of the separator and the starting flow. -/
structure SCtx (M' : CombMap D' V' F') where
  O : NodeOracles M'
  U : D' → ℤ
  S : Finset V'
  T : Finset V'
  Hs : List (Finset V')
  P : Finset D'
  L : List (SPath M')
  f : D' → ℤ

namespace SCtx

variable (C : SCtx M')

/-- The flow before the part `j`. -/
noncomputable def seg (j : ℕ) : D' → ℤ := sst C.O C.U C.S C.T C.Hs C.P C.L C.f j

/-- The holes of the step on the part `j`. -/
def holes (j : ℕ) : List (Finset V') := sHoles C.Hs C.L j

/-- The flow before the hole `i` of the part `j` (`π` the part `j`): after FixConservationOnPath,
the first `i` holes. -/
noncomputable def hole (j : ℕ) (π : SPath M') (i : ℕ) : D' → ℤ :=
  hst C.O C.U π (C.holes j) (C.O.fix C.U (C.seg j) π) i

/-- The flow after `c2s` on the hole `H` (the hole `i` of the part `j`). -/
noncomputable def c2s (j : ℕ) (π : SPath M') (i : ℕ) (H : Finset V') : D' → ℤ :=
  C.O.c2s C.U (C.hole j π i) π H

/-- The flow after the push-back of the excess to the sources (line 13). -/
noncomputable def ret (j : ℕ) (π : SPath M') : D' → ℤ :=
  C.O.ret C.U (C.hole j π (C.holes j).length)
    (posSet M' (C.hole j π (C.holes j).length) π.verts) C.S

lemma seg_zero : C.seg 0 = C.f := rfl

/-- **The part `j`**: FixConservationOnPath, the holes, the two push-backs. -/
theorem seg_succ {j : ℕ} {π : SPath M'} (hj : C.L[j]? = some π)
    (hT : ∀ H ∈ C.holes j, ∃ v ∈ H, Touch M' C.P v) :
    C.seg (j + 1) = C.O.frm C.U (C.ret j π) C.T (negSet M' (C.ret j π) π.verts) := by
  have e := holeLoop_eq_hst C.O C.U C.P π (sHoles C.Hs C.L j) (C.O.fix C.U (C.seg j) π) hT
  show segStep C.O C.U C.S C.T C.Hs C.P C.L j (C.seg j) = _
  simp only [segStep, hj, nodeStep]
  rw [e]
  rfl

lemma hole_zero (j : ℕ) (π : SPath M') : C.hole j π 0 = C.O.fix C.U (C.seg j) π := rfl

/-- **One hole**: `c2s`, then `s2c`. -/
theorem hole_succ {j i : ℕ} {π : SPath M'} {H : Finset V'} (hi : (C.holes j)[i]? = some H) :
    C.hole j π (i + 1) = C.O.s2c C.U (C.c2s j π i H) π H := by
  show hStep C.O C.U π (C.holes j) i (C.hole j π i) = _
  simp only [hStep, hi]
  rfl

end SCtx

end Fold

/-! ### At a node call -/

section Call

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- The condition of `arunL` at a node call. -/
def SCond (l r : ADec M) (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) : Prop :=
  PieceInv M (l.piece ∪ r.piece) Hs σ ∧ ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s

/-- The implemented subroutines of a piece map. -/
noncomputable def stOr (O : PlaneOracles.{w}) {P : Finset D} {Hs : List (Finset V)}
    {σ : Perm D} (h : PieceInv M P Hs σ) : NodeOracles (pmap h) :=
  impl (pmap h) (Klein.msspPlaneK (pmap h)) (O.fr _) (O.negSSSP (pmap h)) (O.stflow (pmap h))

variable (M) in
/-- **The data of the step at a node call** (`arunL`). -/
noncomputable def xCtx (O : PlaneOracles.{w}) (u : D → ℤ) (S T : Finset V) (l r : ADec M)
    (π : HSep M) (Hs : List (Finset V)) (σ : Perm D) (h : SCond M l r π Hs σ) :
    SCtx (pmap h.1) where
  O := stOr O h.1
  U := fun x => u x.1
  S := vimg M σ _ S
  T := vimg M σ _ T
  Hs := pholes M σ (pdarts M (l.piece ∪ r.piece) Hs) Hs
  P := univ
  L := segsP h.1 π.segs h.2
  f := joinFlow (B := pdarts M (l.piece ∪ r.piece) Hs)
    (cflow M O u S T (chL M l r π Hs σ)) (cflow M O u S T (chR M l r π Hs σ))

lemma length_segsP {P : Finset D} {Hs : List (Finset V)} {σ : Perm D} (h : PieceInv M P Hs σ) :
    ∀ (L : List (SPath M)) (hL : ∀ π ∈ L, SegIn M P Hs π), (segsP h L hL).length = L.length
  | [], _ => rfl
  | π :: L, hL => by rw [segsP, List.length_cons, List.length_cons, length_segsP h L]

/-- **The flow of a node call is the last flow of the unrolled step.** -/
theorem cflow_node_eq (O : PlaneOracles.{w}) (u : D → ℤ) (S T : Finset V) {l r : ADec M}
    {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ) :
    cflow M O u S T (.node l r π, Hs, σ) = (xCtx M O u S T l r π Hs σ h).seg π.segs.length := by
  have h' : PieceInv M (l.piece ∪ r.piece) Hs σ ∧
      ∀ s ∈ π.segs, SegIn M (l.piece ∪ r.piece) Hs s := h
  show arunL M O u S T (.node l r π) Hs σ = _
  rw [arunL, dite_of_pos h']
  exact (sepStep_eq_sst _ _ _ _ _ _ _ _).trans
    (congrArg (sst _ _ _ _ _ _ _ _) (length_segsP h.1 π.segs h.2))

/-- On a piece map every vertex is the tail of a dart. -/
lemma touch_pmap {P : Finset D} {Hs : List (Finset V)} {σ : Perm D} (h : PieceInv M P Hs σ)
    (v : SVert σ (pdarts M P Hs)) : Touch (pmap h) univ v := by
  induction v using Quotient.inductionOn with
  | h x => exact ⟨x, mem_univ _, rfl⟩

/-- **Every hole of the step on a piece map is touched**: the holes of the piece map are
nonempty, and so are the vertex sets of the later parts. -/
lemma sHoles_touch {P : Finset D} {Hs : List (Finset V)} {σ : Perm D} (h : PieceInv M P Hs σ)
    (L : List (SPath (pmap h))) (j : ℕ) :
    ∀ H ∈ sHoles (pholes M σ (pdarts M P Hs) Hs) L j, ∃ v ∈ H, Touch (pmap h) univ v := by
  intro H hH
  simp only [sHoles, List.mem_append, List.mem_map] at hH
  rcases hH with hH | ⟨π, -, rfl⟩
  · simp only [pholes, List.mem_filter, decide_eq_true_eq] at hH
    obtain ⟨v, hv⟩ := hH.2
    exact ⟨v, hv, touch_pmap h v⟩
  · exact ⟨π.p 0, π.p_mem_init (Nat.zero_le _), touch_pmap h _⟩

/-- The touch hypothesis of `SCtx.seg_succ` at a node call. -/
lemma xCtx_touch (O : PlaneOracles.{w}) (u : D → ℤ) (S T : Finset V) {l r : ADec M}
    {π : HSep M} {Hs : List (Finset V)} {σ : Perm D} (h : SCond M l r π Hs σ) (j : ℕ) :
    ∀ H ∈ (xCtx M O u S T l r π Hs σ h).holes j, ∃ v ∈ H,
      Touch (pmap h.1) (xCtx M O u S T l r π Hs σ h).P v :=
  sHoles_touch h.1 _ j

end Call

end MfDrv

end BKMNW

end PlanarFlow
