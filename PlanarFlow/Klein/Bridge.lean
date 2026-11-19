module

public import PlanarFlow.Klein.Trip
public import PlanarFlow.Klein.CutReach

/-!
# Klein's trip as multiple-source shortest paths for the maximum-flow algorithm

The labels of a trip (`PlanarFlow.Klein.IsTrip`) at the start of the move `j` are the distances
from the root `tail (g j)` (`IsTrip.labels`). This file reads them as the answers of a
multiple-source shortest path structure, as an alternative to the structure of Das, Kipouridis,
Probst Gutenberg and Wulff-Nilsen (`PlanarFlow.MSSP.dkpwNN`, `PlanarFlow.BKMNW.msspPlane`, which
are kept).

* `kleinAns`: the answers of the trip `kleinTrip` from the root `tail (g j)`: the label at the
  start of the move `j` at the vertices reached, `none` elsewhere; `kleinAns_eq`: they are the
  distances `odist`.
* `kleinNN`: for nonnegative lengths, the trip on the perturbed lengths (which meet the
  assumptions `Hyp`), answers divided by `2^|D|`; `kleinNN_eq`: they are the distances for the
  lengths themselves.
* `Cut.answerK`, `msspCutK`, `msspPlaneK`: the answers on a cut of the dual graph minus a path
  (`PlanarFlow.BKMNW.Cut`) on which the roots reach the same vertices (`SameReach`, which
  `cut_hyp_sameReach` provides for the cut `cutOf` built in `PlanarFlow/BKMNW/CutBuild.lean`).
* `msspPlaneK_spec`: **Klein's trip meets the specification `PlanarFlow.BKMNW.MSSPSpec` of
  multiple-source shortest paths in the dual graph minus a path**, for every plane map with
  transitive rotations and faces.

For the pieces of the recursion for negative lengths (`PlanarFlow.NegSSSP.PieceMSSPSpec`), whose
sources lie on one face of a plane map but may be entered by darts of the piece, the sources are
first copied inside the face (`PlanarFlow.Klein.srcMap`, `PlanarFlow/Klein/Sources.lean`;
`PlanarFlow.NegSSSP.msspK`, `PlanarFlow/NegSSSP/FaceKlein.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

section Answers

open Classical in
/-- **The answers of the trip from the root of the move `j`**: the label at the start of the
move at the vertices reached from the root, `none` elsewhere. -/
noncomputable def kleinAns (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (j : ℕ) (x : V) :
    Option ℤ :=
  if Reach (pieceGraph M S ℓ) (tripSrc M k g j) x then
    some (((kleinTrip H hR j).T 0).psum (tripφ S ℓ) x)
  else none

/-- **The answers of the trip are the distances.** -/
theorem kleinAns_eq (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (j : ℕ) :
    kleinAns H hR j = odist (pieceGraph M S ℓ) (tripSrc M k g j) := by
  funext x
  unfold kleinAns odist
  split_ifs with h
  · rw [(kleinTrip_isTrip H hR).labels H hR j h]
  · rfl

/-- **The trip for nonnegative lengths**: run on the perturbed lengths, answers divided by
`2^|D|`. -/
noncomputable def kleinNN (H : HypNN M k g S ℓ) (hR : SameReach M k g S (pert ℓ)) (j : ℕ)
    (x : V) : Option ℤ :=
  (kleinAns H.hyp hR j x).map (· / 2 ^ Fintype.card D)

/-- **The trip for nonnegative lengths gives the distances for the lengths themselves.** -/
theorem kleinNN_eq (H : HypNN M k g S ℓ) (hR : SameReach M k g S (pert ℓ)) (j : ℕ) :
    kleinNN H hR j = odist (pieceGraph M S ℓ) (tripSrc M k g j) := by
  funext x
  have hP := isPerturb_pert M S ℓ
  have hnn : ∀ a : {d // d ∈ S}, 0 ≤ (pieceGraph M S ℓ).len a := fun a => H.nonneg a.1 a.2
  unfold kleinNN
  rw [kleinAns_eq]
  unfold odist
  split_ifs with h1 h2 h2
  · rw [Option.map_some, ← hP.dist_div hnn h2]
  · exact absurd (hP.reach_iff.1 h1) h2
  · exact absurd (hP.reach_iff.2 h2) h1
  · rfl

/-- The answers of the trip for nonnegative lengths meet the specification of distances. -/
theorem kleinNN_isDist (H : HypNN M k g S ℓ) (hR : SameReach M k g S (pert ℓ)) {j : ℕ}
    (hj : j < k) :
    BKMNW.IsDist (pieceGraph M S ℓ) (M.tail (g j)) (kleinNN H hR j) := by
  rw [kleinNN_eq]
  unfold tripSrc
  rw [Nat.mod_eq_of_lt hj]
  exact isDist_odist (fun a => H.nonneg a.1 a.2) _

end Answers

/-! ### On the cuts -/

section Cuts

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']
variable {ℓ : D → ℤ} {L : List D}

open Classical in
/-- **The answers of the trip on a cut** (whose roots reach the same vertices): from the face `x`,
the answers from its root at the copies of the faces. -/
noncomputable def _root_.PlanarFlow.BKMNW.Cut.answerK (C : Cut M ℓ L D' V' F')
    (hR : SameReach C.map C.k C.g C.piece (pert C.len)) (x y : F) : Option ℤ :=
  if h : ∃ j, j < C.k ∧ C.root j = x then
    kleinNN C.hyp hR (Nat.find h) (C.vx y)
  else none

/-- **On a cut, the trip gives the distances in the dual graph minus `L`** from every face of a
root. -/
theorem _root_.PlanarFlow.BKMNW.Cut.isDistK (C : Cut M ℓ L D' V' F')
    (hR : SameReach C.map C.k C.g C.piece (pert C.len)) {x : F} (hx : ∃ j, j < C.k ∧ C.root j = x) :
    BKMNW.IsDist ((M.dualGraph ℓ).restrict fun e => e ∉ L) x (C.answerK hR x) := by
  classical
  set j := Nat.find hx with hjdef
  have hj : j < C.k ∧ C.root j = x := Nat.find_spec hx
  have e : C.answerK hR x = fun y => kleinNN C.hyp hR j (C.vx y) := by
    funext y; simp only [BKMNW.Cut.answerK, hx, ↓reduceDIte, hjdef]
  rw [e]
  have hD := kleinNN_isDist C.hyp hR hj.1
  rw [← hj.2]
  refine isDist_of_embed (G := (M.dualGraph ℓ).restrict fun e => e ∉ L)
    (G' := MSSP.pieceGraph C.map C.piece C.len) (arc := C.arc) C.vx_inj
    C.tail_arc C.head_arc C.len_arc ?_ (C.root_ne j hj.1) ?_ ?_ hD
  · intro b
    rcases C.cover b.1 b.2 with ⟨e, he⟩ | ⟨i, hi, h1, -, -⟩
    · exact Or.inl ⟨e, Subtype.ext he⟩
    · right; intro y; change C.map.tail b.1 ≠ _; rw [h1]; exact C.root_ne i hi y
  · intro b hb
    change C.map.tail b.1 = C.map.tail (C.g j) at hb
    rcases C.cover b.1 b.2 with ⟨e, he⟩ | ⟨i, hi, h1, h2, h3⟩
    · rw [← he, C.tail_arc] at hb
      exact absurd hb.symm (C.root_ne j hj.1 _)
    · have hij : i = j := C.hyp.face.inj i hi j hj.1 (h1.symm.trans hb)
      subst hij
      exact ⟨h2, h3⟩
  · obtain ⟨d, hd, h1⟩ := C.pend j hj.1
    exact ⟨⟨d, hd⟩, h1⟩

variable (M D' V' F') in
open Classical in
/-- **Multiple-source shortest paths by Klein's trip on a cut** of the dual graph minus `L` whose
roots reach the same vertices (`none` when there is no such cut). -/
noncomputable def msspCutK (L : List D) (ℓ : D → ℤ) (x y : F) : Option ℤ :=
  if h : ∃ C : Cut M ℓ L D' V' F', SameReach C.map C.k C.g C.piece (pert C.len) then
    h.choose.answerK h.choose_spec x y
  else none

/-- The trip on a cut gives the distances in the dual graph minus `L` from every face along
`L`, when there is a cut whose roots reach the same vertices. -/
theorem msspCutK_isDist
    (h : ∃ C : Cut M ℓ L D' V' F', SameReach C.map C.k C.g C.piece (pert C.len)) {x : F}
    (hx : x ∈ (L.map M.face).toFinset) :
    BKMNW.IsDist ((M.dualGraph ℓ).restrict fun e => e ∉ L) x (msspCutK M D' V' F' L ℓ x) := by
  have e : msspCutK M D' V' F' L ℓ x = h.choose.answerK h.choose_spec x := by
    funext y; simp only [msspCutK, h, ↓reduceDIte]
  rw [e]
  obtain ⟨j, hj, hjx⟩ := h.choose.srcs x hx
  exact h.choose.isDistK h.choose_spec ⟨j, hj, hjx⟩

end Cuts

/-- **Multiple-source shortest paths in the dual graph minus the darts `L` by Klein's trip**, on
the cut of `M` along `L` (with the dart, vertex and face types `CutD`, `CutV`, `CutF`). -/
noncomputable def msspPlaneK (M : CombMap D V F) (L : List D) (ℓ : D → ℤ) (x y : F) :
    Option ℤ :=
  msspCutK M (CutD M L) (CutV M L) (CutF M L) L ℓ x y

/-- **Klein's trip meets the specification of multiple-source shortest paths in the dual graph
minus a path** used by the maximum-flow algorithm, for every plane map with transitive rotations
and transitive faces. -/
theorem msspPlaneK_spec (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) :
    BKMNW.MSSPSpec M (msspPlaneK M) := by
  intro P ℓ hnn x hx
  have hk : 0 < P.k := by
    rcases Nat.eq_zero_or_pos P.k with h | h
    · simp [SPath.faces, SPath.darts, h] at hx
    · exact h
  obtain ⟨C, -, hR⟩ := cut_hyp_sameReach hM hrot hface P ℓ hnn hk
  exact msspCutK_isDist ⟨C, hR⟩ hx

end Klein

end PlanarFlow
