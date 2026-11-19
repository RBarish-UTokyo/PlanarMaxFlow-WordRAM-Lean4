module

public import PlanarFlow.BKMNW.FixPath
public import PlanarFlow.MSSP.Perturb

/-!
# The multiple-source shortest path library and the specification of the algorithm

The library `PlanarFlow/MSSP` (Das, Kipouridis, Probst Gutenberg and Wulff-Nilsen, SOSA 2022) has
its own walks and distances (`PlanarFlow/MSSP/Defs.lean`, `PlanarFlow/MSSP/Walk.lean`). This file
relates them to the list walks and distances of the specifications of the algorithm of
Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (`PlanarFlow/BKMNW/Dist.lean`), and to the
specification `MSSPSpec` of multiple-source shortest paths in the dual graph minus a simple path
(`PlanarFlow/BKMNW/FixPath.lean`).

## Walks and distances

* `isWalk_iff_lwalk`: the walks are the same (`MSSP.LWalk G x y l ↔ IsWalk G x l y`), and so are
  the lengths (`wlen_eq_mssp`).
* `isDist_odist`: for nonnegative lengths, the distances `MSSP.odist G r` of the library meet
  `IsDist G r`; `odist_eq_of_isDist`: they are the only ones.
* `isDist_iff_mssp`: on a nonempty type of arcs, the indexed distances `MSSP.IsDist` are the
  distances `IsDist` (with no arcs at all, the indexed form has no walks, not even the empty one);
  `msspOut_iff`, `isDDGOf_of_mssp`: the same for outputs of multiple-source shortest paths and for
  dense distance graphs.
* `dkpwNN_eq_odist`, `dkpwNN_isDist`: the data structure of the article, on a piece of a plane map
  in its setting (`MSSP.HypNN`), answers with the distances `IsDist` from every root.

## The dual graph minus a path

`MSSPSpec` asks for the distances in `H* = (M.dualGraph ℓ).restrict (· ∉ P.darts)` from the faces
`X*` along `P`. The data structure answers for the roots of a face of a plane map whose boundary
walk is a simple cycle with no arc of the piece entering a root (`MSSP.HypNN`). The faces of `X*`
lie on one face of `H*`, but its boundary walk visits a face of `X*` once for every side of a dart
of `P` that it borders, so it is not a simple cycle of `H*` itself. A **cut** (`Cut`) packages the
plane map in which the article runs Klein's algorithm: a plane map in the setting `MSSP.HypNN`
containing a copy of `H*` (`vx`, `arc`), and inside the face a ring of new root vertices, each with
pendant arcs of length `0` to the face of `X*` it stands for.

* `isDist_of_embed`: distances from a pendant root of a digraph containing a copy of `G` are the
  distances in `G` from the end of the pendant arcs.
* `Cut.isDist`: from a cut, the data structure gives the distances in `H*` from every face of `X*`.
* `msspCut_isDist`, `msspCut_spec`: **if a cut exists for every simple path and every choice of
  lengths that are nonnegative off the path** (and some face along it), then the data structure
  run on a cut meets `MSSPSpec`.

The construction of a cut from a plane map `M` and a simple path `P` of `M` (the dual map of `M`
with the darts of `P` deleted, opened along `P`, with the ring of roots added inside the face, and
its planarity and transitive rotations) is in `PlanarFlow/BKMNW/CutBuild.lean`
(`PlanarFlow.BKMNW.msspPlane_spec`).

* `dualDist`, `dualDist_spec`: **a witness only that `MSSPSpec` is satisfiable**, not an
  algorithm: the distances themselves.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

/-! ### Walks and distances -/

section Walks

variable {X A : Type*} {G : Digraph X A}

/-- **The walks of the library are the walks of the specification.** -/
theorem isWalk_iff_lwalk {x y : X} {l : List A} : IsWalk G x l y ↔ MSSP.LWalk G x y l := by
  induction l generalizing x with
  | nil => rw [isWalk_nil, MSSP.LWalk.nil_iff]
  | cons a l ih => rw [isWalk_cons, MSSP.LWalk.cons_iff, ih]

/-- The lengths of walks agree. -/
theorem wlen_eq_mssp (l : List A) : wlen G l = MSSP.wlen G l := rfl

/-- **The distances of the library meet the specification** (nonnegative lengths). -/
theorem isDist_odist (hnn : ∀ a, 0 ≤ G.len a) (r : X) : IsDist G r (MSSP.odist G r) where
  some_walk y ℓ h := by
    unfold MSSP.odist at h
    split_ifs at h with hr
    cases h
    obtain ⟨l, hl, he⟩ := MSSP.exists_walk_dist hnn hr
    exact ⟨l, isWalk_iff_lwalk.2 hl, he⟩
  some_le y ℓ h l hl := by
    unfold MSSP.odist at h
    split_ifs at h with hr
    cases h
    exact MSSP.dist_le hnn (isWalk_iff_lwalk.1 hl)
  none y h l hl := by
    unfold MSSP.odist at h
    split_ifs at h with hr
    exact hr ⟨l, isWalk_iff_lwalk.1 hl⟩

/-- **(a) The distances of the library are the distances of the specification** (nonnegative
lengths). -/
theorem odist_eq_of_isDist (hnn : ∀ a, 0 ≤ G.len a) {r : X} {δ : X → Option ℤ}
    (h : IsDist G r δ) : δ = MSSP.odist G r :=
  h.unique (isDist_odist hnn r)

/-- **(a) The indexed distances of the library are the distances of the specification**, on a
nonempty type of arcs. -/
theorem isDist_iff_mssp [Nonempty A] {r : X} {δ : X → Option ℤ} :
    IsDist G r δ ↔ MSSP.IsDist G r δ := by
  obtain ⟨a₀⟩ := ‹Nonempty A›
  constructor
  · intro h
    refine ⟨fun y ℓ hy => ?_, fun y ℓ hy m c hw => ?_, fun y hy m c hw => ?_⟩
    · obtain ⟨l, hl, he⟩ := h.some_walk y ℓ hy
      exact MSSP.exists_isWalk_iff.2 ⟨l, isWalk_iff_lwalk.1 hl, he⟩
    · obtain ⟨h1, h2⟩ := MSSP.lwalk_of_isWalk hw
      rw [← h2]; exact h.some_le y ℓ hy _ (isWalk_iff_lwalk.2 h1)
    · exact h.none y hy _ (isWalk_iff_lwalk.2 (MSSP.lwalk_of_isWalk hw).1)
  · intro h
    refine ⟨fun y ℓ hy => ?_, fun y ℓ hy l hl => ?_, fun y hy l hl => ?_⟩
    · obtain ⟨l, hl, he⟩ := MSSP.exists_isWalk_iff.1 (h.some_walk y ℓ hy)
      exact ⟨l, isWalk_iff_lwalk.2 hl, he⟩
    · obtain ⟨h1, h2⟩ := MSSP.isWalk_of_lwalk (isWalk_iff_lwalk.1 hl) a₀
      rw [wlen_eq_mssp, ← h2]; exact h.some_le y ℓ hy _ _ h1
    · exact h.none y hy _ _ (MSSP.isWalk_of_lwalk (isWalk_iff_lwalk.1 hl) a₀).1

/-- Outputs of multiple-source shortest paths of the library are distances of the
specification. -/
theorem msspOut_iff [Nonempty A] {B : Finset X} {δ : X → X → Option ℤ} :
    MSSP.MSSPOut G B δ ↔ ∀ b ∈ B, IsDist G b (δ b) :=
  forall₂_congr fun _ _ => isDist_iff_mssp.symm

/-- Dense distance graphs of the library are dense distance graphs of the specification. -/
theorem isDDGOf_of_mssp [Nonempty A] {H : MSSP.DDG X} (h : MSSP.IsDDGOf G H) :
    IsDDGOf G ⟨H.bdry, H.len⟩ :=
  fun b hb => let ⟨δ, h1, h2⟩ := h b hb; ⟨δ, isDist_iff_mssp.2 h1, h2⟩

end Walks

/-! ### The data structure on a piece of a plane map -/

section Piece

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}

/-- **The data structure for nonnegative lengths answers with the distances** from every root. -/
theorem dkpwNN_eq_odist (H : MSSP.HypNN M k g S ℓ) (hS : S.Nonempty) {j : ℕ} (hj : j < k) :
    MSSP.dkpwNN M k g S ℓ (M.tail (g j)) = MSSP.odist (MSSP.pieceGraph M S ℓ) (M.tail (g j)) := by
  funext v
  have e := MSSP.dkpw_pert H hj (M.face (g 0)) ∅ v
  unfold MSSP.dkpwNN
  rw [e]
  simp [MSSP.msspDist, hS]

/-- **The data structure for nonnegative lengths meets the specification of distances** from
every root. -/
theorem dkpwNN_isDist (H : MSSP.HypNN M k g S ℓ) (hS : S.Nonempty) {j : ℕ} (hj : j < k) :
    IsDist (MSSP.pieceGraph M S ℓ) (M.tail (g j)) (MSSP.dkpwNN M k g S ℓ (M.tail (g j))) := by
  rw [dkpwNN_eq_odist H hS hj]
  exact isDist_odist (fun a => H.nonneg a.1 a.2) _

end Piece

/-! ### Distances from a pendant root -/

section Embed

variable {X A Y B : Type*} {G : Digraph X A} {G' : Digraph Y B} {vx : X → Y} {arc : A → B}

/-- Walks of `G` are walks of a digraph containing a copy of it. -/
lemma IsWalk.embed (hsrc : ∀ a, G'.src (arc a) = vx (G.src a))
    (hdst : ∀ a, G'.dst (arc a) = vx (G.dst a)) (hlen : ∀ a, G'.len (arc a) = G.len a)
    {x y : X} {l : List A} (h : IsWalk G x l y) :
    IsWalk G' (vx x) (l.map arc) (vx y) ∧ wlen G' (l.map arc) = wlen G l := by
  induction l generalizing x with
  | nil => simp only [isWalk_nil] at h; subst h; simp
  | cons a l ih =>
    obtain ⟨h1, h2⟩ := h
    obtain ⟨i1, i2⟩ := ih h2
    refine ⟨⟨by rw [hsrc, h1], by rw [hdst]; exact i1⟩, ?_⟩
    simp only [List.map_cons, wlen_cons, hlen, i2]

/-- Walks between copies of vertices of `G` are walks of `G`, when the other arcs leave
vertices outside the copy. -/
lemma IsWalk.unembed (hinj : Function.Injective vx) (hsrc : ∀ a, G'.src (arc a) = vx (G.src a))
    (hdst : ∀ a, G'.dst (arc a) = vx (G.dst a)) (hlen : ∀ a, G'.len (arc a) = G.len a)
    (hcover : ∀ b, (∃ a, arc a = b) ∨ ∀ y, G'.src b ≠ vx y) {x y : X} {l' : List B}
    (h : IsWalk G' (vx x) l' (vx y)) : ∃ l, IsWalk G x l y ∧ wlen G l = wlen G' l' := by
  induction l' generalizing x with
  | nil => exact ⟨[], hinj h, rfl⟩
  | cons b l' ih =>
    obtain ⟨h1, h2⟩ := h
    rcases hcover b with ⟨a, rfl⟩ | hb
    · rw [hsrc] at h1
      rw [hdst] at h2
      obtain ⟨l, hl, he⟩ := ih h2
      exact ⟨a :: l, ⟨hinj h1, hl⟩, by simp only [wlen_cons, he, hlen]⟩
    · exact absurd h1 (hb x)

/-- **Distances from a pendant root**: if `G'` contains a copy of `G`, its other arcs leave
vertices outside the copy, and the arcs leaving the root `r` (there is one) are arcs of length `0`
to the copy of `x₀`, then the distances in `G'` from `r` to the copy are the distances in `G` from
`x₀`. -/
theorem isDist_of_embed (hinj : Function.Injective vx) (hsrc : ∀ a, G'.src (arc a) = vx (G.src a))
    (hdst : ∀ a, G'.dst (arc a) = vx (G.dst a)) (hlen : ∀ a, G'.len (arc a) = G.len a)
    (hcover : ∀ b, (∃ a, arc a = b) ∨ ∀ y, G'.src b ≠ vx y) {r : Y} {x₀ : X}
    (hr : ∀ y, r ≠ vx y) (hout : ∀ b, G'.src b = r → G'.dst b = vx x₀ ∧ G'.len b = 0)
    (hpend : ∃ b, G'.src b = r) {δ : Y → Option ℤ} (h : IsDist G' r δ) :
    IsDist G x₀ (fun y => δ (vx y)) := by
  obtain ⟨b₀, hb₀⟩ := hpend
  -- walks of `G` from `x₀` give walks of `G'` from `r`
  have up : ∀ y l, IsWalk G x₀ l y →
      IsWalk G' r (b₀ :: l.map arc) (vx y) ∧ wlen G' (b₀ :: l.map arc) = wlen G l := by
    intro y l hl
    obtain ⟨e1, e2⟩ := hl.embed hsrc hdst hlen
    obtain ⟨d1, d2⟩ := hout b₀ hb₀
    exact ⟨⟨hb₀, by rw [d1]; exact e1⟩, by rw [wlen_cons, d2, e2, zero_add]⟩
  -- walks of `G'` from `r` give walks of `G` from `x₀`
  have down : ∀ y l', IsWalk G' r l' (vx y) → ∃ l, IsWalk G x₀ l y ∧ wlen G l = wlen G' l' := by
    intro y l' hl'
    cases l' with
    | nil => exact absurd hl' (hr y)
    | cons b l' =>
      obtain ⟨h1, h2⟩ := hl'
      obtain ⟨d1, d2⟩ := hout b h1
      rw [d1] at h2
      obtain ⟨l, hl, he⟩ := h2.unembed hinj hsrc hdst hlen hcover
      exact ⟨l, hl, by rw [wlen_cons, d2, zero_add, he]⟩
  refine ⟨fun y ℓ hy => ?_, fun y ℓ hy l hl => ?_, fun y hy l hl => ?_⟩
  · obtain ⟨l', hl', he⟩ := h.some_walk _ ℓ hy
    obtain ⟨l, hl, he'⟩ := down y l' hl'
    exact ⟨l, hl, he'.trans he⟩
  · obtain ⟨u1, u2⟩ := up y l hl
    rw [← u2]; exact h.some_le _ ℓ hy _ u1
  · exact h.none _ hy _ (up y l hl).1

end Embed

/-! ### The dual graph minus a path -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **A cut of the dual graph minus the darts `L`** (`H*` of the article, with lengths `ℓ`): a
plane map `map` in the setting of the data structure (`MSSP.HypNN`, with the face cycle `g` of
`k` darts) whose piece contains a copy of `H*` (the faces of `M` as vertices `vx`, the darts off
`L` as arcs `arc`), and otherwise only pendant arcs of length `0` from each root `tail (g j)` (a
new vertex) to the face `root j`; every face along `L` is the face of a root. -/
structure Cut (M : CombMap D V F) (ℓ : D → ℤ) (L : List D) (D' V' F' : Type*) [Fintype D']
    [DecidableEq D'] [Fintype V'] [DecidableEq V'] [Fintype F'] [DecidableEq F'] where
  /-- The plane map. -/
  map : CombMap D' V' F'
  /-- The number of roots. -/
  k : ℕ
  /-- The boundary walk of the face of the roots. -/
  g : ℕ → D'
  /-- The darts of the piece. -/
  piece : Finset D'
  /-- The lengths. -/
  len : D' → ℤ
  hyp : MSSP.HypNN map k g piece len
  /-- The copy of the faces of `M`. -/
  vx : F → V'
  vx_inj : Function.Injective vx
  /-- The copy of the darts off `L`. -/
  arc : {e // e ∉ L} → {d // d ∈ piece}
  tail_arc : ∀ e, map.tail (arc e).1 = vx (M.face e.1)
  head_arc : ∀ e, map.head (arc e).1 = vx (M.face (M.rev e.1))
  len_arc : ∀ e, len (arc e).1 = ℓ e.1
  /-- The face of `M` for which a root stands. -/
  root : ℕ → F
  root_ne : ∀ j < k, ∀ y, map.tail (g j) ≠ vx y
  pend : ∀ j < k, ∃ d ∈ piece, map.tail d = map.tail (g j)
  cover : ∀ d ∈ piece, (∃ e, (arc e).1 = d) ∨
    ∃ j < k, map.tail d = map.tail (g j) ∧ map.head d = vx (root j) ∧ len d = 0
  srcs : ∀ x ∈ (L.map M.face).toFinset, ∃ j < k, root j = x

namespace Cut

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']
variable {M : CombMap D V F} {ℓ : D → ℤ} {L : List D}

open Classical in
/-- **The answer of the data structure on a cut**: from the face `x`, the answers from its root
at the copies of the faces. -/
noncomputable def answer (C : Cut M ℓ L D' V' F') (x y : F) : Option ℤ :=
  if h : ∃ j, j < C.k ∧ C.root j = x then
    MSSP.dkpwNN C.map C.k C.g C.piece C.len (C.map.tail (C.g (Nat.find h))) (C.vx y)
  else none

/-- **On a cut, the data structure gives the distances in the dual graph minus `L`** from every
face of a root. -/
theorem isDist (C : Cut M ℓ L D' V' F') {x : F} (hx : ∃ j, j < C.k ∧ C.root j = x) :
    IsDist ((M.dualGraph ℓ).restrict fun e => e ∉ L) x (C.answer x) := by
  classical
  set j := Nat.find hx with hjdef
  have hj : j < C.k ∧ C.root j = x := Nat.find_spec hx
  have e : C.answer x = fun y => MSSP.dkpwNN C.map C.k C.g C.piece C.len
      (C.map.tail (C.g j)) (C.vx y) := by
    funext y; simp only [answer, hx, ↓reduceDIte, hjdef]
  rw [e]
  have hS : C.piece.Nonempty := by
    obtain ⟨d, hd, -⟩ := C.pend j hj.1; exact ⟨d, hd⟩
  have hD := dkpwNN_isDist C.hyp hS hj.1
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

end Cut

open Classical in
/-- **Multiple-source shortest paths from a cut**: the answer of the data structure on some cut
of the dual graph minus `L` with vertex, dart and face types `V'`, `D'`, `F'` (`none` when there is
no cut). -/
noncomputable def msspCut (M : CombMap D V F) (D' V' F' : Type*) [Fintype D'] [DecidableEq D']
    [Fintype V'] [DecidableEq V'] [Fintype F'] [DecidableEq F'] (L : List D) (ℓ : D → ℤ)
    (x y : F) : Option ℤ :=
  if h : Nonempty (Cut M ℓ L D' V' F') then h.some.answer x y else none

/-- **The data structure on a cut gives the distances in the dual graph minus `L`** from every
face along `L`, when there is a cut. -/
theorem msspCut_isDist {M : CombMap D V F} {D' V' F' : Type*} [Fintype D'] [DecidableEq D']
    [Fintype V'] [DecidableEq V'] [Fintype F'] [DecidableEq F'] {L : List D} {ℓ : D → ℤ}
    (h : Nonempty (Cut M ℓ L D' V' F')) {x : F} (hx : x ∈ (L.map M.face).toFinset) :
    IsDist ((M.dualGraph ℓ).restrict fun e => e ∉ L) x (msspCut M D' V' F' L ℓ x) := by
  have e : msspCut M D' V' F' L ℓ x = h.some.answer x := by
    funext y; simp only [msspCut, h, ↓reduceDIte]
  rw [e]
  obtain ⟨j, hj, hjx⟩ := h.some.srcs x hx
  exact h.some.isDist ⟨j, hj, hjx⟩

/-- **(b) The data structure meets the specification of multiple-source shortest paths in the
dual graph minus a path**, given a cut of the dual graph minus every simple path, for every choice
of lengths that are nonnegative off the path, whenever some face lies along the path. -/
theorem msspCut_spec {M : CombMap D V F} {D' V' F' : Type*} [Fintype D'] [DecidableEq D']
    [Fintype V'] [DecidableEq V'] [Fintype F'] [DecidableEq F']
    (hcut : ∀ (P : SPath M) (ℓ : D → ℤ), (∀ e, e ∉ P.darts → 0 ≤ ℓ e) → ∀ x ∈ P.faces,
      Nonempty (Cut M ℓ P.darts D' V' F')) :
    MSSPSpec M (msspCut M D' V' F') :=
  fun P ℓ hnn x hx => msspCut_isDist (hcut P ℓ hnn x hx) hx

/-! ### A witness of satisfiability -/

/-- **Not an algorithm: a witness only that `MSSPSpec` is satisfiable.** The distances in the dual
graph minus the darts `L`. -/
noncomputable def dualDist (M : CombMap D V F) (L : List D) (ℓ : D → ℤ) (x y : F) : Option ℤ :=
  MSSP.odist ((M.dualGraph ℓ).restrict fun e => e ∉ L) x y

/-- **`MSSPSpec` is satisfiable** (by the distances themselves, `dualDist`). -/
theorem dualDist_spec (M : CombMap D V F) : MSSPSpec M (dualDist M) :=
  fun _ _ hnn x _ => isDist_odist (fun a => hnn a.1 a.2) x

end BKMNW

end PlanarFlow
