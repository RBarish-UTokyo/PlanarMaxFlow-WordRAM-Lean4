module

public import PlanarFlow.NegSSSP.SepCost
public import PlanarFlow.NegSSSP.FaceDec
public import PlanarFlow.BKMNW.Main

/-!
# Maximum flow with shortest paths with negative lengths implemented

The maximum-flow algorithm of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen (SIAM J.
Comput. 46(4), 2017) takes as a subroutine shortest paths with negative
lengths in the dual graph, specified by `PlanarFlow.BKMNW.NegSSSPSpec`. Here that subroutine is
the recursion of Klein–Mozes–Weimann and Mozes–Wulff-Nilsen run on the dual map.

* `negSSSPDecF_dual`: **the subroutine used by the maximum-flow algorithm**
  (`PlanarFlow.BKMNW.negSSSPImpl`, `PlanarFlow.BKMNW.planeOracles`): the recursion
  `PlanarFlow.NegSSSP.negSSSPDecF` on the dual map, through its simple graph, on the
  decomposition `negDecF` by simple cycle separators (`PlanarFlow/NegSSSP/FaceDec.lean`). It
  meets `NegSSSPSpec M` on every map, and on every plane map with transitive rotations and faces
  (the maps the maximum-flow algorithm calls it on: its piece maps) its decomposition has **at
  every node the shared vertices on one face** (`NTree.FDec`, `OneFace`: of a plane map with at
  most `18 m` vertices, faces and darts containing the part, along a face of `k` darts,
  `k² ≤ 1200 m`) and `b` shared vertices with `(b + 1)² ≤ 1200 m`, and **its counted cost is
  `O(n log² n)`**: at most `10920 K n lg² n + (10⁶ + 1) K n` (`negDecFCost_le`), for subroutine
  costs meeting `NegCosts.Bounds K`.
* `negSSSPDec_dual`: the recursion on the decomposition of a separator tree of Lipton, Rose and
  Tarjan (`negSSSPDec`, `PlanarFlow/NegSSSP/Simple.lean`), with the same correctness and an
  `O(n log² n)` bound; its boundaries need not lie on few faces.
* `negSSSP_dual`, `negSSSPSpec_family`: the recursion on the decomposition computed by a separator
  subroutine (`PlanarFlow.NegSSSP.negSSSP`), correct for every separator; its cost bound assumes
  a separator meeting `PlanarFlow.BKMNW.SepSpec`, which cannot be met in general.

**What the cost model assumes** (`NegCosts.Bounds`): in particular multiple-source shortest
paths in a piece of `m` darts from `b` boundary vertices in `K (m lg m + b² lg m)`. With the
decomposition `negDecF` every such call is one call from a face of a plane map of `O(m)` darts,
along a face of `O(√m)` darts (`OneFace`), the setting of Klein's algorithm, whose cost
`O(N log N + k t log N)` for `t = k` targets (`PlanarFlow.Klein.klein_steps_le`) is then
`O(m lg m)` per node, the order of the charge of a node (`oneFace_cost_le`,
`NegCosts.node_le`); its distances give those of the piece (`FaceInst.isDist`). The maximum-flow
algorithm uses the multiple-source shortest paths `msspK` (`PlanarFlow/NegSSSP/FaceKlein.lean`):
Klein's trip on the map of the one-face instance with the sources copied inside the face
(`PlanarFlow.Klein.srcMap`, on which no dart of the piece enters a source,
`PlanarFlow.MSSP.Hyp.noIn`, and all sources reach the same vertices), meeting `PieceMSSPSpec` on
every map (`msspK_spec`); on such an instance the machine program `kleinProg` runs within
`32886 · 2372500000 · m lg m` steps at a node of `m` darts (`splitF_exec`) and ends with the
distances in the part between the shared vertices in its output (the `k²` path-sum queries are
part of the program and of its count). The hypotheses of `NegCosts.Bounds` are still not met by
a proved implementation in that counted model: Bellman–Ford over dense distance graphs is the
reference version `bfRef`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- **Shortest paths with negative lengths in the dual graph of a map**: the recursion on the
dual map meets `NegSSSPSpec M` (a feasible potential of the dual graph, or a closed walk of
negative length), and, with a separator subroutine for the dual map meeting `SepSpec` and the
costs of the subroutines bounded by `NegCosts.Bounds`, its counted cost is at most
`2 (58 + 3 κ²) K n lg² n + K s n` for `n ≥ 1` darts. The hypothesis `SepSpec` cannot be met in
general; `negSSSPDec_dual` gives the bound without it. -/
theorem negSSSP_dual (M : CombMap D V F) {κ η s : ℕ}
    {sep : Finset D → List (Finset F) → Finset D × Finset D × SPath M.dual}
    (hsep : SepSpec M.dual ∅ ∅ κ η s sep)
    {mssp : Finset D → (D → ℤ) → Finset F → F → F → Option ℤ}
    (hmssp : PieceMSSPSpec M.dual mssp) {bf : DDG F → DDG F → Option (F → ℤ)}
    (hbf : BFDDGSpec bf)
    {fr : DDG (Option F) → List (Option F × Option F × ℤ) → Option F → (Option F → ℤ) →
      Option F → Option ℤ} (hfr : FRSpec fr) {c : NegCosts} {K : ℕ} (hc : c.Bounds K)
    (hD : 0 < Fintype.card D) :
    NegSSSPSpec M (negSSSP M.dual sep s mssp bf fr) ∧
      negCost M.dual c (NTree.build sep s univ) ≤
        2 * (58 + 3 * κ ^ 2) * K * Fintype.card D * lg (Fintype.card D) ^ 2 +
          K * s * Fintype.card D :=
  ⟨negSSSPSpec_dual M sep s hmssp hbf hfr, negSSSP_cost_dual M hsep hc hD⟩

universe u in
/-- **Shortest paths with negative lengths for every plane map**, from subroutine families. -/
theorem negSSSPSpec_family
    (sepF : ∀ {D V F : Type u} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
      (N : CombMap D V F), Finset D → List (Finset V) → Finset D × Finset D × SPath N) (s : ℕ)
    (msspF : ∀ {D V F : Type u} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
      (_ : CombMap D V F), Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (hmsspF : ∀ {D V F : Type u} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
      [Fintype F] [DecidableEq F] (N : CombMap D V F), N.IsPlane → PieceMSSPSpec N (msspF N))
    (bfF : ∀ {X : Type u} [Fintype X] [DecidableEq X], DDG X → DDG X → Option (X → ℤ))
    (hbfF : ∀ {X : Type u} [Fintype X] [DecidableEq X], BFDDGSpec (bfF (X := X)))
    (frF : ∀ {X : Type u}, DDG X → List (X × X × ℤ) → X → (X → ℤ) → X → Option ℤ)
    (hfrF : ∀ {X : Type u}, FRSpec (frF (X := X)))
    {D V F : Type u} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
    [DecidableEq F] (M : CombMap D V F) (hM : M.IsPlane) :
    NegSSSPSpec M (negSSSP M.dual (sepF M.dual) s (msspF M.dual) bfF frF) :=
  negSSSPSpec_dual M _ s (hmsspF M.dual hM.dual) hbfF hfrF

/-! ### The subroutine used: the decomposition of a separator tree -/

lemma dual_rot (M : CombMap D V F) : M.dual.rot = M.next := by
  funext d
  show M.rot (M.rev d) = M.next d
  simp only [CombMap.rot, M.rev_rev]

/-- The rotations of the dual map are transitive when the faces of the map are. -/
lemma dual_rotTrans (hface : M.FaceTrans) : M.dual.RotTrans := by
  intro d d' h
  rw [dual_rot]
  exact hface d d' h

/-- The faces of the dual map are transitive when the rotations of the map are. -/
lemma dual_faceTrans (hrot : M.RotTrans) : M.dual.FaceTrans := hrot

/-- **Shortest paths with negative lengths in the dual graph, with the decomposition of a
separator tree**: the recursion `negSSSPDec` on the dual map meets `NegSSSPSpec M` (on every map),
and on a plane map with transitive rotations and faces and `n` darts its counted cost
`negDecCost` is at most `C₁ K n lg² n + (C₂ + 1) K n`, `C₁ = 160 (1 + 9 · 50000²) + 1152 · 50000²`,
`C₂ = 576 · 50000²`, for every family of subroutine costs meeting `NegCosts.Bounds K`. -/
theorem negSSSPDec_dual (M : CombMap D V F) (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) {mssp : Finset D → (D → ℤ) → Finset F → F → F → Option ℤ}
    (hmssp : PieceMSSPSpec M.dual mssp) {bf : DDG F → DDG F → Option (F → ℤ)}
    (hbf : BFDDGSpec bf)
    {fr : DDG (Option F) → List (Option F × Option F × ℤ) → Option F → (Option F → ℤ) →
      Option F → Option ℤ} (hfr : FRSpec fr) {c : NegCosts} {K : ℕ} (hc : c.Bounds K) :
    NegSSSPSpec M (negSSSPDec M.dual mssp bf fr) ∧
      negDecCost M.dual c ≤
        (160 * (1 + 9 * 50000 ^ 2) + 1152 * 50000 ^ 2) * K * Fintype.card D *
            lg (Fintype.card D) ^ 2 +
          (576 * 50000 ^ 2 + 1) * K * Fintype.card D :=
  ⟨negSSSPDec_spec_dual M hmssp hbf hfr,
    negDecCost_le hM.dual (dual_rotTrans hface) (dual_faceTrans hrot) hc⟩

/-- **Shortest paths with negative lengths in the dual graph, with the decomposition by simple
cycles**: the recursion `negSSSPDecF` on the dual map meets `NegSSSPSpec M` (on every map), and on
a plane map with transitive rotations and faces and `n` darts its decomposition has at every node
the shared vertices on one face (`NTree.FDec`: `OneFace` for both parts, `O(√m)` shared vertices,
parts of at most three quarters of the darts) and its counted cost `negDecFCost` is at most
`10920 K n lg² n + (10⁶ + 1) K n`, for every family of subroutine costs meeting
`NegCosts.Bounds K`. -/
theorem negSSSPDecF_dual (M : CombMap D V F) (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) {mssp : Finset D → (D → ℤ) → Finset F → F → F → Option ℤ}
    (hmssp : PieceMSSPSpec M.dual mssp) {bf : DDG F → DDG F → Option (F → ℤ)}
    (hbf : BFDDGSpec bf)
    {fr : DDG (Option F) → List (Option F × Option F × ℤ) → Option F → (Option F → ℤ) →
      Option F → Option ℤ} (hfr : FRSpec fr) {c : NegCosts} {K : ℕ} (hc : c.Bounds K) :
    NegSSSPSpec M (negSSSPDecF M.dual mssp bf fr) ∧ (negDecF M.dual).FDec M.dual ∧
      negDecFCost M.dual c ≤ 10920 * K * Fintype.card D * lg (Fintype.card D) ^ 2 +
        1000001 * K * Fintype.card D :=
  ⟨negSSSPDecF_spec_dual M hmssp hbf hfr,
    negDecF_fDec hM.dual (dual_rotTrans hface) (dual_faceTrans hrot),
    negDecFCost_le hM.dual (dual_rotTrans hface) (dual_faceTrans hrot) hc⟩

end NegSSSP

end PlanarFlow
