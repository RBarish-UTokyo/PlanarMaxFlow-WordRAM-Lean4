module

public import PlanarFlow.BKMNW.FixInv
public import PlanarFlow.BKMNW.DDG
public import PlanarFlow.BKMNW.Specs

/-!
# FixConservationOnPath: the efficient implementation

This file implements the procedure FixConservationOnPath of Borradaile, Klein, Mozes, Nussbaum and
Wulff-Nilsen (SIAM J. Comput. 46(4), 2017, Section 3.2, Algorithm 6) and proves it correct from
the specifications of its three subroutines:

* **multiple-source shortest paths** (`MSSPSpec`, Klein; Cabello–Chambers–Erickson): in the dual
  graph with the darts of a simple path `P` removed (`H*` in the article), with nonnegative
  lengths, the distances from every face along `P`. The procedure calls it once, with the
  lengths `c - f₀` (the residual capacities of the initial flow), to build the dense distance
  graph `D*` of `H*` on the faces `X*` along `P`.
* **FR-Dijkstra** (`FRSpec`): the distances from a face of `X*` in the union of `D*` with the
  explicit darts of `P` and their reverses, given a price function.
* **shortest paths with negative lengths** (`NegSSSPSpec`, Mozes–Wulff-Nilsen): once, at the end,
  to turn the implicit representation into an explicit flow (lines 30–33 of Algorithm 6).

## The representation

As in the article, the flow is kept as `f + cob Φ` where `f` (the *explicit* flow) differs from
the initial flow `f₀` only on the darts of `P`, and the circulation `cob Φ` is known through the
values `φX` of `Φ` on the faces `X*` along `P` only. On the darts off `P`, `f = f₀`, so the
residual capacities there are the reduced lengths `c - f₀ - cob Φ`, and the distances in `H*` with
respect to them are those of `D*` corrected by the price function `φX` (equation (6) of the
article). This is why `D*` never has to be recomputed: the residual graph changes during the
procedure, but only by a circulation `cob Φ` (which changes the lengths of `H*` by a potential)
and on the darts of `P` (which are explicit arcs).

## One stage (`fpStep`, lines 9–29 of Algorithm 6)

1. clip the flow on `d i`, computed from `f` and `φX`;
2. choose the direction from the sign of the net outflow of `p i`;
3. push on the dart itself as much as possible;
4. if some excess is left, Hassin's step: FR-Dijkstra from the face of the reversed dart, with the
   explicit lengths `c' - f` on the darts of `P` (the limit, corrected by `φX`, on the reversed
   dart); the reduced distances `φi` give the amount pushed (`φi` at the face of the dart), and
   `φX` is increased by `φi`.

## The main results

* `fpStep_inv`: a stage preserves the invariant relating the implicit representation to a flow
  meeting the invariant of Lemma B.1 (`SPath.FPInv`, `PlanarFlow/BKMNW/FixInv.lean`). The key
  identity (`dist_correct`): the FR-Dijkstra distances, reduced by `φX`, are the distances in the
  dual graph of Hassin's step (`PlanarFlow.BKMNW.hassin_step`), by the decomposition of walks
  (`PlanarFlow.BKMNW.isDist_union`) and the shift of distances by a potential
  (`PlanarFlow.BKMNW.isDist_addPot`).
* `fixPath_spec`: **FixConservationOnPath meets its specification** (`FixOut`): the output is a
  pseudoflow, its net outflow differs from that of `f₀` only on the vertices of the path, and no
  residual path leads from a vertex of the path with positive inflow to a vertex of the path with
  negative inflow.

## Deviations from the article, all harmless

* The constant by which the capacities of the path are raised is `4 N + 1` (`N` the sum of the
  absolute values of the capacities) instead of the sum of the capacities; it is proved large
  enough (`PlanarFlow.BKMNW.SPath.abs_le_boost`).
* When the push on the dart itself already exhausts the excess, Hassin's step (with limit `0`)
  is skipped; it would push nothing.
* The inflow at `p i` is recomputed as the net outflow of the explicit flow at `p i` (the
  circulation does not change it) instead of being kept in an array.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap SPath

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- **The specification of multiple-source shortest paths** as used by the article: in the dual
graph with the darts of a simple path removed, with lengths nonnegative off the path, the
distances from every face along the path. (Klein's algorithm applies because these faces lie on
one face of the dual graph with the path removed, Figure 1 of the article.) -/
def MSSPSpec (M : CombMap D V F) (mssp : List D → (D → ℤ) → F → F → Option ℤ) : Prop :=
  ∀ (P : SPath M) (ℓ : D → ℤ), (∀ e, e ∉ P.darts → 0 ≤ ℓ e) → ∀ x ∈ P.faces,
    IsDist ((M.dualGraph ℓ).restrict fun e => e ∉ P.darts) x (mssp P.darts ℓ x)

/-- `MSSPSpec` for one simple path `P` (what FixConservationOnPath along `P` uses). -/
def MSSPSpecAt (M : CombMap D V F) (mssp : List D → (D → ℤ) → F → F → Option ℤ) (P : SPath M) :
    Prop :=
  ∀ (ℓ : D → ℤ), (∀ e, e ∉ P.darts → 0 ≤ ℓ e) → ∀ x ∈ P.faces,
    IsDist ((M.dualGraph ℓ).restrict fun e => e ∉ P.darts) x (mssp P.darts ℓ x)

/-- The type of FR-Dijkstra on the dual: a dense distance graph, explicit arcs, a root, a price
function, and the distances. -/
abbrev FRFun (F : Type*) := DDG F → List (F × F × ℤ) → F → (F → ℤ) → F → Option ℤ

variable (M) in
/-- **One stage of FixConservationOnPath** (lines 9–29 of Algorithm 6), on the explicit flow `f`
and the potential `φX` on the faces along the path. -/
noncomputable def fpStep (c : D → ℤ) (P : SPath M) (Dst : DDG F) (fr : FRFun F) (i : ℕ)
    (s : (D → ℤ) × (F → ℤ)) : (D → ℤ) × (F → ℤ) :=
  let f := s.1
  let φX := s.2
  let u := P.cap c (4 * absSum c + 1) (i + 1)
  let e₀ := P.d i
  -- clip the flow on `d i` (lines 10–17)
  let gnew := max (min (f e₀ + M.cob φX e₀) (c e₀)) (-c (M.rev e₀))
  let f₁ := setPair M f e₀ (gnew - M.cob φX e₀)
  -- the direction and the limit (line 18)
  let b := M.div f₁ (P.p i)
  let e := if b < 0 then e₀ else M.rev e₀
  let x := |b|
  -- push on the dart itself (lines 19–22)
  let val₀ := min (u e - f₁ e - M.cob φX e) x
  let f₂ := setPair M f₁ e (f₁ e + val₀)
  if x - val₀ ≤ 0 then (f₂, φX) else
  -- Hassin's step with FR-Dijkstra (lines 23–29)
  let L : D → ℤ := fun e' =>
    if e' = M.rev e then (x - val₀) + M.cob φX (M.rev e) else u e' - f₂ e'
  let r := M.face (M.rev e)
  let δ := fr Dst (explicitArcs (M.dualGraph L) P.darts) r φX
  let φi : F → ℤ := fun y => (δ y).getD 0 - φX y + φX r
  (setPair M f₂ e (f₂ e + φi (M.face e)), fun y => if y ∈ P.faces then φX y + φi y else φX y)

variable (M) in
/-- **FixConservationOnPath** (Algorithm 6): the dense distance graph `D*` by MSSP, the stages
`0, …, k - 1`, and the explicit flow by negative-length shortest paths. -/
noncomputable def fixPath (c f₀ : D → ℤ) (P : SPath M)
    (mssp : List D → (D → ℤ) → F → F → Option ℤ) (fr : FRFun F)
    (negSSSP : (D → ℤ) → Option (F → ℤ)) : D → ℤ :=
  let Dst : DDG F := ⟨P.faces, mssp P.darts (c - f₀)⟩
  let s := (List.range P.k).foldl (fun s i => fpStep M c P Dst fr i s) (f₀, 0)
  match negSSSP (c - s.1) with
  | some χ => s.1 + M.cob χ
  | none => s.1

variable (M) in
/-- **The specification of FixConservationOnPath** (the interface of Section 2 of the article):
`f` is a pseudoflow, `f - f₀` is conserved off the path, and no residual path leads from a vertex
of the path with positive inflow to a vertex of the path with negative inflow. -/
structure FixOut (c f₀ : D → ℤ) (Pv : Finset V) (f : D → ℤ) : Prop where
  pseudo : IsPseudo M c f
  eq : ∀ v, v ∉ Pv → M.div f v = M.div f₀ v
  noPath : NoPath M c f (Pv.filter fun v => M.div f v < 0) (Pv.filter fun v => 0 < M.div f v)

/-! ### Auxiliary facts -/

lemma setPair_add (f h : D → ℤ) (e : D) (a : ℤ) (hh : M.IsAntisymm h) :
    setPair M f e a + h = setPair M (f + h) e (a + h e) := by
  funext e'
  simp only [setPair, Pi.add_apply]
  split_ifs with h1 h2
  · subst h1; rfl
  · subst h2; rw [hh e]; ring
  · rfl

lemma cob_eq_of_faces {P : SPath M} {φ Φ : F → ℤ} (h : ∀ y ∈ P.faces, φ y = Φ y) {e : D}
    (he : e ∈ P.darts) : M.cob φ e = M.cob Φ e := by
  simp only [cob, h _ (P.face_mem he), h _ (P.face_mem (P.rev_mem_darts he))]

lemma setPair_off {f : D → ℤ} {P : SPath M} {e e' : D} {a : ℤ} (he : e ∈ P.darts)
    (he' : e' ∉ P.darts) : setPair M f e a e' = f e' :=
  setPair_of_ne f a (fun h => he' (h ▸ he)) (fun h => he' (h ▸ P.rev_mem_darts he))

/-- A feasible potential only matters on the ends of the arcs. -/
lemma isPot_congr {X A : Type*} {G : Digraph X A} {p q : X → ℤ} (hp : G.IsPot p)
    (h : ∀ a, p (G.src a) = q (G.src a) ∧ p (G.dst a) = q (G.dst a)) : G.IsPot q := by
  intro a; have := hp a; rw [(h a).1, (h a).2] at this; exact this

/-- The arcs of the union have their ends among the faces along the path. -/
lemma union_ends {P : SPath M} {Dst : DDG F} (hb : Dst.bdry = P.faces) (L : D → ℤ)
    (a : Dst.Arc ⊕ Fin (explicitArcs (M.dualGraph L) P.darts).length) :
    (Dst.union (explicitArcs (M.dualGraph L) P.darts)).src a ∈ P.faces ∧
      (Dst.union (explicitArcs (M.dualGraph L) P.darts)).dst a ∈ P.faces := by
  match a with
  | .inl q => exact ⟨hb ▸ q.2.1, hb ▸ q.2.2.1⟩
  | .inr i =>
    have hi : i.1 < P.darts.length := by simpa [length_explicitArcs] using i.2
    simp only [DDG.union_src_inr, DDG.union_dst_inr, explicitArcs_getElem]
    exact ⟨P.face_mem (List.getElem_mem hi),
      P.face_mem (P.rev_mem_darts (List.getElem_mem hi))⟩

/-- **The distances computed with FR-Dijkstra are those of Hassin's step.** Let `g = f + cob Φ`
be a pseudoflow saturating `e ∈ P`, with `f = f₀` off the path and `φX = Φ` on the faces along
the path. FR-Dijkstra on `D*` and the explicit darts with the lengths `L` of `fpStep`, reduced by
`φX`, gives on the faces along the path the distances of Hassin's step with limit `x`. -/
theorem dist_correct (hM : M.IsPlane) {c f₀ : D → ℤ} {P : SPath M}
    {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    (hf₀ : IsPseudo M c f₀) {fr : FRFun F} (hfr : FRSpec fr) {u f : D → ℤ} {Φ φX : F → ℤ}
    (hu : ∀ e, e ∉ P.darts → u e = c e) (hoff : ∀ e, e ∉ P.darts → f e = f₀ e)
    (hφ : ∀ y ∈ P.faces, φX y = Φ y) (hg : IsPseudo M u (f + M.cob Φ)) {e : D}
    (he : e ∈ P.darts) {x : ℤ} (hx : 0 ≤ x) {φt : F → ℤ}
    (ht : IsDist (M.dualGraph (hassinLen M u (f + M.cob Φ) e x)) (M.face (M.rev e))
      fun y => some (φt y)) :
    ∀ y ∈ P.faces,
      ((fr ⟨P.faces, mssp P.darts (c - f₀)⟩
        (explicitArcs (M.dualGraph fun e' =>
          if e' = M.rev e then x + M.cob φX (M.rev e) else u e' - f e') P.darts)
        (M.face (M.rev e)) φX) y).getD 0 - φX y + φX (M.face (M.rev e)) = φt y := by
  generalize hL : (fun e' => if e' = M.rev e then x + M.cob φX (M.rev e) else u e' - f e') = L
  have hre : M.rev e ∈ P.darts := P.rev_mem_darts he
  have hr : M.face (M.rev e) ∈ P.faces := P.face_mem hre
  -- the lengths `L` are Hassin's lengths changed by the potential `Φ`
  have hLeq : M.dualGraph L = (M.dualGraph (hassinLen M u (f + M.cob Φ) e x)).addPot Φ := by
    rw [← hL]
    simp only [CombMap.dualGraph, Digraph.addPot, Digraph.mk.injEq, true_and]
    funext e'
    simp only [hassinLen, Pi.add_apply]
    split_ifs with h1
    · subst h1; rw [cob_eq_of_faces hφ hre]; simp [cob]
    · simp [cob]; ring
  -- the distances in the dual graph with the lengths `L`
  have hdist := isDist_addPot (p := Φ) ht
  rw [← hLeq] at hdist
  -- the decomposition hypotheses
  have hyp : DecompHyp (M.dualGraph L) (fun e' => e' ∉ P.darts) P.darts P.faces
      ⟨P.faces, mssp P.darts (c - f₀)⟩ := by
    refine ⟨fun a => by simp, fun a ha => P.face_mem ha,
      fun a ha => P.face_mem (P.rev_mem_darts ha),
      rfl, fun b hb => ?_⟩
    refine ⟨mssp P.darts (c - f₀) b, ?_, fun _ _ => rfl⟩
    have hres : (M.dualGraph L).restrict (fun e' => e' ∉ P.darts) =
        (M.dualGraph (c - f₀)).restrict (fun e' => e' ∉ P.darts) := by
      simp only [Digraph.restrict, CombMap.dualGraph, Digraph.mk.injEq, true_and]
      funext a
      rw [← hL]
      have h1 : a.1 ≠ M.rev e := fun h => a.2 (h ▸ hre)
      simp only [h1, ite_false, Pi.sub_apply, hu a.1 a.2, hoff a.1 a.2]
    rw [hres]
    exact hmssp (c - f₀) (fun e' _ => by simp only [Pi.sub_apply]; linarith [hf₀.le_cap e']) b hb
  -- the price function is feasible
  have hpotΦ : (M.dualGraph L).IsPot Φ := by
    intro e'
    rw [hLeq]
    simp only [Digraph.addPot, CombMap.dualGraph]
    have : 0 ≤ hassinLen M u (f + M.cob Φ) e x e' := by
      unfold hassinLen; split_ifs
      · exact hx
      · linarith [hg.le_cap e']
    linarith
  have hpot : (DDG.union ⟨P.faces, mssp P.darts (c - f₀)⟩
      (explicitArcs (M.dualGraph L) P.darts)).IsPot
      φX := isPot_congr (isPot_union hyp hpotΦ) fun a => by
    obtain ⟨h1, h2⟩ := union_ends rfl L a
    exact ⟨(hφ _ h1).symm, (hφ _ h2).symm⟩
  have hU := hfr _ _ (M.face (M.rev e)) φX hpot
  intro y hy
  rw [isDist_union hyp hr hdist hU hy]
  simp only [Option.map_some, Option.getD_some, hφ y hy, hφ _ hr]
  ring

/-! ### One stage -/

/-- The invariant of the implementation after the stages `0, …, i - 1`: the explicit flow agrees
with `f₀` off the path, and with a potential `Φ` agreeing with `φX` on the faces along the path,
the flow `f + cob Φ` meets the invariant of Lemma B.1. -/
def EffInv (c f₀ : D → ℤ) (P : SPath M) (i : ℕ) (s : (D → ℤ) × (F → ℤ)) : Prop :=
  ∃ Φ : F → ℤ, (∀ y ∈ P.faces, s.2 y = Φ y) ∧ (∀ e, e ∉ P.darts → s.1 e = f₀ e) ∧
    M.IsAntisymm s.1 ∧ P.FPInv c f₀ (4 * absSum c + 1) i (s.1 + M.cob Φ)

/-- **One stage of the implementation preserves the invariant.** -/
theorem fpStep_inv (hM : M.IsPlane) {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀)
    {P : SPath M} {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    {fr : FRFun F} (hfr : FRSpec fr) {i : ℕ} (hi : i < P.k) {s : (D → ℤ) × (F → ℤ)}
    (hs : EffInv c f₀ P i s) :
    EffInv c f₀ P (i + 1) (fpStep M c P ⟨P.faces, mssp P.darts (c - f₀)⟩ fr i s) := by
  classical
  obtain ⟨f, φX⟩ := s
  obtain ⟨Φ, hφ, hoff, hanti, hinv⟩ := hs
  simp only at hφ hoff hanti hinv
  have hd₀ : P.d i ∈ P.darts := P.d_mem i hi
  have hcob₀ : M.cob φX (P.d i) = M.cob Φ (P.d i) := cob_eq_of_faces hφ hd₀
  generalize hu : P.cap c (4 * absSum c + 1) (i + 1) = u
  have hu_off : ∀ e, e ∉ P.darts → u e = c e := fun e he => by
    rw [← hu, P.cap_of_not_mem c _ _ he]
  -- the true flows
  generalize hg : f + M.cob Φ = g at hinv
  have hgps := hinv.pseudo
  -- clipping
  generalize hf₁ : setPair M f (P.d i) (max (min (f (P.d i) + M.cob φX (P.d i)) (c (P.d i)))
    (-c (M.rev (P.d i))) - M.cob φX (P.d i)) = f₁
  have hg₁ : f₁ + M.cob Φ = SPath.clip M c g (P.d i) := by
    rw [← hf₁, setPair_add _ _ _ _ (M.cob_antisymm Φ), SPath.clip, SPath.clipVal, ← hg, hcob₀]
    simp only [Pi.add_apply, sub_add_cancel]
  have hdivcob : ∀ h : D → ℤ, ∀ v, M.div (h + M.cob Φ) v = M.div h v := fun h v => by
    rw [div_add', show M.div (M.cob Φ) v = 0 from M.div_cob Φ v, add_zero]
  have hb : M.div f₁ (P.p i) = M.div (SPath.clip M c g (P.d i)) (P.p i) := by
    rw [← hg₁, hdivcob]
  -- the direction
  generalize hbv : M.div (SPath.clip M c g (P.d i)) (P.p i) = b at hb
  generalize he : (if b < 0 then P.d i else M.rev (P.d i)) = e
  have hemem : e ∈ P.darts := by
    rw [← he]; split_ifs
    · exact hd₀
    · exact P.rev_mem_darts hd₀
  have htail : M.tail e = if b < 0 then P.p i else P.p (i + 1) := by
    rw [← he]; split_ifs
    · exact P.tail_d i hi
    · rw [M.tail_rev]; exact P.head_d i hi
  have hhead : M.head e = if b < 0 then P.p (i + 1) else P.p i := by
    rw [← he]; split_ifs
    · exact P.head_d i hi
    · rw [M.head_rev]; exact P.tail_d i hi
  have hcobe : M.cob φX e = M.cob Φ e := cob_eq_of_faces hφ hemem
  generalize hx : |b| = x
  have hx0 : 0 ≤ x := hx ▸ abs_nonneg b
  -- the clipped flow is a pseudoflow for the new capacities (from `FPInv.step`'s proof, redone)
  generalize hg₁' : SPath.clip M c g (P.d i) = g₁ at hg₁ hbv
  have hanti₁ : M.IsAntisymm f₁ := hf₁ ▸ setPair_antisymm hanti _ _
  have hg₁ps : IsPseudo M u g₁ := by
    rw [← hg₁', ← hu, SPath.clip]
    refine ⟨setPair_antisymm hgps.antisymm _ _, fun e' => ?_⟩
    have hii : ¬ (i + 1 ≤ i) := by omega
    by_cases h1 : e' = P.d i
    · subst h1
      rw [setPair_self]; simp only [P.cap_d c _ hi, hii, ↓reduceIte, SPath.clipVal]
      have := hc (P.d i); have := hc (M.rev (P.d i)); omega
    · by_cases h2 : e' = M.rev (P.d i)
      · subst h2
        rw [setPair_rev]; simp only [P.cap_rev_d c _ hi, hii, ↓reduceIte, SPath.clipVal]
        have := hc (P.d i); have := hc (M.rev (P.d i)); omega
      · rw [setPair_of_ne _ _ h1 h2, P.cap_succ c _ hi h1 h2]; exact hgps.le_cap e'
  -- the push on the dart itself
  generalize hval₀ : min (u e - f₁ e - M.cob φX e) x = val₀
  have hres₀ : u e - f₁ e - M.cob φX e = u e - g₁ e := by
    rw [hcobe, ← hg₁]; simp only [Pi.add_apply]; ring
  generalize hf₂ : setPair M f₁ e (f₁ e + val₀) = f₂
  generalize hg₂ : setPair M g₁ e (g₁ e + val₀) = g₂
  have hfg₂ : f₂ + M.cob Φ = g₂ := by
    rw [← hf₂, ← hg₂, setPair_add _ _ _ _ (M.cob_antisymm Φ), ← hg₁]
    simp only [Pi.add_apply]; ring_nf
  have hval₀0 : 0 ≤ val₀ := by
    rw [← hval₀, hres₀]; have := hg₁ps.le_cap e; omega
  have hval₀x : val₀ ≤ x := hval₀ ▸ min_le_right _ _
  have hg₂ps : IsPseudo M u g₂ := by
    rw [← hg₂]
    refine ⟨setPair_antisymm hg₁ps.antisymm _ _, fun e' => ?_⟩
    by_cases h1 : e' = e
    · subst h1; rw [setPair_self]; have := min_le_left (u e' - f₁ e' - M.cob φX e') x
      rw [hval₀, hres₀] at this; omega
    · by_cases h2 : e' = M.rev e
      · subst h2; rw [setPair_rev]
        have := hg₁ps.le_cap (M.rev e); rw [hg₁ps.antisymm e] at this
        omega
      · rw [setPair_of_ne _ _ h1 h2]; exact hg₁ps.le_cap e'
  have hdiv₂ : ∀ v, M.div g₂ v = M.div g₁ v +
      val₀ * ((if M.tail e = v then 1 else 0) - (if M.head e = v then 1 else 0)) := fun v => by
    rw [← hg₂, div_setPair hg₁ps.antisymm]; ring_nf
  have hanti₂ : M.IsAntisymm f₂ := hf₂ ▸ setPair_antisymm hanti₁ _ _
  have hoff₁ : ∀ e', e' ∉ P.darts → f₁ e' = f₀ e' := fun e' h' => by
    rw [← hf₁, setPair_off hd₀ h']; exact hoff e' h'
  have hoff₂ : ∀ e', e' ∉ P.darts → f₂ e' = f₀ e' := fun e' h' => by
    rw [← hf₂, setPair_off hemem h']; exact hoff₁ e' h'
  -- the stage, unfolded
  generalize hδ : fr ⟨P.faces, mssp P.darts (c - f₀)⟩ (explicitArcs (M.dualGraph fun e' =>
    if e' = M.rev e then (x - val₀) + M.cob φX (M.rev e) else u e' - f₂ e') P.darts)
    (M.face (M.rev e)) φX = δ
  have hstep : fpStep M c P ⟨P.faces, mssp P.darts (c - f₀)⟩ fr i (f, φX) =
      if x - val₀ ≤ 0 then (f₂, φX) else
        (setPair M f₂ e (f₂ e + ((δ (M.face e)).getD 0 - φX (M.face e) + φX (M.face (M.rev e)))),
         fun y => if y ∈ P.faces then φX y + ((δ y).getD 0 - φX y + φX (M.face (M.rev e)))
          else φX y) := by
    simp only [fpStep, hu, hf₁, hb, hbv, he, hx, hval₀, hf₂, hδ]
  rw [hstep]
  -- the step of the invariant
  have hgoal : ∀ (f' : D → ℤ) (Φ' : F → ℤ) (φX' : F → ℤ), (∀ y ∈ P.faces, φX' y = Φ' y) →
      (∀ e', e' ∉ P.darts → f' e' = f₀ e') → M.IsAntisymm f' →
      LimPush M u g₁ (f' + M.cob Φ') (if b < 0 then P.p i else P.p (i + 1))
        (if b < 0 then P.p (i + 1) else P.p i) x →
      EffInv c f₀ P (i + 1) (f', φX') := by
    intro f' Φ' φX' h1 h2 h3 h4
    refine ⟨Φ', h1, h2, h3, ?_⟩
    have := SPath.FPInv.step P (g' := f' + M.cob Φ') hc hf₀ hi hinv
    simp only [hg₁', hbv, hx, hu] at this
    exact this h4
  split_ifs with hle
  · -- the limit is reached on the dart itself
    refine hgoal f₂ Φ φX hφ hoff₂ hanti₂ ⟨hfg₂ ▸ hg₂ps, val₀, hval₀0, hval₀x, ?_, Or.inl (by omega)⟩
    rw [hfg₂, ← htail, ← hhead]; exact hdiv₂
  · -- Hassin's step
    have hsat : g₂ e = u e := by
      have : val₀ = u e - g₁ e := by
        rw [← hval₀, hres₀]; rw [hres₀] at hval₀
        exact min_eq_left (by omega)
      rw [← hg₂, setPair_self]; omega
    have hx' : 0 ≤ x - val₀ := by omega
    obtain ⟨φt, ht⟩ := exists_hassin_dist hM hg₂ps e hx'
    obtain ⟨hps₃, hdiv₃, hv0, hvx, hmax⟩ := hassin_step hM hg₂ps hsat hx' ht
    have hroot : φt (M.face (M.rev e)) = 0 := by
      have := ht.self (p := fun _ => 0) (fun a => by
        show (0 : ℤ) ≤ 0 + hassinLen M u g₂ e (x - val₀) a
        unfold hassinLen; split_ifs
        · omega
        · linarith [hg₂ps.le_cap a])
      simpa using this
    have hdc := dist_correct hM hmssp hf₀ hfr (u := u) (f := f₂) (Φ := Φ) (φX := φX) hu_off hoff₂ hφ
      (hfg₂ ▸ hg₂ps) hemem hx' (by rw [hfg₂]; exact ht)
    rw [hδ] at hdc
    have hfe := hdc (M.face e) (P.face_mem hemem)
    rw [hfe]
    -- the new representation
    have hf₃ : setPair M f₂ e (f₂ e + φt (M.face e)) + M.cob (Φ + φt) = hassinFlow M g₂ e φt := by
      funext e'
      have hcobadd : M.cob (Φ + φt) e' = M.cob Φ e' + M.cob φt e' := by
        simp only [cob, Pi.add_apply]; ring
      simp only [Pi.add_apply, hcobadd, hassinFlow]
      by_cases h1 : e' = e
      · subst h1
        simp only [setPair_self, true_or, ↓reduceIte, ← hfg₂, Pi.add_apply, cob, hroot]; ring
      · by_cases h2 : e' = M.rev e
        · subst h2
          simp only [setPair_rev, or_true, ↓reduceIte, ← hfg₂, Pi.add_apply, cob, M.rev_rev,
            hroot, hanti₂ e]; ring
        · simp only [setPair_of_ne _ _ h1 h2, h1, h2, or_self, ↓reduceIte, ← hfg₂, Pi.add_apply]
          ring
    refine hgoal _ (Φ + φt) _ (fun y hy => ?_) (fun e' h' => ?_) (setPair_antisymm hanti₂ _ _) ?_
    · simp only [hy, ↓reduceIte, Pi.add_apply]; rw [hdc y hy, hφ y hy]
    · rw [setPair_off hemem h']; exact hoff₂ e' h'
    · rw [hf₃]
      refine ⟨hps₃, val₀ + φt (M.face e), by omega, by omega, fun v => ?_, ?_⟩
      · rw [hdiv₃ v, hdiv₂ v, htail, hhead]; ring
      · rcases hmax with h | ⟨Y, h1, h2, h3⟩
        · left; omega
        · right; exact ⟨Y, htail ▸ h1, hhead ▸ h2, h3⟩

/-! ### The procedure -/

/-- **FixConservationOnPath meets its specification**, given the specifications of MSSP,
FR-Dijkstra and shortest paths with negative lengths, on a plane map with nonnegative
capacities. -/
theorem fixPath_spec (hM : M.IsPlane) {c f₀ : D → ℤ} (hc : ∀ e, 0 ≤ c e) (hf₀ : IsPseudo M c f₀)
    (P : SPath M) {mssp : List D → (D → ℤ) → F → F → Option ℤ} (hmssp : MSSPSpecAt M mssp P)
    {fr : FRFun F} (hfr : FRSpec fr) {negSSSP : (D → ℤ) → Option (F → ℤ)}
    (hneg : NegSSSPSpec M negSSSP) :
    FixOut M c f₀ P.verts (fixPath M c f₀ P mssp fr negSSSP) := by
  classical
  -- the stages
  have hall : ∀ n ≤ P.k, EffInv c f₀ P n ((List.range n).foldl
      (fun s i => fpStep M c P ⟨P.faces, mssp P.darts (c - f₀)⟩ fr i s) (f₀, 0)) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨0, fun y _ => rfl, fun e _ => rfl, hf₀.antisymm, ?_⟩
      have : f₀ + M.cob (0 : F → ℤ) = f₀ := by funext e; simp [cob]
      show P.FPInv c f₀ _ 0 (f₀ + M.cob 0)
      rw [this]
      exact P.fpInv_zero hf₀ (by have := absSum_nonneg c; omega)
    | succ n ih =>
      intro hn
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact fpStep_inv hM hc hf₀ hmssp hfr (by omega) (ih (by omega))
  obtain ⟨Φ, -, -, hanti, hinv⟩ := hall P.k le_rfl
  generalize hs : (List.range P.k).foldl
    (fun s i => fpStep M c P ⟨P.faces, mssp P.darts (c - f₀)⟩ fr i s) (f₀, 0) = s at hanti hinv
  obtain ⟨hps, heq, hnp⟩ := SPath.FPInv.final P hinv
  have hdivcob : ∀ h : D → ℤ, ∀ (ψ : F → ℤ) v, M.div (h + M.cob ψ) v = M.div h v := fun h ψ v => by
    rw [div_add', show M.div (M.cob ψ) v = 0 from M.div_cob ψ v, add_zero]
  -- the explicit flow
  have hout : ∃ χ, fixPath M c f₀ P mssp fr negSSSP = s.1 + M.cob χ ∧
      M.IsPotential (c - s.1) χ := by
    have hspec := hneg (c - s.1)
    simp only [fixPath, hs]
    cases h : negSSSP (c - s.1) with
    | none =>
      rw [h] at hspec
      obtain ⟨m, w, hw, hlt⟩ := hspec
      have hpot : (M.dualGraph (c - s.1)).IsPot Φ := by
        rw [← isPotential_iff_isPot]
        intro e
        have := hps.le_cap e
        simp only [Pi.add_apply, Pi.sub_apply] at this ⊢; linarith
      exact absurd (Digraph.walkLen_nonneg _ hpot hw) (by omega)
    | some χ =>
      rw [h] at hspec
      exact ⟨χ, rfl, (isPotential_iff_isPot _ _).2 hspec⟩
  obtain ⟨χ, hχ, hχpot⟩ := hout
  rw [hχ]
  have hps' : IsPseudo M c (s.1 + M.cob χ) := ⟨fun e => by
    simp only [Pi.add_apply, hanti e, M.cob_antisymm χ e]; ring, fun e => by
    have := hχpot e; simp only [Pi.sub_apply] at this; simp only [Pi.add_apply]; linarith⟩
  have hdiv : ∀ v, M.div (s.1 + M.cob χ) v = M.div (s.1 + M.cob Φ) v := fun v => by
    rw [hdivcob, hdivcob]
  refine ⟨hps', fun v hv => by rw [hdiv]; exact heq v hv, ?_⟩
  simp only [hdiv]
  obtain ⟨Y, h1, h2, h3⟩ := hnp
  exact ⟨Y, h1, h2, h3.of_sum_le hps hps' (by simp only [hdiv]; rfl)⟩

end BKMNW

end PlanarFlow
