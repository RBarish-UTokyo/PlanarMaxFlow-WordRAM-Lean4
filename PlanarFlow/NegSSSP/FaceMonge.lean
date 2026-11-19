module

public import PlanarFlow.NegSSSP.FaceKlein
public import PlanarFlow.NegSSSP.Step
public import PlanarFlow.BKMNW.FaceCross

/-!
# The dense distance graphs of the recursion satisfy the crossing inequality

At a node of the recursion (`PlanarFlow.NegSSSP.step`) the dense distance graph of each part `P`
on the shared vertices `B` is `childDDG N mssp P ℓ δ B`: the distances in the part with the
lengths reduced by its potential `δ`, shifted back by `δ`. When the sources `B` lie on one face of
a plane map containing the part (`FaceInst`, `OneFace`, which the decomposition by simple cycles
provides at every node, `PlanarFlow.NegSSSP.SplitF`), the vertices of `B` are ordered along the
face and the lengths of the dense distance graph between them, in this order, satisfy the crossing
inequality `Monge.Crossing`, the hypothesis of Bellman–Ford over a dense distance graph on the
machine (`PlanarFlow.Monge.bfDDG_exec`) and of FR-Dijkstra (`PlanarFlow.BKMNW.frProg_isDist`).

* `FaceInst.exists_corners`: the sources, ordered along the face: `β 0, …, β (b - 1)`, distinct,
  covering `B`, at increasing positions `t 0 < ⋯ < t (b - 1)` of the face cycle.
* `FaceInst.crossingO_childDDG`: **with missing arcs, unconditionally**: in this order the lengths
  satisfy `Monge.CrossingO` (`none` read as an infinite length).
* `FaceInst.crossing_childDDG`: **for any such order and any implementation `mssp` meeting
  `PieceMSSPSpec`, the lengths `(childDDG N mssp P ℓ δ B).len (β i) (β i')` satisfy the crossing
  inequality, when they are all finite** (by `PlanarFlow.BKMNW.crossing_faceCycle` on the face of
  the instance, through `FaceInst.isDist`, and `Monge.Crossing.add_pot` for the shift by `δ`).
* `OneFace.crossing_childDDG`, `crossing_step_parts`: both from `OneFace`, and for the two
  parts of a node.

## What is not claimed

* **Missing arcs.** A part need not be strongly connected between its sources, and an infinite
  length cannot be replaced by a finite one without breaking the crossing inequality in general.
  `Monge.Crossing` (the form `Monge.Crossing b D` of the machine theorems, whose dense distance
  graph is complete) is stated when all the lengths between the sources are finite; without this
  assumption what holds is `Monge.CrossingO`, the crossing inequality with `none` read as an
  infinite length.
* **The union of the two parts.** Each part is Monge in the order of the face of its own
  instance; the two dense distance graphs live on the same vertices `B` but the union
  `DDG.join` of the recursion is not claimed to be one Monge matrix (the minimum of two Monge
  matrices is not Monge in general). Bellman–Ford over the union has to relax the two parts as
  two separate dense distance graphs, each with its own order (`crossing_step_parts`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW CombMap

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F} {P : Finset D} {B : Finset V} {q k : ℕ}
  {DQ VQ FQ : Type u} [Fintype DQ] [DecidableEq DQ] [Fintype VQ] [DecidableEq VQ]
  [Fintype FQ] [DecidableEq FQ] {Q : CombMap DQ VQ FQ} {g : ℕ → DQ} {P' : Finset D}
  {e : D → DQ} {j : V → VQ}

namespace FaceInst

/-- **The sources in the order of the face**: distinct vertices `β 0, …, β (b - 1)` covering `B`,
at increasing positions of the face cycle. -/
theorem exists_corners (h : FaceInst N P B q k Q g P' e j) (hB : B.Nonempty) :
    ∃ (b : ℕ) (t : ℕ → ℕ) (β : ℕ → V), (∀ i i', i < i' → i' < b → t i < t i') ∧
      (∀ i < b, t i < k) ∧ (∀ i < b, β i ∈ B) ∧ (∀ i < b, j (β i) = Q.tail (g (t i))) ∧
      (∀ v ∈ B, ∃ i < b, β i = v) := by
  classical
  obtain ⟨v₀, hv₀⟩ := hB
  let S : Finset ℕ := (range k).filter fun i => ∃ v ∈ B, j v = Q.tail (g i)
  let t : ℕ → ℕ := fun i => if hi : i < S.card then S.orderEmbOfFin rfl ⟨i, hi⟩ else 0
  have hmem : ∀ i (hi : i < S.card), t i ∈ S := fun i hi => by
    simp only [t, hi, ↓reduceDIte]; exact S.orderEmbOfFin_mem rfl _
  let β : ℕ → V := fun i => if hi : ∃ v ∈ B, j v = Q.tail (g (t i)) then hi.choose else v₀
  have hβ : ∀ i < S.card, β i ∈ B ∧ j (β i) = Q.tail (g (t i)) := fun i hi => by
    have hx := (mem_filter.1 (hmem i hi)).2
    simp only [β, hx, ↓reduceDIte]
    exact hx.choose_spec
  refine ⟨S.card, t, β, fun i i' hii' hi' => ?_, fun i hi => mem_range.1 (mem_filter.1
    (hmem i hi)).1, fun i hi => (hβ i hi).1, fun i hi => (hβ i hi).2, fun v hv => ?_⟩
  · simp only [t, hi', show i < S.card by omega, ↓reduceDIte]
    exact (S.orderEmbOfFin rfl).strictMono (show (⟨i, by omega⟩ : Fin S.card) < ⟨i', hi'⟩ from hii')
  · obtain ⟨n, hn, hnv⟩ := h.src v hv
    have hnS : n ∈ S := mem_filter.2 ⟨mem_range.2 hn, v, hv, hnv.symm⟩
    have : n ∈ Set.range (S.orderEmbOfFin rfl) := by rw [S.range_orderEmbOfFin rfl]; exact hnS
    obtain ⟨⟨i, hi⟩, hi'⟩ := this
    have ht : t i = n := by simp only [t, hi, ↓reduceDIte, hi']
    refine ⟨i, hi, h.injJ' (mem_union_right _ (hβ i hi).1) (mem_union_right _ hv) ?_⟩
    rw [(hβ i hi).2, ht, hnv]

/-- Sources at distinct positions of the face cycle are distinct. -/
lemma corners_inj (h : FaceInst N P B q k Q g P' e j) {b : ℕ} {t : ℕ → ℕ} {β : ℕ → V}
    (ht : ∀ i i', i < i' → i' < b → t i < t i') (htk : ∀ i < b, t i < k)
    (hβ : ∀ i < b, j (β i) = Q.tail (g (t i))) :
    ∀ i < b, ∀ i' < b, β i = β i' → i = i' := by
  intro i hi i' hi' hii
  have := h.cycle.inj _ (htk i hi) _ (htk i' hi') (by rw [← hβ i hi, ← hβ i' hi', hii])
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · exact absurd this (ht i i' h' hi').ne
  · exact absurd this (ht i' i h' hi).ne'

/-- **The lengths of the dense distance graph of a part between sources are distances in the
instance**, along its face (with the reduced lengths carried by `faceLen`), shifted back by `δ`. -/
theorem childDDG_len (h : FaceInst N P B q k Q g P' e j)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {ℓ : D → ℤ} {δ : V → ℤ} (hnn : ∀ d ∈ P, 0 ≤ redLen N ℓ δ d) {x y : V} (hx : x ∈ B)
    (hy : y ∈ B) :
    (childDDG N mssp P ℓ δ B).len x y =
      (MSSP.odist (MSSP.pieceGraph Q (P'.image e) (faceLen P' e (redLen N ℓ δ))) (j x)
        (j y)).map (· + (δ y - δ x)) := by
  classical
  have hℓ : ∀ d ∈ P', faceLen P' e (redLen N ℓ δ) (e d) = redLen N ℓ δ d := fun d hd =>
    faceLen_e h.injE (fun d' hd' => hnn d' (h.sub hd')) hd
  have hnnQ : ∀ a, 0 ≤ (MSSP.pieceGraph Q (P'.image e) (faceLen P' e (redLen N ℓ δ))).len a :=
    fun a => faceLen_nonneg _ _ _ _
  have h1 := h.isDist hℓ hx (isDist_odist hnnQ (j x))
  have h2 := hmssp P (redLen N ℓ δ) B hnn x hx
  have e := congrFun (h2.unique h1) y
  show (mssp P (redLen N ℓ δ) B x y).map _ = _
  rw [e, ite_eq_left (mem_union_right _ hy)]

/-- **The dense distance graph of a part satisfies the crossing inequality in the order of the
face, with missing arcs** (`Monge.CrossingO`: for interleaved ends, if the lengths from `β i` to
`β j` and from `β i'` to `β j'` are defined, so are those from `β i` to `β j'` and from `β i'` to
`β j`, and the crossing inequality holds). No finiteness is assumed. -/
theorem crossingO_childDDG (h : FaceInst N P B q k Q g P' e j)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {ℓ : D → ℤ} {δ : V → ℤ} (hnn : ∀ d ∈ P, 0 ≤ redLen N ℓ δ d) {b : ℕ} {t : ℕ → ℕ}
    {β : ℕ → V} (ht : ∀ i i', i < i' → i' < b → t i < t i') (htk : ∀ i < b, t i < k)
    (hβB : ∀ i < b, β i ∈ B) (hβ : ∀ i < b, j (β i) = Q.tail (g (t i))) :
    Monge.CrossingO b (fun i i' => (childDDG N mssp P ℓ δ B).len (β i) (β i')) := by
  have hnnQ : ∀ a, 0 ≤ (MSSP.pieceGraph Q (P'.image e) (faceLen P' e (redLen N ℓ δ))).len a :=
    fun a => faceLen_nonneg _ _ _ _
  have hc := BKMNW.crossingO_faceCycle h.plane h.rot h.cycle (S := P'.image e)
    (ℓ := faceLen P' e (redLen N ℓ δ)) ht htk
    (Dm := fun i i' => MSSP.odist (MSSP.pieceGraph Q (P'.image e) (faceLen P' e (redLen N ℓ δ)))
      (Q.tail (g (t i))) (Q.tail (g (t i'))))
    fun i hi => ⟨_, isDist_odist hnnQ _, fun i' hi' => rfl⟩
  refine (hc.add_pot (fun i => -δ (β i)) (fun i => δ (β i))).congr fun i i' hi hi' => ?_
  rw [h.childDDG_len hmssp hnn (hβB i hi) (hβB i' hi'), hβ i hi, hβ i' hi']
  simp only [neg_add_eq_sub]

/-- **The dense distance graph of a part satisfies the crossing inequality in the order of the
face.** For a one-face instance of the part `P` with sources `B`, any implementation `mssp` of
multiple-source shortest paths in a piece (`PieceMSSPSpec`), a potential `δ` making the reduced
lengths of `P` nonnegative, and sources `β 0, …, β (b - 1)` at increasing positions
`t 0 < ⋯ < t (b - 1)` of the face cycle: if the lengths of `childDDG N mssp P ℓ δ B` between
them are all finite, they satisfy `Monge.Crossing b`. -/
theorem crossing_childDDG (h : FaceInst N P B q k Q g P' e j)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {ℓ : D → ℤ} {δ : V → ℤ} (hnn : ∀ d ∈ P, 0 ≤ redLen N ℓ δ d) {b : ℕ} {t : ℕ → ℕ}
    {β : ℕ → V} (ht : ∀ i i', i < i' → i' < b → t i < t i') (htk : ∀ i < b, t i < k)
    (hβB : ∀ i < b, β i ∈ B) (hβ : ∀ i < b, j (β i) = Q.tail (g (t i)))
    (hfin : ∀ i < b, ∀ i' < b, ((childDDG N mssp P ℓ δ B).len (β i) (β i')).isSome) :
    Monge.Crossing b (fun i i' => ((childDDG N mssp P ℓ δ B).len (β i) (β i')).getD 0) :=
  (h.crossingO_childDDG hmssp hnn ht htk hβB hβ).crossing fun i hi i' hi' => by
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (hfin i hi i' hi')
    rw [ha, Option.getD_some]

end FaceInst

/-- **From a one-face instance: an order of the sources in which the dense distance graph of the
part satisfies the crossing inequality** (when its lengths between the sources are finite). The
order `β` lists every source once. -/
theorem OneFace.crossing_childDDG (h : OneFace N P B q k) (hB : B.Nonempty)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {ℓ : D → ℤ} {δ : V → ℤ} (hnn : ∀ d ∈ P, 0 ≤ redLen N ℓ δ d) :
    ∃ (b : ℕ) (β : ℕ → V), (∀ i < b, β i ∈ B) ∧ (∀ v ∈ B, ∃ i < b, β i = v) ∧
      (∀ i < b, ∀ i' < b, β i = β i' → i = i') ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp P ℓ δ B).len (β i) (β i')) ∧
      ((∀ i < b, ∀ i' < b, ((childDDG N mssp P ℓ δ B).len (β i) (β i')).isSome) →
        Monge.Crossing b (fun i i' => ((childDDG N mssp P ℓ δ B).len (β i) (β i')).getD 0)) := by
  obtain ⟨DQ, VQ, FQ, _, _, _, _, _, _, Q, g, P', e, j, hI⟩ := h
  obtain ⟨b, t, β, ht, htk, hβB, hβ, hcov⟩ := hI.exists_corners hB
  exact ⟨b, β, hβB, hcov, hI.corners_inj ht htk hβ,
    hI.crossingO_childDDG hmssp hnn ht htk hβB hβ, hI.crossing_childDDG hmssp hnn ht htk hβB hβ⟩

/-- **Each part of a node is Monge in its own order.** At a node whose two parts have one-face
instances for their shared vertices (as `SplitF` provides), the dense distance graph of each part
satisfies the crossing inequality in an order of the shared vertices given by its own instance.
-/
theorem crossing_step_parts {P₀ P₁ : Finset D} {q₀ q₁ k₀ k₁ : ℕ}
    (h₀ : OneFace N P₀ (bdry N P₀ P₁) q₀ k₀) (h₁ : OneFace N P₁ (bdry N P₀ P₁) q₁ k₁)
    (hB : (bdry N P₀ P₁).Nonempty)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {ℓ : D → ℤ} {δ₀ δ₁ : V → ℤ} (hnn₀ : ∀ d ∈ P₀, 0 ≤ redLen N ℓ δ₀ d)
    (hnn₁ : ∀ d ∈ P₁, 0 ≤ redLen N ℓ δ₁ d) :
    (∃ (b : ℕ) (β : ℕ → V), (∀ i < b, β i ∈ bdry N P₀ P₁) ∧
      (∀ v ∈ bdry N P₀ P₁, ∃ i < b, β i = v) ∧ (∀ i < b, ∀ i' < b, β i = β i' → i = i') ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).len (β i) (β i')) ∧
      ((∀ i < b, ∀ i' < b,
        ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).len (β i) (β i')).isSome) →
        Monge.Crossing b (fun i i' =>
          ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).len (β i) (β i')).getD 0))) ∧
    (∃ (b : ℕ) (β : ℕ → V), (∀ i < b, β i ∈ bdry N P₀ P₁) ∧
      (∀ v ∈ bdry N P₀ P₁, ∃ i < b, β i = v) ∧ (∀ i < b, ∀ i' < b, β i = β i' → i = i') ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)).len (β i) (β i')) ∧
      ((∀ i < b, ∀ i' < b,
        ((childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)).len (β i) (β i')).isSome) →
        Monge.Crossing b (fun i i' =>
          ((childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)).len (β i) (β i')).getD 0))) :=
  ⟨h₀.crossing_childDDG hB hmssp hnn₀, h₁.crossing_childDDG hB hmssp hnn₁⟩

end NegSSSP

end PlanarFlow
