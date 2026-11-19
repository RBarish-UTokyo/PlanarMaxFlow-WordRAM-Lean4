module

public import PlanarFlow.NegSSSP.FaceSplit
public import PlanarFlow.NegSSSP.Cost

/-!
# The decomposition by simple cycles, with the boundary on one face: existence and cost

The recursion `PlanarFlow.NegSSSP.run` is correct on every decomposition; its cost model
(`NegCosts.Bounds`) charges multiple-source shortest paths in a piece of `m` darts from its `b`
boundary vertices `K (m lg m + b² lg m)`, the cost of Klein's algorithm when the boundary lies on
`O(1)` faces. Here the decomposition is built as in the article (Klein, Mozes and Weimann; Mozes
and Wulff-Nilsen, Section 2) from simple cycle separators, so that at every node the vertices
shared by the two parts lie on **one** face, of `O(√m)` darts, of a plane map of `O(m)` darts
containing each part (`PlanarFlow.NegSSSP.OneFace`, `h = 1`).

* `SplitF N P P₀ P₁`: the conditions at a node: the parts are disjoint and nonempty, with at most
  three quarters of the darts each; the shared vertices (`bdry`, exactly the sources of the
  multiple-source shortest paths of `step`) number `b ≤ m` with `(b + 1)² ≤ 1200 m`; and, when
  there are some, `OneFace` holds for both parts with a plane map of at most `18 m` vertices,
  faces and darts and a face of `k` darts, `k² ≤ 1200 m`.
* `exists_splitF`: **every piece of more than `10⁶` kept darts of a plane map with transitive
  rotations and faces has such a split**: if a component (`pcomp`: darts joined by darts sharing
  an end) has more than three quarters of the darts, it is split by a short simple cycle
  (`PlanarFlow.NegSSSP.exists_cycle_cut`, Miller's theorem), the rest of the piece, which shares
  no vertex with the component, joined to the smaller part (`splitF_of_comp`); otherwise the
  components are grouped into two parts sharing no vertex (`splitF_of_comps`).
* `NTree.FDec`, `exists_fDec`: **decompositions with `SplitF` at every node and leaves of at most
  `10⁶` darts exist**; their depth is at most `3 lg n` (`NTree.FDec.depth_le`).
* `negCost_le_fsq`: the cost of the recursion on such a decomposition is at most
  `10920 K n lg² n + 10⁶ K n`.
* `negDecF`, `negSSSPDecF`: **the decomposition used** and the recursion on it, correct on every
  map (`negSSSPDecF_potOut`, `negSSSPDecF_spec_dual`); `negDecF_fDec`: it meets `NTree.FDec` on
  every plane map with transitive rotations and faces; `negDecFCost_le`: its counted cost is
  `O(n log² n)`.
* `oneFace_cost_le`: a one-face call costing `K (q lg q + k² lg q)` (the form of the cost of
  Klein's algorithm, `PlanarFlow.Klein.klein_steps_le`) on the plane maps of `SplitF` costs at most
  `32886 K m lg m` at a node of `m` darts: `O(m lg m)` per node, the order of what
  `NegCosts.node_le` charges a node under `NegCosts.Bounds`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation BKMNW

/-! ### Two groups -/

/-- **Two groups**: items of weight at most `A` each, of total at most `W` with `2 W ≤ 3 A`, at
least two of them, split into two nonempty groups of weight at most `A` each. -/
lemma exists_two_groups' {ι : Type*} [DecidableEq ι] (J : Finset ι) (ω : ι → ℕ) {A W : ℕ}
    (hJ : 2 ≤ J.card) (hω : ∀ i ∈ J, ω i ≤ A) (hW : ∑ i ∈ J, ω i ≤ W) (hAW : 2 * W ≤ 3 * A) :
    ∃ S ⊆ J, S.Nonempty ∧ (J \ S).Nonempty ∧ ∑ i ∈ S, ω i ≤ A ∧ ∑ i ∈ J \ S, ω i ≤ A := by
  classical
  obtain ⟨S, hS, hmax⟩ := (J.powerset.filter fun S => ∑ i ∈ S, ω i ≤ A).exists_max_image
    (fun S => ∑ i ∈ S, ω i) ⟨∅, by simp⟩
  simp only [mem_filter, mem_powerset] at hS hmax
  obtain ⟨hSJ, hSA⟩ := hS
  have hsplit : ∑ i ∈ S, ω i + ∑ i ∈ J \ S, ω i = ∑ i ∈ J, ω i := by
    rw [add_comm, sum_sdiff hSJ]
  -- the rest weighs at most `A`
  have hrest : ∑ i ∈ J \ S, ω i ≤ A := by
    by_contra hlt
    push Not at hlt
    have h3 : 3 * ∑ i ∈ S, ω i < W := by omega
    obtain ⟨i, hi, hpos⟩ : ∃ i ∈ J \ S, 0 < ω i := by
      by_contra h
      push Not at h
      have := sum_eq_zero (s := J \ S) (f := ω) fun i hi => Nat.le_zero.1 (h i hi)
      omega
    have hiJ := (mem_sdiff.1 hi).1
    have hiS := (mem_sdiff.1 hi).2
    by_cases hfit : ∑ j ∈ S, ω j + ω i ≤ A
    · have := hmax (insert i S) ⟨insert_subset hiJ hSJ, by rw [sum_insert hiS]; omega⟩
      rw [sum_insert hiS] at this; omega
    · have := hmax {i} ⟨singleton_subset_iff.2 hiJ, by simpa using hω i hiJ⟩
      simp only [sum_singleton] at this
      omega
  -- make both groups nonempty
  by_cases hS0 : S.Nonempty
  · by_cases hS1 : (J \ S).Nonempty
    · exact ⟨S, hSJ, hS0, hS1, hSA, hrest⟩
    · have hSeq : S = J := by
        rw [not_nonempty_iff_eq_empty, sdiff_eq_empty_iff_subset] at hS1
        exact Subset.antisymm hSJ hS1
      obtain ⟨i, hi⟩ := hS0
      refine ⟨{i}, singleton_subset_iff.2 (hSeq ▸ hi), singleton_nonempty _, ?_, ?_, ?_⟩
      · rw [← card_pos, card_sdiff_of_subset (singleton_subset_iff.2 (hSeq ▸ hi)), card_singleton]
        omega
      · simpa using hω i (hSeq ▸ hi)
      · have := sum_le_sum_of_subset (f := ω) (sdiff_subset (s := J) (t := {i}))
        rw [← hSeq] at this ⊢; omega
  · rw [not_nonempty_iff_eq_empty] at hS0
    subst hS0
    rw [sdiff_empty] at hrest
    obtain ⟨i, hi⟩ : J.Nonempty := card_pos.1 (by omega)
    refine ⟨{i}, singleton_subset_iff.2 hi, singleton_nonempty _, ?_, by simpa using hω i hi, ?_⟩
    · rw [← card_pos, card_sdiff_of_subset (singleton_subset_iff.2 hi), card_singleton]; omega
    · exact (sum_le_sum_of_subset sdiff_subset).trans hrest

/-! ### The components of a piece -/

section Comp

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {N : CombMap D V F}

lemma share_symm {a b : D} (h : Share N a b) : Share N b a := by
  unfold Share at *
  rcases h with h | h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr (Or.inl h.symm))
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr (Or.inr h.symm))

lemma share_of {a b : D} {v : V} (ha : N.tail a = v ∨ N.head a = v)
    (hb : N.tail b = v ∨ N.head b = v) : Share N a b := by
  unfold Share
  rcases ha with rfl | rfl <;> rcases hb with h | h <;> tauto

variable (N) in
/-- **The component of `x` in the piece `P`**: the darts of `P` joined to `x` by darts of `P`,
each sharing an end with the next. -/
noncomputable def pcomp (P : Finset D) (x : D) : Finset D := by
  classical exact P.filter fun y => ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ Share N a b) x y

lemma mem_pcomp {P : Finset D} {x y : D} :
    y ∈ pcomp N P x ↔ y ∈ P ∧ ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ Share N a b) x y := by
  classical
  unfold pcomp; rw [mem_filter]

lemma pcomp_subset (P : Finset D) (x : D) : pcomp N P x ⊆ P := fun _ h => (mem_pcomp.1 h).1

lemma self_mem_pcomp {P : Finset D} {x : D} (hx : x ∈ P) : x ∈ pcomp N P x :=
  mem_pcomp.2 ⟨hx, .refl⟩

lemma rtg_share_symm {P : Finset D} {x y : D}
    (h : ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ Share N a b) x y) :
    ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ Share N a b) y x := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact (ReflTransGen.single ⟨hst.2.1, hst.1, share_symm hst.2.2⟩).trans ih

lemma pcomp_eq {P : Finset D} {x y : D} (hy : y ∈ pcomp N P x) : pcomp N P y = pcomp N P x := by
  have hxy := (mem_pcomp.1 hy).2
  ext z
  rw [mem_pcomp, mem_pcomp]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, hxy.trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (rtg_share_symm hxy).trans h2⟩⟩

lemma mem_pcomp_of_share {P : Finset D} {x d e : D} (hd : d ∈ pcomp N P x) (he : e ∈ P)
    (h : Share N d e) : e ∈ pcomp N P x := by
  obtain ⟨hdP, hxd⟩ := mem_pcomp.1 hd
  exact mem_pcomp.2 ⟨he, hxd.tail ⟨hdP, he, h⟩⟩

/-- **A component is connected.** -/
lemma pcomp_dconn {P : Finset D} {x : D} : DConn N (pcomp N P x) := by
  have key : ∀ a ∈ pcomp N P x, ∀ b, ReflTransGen (fun a b => a ∈ P ∧ b ∈ P ∧ Share N a b) a b →
      ReflTransGen (fun a b => a ∈ pcomp N P x ∧ b ∈ pcomp N P x ∧ Share N a b) a b := by
    intro a ha b h
    induction h with
    | refl => exact .refl
    | @tail b c hab hst ih =>
      have hb : b ∈ pcomp N P x := mem_pcomp.2 ⟨hst.1, (mem_pcomp.1 ha).2.trans hab⟩
      exact ih.tail ⟨hb, mem_pcomp_of_share hb hst.2.1 hst.2.2, hst.2.2⟩
  intro a ha b hb
  exact key a ha b ((rtg_share_symm (mem_pcomp.1 ha).2).trans (mem_pcomp.1 hb).2)

lemma verts_union (X Y : Finset D) : verts N (X ∪ Y) = verts N X ∪ verts N Y := by
  unfold verts; rw [image_union, image_union]; ext; simp only [mem_union]; tauto

/-- **The rest of a piece shares no vertex with a component.** -/
lemma disjoint_verts_pcomp (P : Finset D) (x : D) :
    Disjoint (verts N (P \ pcomp N P x)) (verts N (pcomp N P x)) := by
  refine disjoint_left.2 fun v hv hv' => ?_
  obtain ⟨d, hd, e⟩ := mem_verts_iff'.1 hv
  obtain ⟨d', hd', e'⟩ := mem_verts_iff'.1 hv'
  exact (mem_sdiff.1 hd).2 (mem_pcomp_of_share hd' (mem_sdiff.1 hd).1 (share_of e' e))

end Comp

/-! ### The split of a large piece -/

section Split

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {N : CombMap D V F}

/-- Above `10⁶` darts, `48 (6 √(12 m) + 4) ≤ m`. -/
lemma sqrt_cut_le {m : ℕ} (hm : 1000000 < m) : 48 * (6 * Nat.sqrt (12 * m) + 4) ≤ m := by
  have h := Nat.sqrt_le' (12 * m)
  set r := Nat.sqrt (12 * m)
  by_contra h'
  have hr : 3472 ≤ r := by omega
  nlinarith

lemma succ_sq_cut_le {m c : ℕ} (hm : 1 ≤ m) (hc : c ≤ 6 * Nat.sqrt (12 * m) + 4) :
    (c + 1) ^ 2 ≤ 1200 * m := by
  have h := Nat.sqrt_le' (12 * m)
  set r := Nat.sqrt (12 * m)
  have h1 : (c + 1) ^ 2 ≤ (6 * r + 5) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have h2 : r ≤ r ^ 2 := by nlinarith
  nlinarith

lemma OneFace.mono {P : Finset D} {B : Finset V} {q q' k : ℕ} (h : OneFace N P B q k)
    (hq : q ≤ q') : OneFace N P B q' k := by
  obtain ⟨DQ, VQ, FQ, i1, i2, i3, i4, i5, i6, Q, g, P', e, j, h⟩ := h
  exact ⟨DQ, VQ, FQ, i1, i2, i3, i4, i5, i6, Q, g, P', e, j, { h with card := h.card.trans hq }⟩

lemma bdry_union_right {X Y R : Finset D} (hR : Disjoint (verts N R) (verts N Y)) :
    bdry N (X ∪ R) Y = bdry N X Y := by
  unfold bdry
  rw [verts_union, union_inter_distrib_right, disjoint_iff_inter_eq_empty.1 hR, union_empty]

lemma bdry_comm (X Y : Finset D) : bdry N X Y = bdry N Y X := inter_comm _ _

/-- **The node conditions of the decomposition** at a split of `P` into `P₀` and `P₁`: disjoint,
nonempty, at most three quarters of the darts each, the shared vertices at most `m` with
`(b + 1)² ≤ 1200 m`, and, when there are shared vertices, multiple-source shortest paths from
them in each part are one call from a face of `k` darts, `k² ≤ 1200 m`, of a plane map with at
most `18 m` vertices, faces and darts (`OneFace`). -/
def SplitF (N : CombMap D V F) (P P₀ P₁ : Finset D) : Prop :=
  P₀ ∪ P₁ = P ∧ Disjoint P₀ P₁ ∧ 0 < P₀.card ∧ 0 < P₁.card ∧ 4 * P₀.card ≤ 3 * P.card ∧
    4 * P₁.card ≤ 3 * P.card ∧ ((bdry N P₀ P₁).card + 1) ^ 2 ≤ 1200 * P.card ∧
    (bdry N P₀ P₁).card ≤ P.card ∧
    ((bdry N P₀ P₁).Nonempty → ∃ k, k ^ 2 ≤ 1200 * P.card ∧
      OneFace N P₀ (bdry N P₀ P₁) (18 * P.card) k ∧ OneFace N P₁ (bdry N P₀ P₁) (18 * P.card) k)

/-- **A large connected component is split by a short simple cycle**, the rest of the piece
joined to the smaller part. -/
lemma splitF_of_comp (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {P : Finset D} (hPr : P ⊆ reps N) (hs : 1000000 < P.card) {x : D} (hx : x ∈ P)
    (hbig : 3 * P.card / 4 < (pcomp N P x).card) :
    ∃ P₀ P₁, SplitF N P P₀ P₁ := by
  set K := pcomp N P x with hKdef
  have hKP : K ⊆ P := pcomp_subset P x
  have hKr : K ⊆ reps N := hKP.trans hPr
  obtain ⟨A₀, A₁, c, hu, hd, hc, h0, h1, hb, hw⟩ :=
    exists_cycle_cut hM hrot hface hKr ⟨x, self_mem_pcomp hx⟩ pcomp_dconn
  set R := P \ K with hR
  have hRd : Disjoint (verts N R) (verts N K) := disjoint_verts_pcomp P x
  have hK : K.card ≤ P.card := card_le_card hKP
  have hc' : c ≤ 6 * Nat.sqrt (12 * P.card) + 4 :=
    hc.trans (by have := Nat.sqrt_le_sqrt (Nat.mul_le_mul_left 12 hK); omega)
  have h48 := sqrt_cut_le hs
  have hsq := succ_sq_cut_le (by omega) hc'
  have hcard : A₀.card + A₁.card = K.card := by rw [← card_union_of_disjoint hd, hu]
  have hRc : R.card + K.card = P.card := by rw [hR, card_sdiff_add_card_eq_card hKP]
  have hA₀K : A₀ ⊆ K := hu ▸ subset_union_left
  have hA₁K : A₁ ⊆ K := hu ▸ subset_union_right
  have hRA₀ : Disjoint R A₀ := disjoint_left.2 fun d hd h => (mem_sdiff.1 hd).2 (hA₀K h)
  have hRA₁ : Disjoint R A₁ := disjoint_left.2 fun d hd h => (mem_sdiff.1 hd).2 (hA₁K h)
  have hv₀ : Disjoint (verts N R) (verts N A₀) := hRd.mono_right (verts_mono hA₀K)
  have hv₁ : Disjoint (verts N R) (verts N A₁) := hRd.mono_right (verts_mono hA₁K)
  have hbP : (bdry N A₀ A₁).card ≤ P.card := by omega
  have hsq' : ((bdry N A₀ A₁).card + 1) ^ 2 ≤ 1200 * P.card :=
    (Nat.pow_le_pow_left (by omega) 2).trans hsq
  have hcsq : c ^ 2 ≤ 1200 * P.card := (Nat.pow_le_pow_left (by omega) 2).trans hsq
  obtain ⟨w₀, w₁⟩ := hw R hRd
  obtain ⟨w₀', w₁'⟩ := hw ∅ (by simp [verts])
  rw [union_empty] at w₀' w₁'
  rcases le_total A₀.card A₁.card with hle | hle
  · refine ⟨A₀ ∪ R, A₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [union_right_comm, hu, union_sdiff_of_subset hKP]
    · exact disjoint_union_left.2 ⟨hd, hRA₁⟩
    · rw [card_union_of_disjoint hRA₀.symm]; omega
    · omega
    · rw [card_union_of_disjoint hRA₀.symm]; omega
    · omega
    · rwa [bdry_union_right hv₁]
    · rwa [bdry_union_right hv₁]
    · intro _
      rw [bdry_union_right hv₁]
      exact ⟨c, hcsq, w₀.mono (by omega), w₁'.mono (by omega)⟩
  · refine ⟨A₀, A₁ ∪ R, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← union_assoc, hu, union_sdiff_of_subset hKP]
    · exact disjoint_union_right.2 ⟨hd, hRA₀.symm⟩
    · omega
    · rw [card_union_of_disjoint hRA₁.symm]; omega
    · omega
    · rw [card_union_of_disjoint hRA₁.symm]; omega
    · rwa [bdry_comm, bdry_union_right hv₀, bdry_comm]
    · rwa [bdry_comm, bdry_union_right hv₀, bdry_comm]
    · intro _
      rw [bdry_comm, bdry_union_right hv₀, bdry_comm]
      exact ⟨c, hcsq, w₀'.mono (by omega), w₁.mono (by omega)⟩

/-- **Small components are grouped into two parts** sharing no vertex
(`exists_two_groups'`). -/
lemma splitF_of_comps {P : Finset D} (hs : 1000000 < P.card)
    (hsmall : ∀ x ∈ P, (pcomp N P x).card ≤ 3 * P.card / 4) : ∃ P₀ P₁, SplitF N P P₀ P₁ := by
  classical
  set J := P.image (pcomp N P) with hJdef
  have hcls : ∀ X ∈ J, ∀ Y ∈ J, X ≠ Y → Disjoint X Y := by
    intro X hX Y hY hXY
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hY
    refine disjoint_left.2 fun z hz hz' => hXY ?_
    rw [← pcomp_eq hz, pcomp_eq hz']
  have hcard : ∀ T ⊆ J, (T.biUnion id).card = ∑ X ∈ T, X.card := fun T hT =>
    card_biUnion fun X hX Y hY h => hcls X (hT (mem_coe.1 hX)) Y (hT (mem_coe.1 hY)) h
  have hcov : J.biUnion id = P := by
    ext z
    simp only [mem_biUnion, id, hJdef, mem_image]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, hz⟩; exact pcomp_subset P x hz
    · intro hz; exact ⟨_, ⟨z, hz, rfl⟩, self_mem_pcomp hz⟩
  have hsum : ∑ X ∈ J, X.card = P.card := by rw [← hcard J subset_rfl, hcov]
  have hω : ∀ X ∈ J, X.card ≤ 3 * P.card / 4 := by
    intro X hX
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
    exact hsmall x hx
  have hJ2 : 2 ≤ J.card := by
    by_contra h
    have hP0 : P.Nonempty := card_pos.1 (by omega)
    have hJ1 : J.card = 1 := by
      have : 0 < J.card := card_pos.2 (hP0.image _)
      omega
    obtain ⟨X, hX⟩ := card_eq_one.1 hJ1
    have hXP : X = P := by rw [← hcov, hX, singleton_biUnion, id]
    have := hω X (by rw [hX]; exact mem_singleton_self X)
    rw [hXP] at this
    omega
  obtain ⟨S, hSJ, hS0, hS1, hSA, hSA'⟩ :=
    exists_two_groups' J card hJ2 hω hsum.le (by omega)
  have hne : ∀ X ∈ J, X.Nonempty := fun X hX => by
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
    exact ⟨x, self_mem_pcomp hx⟩
  have hbd : bdry N (S.biUnion id) ((J \ S).biUnion id) = ∅ := by
    refine eq_empty_of_forall_notMem fun v hv => ?_
    obtain ⟨h0, h1⟩ := mem_inter.1 hv
    obtain ⟨d₀, hd₀, e₀⟩ := mem_verts_iff'.1 h0
    obtain ⟨d₁, hd₁, e₁⟩ := mem_verts_iff'.1 h1
    obtain ⟨X, hX, hdX⟩ := mem_biUnion.1 hd₀
    obtain ⟨Y, hY, hdY⟩ := mem_biUnion.1 hd₁
    obtain ⟨x, hx, rfl⟩ := mem_image.1 (hSJ hX)
    have hd₁P : d₁ ∈ P := hcov ▸ mem_biUnion.2 ⟨Y, (mem_sdiff.1 hY).1, hdY⟩
    have hin := mem_pcomp_of_share hdX hd₁P (share_of e₀ e₁)
    have hXY : pcomp N P x ≠ Y := fun h => (mem_sdiff.1 hY).2 (h ▸ hX)
    exact disjoint_left.1 (hcls _ (hSJ hX) Y (mem_sdiff.1 hY).1 hXY) hin hdY
  refine ⟨S.biUnion id, (J \ S).biUnion id, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← union_biUnion, union_sdiff_of_subset hSJ, hcov]
  · refine (disjoint_biUnion_left _ _ _).2 fun X hX => (disjoint_biUnion_right _ _ _).2
      fun Y hY => ?_
    exact hcls X (hSJ hX) Y (mem_sdiff.1 hY).1 fun h => (mem_sdiff.1 hY).2 (h ▸ hX)
  · obtain ⟨X, hX⟩ := hS0
    obtain ⟨z, hz⟩ := hne X (hSJ hX)
    exact card_pos.2 ⟨z, mem_biUnion.2 ⟨X, hX, hz⟩⟩
  · obtain ⟨X, hX⟩ := hS1
    obtain ⟨z, hz⟩ := hne X (mem_sdiff.1 hX).1
    exact card_pos.2 ⟨z, mem_biUnion.2 ⟨X, hX, hz⟩⟩
  · rw [hcard S hSJ]; omega
  · rw [hcard _ sdiff_subset]; omega
  · rw [hbd, card_empty]; omega
  · rw [hbd, card_empty]; omega
  · rw [hbd]; exact fun h => absurd h not_nonempty_empty

/-- **Every large piece of the simple graph of a plane map with transitive rotations and faces
has a split meeting `SplitF`**: by a short simple cycle in a component of more than three
quarters of the darts (`splitF_of_comp`), or by grouping the components (`splitF_of_comps`). -/
theorem exists_splitF (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {P : Finset D} (hPr : P ⊆ reps N) (hs : 1000000 < P.card) : ∃ P₀ P₁, SplitF N P P₀ P₁ := by
  by_cases h : ∃ x ∈ P, 3 * P.card / 4 < (pcomp N P x).card
  · obtain ⟨x, hx, hb⟩ := h
    exact splitF_of_comp hM hrot hface hPr hs hx hb
  · push Not at h
    exact splitF_of_comps hs h

end Split

/-! ### The decomposition and its cost -/

section Dec

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {N : CombMap D V F}

namespace NTree

variable (N) in
/-- **A decomposition by simple cycles with the boundary on one face**: every node meets
`SplitF` (in particular `OneFace` for both parts), every leaf has at most `10⁶` darts. -/
def FDec : NTree D → Prop
  | leaf P => P.card ≤ 1000000
  | node l r => l.FDec ∧ r.FDec ∧ SplitF N (l.piece ∪ r.piece) l.piece r.piece

/-- **The depth of a decomposition by simple cycles**: `(4/3)^depth ≤ n`. -/
theorem FDec.pow_depth :
    ∀ {τ : NTree D}, τ.FDec N → 0 < τ.piece.card → 4 ^ τ.depth ≤ 3 ^ τ.depth * τ.piece.card
  | leaf _, _, hpos => by simp only [depth, pow_zero, one_mul]; exact hpos
  | node l r, h, _ => by
    obtain ⟨hl, hr, -, -, hl0, hr0, b0, b1, -⟩ := h
    have il := FDec.pow_depth hl hl0
    have ir := FDec.pow_depth hr hr0
    simp only [depth, piece] at il ir ⊢
    rcases le_total l.depth r.depth with hle | hle
    · rw [max_eq_right hle, pow_succ, pow_succ]
      nlinarith [Nat.zero_le (3 ^ r.depth)]
    · rw [max_eq_left hle, pow_succ, pow_succ]
      nlinarith [Nat.zero_le (3 ^ l.depth)]

lemma two_pow_third_mul (d : ℕ) : 2 ^ (d / 3) * 3 ^ d ≤ 4 ^ d := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ d = 3 * q + r :=
    ⟨d / 3, d % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod d 3).symm⟩
  rw [show (3 * q + r) / 3 = q by omega, pow_add, pow_add, pow_mul, pow_mul]
  have h1 : 2 ^ q * (3 ^ 3) ^ q ≤ (4 ^ 3) ^ q := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) q
  have h2 : 3 ^ r ≤ 4 ^ r := Nat.pow_le_pow_left (by norm_num) r
  calc 2 ^ q * ((3 ^ 3) ^ q * 3 ^ r) = (2 ^ q * (3 ^ 3) ^ q) * 3 ^ r := by ring
    _ ≤ (4 ^ 3) ^ q * 4 ^ r := Nat.mul_le_mul h1 h2

/-- The depth of a decomposition by simple cycles of `n ≥ 1` darts is at most `3 lg n`. -/
theorem FDec.depth_le {τ : NTree D} (h : τ.FDec N) (hpos : 0 < τ.piece.card) :
    τ.depth ≤ 3 * lg τ.piece.card := by
  have h1 := h.pow_depth hpos
  have h2 := two_pow_third_mul τ.depth
  have h3 : 2 ^ (τ.depth / 3) ≤ τ.piece.card :=
    Nat.le_of_mul_le_mul_right (h2.trans (h1.trans (by rw [mul_comm]))) (by positivity)
  have := Nat.le_log_of_pow_le (by norm_num) h3
  unfold lg
  omega

end NTree

/-- **The cost per depth** of a decomposition by simple cycles: `O(n lg n)` per depth, with
`β = 1200` in `NegCosts.node_le`. -/
theorem negCost_le_fdepth {c : NegCosts} {K Nn : ℕ} (hc : c.Bounds K) :
    ∀ {τ : NTree D}, τ.FDec N → τ.piece.card ≤ Nn →
      negCost N c τ ≤ (40 + 3 * 1200) * K * lg Nn * (τ.piece.card * τ.depth) +
        K * 1000000 * τ.piece.card
  | .leaf P, hs, _ => by
    simp only [negCost, NTree.piece, NTree.depth, mul_zero, zero_add]
    calc c.leaf P.card ≤ K * P.card ^ 2 := hc.leaf _
      _ = K * P.card * P.card := by ring
      _ ≤ K * 1000000 * P.card := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hs)
  | .node l r, h, hN => by
    obtain ⟨hl, hr, -, hlr, hl0, hr0, -, -, hb, hbm, -⟩ := h
    have hcard : (l.piece ∪ r.piece).card = l.piece.card + r.piece.card :=
      card_union_of_disjoint hlr
    simp only [NTree.piece] at hN
    have il := negCost_le_fdepth hc hl (by omega : l.piece.card ≤ Nn)
    have ir := negCost_le_fdepth hc hr (by omega : r.piece.card ≤ Nn)
    have hn := NegCosts.node_le hc hl0 hr0 (by omega) (by omega)
      (NTree.card_verts_le (N := N) l.piece) (NTree.card_verts_le (N := N) r.piece) hbm hb
    have hlg : lg (l.piece ∪ r.piece).card ≤ lg Nn := lg_mono hN
    generalize (40 + 3 * 1200) * K = B at il ir hn ⊢
    have hn' : c.node (l.piece ∪ r.piece).card (bdry N l.piece r.piece).card l.piece.card
        (verts N l.piece).card r.piece.card (verts N r.piece).card ≤
        B * lg Nn * (l.piece ∪ r.piece).card := by
      calc _ ≤ B * (l.piece ∪ r.piece).card * lg (l.piece ∪ r.piece).card := hn
        _ ≤ B * (l.piece ∪ r.piece).card * lg Nn := Nat.mul_le_mul_left _ hlg
        _ = _ := by ring
    simp only [negCost, NTree.piece, NTree.depth]
    rw [hcard] at hn' ⊢
    generalize B * lg Nn = A at il ir hn' ⊢
    have hw : l.piece.card * l.depth + r.piece.card * r.depth + (l.piece.card + r.piece.card) ≤
        (l.piece.card + r.piece.card) * (max l.depth r.depth + 1) := by
      nlinarith [Nat.mul_le_mul_left l.piece.card (le_max_left l.depth r.depth),
        Nat.mul_le_mul_left r.piece.card (le_max_right l.depth r.depth)]
    have := Nat.mul_le_mul_left A hw
    nlinarith

/-- **The cost of the recursion on a decomposition by simple cycles is `O(n log² n)`**: at most
`10920 K n lg² n + 10⁶ K n` for `n` darts. -/
theorem negCost_le_fsq {c : NegCosts} {K : ℕ} (hc : c.Bounds K) {τ : NTree D} (h : τ.FDec N) :
    negCost N c τ ≤ 10920 * K * τ.piece.card * lg τ.piece.card ^ 2 +
      1000000 * K * τ.piece.card := by
  rcases Nat.eq_zero_or_pos τ.piece.card with h0 | hpos
  · cases τ with
    | leaf P =>
      simp only [NTree.piece] at h0
      simp only [negCost, h0, NTree.piece, mul_zero, zero_mul, add_zero]
      have := hc.leaf 0
      simpa using this
    | node l r =>
      obtain ⟨-, -, -, -, hl0, -⟩ := h
      simp only [NTree.piece] at h0
      have := card_le_card (subset_union_left (s₁ := l.piece) (s₂ := r.piece))
      omega
  have h1 := negCost_le_fdepth hc h le_rfl
  have h2 := h.depth_le hpos
  have h3 : (40 + 3 * 1200) * K * lg τ.piece.card * (τ.piece.card * τ.depth) ≤
      (40 + 3 * 1200) * K * lg τ.piece.card * (τ.piece.card * (3 * lg τ.piece.card)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
  calc _ ≤ _ := h1
    _ ≤ (40 + 3 * 1200) * K * lg τ.piece.card * (τ.piece.card * (3 * lg τ.piece.card)) +
        K * 1000000 * τ.piece.card := Nat.add_le_add_right h3 _
    _ = _ := by ring

/-- **Decompositions by simple cycles exist** for every set of kept darts of a plane map with
transitive rotations and faces (`exists_splitF` at every piece of more than `10⁶` darts). -/
theorem exists_fDec (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) :
    ∀ (n : ℕ) (P : Finset D), P.card ≤ n → P ⊆ reps N → ∃ τ : NTree D, τ.piece = P ∧ τ.FDec N := by
  intro n
  induction n with
  | zero => intro P hP _; exact ⟨.leaf P, rfl, by simp only [NTree.FDec]; omega⟩
  | succ n ih =>
    intro P hP hPr
    by_cases hs : 1000000 < P.card
    · obtain ⟨P₀, P₁, h⟩ := exists_splitF hM hrot hface hPr hs
      have h' := h
      obtain ⟨hu, -, -, -, hc0, hc1, -⟩ := h'
      have hP₀ : P₀ ⊆ P := hu ▸ subset_union_left
      have hP₁ : P₁ ⊆ P := hu ▸ subset_union_right
      obtain ⟨τ₀, e₀, g₀⟩ := ih P₀ (by omega) (hP₀.trans hPr)
      obtain ⟨τ₁, e₁, g₁⟩ := ih P₁ (by omega) (hP₁.trans hPr)
      refine ⟨.node τ₀ τ₁, by simp only [NTree.piece, e₀, e₁, hu], g₀, g₁, ?_⟩
      rw [e₀, e₁, hu]; exact h
    · exact ⟨.leaf P, rfl, by simp only [NTree.FDec]; omega⟩

end Dec

/-! ### The decomposition used and its cost -/

section Impl

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {N : CombMap D V F}

variable (N) in
/-- **The decomposition used**: a decomposition of the kept darts by simple cycles meeting
`NTree.FDec` if there is one (on every plane map with transitive rotations and faces there is
one, `negDecF_fDec`), the leaf of all kept darts otherwise. -/
noncomputable def negDecF : NTree D := by
  classical exact
    if h : ∃ τ : NTree D, τ.piece = reps N ∧ τ.FDec N then h.choose else .leaf (reps N)

lemma piece_negDecF : (negDecF N).piece = reps N := by
  classical
  unfold negDecF
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

/-- **The decomposition used is by simple cycles, with the boundary on one face** at every node,
on every plane map with transitive rotations and faces. -/
theorem negDecF_fDec (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans) :
    (negDecF N).FDec N := by
  classical
  have hex : ∃ τ : NTree D, τ.piece = reps N ∧ τ.FDec N :=
    exists_fDec hM hrot hface _ (reps N) le_rfl subset_rfl
  unfold negDecF
  simp only [hex, ↓reduceDIte]
  exact hex.choose_spec.2

variable (N) in
/-- **Shortest paths with negative lengths** in the graph of `N`: the recursion through the
simple graph on the decomposition by simple cycles `negDecF N`. -/
noncomputable def negSSSPDecF (mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ)
    (bf : DDG V → DDG V → Option (V → ℤ))
    (fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ) (ℓ : D → ℤ) : Option (V → ℤ) :=
  negSSSPS N mssp bf fr (negDecF N) ℓ

/-- **Correctness of `negSSSPDecF`**, on every map. -/
theorem negSSSPDecF_potOut {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ}
    (hmssp : PieceMSSPSpec N mssp) {bf : DDG V → DDG V → Option (V → ℤ)} (hbf : BFDDGSpec bf)
    {fr : DDG (Option V) → List (Option V × Option V × ℤ) → Option V → (Option V → ℤ) →
      Option V → Option ℤ} (hfr : FRSpec fr) (ℓ : D → ℤ) :
    PotOut (N.graph ℓ) (negSSSPDecF N mssp bf fr ℓ) :=
  negSSSPS_potOut hmssp hbf hfr piece_negDecF ℓ

/-- **The recursion `negSSSPDecF` on the dual map meets `NegSSSPSpec`**, on every map. -/
theorem negSSSPDecF_spec_dual (M : CombMap D V F)
    {mssp : Finset D → (D → ℤ) → Finset F → F → F → Option ℤ}
    (hmssp : PieceMSSPSpec M.dual mssp) {bf : DDG F → DDG F → Option (F → ℤ)}
    (hbf : BFDDGSpec bf)
    {fr : DDG (Option F) → List (Option F × Option F × ℤ) → Option F → (Option F → ℤ) →
      Option F → Option ℤ} (hfr : FRSpec fr) :
    NegSSSPSpec M (negSSSPDecF M.dual mssp bf fr) := fun ℓ => by
  rw [← dual_graph]
  exact negSSSPOut_of_potOut (negSSSPDecF_potOut hmssp hbf hfr ℓ)

variable (N) in
/-- **The counted cost of `negSSSPDecF`**: the simple graph (linear bookkeeping on the `n`
darts) and the recursion on `negDecF N`. The decomposition is given by an existence proof; the
computation of its cycles (Miller: linear time per separator in the article, `O(m log m)` on the
machine) is charged at the nodes, as the separator calls `c.sep` (`K m lg m`). -/
noncomputable def negDecFCost (c : NegCosts) : ℕ :=
  c.lin (Fintype.card D) + negCost N c (negDecF N)

/-- **The cost of `negSSSPDecF` is `O(n log² n)`**: on a plane map with transitive rotations and
faces and `n` darts, at most `10920 K n lg² n + (10⁶ + 1) K n`, for every family of subroutine
costs meeting `NegCosts.Bounds K`. -/
theorem negDecFCost_le (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {c : NegCosts} {K : ℕ} (hc : c.Bounds K) :
    negDecFCost N c ≤ 10920 * K * Fintype.card D * lg (Fintype.card D) ^ 2 +
      1000001 * K * Fintype.card D := by
  have h1 := hc.lin (Fintype.card D)
  have h2 := negCost_le_fsq hc (negDecF_fDec hM hrot hface)
  rw [piece_negDecF] at h2
  have hr : (reps N).card ≤ Fintype.card D := card_le_univ _
  have hl := lg_mono hr
  have h3 : 10920 * K * (reps N).card * lg (reps N).card ^ 2 ≤
      10920 * K * Fintype.card D * lg (Fintype.card D) ^ 2 := by gcongr
  have h4 : 1000000 * K * (reps N).card ≤ 1000000 * K * Fintype.card D := by gcongr
  unfold negDecFCost
  nlinarith

/-- **A one-face call at the cost of Klein's algorithm costs `O(m lg m)` at a node**, like the
multiple-source shortest paths charged by `NegCosts.Bounds.mssp` (`K (mᵢ lg mᵢ + b² lg mᵢ)` with
`(b + 1)² ≤ 1200 m`): for a cost
`f q k ≤ K (q lg q + k² lg q)` on a plane map with `q` vertices, faces and darts from a face of
`k` darts (the form of `PlanarFlow.Klein.klein_steps_le`), the calls of the decomposition by
simple cycles (`OneFace` with `q ≤ 18 m`, `k² ≤ 1200 m`, `SplitF`) cost at most
`32886 K m lg m` at a node of `m` darts: `O(m lg m)` per node, the order of what
`NegCosts.node_le` charges a node under `NegCosts.Bounds`. -/
theorem oneFace_cost_le {f : ℕ → ℕ → ℕ} {K : ℕ}
    (hf : ∀ q k, f q k ≤ K * (q * lg q + k ^ 2 * lg q))
    {m q k : ℕ} (hq : q ≤ 18 * m) (hk : k ^ 2 ≤ 1200 * m) : f q k ≤ 32886 * K * m * lg m := by
  have hl : lg q ≤ 27 * lg m := by
    have h1 := lg_mono (show q ≤ 3 * (3 * (3 * m)) by omega)
    have h2 := lg_three_mul (3 * (3 * m))
    have h3 := lg_three_mul (3 * m)
    have h4 := lg_three_mul m
    omega
  calc f q k ≤ K * (q * lg q + k ^ 2 * lg q) := hf q k
    _ ≤ K * (18 * m * (27 * lg m) + 1200 * m * (27 * lg m)) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.mul_le_mul hq hl) (Nat.mul_le_mul hk hl))
    _ = 32886 * K * m * lg m := by ring

end Impl

end NegSSSP

end PlanarFlow
