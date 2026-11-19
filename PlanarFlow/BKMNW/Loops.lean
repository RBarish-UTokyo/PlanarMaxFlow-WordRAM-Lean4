module

public import PlanarFlow.BKMNW.ExistPre

/-!
# Deleting the loops

The balanced decompositions of the preprocessed map (`PlanarFlow.BKMNW.exists_balDecA_pre`) need
a map without loops: the stellar subdivision of a map with a loop has a face of two edges. A loop
carries no net flow between vertices: the flows on its two darts cancel in the net outflow of its
vertex. So the loops can be deleted first.

* `nlMap M`: the map of the darts of `M` that are not loops (`nlDarts`), the rotation the first
  return of the rotation of `M` (`PlanarFlow.Orbit.ret`): a submap (`PlanarFlow.Orbit.subMap`),
  with transitive rotations and faces, without loops (`nlMap_loopless`), plane when `M` is plane
  with transitive rotations and faces and has a dart that is not a loop (`nlMap_isPlane`: the
  Euler gap stays zero, `PlanarFlow.Orbit.gap_ret_eq_zero`, and deleting loops keeps the graph
  connected). Its vertices are the vertices of `M` with a dart that is not a loop (`nlVert`,
  injective).
* `isMax_nlExt`: **a maximum flow of `nlMap M`, extended by zero on the loops, is a maximum flow
  of `M`**, for the capacities of `M` and the terminals of `M` that remain (`nlTerm`).
* `maxflow_cost`: **the algorithm `runL` on the preprocessed map of `nlMap M` computes a maximum
  flow of `M`, at a cost `O(n lg³ n)`**, on every plane map with transitive rotations and faces,
  with or without loops: `maxflow_pre_cost` without its hypothesis that `M` has no loop. When
  every dart is a loop, the preprocessed map is empty, the flow is zero, and the cost is zero.
* `loopMap`: a plane map with one vertex and one loop, meeting the hypotheses of `maxflow_cost`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap Orbit Function Equiv Relation PlanarSeparator.StDart

universe w

section Loops

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- The darts of `M` that are not loops. -/
def nlDarts : Finset D := univ.filter fun d => M.head d ≠ M.tail d

lemma mem_nlDarts {d : D} : d ∈ nlDarts M ↔ M.head d ≠ M.tail d := by simp [nlDarts]

lemma stable_rev_nlDarts : Stable (revPerm M) (nlDarts M) := fun d hd => by
  simp only [revPerm_apply, mem_nlDarts, head_rev, tail_rev] at hd ⊢
  exact Ne.symm hd

variable (M) in
/-- The rotation of `M` with the loops deleted: the first return to the darts that are not
loops. -/
noncomputable def nlRot : Perm D := ret (rotPerm M) (nlDarts M)

variable (M) in
/-- **The map with the loops deleted.** -/
noncomputable def nlMap : CombMap (SDart (nlDarts M)) (SVert (nlRot M) (nlDarts M))
    (SFace (nlRot M) (nlDarts M) (revPerm M)) :=
  subMap (nlDarts M) (revPerm_isInv M) (stable_ret _ _) stable_rev_nlDarts

theorem nlMap_rotTrans : (nlMap M).RotTrans := subMap_rotTrans _ _ _

theorem nlMap_faceTrans : (nlMap M).FaceTrans := subMap_faceTrans _ _ _

variable (M) in
/-- The vertex of `M` of a vertex of the map without loops. -/
noncomputable def nlVert : SVert (nlRot M) (nlDarts M) → V :=
  Quotient.lift (fun x => M.tail x.1) fun x y h => by
    obtain ⟨n, hn⟩ := sameCycle_iff.1 ((sameCycle_ret (π := rotPerm M) x.2 y.2).1 h)
    rw [← hn, iterate_rotPerm, tail_rot_iterate]

lemma nlVert_tail (x : SDart (nlDarts M)) : nlVert M ((nlMap M).tail x) = M.tail x.1 := rfl

lemma nlVert_head (x : SDart (nlDarts M)) : nlVert M ((nlMap M).head x) = M.head x.1 := rfl

lemma nlVert_injective (hrot : M.RotTrans) : Injective (nlVert M) := by
  intro a b h
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  rename_i x y
  exact Quotient.sound ((sameCycle_ret x.2 y.2).2 ((sameCycle_rotPerm hrot).2 h))

/-- **The map without loops has no loop.** -/
theorem nlMap_loopless (x : SDart (nlDarts M)) : (nlMap M).head x ≠ (nlMap M).tail x :=
  fun h => mem_nlDarts.1 x.2 (congrArg (nlVert M) h)

variable (M) in
/-- A dart at every vertex of the map without loops. -/
noncomputable def nlE (w : SVert (nlRot M) (nlDarts M)) : SDart (nlDarts M) := w.out

lemma nlE_tail : ∀ w, (nlMap M).tail (nlE M w) = w := fun w => Quotient.out_eq w

/-- **Deleting the loops keeps the graph connected.** -/
lemma nl_conn (hM : M.IsPlane) (hrot : M.RotTrans) :
    ∀ x ∈ nlDarts M, ∀ y ∈ nlDarts M, Conn (revPerm M) (nlRot M) x y := by
  have hsame : ∀ {a b : D}, a ∈ nlDarts M → b ∈ nlDarts M → M.tail a = M.tail b →
      Conn (revPerm M) (nlRot M) a b := fun ha hb h =>
    conn_of_sameCycle ((sameCycle_ret ha hb).2 ((sameCycle_rotPerm hrot).2 h))
  have key : ∀ a b, ReflTransGen M.Adj a b → ∀ x ∈ nlDarts M, ∀ y ∈ nlDarts M,
      M.tail x = a → M.tail y = b → Conn (revPerm M) (nlRot M) x y := by
    intro a b h
    induction h with
    | refl => intro x hx y hy h1 h2; exact hsame hx hy (h1.trans h2.symm)
    | tail _ hst ih =>
      obtain ⟨e, he, rfl⟩ := hst
      intro x hx y hy h1 h2
      by_cases hl : e ∈ nlDarts M
      · refine (ih x hx e hl h1 he).trans ((conn_inv (ι := revPerm M) e).trans
          (hsame (stable_rev_nlDarts e hl) hy ?_))
        rw [revPerm_apply, tail_rev, h2]
      · have : M.head e = M.tail e := by simpa [mem_nlDarts] using hl
        exact ih x hx y hy h1 (by rw [h2, this, he])
  exact fun x hx y hy => key _ _ (hM.conn _ _) x hx y hy rfl rfl

/-- **The map without loops is plane**, when `M` is plane with transitive rotations and faces and
has a dart that is not a loop. -/
theorem nlMap_isPlane (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) : (nlMap M).IsPlane :=
  subMap_isPlane _ _ _ hx₀ (nl_conn hM hrot)
    (gap_ret_eq_zero (revPerm_isInv M) (fun _ _ => mem_univ _) (fun _ _ => mem_univ _)
      (subset_univ _) stable_rev_nlDarts (gap_rot_eq_zero hM hrot hface ⟨x₀⟩).2)

/-! ### Flows -/

/-- **The loops at a vertex carry no net flow.** -/
lemma div_eq_nl {g : D → ℤ} (hg : M.IsAntisymm g) (v : V) :
    M.div g v = ∑ x : SDart (nlDarts M) with M.tail x.1 = v, g x.1 := by
  unfold CombMap.div
  rw [← sum_filter_add_sum_filter_not _ (· ∈ nlDarts M)]
  have h0 : ∑ d ∈ (univ.filter fun d => M.tail d = v).filter (· ∉ nlDarts M), g d = 0 := by
    refine sum_involution (fun d _ => M.rev d) (fun d _ => by rw [hg]; ring)
      (fun d _ _ => M.rev_ne d) (fun d hd => ?_) (fun d _ => M.rev_rev d)
    simp only [mem_filter, mem_univ, true_and, mem_nlDarts, not_not] at hd ⊢
    simp only [head_rev, tail_rev]
    exact ⟨hd.2 ▸ hd.1, hd.2.symm⟩
  rw [h0, add_zero]
  symm
  refine sum_bij (fun x _ => x.1) (fun x hx => ?_) (fun a _ b _ h => Subtype.ext h)
    (fun d hd => ?_) (fun _ _ => rfl)
  · simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨hx, x.2⟩
  · simp only [mem_filter, mem_univ, true_and] at hd
    exact ⟨⟨d, hd.2⟩, by simpa using hd.1, rfl⟩

lemma div_nlMap (hrot : M.RotTrans) (g : SDart (nlDarts M) → ℤ) (w : SVert (nlRot M) (nlDarts M)) :
    (nlMap M).div g w = ∑ x : SDart (nlDarts M) with M.tail x.1 = nlVert M w, g x := by
  unfold CombMap.div
  refine sum_congr (filter_congr fun x _ => ?_) fun _ _ => rfl
  rw [← (nlVert_injective hrot).eq_iff]
  rfl

/-- The net outflow at a vertex of the map without loops is that of `M`. -/
lemma div_nlVert (hrot : M.RotTrans) {g : D → ℤ} (hg : M.IsAntisymm g)
    (w : SVert (nlRot M) (nlDarts M)) :
    M.div g (nlVert M w) = (nlMap M).div (fun x => g x.1) w := by
  rw [div_eq_nl hg, div_nlMap hrot]

/-- The net outflow at a vertex all of whose darts are loops is zero. -/
lemma div_eq_zero_of_nl {g : D → ℤ} (hg : M.IsAntisymm g) {v : V}
    (hv : ∀ w, nlVert M w ≠ v) : M.div g v = 0 := by
  rw [div_eq_nl hg]
  refine sum_eq_zero fun x hx => ?_
  simp only [mem_filter, mem_univ, true_and] at hx
  exact absurd hx (hv ((nlMap M).tail x))

variable (M) in
/-- The terminals of the map without loops: its vertices whose vertex of `M` is in `S`. -/
noncomputable def nlTerm (S : Finset V) : Finset (SVert (nlRot M) (nlDarts M)) :=
  univ.filter fun w => nlVert M w ∈ S

/-- The value of a flow is that of its restriction to the darts that are not loops. -/
lemma val_nl (hrot : M.RotTrans) {g : D → ℤ} (hg : M.IsAntisymm g) (S : Finset V) :
    val M S g = val (nlMap M) (nlTerm M S) (fun x => g x.1) := by
  unfold val
  have e : ∑ w ∈ nlTerm M S, (nlMap M).div (fun x => g x.1) w =
      ∑ v ∈ (nlTerm M S).image (nlVert M), M.div g v := by
    rw [sum_image fun a _ b _ h => nlVert_injective hrot h]
    exact sum_congr rfl fun w _ => (div_nlVert hrot hg w).symm
  rw [e]
  symm
  refine sum_subset (fun v hv => ?_) (fun v hv hv' => div_eq_zero_of_nl hg fun w hw => hv' ?_)
  · obtain ⟨w, hw, rfl⟩ := mem_image.1 hv
    simpa [nlTerm] using hw
  · exact mem_image.2 ⟨w, by simpa [nlTerm, hw] using hv, hw⟩

variable (M) in
/-- The flow of `M` of a flow of the map without loops: zero on the loops. -/
noncomputable def nlExt (f : SDart (nlDarts M) → ℤ) (d : D) : ℤ :=
  if h : d ∈ nlDarts M then f ⟨d, h⟩ else 0

/-- **A maximum flow of the map without loops, extended by zero on the loops, is a maximum flow
of `M`.** -/
theorem isMax_nlExt (hrot : M.RotTrans) {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V}
    {f : SDart (nlDarts M) → ℤ}
    (hf : IsMax (nlMap M) (fun x => u x.1) (nlTerm M S) (nlTerm M T) f) :
    IsMax M u S T (nlExt M f) := by
  have hr : (fun x : SDart (nlDarts M) => nlExt M f x.1) = f := funext fun x => by
    simp [nlExt, x.2]
  have hanti : M.IsAntisymm (nlExt M f) := fun d => by
    by_cases hd : d ∈ nlDarts M
    · have hd' := stable_rev_nlDarts d hd
      simp only [revPerm_apply] at hd'
      have := hf.1.antisymm ⟨d, hd⟩
      simp only [nlExt, hd, hd', dite_true]
      exact this
    · have hd' : M.rev d ∉ nlDarts M := fun h => hd (by
        have := stable_rev_nlDarts (M.rev d) h
        simpa [M.rev_rev] using this)
      simp [nlExt, hd, hd']
  -- the restriction of a flow of `M` is a flow of the map without loops
  have hres : ∀ g, IsFlow M u S T g →
      IsFlow (nlMap M) (fun x => u x.1) (nlTerm M S) (nlTerm M T) (fun x => g x.1) :=
    fun g hg => ⟨⟨fun x => hg.antisymm x.1, fun x => hg.le_cap x.1⟩, fun w hS hT => by
      rw [← div_nlVert hrot hg.antisymm]
      exact hg.conserve _ (fun h => hS (by simpa [nlTerm] using h))
        (fun h => hT (by simpa [nlTerm] using h))⟩
  refine ⟨⟨⟨hanti, fun d => ?_⟩, fun v hS hT => ?_⟩, fun g hg => ?_⟩
  · by_cases hd : d ∈ nlDarts M
    · simp only [nlExt, hd, dite_true]; exact hf.1.le_cap ⟨d, hd⟩
    · simp only [nlExt, hd, dite_false]; exact hu d
  · by_cases hv : ∃ w, nlVert M w = v
    · obtain ⟨w, rfl⟩ := hv
      rw [div_nlVert hrot hanti, hr]
      exact hf.1.conserve w (by simpa [nlTerm] using hS) (by simpa [nlTerm] using hT)
    · push Not at hv
      exact div_eq_zero_of_nl hanti hv
  · rw [val_nl hrot hg.antisymm, val_nl hrot hanti, hr]
    exact hf.2 _ (hres g hg)

/-! ### The cost, without the hypothesis on loops -/

variable (M) in
/-- **The preprocessed map without loops**: the preprocessed map (`preMap`: triangulation, then a
pendant edge at every vertex) of the map without loops `nlMap M`. -/
noncomputable abbrev lpreMap := preMap (M := nlMap M) nlMap_rotTrans (nlE_tail (M := M))

variable (M) in
/-- **The algorithm on the preprocessed map without loops**: `runL` on the decomposition `τ` of
`lpreMap M`, with the capacities and the terminals of the preprocessing, restricted to the darts
of `M` that are not loops and extended by zero on the loops. -/
noncomputable def nlRun (u : D → ℤ) (S T : Finset V) (τ : ADec (lpreMap M)) (O : PlaneOracles.{w}) :
    D → ℤ :=
  nlExt M fun x => runL (lpreMap M) (preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)) τ O
    (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) (.inl (old x))

lemma lg_le_of_le {m n : ℕ} (h : m ≤ n) (K K₀ C : ℕ) :
    (100000 + 11) ^ 2 * (C * K * (7 * m) * lg (7 * m) ^ 3 + K₀ * (7 * m) * lg (7 * m)) ≤
      (100000 + 11) ^ 2 * (C * K * (7 * n) * lg (7 * n) ^ 3 + K₀ * (7 * n) * lg (7 * n)) := by
  have hl := lg_mono (Nat.mul_le_mul_left 7 h)
  gcongr

/-- **Maximum flow at cost `O(n lg³ n)`, on every plane map with transitive rotations and faces,
loops allowed**: with `n` darts, nonnegative capacities and disjoint sources and sinks, there is
a decomposition `τ` of the preprocessed map without loops (`lpreMap M`) meeting `BalDecA` (with
`κ = 9`, `η = 6`, `s = 100000`) such that the algorithm on it (`nlRun`: `runL` on `lpreMap M`,
restricted to the darts of `M`, zero on the loops) is a maximum flow of `M`, and the cost of
`runL` for subroutine costs meeting `SubCosts.Bounds K K₀` is at most
`(s + 11)² ((27 Cₙ + 25) K (7 n) lg³ (7 n) + K₀ (7 n) lg (7 n))`,
`Cₙ = (η + 1) (25 + 7 κ² + 2 η (34 + 14 κ²))`. -/
theorem maxflow_cost (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {u : D → ℤ}
    (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) {O : PlaneOracles.{w}}
    (hO : O.Spec) {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    ∃ τ : ADec (lpreMap M),
      BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRun M u S T τ O) ∧
      runLCost (lpreMap M) c τ ≤ (100000 + 11) ^ 2 * ((27 * ((6 + 1) * (25 + 7 * 9 ^ 2 +
        2 * 6 * (34 + 14 * 9 ^ 2))) + 25) * K * (7 * Fintype.card D) *
          lg (7 * Fintype.card D) ^ 3 + K₀ * (7 * Fintype.card D) * lg (7 * Fintype.card D)) := by
  have hST' : Disjoint (nlTerm M S) (nlTerm M T) := by
    rw [disjoint_left]
    intro w h1 h2
    simp only [nlTerm, mem_filter, mem_univ, true_and] at h1 h2
    exact disjoint_left.1 hST h1 h2
  have hcard : Fintype.card (SDart (nlDarts M)) ≤ Fintype.card D := by
    rw [Fintype.card_coe]; exact card_le_univ _
  by_cases hB : (nlDarts M).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hB
    obtain ⟨τ, hτ, h1, h2⟩ := maxflow_pre_cost (nlMap_isPlane hM hrot hface hx₀) nlMap_rotTrans
      nlMap_faceTrans nlMap_loopless (u := fun x => u x.1) (fun x => hu x.1) hST' nlE_tail hO hc
    exact ⟨τ, hτ, isMax_nlExt hrot hu h1, h2.trans (lg_le_of_le hcard K K₀ _)⟩
  · -- every dart is a loop: the preprocessed map is empty
    rw [not_nonempty_iff_eq_empty] at hB
    have hD0 : Fintype.card (SDart (nlDarts M)) = 0 := by rw [Fintype.card_coe, hB]; rfl
    have : IsEmpty (SDart (nlDarts M)) := Fintype.card_eq_zero_iff.1 hD0
    have hV0 : Fintype.card (SVert (nlRot M) (nlDarts M)) = 0 :=
      le_zero_iff.1 (hD0 ▸ Fintype.card_le_of_surjective (nlMap M).tail
        fun w => ⟨nlE M w, nlE_tail w⟩)
    have hF0 : Fintype.card ((nlMap M).toSep nlMap_rotTrans).Face = 0 :=
      le_zero_iff.1 (hD0 ▸ Fintype.card_le_of_surjective _
        ((nlMap M).toSep nlMap_rotTrans).face_surjective)
    have hS0 : Fintype.card (PlanarSeparator.StDart (SDart (nlDarts M))) = 0 := by
      rw [card_triMap_darts, hD0]
    have hG0 : Fintype.card ((nlMap M).toSep nlMap_rotTrans).stellar.Face = 0 :=
      le_zero_iff.1 (hS0 ▸ Fintype.card_le_of_surjective _
        ((nlMap M).toSep nlMap_rotTrans).stellar.face_surjective)
    have hP0 : Fintype.card (PlanarSeparator.StDart (SDart (nlDarts M)) ⊕
        ((SVert (nlRot M) (nlDarts M) ⊕ ((nlMap M).toSep nlMap_rotTrans).Face) × Bool)) = 0 := by
      simp only [Fintype.card_sum, Fintype.card_prod, hS0, hV0, hF0, zero_add, zero_mul]
    have : IsEmpty (PlanarSeparator.StDart (SDart (nlDarts M)) ⊕
        ((SVert (nlRot M) (nlDarts M) ⊕ ((nlMap M).toSep nlMap_rotTrans).Face) × Bool)) :=
      Fintype.card_eq_zero_iff.1 hP0
    refine ⟨.leaf univ, ⟨rfl, fun d _ => mem_univ _, fun x => isEmptyElim x,
      Or.inl (by rw [card_univ, hP0]; omega), trivial⟩,
      isMax_nlExt hrot hu (isMax_of_isEmpty _ _ _ _), ?_⟩
    have hmap : mapSize (lpreMap M) = 0 := by
      unfold mapSize
      simp only [Fintype.card_sum, hP0, hV0, hF0, hG0]
    have h1 := hc.leaf (pdarts (lpreMap M) univ []).card
    have h2 := hc.lin 0
    have h3 : (pdarts (lpreMap M) univ []).card = 0 :=
      le_zero_iff.1 ((card_le_univ _).trans hP0.le)
    unfold runLCost arunLCost
    rw [h3] at h1
    rw [h3, hmap, card_univ, hP0]
    simp only [List.length_nil, add_zero, mul_zero] at h1 h2 ⊢
    omega

end Loops

/-! ### A map with a loop -/

/-- **A plane map with one vertex and one loop**: two darts, one vertex, two faces. -/
def loopMap : CombMap Bool Unit Bool where
  rev := not
  rev_rev := Bool.not_not
  rev_ne d := by cases d <;> decide
  tail _ := ()
  face := id
  next := id
  next_injective := injective_id
  face_next _ := rfl
  tail_next _ := rfl

/-- **The hypotheses of `maxflow_cost` can be met by a map with a loop**: `loopMap` is plane,
with transitive rotations and faces, and its darts are loops. -/
theorem loopMap_hyps : loopMap.IsPlane ∧ loopMap.RotTrans ∧ loopMap.FaceTrans ∧
    ∀ d, loopMap.head d = loopMap.tail d := by
  refine ⟨⟨⟨()⟩, fun _ _ => .refl, fun x y => ?_, rfl⟩, fun d d' _ => ?_, fun d d' h => ⟨0, h⟩,
    fun _ => rfl⟩
  · by_cases h : x = y
    · rw [h]
    · exact .single ⟨x, rfl, by cases x <;> cases y <;> simp_all [loopMap]⟩
  · by_cases h : d = d'
    · exact ⟨0, h⟩
    · exact ⟨1, by cases d <;> cases d' <;> simp_all [loopMap, CombMap.rot]⟩

end BKMNW

end PlanarFlow
