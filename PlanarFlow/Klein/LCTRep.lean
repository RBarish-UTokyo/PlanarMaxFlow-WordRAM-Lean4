module

public import PlanarFlow.Klein.Values
public import PlanarFlow.DynTree.Forest
public import PlanarFlow.DynTree.Access

/-!
# A tree of a map stored in the forest of the dynamic trees

The data of Klein's algorithm are two trees of a map: the spanning tree `T` of the primal graph
(a `PlanarFlow.STFlow.DTree` of the dual map, on the vertices) and the dual cotree (a `DTree` of
the map, on the faces). Both are stored in the forest of the dynamic trees
(`PlanarFlow.DynTree.Forest`, on the nodes `0, …, n-1`) in the same way: a node `ιf y` for
every face `y` of the tree, and a node `ιe d` for every edge (shared by the two darts `d` and
`rev d`), subdivided: the parent of the node of a face `y` other than the root is the node of
the edge of its parent dart `C.par y`, whose parent is the node of the parent face. The first
value of the node of an edge is the value `κ` of its dart towards the root, the second value
that of its dart away from the root (the dart semantics of Goldberg, Grigoriadis and Tarjan,
under which `evert` exchanges the two values on the reversed path).

* `TRep`: this representation, with values `β`, `β₂` at the nodes of the faces.
* `rootPath_rep`: **the root path of the node of a face** alternates the nodes of the faces on
  the path to the root and the nodes of the edges of their parent darts (`tpath`).
* `pathSum_rep`: the path sum at the node of a face is the sum of the values `κ` of the darts
  towards the root (with `β = 0`): the path sum `C.psum` of the tree, for `κ ∘ rev = φ`.
* `pathMin2_rep`: **the least second value on the root path**: if it is below every value `β₂`,
  it is the value `κ (C.par z)` of the parent dart of a face `z ≠ root` on the path (a dart away
  from the root), the node attaining it is the node of the edge of that dart, and the value is
  at most the values `κ` of all the parent darts on the path.
* `treeForest_rep`, `exists_trep`: **every tree can be stored** (the forest `treeForest`, for
  node maps meeting `Nodes`, such as `faceNode`, `edgeNode` on `#Y + #D` nodes).
* `chi_eq_pflow`, `chi_eq_one_iff`: when the parent darts of a tree `C` of the map are off a
  spanning tree `T` of the dual map, **the path of the cotree of `T` from the root of `C` to `x`
  (`T.chi`) is the path of `C`**: its darts of value `1` are the parent darts on the path from
  `x` to the root.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap STFlow DynTree

variable {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype Y] [DecidableEq Y]
variable {N : CombMap D X Y}

/-! ### Lists -/

lemma lmin_spec : ∀ {l : List (ℕ × ℝ)}, l ≠ [] →
    ((lmin l).2, (lmin l).1) ∈ l ∧ ∀ p ∈ l, (lmin l).1 ≤ p.2
  | [], h => absurd rfl h
  | [p], _ => by simp [lmin]
  | p :: q :: ps, _ => by
    obtain ⟨h1, h2⟩ := lmin_spec (l := q :: ps) (by simp)
    rw [lmin_cons]
    split_ifs with h
    · refine ⟨List.mem_cons_of_mem _ h1, fun r hr => ?_⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · exact h.le
      · exact h2 r hr
    · push Not at h
      refine ⟨by simp, fun r hr => ?_⟩
      rcases List.mem_cons.1 hr with rfl | hr
      · exact le_rfl
      · exact h.trans (h2 r hr)

/-! ### The representation -/

variable (n : ℕ) (Fo : Forest) (C : DTree N) (ιf : Y → ℕ) (ιe : D → ℕ)

/-- **A tree of the map stored in the forest**, subdivided by the nodes of the edges, with the
values `κ` of the darts on the nodes of the edges and `β`, `β₂` on the nodes of the faces. -/
structure TRep (κ : D → ℝ) (β β₂ : Y → ℝ) : Prop where
  pf : ∀ y, y ≠ C.root → Fo.par (ιf y) = ιe (C.par y)
  pr : Fo.par (ιf C.root) = n
  pe : ∀ y, y ≠ C.root → Fo.par (ιe (C.par y)) = ιf (N.face (C.par y))
  ve : ∀ y, y ≠ C.root → Fo.val (ιe (C.par y)) = κ (N.rev (C.par y))
  ve2 : ∀ y, y ≠ C.root → Fo.val2 (ιe (C.par y)) = κ (C.par y)
  vf : ∀ y, Fo.val (ιf y) = β y
  vf2 : ∀ y, Fo.val2 (ιf y) = β₂ y

/-- The path from the node of `y` towards the root in `k` steps of the tree. -/
def tpath : ℕ → Y → List ℕ
  | 0, y => [ιf y]
  | k + 1, y => ιf y :: ιe (C.par y) :: tpath k (C.up y)

variable {n Fo C ιf ιe} {κ : D → ℝ} {β β₂ : Y → ℝ}

lemma tpath_ne_nil (k : ℕ) (y : Y) : tpath C ιf ιe k y ≠ [] := by
  cases k <;> simp [tpath]

/-- **The root path of the node of a face** in the forest. -/
theorem upPath_rep (hR : TRep n Fo C ιf ιe κ β β₂) (hf : ∀ y, ιf y < n) (he : ∀ d, ιe d < n) :
    ∀ (k : ℕ) (y : Y), C.depth y = k → ∀ fuel, 2 * k + 1 ≤ fuel →
      upPath Fo n fuel (ιf y) = tpath C ιf ιe k y := by
  intro k
  induction k with
  | zero =>
    intro y hy fuel hfuel
    have hyr : y = C.root := by
      have := C.iterate_depth y; rw [hy] at this; exact this
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [upPath, hf y, ↓reduceIte, tpath]
    rw [hyr, hR.pr, upPath_nil]
  | succ k ih =>
    intro y hy fuel hfuel
    have hyr : y ≠ C.root := by
      intro h; rw [h, C.depth_root] at hy; omega
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 2 := ⟨fuel - 2, by omega⟩
    simp only [upPath, hf y, ↓reduceIte, hR.pf y hyr, he, hR.pe y hyr, tpath]
    rw [← C.up_of_ne hyr]
    refine congrArg _ (congrArg _ (ih _ ?_ _ (by omega)))
    rw [C.depth_up hyr] at hy; omega

/-- **The root path of the node of a face** is `tpath`, when the forest has at least twice as
many nodes as the tree has faces. -/
theorem rootPath_rep (hR : TRep n Fo C ιf ιe κ β β₂) (hf : ∀ y, ιf y < n) (he : ∀ d, ιe d < n)
    (hn : 2 * Fintype.card Y ≤ n) (y : Y) :
    rootPath Fo n (ιf y) = tpath C ιf ιe (C.depth y) y :=
  upPath_rep hR hf he _ y rfl n (by have := C.depth_lt_card y; omega)

/-- **The path sum at the node of a face** is the path sum of the tree for the values of the
darts towards the root (integer values, `β = 0`). -/
theorem pathSum_rep (hR : TRep n Fo C ιf ιe κ β β₂) (hf : ∀ y, ιf y < n) (he : ∀ d, ιe d < n)
    (hn : 2 * Fintype.card Y ≤ n) (hβ : ∀ y, β y = 0) {φ : D → ℤ}
    (hκ : ∀ d, κ (N.rev d) = φ d) (y : Y) :
    pathSum Fo n (ιf y) = C.psum φ y := by
  unfold pathSum
  rw [rootPath_rep hR hf he hn]
  suffices ∀ (k : ℕ) (y : Y), C.depth y = k →
      ((tpath C ιf ιe k y).map Fo.val).sum = C.psum φ y from this _ y rfl
  intro k
  induction k with
  | zero =>
    intro y hy
    have hyr : y = C.root := by
      have := C.iterate_depth y; rw [hy] at this; exact this
    simp [tpath, hR.vf, hβ, hyr, C.psum_root]
  | succ k ih =>
    intro y hy
    have hyr : y ≠ C.root := by
      intro h; rw [h, C.depth_root] at hy; omega
    simp only [tpath, List.map_cons, List.sum_cons, hR.vf, hβ, hR.ve y hyr, hκ]
    rw [ih _ (by rw [C.depth_up hyr] at hy; omega), C.psum_of_ne φ hyr]
    push_cast; ring

/-- The pairs of the second values along `tpath`. -/
lemma mem_tpath_val2 (hR : TRep n Fo C ιf ιe κ β β₂) :
    ∀ (k : ℕ) (y : Y), k ≤ C.depth y → ∀ q ∈ (tpath C ιf ιe k y).map fun u => (u, Fo.val2 u),
      (∃ i ≤ k, q = (ιf (C.up^[i] y), β₂ (C.up^[i] y))) ∨
        ∃ i < k, C.up^[i] y ≠ C.root ∧
          q = (ιe (C.par (C.up^[i] y)), κ (C.par (C.up^[i] y))) := by
  intro k
  induction k with
  | zero =>
    intro y _ q hq
    simp only [tpath, List.map_cons, List.map_nil, List.mem_singleton] at hq
    exact Or.inl ⟨0, le_rfl, by simp [hq, hR.vf2]⟩
  | succ k ih =>
    intro y hk q hq
    have hyr : y ≠ C.root := by
      intro h; rw [h, C.depth_root] at hk; omega
    simp only [tpath, List.map_cons, List.mem_cons] at hq
    rcases hq with rfl | rfl | hq
    · exact Or.inl ⟨0, by omega, by simp [hR.vf2]⟩
    · exact Or.inr ⟨0, by omega, hyr, by simp [hR.ve2 y hyr]⟩
    · rcases ih (C.up y) (by rw [C.depth_up hyr] at hk; omega) q hq with
        ⟨i, hi, rfl⟩ | ⟨i, hi, hne, rfl⟩
      · exact Or.inl ⟨i + 1, by omega, by rw [Function.iterate_succ_apply]⟩
      · exact Or.inr ⟨i + 1, by omega, by rwa [Function.iterate_succ_apply],
          by rw [Function.iterate_succ_apply]⟩

/-- The parent darts along `tpath` have their pairs in it. -/
lemma val2_mem_tpath (hR : TRep n Fo C ιf ιe κ β β₂) :
    ∀ (k : ℕ) (y : Y), k ≤ C.depth y → ∀ i < k,
      (ιe (C.par (C.up^[i] y)), κ (C.par (C.up^[i] y))) ∈
        (tpath C ιf ιe k y).map fun u => (u, Fo.val2 u) := by
  intro k
  induction k with
  | zero => intro y _ i hi; omega
  | succ k ih =>
    intro y hk i hi
    have hyr : y ≠ C.root := by
      intro h; rw [h, C.depth_root] at hk; omega
    simp only [tpath, List.map_cons, List.mem_cons]
    rcases i with _ | i
    · right; left; simp [hR.ve2 y hyr]
    · right; right
      have := ih (C.up y) (by rw [C.depth_up hyr] at hk; omega) i (by omega)
      rwa [Function.iterate_succ_apply]

/-- **The least second value on the root path of the node of a face**: when it is below every
value `β₂`, it is the value of a parent dart `C.par z` on the path to the root (a dart away from
the root, `z ≠ root`), it is attained at the node of the edge of that dart, and it is at most the
values of all the parent darts on the path. -/
theorem pathMin2_rep (hR : TRep n Fo C ιf ιe κ β β₂) (hf : ∀ y, ιf y < n) (he : ∀ d, ιe d < n)
    (hn : 2 * Fintype.card Y ≤ n) (y : Y) (hlow : ∀ z, (pathMin2 Fo n (ιf y)).1 < β₂ z) :
    ∃ i < C.depth y, C.up^[i] y ≠ C.root ∧
      (pathMin2 Fo n (ιf y)).2 = ιe (C.par (C.up^[i] y)) ∧
      (pathMin2 Fo n (ιf y)).1 = κ (C.par (C.up^[i] y)) ∧
      ∀ j < C.depth y, (pathMin2 Fo n (ιf y)).1 ≤ κ (C.par (C.up^[j] y)) := by
  unfold pathMin2 downVals2 at hlow ⊢
  rw [rootPath_rep hR hf he hn] at hlow ⊢
  have hne : ((tpath C ιf ιe (C.depth y) y).reverse.map fun u => (u, Fo.val2 u)) ≠ [] := by
    simp [tpath_ne_nil]
  obtain ⟨h1, h2⟩ := lmin_spec hne
  have key : ∀ q, q ∈ (tpath C ιf ιe (C.depth y) y).reverse.map (fun u => (u, Fo.val2 u)) ↔
      q ∈ (tpath C ιf ιe (C.depth y) y).map (fun u => (u, Fo.val2 u)) := by
    intro q; simp only [List.mem_map, List.mem_reverse]
  rcases mem_tpath_val2 hR _ y le_rfl _ ((key _).1 h1) with ⟨i, hi, hq⟩ | ⟨i, hi, hir, hq⟩
  · exfalso
    have := congrArg Prod.snd hq
    simp only at this
    exact absurd (hlow (C.up^[i] y)) (by rw [this]; exact lt_irrefl _)
  · refine ⟨i, hi, hir, (congrArg Prod.fst hq), (congrArg Prod.snd hq), fun j hj => ?_⟩
    exact h2 _ ((key _).2 (val2_mem_tpath hR _ y le_rfl j hj))

/-- The second values on the root path are at least the least one. -/
theorem pathMin2_le (hR : TRep n Fo C ιf ιe κ β β₂) (hf : ∀ y, ιf y < n) (he : ∀ d, ιe d < n)
    (hn : 2 * Fintype.card Y ≤ n) (y : Y) :
    ∀ j < C.depth y, (pathMin2 Fo n (ιf y)).1 ≤ κ (C.par (C.up^[j] y)) := by
  intro j hj
  unfold pathMin2 downVals2
  rw [rootPath_rep hR hf he hn]
  have hne : ((tpath C ιf ιe (C.depth y) y).reverse.map fun u => (u, Fo.val2 u)) ≠ [] := by
    simp [tpath_ne_nil]
  obtain ⟨-, h2⟩ := lmin_spec hne
  have key : ∀ q, q ∈ (tpath C ιf ιe (C.depth y) y).reverse.map (fun u => (u, Fo.val2 u)) ↔
      q ∈ (tpath C ιf ιe (C.depth y) y).map (fun u => (u, Fo.val2 u)) := by
    intro q; simp only [List.mem_map, List.mem_reverse]
  exact h2 _ ((key _).2 (val2_mem_tpath hR _ y le_rfl j hj))

/-! ### A forest storing a given tree -/

section Build

variable (n) in
/-- **Node maps**: injective on the faces, one node per edge (shared by a dart and its
reverse), the faces and the edges on different nodes, all below `n`. -/
structure Nodes (N : CombMap D X Y) (ιf : Y → ℕ) (ιe : D → ℕ) : Prop where
  f_inj : Function.Injective ιf
  e_rev : ∀ d, ιe (N.rev d) = ιe d
  e_eq : ∀ d d', ιe d = ιe d' → d' = d ∨ d' = N.rev d
  fe : ∀ y d, ιf y ≠ ιe d
  f_lt : ∀ y, ιf y < n
  e_lt : ∀ d, ιe d < n

/-- The parent darts of a tree are distinct, and none is the reverse of another. -/
lemma _root_.PlanarFlow.STFlow.DTree.par_eq_or (C : DTree N) {y y' : Y} (hy : y ≠ C.root)
    (hy' : y' ≠ C.root)
    (h : C.par y' = C.par y ∨ C.par y' = N.rev (C.par y)) : y' = y := by
  rcases h with h | h
  · rw [← C.head_par y hy, ← C.head_par y' hy', h]
  · exfalso
    have e1 : y' = C.up y := by
      rw [← C.head_par y' hy', h, N.rev_rev, C.up_of_ne hy]
    have e2 : y = C.up y' := by
      rw [← C.head_par y hy, C.up_of_ne hy', h]
    have d1 := C.depth_up hy
    have d2 := C.depth_up hy'
    rw [← e1] at d1
    rw [← e2] at d2
    omega

open Classical in
variable (n) in
/-- **The forest storing a tree** `C`, with the values `κ` of the darts and `β`, `β₂` at the
nodes of the faces (every other node isolated, with value `0`). -/
noncomputable def treeForest (C : DTree N) (ιf : Y → ℕ) (ιe : D → ℕ) (κ : D → ℝ)
    (β β₂ : Y → ℝ) : Forest where
  par u :=
    if h : ∃ y, y ≠ C.root ∧ ιf y = u then ιe (C.par h.choose)
    else if h' : ∃ y, y ≠ C.root ∧ ιe (C.par y) = u then ιf (N.face (C.par h'.choose))
    else n
  val u :=
    if h : ∃ y, ιf y = u then β h.choose
    else if h' : ∃ y, y ≠ C.root ∧ ιe (C.par y) = u then κ (N.rev (C.par h'.choose))
    else 0
  val2 u :=
    if h : ∃ y, ιf y = u then β₂ h.choose
    else if h' : ∃ y, y ≠ C.root ∧ ιe (C.par y) = u then κ (C.par h'.choose)
    else 0

/-- **Every tree is stored in its forest** (`treeForest`, for node maps meeting `Nodes`). -/
theorem treeForest_rep (C : DTree N) {ιf : Y → ℕ} {ιe : D → ℕ} (hN : Nodes n N ιf ιe)
    (κ : D → ℝ) (β β₂ : Y → ℝ) :
    TRep n (treeForest n C ιf ιe κ β β₂) C ιf ιe κ β β₂ := by
  classical
  -- the node of a face determines the face
  have hF : ∀ y, ∀ h : ∃ y', ιf y' = ιf y, h.choose = y := fun y h =>
    hN.f_inj h.choose_spec
  have hF' : ∀ y, ∀ h : ∃ y', y' ≠ C.root ∧ ιf y' = ιf y, h.choose = y := fun y h =>
    hN.f_inj h.choose_spec.2
  -- the node of the edge of a parent dart determines the face
  have hE : ∀ y, y ≠ C.root → ∀ h : ∃ y', y' ≠ C.root ∧ ιe (C.par y') = ιe (C.par y),
      h.choose = y := fun y hy h =>
    C.par_eq_or hy h.choose_spec.1 (hN.e_eq _ _ h.choose_spec.2.symm)
  have hnf : ∀ y, ¬ ∃ y', y' ≠ C.root ∧ ιf y' = ιe (C.par y) := fun y ⟨y', _, h⟩ =>
    hN.fe y' _ h
  have hnf' : ∀ y, ¬ ∃ y', ιf y' = ιe (C.par y) := fun y ⟨y', h⟩ => hN.fe y' _ h
  have hne : ∀ y, ¬ ∃ y', y' ≠ C.root ∧ ιe (C.par y') = ιf y := fun y ⟨y', _, h⟩ =>
    hN.fe y _ h.symm
  refine ⟨fun y hy => ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y => ?_,
    fun y => ?_⟩
  · have h : ∃ y', y' ≠ C.root ∧ ιf y' = ιf y := ⟨y, hy, rfl⟩
    simp only [treeForest, h, ↓reduceDIte, hF' y h]
  · have h : ¬ ∃ y', y' ≠ C.root ∧ ιf y' = ιf C.root := fun ⟨y', hy', e⟩ =>
      hy' (hN.f_inj e)
    simp only [treeForest, h, ↓reduceDIte, hne]
  · have h : ∃ y', y' ≠ C.root ∧ ιe (C.par y') = ιe (C.par y) := ⟨y, hy, rfl⟩
    simp only [treeForest, hnf, ↓reduceDIte, h, hE y hy h]
  · have h : ∃ y', y' ≠ C.root ∧ ιe (C.par y') = ιe (C.par y) := ⟨y, hy, rfl⟩
    simp only [treeForest, hnf', ↓reduceDIte, h, hE y hy h]
  · have h : ∃ y', y' ≠ C.root ∧ ιe (C.par y') = ιe (C.par y) := ⟨y, hy, rfl⟩
    simp only [treeForest, hnf', ↓reduceDIte, h, hE y hy h]
  · have h : ∃ y', ιf y' = ιf y := ⟨y, rfl⟩
    simp only [treeForest, h, ↓reduceDIte, hF y h]
  · have h : ∃ y', ιf y' = ιf y := ⟨y, rfl⟩
    simp only [treeForest, h, ↓reduceDIte, hF y h]

/-- The node maps of the faces and the edges: the faces first, then one node for each dart,
the edge using the node of its dart of least index. -/
noncomputable def faceNode (y : Y) : ℕ := Fintype.equivFin Y y

noncomputable def edgeNode (N : CombMap D X Y) (d : D) : ℕ :=
  Fintype.card Y + min (Fintype.equivFin D d : ℕ) (Fintype.equivFin D (N.rev d))

/-- **The node maps meet `Nodes`** on `#Y + #D` nodes. -/
theorem nodes_std : Nodes (Fintype.card Y + Fintype.card D) N faceNode (edgeNode N) where
  f_inj a b h := (Fintype.equivFin Y).injective (Fin.ext h)
  e_rev d := by unfold edgeNode; rw [N.rev_rev, min_comm]
  e_eq d d' h := by
    unfold edgeNode at h
    have hinj : ∀ a b : D, (Fintype.equivFin D a : ℕ) = Fintype.equivFin D b → a = b :=
      fun a b h => (Fintype.equivFin D).injective (Fin.ext h)
    have h' : min (Fintype.equivFin D d : ℕ) (Fintype.equivFin D (N.rev d)) =
        min (Fintype.equivFin D d' : ℕ) (Fintype.equivFin D (N.rev d')) := by omega
    rcases min_choice (Fintype.equivFin D d : ℕ) (Fintype.equivFin D (N.rev d)) with h1 | h1 <;>
      rcases min_choice (Fintype.equivFin D d' : ℕ) (Fintype.equivFin D (N.rev d')) with
        h2 | h2 <;> rw [h1, h2] at h'
    · exact Or.inl (hinj _ _ h').symm
    · right; have := hinj _ _ h'; rw [this, N.rev_rev]
    · right; exact (hinj _ _ h').symm
    · left; have := hinj _ _ h'
      rw [← N.rev_rev d, this, N.rev_rev]
  fe y d := by
    unfold faceNode edgeNode
    have := (Fintype.equivFin Y y).isLt
    omega
  f_lt y := by
    unfold faceNode
    have := (Fintype.equivFin Y y).isLt
    omega
  e_lt d := by
    unfold edgeNode
    have := (Fintype.equivFin D d).isLt
    omega

/-- **Every tree can be stored** in a forest on `#Y + #D` nodes (a witness that the hypothesis
`TRep` of the queries can be met). -/
theorem exists_trep (C : DTree N) (κ : D → ℝ) (β β₂ : Y → ℝ) :
    ∃ Fo : Forest, TRep (Fintype.card Y + Fintype.card D) Fo C faceNode (edgeNode N) κ β β₂ :=
  ⟨_, treeForest_rep C nodes_std κ β β₂⟩

end Build

/-! ### The path of the tree is the path of the cotree -/

section Flow

variable {V F : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-- The iterates of the parent map are distinct up to the root. -/
lemma _root_.PlanarFlow.STFlow.DTree.iterate_inj (C : DTree M) {x : F} {i j : ℕ}
    (hi : i ≤ C.depth x) (hj : j ≤ C.depth x) (h : C.up^[i] x = C.up^[j] x) : i = j := by
  by_contra hne
  wlog hlt : i < j generalizing i j
  · exact this hj hi h.symm (Ne.symm hne) (by omega)
  have : C.up^[C.depth x - j + i] x = C.root := by
    rw [Function.iterate_add_apply, h, ← Function.iterate_add_apply, Nat.sub_add_cancel hj,
      C.iterate_depth]
  exact C.iterate_ne_root (show C.depth x - j + i < C.depth x by omega) this

/-- **The unit flow along the path of a tree** from its root to `x`. -/
def pflow (C : DTree M) (x : F) (d : D) : ℤ :=
  ∑ i ∈ range (C.depth x), ((if d = C.par (C.up^[i] x) then 1 else 0) -
    (if d = M.rev (C.par (C.up^[i] x)) then 1 else 0))

lemma pflow_of_ne (C : DTree M) {x : F} (hx : x ≠ C.root) (d : D) :
    pflow C x d = pflow C (C.up x) d + ((if d = C.par x then 1 else 0) -
      (if d = M.rev (C.par x) then 1 else 0)) := by
  unfold pflow
  rw [C.depth_up hx, sum_range_succ']
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rfl

lemma pflow_antisymm (C : DTree M) (x : F) : M.dual.IsAntisymm (pflow C x) := by
  intro d
  change pflow C x (M.rev d) = _
  unfold pflow
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  have h1 : ∀ p, M.rev d = p ↔ d = M.rev p := fun p =>
    ⟨fun h => by rw [← h, M.rev_rev], fun h => by rw [h, M.rev_rev]⟩
  simp only [h1, M.rev_rev]
  split_ifs <;> ring

lemma div_pflowT (C : DTree M) (x f : F) :
    M.dual.div (pflow C x) f = (if C.root = f then 1 else 0) - (if x = f then 1 else 0) := by
  generalize hk : C.depth x = k
  induction k generalizing x with
  | zero =>
    have hx : x = C.root := by have := C.iterate_depth x; rw [hk] at this; exact this
    have h0 : pflow C x = 0 := by funext d; simp [pflow, hk]
    rw [h0, hx]
    simp [CombMap.div]
  | succ k ih =>
    have hx : x ≠ C.root := by intro h; rw [h, C.depth_root] at hk; omega
    have e : pflow C x = fun d => pflow C (C.up x) d + ((if d = C.par x then 1 else 0) -
        (if d = M.rev (C.par x) then 1 else 0)) := funext (pflow_of_ne C hx)
    have ih' := ih (C.up x) (by rw [C.depth_up hx] at hk; omega)
    unfold CombMap.div at ih' ⊢
    rw [e, sum_add_distrib, ih', sum_sub_distrib]
    change _ + (∑ d with M.face d = f, _ - ∑ d with M.face d = f, _) = _
    rw [sum_ite_eq', sum_ite_eq']
    simp only [mem_filter, mem_univ, true_and]
    rw [← C.up_of_ne hx, C.head_par x hx]
    split_ifs <;> ring

lemma pflow_offT {T : DTree M.dual} {C : DTree M} (hoff : ∀ y, y ≠ C.root → ¬ T.InT (C.par y))
    (x : F) : T.OffT (pflow C x) := by
  intro d hd
  unfold pflow
  refine sum_eq_zero fun i hi => ?_
  have hne : C.up^[i] x ≠ C.root := C.iterate_ne_root (mem_range.1 hi)
  have h1 : d ≠ C.par (C.up^[i] x) := fun h => hoff _ hne (h ▸ hd)
  have h2 : d ≠ M.rev (C.par (C.up^[i] x)) := fun h => by
    have := T.inT_rev hd
    rw [h] at this
    exact hoff _ hne (by simpa [CombMap.dual, M.rev_rev] using this)
  simp [h1, h2]

/-- **The path of the cotree from the root of `C` to `x` is the path of `C`**, when the parent
darts of `C` are off the tree `T`. -/
theorem chi_eq_pflow (hM : M.IsPlane) (T : DTree M.dual) (C : DTree M)
    (hoff : ∀ y, y ≠ C.root → ¬ T.InT (C.par y)) (x : F) :
    T.chi C.root x = pflow C x := by
  obtain ⟨h1, h2, h3, -⟩ := T.chi_spec hM.dual C.root x
  funext d
  have hc : M.dual.IsCirc (T.chi C.root x - pflow C x) := by
    refine ⟨fun d => ?_, fun v => ?_⟩
    · simp only [Pi.sub_apply, h1 d, pflow_antisymm C x d]; ring
    · have e : M.dual.div (T.chi C.root x - pflow C x) v =
          M.dual.div (T.chi C.root x) v - M.dual.div (pflow C x) v := by
        unfold CombMap.div; rw [← sum_sub_distrib]; rfl
      rw [e, h2 v, div_pflowT]; ring
  have := T.circ_eq_zero hM.dual hc (fun d hd => by
    simp [h3 d hd, pflow_offT hoff x d hd]) d
  simp only [Pi.sub_apply] at this
  linarith

/-- **The darts of value `1` on the path of the cotree** from the root of `C` to `x` are the
parent darts of `C` on the path from `x` to the root. -/
theorem chi_eq_one_iff (hM : M.IsPlane) (T : DTree M.dual) (C : DTree M)
    (hoff : ∀ y, y ≠ C.root → ¬ T.InT (C.par y)) (x : F) (d : D) :
    T.chi C.root x d = 1 ↔ ∃ i < C.depth x, d = C.par (C.up^[i] x) := by
  rw [chi_eq_pflow hM T C hoff]
  -- the parent darts of the path are distinct, and none is the reverse of another
  have hpar : ∀ i j, i < C.depth x → j < C.depth x →
      C.par (C.up^[i] x) = C.par (C.up^[j] x) → i = j := by
    intro i j hi hj h
    have := congrArg (fun d => M.face (M.rev d)) h
    simp only [C.head_par _ (C.iterate_ne_root hi), C.head_par _ (C.iterate_ne_root hj)] at this
    exact C.iterate_inj hi.le hj.le this
  have hrev : ∀ i j, i < C.depth x → j < C.depth x →
      C.par (C.up^[i] x) ≠ M.rev (C.par (C.up^[j] x)) := by
    intro i j hi hj h
    have e1 := congrArg (fun d => M.face (M.rev d)) h
    have e2 := congrArg M.face h
    simp only [M.rev_rev, C.head_par _ (C.iterate_ne_root hi)] at e1
    simp only [C.head_par _ (C.iterate_ne_root hj)] at e2
    rw [← C.up_of_ne (C.iterate_ne_root hj), ← Function.iterate_succ_apply' C.up j x] at e1
    rw [← C.up_of_ne (C.iterate_ne_root hi), ← Function.iterate_succ_apply' C.up i x] at e2
    have := C.iterate_inj hi.le (show j + 1 ≤ C.depth x by omega) e1
    have := C.iterate_inj (show i + 1 ≤ C.depth x by omega) hj.le e2
    omega
  constructor
  · intro h
    by_contra hno
    push Not at hno
    have : pflow C x d ≤ 0 := by
      unfold pflow
      refine sum_nonpos fun i hi => ?_
      simp only [hno i (mem_range.1 hi), ↓reduceIte]
      split_ifs <;> norm_num
    omega
  · rintro ⟨i, hi, rfl⟩
    unfold pflow
    rw [sum_eq_single i]
    · simp [hrev i i hi hi]
    · intro j hj hji
      have e1 : C.par (C.up^[i] x) ≠ C.par (C.up^[j] x) :=
        fun h => hji (hpar _ _ hi (mem_range.1 hj) h).symm
      simp [e1, hrev _ _ hi (mem_range.1 hj)]
    · intro h; exact absurd (mem_range.2 hi) h

end Flow

end Klein

end PlanarFlow
