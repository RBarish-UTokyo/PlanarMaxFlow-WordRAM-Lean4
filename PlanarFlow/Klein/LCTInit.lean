module

public import PlanarFlow.Klein.LCTMove

/-!
# Storing the trees from the empty forest

* `setOps_run`: `add` and `add2` at distinct roots set their values.
* `linkOps_run`: linking the faces of a tree one after the other, in an order of nondecreasing
  depth (each face below the edge of its parent dart, below the node of its parent face), is
  valid and stores the parent structure of the tree.
* `build_trep`: **storing a tree** with integer values in a forest in which its nodes are
  isolated roots of value `0`: at most `6 #Y` valid operations.
* `init_stored`: **the initial stored data of a move** (`Stored`) from the empty forest
  (`Forest.init`): the cotree, then the spanning tree, with at most `6 (#V + #F)` operations.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap STFlow DynTree

/-! ### Setting the values of roots -/

/-- `add` and `add2` at every node of the list. -/
def setOps (L : List (ℕ × ℤ × ℤ)) : List EOp :=
  L.flatMap fun t => [.add t.1 t.2.1, .add2 t.1 t.2.2]

lemma setOps_length (L : List (ℕ × ℤ × ℤ)) : (setOps L).length = 2 * L.length := by
  induction L with
  | nil => rfl
  | cons t L ih => simp only [setOps, List.flatMap_cons, List.length_append] at ih ⊢; simp; omega

/-- **Setting the values of roots.** -/
lemma setOps_run {n : ℕ} : ∀ (L : List (ℕ × ℤ × ℤ)) (Fo : Forest),
    (∀ t ∈ L, t.1 < n ∧ Fo.par t.1 = n) →
    ValidOpsE n Fo (setOps L) ∧ (runOpsE n Fo (setOps L)).2 = [] ∧
      (runOpsE n Fo (setOps L)).1.par = Fo.par ∧
      ∀ u, (runOpsE n Fo (setOps L)).1.val u =
          Fo.val u + (L.map fun t => if t.1 = u then (t.2.1 : ℝ) else 0).sum ∧
        (runOpsE n Fo (setOps L)).1.val2 u =
          Fo.val2 u + (L.map fun t => if t.1 = u then (t.2.2 : ℝ) else 0).sum
  | [], Fo, _ => by simp [setOps, runOpsE, ValidOpsE]
  | t :: L, Fo, h => by
    obtain ⟨ht, hp⟩ := h t (by simp)
    set F1 := addPath2 (addPath Fo n t.1 t.2.1) n t.1 t.2.2 with hF1
    have hrp : rootPath Fo n t.1 = [t.1] := rootPath_root ht hp
    have hrp' : rootPath (addPath Fo n t.1 t.2.1) n t.1 = [t.1] := by
      rw [rootPath_congr (Fo := Fo) (Fo' := addPath Fo n t.1 t.2.1) rfl]; exact hrp
    have hF1v : ∀ u, F1.val u = Fo.val u + if t.1 = u then (t.2.1 : ℝ) else 0 := by
      intro u
      simp only [hF1, addPath2, addPath, hrp, List.mem_singleton]
      by_cases hu : u = t.1
      · subst hu; simp
      · simp [hu, Ne.symm hu]
    have hF1v2 : ∀ u, F1.val2 u = Fo.val2 u + if t.1 = u then (t.2.2 : ℝ) else 0 := by
      intro u
      simp only [hF1, addPath2, hrp', List.mem_singleton]
      by_cases hu : u = t.1
      · subst hu; simp [addPath]
      · simp [hu, Ne.symm hu, addPath]
    have ih := setOps_run L F1 fun t' ht' =>
      ⟨(h t' (by simp [ht'])).1, (h t' (by simp [ht'])).2⟩
    have hsplit : setOps (t :: L) = [.add t.1 t.2.1, .add2 t.1 t.2.2] ++ setOps L := by
      simp [setOps]
    have hrun2 : runOpsE n Fo [.add t.1 t.2.1, .add2 t.1 t.2.2] = (F1, []) := rfl
    rw [hsplit, runOpsE_append, validOpsE_append, hrun2]
    refine ⟨⟨⟨ht, ht, trivial⟩, ih.1⟩, by simp [ih.2.1], ih.2.2.1, fun u => ?_⟩
    rw [(ih.2.2.2 u).1, (ih.2.2.2 u).2, hF1v, hF1v2]
    simp only [List.map_cons, List.sum_cons]
    constructor <;> ring

lemma sum_ite_single {f : ℕ × ℤ × ℤ → ℝ} : ∀ {L : List (ℕ × ℤ × ℤ)},
    (L.map Prod.fst).Nodup → ∀ {t}, t ∈ L →
      (L.map fun t' => if t'.1 = t.1 then f t' else 0).sum = f t
  | [], _, _, h => absurd h (by simp)
  | a :: L, hnd, t, ht => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 ht with rfl | ht
    · rw [ite_eq_left rfl, List.sum_eq_zero, add_zero]
      intro x hx
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hx
      rw [ite_eq_right fun (h : t'.1 = _) => hnd.1 (by rw [← h]; exact List.mem_map_of_mem ht')]
    · rw [ite_eq_right fun (h : a.1 = t.1) => hnd.1 (by rw [h]; exact List.mem_map_of_mem ht),
        sum_ite_single hnd.2 ht, zero_add]

lemma sum_ite_none {f : ℕ × ℤ × ℤ → ℝ} {L : List (ℕ × ℤ × ℤ)} {u : ℕ}
    (h : ∀ t ∈ L, t.1 ≠ u) : (L.map fun t' => if t'.1 = u then f t' else 0).sum = 0 := by
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 hx
  rw [ite_eq_right (h t' ht')]

/-! ### Linking a tree -/

section Generic

variable {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]
variable {N : CombMap D X Y} {n : ℕ} {C : DTree N} {ιf : Y → ℕ} {ιe : D → ℕ}

/-- The two links hanging the face `y` (other than the root): the node of the edge of its parent
dart below the node of the parent face, then the node of `y` below it. -/
def linkOps (C : DTree N) (ιf : Y → ℕ) (ιe : D → ℕ) (ys : List Y) : List EOp :=
  ys.flatMap fun y => [.link (ιe (C.par y)) (ιf (N.face (C.par y))), .link (ιf y) (ιe (C.par y))]

lemma linkOps_length (ys : List Y) : (linkOps C ιf ιe ys).length = 2 * ys.length := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [linkOps, List.flatMap_cons, List.length_append] at ih ⊢; simp; omega

variable (n C ιf ιe) in
/-- The forest after linking the faces of `Q` (closed under the parent), the other nodes as in
`Fo₀`. -/
structure LInv (Fo₀ : Forest) (Q : Finset Y) (Fo : Forest) : Prop where
  pf : ∀ y, y ≠ C.root → Fo.par (ιf y) = if y ∈ Q then ιe (C.par y) else n
  pe : ∀ y, y ≠ C.root → Fo.par (ιe (C.par y)) = if y ∈ Q then ιf (N.face (C.par y)) else n
  pr : Fo.par (ιf C.root) = n
  po : ∀ u, (∀ y, u ≠ ιf y) → (∀ y, y ≠ C.root → u ≠ ιe (C.par y)) → Fo.par u = Fo₀.par u
  val : Fo.val = Fo₀.val
  val2 : Fo.val2 = Fo₀.val2
  closed : ∀ y ∈ Q, y ≠ C.root ∧ (C.up y = C.root ∨ C.up y ∈ Q)

lemma LInv.path {Fo₀ Fo : Forest} {Q : Finset Y} (hI : LInv n C ιf ιe Fo₀ Q Fo)
    (hN : Nodes n N ιf ιe) {x : Y} (hx : x = C.root ∨ x ∈ Q) :
    ∀ fuel, 2 * C.depth x + 1 ≤ fuel → upPath Fo n fuel (ιf x) = tpath C ιf ιe (C.depth x) x := by
  have hQ : ∀ i < C.depth x, C.up^[i] x ∈ Q := by
    intro i
    induction i with
    | zero =>
      intro hi
      rcases hx with rfl | hx
      · rw [C.depth_root] at hi; omega
      · exact hx
    | succ i ih =>
      intro hi
      rcases (hI.closed _ (ih (by omega))).2 with h | h
      · exact absurd (by rw [Function.iterate_succ_apply']; exact h)
          (C.iterate_ne_root (show i + 1 < C.depth x from hi))
      · rw [Function.iterate_succ_apply']; exact h
  intro fuel hfuel
  refine upPath_seg hN.f_lt hN.e_lt _ x le_rfl (fun i hi => ⟨?_, ?_⟩) ?_ fuel hfuel
  · rw [hI.pf _ (C.iterate_ne_root hi), ite_eq_left (hQ i hi)]
  · rw [hI.pe _ (C.iterate_ne_root hi), ite_eq_left (hQ i hi), Function.iterate_succ_apply',
      C.up_of_ne (C.iterate_ne_root hi)]
  · rw [C.iterate_depth]; exact hI.pr

lemma LInv.findRoot {Fo₀ Fo : Forest} {Q : Finset Y} (hI : LInv n C ιf ιe Fo₀ Q Fo)
    (hN : Nodes n N ιf ιe) (hn : 2 * Fintype.card Y ≤ n) {x : Y} (hx : x = C.root ∨ x ∈ Q) :
    DynTree.findRoot Fo n (ιf x) = ιf C.root := by
  unfold DynTree.findRoot rootPath
  rw [hI.path hN hx n (by have := C.depth_lt_card x; omega), tpath_getLast, C.iterate_depth]

/-- **Hanging one face** below its parent face, already stored. -/
lemma LInv.step {Fo₀ Fo : Forest} {Q : Finset Y} (hI : LInv n C ιf ιe Fo₀ Q Fo)
    (hN : Nodes n N ιf ιe) (hn : 2 * Fintype.card Y ≤ n) {y : Y} (hy : y ≠ C.root)
    (hyQ : y ∉ Q) (hup : C.up y = C.root ∨ C.up y ∈ Q) :
    ValidOpsE n Fo (linkOps C ιf ιe [y]) ∧ (runOpsE n Fo (linkOps C ιf ιe [y])).2 = [] ∧
      LInv n C ιf ιe Fo₀ (insert y Q) (runOpsE n Fo (linkOps C ιf ιe [y])).1 := by
  classical
  set p := C.par y with hp
  have hfp : N.face p = C.up y := (C.up_of_ne hy).symm
  set F1 := DynTree.link Fo (ιe p) (ιf (N.face p)) with hF1
  set F2 := DynTree.link F1 (ιf y) (ιe p) with hF2
  have hrun : runOpsE n Fo (linkOps C ιf ιe [y]) = (F2, []) := by
    simp [linkOps, runOpsE, EOp.apply, EOp.answer, hF2, hF1, hp]
  have hpe : ∀ x, x ≠ C.root → ιe (C.par x) = ιe p → x = y := fun x hx h =>
    C.par_eq_or hy hx (hN.e_eq _ _ h.symm)
  have hupQ : C.up y = C.root ∨ C.up y ∈ Q := hup
  have hr1 : DynTree.findRoot Fo n (ιf (N.face p)) = ιf C.root := by
    rw [hfp]; exact hI.findRoot hN hn hup
  -- the path from the parent face in `F1`
  have hdy := C.depth_up hy
  have hnot : ∀ u ∈ tpath C ιf ιe (C.depth (C.up y)) (C.up y), u ≠ ιe p := by
    rintro u hu rfl
    rcases mem_tpath_cases hu with ⟨x, hx⟩ | ⟨i, hi, hx⟩
    · exact hN.fe _ _ hx.symm
    · have h1 := hpe _ (C.iterate_ne_root hi) hx.symm
      rw [← Function.iterate_succ_apply] at h1
      have := C.iterate_inj (show i + 1 ≤ C.depth y by omega) (show 0 ≤ C.depth y by omega) h1
      omega
  have hseg : ∀ fuel, 2 * C.depth (C.up y) + 1 ≤ fuel →
      upPath F1 n fuel (ιf (C.up y)) = tpath C ιf ιe (C.depth (C.up y)) (C.up y) := by
    intro fuel hfuel
    rw [upPath_congr (Fo := Fo) (Fo' := F1) fuel _ fun u hu => ?_]
    · exact hI.path hN hup fuel hfuel
    · rw [hI.path hN hup fuel hfuel] at hu
      simp [hF1, DynTree.link, hnot u hu]
  have hmn : 2 * C.depth (C.up y) + 2 ≤ n := by have := C.depth_lt_card (C.up y); omega
  have hr2 : DynTree.findRoot F1 n (ιe p) = ιf C.root := by
    unfold DynTree.findRoot rootPath
    have h5 : F1.par (ιe p) = ιf (C.up y) := by simp [hF1, DynTree.link, hfp]
    have hcons : upPath F1 n n (ιe p) = ιe p :: upPath F1 n (n - 1) (F1.par (ιe p)) := by
      have e1 : upPath F1 n n (ιe p) = upPath F1 n ((n - 1) + 1) (ιe p) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      rw [e1]
      simp [upPath, hN.e_lt p]
    rw [hcons, h5, hseg _ (by omega), List.getLastD_cons, tpath_getLast, C.iterate_depth]
  have hyp : ιf y ≠ ιe p := hN.fe _ _
  have hF1y : F1.par (ιf y) = n := by
    simp only [hF1, DynTree.link, ite_eq_right hyp]
    rw [hI.pf y hy, ite_eq_right hyQ]
  rw [hrun]
  refine ⟨⟨⟨hN.e_lt _, hN.f_lt _, by rw [hI.pe y hy, ite_eq_right hyQ], ?_⟩,
    ⟨hN.f_lt _, hN.e_lt _, hF1y, ?_⟩, trivial⟩, rfl, ⟨fun x hx => ?_, fun x hx => ?_, ?_,
    fun u hu1 hu2 => ?_, hI.val, hI.val2, fun x hx => ?_⟩⟩
  · rw [hr1]; exact hN.fe _ _
  · show DynTree.findRoot F1 n (ιe p) ≠ ιf y
    rw [hr2]; exact fun h => hy (hN.f_inj h).symm
  · show F2.par (ιf x) = _
    by_cases hxy : x = y
    · subst hxy; simp [hF2, DynTree.link, hp]
    · have h1 : ιf x ≠ ιf y := fun h => hxy (hN.f_inj h)
      simp only [hF2, hF1, DynTree.link, ite_eq_right h1, ite_eq_right (hN.fe x p), mem_insert,
        hxy, false_or]
      exact hI.pf x hx
  · show F2.par (ιe (C.par x)) = _
    simp only [hF2, hF1, DynTree.link, ite_eq_right (Ne.symm (hN.fe _ _)), mem_insert]
    by_cases hxy : x = y
    · subst hxy; simp [hp]
    · have h1 : ιe (C.par x) ≠ ιe p := fun h => hxy (hpe x hx h)
      rw [ite_eq_right h1, hI.pe x hx]
      simp [hxy]
  · show F2.par (ιf C.root) = n
    have h1 : ιf C.root ≠ ιf y := fun h => hy (hN.f_inj h).symm
    simp only [hF2, hF1, DynTree.link, ite_eq_right h1, ite_eq_right (hN.fe _ _)]
    exact hI.pr
  · show F2.par u = Fo₀.par u
    simp only [hF2, hF1, DynTree.link, ite_eq_right (hu1 y)]
    rw [ite_eq_right (show u ≠ ιe p from hu2 y hy)]
    exact hI.po u hu1 hu2
  · rcases mem_insert.1 hx with rfl | hx
    · exact ⟨hy, hup.imp id fun h => mem_insert_of_mem h⟩
    · obtain ⟨h1, h2⟩ := hI.closed x hx
      exact ⟨h1, h2.imp id fun h => mem_insert_of_mem h⟩

/-- **Linking the faces of a list**, in an order of nondecreasing depth, each with its parent
face already stored or in the list. -/
lemma LInv.run (hN : Nodes n N ιf ιe) (hn : 2 * Fintype.card Y ≤ n) {Fo₀ : Forest} :
    ∀ (ys : List Y) (Q : Finset Y) (Fo : Forest), LInv n C ιf ιe Fo₀ Q Fo → ys.Nodup →
      (∀ y ∈ ys, y ≠ C.root ∧ y ∉ Q) →
      (∀ y ∈ ys, C.up y = C.root ∨ C.up y ∈ Q ∨ C.up y ∈ ys) →
      ys.Pairwise (fun a b => C.depth a ≤ C.depth b) →
      ValidOpsE n Fo (linkOps C ιf ιe ys) ∧ (runOpsE n Fo (linkOps C ιf ιe ys)).2 = [] ∧
        LInv n C ιf ιe Fo₀ (Q ∪ ys.toFinset) (runOpsE n Fo (linkOps C ιf ιe ys)).1
  | [], Q, Fo, hI, _, _, _, _ => by simpa [linkOps, runOpsE, ValidOpsE] using hI
  | y :: ys, Q, Fo, hI, hnd, hyQ, hup, hpw => by
    classical
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hpw
    obtain ⟨hy, hyQ'⟩ := hyQ y (by simp)
    have hup' : C.up y = C.root ∨ C.up y ∈ Q := by
      rcases hup y (by simp) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · rcases List.mem_cons.1 h with h | h
        · exact absurd h (fun h' => by
            have := C.depth_up hy; rw [h'] at this; omega)
        · have := hpw.1 _ h
          have := C.depth_up hy
          omega
    obtain ⟨hv1, ho1, hI1⟩ := hI.step hN hn hy hyQ' hup'
    have hsplit : linkOps C ιf ιe (y :: ys) = linkOps C ιf ιe [y] ++ linkOps C ιf ιe ys := by
      simp [linkOps]
    obtain ⟨hv2, ho2, hI2⟩ := LInv.run hN hn ys (insert y Q) _ hI1 hnd.2
      (fun y' hy' => ⟨(hyQ y' (by simp [hy'])).1, by
        rw [mem_insert]; rintro (h | h)
        · exact hnd.1 (h ▸ hy')
        · exact (hyQ y' (by simp [hy'])).2 h⟩)
      (fun y' hy' => by
        rcases hup y' (by simp [hy']) with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (mem_insert_of_mem h))
        · rcases List.mem_cons.1 h with h | h
          · exact Or.inr (Or.inl (h ▸ mem_insert_self _ _))
          · exact Or.inr (Or.inr h))
      hpw.2
    rw [hsplit, runOpsE_append, validOpsE_append]
    refine ⟨⟨hv1, hv2⟩, by rw [ho1, ho2]; rfl, ?_⟩
    have : Q ∪ (y :: ys).toFinset = insert y Q ∪ ys.toFinset := by
      ext x; simp
    rw [this]; exact hI2

/-! ### Storing a tree -/

/-- The values of a stored tree, by nodes: the faces, then the edges of the tree. -/
noncomputable def treeVals (C : DTree N) (ιf : Y → ℕ) (ιe : D → ℕ) (κ : D → ℤ) (β β₂ : Y → ℤ) :
    List (ℕ × ℤ × ℤ) :=
  (univ : Finset Y).toList.map (fun y => (ιf y, β y, β₂ y)) ++
    ((univ : Finset Y).filter (· ≠ C.root)).toList.map
      (fun y => (ιe (C.par y), κ (N.rev (C.par y)), κ (C.par y)))

/-- The faces other than the root, by nondecreasing depth. -/
noncomputable def depthOrder (C : DTree N) : List Y :=
  ((univ : Finset Y).filter (· ≠ C.root)).toList.mergeSort
    fun a b => decide (C.depth a ≤ C.depth b)

/-- The operations storing a tree: the values of its nodes, then the links. -/
noncomputable def buildOps (C : DTree N) (ιf : Y → ℕ) (ιe : D → ℕ) (κ : D → ℤ) (β β₂ : Y → ℤ) :
    List EOp :=
  setOps (treeVals C ιf ιe κ β β₂) ++ linkOps C ιf ιe (depthOrder C)

/-- **Storing a tree** with integer values in a forest in which its nodes are isolated roots of
value `0`: at most `6 #Y` valid operations, printing nothing, store it, with the nodes of the
edges off the tree isolated and the other nodes unchanged. -/
theorem build_trep (hN : Nodes n N ιf ιe) (hn : 2 * Fintype.card Y ≤ n) (κ : D → ℤ)
    (β β₂ : Y → ℤ) {Fo : Forest} (hpf : ∀ y, Fo.par (ιf y) = n) (hpe : ∀ d, Fo.par (ιe d) = n)
    (hvf : ∀ y, Fo.val (ιf y) = 0 ∧ Fo.val2 (ιf y) = 0)
    (hve : ∀ d, Fo.val (ιe d) = 0 ∧ Fo.val2 (ιe d) = 0) :
    (buildOps C ιf ιe κ β β₂).length ≤ 6 * Fintype.card Y ∧
      ValidOpsE n Fo (buildOps C ιf ιe κ β β₂) ∧
      (runOpsE n Fo (buildOps C ιf ιe κ β β₂)).2 = [] ∧
      TRep n (runOpsE n Fo (buildOps C ιf ιe κ β β₂)).1 C ιf ιe (fun d => (κ d : ℝ))
        (fun y => (β y : ℝ)) (fun y => (β₂ y : ℝ)) ∧
      Iso n (runOpsE n Fo (buildOps C ιf ιe κ β β₂)).1 C ιe ∧
      ∀ u, (∀ y, u ≠ ιf y) → (∀ d, u ≠ ιe d) →
        Agree Fo (runOpsE n Fo (buildOps C ιf ιe κ β β₂)).1 u := by
  classical
  set L := treeVals C ιf ιe κ β β₂ with hLdef
  set R := (univ : Finset Y).filter (· ≠ C.root) with hR
  have hmemL : ∀ t ∈ L, (∃ y, t = (ιf y, β y, β₂ y)) ∨
      ∃ y, y ≠ C.root ∧ t = (ιe (C.par y), κ (N.rev (C.par y)), κ (C.par y)) := by
    intro t ht
    simp only [hLdef, treeVals, List.mem_append, List.mem_map, mem_toList, mem_univ, true_and,
      mem_filter] at ht
    rcases ht with ⟨y, rfl⟩ | ⟨y, hy, rfl⟩
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨y, hy, rfl⟩
  have hnd : (L.map Prod.fst).Nodup := by
    have e : L.map Prod.fst = (univ : Finset Y).toList.map ιf ++
        R.toList.map (fun y => ιe (C.par y)) := by
      simp [hLdef, treeVals, List.map_map, Function.comp_def, hR]
    rw [e, List.nodup_append]
    refine ⟨(nodup_toList _).map hN.f_inj, (nodup_toList _).map_on fun x hx y hy h => ?_,
      fun a ha b hb => ?_⟩
    · rw [mem_toList, hR, mem_filter] at hx hy
      exact (C.par_eq_or hx.2 hy.2 (hN.e_eq _ _ h)).symm
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
      obtain ⟨y', -, rfl⟩ := List.mem_map.1 hb
      exact hN.fe _ _
  -- the values
  obtain ⟨hv1, ho1, hp1, hval1⟩ := setOps_run (n := n) L Fo fun t ht => by
    rcases hmemL t ht with ⟨y, rfl⟩ | ⟨y, -, rfl⟩
    · exact ⟨hN.f_lt y, hpf y⟩
    · exact ⟨hN.e_lt _, hpe _⟩
  set F1 := (runOpsE n Fo (setOps L)).1 with hF1
  have hI0 : LInv n C ιf ιe F1 ∅ F1 :=
    ⟨fun y _ => by simp [hp1, hpf], fun y _ => by simp [hp1, hpe], by simp [hp1, hpf],
      fun _ _ _ => rfl, rfl, rfl, fun y hy => absurd hy (Finset.notMem_empty y)⟩
  -- the links
  have hmemR : ∀ y, y ∈ depthOrder C ↔ y ≠ C.root := by
    intro y; simp [depthOrder]
  obtain ⟨hv2, ho2, hI2⟩ := LInv.run hN hn (depthOrder C) ∅ F1 hI0
    ((List.mergeSort_perm _ _).nodup_iff.2 (nodup_toList _))
    (fun y hy => ⟨(hmemR y).1 hy, Finset.notMem_empty y⟩)
    (fun y hy => by
      by_cases h : C.up y = C.root
      · exact Or.inl h
      · exact Or.inr (Or.inr ((hmemR _).2 h)))
    ((List.pairwise_mergeSort (le := fun a b => decide (C.depth a ≤ C.depth b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at h1 h2 ⊢; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
      fun h => by simpa using h)
  have hmemQ : ∀ y, y ∈ (∅ : Finset Y) ∪ (depthOrder C).toFinset ↔ y ≠ C.root := by
    intro y; rw [empty_union, List.mem_toFinset, hmemR]
  have hrun : (runOpsE n Fo (buildOps C ιf ιe κ β β₂)).1 =
      (runOpsE n F1 (linkOps C ιf ιe (depthOrder C))).1 := by
    rw [buildOps, runOpsE_append]
  set F2 := (runOpsE n F1 (linkOps C ιf ιe (depthOrder C))).1 with hF2
  have hval2 : ∀ u, F2.val u = Fo.val u +
      (L.map fun t => if t.1 = u then (t.2.1 : ℝ) else 0).sum := by
    intro u; rw [hI2.val]; exact (hval1 u).1
  have hval22 : ∀ u, F2.val2 u = Fo.val2 u +
      (L.map fun t => if t.1 = u then (t.2.2 : ℝ) else 0).sum := by
    intro u; rw [hI2.val2]; exact (hval1 u).2
  have hmemf : ∀ y, (ιf y, β y, β₂ y) ∈ L := fun y => by
    simp only [hLdef, treeVals, List.mem_append, List.mem_map, mem_toList, mem_univ, true_and]
    exact Or.inl ⟨y, rfl⟩
  have hmeme : ∀ y, y ≠ C.root →
      (ιe (C.par y), κ (N.rev (C.par y)), κ (C.par y)) ∈ L := fun y hy => by
    simp only [hLdef, treeVals, List.mem_append, List.mem_map, mem_toList, mem_univ, true_and,
      mem_filter]
    exact Or.inr ⟨y, hy, rfl⟩
  have hlen : (buildOps C ιf ιe κ β β₂).length ≤ 6 * Fintype.card Y := by
    have h1 : R.card ≤ Fintype.card Y := card_le_univ R
    simp only [buildOps, List.length_append, setOps_length, linkOps_length, depthOrder,
      List.length_mergeSort, treeVals, List.length_map, length_toList, card_univ]
    rw [← hR]
    omega
  refine ⟨hlen, (validOpsE_append n _ _ _).2 ⟨hv1, hv2⟩, ?_, ?_, ?_, ?_⟩
  · rw [buildOps, runOpsE_append, ho1, ho2]; rfl
  · rw [hrun]
    refine ⟨fun y hy => ?_, ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y => ?_,
      fun y => ?_⟩
    · rw [hI2.pf y hy, ite_eq_left ((hmemQ y).2 hy)]
    · exact hI2.pr
    · rw [hI2.pe y hy, ite_eq_left ((hmemQ y).2 hy)]
    · rw [hval2, (hve _).1, sum_ite_single hnd (hmeme y hy), zero_add]
    · rw [hval22, (hve _).2, sum_ite_single hnd (hmeme y hy), zero_add]
    · rw [hval2, (hvf _).1, sum_ite_single hnd (hmemf y), zero_add]
    · rw [hval22, (hvf _).2, sum_ite_single hnd (hmemf y), zero_add]
  · rw [hrun]
    intro d hd
    rw [hI2.po _ (fun y => (hN.fe y d).symm) fun y hy h => ?_, hp1]
    · exact hpe d
    · rcases hN.e_eq _ _ h with h' | h'
      · exact (hd y hy).1 h'.symm
      · exact (hd y hy).2 (by rw [h', N.rev_rev])
  · intro u hu1 hu2
    rw [hrun]
    have hnot : ∀ t ∈ L, t.1 ≠ u := by
      intro t ht
      rcases hmemL t ht with ⟨y, rfl⟩ | ⟨y, -, rfl⟩
      · exact fun h => hu1 y h.symm
      · exact fun h => hu2 _ h.symm
    refine ⟨?_, ?_, ?_⟩
    · rw [hI2.po u hu1 fun y _ => hu2 _, hp1]
    · rw [hval2, sum_ite_none hnot, add_zero]
    · rw [hval22, sum_ite_none hnot, add_zero]


end Generic

/-! ### The initial stored data -/

section Init

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

lemma intF_init (n : ℕ) : IntF (Forest.init n) := fun _ => ⟨⟨0, by simp [Forest.init]⟩,
  ⟨0, by simp [Forest.init]⟩⟩

/-- **The initial stored data**: from the empty forest (`Forest.init`), at most `6 (#V + #F)`
valid operations, printing nothing, store a cotree `C` (its parent darts off `T`) with the
values `val` and the value `H₀` at the nodes of the faces, and the spanning tree `T` with the
weights `φ`. -/
theorem init_stored (hL : Layout M n ιv ιg ιf ιe) {T : DTree M.dual} {C : DTree M}
    (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x)) (φ val : D → ℤ) (H₀ : ℤ) :
    ∃ os : List EOp, os.length ≤ 6 * (Fintype.card V + Fintype.card F) ∧
      ValidOpsE n (Forest.init n) os ∧ (runOpsE n (Forest.init n) os).2 = [] ∧
      Stored M n ιv ιg ιf ιe φ C.root H₀ (runOpsE n (Forest.init n) os).1 T val := by
  obtain ⟨hl1, hv1, ho1, hR1, hI1, hag1⟩ := build_trep (C := C) hL.dual hL.hf val
    (fun _ => H₀) (fun _ => H₀) (Fo := Forest.init n) (fun _ => rfl) (fun _ => rfl)
    (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
  set F1 := (runOpsE n (Forest.init n) (buildOps C ιf ιe val (fun _ => H₀) (fun _ => H₀))).1
    with hF1
  have hav : ∀ x, Agree (Forest.init n) F1 (ιv x) := fun x => hag1 _ (hL.vf x) (hL.ve x)
  have hag : ∀ d, Agree (Forest.init n) F1 (ιg d) := fun d => hag1 _ (hL.gf d) (hL.ge d)
  obtain ⟨hl2, hv2, ho2, hR2, hI2, hag2⟩ := build_trep (C := T) hL.prim hL.hv
    (fun d => φ (M.rev d)) (fun _ => 0) (fun _ => 0) (Fo := F1) (fun x => (hav x).1)
    (fun d => (hag d).1) (fun x => ⟨(hav x).2.1, (hav x).2.2⟩)
    (fun d => ⟨(hag d).2.1, (hag d).2.2⟩)
  refine ⟨buildOps C ιf ιe val (fun _ => H₀) (fun _ => H₀) ++
    buildOps T ιv ιg (fun d => φ (M.rev d)) (fun _ => 0) (fun _ => 0), ?_,
    (validOpsE_append n _ _ _).2 ⟨hv1, hv2⟩, ?_, ?_⟩
  · rw [List.length_append]; omega
  · rw [runOpsE_append, ho1, ho2]; rfl
  · rw [runOpsE_append]
    have hagc : ∀ y, Agree F1 _ (ιf y) := fun y =>
      hag2 _ (fun x => (hL.vf x y).symm) (fun d => (hL.gf d y).symm)
    have hage : ∀ d, Agree F1 _ (ιe d) := fun d =>
      hag2 _ (fun x => (hL.ve x d).symm) (fun d' => (hL.ge d' d).symm)
    refine ⟨hR2.congrβ (fun _ => by simp) (fun _ => by simp), hI2,
      ⟨C, fun _ => H₀, fun _ => H₀, rfl, hoff, hR1.congr hagc hage, hI1.congr hage,
        fun _ => ⟨le_rfl, le_rfl⟩⟩, intF_runOpsE _ (intF_runOpsE _ (intF_init n))⟩

end Init

end Klein

end PlanarFlow
