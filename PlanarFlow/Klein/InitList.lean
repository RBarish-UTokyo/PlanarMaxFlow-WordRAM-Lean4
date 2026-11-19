module

public import PlanarFlow.Klein.LCTTrip

/-!
# Storing the trees from the empty forest, in given orders

`build_trep` and `init_stored` (`PlanarFlow/Klein/LCTInit.lean`) store the trees in orders chosen
by existence (`Finset.toList`, `depthOrder`). A program reads the orders from its input; here they
are any lists meeting the requirements.

* `buildOpsL C ιf ιe κ β β₂ fs ys`: the values of the nodes of the faces in the order `fs`, then
  those of the edges in the order `ys`, then the links in the order `ys`; `build_trepL`: **storing
  a tree** with these operations, for `fs` listing every face once and `ys` every face but the root
  once by nondecreasing depth.
* `init_storedL`: **the initial stored data** from the empty forest, the spanning tree first (in
  the orders `vs`, `ts`), then the cotree (in the orders `fs`, `cs`): at most `6 (#V + #F)`
  operations; the spanning tree is stored after the first part, so the program may read its path
  sums before storing the cotree.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap STFlow DynTree

section Generic

variable {D X Y : Type*} [Fintype D] [DecidableEq D] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]
variable {N : CombMap D X Y} {n : ℕ} {C : DTree N} {ιf : Y → ℕ} {ιe : D → ℕ}

/-- The values of a stored tree, in the orders `fs` (the faces) and `ys` (the edges). -/
def treeValsL (C : DTree N) (ιf : Y → ℕ) (ιe : D → ℕ) (κ : D → ℤ) (β β₂ : Y → ℤ)
    (fs ys : List Y) : List (ℕ × ℤ × ℤ) :=
  fs.map (fun y => (ιf y, β y, β₂ y)) ++
    ys.map (fun y => (ιe (C.par y), κ (N.rev (C.par y)), κ (C.par y)))

/-- The operations storing a tree in the orders `fs`, `ys`: the values, then the links. -/
def buildOpsL (C : DTree N) (ιf : Y → ℕ) (ιe : D → ℕ) (κ : D → ℤ) (β β₂ : Y → ℤ)
    (fs ys : List Y) : List EOp :=
  setOps (treeValsL C ιf ιe κ β β₂ fs ys) ++ linkOps C ιf ιe ys

/-- The requirements on the orders: `fs` lists every face once, `ys` every face but the root
once, by nondecreasing depth. -/
structure Orders (C : DTree N) (fs ys : List Y) : Prop where
  fnd : fs.Nodup
  fmem : ∀ y, y ∈ fs
  ynd : ys.Nodup
  ymem : ∀ y, y ∈ ys ↔ y ≠ C.root
  ypw : ys.Pairwise (fun a b => C.depth a ≤ C.depth b)

lemma Orders.flen {fs ys : List Y} (h : Orders C fs ys) : fs.length = Fintype.card Y := by
  rw [← List.toFinset_card_of_nodup h.fnd]
  congr 1
  ext y; simp [h.fmem y]

lemma Orders.ylen {fs ys : List Y} (h : Orders C fs ys) : ys.length ≤ Fintype.card Y := by
  rw [← List.toFinset_card_of_nodup h.ynd]; exact card_le_univ _

/-- **Orders exist**: `Finset.toList` and `depthOrder`. -/
lemma orders_exist (C : DTree N) : Orders C (univ : Finset Y).toList (depthOrder C) :=
  ⟨nodup_toList _, fun y => by simp, (List.mergeSort_perm _ _).nodup_iff.2 (nodup_toList _),
    fun y => by simp [depthOrder],
    (List.pairwise_mergeSort (le := fun a b => decide (C.depth a ≤ C.depth b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at h1 h2 ⊢; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).imp
      fun h => by simpa using h⟩

/-- **Storing a tree in given orders** (`build_trep`). -/
theorem build_trepL (hN : Nodes n N ιf ιe) (hn : 2 * Fintype.card Y ≤ n) (κ : D → ℤ)
    (β β₂ : Y → ℤ) {fs ys : List Y} (hO : Orders C fs ys) {Fo : Forest}
    (hpf : ∀ y, Fo.par (ιf y) = n) (hpe : ∀ d, Fo.par (ιe d) = n)
    (hvf : ∀ y, Fo.val (ιf y) = 0 ∧ Fo.val2 (ιf y) = 0)
    (hve : ∀ d, Fo.val (ιe d) = 0 ∧ Fo.val2 (ιe d) = 0) :
    (buildOpsL C ιf ιe κ β β₂ fs ys).length ≤ 6 * Fintype.card Y ∧
      ValidOpsE n Fo (buildOpsL C ιf ιe κ β β₂ fs ys) ∧
      (runOpsE n Fo (buildOpsL C ιf ιe κ β β₂ fs ys)).2 = [] ∧
      TRep n (runOpsE n Fo (buildOpsL C ιf ιe κ β β₂ fs ys)).1 C ιf ιe (fun d => (κ d : ℝ))
        (fun y => (β y : ℝ)) (fun y => (β₂ y : ℝ)) ∧
      Iso n (runOpsE n Fo (buildOpsL C ιf ιe κ β β₂ fs ys)).1 C ιe ∧
      ∀ u, (∀ y, u ≠ ιf y) → (∀ d, u ≠ ιe d) →
        Agree Fo (runOpsE n Fo (buildOpsL C ιf ιe κ β β₂ fs ys)).1 u := by
  classical
  set L := treeValsL C ιf ιe κ β β₂ fs ys with hLdef
  have hmemL : ∀ t ∈ L, (∃ y, t = (ιf y, β y, β₂ y)) ∨
      ∃ y, y ≠ C.root ∧ t = (ιe (C.par y), κ (N.rev (C.par y)), κ (C.par y)) := by
    intro t ht
    simp only [hLdef, treeValsL, List.mem_append, List.mem_map] at ht
    rcases ht with ⟨y, -, rfl⟩ | ⟨y, hy, rfl⟩
    · exact Or.inl ⟨y, rfl⟩
    · exact Or.inr ⟨y, (hO.ymem y).1 hy, rfl⟩
  have hnd : (L.map Prod.fst).Nodup := by
    have e : L.map Prod.fst = fs.map ιf ++ ys.map (fun y => ιe (C.par y)) := by
      simp [hLdef, treeValsL, List.map_map, Function.comp_def]
    rw [e, List.nodup_append]
    refine ⟨hO.fnd.map hN.f_inj, hO.ynd.map_on fun x hx y hy h => ?_, fun a ha b hb => ?_⟩
    · exact (C.par_eq_or ((hO.ymem x).1 hx) ((hO.ymem y).1 hy) (hN.e_eq _ _ h)).symm
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 ha
      obtain ⟨y', -, rfl⟩ := List.mem_map.1 hb
      exact hN.fe _ _
  obtain ⟨hv1, ho1, hp1, hval1⟩ := setOps_run (n := n) L Fo fun t ht => by
    rcases hmemL t ht with ⟨y, rfl⟩ | ⟨y, -, rfl⟩
    · exact ⟨hN.f_lt y, hpf y⟩
    · exact ⟨hN.e_lt _, hpe _⟩
  set F1 := (runOpsE n Fo (setOps L)).1 with hF1
  have hI0 : LInv n C ιf ιe F1 ∅ F1 :=
    ⟨fun y _ => by simp [hp1, hpf], fun y _ => by simp [hp1, hpe], by simp [hp1, hpf],
      fun _ _ _ => rfl, rfl, rfl, fun y hy => absurd hy (Finset.notMem_empty y)⟩
  obtain ⟨hv2, ho2, hI2⟩ := LInv.run hN hn ys ∅ F1 hI0 hO.ynd
    (fun y hy => ⟨(hO.ymem y).1 hy, Finset.notMem_empty y⟩)
    (fun y hy => by
      by_cases h : C.up y = C.root
      · exact Or.inl h
      · exact Or.inr (Or.inr ((hO.ymem _).2 h)))
    hO.ypw
  have hmemQ : ∀ y, y ∈ (∅ : Finset Y) ∪ ys.toFinset ↔ y ≠ C.root := by
    intro y; rw [empty_union, List.mem_toFinset, hO.ymem]
  have hrun : (runOpsE n Fo (buildOpsL C ιf ιe κ β β₂ fs ys)).1 =
      (runOpsE n F1 (linkOps C ιf ιe ys)).1 := by
    rw [buildOpsL, runOpsE_append]
  set F2 := (runOpsE n F1 (linkOps C ιf ιe ys)).1 with hF2
  have hval2 : ∀ u, F2.val u = Fo.val u +
      (L.map fun t => if t.1 = u then (t.2.1 : ℝ) else 0).sum := by
    intro u; rw [hI2.val]; exact (hval1 u).1
  have hval22 : ∀ u, F2.val2 u = Fo.val2 u +
      (L.map fun t => if t.1 = u then (t.2.2 : ℝ) else 0).sum := by
    intro u; rw [hI2.val2]; exact (hval1 u).2
  have hmemf : ∀ y, (ιf y, β y, β₂ y) ∈ L := fun y => by
    simp only [hLdef, treeValsL, List.mem_append, List.mem_map]
    exact Or.inl ⟨y, hO.fmem y, rfl⟩
  have hmeme : ∀ y, y ≠ C.root →
      (ιe (C.par y), κ (N.rev (C.par y)), κ (C.par y)) ∈ L := fun y hy => by
    simp only [hLdef, treeValsL, List.mem_append, List.mem_map]
    exact Or.inr ⟨y, (hO.ymem y).2 hy, rfl⟩
  have hlen : (buildOpsL C ιf ιe κ β β₂ fs ys).length ≤ 6 * Fintype.card Y := by
    have h1 := hO.flen
    have h2 := hO.ylen
    simp only [buildOpsL, List.length_append, setOps_length, linkOps_length, treeValsL,
      List.length_map]
    omega
  refine ⟨hlen, (validOpsE_append n _ _ _).2 ⟨hv1, hv2⟩, ?_, ?_, ?_, ?_⟩
  · rw [buildOpsL, runOpsE_append, ho1, ho2]; rfl
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

section Init

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

/-- The operations storing the spanning tree `T` with the weights `φ`, in the orders `vs`, `ts`. -/
def treeOpsL (T : DTree M.dual) (ιv : V → ℕ) (ιg : D → ℕ) (φ : D → ℤ) (vs ts : List V) :
    List EOp :=
  buildOpsL T ιv ιg (fun d => φ (M.rev d)) (fun _ => 0) (fun _ => 0) vs ts

/-- The operations storing the cotree `C` with the values `val` and `H₀`, in the orders `fs`,
`cs`. -/
def cotOpsL (C : DTree M) (ιf : F → ℕ) (ιe : D → ℕ) (val : D → ℤ) (H₀ : ℤ) (fs cs : List F) :
    List EOp :=
  buildOpsL C ιf ιe val (fun _ => H₀) (fun _ => H₀) fs cs

/-- **The spanning tree stored first**: after `treeOpsL`, the forest stores `T` with the weights
`φ`, and the nodes of the faces and of the edges of the cotree are isolated roots of value `0`. -/
theorem tree_storedL (hL : Layout M n ιv ιg ιf ιe) {T : DTree M.dual} (φ : D → ℤ)
    {vs ts : List V} (hOT : Orders T vs ts) :
    (treeOpsL T ιv ιg φ vs ts).length ≤ 6 * Fintype.card V ∧
      ValidOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts) ∧
      (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)).2 = [] ∧
      TRep n (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)).1 T ιv ιg
        (fun d => (φ (M.rev d) : ℝ)) 0 0 ∧
      Iso n (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)).1 T ιg ∧
      (∀ y, Agree (Forest.init n) (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)).1
        (ιf y)) ∧
      ∀ d, Agree (Forest.init n) (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)).1
        (ιe d) := by
  obtain ⟨hl, hv, ho, hR, hI, hag⟩ := build_trepL (C := T) hL.prim hL.hv
    (fun d => φ (M.rev d)) (fun _ => 0) (fun _ => 0) hOT (Fo := Forest.init n) (fun _ => rfl)
    (fun _ => rfl) (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
  refine ⟨hl, hv, ho, hR.congrβ (fun _ => by simp) (fun _ => by simp), hI,
    fun y => hag _ (fun x => (hL.vf x y).symm) (fun d => (hL.gf d y).symm),
    fun d => hag _ (fun x => (hL.ve x d).symm) (fun d' => (hL.ge d' d).symm)⟩

/-- **The initial stored data in given orders** (`init_stored`, the spanning tree first): from
the empty forest, `treeOpsL` then `cotOpsL`, at most `6 (#V + #F)` valid operations, printing
nothing, store the spanning tree `T` with the weights `φ` and the cotree `C` (its parent darts
off `T`) with the values `val` and the value `H₀` at the nodes of the faces. -/
theorem init_storedL (hL : Layout M n ιv ιg ιf ιe) {T : DTree M.dual} {C : DTree M}
    (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x)) (φ val : D → ℤ) (H₀ : ℤ) {vs ts : List V}
    (hOT : Orders T vs ts) {fs cs : List F} (hOC : Orders C fs cs) :
    (treeOpsL T ιv ιg φ vs ts ++ cotOpsL C ιf ιe val H₀ fs cs).length ≤
        6 * (Fintype.card V + Fintype.card F) ∧
      ValidOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts ++ cotOpsL C ιf ιe val H₀ fs cs) ∧
      (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts ++ cotOpsL C ιf ιe val H₀ fs cs)).2 =
        [] ∧
      Stored M n ιv ιg ιf ιe φ C.root H₀
        (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts ++ cotOpsL C ιf ιe val H₀ fs cs)).1
        T val := by
  obtain ⟨hl1, hv1, ho1, hR1, hI1, hagf, hage⟩ := tree_storedL hL φ hOT
  set F1 := (runOpsE n (Forest.init n) (treeOpsL T ιv ιg φ vs ts)).1 with hF1
  obtain ⟨hl2, hv2, ho2, hR2, hI2, hag2⟩ := build_trepL (C := C) hL.dual hL.hf val
    (fun _ => H₀) (fun _ => H₀) hOC (Fo := F1) (fun y => (hagf y).1) (fun d => (hage d).1)
    (fun y => ⟨(hagf y).2.1, (hagf y).2.2⟩) (fun d => ⟨(hage d).2.1, (hage d).2.2⟩)
  refine ⟨?_, (validOpsE_append n _ _ _).2 ⟨hv1, hv2⟩, ?_, ?_⟩
  · rw [List.length_append]; unfold cotOpsL; omega
  · rw [runOpsE_append, ho1]; exact ho2
  · rw [runOpsE_append]
    have hagv : ∀ x, Agree F1 (runOpsE n F1 (cotOpsL C ιf ιe val H₀ fs cs)).1 (ιv x) :=
      fun x => hag2 _ (hL.vf x) (hL.ve x)
    have hagg : ∀ d, Agree F1 (runOpsE n F1 (cotOpsL C ιf ιe val H₀ fs cs)).1 (ιg d) :=
      fun d => hag2 _ (hL.gf d) (hL.ge d)
    exact ⟨hR1.congr hagv hagg, hI1.congr hagg,
      ⟨C, fun _ => H₀, fun _ => H₀, rfl, hoff, hR2, hI2, fun _ => ⟨le_rfl, le_rfl⟩⟩,
      intF_runOpsE _ (intF_runOpsE _ (intF_init n))⟩

end Init

end Klein

end PlanarFlow
