module

public import PlanarFlow.STFlow.ProgKey
public import PlanarFlow.Klein.ProgExists

/-!
# The perturbed run stored in the dynamic trees

The data of the perturbed run (`PlanarFlow/STFlow/Lex.lean`) are the dual tree `T*` (a `DTree`
of the map, on the faces) and its cotree, a spanning tree of the graph. These are the two trees
of Klein's algorithm on the dual map: for the map `M.dual`, the spanning tree of Klein's program
(a `DTree` of `M.dual.dual`, which has the faces and the reverses of `M`) is `T*` (`toDD`), and
the dual cotree of Klein's program (a `DTree` of `M.dual`, on the vertices) is the cotree. So the
representation `PlanarFlow.Klein.Stored` (for `M.dual`) and the machine blocks of Klein's program
(`PlanarFlow.Klein.pivCore_orun`) apply as they are:

* `T*` is stored on the nodes `ιF` of the faces and `ιG` of its edges, with the values `w` of
  the darts, `w d = N c d + ε d` (the perturbed lengths, `wlen`), and `0` at the nodes of the
  faces;
* the cotree, rooted at the source `s`, on the nodes `ιV` of the vertices and `ιE` of its
  edges, with **the keys** `lkey N c ε g h` of the darts (`PlanarFlow/STFlow/ProgKey.lean`),
  the key of the dart towards the root as the first value of the node of its edge, the key of
  the dart away from the root as the second value; the values at the nodes of the vertices are
  at least a bound `Lo`.

* `lstored`: this representation of a state of the run.
* `stored_min2_at`: the query `min2` at the node of `t` below a threshold `z ≤ Lo` gives the dart
  of least key of the path of the cotree from `s` to `t`, the node of its edge, oriented by the
  parent of that node.
* `stored_min2_lt`: the least value is below the threshold when some dart of the path is.
* `aug_stored`: **the augmentation** (`add` of `z` and `add2` of `-z` at the node of `t`)
  subtracts `z χ` from the keys, `χ` the path of the cotree; the bound `Lo` drops by `|z|`.
* `anc_test`: **the test of the stop** (`add 1` at the node of the face `x`, the value of the
  node of the face `y`, `add (-1)` at the node of `x`): the value is `1` if `y` is an ancestor of
  `x` in `T*`, `0` otherwise, and the forest is restored.
* `pivotVal_key`: the values after a pivot of Klein's program with the amount `0` and the weights
  `w` are the keys of the state after the step.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW Klein DynTree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-! ### The dual tree as a tree of the dual of the dual -/

/-- A tree of the dual graph, as a tree of the map `M.dual.dual` (the same faces and reverses). -/
def toDD {M : CombMap D V F} (T : DTree M) : DTree M.dual.dual :=
  ⟨T.root, T.par, T.head_par, T.reach⟩

@[simp] lemma toDD_root {M : CombMap D V F} (T : DTree M) : (toDD T).root = T.root := rfl

@[simp] lemma toDD_par {M : CombMap D V F} (T : DTree M) : (toDD T).par = T.par := rfl

/-- The perturbed lengths `N c + ε`. -/
def wlen (N : ℤ) (c ε : D → ℤ) (d : D) : ℤ := N * c d + ε d

/-! ### Generic lemmas on the forest -/

section Generic

variable {M : CombMap D V F} {n : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ}

/-- **The query `min2` at the node of a face `x`**, for a cotree rooted at `fe`: below the
threshold, the least second value on the root path is the value of a dart of least value on the
path of the cotree from `fe` to `x`, whose edge node is the argmin, oriented by the parent of
that node; the two faces of that dart differ. -/
theorem stored_min2_at (hM : M.IsPlane) (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {fe : F}
    {Lo : ℝ} {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val) {z : ℤ} (hz : (z : ℝ) ≤ Lo) (x : F)
    (h : (pathMin2 Fo n (ιf x)).1 < z) :
    ∃ d, (pathMin2 Fo n (ιf x)).2 = ιe d ∧ (pathMin2 Fo n (ιf x)).1 = val d ∧
      Fo.par (ιe d) = ιf (M.face d) ∧ M.face d ≠ M.face (M.rev d) ∧
      T.chi fe x d = 1 ∧ ∀ d', T.chi fe x d' = 1 → val d ≤ val d' := by
  obtain ⟨C, β, β₂, hroot, hoff, hR, -, hLo⟩ := hS.cot
  have hβ : ∀ y, (z : ℝ) ≤ β₂ y := fun y => hz.trans (hLo y).2
  obtain ⟨h1, -⟩ := lct_minpath hM hoff hR hL.dual.f_lt hL.dual.e_lt hL.hf hβ x
  rw [hroot] at h1
  obtain ⟨d, hd, hpar, hchi, -, hmin⟩ := h1 h
  obtain ⟨i, hi, hir, h2', h1', -⟩ := pathMin2_rep hR hL.dual.f_lt hL.dual.e_lt hL.hf
    x fun y => lt_of_lt_of_le h (hβ y)
  have : C.par (C.up^[i] x) = d := by
    rcases hL.dual.e_eq _ _ (hd.symm.trans h2') with h | h
    · exact h
    · exfalso
      set y := C.up^[i] x with hy
      have hp := hR.pe _ hir
      rw [h, hL.dual.e_rev, hpar] at hp
      have hf := hL.dual.f_inj hp
      have hrr := C.head_par _ hir
      rw [h, M.rev_rev] at hrr
      have hup : C.up y = y := by rw [C.up_of_ne hir, h, ← hf, hrr]
      have hdep := C.depth_up hir
      rw [hup] at hdep
      omega
  refine ⟨d, hd, by rw [h1', this], hpar, fun hff => ?_, hchi, hmin⟩
  have hrr := C.head_par _ hir
  have hup : C.up (C.up^[i] x) = C.up^[i] x := by
    rw [C.up_of_ne hir, this, hff, ← this, hrr]
  have hdep := C.depth_up hir
  rw [hup] at hdep
  omega

/-- **The query `min2` is below the threshold** when some dart of the path of the cotree from
`fe` to `x` has a value below it. -/
theorem stored_min2_lt (hM : M.IsPlane) (hL : Layout M n ιv ιg ιf ιe) {φ : D → ℤ} {fe : F}
    {Lo : ℝ} {Fo : Forest} {T : DTree M.dual} {val : D → ℤ}
    (hS : Stored M n ιv ιg ιf ιe φ fe Lo Fo T val) {z : ℤ} (hz : (z : ℝ) ≤ Lo) (x : F) {d : D}
    (hd : T.chi fe x d = 1) (hdz : val d < z) : (pathMin2 Fo n (ιf x)).1 < z := by
  obtain ⟨C, β, β₂, hroot, hoff, hR, -, hLo⟩ := hS.cot
  have hβ : ∀ y, (z : ℝ) ≤ β₂ y := fun y => hz.trans (hLo y).2
  obtain ⟨-, h2⟩ := lct_minpath hM hoff hR hL.dual.f_lt hL.dual.e_lt hL.hf hβ x
  rw [hroot] at h2
  by_contra h
  have := h2 h d hd
  omega

/-- Adding `z` and then `-z` along a root path restores the forest. -/
lemma addPath_addPath_neg (Fo : Forest) (n v : ℕ) (z : ℝ) :
    addPath (addPath Fo n v z) n v (-z) = Fo := by
  have hp : rootPath (addPath Fo n v z) n v = rootPath Fo n v :=
    rootPath_congr (Fo := Fo) (Fo' := addPath Fo n v z) rfl v
  cases Fo with
  | mk par val val2 =>
    simp only [addPath, Forest.mk.injEq, true_and, and_true] at hp ⊢
    funext u
    rw [hp]
    split_ifs <;> ring

open Classical in
/-- **The ancestor test**: in a forest storing `T` with values `0` at the nodes of the faces,
after adding `1` along the root path of the node of `x`, the value of the node of `y` is `1` if
`y` is an ancestor of `x`, `0` otherwise. -/
lemma anc_val {N : CombMap D V F} {C : DTree N} {κ : D → ℝ} {β₂ : F → ℝ} {Fo : Forest}
    (hR : TRep n Fo C ιf ιe κ 0 β₂) (hN : Nodes n N ιf ιe) (hn : 2 * Fintype.card F ≤ n)
    (x y : F) :
    (addPath Fo n (ιf x) 1).val (ιf y) = if C.Anc y x then 1 else 0 := by
  have hrp := rootPath_rep hR hN.f_lt hN.e_lt hn x
  have hv := hR.vf y
  simp only [Pi.zero_apply] at hv
  simp only [addPath, hrp, mem_tpath_face hN, hv]
  have : (∃ i ≤ C.depth x, C.up^[i] x = y) ↔ C.Anc y x := by
    constructor
    · rintro ⟨i, -, h⟩; exact ⟨i, h⟩
    · rintro ⟨i, h⟩
      by_cases hi : i ≤ C.depth x
      · exact ⟨i, hi, h⟩
      · refine ⟨C.depth x, le_rfl, ?_⟩
        rw [C.iterate_depth, ← h, C.iterate_of_le (by omega)]
  simp only [this]
  split_ifs <;> ring

end Generic

/-! ### The stored state of the perturbed run -/

variable {M : CombMap D V F} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ} {ιV : V → ℕ} {ιE : D → ℕ}

variable (M n ιF ιG ιV ιE) in
/-- **A state of the perturbed run stored in the forest** `Fo`: `T*` with the perturbed lengths
`w = N c + ε`, the cotree rooted at `s` with the keys, the values at the nodes of the vertices at
least `Lo` (`PlanarFlow.Klein.Stored` for the dual map). -/
def LStored (N : ℤ) (c ε : D → ℤ) (s : V) (Lo : ℝ) (Fo : Forest) (st : LSt M) : Prop :=
  Stored M.dual n ιF ιG ιV ιE (wlen N c ε) s Lo Fo (toDD st.T) (lkey N c ε st.g st.h)

/-- **The augmentation on the stored cotree**: `add z` and `add2 (-z)` at the node of `t`
subtract `z χ` from the values of the darts (`χ` the path of the cotree from `s` to `t`), keep
the stored dual tree, and lower the bound at the nodes of the vertices by `|z|`. -/
theorem aug_stored (hM : M.IsPlane) (hL : Layout M.dual n ιF ιG ιV ιE) {φ : D → ℤ} {s : V}
    {Lo : ℝ} {Fo : Forest} {T : DTree M} {κ : D → ℤ}
    (hS : Stored M.dual n ιF ιG ιV ιE φ s Lo Fo (toDD T) κ) (t : V) (z : ℤ) :
    Stored M.dual n ιF ιG ιV ιE φ s (Lo - |(z : ℝ)|)
      (runOpsE n Fo [.add (ιV t) z, .add2 (ιV t) (-z)]).1 (toDD T)
      (fun d => κ d - z * T.chi s t d) := by
  obtain ⟨C, β, β₂, hroot, hoff, hR, hI, hLo⟩ := hS.cot
  have hrun : (runOpsE n Fo [.add (ιV t) z, .add2 (ιV t) (-z)]).1 =
      addPath2 (addPath Fo n (ιV t) (z : ℝ)) n (ιV t) (-(z : ℝ)) := by
    simp [runOpsE, EOp.apply]
  have h1 := addBoth_trep hR hL.dual hL.hf t (z : ℝ)
  have i1 := addBoth_iso hR hI hL.dual hL.hf t (z : ℝ)
  have hchi : pflow C t = (toDD T).chi C.root t := (chi_eq_pflow hM.dual (toDD T) C hoff t).symm
  rw [hroot] at hchi
  have hag : ∀ u, (∀ x, u ≠ ιV x) → (∀ d, u ≠ ιE d) →
      Agree Fo (addPath2 (addPath Fo n (ιV t) (z : ℝ)) n (ιV t) (-(z : ℝ))) u :=
    fun u h1 h2 => ⟨(i1.2 u h1 h2).1, (i1.2 u h1 h2).2.1, (i1.2 u h1 h2).2.2⟩
  have hint := intF_runOpsE (n := n) [.add (ιV t) z, .add2 (ιV t) (-z)] hS.int
  rw [hrun] at hint ⊢
  refine ⟨hS.tree.congr (fun x => hag _ (fun v => (hL.vf x v)) (fun d => hL.ve x d))
      (fun d => hag _ (fun v => hL.gf d v) (fun d' => hL.ge d d')),
    hS.treeIso.congr (fun d => hag _ (fun v => hL.gf d v) (fun d' => hL.ge d d')),
    ⟨C, _, _, hroot, hoff, h1.congrκ fun d => ?_, i1.1, fun x => ?_⟩, hint⟩
  · rw [hchi]; push_cast; rfl
  · have hl := hLo x
    have hz1 := le_abs_self (z : ℝ)
    have hz2 := neg_abs_le (z : ℝ)
    split_ifs <;> constructor <;> linarith

open Classical in
/-- **The ancestor test on the stored dual tree**: adding `1` along the root path of the node of
the face `x` gives the node of the face `y` the value `1` if `y` is an ancestor of `x` in `T`,
`0` otherwise; adding `-1` then restores the forest. -/
theorem anc_test (hL : Layout M.dual n ιF ιG ιV ιE) {φ : D → ℤ} {s : V} {Lo : ℝ}
    {Fo : Forest} {T : DTree M} {κ : D → ℤ}
    (hS : Stored M.dual n ιF ιG ιV ιE φ s Lo Fo (toDD T) κ) (x y : F) :
    (runOpsE n Fo [.add (ιF x) 1]).1.val (ιF y) = (if T.Anc y x then 1 else 0) ∧
      runOpsE n Fo [.add (ιF x) 1, .add (ιF x) (-1)] = (Fo, []) := by
  refine ⟨?_, ?_⟩
  · have := anc_val hS.tree hL.prim hL.hv x y
    have e : (runOpsE n Fo [.add (ιF x) 1]).1 = addPath Fo n (ιF x) 1 := by
      simp [runOpsE, EOp.apply]
    rw [e, this]; rfl
  · have := addPath_addPath_neg Fo n (ιF x) 1
    simp only [runOpsE, EOp.apply, EOp.answer, List.append_nil, Prod.mk.injEq, and_true]
    push_cast
    exact this

/-- **The values after a pivot with the amount `0` and the weights `w`** are the keys of the
state: the old parent dart `a` of the face `y` was saturated in both coordinates (key `0`), its
reverse gets `w a + w (rev a)`. -/
theorem pivotVal_key {N : ℤ} {c ε : D → ℤ} {s t : V} {st : LSt M} (hI : LInv c ε s t st)
    {y : F} (hy : y ≠ st.T.root) (g' h' : D → ℤ) (hg : ∀ d, st.T.InT d → g' d = st.g d)
    (hh : ∀ d, st.T.InT d → h' d = st.h d) :
    pivotVal (toDD st.T) (wlen N c ε) (wlen N c ε) (lkey N c ε g' h') y 0 =
      lkey N c ε g' h' := by
  funext d
  have ha := st.T.inT_par hy
  have hra := st.T.inT_rev ha
  have hsg := hI.base.sat y hy
  have hsh := hI.sat y hy
  have hanti := hI.base.pseudo.antisymm (st.T.par y)
  have hantih := hI.antisymm (st.T.par y)
  simp only [LSt.base_g, LSt.base_T] at hsg hanti
  unfold pivotVal
  simp only [toDD_par, show M.dual.rev = M.rev from rfl]
  by_cases h1 : d = st.T.par y
  · rw [ite_eq_left h1, h1]
    simp only [lkey, wlen, hg _ ha, hh _ ha, hsg, hsh]; ring
  · rw [ite_eq_right h1]
    by_cases h2 : d = M.rev (st.T.par y)
    · rw [ite_eq_left h2, h2]
      simp only [lkey, wlen, hg _ hra, hh _ hra, hanti, hantih, hsg, hsh]; ring
    · rw [ite_eq_right h2]; ring

end STFlow

end PlanarFlow
