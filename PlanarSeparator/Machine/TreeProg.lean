module

public import PlanarSeparator.Machine.SplitWProg

/-!
# The separator tree on the machine

**`PlanarSeparator.Piece.treeProg`** computes `PlanarSeparator.SepRoutine.buildAux` of the square
of `G` with the separator `sqSep` of the square (`squareProg`), as a worklist in preorder calling
`splitWProg` at every node; all vertex lists of the pending subtrees live in one area
`[base, base + N)` (the two parts of a split are written by `splitWProg` in place of the list of
the node), the frames `(start, size, fuel)` in a stack at `aT`.

The tree is **printed** in preorder (`tenc`): a leaf `s` as `0, #s, s` and a node with separator
`s` as `1, #s, s` followed by the two subtrees, each set as its sorted list of vertex numbers.

* `tenc`, `tcost` (the cost along the tree: per leaf `6 m + 21`, per node the bound of
  `splitWProg_spec` plus `6 #S + 45`).
* `SWB.congr`, `prList_exec` (printing a list from memory).
* **`treeProg_spec`**: from the state between splits `SWB` and the sorted list of `U` at
  `base`, the program prints `tenc (buildAux (square G) (sqSep hR hΔ) (ord N) T k U)`, within
  `tcost … k U + 8` steps; the state between splits holds again.
* **`treeProg_buildTree`**: the same for `U = univ`, fuel `N`: `buildTree`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset NestedDissection WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
open NestedDissection.SepTree

variable {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj] {W : ℕ} {P : Input}

/-! ### The encoding of a tree -/

/-- The sorted list of the vertex numbers of `U`. -/
def lvs (U : Finset (Fin N)) : List ℕ := (List.range #U).map (lv U)

theorem length_lvs (U : Finset (Fin N)) : (lvs U).length = #U := by simp [lvs]

/-- **The preorder encoding of a separator tree**: a leaf `s` as `0, #s, s`, a node as
`1, #s, s` (the separator) followed by the encodings of the two subtrees. -/
def tenc : SepTree (Fin N) → List ℕ
  | leaf s => 0 :: #s :: lvs s
  | node s a b => 1 :: #s :: (lvs s ++ tenc a ++ tenc b)

/-! ### The state between splits is stable -/

theorem SWB.congr {R : Kasteleyn.RotationSystem G}
    {Z M aS aP aV aF aZ aCW aCB aSn aJ : ℕ} {c d : Config}
    (h : SWB G R Z W M aS aP aV aF aZ aCW aCB aSn aJ c) (hw : WordsBounded W d)
    (hr : ∀ r < 1420, d.nreg r = c.nreg r) (hm : ∀ a < aJ + N, d.nmem a = c.nmem a)
    (hrr : d.rreg = c.rreg) (hrm : d.rmem = c.rmem) :
    SWB G R Z W M aS aP aV aF aZ aCW aCB aSn aJ d := by
  have hb := h.base
  have := hb.lB; have := hb.lF; have := hb.lV; have := hb.lA
  have := h.lay1; have := h.lay2; have := h.lay3; have := h.lay4; have := h.lay5
  have := h.lay6; have := h.lay7; have := h.lay8; have := h.lay9; have := h.lay10
  have e1203 := hr 1203 (by omega)
  exact
    { base := hb.congr hw (fun r hr' _ => by unfold KeptS at hr'; exact hr r (by omega))
        (fun a ha => hm a (by omega)) hrr hrm
      rS := by rw [hr 1310 (by omega)]; exact h.rS
      rP := by rw [hr 1311 (by omega)]; exact h.rP
      rV := by rw [hr 1312 (by omega)]; exact h.rV
      rF := by rw [hr 1313 (by omega)]; exact h.rF
      rZ := by rw [hr 1390 (by omega)]; exact h.rZ
      rCW := by rw [hr 1391 (by omega)]; exact h.rCW
      rCB := by rw [hr 1392 (by omega)]; exact h.rCB
      rSn := by rw [hr 1393 (by omega)]; exact h.rSn
      rJ := by rw [hr 1394 (by omega)]; exact h.rJ
      lay1 := by rw [e1203]; exact h.lay1
      lay2 := h.lay2, lay3 := h.lay3, lay4 := h.lay4, lay5 := h.lay5, lay6 := h.lay6
      lay7 := h.lay7, lay8 := h.lay8, lay9 := h.lay9, lay10 := h.lay10
      hMN := h.hMN, hM := h.hM
      zZ := fun x hx => by rw [hm _ (by omega)]; exact h.zZ x hx
      zCW := fun x hx => by rw [hm _ (by omega)]; exact h.zCW x hx
      zCB := fun x hx => by rw [hm _ (by omega)]; exact h.zCB x hx
      zSn := fun x hx => by rw [hm _ (by omega)]; exact h.zSn x hx
      zJ := fun x hx => by rw [hm _ (by omega)]; exact h.zJ x hx }

/-! ### Printing a list from memory -/

/-- One word of the list at `nreg 1435` printed (counter `1433`). -/
def prBody : Stmt := block [.addN 1429 1435 1433, .loadN 1434 1429, .outN 1434,
  .addN 1433 1433 1001]

/-- **Printing** the `nreg 1436` words at `nreg 1435` (the counter `1433` starts at `0`). -/
def prList : Stmt := .whileLtN 1433 1436 prBody

theorem prList_exec {d : Config} (hw : WordsBounded W d) {a n : ℕ} {f : ℕ → ℕ}
    (h01 : d.nreg 1001 = 1) (h35 : d.nreg 1435 = a) (h36 : d.nreg 1436 = n)
    (h33 : d.nreg 1433 = 0) (hv : ∀ j < n, d.nmem (a + j) = f j) (ha : a + n ≤ W) :
    ∃ d' k, Exec P W prList d d' k ∧ WordsBounded W d' ∧
      d'.output = d.output ++ (List.range n).map f ∧ d'.nmem = d.nmem ∧
      (∀ r, r ≠ 1429 → r ≠ 1433 → r ≠ 1434 → d'.nreg r = d.nreg r) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ k ≤ 6 * n + 2 := by
  let I : ℕ → Config → Prop := fun j d' => WordsBounded W d' ∧ d'.nreg 1433 = j ∧
    d'.nreg 1436 = n ∧ d'.output = d.output ++ (List.range j).map f ∧ d'.nmem = d.nmem ∧
    (∀ r, r ≠ 1429 → r ≠ 1433 → r ≠ 1434 → d'.nreg r = d.nreg r) ∧
    d'.rreg = d.rreg ∧ d'.rmem = d.rmem
  obtain ⟨d₁, k₁, e₁, h₁, hk₁⟩ := Exec.forN (P := P) (W := W) (ri := 1433) (rN := 1436)
    (N := n) (lo := 0) (B := 4) (body := prBody) I (fun i d' h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun i d' h hi => by
      obtain ⟨hw', h33', h36', ho, hm, hq, hrr, hrm⟩ := h
      have r35 : d'.nreg 1435 = a := by rw [hq 1435 (by omega) (by omega) (by omega), h35]
      have r1 : d'.nreg 1001 = 1 := by rw [hq 1001 (by omega) (by omega) (by omega), h01]
      unfold prBody
      exec_block
      · rw [r35, h33']; omega
      · config_simp; rw [h33', r1]; omega
      · refine ⟨⟨‹WordsBounded _ _›, by config_simp; rw [h33', r1], by config_simp; exact h36',
          ?_, by config_simp; exact hm, fun r a b c' => ?_, by config_simp; exact hrr,
          by config_simp; exact hrm⟩, by omega⟩
        · config_simp
          rw [ho, r35, h33', hm, hv i hi, List.range_succ, List.map_append, List.append_assoc]
          rfl
        · simp only [upd_apply, a, b, c', ite_false]; exact hq r a b c')
    (Nat.zero_le _) ⟨hw, h33, h36, by simp, rfl, fun _ _ _ _ => rfl, rfl, rfl⟩
  obtain ⟨hw₁, -, -, ho₁, hm₁, hq₁, hr₁, hrm₁⟩ := h₁
  exact ⟨d₁, k₁, e₁, hw₁, ho₁, hm₁, hq₁, hr₁, hrm₁, by omega⟩

/-! ### The worklist -/

/-- The parts of the split are a partition of a subset of `U`. -/
theorem splitW_card_le (U : Finset (Fin N))
    (sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N)) :
    #(SepRoutine.splitW (square G) sep (ord N) U).2.1 +
      #(SepRoutine.splitW (square G) sep (ord N) U).2.2 ≤ #U := by
  simp only [SepRoutine.splitW]
  rw [card_filter_add_card_filter_not]
  exact card_le_card sdiff_subset

theorem splitW_fst_subset (U : Finset (Fin N))
    (sep : Finset (Fin N) → (Fin N → ℕ) → Finset (Fin N) × Finset (Fin N) × Finset (Fin N)) :
    (SepRoutine.splitW (square G) sep (ord N) U).1 ⊆ U := by
  simp only [SepRoutine.splitW]
  exact inter_subset_left

variable (G) in
/-- The subtree of `buildAux` built by the machine. -/
noncomputable abbrev tTree {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (T k : ℕ) (U : Finset (Fin N)) : SepTree (Fin N) :=
  SepRoutine.buildAux (square G) (sqSep hR hΔ) (ord N) T k U

/-- The cost of a split round, without the subtrees. -/
noncomputable def scost {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (U : Finset (Fin N)) : ℕ :=
  430 * N + 362 + 22 * ∑ v ∈ closedNbhd G U, G.degree v +
    dcost (sqSep hR hΔ) (spMu (square G) U) (spL (square G) U) Δ
      #(closedNbhd G (closedNbhd G U)) (closedNbhd G (closedNbhd G U)) +
    6 * #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).1 + 45

/-- **The cost of the machine along the tree** `buildAux … T k U`: `6 m + 21` per leaf with `m`
vertices, `scost` per node. -/
noncomputable def tcost {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (T : ℕ) : ℕ → Finset (Fin N) → ℕ
  | 0, U => 6 * #U + 21
  | k + 1, U =>
    if #U ≤ T ^ 2 then 6 * #U + 21
    else scost hR hΔ U + tcost hR hΔ T k (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.1 + tcost hR hΔ T k (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.2

theorem tTree_leaf {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {T k : ℕ} {U : Finset (Fin N)} (h : k = 0 ∨ #U ≤ T ^ 2) :
    tTree G hR hΔ T k U = leaf U ∧ tcost hR hΔ T k U = 6 * #U + 21 := by
  rcases k with _ | k
  · exact ⟨rfl, rfl⟩
  · have h' : #U ≤ T ^ 2 := by omega
    simp only [tTree, SepRoutine.buildAux, tcost, h', ↓reduceIte, and_self]

theorem tTree_node {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) {T k : ℕ} {U : Finset (Fin N)} (h : ¬ #U ≤ T ^ 2) :
    tTree G hR hΔ T (k + 1) U = node (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).1 (tTree G hR hΔ T k (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.1)
      (tTree G hR hΔ T k (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.2) ∧
    tcost hR hΔ T (k + 1) U = scost hR hΔ U + tcost hR hΔ T k (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.1 +
      tcost hR hΔ T k (SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) U).2.2 := by
  simp only [tTree, SepRoutine.buildAux, tcost, h, ↓reduceIte, and_self]

/-- The pending subtrees: `m` frames, frame `i` with vertex set `U i`, fuel `k i` and its list
at `s i` (frame `m - 1` on top). -/
structure TFr (N : ℕ) where
  /-- The number of frames. -/
  m : ℕ
  /-- The vertex sets. -/
  U : ℕ → Finset (Fin N)
  /-- The fuels. -/
  k : ℕ → ℕ
  /-- The positions of the lists. -/
  s : ℕ → ℕ

/-- The words still to be printed for the frames: their encodings from the top. -/
noncomputable def TFr.rem {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (T : ℕ) (a : TFr N) : List ℕ :=
  ((List.range a.m).reverse.map fun i => tenc (tTree G hR hΔ T (a.k i) (a.U i))).flatten

/-- The cost still to come for the frames. -/
noncomputable def TFr.pot {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (T : ℕ) (a : TFr N) : ℕ :=
  ∑ i ∈ range a.m, tcost hR hΔ T (a.k i) (a.U i)

section frames

variable {R : Kasteleyn.RotationSystem G} (hR : R.IsPlane) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
  (T : ℕ)

theorem TFr.rem_congr {a b : TFr N} (hm : a.m = b.m)
    (h : ∀ i < a.m, a.U i = b.U i ∧ a.k i = b.k i) :
    a.rem (G := G) hR hΔ T = b.rem hR hΔ T := by
  unfold TFr.rem
  rw [← hm]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < a.m := by simpa using hi
  rw [(h i hi').1, (h i hi').2]

theorem TFr.pot_congr {a b : TFr N} (hm : a.m = b.m)
    (h : ∀ i < a.m, a.U i = b.U i ∧ a.k i = b.k i) :
    a.pot (G := G) hR hΔ T = b.pot hR hΔ T := by
  unfold TFr.pot
  rw [← hm]
  exact sum_congr rfl fun i hi => by
    have hi' : i < a.m := mem_range.1 hi
    rw [(h i hi').1, (h i hi').2]

theorem TFr.rem_succ (a : TFr N) {i : ℕ} (hm : a.m = i + 1) :
    a.rem (G := G) hR hΔ T =
      tenc (tTree G hR hΔ T (a.k i) (a.U i)) ++ (⟨i, a.U, a.k, a.s⟩ : TFr N).rem hR hΔ T := by
  simp only [TFr.rem, hm, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.map_cons, List.singleton_append, List.flatten_cons]

theorem TFr.pot_succ (a : TFr N) {i : ℕ} (hm : a.m = i + 1) :
    a.pot (G := G) hR hΔ T =
      tcost hR hΔ T (a.k i) (a.U i) + (⟨i, a.U, a.k, a.s⟩ : TFr N).pot hR hΔ T := by
  simp only [TFr.pot, hm, sum_range_succ]
  omega

end frames

/-- The layout of the tree program: the parameters of `SWB`, the stack `aT`, the output buffer
`aO` of the splits, the list area `base`, the bound `k0` of the fuels. -/
structure TL where
  Z : ℕ
  M : ℕ
  aS : ℕ
  aP : ℕ
  aV : ℕ
  aF : ℕ
  aZ : ℕ
  aCW : ℕ
  aCB : ℕ
  aSn : ℕ
  aJ : ℕ
  aT : ℕ
  aO : ℕ
  base : ℕ
  k0 : ℕ

variable (G W) in
/-- **The worklist state** of the tree program (without the frame count `1428`): the state
between splits, `T²` in `1426`, the stack base in `1427`, the output buffer in `1437`, the
layout, the frames (lists in `[base, base + N)`, disjoint, the lower frames higher), the output
so far followed by the words still to be printed is `goal`, the kept registers and memory
relative to the start `c0`. -/
structure TCore (R : Kasteleyn.RotationSystem G) (hR : R.IsPlane) {Δ : ℕ}
    (hΔ : ∀ v, G.degree v ≤ Δ) (T : ℕ) (L : TL) (goal : List ℕ) (c0 : Config) (a : TFr N)
    (c : Config) : Prop where
  swb : SWB G R L.Z W L.M L.aS L.aP L.aV L.aF L.aZ L.aCW L.aCB L.aSn L.aJ c
  rT2 : c.nreg 1426 = T ^ 2
  rT : c.nreg 1427 = L.aT
  rO : c.nreg 1437 = L.aO
  lO : L.aJ + N ≤ L.aO
  lO' : L.aO + N ≤ L.base
  lB : L.base + N ≤ L.aT
  lT : L.aT + 3 * (L.k0 + 1) + N ≤ W
  fr : ∀ i < a.m, c.nmem (L.aT + 3 * i) = a.s i ∧ c.nmem (L.aT + 3 * i + 1) = #(a.U i) ∧
    c.nmem (L.aT + 3 * i + 2) = a.k i ∧ (∀ j < #(a.U i), c.nmem (a.s i + j) = lv (a.U i) j) ∧
    L.base ≤ a.s i ∧ a.s i + #(a.U i) ≤ L.base + N ∧ a.k i + i ≤ L.k0
  ord : ∀ i j, i < j → j < a.m → a.s j + #(a.U j) ≤ a.s i
  out : c.output ++ a.rem hR hΔ T = goal
  keep : ∀ r, (KeptS r ∧ r ≠ 1201) ∨ 1438 ≤ r → c.nreg r = c0.nreg r
  mem : ∀ x, L.aJ + N ≤ x → (x < L.aO ∨ L.aO + N ≤ x) → (x < L.base ∨ L.base + N ≤ x) →
    (x < L.aT ∨ L.aT + 3 * (L.k0 + 1) ≤ x) → c.nmem x = c0.nmem x

section core

variable {R : Kasteleyn.RotationSystem G} {hR : R.IsPlane} {Δ : ℕ} {hΔ : ∀ v, G.degree v ≤ Δ}
  {T : ℕ} {L : TL} {goal : List ℕ} {c0 : Config}

/-- `TCore` for fewer frames, after steps keeping the memory and printing the encodings of the
removed frames. -/
theorem TCore.restrict {a : TFr N} {c d : Config} (h : TCore G W R hR hΔ T L goal c0 a c)
    (hw : WordsBounded W d)
    (hr : ∀ r, (r < 1420 ∨ r = 1426 ∨ r = 1427 ∨ 1437 ≤ r) → d.nreg r = c.nreg r)
    (hm : d.nmem = c.nmem) (hrr : d.rreg = c.rreg) (hrm : d.rmem = c.rmem) {a' : TFr N}
    (hm' : a'.m ≤ a.m) (hU : ∀ i < a'.m, a'.U i = a.U i ∧ a'.k i = a.k i ∧ a'.s i = a.s i)
    (hout : d.output ++ a'.rem hR hΔ T = goal) : TCore G W R hR hΔ T L goal c0 a' d where
  swb := h.swb.congr hw (fun r hr' => hr r (Or.inl hr')) (fun x _ => by rw [hm]) hrr hrm
  rT2 := by rw [hr 1426 (by omega)]; exact h.rT2
  rT := by rw [hr 1427 (by omega)]; exact h.rT
  rO := by rw [hr 1437 (by omega)]; exact h.rO
  lO := h.lO
  lO' := h.lO'
  lB := h.lB
  lT := h.lT
  fr := fun i hi => by
    obtain ⟨e1, e2, e3⟩ := hU i hi
    rw [hm, e1, e2, e3]; exact h.fr i (by omega)
  ord := fun i j hij hj => by
    obtain ⟨-, -, e3⟩ := hU i (by omega)
    obtain ⟨f1, -, f3⟩ := hU j hj
    rw [e3, f1, f3]; exact h.ord i j hij (by omega)
  out := hout
  keep := fun r hr' => by
    rw [hr r (by rcases hr' with ⟨h1, -⟩ | h1 <;> [(unfold KeptS at h1; omega); omega])]
    exact h.keep r hr'
  mem := fun x h1 h2 h3 h4 => by rw [hm]; exact h.mem x h1 h2 h3 h4

/-! ### The programs -/

/-- The removal of the top frame: `nreg 1430`, `1431`, `1432` := start, size, fuel. -/
def tPop : Stmt := block [.subN 1428 1428 1001, .addN 1429 1428 1428, .addN 1429 1429 1428,
  .addN 1429 1429 1427, .loadN 1430 1429, .addN 1429 1429 1001, .loadN 1431 1429,
  .addN 1429 1429 1001, .loadN 1432 1429]

/-- A leaf: `0, #s`, then the list of `s`. -/
def tLeaf : Stmt := .seq (block [.outN 0, .outN 1431, .copyN 1435 1430, .copyN 1436 1431,
  .constN 1433 0]) prList

/-- The two frames of the parts: the second part at the place of the removed frame, the first
part on top. -/
def tPush : Stmt := block [.subN 1432 1432 1001,
  .addN 1429 1428 1428, .addN 1429 1429 1428, .addN 1429 1429 1427,
  .addN 1434 1430 1424, .storeN 1429 1434,
  .addN 1429 1429 1001, .storeN 1429 1425,
  .addN 1429 1429 1001, .storeN 1429 1432,
  .addN 1429 1429 1001, .storeN 1429 1430,
  .addN 1429 1429 1001, .storeN 1429 1424,
  .addN 1429 1429 1001, .storeN 1429 1432,
  .addN 1428 1428 1001, .addN 1428 1428 1001]

/-- A node: the split, `1, #S`, the list of `S`, the two frames. -/
def tSplit : Stmt := .seq (block [.copyN 1420 1430, .copyN 1421 1431, .copyN 1422 1437])
  (.seq splitWProg (.seq (block [.outN 1001, .outN 1423, .copyN 1435 1437, .copyN 1436 1423,
    .constN 1433 0]) (.seq prList tPush)))

/-- A round of the worklist. -/
def tBody : Stmt := .seq tPop (.ifLtN 0 1432 (.ifLtN 1426 1431 tSplit tLeaf) tLeaf)

/-- The worklist loop. -/
def treeLoop : Stmt := .whileLtN 0 1428 tBody

/-- **The tree program**: the first frame (start `nreg 1430`, size `1431`, fuel `1432`), the
loop. -/
def treeProg : Stmt := .seq (block [.storeN 1427 1430, .addN 1429 1427 1001, .storeN 1429 1431,
  .addN 1429 1429 1001, .storeN 1429 1432, .copyN 1428 1001]) treeLoop

theorem tPop_exec {a : TFr N} {c : Config} (h : TCore G W R hR hΔ T L goal c0 a c)
    (hm : c.nreg 1428 = a.m) (h0 : 0 < a.m) :
    ∃ c₁ k, Exec P W tPop c c₁ k ∧ k = 9 ∧ TCore G W R hR hΔ T L goal c0 a c₁ ∧
      c₁.nreg 1428 = a.m - 1 ∧ c₁.nreg 1430 = a.s (a.m - 1) ∧
      c₁.nreg 1431 = #(a.U (a.m - 1)) ∧ c₁.nreg 1432 = a.k (a.m - 1) := by
  have hb := h.swb.base
  have hw := hb.wb
  have := h.lT
  have h01 := hb.one
  obtain ⟨f0, f1, f2, -, -, -, fk⟩ := h.fr (a.m - 1) (by omega)
  obtain ⟨c₁, k₁, e₁, hk₁, hw₁, m₁, s₁, n₁, k₁', nm₁, q₁, ou₁, rr₁, rm₁⟩ : ∃ c₁ k₁,
      Exec P W tPop c c₁ k₁ ∧ k₁ = 9 ∧ WordsBounded W c₁ ∧ c₁.nreg 1428 = a.m - 1 ∧
      c₁.nreg 1430 = a.s (a.m - 1) ∧ c₁.nreg 1431 = #(a.U (a.m - 1)) ∧
      c₁.nreg 1432 = a.k (a.m - 1) ∧ c₁.nmem = c.nmem ∧
      (∀ r, r ≠ 1428 → r ≠ 1429 → r ≠ 1430 → r ≠ 1431 → r ≠ 1432 → c₁.nreg r = c.nreg r) ∧
      c₁.output = c.output ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem := by
    unfold tPop
    exec_block
    · config_simp; rw [hm, h01]; omega
    · config_simp; rw [hm, h01]; omega
    · config_simp; rw [hm, h01, h.rT]; omega
    · config_simp; rw [hm, h01, h.rT]; omega
    · config_simp; rw [hm, h01, h.rT]; omega
    · refine ⟨rfl, ‹_›, by config_simp; rw [hm, h01], ?_, ?_, ?_, rfl, ?_, rfl, rfl, rfl⟩
      · config_simp; rw [hm, h01, h.rT]
        rw [show a.m - 1 + (a.m - 1) + (a.m - 1) + L.aT = L.aT + 3 * (a.m - 1) by omega]
        exact f0
      · config_simp; rw [hm, h01, h.rT]
        rw [show a.m - 1 + (a.m - 1) + (a.m - 1) + L.aT + 1 = L.aT + 3 * (a.m - 1) + 1 by
          omega]
        exact f1
      · config_simp; rw [hm, h01, h.rT]
        rw [show a.m - 1 + (a.m - 1) + (a.m - 1) + L.aT + 1 + 1 = L.aT + 3 * (a.m - 1) + 2 by
          omega]
        exact f2
      · intro r h1 h2 h3 h4 h5; simp [h1, h2, h3, h4, h5]
  refine ⟨c₁, k₁, e₁, hk₁, h.restrict hw₁ (fun r hr => q₁ r (by omega) (by omega) (by omega)
    (by omega) (by omega)) nm₁ rr₁ rm₁ le_rfl (fun i _ => ⟨rfl, rfl, rfl⟩)
    (by rw [ou₁]; exact h.out), m₁, s₁, n₁, k₁'⟩

/-- A leaf round after the pop. -/
theorem tLeafCase {a : TFr N} {c : Config} (h : TCore G W R hR hΔ T L goal c0 a c)
    (h0 : 0 < a.m) (hlf : a.k (a.m - 1) = 0 ∨ #(a.U (a.m - 1)) ≤ T ^ 2)
    (h28 : c.nreg 1428 = a.m - 1) (h30 : c.nreg 1430 = a.s (a.m - 1))
    (h31 : c.nreg 1431 = #(a.U (a.m - 1))) :
    ∃ c' k, Exec P W tLeaf c c' k ∧ k + 14 ≤ tcost hR hΔ T (a.k (a.m - 1)) (a.U (a.m - 1)) ∧
      TCore G W R hR hΔ T L goal c0 ⟨a.m - 1, a.U, a.k, a.s⟩ c' ∧ c'.nreg 1428 = a.m - 1 := by
  have hb := h.swb.base
  have hw := hb.wb
  have := h.lT; have := h.lB
  have h01 := hb.one
  have h00 := hb.zreg 0 (by omega)
  obtain ⟨-, -, -, fl, fs1, fs2, -⟩ := h.fr (a.m - 1) (by omega)
  obtain ⟨hT, hc⟩ := tTree_leaf hR hΔ hlf
  set U := a.U (a.m - 1)
  set s := a.s (a.m - 1)
  obtain ⟨c₁, k₁, e₁, hk₁, hw₁, g35, g36, g33, ou₁, nm₁, q₁, rr₁, rm₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.outN 0, .outN 1431, .copyN 1435 1430, .copyN 1436 1431,
        .constN 1433 0]) c c₁ k₁ ∧ k₁ = 5 ∧ WordsBounded W c₁ ∧ c₁.nreg 1435 = s ∧
      c₁.nreg 1436 = #U ∧ c₁.nreg 1433 = 0 ∧ c₁.output = c.output ++ [0, #U] ∧
      c₁.nmem = c.nmem ∧
      (∀ r, r ≠ 1433 → r ≠ 1435 → r ≠ 1436 → c₁.nreg r = c.nreg r) ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem := by
    exec_block
    · omega
    · refine ⟨rfl, ‹_›, by config_simp; exact h30, by config_simp; exact h31, by config_simp,
        by config_simp; rw [h00, h31]; simp, rfl, fun r h1 h2 h3 => by simp [h1, h2, h3], rfl,
        rfl⟩
  obtain ⟨c₂, k₂, e₂, hw₂, ou₂, nm₂, q₂, rr₂, rm₂, hk₂⟩ := prList_exec (P := P) (a := s) (n := #U) (f := lv U) hw₁
    (by rw [q₁ 1001 (by omega) (by omega) (by omega)]; exact h01) g35 g36 g33
    (fun j hj => by rw [nm₁]; exact fl j hj) (by omega)
  have Q : ∀ r, (r < 1420 ∨ r = 1426 ∨ r = 1427 ∨ 1437 ≤ r) → c₂.nreg r = c.nreg r :=
    fun r hr => by rw [q₂ r (by omega) (by omega) (by omega), q₁ r (by omega) (by omega)
      (by omega)]
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by rw [hc]; omega, h.restrict hw₂ Q (by rw [nm₂, nm₁])
    (by rw [rr₂, rr₁]) (by rw [rm₂, rm₁]) (by simp only; omega)
    (fun i _ => ⟨rfl, rfl, rfl⟩) ?_, by
      rw [q₂ 1428 (by omega) (by omega) (by omega), q₁ 1428 (by omega) (by omega) (by omega)]
      exact h28⟩
  rw [ou₂, ou₁, ← h.out, a.rem_succ hR hΔ T (i := a.m - 1) (by omega), hT]
  simp [tenc, lvs]

theorem tPush_exec {d : Config} (hw : WordsBounded W d) {i aT s pa pb k : ℕ}
    (h01 : d.nreg 1001 = 1) (h28 : d.nreg 1428 = i) (h27 : d.nreg 1427 = aT)
    (h30 : d.nreg 1430 = s) (h24 : d.nreg 1424 = pa) (h25 : d.nreg 1425 = pb)
    (h32 : d.nreg 1432 = k + 1) (hb : aT + 3 * i + 6 ≤ W) (hs : s + pa ≤ W) :
    ∃ d' k', Exec P W tPush d d' k' ∧ k' = 18 ∧ WordsBounded W d' ∧ d'.nreg 1428 = i + 2 ∧
      d'.nmem (aT + 3 * i) = s + pa ∧ d'.nmem (aT + 3 * i + 1) = pb ∧
      d'.nmem (aT + 3 * i + 2) = k ∧ d'.nmem (aT + 3 * (i + 1)) = s ∧
      d'.nmem (aT + 3 * (i + 1) + 1) = pa ∧ d'.nmem (aT + 3 * (i + 1) + 2) = k ∧
      (∀ x, (x < aT + 3 * i ∨ aT + 3 * i + 6 ≤ x) → d'.nmem x = d.nmem x) ∧
      (∀ r, r ≠ 1428 → r ≠ 1429 → r ≠ 1432 → r ≠ 1434 → d'.nreg r = d.nreg r) ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem := by
  unfold tPush
  exec_block
  all_goals try (config_simp; simp (config := {failIfUnchanged := false}) only [h28, h27, h01,
    h30, h24, h25, h32]; omega)
  refine ⟨rfl, ‹_›, by config_simp; rw [h28, h01], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl,
    rfl⟩
  all_goals simp only [upd_apply, h28, h27, h01, h30, h24, h25, h32]
  all_goals norm_num
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · split_ifs <;> omega
  · intro x hx; split_ifs <;> omega
  · intro r h1 h2 h3 h4; simp [h1, h2, h3, h4]

/-- The frames after a split of the top frame `i` into `A` (on top, at `s`) and `A'` (at
`s + #A`), both with fuel `k`. -/
def tSplitFr (a : TFr N) (i k s : ℕ) (A A' : Finset (Fin N)) : TFr N :=
  ⟨i + 2, fun j => if j = i + 1 then A else if j = i then A' else a.U j,
    fun j => if j = i + 1 then k else if j = i then k else a.k j,
    fun j => if j = i + 1 then s else if j = i then s + #A else a.s j⟩

set_option maxHeartbeats 4000000 in
/-- A split round after the pop. -/
theorem tSplitCase {a : TFr N} {c : Config} (h : TCore G W R hR hΔ T L goal c0 a c) {i : ℕ}
    (hi : a.m = i + 1) {k' : ℕ} (hk : a.k i = k' + 1) (hn : ¬ #(a.U i) ≤ T ^ 2)
    (h28 : c.nreg 1428 = i) (h30 : c.nreg 1430 = a.s i) (h31 : c.nreg 1431 = #(a.U i))
    (h32 : c.nreg 1432 = a.k i) :
    ∃ a' c' k, Exec P W tSplit c c' k ∧ TCore G W R hR hΔ T L goal c0 a' c' ∧
      c'.nreg 1428 = a'.m ∧ a'.pot hR hΔ T + k + 13 ≤ a.pot hR hΔ T := by
  have hb := h.swb.base
  have hw := hb.wb
  have := h.lT; have := h.lB; have := h.lO; have := h.lO'
  have h01 := hb.one
  obtain ⟨f0, f1, f2, fl, fs1, fs2, fk⟩ := h.fr i (by omega)
  have hUN := card_le_N (a.U i)
  have hn' := tTree_node (G := G) hR hΔ (T := T) (k := k') hn
  have hAA := splitW_card_le (G := G) (a.U i) (sqSep hR hΔ)
  have hSU := card_le_card (splitW_fst_subset (G := G) (a.U i) (sqSep hR hΔ))
  have hsc : scost hR hΔ (a.U i) = 430 * N + 362 + 22 * ∑ v ∈ closedNbhd G (a.U i), G.degree v +
      dcost (sqSep hR hΔ) (spMu (square G) (a.U i)) (spL (square G) (a.U i)) Δ
        #(closedNbhd G (closedNbhd G (a.U i))) (closedNbhd G (closedNbhd G (a.U i))) +
      6 * #(SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) (a.U i)).1 + 45 := rfl
  -- the arguments of the split
  obtain ⟨c₁, k₁, e₁, hk₁, hw₁, g20, g21, g22, nm₁, q₁, ou₁, rr₁, rm₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.copyN 1420 1430, .copyN 1421 1431, .copyN 1422 1437]) c c₁ k₁ ∧
      k₁ = 3 ∧ WordsBounded W c₁ ∧ c₁.nreg 1420 = a.s i ∧ c₁.nreg 1421 = #(a.U i) ∧
      c₁.nreg 1422 = L.aO ∧ c₁.nmem = c.nmem ∧
      (∀ r, r ≠ 1420 → r ≠ 1421 → r ≠ 1422 → c₁.nreg r = c.nreg r) ∧
      c₁.output = c.output ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem := by
    exec_block
    exact ⟨rfl, ‹_›, by config_simp; exact h30, by config_simp; exact h31,
      by config_simp; exact h.rO, rfl, fun r h1 h2 h3 => by simp [h1, h2, h3], rfl, rfl, rfl⟩
  have sw₁ := h.swb.congr hw₁ (fun r hr => q₁ r (by omega) (by omega) (by omega))
    (fun x _ => by rw [nm₁]) rr₁ rm₁
  -- the split
  obtain ⟨c₂, k₂, e₂, hk₂, sw₂, g23, gS, g24, gA, g25, gA', K2, M2, ou₂⟩ :=
    splitWProg_spec (P := P) hR hΔ sw₁ g20 g21 g22 (fun l hl => by rw [nm₁]; exact fl l hl)
      (by omega) (by omega) h.lO (by omega) (Or.inl (by omega))
  obtain ⟨S, A, A', hSAA⟩ : ∃ S A A',
      SepRoutine.splitW (square G) (sqSep hR hΔ) (ord N) (a.U i) = (S, A, A') :=
    ⟨_, _, _, rfl⟩
  rw [hSAA] at g23 gS g24 gA g25 gA' hn' hAA hSU hsc
  simp only at g23 gS g24 gA g25 gA' hn' hAA hSU hsc
  have hw₂ := sw₂.base.wb
  have r01 : c₂.nreg 1001 = 1 := sw₂.base.one
  have K21 : ∀ r, 1426 ≤ r → r ≠ 1420 → r ≠ 1421 → r ≠ 1422 → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 h4 => by rw [K2 r (Or.inr h1), q₁ r h2 h3 h4]
  have r37 : c₂.nreg 1437 = L.aO := by
    rw [K21 1437 (by omega) (by omega) (by omega) (by omega)]; exact h.rO
  -- the separator printed
  obtain ⟨c₃, k₃, e₃, hk₃, hw₃, g35, g36, g33, ou₃, nm₃, q₃, rr₃, rm₃⟩ : ∃ c₃ k₃,
      Exec P W (block [.outN 1001, .outN 1423, .copyN 1435 1437, .copyN 1436 1423,
        .constN 1433 0]) c₂ c₃ k₃ ∧ k₃ = 5 ∧
      WordsBounded W c₃ ∧ c₃.nreg 1435 = L.aO ∧ c₃.nreg 1436 = #S ∧ c₃.nreg 1433 = 0 ∧
      c₃.output = c₂.output ++ [1, #S] ∧ c₃.nmem = c₂.nmem ∧
      (∀ r, r ≠ 1433 → r ≠ 1435 → r ≠ 1436 → c₃.nreg r = c₂.nreg r) ∧
      c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem := by
    exec_block
    · omega
    · exact ⟨rfl, ‹_›, by config_simp; exact r37, by config_simp; exact g23, by config_simp,
        by config_simp; rw [r01, g23]; simp, rfl, fun r h1 h2 h3 => by simp [h1, h2, h3],
        rfl, rfl⟩
  obtain ⟨c₄, k₄, e₄, hw₄, ou₄, nm₄, q₄, rr₄, rm₄, hk₄⟩ := prList_exec (P := P) (a := L.aO)
    (n := #S) (f := lv S) hw₃ (by rw [q₃ 1001 (by omega) (by omega) (by omega)]; exact r01)
    g35 g36 g33 (fun j hj => by rw [nm₃]; exact gS j hj) (by omega)
  have Q4 : ∀ r, r ≠ 1429 → r ≠ 1433 → r ≠ 1434 → r ≠ 1435 → r ≠ 1436 →
      c₄.nreg r = c₂.nreg r := fun r h1 h2 h3 h4 h5 => by rw [q₄ r h1 h2 h3, q₃ r h2 h4 h5]
  -- the two frames
  obtain ⟨c₅, k₅, e₅, hk₅, hw₅, g28, p0, p1, p2, p3, p4, p5, M5, q₅, ou₅, rr₅, rm₅⟩ :=
    tPush_exec (P := P) (i := i) (aT := L.aT) (s := a.s i) (pa := #A) (pb := #A') (k := k') hw₄
      (by rw [Q4 1001 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact r01)
      (by rw [Q4 1428 (by omega) (by omega) (by omega) (by omega) (by omega),
        K21 1428 (by omega) (by omega) (by omega) (by omega)]; exact h28)
      (by rw [Q4 1427 (by omega) (by omega) (by omega) (by omega) (by omega),
        K21 1427 (by omega) (by omega) (by omega) (by omega)]; exact h.rT)
      (by rw [Q4 1430 (by omega) (by omega) (by omega) (by omega) (by omega),
        K21 1430 (by omega) (by omega) (by omega) (by omega)]; exact h30)
      (by rw [Q4 1424 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact g24)
      (by rw [Q4 1425 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact g25)
      (by rw [Q4 1432 (by omega) (by omega) (by omega) (by omega) (by omega),
        K21 1432 (by omega) (by omega) (by omega) (by omega), h32, hk])
      (by omega) (by omega)
  -- the frames of memory and registers
  have MM : ∀ x, (x < L.aT + 3 * i ∨ L.aT + 3 * i + 6 ≤ x) → c₅.nmem x = c₂.nmem x :=
    fun x hx => by rw [M5 x hx, nm₄, nm₃]
  have M2' : ∀ x, L.aJ + N ≤ x → (x < L.aO ∨ L.aO + #(a.U i) ≤ x) →
      (x < a.s i ∨ a.s i + #(a.U i) ≤ x) → c₂.nmem x = c.nmem x :=
    fun x h1 h2 h3 => by rw [M2 x h1 h2 h3, nm₁]
  have R5 : ∀ r, r ≠ 1428 → r ≠ 1429 → r ≠ 1432 → r ≠ 1433 → r ≠ 1434 → r ≠ 1435 →
      r ≠ 1436 → c₅.nreg r = c₂.nreg r := fun r h1 h2 h3 h4 h5 h6 h7 => by
    rw [q₅ r h1 h2 h3 h5, Q4 r h2 h4 h5 h6 h7]
  have hrr : c₅.rreg = c₂.rreg := by rw [rr₅, rr₄, rr₃]
  have hrm : c₅.rmem = c₂.rmem := by rw [rm₅, rm₄, rm₃]
  have hout : c₅.output = c.output ++ (1 :: #S :: lvs S) := by
    rw [ou₅, ou₄, ou₃, ou₂, ou₁, lvs]; simp
  have hsub : ∀ j < i, (tSplitFr a i k' (a.s i) A A').U j = a.U j ∧
      (tSplitFr a i k' (a.s i) A A').k j = a.k j := fun j hj => by
    simp [tSplitFr, show j ≠ i + 1 by omega, show j ≠ i by omega]
  refine ⟨tSplitFr a i k' (a.s i) A A', c₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), ?_, by rw [g28]; rfl, ?_⟩
  · exact
    { swb := sw₂.congr hw₅ (fun r hr => R5 r (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)) (fun x hx => MM x (Or.inl (by omega))) hrr hrm
      rT2 := by
        rw [R5 1426 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega), K21 1426 (by omega) (by omega) (by omega) (by omega)]; exact h.rT2
      rT := by
        rw [R5 1427 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega), K21 1427 (by omega) (by omega) (by omega) (by omega)]; exact h.rT
      rO := by
        rw [R5 1437 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega)]; exact r37
      lO := h.lO, lO' := h.lO', lB := h.lB, lT := h.lT
      fr := fun j hj => by
        simp only [tSplitFr] at hj ⊢
        by_cases e1 : j = i + 1
        · rw [e1]
          simp only [↓reduceIte]
          refine ⟨p3, p4, p5, fun t ht => ?_, by omega, by omega, by omega⟩
          rw [MM _ (Or.inl (by omega))]; exact gA t ht
        by_cases e2 : j = i
        · rw [e2]
          simp only [show i ≠ i + 1 by omega, ↓reduceIte]
          refine ⟨p0, p1, p2, fun t ht => ?_, by omega, by omega, by omega⟩
          rw [MM _ (Or.inl (by omega))]; exact gA' t ht
        simp only [e1, e2, ↓reduceIte]
        have hj' : j < i := by omega
        obtain ⟨u0, u1, u2, ul, us1, us2, uk⟩ := h.fr j (by omega)
        have ho := h.ord j i hj' (by omega)
        refine ⟨?_, ?_, ?_, fun t ht => ?_, us1, us2, uk⟩
        · rw [MM _ (Or.inl (by omega)), M2' _ (by omega) (Or.inr (by omega))
            (Or.inr (by omega))]; exact u0
        · rw [MM _ (Or.inl (by omega)), M2' _ (by omega) (Or.inr (by omega))
            (Or.inr (by omega))]; exact u1
        · rw [MM _ (Or.inl (by omega)), M2' _ (by omega) (Or.inr (by omega))
            (Or.inr (by omega))]; exact u2
        · rw [MM _ (Or.inl (by omega)), M2' _ (by omega) (Or.inr (by omega))
            (Or.inr (by omega))]; exact ul t ht
      ord := fun j1 j2 h12 hj2 => by
        simp only [tSplitFr] at hj2 ⊢
        by_cases e1 : j2 = i + 1
        · rw [e1]
          by_cases e2 : j1 = i
          · rw [e2]; simp
          · have hj1 : j1 < i := by omega
            have ho := h.ord j1 i hj1 (by omega)
            simp only [↓reduceIte, e2, show j1 ≠ i + 1 by omega]
            omega
        by_cases e2 : j2 = i
        · rw [e2] at h12 ⊢
          have ho := h.ord j1 i h12 (by omega)
          simp only [↓reduceIte, show i ≠ i + 1 by omega, show j1 ≠ i + 1 by omega,
            show j1 ≠ i by omega]
          omega
        simp only [e1, e2, ↓reduceIte, show j1 ≠ i + 1 by omega, show j1 ≠ i by omega]
        exact h.ord j1 j2 h12 (by omega)
      out := by
        rw [hout, ← h.out, a.rem_succ hR hΔ T hi, hk, hn'.1,
          (tSplitFr a i k' (a.s i) A A').rem_succ hR hΔ T (i := i + 1) rfl,
          TFr.rem_succ hR hΔ T _ (i := i) rfl,
          TFr.rem_congr hR hΔ T (a := ⟨i, (tSplitFr a i k' (a.s i) A A').U,
            (tSplitFr a i k' (a.s i) A A').k, (tSplitFr a i k' (a.s i) A A').s⟩)
            (b := ⟨i, a.U, a.k, a.s⟩) rfl hsub]
        simp [tSplitFr, tenc]
      keep := fun r hr => by
        have hr' : r ≠ 1420 ∧ r ≠ 1421 ∧ r ≠ 1422 ∧ r ≠ 1428 ∧ r ≠ 1429 ∧ r ≠ 1432 ∧
            r ≠ 1433 ∧ r ≠ 1434 ∧ r ≠ 1435 ∧ r ≠ 1436 := by
          rcases hr with ⟨h1, -⟩ | h1
          · unfold KeptS at h1; omega
          · omega
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hr'
        have hK : (KeptS r ∧ r ≠ 1201) ∨ 1426 ≤ r := by
          rcases hr with h1 | h1
          · exact Or.inl h1
          · exact Or.inr (by omega)
        rw [R5 r a4 a5 a6 a7 a8 a9 a10, K2 r hK, q₁ r a1 a2 a3]
        exact h.keep r hr
      mem := fun x h1 h2 h3 h4 => by
        rw [MM x (by omega), M2' x h1 (by omega) (by omega)]
        exact h.mem x h1 h2 h3 h4 }
  · rw [a.pot_succ hR hΔ T hi, (tSplitFr a i k' (a.s i) A A').pot_succ hR hΔ T (i := i + 1) rfl,
      TFr.pot_succ hR hΔ T _ (i := i) rfl,
      TFr.pot_congr hR hΔ T (a := ⟨i, (tSplitFr a i k' (a.s i) A A').U,
        (tSplitFr a i k' (a.s i) A A').k, (tSplitFr a i k' (a.s i) A A').s⟩)
        (b := ⟨i, a.U, a.k, a.s⟩) rfl hsub, hk, hn'.2]
    simp only [tSplitFr, ↓reduceIte, show i ≠ i + 1 by omega]
    omega

/-- A round of the worklist. -/
theorem tBody_exec {a : TFr N} {c : Config} (h : TCore G W R hR hΔ T L goal c0 a c)
    (hm : c.nreg 1428 = a.m) (h0 : 0 < a.m) :
    ∃ a' c' k, Exec P W tBody c c' k ∧ TCore G W R hR hΔ T L goal c0 a' c' ∧
      c'.nreg 1428 = a'.m ∧ a'.pot hR hΔ T + k + 2 ≤ a.pot hR hΔ T := by
  obtain ⟨c₁, k₁, e₁, hk₁, h₁, m₁, s₁, n₁, f₁⟩ := tPop_exec (P := P) h hm h0
  obtain ⟨i, hi⟩ : ∃ i, a.m = i + 1 := ⟨a.m - 1, by omega⟩
  have hi' : a.m - 1 = i := by omega
  rw [hi'] at m₁ s₁ n₁ f₁
  have r0 : c₁.nreg 0 = 0 := h₁.swb.base.r0
  have hp := a.pot_succ hR hΔ T hi
  have hleaf : ∀ (hlf : a.k i = 0 ∨ #(a.U i) ≤ T ^ 2),
      ∃ c' k, Exec P W tLeaf c₁ c' k ∧ k + 14 ≤ tcost hR hΔ T (a.k i) (a.U i) ∧
        TCore G W R hR hΔ T L goal c0 ⟨i, a.U, a.k, a.s⟩ c' ∧ c'.nreg 1428 = i := by
    intro hlf
    have := tLeafCase (P := P) h₁ h0 (by rw [hi']; exact hlf) (by rw [hi']; exact m₁)
      (by rw [hi']; exact s₁) (by rw [hi']; exact n₁)
    rw [hi'] at this
    exact this
  by_cases hk : 0 < a.k i
  · by_cases hn : T ^ 2 < #(a.U i)
    · obtain ⟨k', hk'⟩ : ∃ k', a.k i = k' + 1 := ⟨a.k i - 1, by omega⟩
      obtain ⟨a', c', k, e, h', m', hk2⟩ := tSplitCase (P := P) h₁ hi hk' (by omega) m₁ s₁ n₁ f₁
      exact ⟨a', c', k₁ + (k + 1 + 1), .seq e₁ (.ifLtN_true (by rw [r0, f₁]; exact hk)
        (.ifLtN_true (by rw [h₁.rT2, n₁]; exact hn) e)), h', m', by omega⟩
    · obtain ⟨c', k, e, hk', h', m'⟩ := hleaf (Or.inr (by omega))
      refine ⟨⟨i, a.U, a.k, a.s⟩, c', k₁ + (k + 2 + 1), .seq e₁ (.ifLtN_true
        (by rw [r0, f₁]; exact hk) (.ifLtN_false (by rw [h₁.rT2, n₁]; exact hn) e)), h', m', ?_⟩
      omega
  · obtain ⟨c', k, e, hk', h', m'⟩ := hleaf (Or.inl (by omega))
    refine ⟨⟨i, a.U, a.k, a.s⟩, c', k₁ + (k + 2), .seq e₁ (.ifLtN_false
      (by rw [r0, f₁]; exact hk) e), h', m', ?_⟩
    omega

/-- **The worklist loop**: all frames printed. -/
theorem treeLoop_exec {a : TFr N} {c : Config} (h : TCore G W R hR hΔ T L goal c0 a c)
    (hm : c.nreg 1428 = a.m) :
    ∃ a' c' k, Exec P W treeLoop c c' k ∧ TCore G W R hR hΔ T L goal c0 a' c' ∧ a'.m = 0 ∧
      c'.output = goal ∧ k ≤ a.pot hR hΔ T + 2 := by
  obtain ⟨a', c', k, e, ⟨hD, hm'⟩, hn, hk⟩ := whileLtN_abs (P := P) (W := W) (a := 0)
    (b := 1428) (body := tBody)
    (fun a' c' => TCore G W R hR hΔ T L goal c0 a' c' ∧ c'.nreg 1428 = a'.m)
    (fun a' => a'.pot hR hΔ T) (fun _ _ h => h.1.swb.base.wb)
    (fun a' c' ⟨hD, hm'⟩ ht => by
      rw [hD.swb.base.r0, hm'] at ht
      obtain ⟨a'', c'', k, e, hD', hm'', hk⟩ := tBody_exec (P := P) hD hm' ht
      exact ⟨a'', c'', k, e, ⟨hD', hm''⟩, hk⟩) ⟨h, hm⟩
  rw [hD.swb.base.r0, hm'] at hn
  have h0 : a'.m = 0 := by omega
  refine ⟨a', c', k, e, hD, h0, ?_, hk⟩
  rw [← hD.out]
  simp [TFr.rem, h0]

end core

variable {R : Kasteleyn.RotationSystem G}

set_option maxHeartbeats 1000000 in
/-- **The separator tree on the machine.** From the state between splits `SWB`, with `T²` in
`1426`, the stack base `aT` in `1427`, the output buffer `aO` of the splits in `1437`, the list
area `base` in `1430`, `#U` in `1431`, the fuel `k ≤ k0` in `1432`, and the sorted list of `U`
at `base`, the program `treeProg` prints the preorder encoding `tenc` of the tree
`buildAux (square G) (sqSep hR hΔ) (ord N) T k U`, within `tcost … k U + 8` steps; the state
between splits holds again, the registers of `SWB`, those from `1438` and `1426`, `1427`,
`1437` are kept, and so is the memory above `aJ + N` outside the output buffer, the list area
and the stack. -/
theorem treeProg_spec (hR : R.IsPlane) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {T : ℕ} {L : TL}
    {c : Config} (hc : SWB G R L.Z W L.M L.aS L.aP L.aV L.aF L.aZ L.aCW L.aCB L.aSn L.aJ c)
    {U : Finset (Fin N)} {k : ℕ} (h26 : c.nreg 1426 = T ^ 2) (h27 : c.nreg 1427 = L.aT)
    (h37 : c.nreg 1437 = L.aO) (h30 : c.nreg 1430 = L.base) (h31 : c.nreg 1431 = #U)
    (h32 : c.nreg 1432 = k) (hk : k ≤ L.k0) (hl : ∀ j < #U, c.nmem (L.base + j) = lv U j)
    (lO : L.aJ + N ≤ L.aO) (lO' : L.aO + N ≤ L.base) (lB : L.base + N ≤ L.aT)
    (lT : L.aT + 3 * (L.k0 + 1) + N ≤ W) :
    ∃ c' k', Exec P W treeProg c c' k' ∧ k' ≤ tcost hR hΔ T k U + 8 ∧
      SWB G R L.Z W L.M L.aS L.aP L.aV L.aF L.aZ L.aCW L.aCB L.aSn L.aJ c' ∧
      c'.output = c.output ++ tenc (SepRoutine.buildAux (square G) (sqSep hR hΔ) (ord N) T k U) ∧
      (∀ r, (KeptS r ∧ r ≠ 1201) ∨ 1438 ≤ r ∨ r = 1426 ∨ r = 1427 ∨ r = 1437 →
        c'.nreg r = c.nreg r) ∧
      (∀ x, L.aJ + N ≤ x → (x < L.aO ∨ L.aO + N ≤ x) → (x < L.base ∨ L.base + N ≤ x) →
        (x < L.aT ∨ L.aT + 3 * (L.k0 + 1) ≤ x) → c'.nmem x = c.nmem x) := by
  have hb := hc.base
  have hw := hb.wb
  have h01 := hb.one
  have hUN := card_le_N U
  obtain ⟨c₁, k₁, e₁, hk₁, hw₁, m₁, t0, t1, t2, M1, q₁, ou₁, rr₁, rm₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.storeN 1427 1430, .addN 1429 1427 1001, .storeN 1429 1431,
        .addN 1429 1429 1001, .storeN 1429 1432, .copyN 1428 1001]) c c₁ k₁ ∧ k₁ = 6 ∧
      WordsBounded W c₁ ∧ c₁.nreg 1428 = 1 ∧ c₁.nmem L.aT = L.base ∧
      c₁.nmem (L.aT + 1) = #U ∧ c₁.nmem (L.aT + 2) = k ∧
      (∀ x, (x < L.aT ∨ L.aT + 3 ≤ x) → c₁.nmem x = c.nmem x) ∧
      (∀ r, r ≠ 1428 → r ≠ 1429 → c₁.nreg r = c.nreg r) ∧
      c₁.output = c.output ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem := by
    exec_block
    · config_simp; rw [h27, h01]; omega
    · config_simp; rw [h27, h01]; omega
    · refine ⟨rfl, ‹_›, by config_simp; exact h01, ?_, ?_, ?_, ?_, fun r h1 h2 => by
        simp [h1, h2], rfl, rfl, rfl⟩
      all_goals simp only [upd_apply, h27, h01, h30, h31, h32]
      all_goals norm_num
      all_goals first | omega | (intro x hx; split_ifs <;> omega)
  let a0 : TFr N := ⟨1, fun _ => U, fun _ => k, fun _ => L.base⟩
  have hD : TCore G W R hR hΔ T L (c.output ++ tenc (tTree G hR hΔ T k U)) c a0 c₁ :=
    { swb := hc.congr hw₁ (fun r hr => q₁ r (by omega) (by omega))
        (fun x hx => M1 x (Or.inl (by omega))) rr₁ rm₁
      rT2 := by rw [q₁ 1426 (by omega) (by omega)]; exact h26
      rT := by rw [q₁ 1427 (by omega) (by omega)]; exact h27
      rO := by rw [q₁ 1437 (by omega) (by omega)]; exact h37
      lO := lO, lO' := lO', lB := lB, lT := lT
      fr := fun i hi => by
        obtain rfl : i = 0 := by simp only [a0] at hi; omega
        simp only [a0]
        refine ⟨by simpa using t0, t1, t2, fun j hj => ?_, le_rfl, by omega, by omega⟩
        rw [M1 _ (Or.inl (by omega))]; exact hl j hj
      ord := fun i j hij hj => by simp only [a0] at hj; omega
      out := by rw [ou₁]; simp [TFr.rem, a0]
      keep := fun r hr => q₁ r (by rcases hr with ⟨h1, -⟩ | h1 <;> [(unfold KeptS at h1; omega);
        omega]) (by rcases hr with ⟨h1, -⟩ | h1 <;> [(unfold KeptS at h1; omega); omega])
      mem := fun x _ _ _ h4 => M1 x (by omega) }
  obtain ⟨a', c', k', e, hD', -, hout, hk'⟩ := treeLoop_exec (P := P) hD m₁
  have hpot : a0.pot hR hΔ T = tcost hR hΔ T k U := by simp [TFr.pot, a0]
  refine ⟨c', k₁ + k', .seq e₁ e, by omega, hD'.swb, hout, fun r hr => ?_,
    fun x h1 h2 h3 h4 => hD'.mem x h1 h2 h3 h4⟩
  rcases hr with hr | hr | hr | hr | hr
  · exact hD'.keep r (Or.inl hr)
  · exact hD'.keep r (Or.inr hr)
  · rw [hr, hD'.rT2, h26]
  · rw [hr, hD'.rT, h27]
  · rw [hr, hD'.rO, h37]

theorem lv_univ (j : ℕ) (hj : j < N) : lv (univ : Finset (Fin N)) j = j := by
  have h : clist (ord N) (univ : Finset (Fin N)) = List.finRange N := by
    rw [clist_eq]; simp
  simp [lv, h, List.getD_eq_getElem?_getD, hj]

/-- **The separator tree of the square on the machine**: `treeProg_spec` for all vertices with
fuel `N`, the tree `buildTree (square G) (sqSep hR hΔ) (ord N) T`; for
`T ≥ 40 (177 · 9 (Δ + 1)² + 1)` it is a good tree of the square (`GoodTree`). -/
theorem treeProg_buildTree (hR : R.IsPlane) {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) {T : ℕ}
    {L : TL} {c : Config}
    (hc : SWB G R L.Z W L.M L.aS L.aP L.aV L.aF L.aZ L.aCW L.aCB L.aSn L.aJ c)
    (h26 : c.nreg 1426 = T ^ 2) (h27 : c.nreg 1427 = L.aT) (h37 : c.nreg 1437 = L.aO)
    (h30 : c.nreg 1430 = L.base) (h31 : c.nreg 1431 = N) (h32 : c.nreg 1432 = N)
    (hk : N ≤ L.k0) (hl : ∀ j < N, c.nmem (L.base + j) = j)
    (lO : L.aJ + N ≤ L.aO) (lO' : L.aO + N ≤ L.base) (lB : L.base + N ≤ L.aT)
    (lT : L.aT + 3 * (L.k0 + 1) + N ≤ W) :
    ∃ c' k', Exec P W treeProg c c' k' ∧ k' ≤ tcost hR hΔ T N univ + 8 ∧
      SWB G R L.Z W L.M L.aS L.aP L.aV L.aF L.aZ L.aCW L.aCB L.aSn L.aJ c' ∧
      c'.output = c.output ++ tenc (SepRoutine.buildTree (square G) (sqSep hR hΔ) (ord N) T) ∧
      (sepTreeConst (9 * ((Δ : ℝ) + 1) ^ 2) ≤ T →
        GoodTree (square G) T (SepRoutine.buildTree (square G) (sqSep hR hΔ) (ord N) T)) ∧
      (∀ r, (KeptS r ∧ r ≠ 1201) ∨ 1438 ≤ r ∨ r = 1426 ∨ r = 1427 ∨ r = 1437 →
        c'.nreg r = c.nreg r) ∧
      (∀ x, L.aJ + N ≤ x → (x < L.aO ∨ L.aO + N ≤ x) → (x < L.base ∨ L.base + N ≤ x) →
        (x < L.aT ∨ L.aT + 3 * (L.k0 + 1) ≤ x) → c'.nmem x = c.nmem x) := by
  have hcard : #(univ : Finset (Fin N)) = N := by simp
  obtain ⟨c', k', e, hk', hsw, hout, hr, hm⟩ := treeProg_spec (P := P) hR hΔ (U := univ)
    (k := N) hc h26 h27 h37 h30 (by rw [hcard]; exact h31) h32 hk
    (fun j hj => by rw [hl j (by rw [hcard] at hj; exact hj)]; exact (lv_univ j (by simpa using hj)).symm)
    lO lO' lB lT
  refine ⟨c', k', e, hk', hsw, ?_, fun hT => buildTree_ltRoutine_square_spec R hR mem_ord hΔ hT,
    hr, hm⟩
  rw [hout]
  simp [SepRoutine.buildTree]

end Piece

end PlanarSeparator
