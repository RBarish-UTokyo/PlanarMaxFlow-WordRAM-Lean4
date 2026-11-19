module

public import PlanarSeparator.Machine.TreeProg
public import NestedDissection.MachineAssemble

/-!
# The nested dissection order from the printed tree, on the machine

The tree program prints a separator tree `t` in preorder (`PlanarSeparator.Piece.tenc`). The
nested-dissection stage `nbuild` reads the ranks `rkWords (ndPerm t)` of the nested dissection order
`t.order` (both parts, then the separator). **`ordProg`** computes them from `tenc t` with an
explicit stack of work items (`OIt`: a subtree still to be read from the input, or a separator
whose vertices are to be numbered once both parts are done), numbering the vertices in the order
`t.order`, then prints the ranks.

* `ordProg_exec`: from the initial configuration on the input `tenc t`, for a tree with
  `t.order` without repetition and of vertices `< n`, the program prints for each vertex `u < k`
  (`k` the number of vertices) the position of `u` in `t.order`, within `21 |tenc t| + 6 k + 13`
  steps.
* **`ordProg_runsWithin`**: for a separator tree `t` of `Fin n` covering all vertices, the
  output is `rkWords (ndPerm t hd hv)`.
* `length_tenc_buildAux`: `|tenc (buildAux …)| ≤ 9 m + 2` for the trees of `buildAux`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

namespace Piece

open Finset NestedDissection NestedDissection.SepTree WordRAM WordRAM.Machine
open WordRAM.Machine.Stmt WordRAM.Programs

variable {N : ℕ} {P : Input} {W : ℕ}

/-! ### Sorted lists -/

theorem clist_ord_eq_sort (s : Finset (Fin N)) : clist (ord N) s = s.sort (· ≤ ·) := by
  have hs1 : (clist (ord N) s).SortedLT := by
    unfold clist
    rw [List.Nodup.dedup ((List.nodup_finRange N).filter _)]
    exact ((List.sortedLT_finRange N).pairwise.filter _).sortedLT
  exact hs1.eq_of_mem_iff (Finset.sortedLT_sort s) fun x => by
    rw [mem_clist mem_ord, Finset.mem_sort]

theorem lvs_eq (s : Finset (Fin N)) : lvs s = (s.sort (· ≤ ·)).map Fin.val := by
  rw [← clist_ord_eq_sort]
  apply List.ext_getElem
  · simp [lvs, length_clist_ord]
  · intro i h1 h2
    simp only [lvs, List.getElem_map, List.getElem_range, lv]
    rw [List.getD_eq_getElem _ _ (by simpa using h2)]
    simp

theorem order_leaf_map (s : Finset (Fin N)) : (leaf s).order.map Fin.val = lvs s := by
  rw [lvs_eq]; rfl

theorem order_node_map (s : Finset (Fin N)) (a b : SepTree (Fin N)) :
    (node s a b).order.map Fin.val = a.order.map Fin.val ++ b.order.map Fin.val ++ lvs s := by
  rw [lvs_eq]; simp [order]

/-! ### Work items -/

/-- A work item: a subtree still to be read, or a separator to be numbered. -/
inductive OIt (N : ℕ) where
  | T (t : SepTree (Fin N))
  | S (s : Finset (Fin N))

/-- The vertex numbers an item contributes to the order. -/
def OIt.ord : OIt N → List ℕ
  | T t => t.order.map Fin.val
  | S s => lvs s

/-- The input words an item still reads. -/
def OIt.inp : OIt N → List ℕ
  | T t => tenc t
  | S _ => []

/-- The cost still to come for an item. -/
def OIt.pot : OIt N → ℕ
  | T t => 21 * (tenc t).length
  | S s => 8 * #s + 11

/-- The frame words of an item in memory: `0` for a subtree, the position `x ≥ 1` of the
separator's list in the input and its length for a separator. -/
def OIt.ok (P : Input) : OIt N → ℕ → ℕ → Prop
  | T _, x, _ => x = 0
  | S s, x, l => 1 ≤ x ∧ l = #s ∧ x + #s ≤ P.data.length ∧
      ∀ j < #s, P.data.getD (x + j) 0 = lv s j

/-- The stack: `m` items, item `m - 1` on top. -/
structure OFr (N : ℕ) where
  m : ℕ
  it : ℕ → OIt N

/-- The order still to come. -/
def OFr.ords (a : OFr N) : List ℕ := ((List.range a.m).reverse.map fun i => (a.it i).ord).flatten

/-- The input still to be read. -/
def OFr.inps (a : OFr N) : List ℕ := ((List.range a.m).reverse.map fun i => (a.it i).inp).flatten

/-- The cost still to come. -/
def OFr.pot (a : OFr N) : ℕ := ∑ i ∈ range a.m, (a.it i).pot

theorem OFr.ords_succ (a : OFr N) {i : ℕ} (h : a.m = i + 1) :
    a.ords = (a.it i).ord ++ (⟨i, a.it⟩ : OFr N).ords := by
  simp only [OFr.ords, h, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.map_cons, List.singleton_append, List.flatten_cons]

theorem OFr.inps_succ (a : OFr N) {i : ℕ} (h : a.m = i + 1) :
    a.inps = (a.it i).inp ++ (⟨i, a.it⟩ : OFr N).inps := by
  simp only [OFr.inps, h, List.range_succ, List.reverse_append, List.reverse_singleton,
    List.map_cons, List.singleton_append, List.flatten_cons]

theorem OFr.pot_succ (a : OFr N) {i : ℕ} (h : a.m = i + 1) :
    a.pot = (a.it i).pot + (⟨i, a.it⟩ : OFr N).pot := by
  simp only [OFr.pot, h, sum_range_succ]; omega

theorem OFr.congr {a b : OFr N} (hm : a.m = b.m) (h : ∀ i < a.m, a.it i = b.it i) :
    a.ords = b.ords ∧ a.inps = b.inps ∧ a.pot = b.pot := by
  refine ⟨?_, ?_, ?_⟩
  · unfold OFr.ords; rw [← hm]; congr 1
    exact List.map_congr_left fun i hi => by rw [h i (by simpa using hi)]
  · unfold OFr.inps; rw [← hm]; congr 1
    exact List.map_congr_left fun i hi => by rw [h i (by simpa using hi)]
  · unfold OFr.pot; rw [← hm]; exact sum_congr rfl fun i hi => by rw [h i (mem_range.1 hi)]

/-! ### The program

Registers: `1500` the input length `L`, `1501` the input position, `1502` the number of frames,
`1503` the base `2 L + 6` of the ranks, `1504` the next rank, `1505`–`1510` scratch. The frame
`i` is at `2 i`, `2 i + 1`. -/

def oInit : Stmt := block [.constN 1001 1, .inputSize 1500, .addN 1503 1500 1500,
  .constN 1505 6, .addN 1503 1503 1505, .constN 1501 0, .constN 1504 0, .copyN 1502 1001]

/-- The removal of the top frame: `1505`, `1507` := its words. -/
def oPop : Stmt := block [.subN 1502 1502 1001, .addN 1506 1502 1502, .loadN 1505 1506,
  .addN 1506 1506 1001, .loadN 1507 1506]

/-- One vertex numbered. -/
def asBody : Stmt := block [.addN 1509 1505 1508, .readIn 1510 1509, .addN 1509 1503 1510,
  .storeN 1509 1504, .addN 1504 1504 1001, .addN 1508 1508 1001]

/-- **Numbering** the `nreg 1507` vertices listed in the input from `nreg 1505`. -/
def oAssign : Stmt := .seq (block [.constN 1508 0]) (.whileLtN 1508 1507 asBody)

/-- Reading the header of a subtree. -/
def oParse0 : Stmt := block [.readIn 1508 1501, .addN 1509 1501 1001, .readIn 1507 1509,
  .addN 1505 1509 1001, .addN 1501 1505 1507]

/-- The frames of a node: its separator, the second part, the first part on top. -/
def oPush : Stmt := block [.addN 1506 1502 1502, .storeN 1506 1505, .addN 1506 1506 1001,
  .storeN 1506 1507, .addN 1506 1506 1001, .storeN 1506 0, .addN 1506 1506 1001,
  .addN 1506 1506 1001, .storeN 1506 0, .addN 1502 1502 1001, .addN 1502 1502 1001,
  .addN 1502 1502 1001]

def oParse : Stmt := .seq oParse0 (.ifLtN 0 1508 oPush oAssign)

def oBody : Stmt := .seq oPop (.ifLtN 0 1505 oAssign oParse)

def oLoop : Stmt := .whileLtN 0 1502 oBody

def oPrBody : Stmt := block [.addN 1509 1503 1508, .loadN 1510 1509, .outN 1510,
  .addN 1508 1508 1001]

def oPrint : Stmt := .seq (block [.constN 1508 0]) (.whileLtN 1508 1504 oPrBody)

/-- **The order program.** -/
def ordProg : Stmt := .seq oInit (.seq oLoop oPrint)

/-! ### The state of the loop -/

/-- **The state of the loop** for the target order `goal`: the stack `a`, the vertices `A`
numbered so far (`A ++ a.ords = goal`), the input from the position on holds `a.inps`, the
frames hold the items, the rank of `A[i]` is `i`. -/
structure OCore (P : Input) (W : ℕ) (goal : List ℕ) (a : OFr N) (A : List ℕ) (c : Config) :
    Prop where
  wb : WordsBounded W c
  one : c.nreg 1001 = 1
  r0 : c.nreg 0 = 0
  rL : c.nreg 1500 = P.data.length
  rR : c.nreg 1503 = 2 * P.data.length + 6
  rm : c.nreg 1502 = a.m
  rpos : c.nreg 1504 = A.length
  mip : a.m ≤ c.nreg 1501 + 1
  inp : ∀ j < a.inps.length, P.data.getD (c.nreg 1501 + j) 0 = a.inps.getD j 0
  inpL : c.nreg 1501 + a.inps.length ≤ P.data.length
  fr : ∀ i < a.m, (a.it i).ok P (c.nmem (2 * i)) (c.nmem (2 * i + 1))
  out : A ++ a.ords = goal
  rk : ∀ i < A.length, c.nmem (2 * P.data.length + 6 + A.getD i 0) = i
  output : c.output = []

/-! ### Numbering a separator -/

theorem oAssign_exec {d : Config} (hw : WordsBounded W d) {x aR p : ℕ} {s : Finset (Fin N)}
    (h01 : d.nreg 1001 = 1) (h05 : d.nreg 1505 = x) (h07 : d.nreg 1507 = #s)
    (h03 : d.nreg 1503 = aR) (h04 : d.nreg 1504 = p)
    (hv : ∀ j < #s, P.data.getD (x + j) 0 = lv s j) (hx : x + #s ≤ W) (hR : aR + N ≤ W)
    (hp : p + #s ≤ W) :
    ∃ d' k, Exec P W oAssign d d' k ∧ k ≤ 8 * #s + 3 ∧ WordsBounded W d' ∧
      d'.nreg 1504 = p + #s ∧ (∀ j < #s, d'.nmem (aR + lv s j) = p + j) ∧
      (∀ a, (∀ j < #s, a ≠ aR + lv s j) → d'.nmem a = d.nmem a) ∧
      (∀ r, r ≠ 1504 → r ≠ 1508 → r ≠ 1509 → r ≠ 1510 → d'.nreg r = d.nreg r) ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem := by
  obtain ⟨d₁, k₁, e₁, hk₁, hw₁, g08, q₁, m₁, o₁, r₁, rm₁⟩ : ∃ d₁ k₁,
      Exec P W (block [.constN 1508 0]) d d₁ k₁ ∧ k₁ = 1 ∧ WordsBounded W d₁ ∧
      d₁.nreg 1508 = 0 ∧ (∀ r, r ≠ 1508 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem ∧
      d₁.output = d.output ∧ d₁.rreg = d.rreg ∧ d₁.rmem = d.rmem := by
    exec_block
    rotate_right
    · exact ⟨rfl, ‹_›, by config_simp, fun r hr => by simp [upd_apply, hr], rfl, rfl, rfl, rfl⟩
    · omega
  let I : ℕ → Config → Prop := fun j c => WordsBounded W c ∧ c.nreg 1508 = j ∧
    c.nreg 1507 = #s ∧ c.nreg 1504 = p + j ∧ (∀ j' < j, c.nmem (aR + lv s j') = p + j') ∧
    (∀ a, (∀ j' < j, a ≠ aR + lv s j') → c.nmem a = d.nmem a) ∧
    (∀ r, r ≠ 1504 → r ≠ 1508 → r ≠ 1509 → r ≠ 1510 → c.nreg r = d.nreg r) ∧
    c.output = d.output ∧ c.rreg = d.rreg ∧ c.rmem = d.rmem
  obtain ⟨d₂, k₂, e₂, h₂, hk₂⟩ := Exec.forN (P := P) (W := W) (ri := 1508) (rN := 1507)
    (N := #s) (lo := 0) (B := 6) (body := asBody) I (fun j c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c h hj => by
      obtain ⟨hw', h08', h07', h04', hv', hm', hq', ho', hrr', hrm'⟩ := h
      have r01 : c.nreg 1001 = 1 := by rw [hq' 1001 (by omega) (by omega) (by omega) (by omega),
        h01]
      have r05 : c.nreg 1505 = x := by
        rw [hq' 1505 (by omega) (by omega) (by omega) (by omega), h05]
      have r03 : c.nreg 1503 = aR := by
        rw [hq' 1503 (by omega) (by omega) (by omega) (by omega), h03]
      have hlt := lv_ltN s hj
      unfold asBody
      exec_block
      rotate_right
      · refine ⟨⟨‹WordsBounded _ _›, by config_simp; rw [h08', r01], by config_simp; exact h07',
          by config_simp; rw [h04', r01]; omega, fun j' hj' => ?_, fun a ha => ?_,
          fun r a1 a2 a3 a4 => ?_, by config_simp; exact ho', by config_simp; exact hrr',
          by config_simp; exact hrm'⟩, by omega⟩
        · config_simp
          rw [upd_apply, r03, h08', r05, hv j hj, h04']
          split_ifs with e
          · have := lv_inj' s (by omega) hj (by omega : lv s j' = lv s j); subst this; rfl
          · have hne : j' ≠ j := fun hh => e (by rw [hh])
            exact hv' j' (by omega)
        · config_simp
          rw [upd_apply, r03, h08', r05, hv j hj]
          split_ifs with e
          · exact absurd e (ha j (by omega))
          · exact hm' a (fun j'' hj'' => ha j'' (by omega))
        · simp only [upd_apply, a1, a2, a3, a4, ite_false]; exact hq' r a1 a2 a3 a4
      all_goals (config_simp <;> simp (config := {failIfUnchanged := false}) only
        [h08', r01, r05, r03, h04', hv j hj] <;> omega))
    (Nat.zero_le _) ⟨hw₁, g08, by rw [q₁ 1507 (by omega), h07], by rw [q₁ 1504 (by omega), h04, Nat.add_zero],
      fun j' hj' => by omega, fun a _ => by rw [m₁], fun r a1 a2 a3 a4 => q₁ r a2,
      o₁, r₁, rm₁⟩
  obtain ⟨hw₂, -, -, g04, hv₂, hm₂, hq₂, ho₂, hr₂, hrm₂⟩ := h₂
  exact ⟨d₂, k₁ + k₂, .seq e₁ e₂, by omega, hw₂, g04, hv₂, hm₂, hq₂, ho₂, hr₂, hrm₂⟩

/-! ### The rounds -/

theorem getD_lvs (s : Finset (Fin N)) {j : ℕ} (hj : j < #s) : (lvs s).getD j 0 = lv s j := by
  simp [lvs, List.getD_eq_getElem?_getD, hj]

theorem length_tenc_pos (t : SepTree (Fin N)) : 2 ≤ (tenc t).length := by
  cases t <;> simp [tenc]

section rounds

variable {goal : List ℕ} {a : OFr N} {A : List ℕ} {c : Config}

theorem OCore.ip_le (h : OCore P W goal a A c) : c.nreg 1501 ≤ P.data.length := by
  have := h.inpL; omega

theorem oPop_exec (h : OCore P W goal a A c) (hW : 2 * P.data.length + 6 + N ≤ W) {i : ℕ}
    (hm : a.m = i + 1) :
    ∃ c₁ k, Exec P W oPop c c₁ k ∧ k = 5 ∧ WordsBounded W c₁ ∧ c₁.nreg 1502 = i ∧
      c₁.nreg 1505 = c.nmem (2 * i) ∧ c₁.nreg 1507 = c.nmem (2 * i + 1) ∧ c₁.nmem = c.nmem ∧
      (∀ r, r ≠ 1502 → r ≠ 1505 → r ≠ 1506 → r ≠ 1507 → c₁.nreg r = c.nreg r) ∧
      c₁.output = c.output ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem := by
  have hw := h.wb
  have h01 := h.one
  have h02 := h.rm
  have hmip := h.mip
  have hip := h.ip_le
  unfold oPop
  exec_block
  rotate_right
  · refine ⟨rfl, ‹_›, by config_simp; rw [h02, h01]; omega, ?_, ?_, rfl, fun r a1 a2 a3 a4 => by
      simp only [upd_apply, a1, a2, a3, a4, ite_false], rfl, rfl, rfl⟩
    · config_simp; rw [h02, h01]; congr 1; omega
    · config_simp; rw [h02, h01]; congr 1; omega
  all_goals (config_simp <;> simp (config := {failIfUnchanged := false}) only [h02, h01] <;> omega)

theorem oParse0_exec {d : Config} (hw : WordsBounded W d) {ip tg len : ℕ}
    (hPW : ∀ j, P.data.getD j 0 ≤ W) (h01 : d.nreg 1001 = 1) (h1501 : d.nreg 1501 = ip) (htg : P.data.getD ip 0 = tg)
    (hlen : P.data.getD (ip + 1) 0 = len) (hb : ip + 2 + len ≤ W) :
    ∃ d' k, Exec P W oParse0 d d' k ∧ k = 5 ∧ WordsBounded W d' ∧ d'.nreg 1508 = tg ∧
      d'.nreg 1507 = len ∧ d'.nreg 1505 = ip + 2 ∧ d'.nreg 1501 = ip + 2 + len ∧
      d'.nmem = d.nmem ∧
      (∀ r, r ≠ 1501 → r ≠ 1505 → r ≠ 1507 → r ≠ 1508 → r ≠ 1509 → d'.nreg r = d.nreg r) ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem := by
  unfold oParse0
  exec_block
  rotate_right
  · refine ⟨rfl, ‹_›, by config_simp; rw [h1501, htg], by config_simp; rw [h1501, h01, hlen],
      by config_simp; rw [h1501, h01], by config_simp; rw [h1501, h01, hlen], rfl,
      fun r a1 a2 a3 a4 a5 => by simp only [upd_apply, a1, a2, a3, a4, a5, ite_false],
      rfl, rfl, rfl⟩
  · config_simp; rw [h1501]; exact hPW _
  · config_simp; rw [h1501, h01]; omega
  · config_simp; rw [h1501, h01]; exact hPW _
  · config_simp; rw [h1501, h01]; omega
  · config_simp; rw [h1501, h01, hlen]; omega

theorem oPush_exec {d : Config} (hw : WordsBounded W d) {i x l : ℕ} (h00 : d.nreg 0 = 0)
    (h01 : d.nreg 1001 = 1) (h02 : d.nreg 1502 = i) (h05 : d.nreg 1505 = x)
    (h07 : d.nreg 1507 = l) (hb : 2 * i + 4 ≤ W) :
    ∃ d' k, Exec P W oPush d d' k ∧ k = 12 ∧ WordsBounded W d' ∧ d'.nreg 1502 = i + 3 ∧
      d'.nmem (2 * i) = x ∧ d'.nmem (2 * i + 1) = l ∧ d'.nmem (2 * (i + 1)) = 0 ∧
      d'.nmem (2 * (i + 2)) = 0 ∧
      (∀ y, (y < 2 * i ∨ 2 * i + 4 < y) → d'.nmem y = d.nmem y) ∧
      (∀ r, r ≠ 1502 → r ≠ 1506 → d'.nreg r = d.nreg r) ∧
      d'.output = d.output ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem := by
  unfold oPush
  exec_block
  rotate_right
  · refine ⟨rfl, ‹_›, by config_simp; rw [h02, h01], ?_, ?_, ?_, ?_, fun y hy => ?_,
      fun r a1 a2 => by simp only [upd_apply, a1, a2, ite_false], rfl, rfl, rfl⟩
    all_goals simp only [Config.nmem_mk, Config.nreg_mk, upd_apply, h02, h01, h05, h07, h00]
    all_goals norm_num
    all_goals (try split_ifs) <;> omega
  all_goals (config_simp <;> simp (config := {failIfUnchanged := false}) only [h02, h01] <;> omega)

theorem inps_tenc (h : OCore P W goal a A c) {i : ℕ} (hm : a.m = i + 1) {t : SepTree (Fin N)}
    (hT : a.it i = .T t) :
    (∀ j < (tenc t).length, P.data.getD (c.nreg 1501 + j) 0 = (tenc t).getD j 0) ∧
      (∀ j < (⟨i, a.it⟩ : OFr N).inps.length,
        P.data.getD (c.nreg 1501 + (tenc t).length + j) 0 = (⟨i, a.it⟩ : OFr N).inps.getD j 0) ∧
      c.nreg 1501 + (tenc t).length + (⟨i, a.it⟩ : OFr N).inps.length ≤ P.data.length := by
  have hi := a.inps_succ hm
  rw [hT] at hi
  simp only [OIt.inp] at hi
  have h1 := h.inp
  have h2 := h.inpL
  rw [hi] at h1 h2
  rw [List.length_append] at h2
  refine ⟨fun j hj => ?_, fun j hj => ?_, by omega⟩
  · rw [h1 j (by rw [List.length_append]; omega), List.getD_append _ _ _ _ hj]
  · rw [Nat.add_assoc, h1 _ (by rw [List.length_append]; omega),
      List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

/-- The frames after the split of a node. -/
def oNodeFr (a : OFr N) (i : ℕ) (s : Finset (Fin N)) (ta tb : SepTree (Fin N)) : OFr N :=
  ⟨i + 3, fun j => if j = i + 2 then .T ta else if j = i + 1 then .T tb else if j = i then .S s
    else a.it j⟩

theorem oNodeFr_eq (a : OFr N) (i : ℕ) (s : Finset (Fin N)) (ta tb : SepTree (Fin N)) :
    (oNodeFr a i s ta tb).ords = ta.order.map Fin.val ++ (tb.order.map Fin.val ++
      (lvs s ++ (⟨i, a.it⟩ : OFr N).ords)) ∧
    (oNodeFr a i s ta tb).inps = tenc ta ++ (tenc tb ++ (⟨i, a.it⟩ : OFr N).inps) ∧
    (oNodeFr a i s ta tb).pot = 21 * (tenc ta).length + (21 * (tenc tb).length +
      (8 * #s + 11 + (⟨i, a.it⟩ : OFr N).pot)) := by
  have e := OFr.congr (a := ⟨i, (oNodeFr a i s ta tb).it⟩) (b := ⟨i, a.it⟩) rfl (fun j (hj : j < i) => by
    simp [oNodeFr, show j ≠ i + 2 by omega, show j ≠ i + 1 by omega, show j ≠ i by omega])
  have h3 : (oNodeFr a i s ta tb).m = (i + 2) + 1 := rfl
  have h2 : (⟨i + 2, (oNodeFr a i s ta tb).it⟩ : OFr N).m = (i + 1) + 1 := rfl
  have h1 : (⟨i + 1, (oNodeFr a i s ta tb).it⟩ : OFr N).m = i + 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [OFr.ords_succ _ h3, OFr.ords_succ _ h2, OFr.ords_succ _ h1, e.1]
    simp [oNodeFr, OIt.ord]
  · rw [OFr.inps_succ _ h3, OFr.inps_succ _ h2, OFr.inps_succ _ h1, e.2.1]
    simp [oNodeFr, OIt.inp]
  · rw [OFr.pot_succ _ h3, OFr.pot_succ _ h2, OFr.pot_succ _ h1, e.2.2]
    simp [oNodeFr, OIt.pot]

theorem getD_tenc_node (s : Finset (Fin N)) (ta tb : SepTree (Fin N)) (j : ℕ) :
    (tenc (node s ta tb)).getD (2 + #s + j) 0 = (tenc ta ++ tenc tb).getD j 0 := by
  have e : tenc (node s ta tb) = [1, #s] ++ (lvs s ++ (tenc ta ++ tenc tb)) := by
    simp [tenc]
  rw [e, List.getD_append_right _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _
    (by simp [length_lvs]; omega)]
  simp [length_lvs]
  rw [show 2 + #s + j - 2 - #s = j by omega]

theorem length_tenc_node (s : Finset (Fin N)) (ta tb : SepTree (Fin N)) :
    (tenc (node s ta tb)).length = 2 + #s + (tenc ta).length + (tenc tb).length := by
  simp [tenc, length_lvs]; omega

variable (hnd : goal.Nodup) (hgl : goal.length ≤ N) (hW : 2 * P.data.length + 6 + N ≤ W)
  (hPW : ∀ j, P.data.getD j 0 ≤ W)
include hnd hgl hW hPW

/-- The numbering of a separator `s` at the input position `x` after the vertices `A`: the new
state, from the frames of `a` up to `i`. -/
theorem oAssign_core (h : OCore P W goal a A c) {i : ℕ} (hm : a.m = i + 1) {s : Finset (Fin N)}
    (hord : (a.it i).ord = lvs s) {d : Config} (hwd : WordsBounded W d)
    (d01 : d.nreg 1001 = 1) (d00 : d.nreg 0 = 0) (d1500 : d.nreg 1500 = P.data.length)
    (d03 : d.nreg 1503 = 2 * P.data.length + 6) (d04 : d.nreg 1504 = A.length)
    (d02 : d.nreg 1502 = i) {x : ℕ} (d05 : d.nreg 1505 = x) (d07 : d.nreg 1507 = #s)
    (hv : ∀ j < #s, P.data.getD (x + j) 0 = lv s j) (hx : x + #s ≤ P.data.length)
    {a' : OFr N} (ha'm : a'.m = i) (ha' : ∀ j < i, a'.it j = a.it j)
    (dmip : i ≤ d.nreg 1501 + 1)
    (dinp : ∀ j < a'.inps.length, P.data.getD (d.nreg 1501 + j) 0 = a'.inps.getD j 0)
    (dinpL : d.nreg 1501 + a'.inps.length ≤ P.data.length)
    (dfr : ∀ j < i, d.nmem (2 * j) = c.nmem (2 * j) ∧ d.nmem (2 * j + 1) = c.nmem (2 * j + 1))
    (drk : ∀ y, 2 * P.data.length + 6 ≤ y → d.nmem y = c.nmem y)
    (dout : d.output = []) :
    ∃ d' k, Exec P W oAssign d d' k ∧ k ≤ 8 * #s + 3 ∧ OCore P W goal a' (A ++ lvs s) d' := by
  have hgo := h.out
  rw [a.ords_succ hm, hord] at hgo
  have hA : A.length + #s ≤ N := by
    have := congrArg List.length hgo; simp [length_lvs] at this; omega
  have hnd' : (A ++ lvs s).Nodup := by
    rw [← hgo, ← List.append_assoc] at hnd; exact hnd.sublist (List.sublist_append_left _ _)
  obtain ⟨d', k, e, hk, hw', g04, gv, gm, gq, go, gr, grm⟩ := oAssign_exec (P := P) hwd
    (s := s) (p := A.length) d01 d05 d07 d03 d04 hv (by omega) (by omega) (by omega)
  refine ⟨d', k, e, hk, ?_⟩
  have Q : ∀ r, r ≠ 1504 → r ≠ 1508 → r ≠ 1509 → r ≠ 1510 → d'.nreg r = d.nreg r := gq
  exact
    { wb := hw'
      one := by rw [Q 1001 (by omega) (by omega) (by omega) (by omega), d01]
      r0 := by rw [Q 0 (by omega) (by omega) (by omega) (by omega), d00]
      rL := by rw [Q 1500 (by omega) (by omega) (by omega) (by omega), d1500]
      rR := by rw [Q 1503 (by omega) (by omega) (by omega) (by omega), d03]
      rm := by rw [Q 1502 (by omega) (by omega) (by omega) (by omega), d02, ha'm]
      rpos := by rw [g04, List.length_append, length_lvs]
      mip := by rw [Q 1501 (by omega) (by omega) (by omega) (by omega), ha'm]; exact dmip
      inp := fun j hj => by rw [Q 1501 (by omega) (by omega) (by omega) (by omega)]; exact dinp j hj
      inpL := by rw [Q 1501 (by omega) (by omega) (by omega) (by omega)]; exact dinpL
      fr := fun j hj => by
        rw [ha'm] at hj
        have hip := h.ip_le
        have hmip := h.mip
        rw [gm _ (fun j' hj' => by omega), gm _ (fun j' hj' => by omega), (dfr j hj).1,
          (dfr j hj).2, ha' j hj]
        exact h.fr j (by omega)
      out := by
        have e := (OFr.congr (a := a') (b := ⟨i, a.it⟩) ha'm (fun j hj => ha' j (by omega))).1
        rw [List.append_assoc, e]; exact hgo
      rk := fun j hj => by
        rw [List.length_append, length_lvs] at hj
        rcases Nat.lt_or_ge j A.length with hj' | hj'
        · rw [List.getD_append _ _ _ _ hj']
          rw [gm _ (fun j' hj'' e => by
            have e' : A.getD j 0 = lv s j' := by omega
            have hmem1 : A.getD j 0 ∈ A := by
              rw [List.getD_eq_getElem _ _ hj']; exact List.getElem_mem _
            have hmem2 : lv s j' ∈ lvs s := by
              rw [← getD_lvs s hj'']
              rw [List.getD_eq_getElem _ _ (by rw [length_lvs]; exact hj'')]
              exact List.getElem_mem _
            rw [e'] at hmem1
            exact List.disjoint_of_nodup_append hnd' hmem1 hmem2)]
          rw [drk _ (by omega)]; exact h.rk j hj'
        · rw [List.getD_append_right _ _ _ _ hj', getD_lvs s (by omega), gv _ (by omega)]
          omega
      output := by rw [go, dout] }

/-- **A separator round.** -/
theorem oSCase (h : OCore P W goal a A c) {i : ℕ} (hm : a.m = i + 1) {s : Finset (Fin N)}
    (hS : a.it i = .S s) :
    ∃ c' k, Exec P W oBody c c' k ∧ OCore P W goal ⟨i, a.it⟩ (A ++ lvs s) c' ∧
      (⟨i, a.it⟩ : OFr N).pot + k + 2 ≤ a.pot := by
  obtain ⟨c₁, k₁, e₁, hk₁, hw₁, g02, g05, g07, gm, gq, go, gr, grm⟩ := oPop_exec h hW hm
  have hf := h.fr i (by omega)
  rw [hS] at hf
  simp only [OIt.ok] at hf
  obtain ⟨hx1, hl, hxL, hv⟩ := hf
  have hinp := a.inps_succ hm
  rw [hS] at hinp
  simp only [OIt.inp, List.nil_append] at hinp
  have Q := fun r (a1 : r ≠ 1502) (a2 : r ≠ 1505) (a3 : r ≠ 1506) (a4 : r ≠ 1507) =>
    gq r a1 a2 a3 a4
  obtain ⟨c', k, e, hk, hc'⟩ := oAssign_core hnd hgl hW hPW h hm (s := s)
    (by rw [hS]; rfl) hw₁ (by rw [Q 1001 (by omega) (by omega) (by omega) (by omega), h.one])
    (by rw [Q 0 (by omega) (by omega) (by omega) (by omega), h.r0])
    (by rw [Q 1500 (by omega) (by omega) (by omega) (by omega), h.rL])
    (by rw [Q 1503 (by omega) (by omega) (by omega) (by omega), h.rR])
    (by rw [Q 1504 (by omega) (by omega) (by omega) (by omega), h.rpos]) g02 g05
    (by rw [g07, hl]) hv hxL (a' := ⟨i, a.it⟩) rfl (fun _ _ => rfl)
    (by rw [Q 1501 (by omega) (by omega) (by omega) (by omega)]; have := h.mip; omega)
    (fun j hj => by
      rw [Q 1501 (by omega) (by omega) (by omega) (by omega), h.inp j (by rw [hinp]; exact hj),
        hinp])
    (by rw [Q 1501 (by omega) (by omega) (by omega) (by omega), ← hinp]; exact h.inpL)
    (fun j _ => by rw [gm]; exact ⟨rfl, rfl⟩) (fun y _ => by rw [gm]) (by rw [go, h.output])
  have t0 : c₁.nreg 0 < c₁.nreg 1505 := by
    rw [Q 0 (by omega) (by omega) (by omega) (by omega), h.r0, g05]; omega
  refine ⟨c', k₁ + (k + 1), .seq e₁ (.ifLtN_true t0 e), hc', ?_⟩
  rw [a.pot_succ hm, hS]
  simp only [OIt.pot]
  omega

/-- **A leaf round.** -/
theorem oLeafCase (h : OCore P W goal a A c) {i : ℕ} (hm : a.m = i + 1) {s : Finset (Fin N)}
    (hT : a.it i = .T (leaf s)) :
    ∃ c' k, Exec P W oBody c c' k ∧ OCore P W goal ⟨i, a.it⟩ (A ++ lvs s) c' ∧
      (⟨i, a.it⟩ : OFr N).pot + k + 2 ≤ a.pot := by
  obtain ⟨c₁, k₁, e₁, hk₁, hw₁, g02, g05, g07, gm, gq, go, gr, grm⟩ := oPop_exec h hW hm
  have hf := h.fr i (by omega)
  rw [hT] at hf
  simp only [OIt.ok] at hf
  obtain ⟨hI1, hI2, hI3⟩ := inps_tenc h hm hT
  have hlen : (tenc (leaf s)).length = 2 + #s := by simp [tenc, length_lvs]; omega
  rw [hlen] at hI2 hI3
  have Q := fun r (a1 : r ≠ 1502) (a2 : r ≠ 1505) (a3 : r ≠ 1506) (a4 : r ≠ 1507) =>
    gq r a1 a2 a3 a4
  have r1501 : c₁.nreg 1501 = c.nreg 1501 := Q 1501 (by omega) (by omega) (by omega) (by omega)
  have w0 := hI1 0 (by omega)
  have w1 := hI1 1 (by omega)
  simp only [tenc, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at w0 w1
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, f08, f07, f05, f01, fm, fq, fo, fr, frm⟩ :=
    oParse0_exec (P := P) hw₁ (ip := c.nreg 1501) hPW
      (by rw [Q 1001 (by omega) (by omega) (by omega) (by omega), h.one]) r1501 w0 w1
      (by have := h.inpL; omega)
  have Q2 : ∀ r, r ≠ 1501 → r ≠ 1502 → r ≠ 1505 → r ≠ 1506 → r ≠ 1507 → r ≠ 1508 → r ≠ 1509 →
      c₂.nreg r = c.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 => by
    rw [fq r a1 a3 a5 a6 a7, Q r a2 a3 a4 a5]
  obtain ⟨c', k, e, hk, hc'⟩ := oAssign_core hnd hgl hW hPW h hm (s := s)
    (by rw [hT]; exact order_leaf_map s) hw₂
    (by rw [Q2 1001 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), h.one])
    (by rw [Q2 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), h.r0])
    (by rw [Q2 1500 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), h.rL])
    (by rw [Q2 1503 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), h.rR])
    (by rw [Q2 1504 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), h.rpos])
    (by rw [fq 1502 (by omega) (by omega) (by omega) (by omega) (by omega), g02]) f05 f07
    (fun j hj => by
      have := hI1 (2 + j) (by omega)
      rw [← Nat.add_assoc] at this
      rw [this]
      simp only [tenc, List.getD_cons_succ, show 2 + j = j + 1 + 1 by omega]
      exact getD_lvs s hj)
    (by omega) (a' := ⟨i, a.it⟩) rfl (fun _ _ => rfl)
    (by rw [f01]; have := h.mip; omega)
    (fun j hj => by rw [f01, ← hI2 j hj]; congr 1; omega)
    (by rw [f01]; omega)
    (fun j _ => by rw [fm, gm]; exact ⟨rfl, rfl⟩) (fun y _ => by rw [fm, gm])
    (by rw [fo, go, h.output])
  have t0 : ¬ c₁.nreg 0 < c₁.nreg 1505 := by
    rw [Q 0 (by omega) (by omega) (by omega) (by omega), h.r0, g05, hf]; omega
  have t1 : ¬ c₂.nreg 0 < c₂.nreg 1508 := by
    rw [Q2 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      h.r0, f08]; omega
  refine ⟨c', k₁ + ((k₂ + (k + 2)) + 2), .seq e₁ (.ifLtN_false t0 (.seq e₂ (.ifLtN_false t1 e))),
    hc', ?_⟩
  rw [a.pot_succ hm, hT]
  simp only [OIt.pot, hlen]
  omega

/-- **A node round.** -/
theorem oNodeCase (h : OCore P W goal a A c) {i : ℕ} (hm : a.m = i + 1) {s : Finset (Fin N)}
    {ta tb : SepTree (Fin N)} (hT : a.it i = .T (node s ta tb)) :
    ∃ c' k, Exec P W oBody c c' k ∧ OCore P W goal (oNodeFr a i s ta tb) A c' ∧
      (oNodeFr a i s ta tb).pot + k + 2 ≤ a.pot := by
  obtain ⟨c₁, k₁, e₁, hk₁, hw₁, g02, g05, g07, gm, gq, go, gr, grm⟩ := oPop_exec h hW hm
  have hf := h.fr i (by omega)
  rw [hT] at hf
  simp only [OIt.ok] at hf
  obtain ⟨hI1, hI2, hI3⟩ := inps_tenc h hm hT
  have hlen := length_tenc_node s ta tb
  rw [hlen] at hI2 hI3
  have hmip := h.mip
  rw [hm] at hmip
  have Q := fun r (a1 : r ≠ 1502) (a2 : r ≠ 1505) (a3 : r ≠ 1506) (a4 : r ≠ 1507) =>
    gq r a1 a2 a3 a4
  have r1501 : c₁.nreg 1501 = c.nreg 1501 := Q 1501 (by omega) (by omega) (by omega) (by omega)
  have w0 := hI1 0 (by omega)
  have w1 := hI1 1 (by omega)
  simp only [tenc, List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero] at w0 w1
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, f08, f07, f05, f01, fm, fq, fo, fr, frm⟩ :=
    oParse0_exec (P := P) hw₁ (ip := c.nreg 1501) hPW
      (by rw [Q 1001 (by omega) (by omega) (by omega) (by omega), h.one]) r1501 w0 w1
      (by omega)
  have Q2 : ∀ r, r ≠ 1501 → r ≠ 1502 → r ≠ 1505 → r ≠ 1506 → r ≠ 1507 → r ≠ 1508 → r ≠ 1509 →
      c₂.nreg r = c.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 => by
    rw [fq r a1 a3 a5 a6 a7, Q r a2 a3 a4 a5]
  obtain ⟨c₃, k₃, e₃, hk₃, hw₃, p02, p0, p1, p2, p3, pm, pq, po, pr, prm⟩ :=
    oPush_exec (P := P) hw₂ (i := i)
      (by rw [Q2 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), h.r0])
      (by rw [Q2 1001 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), h.one])
      (by rw [fq 1502 (by omega) (by omega) (by omega) (by omega) (by omega), g02]) f05 f07
      (by omega)
  have Q3 : ∀ r, r ≠ 1501 → r ≠ 1502 → r ≠ 1505 → r ≠ 1506 → r ≠ 1507 → r ≠ 1508 → r ≠ 1509 →
      c₃.nreg r = c.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 => by
    rw [pq r a2 a4, Q2 r a1 a2 a3 a4 a5 a6 a7]
  have t0 : ¬ c₁.nreg 0 < c₁.nreg 1505 := by
    rw [Q 0 (by omega) (by omega) (by omega) (by omega), h.r0, g05, hf]; omega
  have t1 : c₂.nreg 0 < c₂.nreg 1508 := by
    rw [Q2 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      h.r0, f08]; omega
  have hne := oNodeFr_eq a i s ta tb
  have r1501' : c₃.nreg 1501 = c.nreg 1501 + 2 + #s := by
    rw [pq 1501 (by omega) (by omega), f01]
  refine ⟨c₃, k₁ + ((k₂ + (k₃ + 1)) + 2),
    .seq e₁ (.ifLtN_false t0 (.seq e₂ (.ifLtN_true t1 e₃))), ?_, ?_⟩
  · exact
    { wb := hw₃
      one := by rw [Q3 1001 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), h.one]
      r0 := by rw [Q3 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), h.r0]
      rL := by rw [Q3 1500 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), h.rL]
      rR := by rw [Q3 1503 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), h.rR]
      rm := by rw [p02]; rfl
      rpos := by rw [Q3 1504 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), h.rpos]
      mip := by rw [r1501']; show i + 3 ≤ _; omega
      inp := fun j hj => by
        rw [r1501', hne.2.1, ← List.append_assoc]
        rw [hne.2.1, ← List.append_assoc, List.length_append] at hj
        rcases Nat.lt_or_ge j (tenc ta ++ tenc tb).length with hj' | hj'
        · rw [List.getD_append _ _ _ _ hj', ← getD_tenc_node s ta tb j]
          rw [show c.nreg 1501 + 2 + #s + j = c.nreg 1501 + (2 + #s + j) by omega]
          exact hI1 _ (by rw [hlen]; rw [List.length_append] at hj'; omega)
        · rw [List.getD_append_right _ _ _ _ hj']
          simp only [List.length_append] at hj hj' ⊢
          have := hI2 (j - ((tenc ta).length + (tenc tb).length)) (by omega)
          rw [← this]; congr 1; omega
      inpL := by
        rw [r1501', hne.2.1]; simp only [List.length_append]; omega
      fr := fun j hj => by
        change j < i + 3 at hj
        by_cases e2 : j = i + 2
        · subst e2
          simp only [oNodeFr, ↓reduceIte, OIt.ok]; exact p3
        by_cases e1 : j = i + 1
        · subst e1
          simp only [oNodeFr, show i + 1 ≠ i + 2 by omega, ↓reduceIte, OIt.ok]; exact p2
        by_cases e0 : j = i
        · subst e0
          simp only [oNodeFr, show j ≠ j + 2 by omega, show j ≠ j + 1 by omega, ↓reduceIte,
            OIt.ok]
          refine ⟨by rw [p0]; omega, p1, by rw [p0]; omega, fun l hl => ?_⟩
          rw [p0]
          have := hI1 (2 + l) (by omega)
          rw [← Nat.add_assoc] at this
          rw [this]
          simp only [tenc, List.getD_cons_succ, show 2 + l = l + 1 + 1 by omega]
          rw [List.getD_append _ _ _ _ (by simp [length_lvs]; omega),
            List.getD_append _ _ _ _ (by rw [length_lvs]; exact hl)]
          exact getD_lvs s hl
        · have hj' : j < i := by omega
          simp only [oNodeFr, e2, e1, e0, ↓reduceIte]
          rw [pm _ (Or.inl (by omega)), pm _ (Or.inl (by omega)), fm, gm]
          exact h.fr j (by omega)
      out := by
        rw [hne.1]
        have := h.out
        rw [a.ords_succ hm, hT] at this
        simp only [OIt.ord, order_node_map, List.append_assoc] at this
        exact this
      rk := fun j hj => by
        rw [pm _ (Or.inr (by omega)), fm, gm]; exact h.rk j hj
      output := by rw [po, fo, go, h.output] }
  · rw [hne.2.2, a.pot_succ hm, hT]
    simp only [OIt.pot, hlen]
    omega

/-- **A round of the loop.** -/
theorem oBody_exec (h : OCore P W goal a A c) (h0 : 0 < a.m) :
    ∃ (a' : OFr N) (A' : List ℕ) (c' : Config) (k : ℕ), Exec P W oBody c c' k ∧
      OCore P W goal a' A' c' ∧ a'.pot + k + 2 ≤ a.pot := by
  obtain ⟨i, hm⟩ : ∃ i, a.m = i + 1 := ⟨a.m - 1, by omega⟩
  rcases hT : a.it i with t | s
  · rcases t with s | ⟨s, ta, tb⟩
    · obtain ⟨c', k, e, h', hp⟩ := oLeafCase hnd hgl hW hPW h hm hT
      exact ⟨_, _, c', k, e, h', hp⟩
    · obtain ⟨c', k, e, h', hp⟩ := oNodeCase hnd hgl hW hPW h hm hT
      exact ⟨_, _, c', k, e, h', hp⟩
  · obtain ⟨c', k, e, h', hp⟩ := oSCase hnd hgl hW hPW h hm hT
    exact ⟨_, _, c', k, e, h', hp⟩

/-- **The loop**: all items done, the vertices numbered in the order `goal`. -/
theorem oLoop_exec (h : OCore P W goal a A c) :
    ∃ c' k, Exec P W oLoop c c' k ∧ OCore P W goal ⟨0, a.it⟩ goal c' ∧ k ≤ a.pot + 2 := by
  obtain ⟨⟨a', A'⟩, c', k, e, h', hn, hk⟩ := whileLtN_abs (P := P) (W := W) (a := 0) (b := 1502)
    (body := oBody) (fun (x : OFr N × List ℕ) c => OCore P W goal x.1 x.2 c)
    (fun x => x.1.pot) (fun _ _ h => h.wb)
    (fun x c hx ht => by
      rw [hx.r0, hx.rm] at ht
      obtain ⟨a'', A'', c'', k, e, h'', hk⟩ := oBody_exec hnd hgl hW hPW hx ht
      exact ⟨(a'', A''), c'', k, e, h'', hk⟩) (s := (a, A)) h
  simp only at h' hk
  rw [h'.r0, h'.rm] at hn
  have h0 : a'.m = 0 := by omega
  have hA : A' = goal := by
    have := h'.out
    simp [OFr.ords, h0] at this
    exact this
  subst hA
  refine ⟨c', k, e, ?_, hk⟩
  exact { h' with
    rm := by rw [h'.rm, h0]
    mip := by simp
    inp := fun j hj => by simp [OFr.inps] at hj
    inpL := by have := h'.inpL; simp [OFr.inps]; omega
    fr := fun j hj => by simp at hj
    out := by simp [OFr.ords] }

end rounds

/-! ### Start and printing -/

theorem oInit_exec (hW : 2 * P.data.length + 6 ≤ W) :
    ∃ c k, Exec P W oInit initConfig c k ∧ k = 8 ∧ WordsBounded W c ∧ c.nreg 1001 = 1 ∧
      c.nreg 0 = 0 ∧ c.nreg 1500 = P.data.length ∧ c.nreg 1503 = 2 * P.data.length + 6 ∧
      c.nreg 1501 = 0 ∧ c.nreg 1504 = 0 ∧ c.nreg 1502 = 1 ∧ c.nmem = (fun _ => 0) ∧
      c.output = [] := by
  have hw := wordsBounded_initConfig W
  unfold oInit
  exec_block
  rotate_right
  · refine ⟨rfl, ‹_›, by config_simp, by config_simp; rfl, by config_simp, ?_, by config_simp,
      by config_simp, by config_simp, rfl, rfl⟩
    config_simp; omega
  all_goals (config_simp <;> simp (config := {failIfUnchanged := false}) only
    [show initConfig.nreg 1500 = 0 from rfl] <;> omega)

theorem oPrint_exec {d : Config} (hw : WordsBounded W d) {aR K : ℕ} (h01 : d.nreg 1001 = 1)
    (h03 : d.nreg 1503 = aR) (h04 : d.nreg 1504 = K) (hb : aR + K ≤ W) :
    ∃ d' k, Exec P W oPrint d d' k ∧ d'.output = d.output ++ (List.range K).map
      (fun u => d.nmem (aR + u)) ∧ k ≤ 6 * K + 3 := by
  obtain ⟨d₁, k₁, e₁, hk₁, hw₁, g08, q₁, m₁, o₁⟩ : ∃ d₁ k₁,
      Exec P W (block [.constN 1508 0]) d d₁ k₁ ∧ k₁ = 1 ∧ WordsBounded W d₁ ∧
      d₁.nreg 1508 = 0 ∧ (∀ r, r ≠ 1508 → d₁.nreg r = d.nreg r) ∧ d₁.nmem = d.nmem ∧
      d₁.output = d.output := by
    exec_block
    rotate_right
    · exact ⟨rfl, ‹_›, by config_simp, fun r hr => by simp [upd_apply, hr], rfl, rfl⟩
    · omega
  let I : ℕ → Config → Prop := fun j c => WordsBounded W c ∧ c.nreg 1508 = j ∧
    c.nreg 1504 = K ∧ c.nreg 1503 = aR ∧ c.nreg 1001 = 1 ∧ c.nmem = d.nmem ∧
    c.output = d.output ++ (List.range j).map (fun u => d.nmem (aR + u))
  obtain ⟨d₂, k₂, e₂, h₂, hk₂⟩ := Exec.forN (P := P) (W := W) (ri := 1508) (rN := 1504)
    (N := K) (lo := 0) (B := 4) (body := oPrBody) I (fun j c h => ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun j c h hj => by
      obtain ⟨hw', h08', h04', h03', h01', hm', ho'⟩ := h
      unfold oPrBody
      exec_block
      rotate_right
      · refine ⟨⟨‹WordsBounded _ _›, by config_simp; rw [h08', h01'], by config_simp; exact h04',
          by config_simp; exact h03', by config_simp; exact h01', by config_simp; exact hm', ?_⟩,
          by omega⟩
        config_simp
        rw [ho', h03', h08', hm', List.range_succ, List.map_append, List.append_assoc]
        rfl
      all_goals (config_simp <;> simp (config := {failIfUnchanged := false}) only
        [h08', h01', h03'] <;> omega))
    (Nat.zero_le _) ⟨hw₁, g08, by rw [q₁ 1504 (by omega), h04], by rw [q₁ 1503 (by omega), h03],
      by rw [q₁ 1001 (by omega), h01], m₁, by rw [o₁]; simp⟩
  obtain ⟨-, -, -, -, -, -, ho₂⟩ := h₂
  exact ⟨d₂, k₁ + k₂, .seq e₁ e₂, ho₂, by omega⟩

/-! ### The order program -/

theorem length_order_univ {G' : SimpleGraph (Fin N)} {t : SepTree (Fin N)}
    (hd : IsDissection G' t) (hv : t.verts = univ) : t.order.length = N := by
  rw [← List.toFinset_card_of_nodup (nodup_order hd)]
  have : t.order.toFinset = univ := by ext x; simp [mem_order, hv]
  rw [this, card_univ, Fintype.card_fin]

theorem tenc_le (t : SepTree (Fin N)) : ∀ x ∈ tenc t, x ≤ N + 1 := by
  have hl : ∀ s : Finset (Fin N), ∀ x ∈ lvs s, x ≤ N + 1 := fun s x hx => by
    simp only [lvs, List.mem_map, List.mem_range] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have := lv_ltN s hj; omega
  induction t with
  | leaf s =>
    intro x hx
    simp only [tenc, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · omega
    · have := card_le_N s; omega
    · exact hl s x hx
  | node s a b iha ihb =>
    intro x hx
    simp only [tenc, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | rfl | (hx | hx) | hx
    · omega
    · have := card_le_N s; omega
    · exact hl s x hx
    · exact iha x hx
    · exact ihb x hx

/-- **The ranks of the nested dissection order on the machine.** For a separator tree `t` of a
graph on `Fin n` covering all vertices, the program `ordProg` run on the words `tenc t` (the
output of the tree program), with words of at least `2 |tenc t| + n + 6`, halts within
`21 |tenc t| + 6 n + 14` steps and prints `rkWords (ndPerm t hd hv)`, the input of the
nested-dissection stage `nbuild`. -/
theorem ordProg_runsWithin {G' : SimpleGraph (Fin N)} (t : SepTree (Fin N))
    (hd : IsDissection G' t) (hv : t.verts = univ) {W : ℕ}
    (hW : 2 * (tenc t).length + 6 + N ≤ W) :
    RunsWithin (compile ordProg 0 ++ [Instr.halt]) (DetMod.inp (tenc t)) W
      (21 * (tenc t).length + 6 * N + 14) (SparseMod.rkWords (ndPerm t hd hv)) := by
  set P := DetMod.inp (tenc t) with hPdef
  have hPd : P.data = tenc t := rfl
  set goal := t.order.map Fin.val with hgoal
  have hlen := length_order_univ hd hv
  have hnd : goal.Nodup := (nodup_order hd).map Fin.val_injective
  have hgl : goal.length ≤ N := by simp [goal, hlen]
  have hW' : 2 * P.data.length + 6 + N ≤ W := by rw [hPd]; exact hW
  have hPW : ∀ j, P.data.getD j 0 ≤ W := fun j => by
    rw [hPd, List.getD_eq_getElem?_getD]
    rcases h : (tenc t)[j]? with _ | x
    · simp
    · have := tenc_le t x (List.mem_of_getElem? h); simp; omega
  obtain ⟨c₀, k₀, e₀, hk₀, hw₀, i01, i00, i1500, i1503, i1501, i1504, i1502, im, io⟩ :=
    oInit_exec (P := P) (W := W) (by omega)
  have hc₀ : OCore P W goal ⟨1, fun _ => .T t⟩ [] c₀ :=
    { wb := hw₀, one := i01, r0 := i00, rL := i1500, rR := i1503, rm := i1502
      rpos := i1504
      mip := by rw [i1501]
      inp := fun j hj => by
        rw [i1501, Nat.zero_add, hPd]
        simp [OFr.inps, OIt.inp]
      inpL := by rw [i1501, hPd]; simp [OFr.inps, OIt.inp]
      fr := fun i hi => by
        obtain rfl : i = 0 := by simp only at hi; omega
        simp only [OIt.ok, im]
      out := by simp [OFr.ords, OIt.ord, goal]
      rk := fun i hi => by simp at hi
      output := io }
  obtain ⟨c₁, k₁, e₁, hc₁, hk₁⟩ := oLoop_exec hnd hgl hW' hPW hc₀
  obtain ⟨c₂, k₂, e₂, ho₂, hk₂⟩ := oPrint_exec (P := P) hc₁.wb hc₁.one hc₁.rR hc₁.rpos
    (by simp only [goal, List.length_map, hlen]; omega)
  have hpot : (⟨1, fun _ => .T t⟩ : OFr N).pot = 21 * (tenc t).length := by
    simp [OFr.pot, OIt.pot]
  refine RunsWithin.mono_steps (runsWithin_of_exec_output (.seq e₀ (.seq e₁ e₂)) ?_)
    (by simp only [goal, List.length_map, hlen] at hk₂; omega)
  rw [ho₂, hc₁.output, List.nil_append]
  apply List.ext_getElem
  · simp [goal, hlen, SparseMod.rkWords]
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, SparseMod.rkWords, List.getElem_ofFn]
    simp only [goal, List.length_map, hlen, List.length_range] at h1
    rw [ndPerm_symm_apply]
    set x : Fin N := ⟨i, h1⟩
    have hx : x ∈ t.order := mem_order.2 (by rw [hv]; exact mem_univ x)
    have hidx : t.order.idxOf x < t.order.length := List.idxOf_lt_length_of_mem hx
    have hg : goal.getD (t.order.idxOf x) 0 = i := by
      rw [List.getD_eq_getElem _ _ (by simpa [goal] using hidx)]
      simp [goal, List.getElem_idxOf hidx, x]
    have := hc₁.rk (t.order.idxOf x) (by simpa [goal] using hidx)
    rw [hg] at this
    rw [hPd] at this
    exact this

end Piece

end PlanarSeparator
