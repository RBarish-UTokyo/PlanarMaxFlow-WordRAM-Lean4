module

public import PlanarFlow.Monge.FRSpec

/-!
# Laying out an input of FR-Dijkstra

The machine program `PlanarFlow.Monge.FR.frProg` reads its input from memory in the layout `Prm`:
the lengths of the dense distance graph on the corners `0, …, b - 1`, the prices, and the explicit
arcs in compressed form (the arcs of each tail consecutive, `off x` the first arc of the tail `x`).
`mkPrm N b D p r Es` lays out the vertices `0, …, N - 1`, the matrix `D`, the prices `p`, the root
`r` and a list `Es` of explicit arcs (tail, head, length): the arcs are listed tail by tail
(`arcList`), and the memory regions follow each other.

* `mkPrm_lay`: the layout meets `Lay` when `1 ≤ b ≤ N`, `r < N` and the ends of the arcs are
  vertices.
* `tl_mkPrm`: the tail recovered by the program (`FR.tl`) is the tail of the arc.
* `mem_exArcs_mkPrm`, `exists_exArcs_mkPrm`: the explicit arcs of the input (`FR.exArcs`) are the
  arcs of `Es`, read in `Fin N`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

open Finset

/-! ### The arcs tail by tail -/

/-- The arcs of `Es` with tail `x`. -/
def blk (Es : List (ℕ × ℕ × ℤ)) (x : ℕ) : List (ℕ × ℕ × ℤ) := Es.filter fun a => a.1 = x

/-- The arcs with tail `< u`, tail by tail. -/
def pre (Es : List (ℕ × ℕ × ℤ)) (u : ℕ) : List (ℕ × ℕ × ℤ) := (List.range u).flatMap (blk Es)

theorem pre_succ (Es : List (ℕ × ℕ × ℤ)) (u : ℕ) : pre Es (u + 1) = pre Es u ++ blk Es u := by
  simp [pre, List.range_succ, List.flatMap_append]

theorem length_pre_mono (Es : List (ℕ × ℕ × ℤ)) {u v : ℕ} (h : u ≤ v) :
    (pre Es u).length ≤ (pre Es v).length := by
  induction v with
  | zero => rw [Nat.le_zero.1 h]
  | succ v ih =>
    rcases Nat.lt_or_ge u (v + 1) with h' | h'
    · rw [pre_succ, List.length_append]; have := ih (by omega); omega
    · rw [show u = v + 1 by omega]

theorem pre_add (Es : List (ℕ × ℕ × ℤ)) (u k : ℕ) :
    ∃ rest, pre Es (u + k) = pre Es u ++ rest := by
  induction k with
  | zero => exact ⟨[], by simp⟩
  | succ k ih =>
    obtain ⟨rest, h⟩ := ih
    exact ⟨rest ++ blk Es (u + k), by rw [← add_assoc, pre_succ, h, List.append_assoc]⟩

theorem mem_pre {Es : List (ℕ × ℕ × ℤ)} {u : ℕ} {a : ℕ × ℕ × ℤ} :
    a ∈ pre Es u ↔ a ∈ Es ∧ a.1 < u := by
  simp only [pre, List.mem_flatMap, List.mem_range, blk, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, ha, rfl⟩; exact ⟨ha, hx⟩
  · rintro ⟨ha, hu⟩; exact ⟨a.1, hu, ha, rfl⟩

theorem ite_of_pos {c : Prop} [Decidable c] {α : Sort*} {x y : α} (h : c) :
    (if c then x else y) = x := by simp [h]

theorem ite_of_neg {c : Prop} [Decidable c] {α : Sort*} {x y : α} (h : ¬ c) :
    (if c then x else y) = y := by simp [h]

theorem countP_split (L : List (ℕ × ℕ × ℤ)) (u : ℕ) :
    L.countP (fun a => decide (a.1 < u)) + L.countP (fun a => decide (a.1 = u)) =
      L.countP (fun a => decide (a.1 < u + 1)) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    by_cases h1 : a.1 < u
    · rw [ite_of_pos (by simpa using h1), ite_of_neg (by simp; omega), ite_of_pos (by simp; omega)]; omega
    · by_cases h2 : a.1 = u
      · rw [ite_of_neg (by simpa using h1), ite_of_pos (by simpa using h2), ite_of_pos (by simp; omega)]
        omega
      · rw [ite_of_neg (by simpa using h1), ite_of_neg (by simpa using h2), ite_of_neg (by simp; omega)]
        omega

theorem length_pre_le (Es : List (ℕ × ℕ × ℤ)) (u : ℕ) : (pre Es u).length ≤ Es.length := by
  have hnd : ∀ u, (pre Es u).length = (Es.filter fun a => a.1 < u).length := by
    intro u
    induction u with
    | zero => simp [pre]
    | succ u ih =>
      rw [pre_succ, List.length_append, ih, blk, ← List.countP_eq_length_filter,
        ← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
      exact countP_split Es u
  rw [hnd]; exact List.length_filter_le _ _

/-- All the arcs with tail `< N`, tail by tail. -/
def arcList (N : ℕ) (Es : List (ℕ × ℕ × ℤ)) : List (ℕ × ℕ × ℤ) := pre Es N

/-! ### The layout -/

/-- The levels reserved for the half blocks, as in `Prm.Lv`. -/
def lvOf (b : ℕ) : ℕ := Nat.log 2 b + 1

/-- The layout of an input of FR-Dijkstra. -/
noncomputable def mkPrm (N b : ℕ) (D : ℕ → ℕ → ℤ) (p : ℕ → ℤ) (r : ℕ) (Es : List (ℕ × ℕ × ℤ)) :
    Prm :=
  let m := (arcList N Es).length
  let wb := b * b + N + N + 1 + m + m + N + N
  let hb := wb + 3 * N
  let tb := hb + 16 * b * lvOf b
  let bh := tb + 32 * b * lvOf b
  let rb := bh + 16 * 2 ^ (Nat.log 2 (b * lvOf b) + 1)
  { N := N, b := b, m := m, Db := 0, pb := b * b, ob := b * b + N, lb := b * b + N + N + 1 + m,
    sb := b * b + N + N + 1 + m + m, db := b * b + N + N + 1 + m + m + N, wb := wb,
    W := wb + 3 * N + 16 * b * lvOf b + 16 * b + 16 + rb + 8 * b * lvOf b * lvOf b + 4 * b + 16,
    D := D, p := p, off := fun x => (pre Es x).length,
    dst := fun t => ((arcList N Es).getD t (0, 0, 0)).2.1,
    len := fun t => ((arcList N Es).getD t (0, 0, 0)).2.2, r := r }

variable {N b : ℕ} {D : ℕ → ℕ → ℤ} {p : ℕ → ℤ} {r : ℕ} {Es : List (ℕ × ℕ × ℤ)}

theorem mkPrm_m : (mkPrm N b D p r Es).m = (arcList N Es).length := rfl

theorem mkPrm_off_zero : (mkPrm N b D p r Es).off 0 = 0 := by simp [mkPrm, pre]

theorem mem_arcList {a : ℕ × ℕ × ℤ} : a ∈ arcList N Es ↔ a ∈ Es ∧ a.1 < N := mem_pre

/-- **The layout meets `Lay`.** -/
theorem mkPrm_lay (hb : 1 ≤ b) (hbN : b ≤ N) (hr : r < N) (hhd : ∀ a ∈ Es, a.2.1 < N) :
    Lay (mkPrm N b D p r Es) where
  b_pos := hb
  bN := hbN
  r_lt := hr
  m1 := by simp [mkPrm]
  m2 := by simp [mkPrm]
  m3 := by simp [mkPrm]
  m4 := by simp [mkPrm]
  m5 := by simp [mkPrm]
  m6 := by simp [mkPrm]
  w := by simp only [mkPrm, Prm.Lv, lvOf]; omega
  wx := by simp only [mkPrm, Prm.Lv, lvOf, Prm.rb, Prm.bh, Prm.tb, Prm.hb, Prm.TB]; omega
  off_mono x _ := length_pre_mono Es (Nat.le_succ x)
  off_last := rfl
  dst_lt t ht := by
    simp only [mkPrm] at ht ⊢
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact hhd _ (mem_arcList.1 (List.getElem_mem ht)).1

/-- **The tail recovered by the program is the tail of the arc.** -/
theorem tl_mkPrm {t : ℕ} (ht : t < (arcList N Es).length) :
    tl (mkPrm N b D p r Es) t = ((arcList N Es)[t]).1 := by
  classical
  set P := mkPrm N b D p r Es
  have hoff : ∀ u, P.off u = (pre Es u).length := fun _ => rfl
  -- the block of `t`
  have hex : ∃ u, t < (pre Es (u + 1)).length := ⟨N, by
    have := length_pre_mono Es (Nat.le_succ N); exact lt_of_lt_of_le ht this⟩
  set k := Nat.find hex
  have hk1 : t < (pre Es (k + 1)).length := Nat.find_spec hex
  have hk0 : (pre Es k).length ≤ t := by
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0]; simp [pre]
    · have := Nat.find_min hex (show k - 1 < k by omega)
      rw [Nat.sub_add_cancel hpos] at this; omega
  have hkN : k < N := by
    by_contra hge
    have hNk := length_pre_mono Es (show N ≤ k by omega)
    have ht2 : t < (pre Es N).length := ht
    omega
  -- the arc `t` lies in the block of `k`
  have hget : ((arcList N Es)[t]).1 = k := by
    obtain ⟨rest, hrest⟩ := pre_add Es (k + 1) (N - (k + 1))
    rw [show k + 1 + (N - (k + 1)) = N by omega] at hrest
    have e : (arcList N Es)[t] = (pre Es (k + 1))[t] := by
      unfold arcList
      simp only [hrest]
      rw [List.getElem_append_left hk1]
    rw [e]
    have hmem : (pre Es (k + 1))[t] ∈ pre Es (k + 1) := List.getElem_mem hk1
    have e2 : (pre Es (k + 1))[t] = (blk Es k)[t - (pre Es k).length]'(by
        rw [pre_succ, List.length_append] at hk1; omega) := by
      simp only [pre_succ]
      rw [List.getElem_append_right (by omega)]
    rw [e2]
    have := List.getElem_mem (l := blk Es k) (n := t - (pre Es k).length)
      (by rw [pre_succ, List.length_append] at hk1; omega)
    simp only [blk, List.mem_filter, decide_eq_true_eq] at this
    exact this.2
  rw [hget]
  unfold tl
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by change k ≤ N - 1; omega, fun _ => by rw [hoff]; exact hk0, fun n hn hnN => ?_⟩
  rw [hoff]
  have := length_pre_mono Es (show k + 1 ≤ n by omega)
  omega

/-- **The explicit arcs of the input are the arcs of `Es`**, read in `Fin N`. -/
theorem exArcs_mkPrm_get (hN : 0 < N) {t : ℕ} (ht : t < (exArcs (mkPrm N b D p r Es) hN).length) :
    (exArcs (mkPrm N b D p r Es) hN)[t] =
      (fv (mkPrm N b D p r Es) hN ((arcList N Es)[t]'(by simpa [exArcs, mkPrm] using ht)).1,
        fv (mkPrm N b D p r Es) hN ((arcList N Es)[t]'(by simpa [exArcs, mkPrm] using ht)).2.1,
        ((arcList N Es)[t]'(by simpa [exArcs, mkPrm] using ht)).2.2) := by
  have ht' : t < (arcList N Es).length := by simpa [exArcs, mkPrm] using ht
  simp only [exArcs, List.getElem_ofFn]
  rw [tl_mkPrm ht']
  simp only [mkPrm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]

theorem length_exArcs_mkPrm (hN : 0 < N) :
    (exArcs (mkPrm N b D p r Es) hN).length = (arcList N Es).length := by
  simp [exArcs, mkPrm]

end FR

end Monge

end PlanarFlow
