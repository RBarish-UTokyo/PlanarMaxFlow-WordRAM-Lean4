module

public import PlanarFlow.BKMNW.MfFrame
public import PlanarFlow.BKMNW.LinCmp
public import PlanarFlow.BKMNW.IteR23

/-!
# The frames of the child calls, as functions of the parent's frame and the separator

At a node call `(.node l r π, Hs, σ)` with the separator vertices `C = π.path.mverts`, the child
calls have the holes `childHoles Hs C = (Hs.filter (Disjoint · C)) ++ [newHole Hs C]`. This file
expresses everything a child frame holds through per-dart data of the parent frame and the
separator data `CV` (the tail in `C`), `HM` (the hole meets `C`), `LP` (the dart in `l.piece`):

* `hlab_pos_iff`, `hlab_mem`, `hlab_unique` (with pairwise disjoint holes, the label of a vertex
  of a hole `H` points to `H`), **`mem_newHole_iff'`** (the tail is in the new hole iff it is in
  `C` or its hole meets `C`).
* **`lrk_child`** (the rank of a vertex for the child: `1` on the new hole, as for the parent
  elsewhere), `hcnt` (the kept holes before a position), **`hlab_child`** (the child's hole
  label: `#kept + 1` on the new hole, `hcnt (hlab - 1) + 1` on a kept hole, `0` off the holes),
  `cnt_hcnt` (the machine's count of the kept-hole flags is `hcnt`), `length_childHoles_eq`.
* **`mem_pdarts_child`**: a dart of the parent piece map is a dart of a child piece map iff it is
  in the child's piece and not both its ends are in the new hole.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### Hole labels -/

lemma getD_eq_get {α : Type*} {l : List α} {d : α} {i : ℕ} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

lemma hlab_pos_iff {Hs : List (Finset V)} {v : V} : 0 < hlab Hs v ↔ v ∈ hunion Hs := by
  unfold hlab; split_ifs with h <;> simp [h]

lemma hlab_mem {Hs : List (Finset V)} {v : V} (h : 0 < hlab Hs v) :
    hlab Hs v - 1 < Hs.length ∧ v ∈ Hs.getD (hlab Hs v - 1) ∅ := by
  have hv : v ∈ hunion Hs := hlab_pos_iff.1 h
  have e : hlab Hs v - 1 = Hs.findIdx (fun H => decide (v ∈ H)) := by
    unfold hlab; simp [hv]
  obtain ⟨H, hH, hvH⟩ := mem_hunion.1 hv
  have hlt : Hs.findIdx (fun H => decide (v ∈ H)) < Hs.length :=
    List.findIdx_lt_length_of_exists ⟨H, hH, by simpa using hvH⟩
  rw [e]
  refine ⟨hlt, ?_⟩
  rw [getD_eq_get hlt]
  simpa using List.findIdx_getElem (w := hlt)

/-- **With pairwise disjoint holes, the label of a vertex of a hole points to that hole.** -/
lemma hlab_unique {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {H : Finset V} (hH : H ∈ Hs)
    {v : V} (hv : v ∈ H) : 0 < hlab Hs v ∧ Hs.getD (hlab Hs v - 1) ∅ = H := by
  have hp : 0 < hlab Hs v := hlab_pos_iff.2 (mem_hunion.2 ⟨H, hH, hv⟩)
  obtain ⟨hlt, hm⟩ := hlab_mem hp
  refine ⟨hp, ?_⟩
  by_contra hne
  rw [getD_eq_get hlt] at hm hne
  exact disjoint_left.1 (disjoint_of_pairwise hd (List.getElem_mem hlt) hH hne) hm hv

/-- **The new hole**, through the hole labels. -/
lemma mem_newHole_iff' {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {C : Finset V} {v : V} :
    v ∈ newHole Hs C ↔ v ∈ C ∨ (0 < hlab Hs v ∧ ¬ Disjoint (Hs.getD (hlab Hs v - 1) ∅) C) := by
  rw [mem_newHole]
  constructor
  · rintro (h | ⟨H, hH, hHC, hv⟩)
    · exact Or.inl h
    · obtain ⟨hp, e⟩ := hlab_unique hd hH hv
      exact Or.inr ⟨hp, by rw [e]; exact hHC⟩
  · rintro (h | ⟨hp, hHC⟩)
    · exact Or.inl h
    · obtain ⟨hlt, hm⟩ := hlab_mem hp
      rw [getD_eq_get hlt] at hm hHC
      exact Or.inr ⟨_, List.getElem_mem hlt, hHC, hm⟩

lemma newHole_subset {Hs : List (Finset V)} {C : Finset V} : newHole Hs C ⊆ hunion Hs ∪ C := by
  intro v hv
  rcases mem_newHole.1 hv with h | ⟨H, hH, -, hv⟩
  · exact mem_union_right _ h
  · exact mem_union_left _ (mem_hunion.2 ⟨H, hH, hv⟩)

/-- **The rank of a vertex for a child**: `1` on the new hole, that of the parent elsewhere. -/
lemma lrk_child {S T : Finset V} {Hs : List (Finset V)} {C : Finset V} (hSC : Disjoint S C)
    (_hTC : Disjoint T C) (hS : Disjoint S (hunion Hs)) (v : V) :
    lrk S T (hunion (childHoles Hs C)) v =
      if v ∈ newHole Hs C then 1 else lrk S T (hunion Hs) v := by
  rw [hunion_childHoles]
  unfold lrk
  by_cases hN : v ∈ newHole Hs C
  · have h1 := newHole_subset hN
    have hvS : v ∉ S := fun h => by
      rcases mem_union.1 h1 with h1 | h1
      · exact disjoint_left.1 hS h h1
      · exact disjoint_left.1 hSC h h1
    simp [hN, hvS, h1]
  · have hvC : v ∉ C := fun h => hN (subset_newHole h)
    simp [hN, hvC]

/-- The kept holes (those disjoint from `C`) before the position `j`. -/
def hcnt (Hs : List (Finset V)) (C : Finset V) (j : ℕ) : ℕ :=
  ((Hs.take j).filter fun H => decide (Disjoint H C)).length

lemma length_childHoles_eq (Hs : List (Finset V)) (C : Finset V) :
    (childHoles Hs C).length = (Hs.filter fun H => decide (Disjoint H C)).length + 1 := by
  simp [childHoles]

/-- The position of the first element with `p` in a filtered list. -/
lemma findIdx_filter {α : Type*} (p q : α → Bool) :
    ∀ (l : List α) (h : l.findIdx p < l.length), q (l[l.findIdx p]) = true →
      (l.filter q).findIdx p = ((l.take (l.findIdx p)).filter q).length
  | [], h, _ => by simp at h
  | a :: l, h, hq => by
    by_cases hp : p a = true
    · have e : (a :: l).findIdx p = 0 := by rw [List.findIdx_cons]; simp [hp]
      simp only [e, List.getElem_cons_zero] at hq
      rw [e, List.filter_cons, iteT hq, List.findIdx_cons]
      simp [hp]
    · have e : (a :: l).findIdx p = l.findIdx p + 1 := by rw [List.findIdx_cons]; simp [hp]
      have h' : l.findIdx p < l.length := by rw [e] at h; simpa using h
      have hq' : q (l[l.findIdx p]) = true := by
        simp only [e, List.getElem_cons_succ] at hq; exact hq
      have ih := findIdx_filter p q l h' hq'
      rw [e, List.take_succ_cons, List.filter_cons, List.filter_cons]
      by_cases hqa : q a = true
      · rw [iteT hqa, iteT hqa, List.findIdx_cons]; simp [hp, ih]
      · rw [iteF hqa, iteF hqa]; exact ih

/-- No element of a list with `p` false everywhere: the first index is the length. -/
lemma findIdx_eq_length {α : Type*} {p : α → Bool} {l : List α} (h : ∀ a ∈ l, p a = false) :
    l.findIdx p = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findIdx_cons, iteF (by simp [h a (List.mem_cons_self)]),
      ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    rfl

/-- **The hole label of a vertex for a child.** -/
lemma hlab_child {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {C : Finset V} (v : V) :
    hlab (childHoles Hs C) v =
      if v ∈ newHole Hs C then (Hs.filter fun H => decide (Disjoint H C)).length + 1
      else if hlab Hs v = 0 then 0 else hcnt Hs C (hlab Hs v - 1) + 1 := by
  set q : Finset V → Bool := fun H => decide (Disjoint H C)
  set p : Finset V → Bool := fun H => decide (v ∈ H)
  by_cases hN : v ∈ newHole Hs C
  · rw [iteT hN]
    have hu : v ∈ hunion (childHoles Hs C) := by
      rw [hunion_childHoles]; exact newHole_subset hN
    -- no kept hole contains `v`
    have hno : ∀ H ∈ Hs.filter q, p H = false := by
      intro H hH
      simp only [q, List.mem_filter, decide_eq_true_eq] at hH
      simp only [p, decide_eq_false_iff_not]
      intro hv
      rcases mem_newHole.1 hN with h | ⟨H', hH', hH'C, hv'⟩
      · exact disjoint_left.1 hH.2 hv h
      · have hne : H ≠ H' := fun e => hH'C (e ▸ hH.2)
        exact disjoint_left.1 (disjoint_of_pairwise hd hH.1 hH' hne) hv hv'
    unfold hlab
    rw [iteT hu]
    show (Hs.filter q ++ [newHole Hs C]).findIdx p + 1 = _
    rw [List.findIdx_append, findIdx_eq_length hno, iteF (lt_irrefl _), List.findIdx_cons]
    simp [p, hN]
  · rw [iteF hN]
    have hvC : v ∉ C := fun h => hN (subset_newHole h)
    by_cases hv : v ∈ hunion Hs
    · have hp0 : 0 < hlab Hs v := hlab_pos_iff.2 hv
      rw [iteF (by omega)]
      obtain ⟨hlt, hm⟩ := hlab_mem hp0
      rw [getD_eq_get hlt] at hm
      have hHC : Disjoint Hs[hlab Hs v - 1] C := by
        by_contra hc
        exact hN (mem_newHole.2 (Or.inr ⟨_, List.getElem_mem hlt, hc, hm⟩))
      have hu : v ∈ hunion (childHoles Hs C) := by
        rw [hunion_childHoles]; exact mem_union_left _ hv
      have e : hlab Hs v - 1 = Hs.findIdx p := by unfold hlab; simp [hv, p]
      have hlt' : Hs.findIdx p < Hs.length := e ▸ hlt
      have hq : q (Hs[Hs.findIdx p]) = true := by
        simp only [q, decide_eq_true_eq]; simp only [← e]; exact hHC
      have key := findIdx_filter p q Hs hlt' hq
      have hlt2 : (Hs.filter q).findIdx p < (Hs.filter q).length := by
        apply List.findIdx_lt_length_of_exists
        exact ⟨_, List.mem_filter.2 ⟨List.getElem_mem hlt', hq⟩,
          List.findIdx_getElem (w := hlt')⟩
      have hl : hlab (childHoles Hs C) v = (childHoles Hs C).findIdx p + 1 := by
        unfold hlab; rw [iteT hu]
      rw [hl]
      show (Hs.filter q ++ [newHole Hs C]).findIdx p + 1 = _
      rw [List.findIdx_append, iteT hlt2, key, ← e]
      rfl
    · have hv' : v ∉ hunion (childHoles Hs C) := by
        rw [hunion_childHoles]; simp [hv, hvC]
      have h0 : hlab Hs v = 0 := by unfold hlab; simp [hv]
      rw [iteT h0]
      unfold hlab; simp [hv']

/-- **The machine's count of the kept-hole flags.** -/
lemma cnt_hcnt (Hs : List (Finset V)) (C : Finset V) :
    ∀ j ≤ Hs.length,
      cnt (fun i => if Disjoint (Hs.getD i ∅) C then 1 else 0) j = hcnt Hs C j
  | 0, _ => by simp [cnt, hcnt]
  | j + 1, hj => by
    rw [cnt_succ, cnt_hcnt Hs C j (by omega)]
    unfold hcnt
    rw [List.take_add_one, List.filter_append, List.length_append]
    have hlt : j < Hs.length := by omega
    rw [List.getElem?_eq_getElem hlt, getD_eq_get hlt]
    by_cases h : Disjoint Hs[j] C <;> simp [h]

/-! ### The darts of the child piece maps -/

/-- **A dart of the parent piece map is a dart of a child piece map** iff it is in the child's
piece and not both its ends are in the new hole. -/
lemma mem_pdarts_child {P Pc : Finset D} {Hs : List (Finset V)} {C : Finset V} {y : D}
    (hy : y ∈ pdarts M P Hs) :
    y ∈ pdarts M Pc (childHoles Hs C) ↔
      y ∈ Pc ∧ ¬ (M.tail y ∈ newHole Hs C ∧ M.tail (M.rev y) ∈ newHole Hs C) := by
  have hyB := (mem_pdarts.1 hy).2
  rw [mem_pdarts]
  refine and_congr_right fun _ => not_congr ⟨?_, ?_⟩
  · rintro ⟨H, hH, h1, h2⟩
    simp only [childHoles, List.mem_append, List.mem_filter, List.mem_singleton,
      decide_eq_true_eq] at hH
    rcases hH with ⟨hH, -⟩ | rfl
    · exact absurd ⟨H, hH, h1, h2⟩ hyB
    · exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨newHole Hs C, by simp [childHoles], h1, h2⟩

end MfDrv

end BKMNW

end PlanarFlow
