module

public import PlanarFlow.BKMNW.SmallD
public import PlanarFlow.BKMNW.MfFrameSplit

/-!
# One step of `smD`: its pure description

`smD M pk S T P Hs` (`SmallD.lean`) decides, at a small piece, between a leaf and four kinds of
split (peel a vertex next to a hole, dump the darts inside the holes, a pendant edge, an edge).
For a program computing one step from per-dart arrays:

* hole labels with pairwise disjoint holes: `sm_mem_iff_of_pw`, `hlab_congr`,
  **`inner_iff_hlab`** (`Inner` from the hole labels of the two ends),
  **`hlab_eq_succ_iff`** (`hlab v = j + 1 ↔ v ∈ Hs[j]`);
* `lrk_eq_three_iff`, `lrk_st_iff` (the terminals from the ranks `lrk`);
* **`smD_piece`** (the piece of `smD … P Hs` is `P`, for a rev-closed `P`);
* **`smD_ntag`** (`smD` is a node iff `2 < #P`, `smB ≠ ∅`, and `smX ≠ ∅ ∨ smY = ∅ ∨` the piece has
  a dart inside a hole);
* `SmForm` (the shape of a node: left child `smD` of `L` with the holes `childHoles Hs C`, right
  child a leaf, the path's darts `{x, rev x}` or none, its vertices `C`), **`smD_form`** (the
  three node cases).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function MfDrv

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-! ### Hole labels with pairwise disjoint holes -/

lemma sm_mem_iff_of_pw {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {H : Finset V}
    (hH : H ∈ Hs) {v w : V} (hv : v ∈ H) (hw : w ∈ H) : ∀ H' ∈ Hs, (v ∈ H' ↔ w ∈ H') := by
  intro H' hH'
  by_cases e : H = H'
  · subst e; exact ⟨fun _ => hw, fun _ => hv⟩
  · have := disjoint_of_pairwise hd hH hH' e
    exact ⟨fun h => absurd h (disjoint_left.1 this hv), fun h => absurd h (disjoint_left.1 this hw)⟩

lemma sm_findIdx_congr {v w : V} :
    ∀ (Hs : List (Finset V)), (∀ H ∈ Hs, v ∈ H ↔ w ∈ H) →
      Hs.findIdx (fun H => decide (v ∈ H)) = Hs.findIdx (fun H => decide (w ∈ H))
  | [], _ => rfl
  | a :: l, h => by
    rw [List.findIdx_cons, List.findIdx_cons,
      show decide (v ∈ a) = decide (w ∈ a) by simp [h a List.mem_cons_self],
      sm_findIdx_congr l (fun H hH => h H (List.mem_cons_of_mem _ hH))]

lemma hlab_congr {Hs : List (Finset V)} {v w : V} (h : ∀ H ∈ Hs, v ∈ H ↔ w ∈ H) :
    hlab Hs v = hlab Hs w := by
  have hu : v ∈ hunion Hs ↔ w ∈ hunion Hs := by
    simp only [mem_hunion]
    exact ⟨fun ⟨H, hH, hv⟩ => ⟨H, hH, (h H hH).1 hv⟩, fun ⟨H, hH, hw⟩ => ⟨H, hH, (h H hH).2 hw⟩⟩
  unfold hlab
  rw [sm_findIdx_congr Hs h]
  by_cases hv : v ∈ hunion Hs
  · rw [iteT hv, iteT (hu.1 hv)]
  · rw [iteF hv, iteF (fun hw => hv (hu.2 hw))]

lemma sm_getD_mem {Hs : List (Finset V)} {i : ℕ} (hi : i < Hs.length) : Hs.getD i ∅ ∈ Hs := by
  rw [getD_eq_get hi]; exact List.getElem_mem hi

/-- **A dart is inside a hole iff its two ends have the same positive hole label.** -/
lemma inner_iff_hlab {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) (d : D) :
    Inner M Hs d ↔ 0 < hlab Hs (M.tail d) ∧ hlab Hs (M.tail d) = hlab Hs (M.head d) := by
  constructor
  · rintro ⟨H, hH, ht, hh⟩
    exact ⟨hlab_pos_iff.2 (mem_hunion.2 ⟨H, hH, ht⟩), hlab_congr (sm_mem_iff_of_pw hd hH ht hh)⟩
  · rintro ⟨hp, he⟩
    obtain ⟨hlt, hm⟩ := hlab_mem hp
    have hp' : 0 < hlab Hs (M.head d) := he ▸ hp
    obtain ⟨-, hm'⟩ := hlab_mem hp'
    rw [← he] at hm'
    exact ⟨_, sm_getD_mem hlt, hm, hm'⟩

/-- **With pairwise disjoint holes, the label `j + 1` means the hole `Hs[j]`.** -/
lemma hlab_eq_succ_iff {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {j : ℕ}
    (hj : j < Hs.length) {v : V} : hlab Hs v = j + 1 ↔ v ∈ Hs.getD j ∅ := by
  constructor
  · intro h
    have := (hlab_mem (Hs := Hs) (v := v) (by omega)).2
    rwa [h, Nat.add_sub_cancel] at this
  · intro hv
    have hH := sm_getD_mem hj
    obtain ⟨hp, e⟩ := hlab_unique hd hH hv
    obtain ⟨hlt, -⟩ := hlab_mem hp
    by_contra hne
    have hne' : hlab Hs v - 1 ≠ j := fun h => hne (by omega)
    rw [getD_eq_get hlt, getD_eq_get hj] at e
    rw [getD_eq_get hj] at hv
    have hv' : v ∈ Hs[hlab Hs v - 1] := by rw [e]; exact hv
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact disjoint_left.1 (List.pairwise_iff_getElem.1 hd _ _ hlt hj h) hv' hv
    · exact disjoint_left.1 (List.pairwise_iff_getElem.1 hd _ _ hj hlt h) hv hv'

/-! ### The ranks of the terminals -/

lemma lrk_eq_three_iff {S T A : Finset V} {v : V} : lrk S T A v = 3 ↔ v ∉ S ∪ T ∪ A := by
  unfold lrk; split_ifs <;> simp_all

lemma lrk_st_iff {S T A : Finset V} {v : V} (hA : v ∉ A) :
    (lrk S T A v = 0 ∨ lrk S T A v = 2) ↔ v ∈ S ∪ T := by
  unfold lrk; split_ifs <;> simp_all

/-! ### The piece and the tag of `smD` -/

lemma revClosed_pdarts' {P : Finset D} (hP : RevClosed M P) (Hs : List (Finset V)) :
    RevClosed M (pdarts M P Hs) := fun d hd => by
  rw [mem_pdarts] at hd ⊢
  exact ⟨hP d hd.1, fun h => hd.2 (inner_rev.1 h)⟩

lemma sm_card_sdiff_lt {P : Finset D} {x : D} (hx : x ∈ P) (y : D) :
    (P \ {x, y}).card < P.card :=
  card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨sdiff_subset, fun e => by
    have : x ∈ P \ {x, y} := by rw [e]; exact hx
    simp at this⟩)

lemma smX_sub {S T : Finset V} {P : Finset D} {Hs : List (Finset V)} :
    smX M S T P Hs ⊆ P := fun _ h => (mem_pdarts.1 (mem_filter.1 h).1).1

lemma smY_sub {P : Finset D} {Hs : List (Finset V)} : smY M P Hs ⊆ P := filter_subset _ _

lemma smB_sub {S T : Finset V} {P : Finset D} {Hs : List (Finset V)} :
    smB M S T P Hs ⊆ P := fun _ h => (mem_pdarts.1 (mem_filter.1 h).1).1

/-- **The piece of `smD … P Hs` is `P`.** -/
theorem smD_piece {pk : Finset D → D} {S T : Finset V}
    (hpk : ∀ X : Finset D, X.Nonempty → pk X ∈ X) :
    ∀ (n : ℕ) (P : Finset D) (Hs : List (Finset V)), P.card = n → RevClosed M P →
      (smD M pk S T P Hs).piece = P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Hs hn hP
  rw [smD]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
  all_goals try rfl
  · have hx := smX_sub (hpk _ h2)
    simp only [ADec.piece]
    rw [ih _ (hn ▸ h4) _ _ rfl (revClosed_sdiff_pair hP _)]
    exact sdiff_union_of_subset (insert_subset_iff.2 ⟨hx, singleton_subset_iff.2 (hP _ hx)⟩)
  · simp only [ADec.piece]
    rw [ih _ (hn ▸ h6) _ _ rfl (revClosed_pdarts' hP _)]
    exact union_sdiff_of_subset (pdarts_subset _ _)
  all_goals
    have hB : (smB M S T P Hs).Nonempty := by
      push Not at h1; obtain ⟨-, d, hd, hb⟩ := h1; exact ⟨d, mem_filter.2 ⟨hd, hb⟩⟩
    have hx := smB_sub (hpk _ hB)
    simp only [ADec.piece]
    rw [ih _ (hn ▸ ‹(P \ _).card < P.card›) _ _ rfl (revClosed_sdiff_pair hP _)]
    exact sdiff_union_of_subset (insert_subset_iff.2 ⟨hx, singleton_subset_iff.2 (hP _ hx)⟩)

lemma sm_hL {S T : Finset V} {P : Finset D} {Hs : List (Finset V)} (hn : 2 < P.card)
    (hB : (smB M S T P Hs).Nonempty) :
    ¬ (P.card ≤ 2 ∨ ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs) := by
  rintro (h | h)
  · omega
  · obtain ⟨d, hd⟩ := hB
    obtain ⟨hd, hb⟩ := mem_filter.1 hd
    exact hb (h d hd)

lemma sm_B_of {S T : Finset V} {P : Finset D} {Hs : List (Finset V)}
    (h : ¬ (P.card ≤ 2 ∨ ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs)) :
    2 < P.card ∧ (smB M S T P Hs).Nonempty := by
  push Not at h
  obtain ⟨h1, d, hd, hb⟩ := h
  exact ⟨by omega, d, mem_filter.2 ⟨hd, hb⟩⟩

lemma smX_ne {S T : Finset V} {P : Finset D} {Hs : List (Finset V)} {x : D}
    (hx : x ∈ smX M S T P Hs) : M.head x ≠ M.tail x := by
  obtain ⟨-, hv, ha⟩ := mem_filter.1 hx
  exact fun e => hv (mem_union_right _ (e ▸ ha))

/-- **When `smD` is a node.** -/
theorem smD_ntag {pk : Finset D → D} {S T : Finset V}
    (hpk : ∀ X : Finset D, X.Nonempty → pk X ∈ X) (hloop : ∀ d, M.head d ≠ M.tail d)
    (P : Finset D) (Hs : List (Finset V)) :
    ntag (smD M pk S T P Hs) = 1 ↔ (2 < P.card ∧ (smB M S T P Hs).Nonempty) ∧
      ((smX M S T P Hs).Nonempty ∨ ¬ (smY M P Hs).Nonempty ∨
        (pdarts M P Hs).card < P.card) := by
  rw [smD]
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9
  · simp only [ntag, zero_ne_one, false_iff]
    rintro ⟨⟨hn, hB⟩, -⟩
    exact sm_hL hn hB h1
  · simp only [ntag, true_iff]; exact ⟨sm_B_of h1, Or.inl h2⟩
  · exact absurd (sm_card_sdiff_lt (smX_sub (hpk _ h2)) _) h4
  · exact absurd (smX_ne (hpk _ h2)) h3
  · simp only [ntag, true_iff]; exact ⟨sm_B_of h1, Or.inr (Or.inr h6)⟩
  · simp only [ntag, zero_ne_one, false_iff]
    rintro ⟨-, h | h | h⟩
    · exact h2 h
    · exact h h5
    · exact h6 h
  · simp only [ntag, true_iff]; exact ⟨sm_B_of h1, Or.inr (Or.inl h5)⟩
  · simp only [ntag, true_iff]; exact ⟨sm_B_of h1, Or.inr (Or.inl h5)⟩
  · exact absurd (hloop _) h9
  · exact absurd (sm_card_sdiff_lt (smB_sub (hpk _ (sm_B_of h1).2)) _) h7

variable (M) in
/-- **The shape of a node of `smD`**: the left child is `smD` of `L` (the darts of the piece map
if `lpm`, else the piece without `x`, `rev x`) with the holes of the children of `C` (the vertices
of the path: `{tail x, head x}` if `up`, else `{tail x}`), the right child a leaf, the path's
darts `{x, rev x}` if `up`, else none. -/
def SmForm (pk : Finset D → D) (S T : Finset V) (P : Finset D) (Hs : List (Finset V)) (x : D)
    (up lpm : Bool) : Prop :=
  ∃ (R : Finset D) (π : HSep M),
    smD M pk S T P Hs = .node (smD M pk S T (if lpm then pdarts M P Hs else P \ {x, M.rev x})
      (childHoles Hs (if up then {M.tail x, M.head x} else {M.tail x}))) (.leaf R) π ∧
    π.path.darts.toFinset = (if up then {x, M.rev x} else ∅) ∧
    π.path.mverts = (if up then {M.tail x, M.head x} else {M.tail x})

lemma sm_darts_pair (x : D) (hx : M.head x ≠ M.tail x) :
    (SPath.ofDart x hx).toH.darts.toFinset = {x, M.rev x} := by
  rw [SPath.toH_darts, SPath.ofDart_darts]; simp

lemma sm_darts_point (x : D) (v : V) : (SPath.point (M' := M) x v).toH.darts.toFinset = ∅ := by
  rw [SPath.toH_darts, SPath.point_darts']; rfl

/-- **The three node cases of `smD`.** -/
theorem smD_form {pk : Finset D → D} {S T : Finset V}
    (hpk : ∀ X : Finset D, X.Nonempty → pk X ∈ X) (hloop : ∀ d, M.head d ≠ M.tail d)
    {P : Finset D} {Hs : List (Finset V)} (hn : 2 < P.card) (hB : (smB M S T P Hs).Nonempty) :
    ((smX M S T P Hs).Nonempty → SmForm M pk S T P Hs (pk (smX M S T P Hs)) true false) ∧
    (¬ (smX M S T P Hs).Nonempty → (smY M P Hs).Nonempty → (pdarts M P Hs).card < P.card →
      SmForm M pk S T P Hs (pk (smY M P Hs)) false true) ∧
    (¬ (smX M S T P Hs).Nonempty → ¬ (smY M P Hs).Nonempty →
      SmForm M pk S T P Hs (pk (smB M S T P Hs))
        (decide (M.head (pk (smB M S T P Hs)) ∉ S ∪ T)) false) := by
  have hL := sm_hL hn hB
  refine ⟨fun hX => ?_, fun hX hY hlt => ?_, fun hX hY => ?_⟩
  · have hne := smX_ne (hpk _ hX)
    have hm := HPath.toH_ofDart_mverts (M := M) _ hne
    refine ⟨{pk (smX M S T P Hs), M.rev (pk (smX M S T P Hs))}, peelSep _ hne, ?_,
      sm_darts_pair _ hne, ?_⟩
    · rw [smD_peel hL hX hne (sm_card_sdiff_lt (smX_sub (hpk _ hX)) _)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show (peelSep _ hne).path.mverts = _ from hm]
    · simp only [↓reduceIte]; exact hm
  · have hm := HPath.toH_point_mverts (M := M) (pk (smY M P Hs)) (M.tail (pk (smY M P Hs)))
    refine ⟨P \ pdarts M P Hs, holeSep (M := M) (pk (smY M P Hs)) (M.tail (pk (smY M P Hs))),
      ?_, sm_darts_point _ _, ?_⟩
    · rw [smD_dump hL hX hY hlt]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [show (holeSep (M := M) (pk (smY M P Hs)) (M.tail (pk (smY M P Hs)))).path.mverts = _
        from hm]
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hm
  · have hlt := sm_card_sdiff_lt (smB_sub (hpk _ hB)) (M.rev (pk (smB M S T P Hs)))
    by_cases hw : M.head (pk (smB M S T P Hs)) ∈ S ∪ T
    · have hm := HPath.toH_point_mverts (M := M) (pk (smB M S T P Hs))
        (M.tail (pk (smB M S T P Hs)))
      refine ⟨{pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))},
        (SPath.point (M' := M) (pk (smB M S T P Hs)) (M.tail (pk (smB M S T P Hs)))).toSep,
        ?_, ?_, ?_⟩
      · rw [smD_pend hL hX hY hlt hw]
        simp only [hw, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [show (SPath.point (M' := M) (pk (smB M S T P Hs))
          (M.tail (pk (smB M S T P Hs)))).toSep.path.mverts = _ from hm]
      · simp only [hw, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact sm_darts_point (M := M) _ _
      · simp only [hw, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact hm
    · have hne := hloop (pk (smB M S T P Hs))
      have hm := HPath.toH_ofDart_mverts (M := M) _ hne
      refine ⟨{pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))}, (SPath.ofDart _ hne).toSep,
        ?_, ?_, ?_⟩
      · rw [smD_edge hL hX hY hlt hw hne]
        simp only [hw, not_false_eq_true, decide_true, Bool.false_eq_true, ↓reduceIte]
        rw [show (SPath.ofDart _ hne).toSep.path.mverts = _ from hm]
      · simp only [hw, not_false_eq_true, decide_true, ↓reduceIte]
        exact sm_darts_pair _ hne
      · simp only [hw, not_false_eq_true, decide_true, ↓reduceIte]; exact hm

end BKMNW

end PlanarFlow
