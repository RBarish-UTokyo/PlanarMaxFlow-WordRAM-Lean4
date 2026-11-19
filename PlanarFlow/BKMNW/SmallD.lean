module

public import PlanarFlow.BKMNW.Exist

/-!
# The decomposition of the small pieces, as a function

`exists_decOK_small` with every choice made by a function `pk` picking an element of a nonempty
set of darts: **`smD pk S T P Hs`** (well-founded recursion on `#P`: a leaf if the leaf solver
applies; else peel a vertex next to a hole (`splitOK_peel`), or split off the darts inside the
holes (`splitOK_dump`), or split off a pendant edge (`splitOK_pendant`) or an edge
(`splitOK_edge`)), and **`smD_spec`**: it meets `DecOK` for every flag.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
open Classical in
/-- The darts of the piece map from a vertex off the terminals and the holes into a hole. -/
noncomputable def smX (S T : Finset V) (P : Finset D) (Hs : List (Finset V)) : Finset D :=
  (pdarts M P Hs).filter fun x => M.tail x ∉ S ∪ T ∪ hunion Hs ∧ M.head x ∈ hunion Hs

variable (M) in
/-- The darts of the piece leaving a hole. -/
def smY (P : Finset D) (Hs : List (Finset V)) : Finset D :=
  P.filter fun y => M.tail y ∈ hunion Hs

variable (M) in
open Classical in
/-- The darts of the piece map leaving a vertex off the terminals and the holes. -/
noncomputable def smB (S T : Finset V) (P : Finset D) (Hs : List (Finset V)) : Finset D :=
  (pdarts M P Hs).filter fun d => M.tail d ∉ S ∪ T ∪ hunion Hs

variable (M) in
open Classical in
/-- **The decomposition of a small piece, as a function** of the piece and its holes, given a
function `pk` picking an element of a nonempty set of darts. -/
noncomputable def smD (pk : Finset D → D) (S T : Finset V) (P : Finset D)
    (Hs : List (Finset V)) : ADec M :=
  if P.card ≤ 2 ∨ ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs then .leaf P
  else if (smX M S T P Hs).Nonempty then
    if hne : M.head (pk (smX M S T P Hs)) ≠ M.tail (pk (smX M S T P Hs)) then
      if hlt : (P \ {pk (smX M S T P Hs), M.rev (pk (smX M S T P Hs))}).card < P.card then
        .node (smD pk S T (P \ {pk (smX M S T P Hs), M.rev (pk (smX M S T P Hs))})
          (childHoles Hs (peelSep _ hne).path.mverts))
          (.leaf {pk (smX M S T P Hs), M.rev (pk (smX M S T P Hs))}) (peelSep _ hne)
      else .leaf P
    else .leaf P
  else if (smY M P Hs).Nonempty then
    if hlt : (pdarts M P Hs).card < P.card then
      .node (smD pk S T (pdarts M P Hs) (childHoles Hs
          (holeSep (M := M) (pk (smY M P Hs)) (M.tail (pk (smY M P Hs)))).path.mverts))
        (.leaf (P \ pdarts M P Hs)) (holeSep (pk (smY M P Hs)) (M.tail (pk (smY M P Hs))))
    else .leaf P
  else
    if hlt : (P \ {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))}).card < P.card then
      if M.head (pk (smB M S T P Hs)) ∈ S ∪ T then
        .node (smD pk S T (P \ {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))})
            (childHoles Hs (SPath.point (M' := M) (pk (smB M S T P Hs))
              (M.tail (pk (smB M S T P Hs)))).toSep.path.mverts))
          (.leaf {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))})
          (SPath.point (M' := M) (pk (smB M S T P Hs)) (M.tail (pk (smB M S T P Hs)))).toSep
      else if hne : M.head (pk (smB M S T P Hs)) ≠ M.tail (pk (smB M S T P Hs)) then
        .node (smD pk S T (P \ {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))})
            (childHoles Hs (SPath.ofDart _ hne).toSep.path.mverts))
          (.leaf {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))}) (SPath.ofDart _ hne).toSep
      else .leaf P
    else .leaf P
termination_by P.card
decreasing_by all_goals assumption

section Eqs

variable {pk : Finset D → D} {S T : Finset V} {P : Finset D} {Hs : List (Finset V)}

lemma smD_leaf (hL : P.card ≤ 2 ∨ ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs) :
    smD M pk S T P Hs = .leaf P := by
  rw [smD]; simp only [hL, ↓reduceIte]

lemma smD_peel (hL : ¬ (P.card ≤ 2 ∨ ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs))
    (hX : (smX M S T P Hs).Nonempty)
    (hne : M.head (pk (smX M S T P Hs)) ≠ M.tail (pk (smX M S T P Hs)))
    (hlt : (P \ {pk (smX M S T P Hs), M.rev (pk (smX M S T P Hs))}).card < P.card) :
    smD M pk S T P Hs = .node (smD M pk S T (P \ {pk (smX M S T P Hs),
        M.rev (pk (smX M S T P Hs))}) (childHoles Hs (peelSep _ hne).path.mverts))
      (.leaf {pk (smX M S T P Hs), M.rev (pk (smX M S T P Hs))}) (peelSep _ hne) := by
  rw [smD]; simp only [hL, hX, ↓reduceIte]
  rw [dite_eq_left_of_eq_true (eq_true hne)]; simp only [hlt, ↓reduceDIte]

lemma smD_dump (hL : ¬ (P.card ≤ 2 ∨ ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs))
    (hX : ¬ (smX M S T P Hs).Nonempty) (hY : (smY M P Hs).Nonempty)
    (hlt : (pdarts M P Hs).card < P.card) :
    smD M pk S T P Hs = .node (smD M pk S T (pdarts M P Hs) (childHoles Hs
          (holeSep (M := M) (pk (smY M P Hs)) (M.tail (pk (smY M P Hs)))).path.mverts))
        (.leaf (P \ pdarts M P Hs)) (holeSep (pk (smY M P Hs)) (M.tail (pk (smY M P Hs)))) := by
  rw [smD]; simp only [hL, hX, hY, hlt, ↓reduceIte, ↓reduceDIte]

lemma smD_pend (hL : ¬ (P.card ≤ 2 ∨ ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs))
    (hX : ¬ (smX M S T P Hs).Nonempty) (hY : ¬ (smY M P Hs).Nonempty)
    (hlt : (P \ {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))}).card < P.card)
    (hw : M.head (pk (smB M S T P Hs)) ∈ S ∪ T) :
    smD M pk S T P Hs = .node (smD M pk S T (P \ {pk (smB M S T P Hs),
          M.rev (pk (smB M S T P Hs))})
        (childHoles Hs (SPath.point (M' := M) (pk (smB M S T P Hs))
          (M.tail (pk (smB M S T P Hs)))).toSep.path.mverts))
      (.leaf {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))})
      (SPath.point (M' := M) (pk (smB M S T P Hs)) (M.tail (pk (smB M S T P Hs)))).toSep := by
  rw [smD]; simp only [hL, hX, hY, hlt, hw, ↓reduceIte, ↓reduceDIte]

lemma smD_edge (hL : ¬ (P.card ≤ 2 ∨ ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs))
    (hX : ¬ (smX M S T P Hs).Nonempty) (hY : ¬ (smY M P Hs).Nonempty)
    (hlt : (P \ {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))}).card < P.card)
    (hw : M.head (pk (smB M S T P Hs)) ∉ S ∪ T)
    (hne : M.head (pk (smB M S T P Hs)) ≠ M.tail (pk (smB M S T P Hs))) :
    smD M pk S T P Hs = .node (smD M pk S T (P \ {pk (smB M S T P Hs),
          M.rev (pk (smB M S T P Hs))})
        (childHoles Hs (SPath.ofDart _ hne).toSep.path.mverts))
      (.leaf {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))}) (SPath.ofDart _ hne).toSep := by
  rw [smD]; simp only [hL, hX, hY, hlt, hw, ↓reduceIte, ↓reduceDIte]
  rw [dite_eq_left_of_eq_true (eq_true hne)]

end Eqs

/-- **The small decomposition function is correct** (`exists_decOK_small` for `smD`): for a
picking function `pk` (an element of every nonempty set), `smD M pk S T P Hs` meets `DecOK` for
every flag. -/
theorem smD_spec {S T : Finset V} {κ η s : ℕ} (hκ : 1 ≤ κ) (hη : 1 ≤ η)
    (hloop : ∀ d, M.head d ≠ M.tail d)
    (hdeg : ∀ t ∈ S ∪ T, ∀ d d', M.tail d = t → M.tail d' = t → d = d')
    {pk : Finset D → D} (hpk : ∀ X : Finset D, X.Nonempty → pk X ∈ X) :
    ∀ (n : ℕ) (P : Finset D) (Hs : List (Finset V)), P.card = n → PcOK M S T P Hs →
      P.card ≤ s → nTouch M P Hs ≤ η → ∀ b, DecOK M S T κ η s P Hs b (smD M pk S T P Hs) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P Hs hn hP hs ht
  by_cases hL : P.card ≤ 2 ∨ ∀ d ∈ pdarts M P Hs, M.tail d ∈ S ∪ T ∪ hunion Hs
  · rw [smD_leaf hL]; exact decOK_leaf hP hL
  have hL' := hL
  push Not at hL'
  obtain ⟨hcard, d₀', hd₀', hbad'⟩ := hL'
  by_cases hX : (smX M S T P Hs).Nonempty
  · -- merge a vertex next to a hole into the hole
    have hxm := hpk _ hX
    obtain ⟨hx, hv, ha⟩ := mem_filter.1 hxm
    have hne : M.head (pk (smX M S T P Hs)) ≠ M.tail (pk (smX M S T P Hs)) :=
      fun e => hv (mem_union_right _ (e ▸ ha))
    have h := splitOK_peel (κ := κ) (η := η) hP hx hv ha hcard hne
    rw [smD_peel hL hX hne h.card_l_lt]
    have hm : (peelSep _ hne).path.mverts =
        {M.tail (pk (smX M S T P Hs)), M.head (pk (smX M S T P Hs))} :=
      HPath.toH_ofDart_mverts _ hne
    obtain ⟨H, hH, haH⟩ := mem_hunion.1 ha
    have htl : nTouch M (P \ {pk (smX M S T P Hs), M.rev (pk (smX M S T P Hs))})
        (childHoles Hs (peelSep _ hne).path.mverts) ≤ η :=
      (nTouch_childHoles_le_of_meet sdiff_subset hH
        ⟨M.head (pk (smX M S T P Hs)), haH, M.rev (pk (smX M S T P Hs)),
          hP.rev _ (mem_pdarts.1 hx).1, by rw [CombMap.tail_rev]⟩
        (by rw [hm]; exact not_disjoint_iff.2 ⟨_, haH, by simp⟩)).trans ht
    exact decOK_node_leaf h hP hs ht (Or.inl card_le_two)
      (ih _ (hn ▸ h.card_l_lt) _ _ rfl (h.pcOK_l hP) ((card_le_card sdiff_subset).trans hs) htl)
  have hB1 : ∀ x ∈ pdarts M P Hs, M.tail x ∉ S ∪ T ∪ hunion Hs → M.head x ∉ hunion Hs :=
    fun x hx hv ha => hX ⟨x, mem_filter.2 ⟨hx, hv, ha⟩⟩
  have hB2 : ∀ y ∈ pdarts M P Hs, M.tail y ∉ hunion Hs := by
    intro y hy hyH
    exact hbad' (tail_mem_of_no_peel hdeg hP hB1 hy hyH d₀' hd₀')
  by_cases hY : (smY M P Hs).Nonempty
  · -- split off the darts inside the holes
    obtain ⟨hyP, hyH⟩ := mem_filter.1 (hpk _ hY)
    have hyn : pk (smY M P Hs) ∉ pdarts M P Hs := fun h => hB2 _ h hyH
    have h := splitOK_dump (κ := κ) (η := η) hP hyP hyH hyn hd₀'
    rw [smD_dump hL hX hY h.card_l_lt]
    obtain ⟨H, hH, hyH'⟩ := mem_hunion.1 hyH
    have hm : (holeSep (M := M) (pk (smY M P Hs)) (M.tail (pk (smY M P Hs)))).path.mverts =
        {M.tail (pk (smY M P Hs))} := HPath.toH_point_mverts _ _
    have htl : nTouch M (pdarts M P Hs)
        (childHoles Hs (holeSep (M := M) (pk (smY M P Hs))
          (M.tail (pk (smY M P Hs)))).path.mverts) ≤ η :=
      (nTouch_childHoles_le_of_meet (pdarts_subset _ _) hH ⟨_, hyH', _, hyP, rfl⟩
        (by rw [hm]; exact not_disjoint_iff.2 ⟨_, hyH', mem_singleton_self _⟩)).trans ht
    refine decOK_node_leaf h hP hs ht (Or.inr fun d hd => ?_)
      (ih _ (hn ▸ h.card_l_lt) _ _ rfl (h.pcOK_l hP)
        ((card_le_card (pdarts_subset _ _)).trans hs) htl)
    exfalso
    rw [mem_pdarts, mem_sdiff, mem_pdarts] at hd
    obtain ⟨⟨hdP, hdn⟩, hdi⟩ := hd
    push Not at hdn
    exact hdi ((coarse_childHoles _ _).inner (hdn hdP))
  have hB3 : ∀ y ∈ P, M.tail y ∉ hunion Hs := fun y hy hyH => hY ⟨y, mem_filter.2 ⟨hy, hyH⟩⟩
  -- no dart touches a hole: the first hole
  have hnt : nTouch M P Hs = 0 := nTouch_eq_zero hB3
  have hBne : (smB M S T P Hs).Nonempty := ⟨d₀', mem_filter.2 ⟨hd₀', hbad'⟩⟩
  have hd₀ : pk (smB M S T P Hs) ∈ pdarts M P Hs := (mem_filter.1 (hpk _ hBne)).1
  have hbad : M.tail (pk (smB M S T P Hs)) ∉ S ∪ T ∪ hunion Hs := (mem_filter.1 (hpk _ hBne)).2
  have hwH : M.head (pk (smB M S T P Hs)) ∉ hunion Hs := by
    rw [← CombMap.tail_rev]; exact hB3 _ (hP.rev _ (mem_pdarts.1 hd₀).1)
  by_cases hw : M.head (pk (smB M S T P Hs)) ∈ S ∪ T
  · have hdegw : ∀ d ∈ P, M.tail d = M.head (pk (smB M S T P Hs)) →
        d = M.rev (pk (smB M S T P Hs)) := fun d _ e =>
      hdeg _ hw d _ e (by rw [CombMap.tail_rev])
    have h := splitOK_pendant (κ := κ) (η := η) hP hd₀ hbad hw hwH hdegw hcard
    rw [smD_pend hL hX hY h.card_l_lt hw]
    have htl := nTouch_childHoles_le (M := M) (sdiff_subset (s := P)
      (t := {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))})) Hs
      (SPath.point (M' := M) (pk (smB M S T P Hs))
        (M.tail (pk (smB M S T P Hs)))).toSep.path.mverts
    exact decOK_node_leaf h hP hs ht (Or.inl card_le_two)
      (ih _ (hn ▸ h.card_l_lt) _ _ rfl (h.pcOK_l hP) ((card_le_card sdiff_subset).trans hs)
        (by omega))
  · have hwbad : M.head (pk (smB M S T P Hs)) ∉ S ∪ T ∪ hunion Hs := by
      rw [mem_union, not_or]; exact ⟨hw, hwH⟩
    have h := splitOK_edge (κ := κ) (η := η) hκ hP hd₀ hbad hwbad hcard (hloop _)
    rw [smD_edge hL hX hY h.card_l_lt hw (hloop _)]
    have htl := nTouch_childHoles_le (M := M) (sdiff_subset (s := P)
      (t := {pk (smB M S T P Hs), M.rev (pk (smB M S T P Hs))})) Hs
      (SPath.ofDart _ (hloop (pk (smB M S T P Hs)))).toSep.path.mverts
    exact decOK_node_leaf h hP hs ht (Or.inl card_le_two)
      (ih _ (hn ▸ h.card_l_lt) _ _ rfl (h.pcOK_l hP) ((card_le_card sdiff_subset).trans hs)
        (by omega))

end BKMNW

end PlanarFlow
