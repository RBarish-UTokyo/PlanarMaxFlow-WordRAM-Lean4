module

public import PlanarFlow.BKMNW.MsTourE

/-!
# The cut map of the path on the indices: the numbering of its darts (pure part)

The MSSP of a call runs Klein's algorithm on the cut `cutMap` of the dual graph along the path
(`PlanarFlow.BKMNW.cutOf`, `fixCut`), whose darts `CutD M L` are the darts of `M` off `L = P.darts`
(the copies) and four darts for every dart `t` leaving the path (`CutT`: the pendant dart, its
reverse, the dart of the ring, its reverse). A machine numbers them by **ranks**: for a dart order
`en` of `M` (`EnumOK M en m`),

* `cE L en i` (the darts off `L` among the first `i`), `cT M L en i` (the darts leaving the path
  among the first `i`), `nEc = cE m`, `nTc = cT m`;
* **`cutIx`**: the copy of `e` gets `cE (ix e)`; the four darts of `t` get
  `nE + q nT + cT (ix t)` (`q = 0, 1, 2, 3`): injective (`cutIx_inj`), below `nE + 4 nT`
  (`cutIx_lt`), and `#CutD = nE + 4 nT` (`card_cutD`), so the numbering is onto;
* **`cutEn`** (its inverse, an order of the darts of the cut) with **`enumOK_cut`** and
  **`enumOK_cutDD`**: the hypotheses of the map encoder `StEnc.smP_kin` for the map
  `(cutMap hL).dual` (whose dual is the cut map, `dual_dual'`);
* the reverse and the next dart of the cut on the numbers (`cutIx_rev_*`, `cutIx_next_*`), the
  words a machine writes from the index arrays of `M`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function CombMap NsStep

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-! ### Counting below an index -/

section Count

variable (p : ℕ → Prop) [DecidablePred p]

lemma cnt_succ (i : ℕ) :
    ((range (i + 1)).filter p).card = ((range i).filter p).card + if p i then 1 else 0 := by
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

lemma cnt_mono {i j : ℕ} (hij : i ≤ j) :
    ((range i).filter p).card ≤ ((range j).filter p).card :=
  card_le_card (filter_subset_filter _ (range_subset_range.2 hij))

lemma cnt_lt {i j : ℕ} (hij : i < j) (hi : p i) :
    ((range i).filter p).card < ((range j).filter p).card := by
  have h1 := cnt_succ p i
  simp only [hi, ↓reduceIte] at h1
  have h2 := cnt_mono p (show i + 1 ≤ j by omega)
  omega

lemma cnt_le_self (i : ℕ) : ((range i).filter p).card ≤ i :=
  (card_filter_le _ _).trans (by simp)

lemma cnt_inj {i j : ℕ} (hi : p i) (hj : p j)
    (h : ((range i).filter p).card = ((range j).filter p).card) : i = j := by
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have := cnt_lt p hij hi; omega
  · exact hij
  · have := cnt_lt p hij hj; omega

end Count

/-! ### The numbering of the darts of the cut -/

section Num

variable (M) (L : List D) (en : ℕ → D) (m : ℕ)

/-- The darts off `L` among the first `i`. -/
noncomputable def cE (i : ℕ) : ℕ := ((range i).filter fun j => en j ∉ L).card

/-- The darts leaving the path among the first `i`. -/
noncomputable def cT (i : ℕ) : ℕ := ((range i).filter fun j => M.tail (en j) ∈ cutS M L).card

/-- The number of copies. -/
noncomputable def nEc : ℕ := cE L en m

/-- The number of roots. -/
noncomputable def nTc : ℕ := cT M L en m

/-- **The number of a dart of the cut.** -/
noncomputable def cutIx : CutD M L → ℕ
  | .inl e => cE L en (ixOf en m e.1)
  | .inr (.inl t) => nEc L en m + cT M L en (ixOf en m t.1)
  | .inr (.inr (.inl t)) => nEc L en m + nTc M L en m + cT M L en (ixOf en m t.1)
  | .inr (.inr (.inr (.inl t))) => nEc L en m + 2 * nTc M L en m + cT M L en (ixOf en m t.1)
  | .inr (.inr (.inr (.inr t))) => nEc L en m + 3 * nTc M L en m + cT M L en (ixOf en m t.1)

variable {M L en m}

lemma cE_lt (h : EnumOK M en m) {e : D} (he : e ∉ L) : cE L en (ixOf en m e) < nEc L en m :=
  cnt_lt _ (ixOf_lt h e) (by rw [en_ixOf h]; exact he)

lemma cT_lt (h : EnumOK M en m) {t : D} (ht : M.tail t ∈ cutS M L) :
    cT M L en (ixOf en m t) < nTc M L en m :=
  cnt_lt _ (ixOf_lt h t) (by rw [en_ixOf h]; exact ht)

lemma cutIx_lt (h : EnumOK M en m) (d : CutD M L) :
    cutIx M L en m d < nEc L en m + 4 * nTc M L en m := by
  rcases d with ⟨e, he⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ <;> simp only [cutIx]
  · have := cE_lt h he; omega
  all_goals have := cT_lt h ht; omega

lemma cE_inj (h : EnumOK M en m) {e e' : D} (he : e ∉ L) (he' : e' ∉ L)
    (hh : cE L en (ixOf en m e) = cE L en (ixOf en m e')) : e = e' := by
  have := cnt_inj (fun j => en j ∉ L) (by show en (ixOf en m e) ∉ L; rw [en_ixOf h]; exact he)
    (by show en (ixOf en m e') ∉ L; rw [en_ixOf h]; exact he') hh
  rw [← en_ixOf h e, this, en_ixOf h]

lemma cT_inj (h : EnumOK M en m) {t t' : D} (ht : M.tail t ∈ cutS M L)
    (ht' : M.tail t' ∈ cutS M L)
    (hh : cT M L en (ixOf en m t) = cT M L en (ixOf en m t')) : t = t' := by
  have := cnt_inj (fun j => M.tail (en j) ∈ cutS M L)
    (by show M.tail (en (ixOf en m t)) ∈ cutS M L; rw [en_ixOf h]; exact ht)
    (by show M.tail (en (ixOf en m t')) ∈ cutS M L; rw [en_ixOf h]; exact ht') hh
  rw [← en_ixOf h t, this, en_ixOf h]

/-- **The numbering is injective.** -/
theorem cutIx_inj (h : EnumOK M en m) : Injective (cutIx M L en m) := by
  intro a b hab
  rcases a with ⟨e, he⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ | ⟨t, ht⟩ <;>
    rcases b with ⟨e', he'⟩ | ⟨t', ht'⟩ | ⟨t', ht'⟩ | ⟨t', ht'⟩ | ⟨t', ht'⟩ <;>
    simp only [cutIx] at hab
  all_goals first
    | (have := cE_inj h he he' hab; subst this; rfl)
    | (have := cT_inj h ht ht' (by omega); subst this; rfl)
    | (exfalso; have := cE_lt h he; have := cT_lt h ht'; omega)
    | (exfalso; have := cE_lt h he'; have := cT_lt h ht; omega)
    | (exfalso; have := cT_lt h ht; have := cT_lt h ht'; omega)

/-- The darts with a property, counted on the indices. -/
lemma card_filter_en (h : EnumOK M en m) (q : D → Prop) [DecidablePred q] :
    (univ.filter q).card = ((range m).filter fun j => q (en j)).card := by
  have hinj : Set.InjOn en ((range m).filter fun j => q (en j)) := fun i hi j hj e =>
    h.inj i (mem_range.1 (mem_filter.1 hi).1) j (mem_range.1 (mem_filter.1 hj).1) e
  rw [← card_image_of_injOn hinj]
  congr 1
  ext d
  simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
  constructor
  · intro hd
    obtain ⟨i, hi, rfl⟩ := h.surj d
    exact ⟨i, ⟨hi, hd⟩, rfl⟩
  · rintro ⟨i, ⟨-, hi⟩, rfl⟩
    exact hi

/-- **The number of darts of the cut.** -/
theorem card_cutD (h : EnumOK M en m) :
    Fintype.card (CutD M L) = nEc L en m + 4 * nTc M L en m := by
  simp only [Fintype.card_sum, Fintype.card_subtype]
  rw [card_filter_en h, card_filter_en h]
  unfold nEc nTc cE cT
  ring

lemma cutIx_surj (h : EnumOK M en m) {j : ℕ} (hj : j < nEc L en m + 4 * nTc M L en m) :
    ∃ d, cutIx M L en m d = j := by
  classical
  have hsub : univ.image (cutIx M L en m) ⊆ range (nEc L en m + 4 * nTc M L en m) :=
    fun x hx => by
      obtain ⟨d, -, rfl⟩ := mem_image.1 hx
      exact mem_range.2 (cutIx_lt h d)
  have hcard : (range (nEc L en m + 4 * nTc M L en m)).card ≤ (univ.image (cutIx M L en m)).card
      := by
    rw [card_image_of_injective _ (cutIx_inj h), card_univ, card_cutD h, card_range]
  have he := eq_of_subset_of_card_le hsub hcard
  have : j ∈ univ.image (cutIx M L en m) := by rw [he]; exact mem_range.2 hj
  obtain ⟨d, -, hd⟩ := mem_image.1 this
  exact ⟨d, hd⟩

variable (M L en m) in
/-- **The order of the darts of the cut**: the inverse of the numbering (`d₀` past the end). -/
noncomputable def cutEn (d₀ : CutD M L) (j : ℕ) : CutD M L := by
  classical
  exact if h : ∃ d, cutIx M L en m d = j then h.choose else d₀

lemma cutEn_cutIx (h : EnumOK M en m) (d₀ d : CutD M L) :
    cutEn M L en m d₀ (cutIx M L en m d) = d := by
  classical
  unfold cutEn
  have hex : ∃ d', cutIx M L en m d' = cutIx M L en m d := ⟨d, rfl⟩
  split_ifs
  exact cutIx_inj h (Exists.choose_spec hex)

lemma cutIx_cutEn (h : EnumOK M en m) (d₀ : CutD M L) {j : ℕ}
    (hj : j < nEc L en m + 4 * nTc M L en m) : cutIx M L en m (cutEn M L en m d₀ j) = j := by
  obtain ⟨d, rfl⟩ := cutIx_surj h hj
  rw [cutEn_cutIx h]

end Num

/-! ### The cut map and its dual -/

section Maps

variable {L : List D} (hL : ∀ e ∈ L, M.rev e ∈ L)

lemma combMap_ext {A B : CombMap D V F} (h1 : A.rev = B.rev) (h2 : A.tail = B.tail)
    (h3 : A.face = B.face) (h4 : A.next = B.next) : A = B := by
  cases A; cases B; simp only at h1 h2 h3 h4; subst h1 h2 h3 h4; rfl

/-- **The dual of the dual is the map.** -/
theorem dual_dual' {D' V' F' : Type*} (N : CombMap D' V' F') : N.dual.dual = N := by
  cases N with
  | mk rev rev_rev rev_ne tail face next next_injective face_next tail_next =>
    have : (fun d => next (rev (rev d))) = next := funext fun d => by rw [rev_rev]
    simp only [CombMap.dual]
    congr

variable {en : ℕ → D} {m : ℕ}

/-- **The order of the cut meets the hypotheses of the map encoder** for `(cutMap hL).dual`. -/
theorem enumOK_cut (h : EnumOK M en m) (d₀ : CutD M L) :
    EnumOK (cutMap hL).dual (cutEn M L en m d₀) (nEc L en m + 4 * nTc M L en m) where
  inj i hi j hj e := by rw [← cutIx_cutEn h d₀ hi, ← cutIx_cutEn h d₀ hj, e]
  surj d := ⟨_, cutIx_lt h d, cutEn_cutIx h d₀ d⟩
  fsurj v := by
    rcases v with x | t
    · obtain ⟨d, hd⟩ := h.fsurj x
      by_cases hdL : d ∈ L
      · exact ⟨.inr (.inr (.inl ⟨d, tail_mem_cutS hdL⟩)), by
          simp [CombMap.dual, cutMap, cutTail, hd]⟩
      · exact ⟨.inl ⟨d, hdL⟩, by simp [CombMap.dual, cutMap, cutTail, hd]⟩
    · exact ⟨.inr (.inl t), rfl⟩
  ft := cutMap_rotTrans hL h.ft

include hL in
/-- The index of a dart of the cut in its order is its number. -/
lemma ixOf_cutEn (h : EnumOK M en m) (d₀ d : CutD M L) :
    ixOf (cutEn M L en m d₀) (nEc L en m + 4 * nTc M L en m) d = cutIx M L en m d := by
  have h' := enumOK_cut hL h d₀
  have e := en_ixOf h' d
  have hl := ixOf_lt h' d
  rw [← cutIx_cutEn h d₀ hl, e]

/-- **The order of the cut meets the hypotheses of the map encoder** for the dual of
`(cutMap hL).dual` (the faces of the cut transitive, every vertex of `M` with a dart, a root). -/
theorem enumOK_cutDD (h : EnumOK M en m) (d₀ : CutD M L) (t₀ : CutT M L)
    (hV : ∀ v, ∃ d, M.tail d = v) (hft : (cutMap hL).FaceTrans) :
    EnumOK (cutMap hL).dual.dual (cutEn M L en m d₀) (nEc L en m + 4 * nTc M L en m) where
  inj i hi j hj e := by rw [← cutIx_cutEn h d₀ hi, ← cutIx_cutEn h d₀ hj, e]
  surj d := ⟨_, cutIx_lt h d, cutEn_cutIx h d₀ d⟩
  fsurj y := by
    rw [dual_dual']
    rcases y with ⟨v, hv⟩ | t | u
    · obtain ⟨d, hd⟩ := hV v
      have hdL : d ∉ L := not_mem_of_tail hL (by rw [hd]; exact hv)
      refine ⟨.inl ⟨d, hdL⟩, ?_⟩
      have : M.tail d ∉ cutS M L := by rw [hd]; exact hv
      simp [cutMap, cutFace, hd, hv]
    · exact ⟨.inr (.inl t), rfl⟩
    · exact ⟨.inr (.inr (.inr (.inl t₀))), rfl⟩
  ft := by rw [dual_dual']; exact hft

end Maps

/-! ### The reverse and the next dart on the numbers -/

section Words

variable {L : List D} (hL : ∀ e ∈ L, M.rev e ∈ L) {en : ℕ → D} {m : ℕ}

lemma cutIx_rev_E (h : EnumOK M en m) (e : {e : D // e ∉ L}) :
    cutIx M L en m (cutRev hL (.inl e)) = cE L en (ixOf en m (M.rev e.1)) := rfl

lemma cutIx_next_E (h : EnumOK M en m) (e : {e : D // e ∉ L}) :
    cutIx M L en m (cutNext hL (.inl e)) =
      if M.tail e.1 ∈ cutS M L then
        nEc L en m + nTc M L en m + cT M L en (ixOf en m (tour M L e.1))
      else cE L en (ixOf en m (M.rot e.1)) := by
  by_cases ht : M.tail e.1 ∈ cutS M L
  · simp only [cutNext, ht, ↓reduceDIte, ↓reduceIte, cutIx, tourT_val]
  · simp only [cutNext, ht, ↓reduceDIte, ↓reduceIte, cutIx]

lemma cutIx_rev_1 (t : CutT M L) :
    cutIx M L en m (cutRev hL (.inr (.inl t))) =
      nEc L en m + nTc M L en m + cT M L en (ixOf en m t.1) := rfl

lemma cutIx_next_1 (t : CutT M L) :
    cutIx M L en m (cutNext hL (.inr (.inl t))) =
      if t.1 ∈ L then nEc L en m + nTc M L en m + cT M L en (ixOf en m (tour M L t.1))
      else cE L en (ixOf en m t.1) := by
  by_cases ht : t.1 ∈ L
  · simp only [cutNext, ht, ↓reduceDIte, ↓reduceIte, cutIx, tourT_val]
  · simp only [cutNext, ht, ↓reduceDIte, ↓reduceIte, cutIx]

lemma cutIx_rev_2 (t : CutT M L) :
    cutIx M L en m (cutRev hL (.inr (.inr (.inl t)))) = nEc L en m + cT M L en (ixOf en m t.1) :=
  rfl

lemma cutIx_next_2 (t : CutT M L) :
    cutIx M L en m (cutNext hL (.inr (.inr (.inl t)))) =
      nEc L en m + 3 * nTc M L en m + cT M L en (ixOf en m ((tourT hL).symm t).1) := rfl

lemma cutIx_rev_3 (t : CutT M L) :
    cutIx M L en m (cutRev hL (.inr (.inr (.inr (.inl t))))) =
      nEc L en m + 3 * nTc M L en m + cT M L en (ixOf en m t.1) := rfl

lemma cutIx_next_3 (t : CutT M L) :
    cutIx M L en m (cutNext hL (.inr (.inr (.inr (.inl t))))) =
      nEc L en m + 2 * nTc M L en m + cT M L en (ixOf en m (tour M L t.1)) := rfl

lemma cutIx_rev_4 (t : CutT M L) :
    cutIx M L en m (cutRev hL (.inr (.inr (.inr (.inr t))))) =
      nEc L en m + 2 * nTc M L en m + cT M L en (ixOf en m t.1) := rfl

lemma cutIx_next_4 (t : CutT M L) :
    cutIx M L en m (cutNext hL (.inr (.inr (.inr (.inr t))))) =
      nEc L en m + cT M L en (ixOf en m t.1) := rfl

/-- The walk around `L` undoes its inverse on the roots. -/
lemma tour_symm (t : CutT M L) : tour M L ((tourT hL).symm t).1 = t.1 := by
  have := congrArg Subtype.val ((tourT hL).apply_symm_apply t)
  rw [tourT_val] at this
  exact this

end Words

end MsEnc

end BKMNW

end PlanarFlow
