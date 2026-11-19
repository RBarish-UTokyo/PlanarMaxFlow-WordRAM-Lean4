module

public import PlanarFlow.BKMNW.S7Cl2
public import PlanarFlow.BKMNW.OrdScan

/-!
# Stage 7 of `sepL` (III), pure part: the order of the classes, their weights, the left piece

From class numbers `cid` on an enumeration `g` of a piece `P` (`cid i = cid j ↔ g j ∈ X (g i)`,
`IsCls P X`) and, for every dart, the **last** index `lst i` of its class (a scatter on the
machine), the machine computes the position of each class (`odPos`, a prefix count of the flags
`lst i = i`); this file proves what these numbers mean:

* `OdIn` (the hypotheses), `lst_lst`, `lst_eq_iff`, **`odPos_eq_iff`**, `odPos_lt`;
* `odL q` (the darts at position `q`), **`odL_pos`** (`odL (odPos i) = X (g i)`),
  `mem_odL_iff`, `odL_surj`;
* **`odL_ordE`**: `(List.range (odM n)).map odL = ordE eG N (P.image X)` for a `gid`-increasing
  `g` and the global enumeration `eG` (`gid (eG i) = i`): the classes listed by the machine are
  `pc.ord` of `pcChoiceE`;
* **`odL_card`** (`#(odL q)` is the count of the positions), **`odL_tH_card`** (the holes off `C`
  touched by `odL q`, counted by hole index through the owner of each hole, given that distinct
  classes touch disjoint sets of holes — `exists_cls'` for `K ≠ 0`);
* **`odL_left`**: a dart is in the union of the classes of a list of positions iff its position
  is in the list; **`odL_right`** (the rest).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset

section Od

variable {D : Type*} [DecidableEq D]

/-- **The hypotheses of the order of the classes.** -/
structure OdIn (P : Finset D) (X : D → Finset D) (g : ℕ → D) (n : ℕ) (cid lst : ℕ → ℕ) : Prop
    where
  cls : IsCls P X
  mem : ∀ i < n, g i ∈ P
  surj : ∀ d ∈ P, ∃ i < n, g i = d
  inj : ∀ i < n, ∀ j < n, g i = g j → i = j
  hid : ∀ i < n, ∀ j < n, (cid i = cid j ↔ g j ∈ X (g i))
  lst_lt : ∀ i < n, lst i < n
  lst_id : ∀ i < n, cid (lst i) = cid i
  lst_max : ∀ i < n, ∀ j < n, cid j = cid i → j ≤ lst i

/-- The flag of the last dart of a class. -/
def odR (lst : ℕ → ℕ) (i : ℕ) : ℕ := if lst i = i then 1 else 0

/-- The position of the class of a dart. -/
def odPos (lst : ℕ → ℕ) (i : ℕ) : ℕ := cnt (odR lst) (lst i)

/-- The number of classes. -/
def odM (lst : ℕ → ℕ) (n : ℕ) : ℕ := cnt (odR lst) n

/-- The darts at position `q`. -/
def odL (g : ℕ → D) (n : ℕ) (lst : ℕ → ℕ) (q : ℕ) : Finset D :=
  ((range n).filter fun i => odPos lst i = q).image g

variable {P : Finset D} {X : D → Finset D} {g : ℕ → D} {n : ℕ} {cid lst : ℕ → ℕ}

lemma OdIn.lst_lst (h : OdIn P X g n cid lst) {i : ℕ} (hi : i < n) : lst (lst i) = lst i := by
  have h1 := h.lst_lt i hi
  have a := h.lst_max _ h1 _ h1 rfl
  have b := h.lst_max i hi _ (h.lst_lt _ h1) (by rw [h.lst_id _ h1, h.lst_id i hi])
  omega

lemma OdIn.lst_eq_iff (h : OdIn P X g n cid lst) {i j : ℕ} (hi : i < n) (hj : j < n) :
    lst i = lst j ↔ cid i = cid j := by
  constructor
  · intro e; rw [← h.lst_id i hi, ← h.lst_id j hj, e]
  · intro e
    have a := h.lst_max i hi _ (h.lst_lt j hj) (by rw [h.lst_id j hj, e])
    have b := h.lst_max j hj _ (h.lst_lt i hi) (by rw [h.lst_id i hi, e])
    omega

lemma OdIn.odR_lst (h : OdIn P X g n cid lst) {i : ℕ} (hi : i < n) : 0 < odR lst (lst i) := by
  unfold odR; rw [h.lst_lst hi]; simp

lemma OdIn.odPos_eq_iff (h : OdIn P X g n cid lst) {i j : ℕ} (hi : i < n) (hj : j < n) :
    odPos lst i = odPos lst j ↔ cid i = cid j := by
  rw [← h.lst_eq_iff hi hj]
  constructor
  · intro e; exact cnt_inj _ (h.odR_lst hi) (h.odR_lst hj) e
  · intro e; unfold odPos; rw [e]

lemma OdIn.odPos_lt (h : OdIn P X g n cid lst) {i : ℕ} (hi : i < n) : odPos lst i < odM lst n :=
  cnt_lt_of _ (h.lst_lt i hi) (h.odR_lst hi)

lemma OdIn.mem_odL_iff (h : OdIn P X g n cid lst) {i : ℕ} (hi : i < n) (q : ℕ) :
    g i ∈ odL g n lst q ↔ odPos lst i = q := by
  unfold odL
  simp only [mem_image, mem_filter, mem_range]
  constructor
  · rintro ⟨j, ⟨hj, e⟩, hg⟩; rw [← h.inj j hj i hi hg]; exact e
  · intro e; exact ⟨i, ⟨hi, e⟩, rfl⟩

lemma OdIn.odL_sub (h : OdIn P X g n cid lst) (q : ℕ) : odL g n lst q ⊆ P := by
  intro d hd
  unfold odL at hd
  simp only [mem_image, mem_filter, mem_range] at hd
  obtain ⟨j, ⟨hj, -⟩, rfl⟩ := hd
  exact h.mem j hj

/-- **The darts at the position of a dart form its class.** -/
theorem OdIn.odL_pos (h : OdIn P X g n cid lst) {i : ℕ} (hi : i < n) :
    odL g n lst (odPos lst i) = X (g i) := by
  ext d
  constructor
  · intro hd
    obtain ⟨j, hj, rfl⟩ := h.surj d (h.odL_sub _ hd)
    rw [h.mem_odL_iff hj, h.odPos_eq_iff hj hi] at hd
    exact (h.hid i hi j hj).1 hd.symm
  · intro hd
    obtain ⟨j, hj, rfl⟩ := h.surj d (h.cls.sub _ (h.mem i hi) hd)
    rw [h.mem_odL_iff hj, h.odPos_eq_iff hj hi]
    exact ((h.hid i hi j hj).2 hd).symm

lemma OdIn.odL_surj (h : OdIn P X g n cid lst) {q : ℕ} (hq : q < odM lst n) :
    ∃ i < n, odPos lst i = q ∧ lst i = i := by
  obtain ⟨i, hi, h1, h2⟩ := cnt_surj _ n q hq
  have e : lst i = i := by unfold odR at h1; split_ifs at h1 with e <;> simp_all
  exact ⟨i, hi, by unfold odPos; rw [e, h2], e⟩

lemma OdIn.odL_nonempty (h : OdIn P X g n cid lst) {q : ℕ} (hq : q < odM lst n) :
    (odL g n lst q).Nonempty := by
  obtain ⟨i, hi, e, -⟩ := h.odL_surj hq
  exact ⟨g i, (h.mem_odL_iff hi q).2 e⟩

/-- The classes listed by position are the classes of the piece. -/
lemma OdIn.odL_image (h : OdIn P X g n cid lst) :
    ((List.range (odM lst n)).map (odL g n lst)).toFinset = P.image X := by
  ext E
  simp only [List.mem_toFinset, List.mem_map, List.mem_range, mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨i, hi, e, -⟩ := h.odL_surj hq
    exact ⟨g i, h.mem i hi, by rw [← h.odL_pos hi, e]⟩
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨i, hi, rfl⟩ := h.surj d hd
    exact ⟨odPos lst i, h.odPos_lt hi, h.odL_pos hi⟩

/-- **The machine's list of the classes is `ordE`** of the global enumeration. -/
theorem OdIn.odL_ordE (h : OdIn P X g n cid lst) {gid : D → ℕ}
    (hmono : ∀ i j, i < j → j < n → gid (g i) < gid (g j)) {eG : ℕ → D} {N : ℕ}
    (he : ∀ i < N, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N, eG i = d) :
    ordE eG N (P.image X) = (List.range (odM lst n)).map (odL g n lst) := by
  -- the global index of a dart is its `gid`
  have hidx : ∀ E : Finset D, idxE eG N E = E.image gid := by
    intro E
    ext i
    simp only [idxE, mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hi, hE⟩; exact ⟨eG i, hE, he i hi⟩
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨j, hj, rfl⟩ := hesurj d
      rw [he j hj]; exact ⟨hj, hd⟩
  -- the largest global index of the class at position `q` is that of its last dart
  have hrep : ∀ q < odM lst n, ∃ r < n, odPos lst r = q ∧ lst r = r ∧
      ∀ j < n, odPos lst j = q → gid (g j) ≤ gid (g r) := by
    intro q hq
    obtain ⟨r, hr, e, hl⟩ := h.odL_surj hq
    refine ⟨r, hr, e, hl, fun j hj ej => ?_⟩
    have := h.lst_max r hr j hj ((h.odPos_eq_iff hj hr).1 (by rw [ej, e]))
    rw [hl] at this
    rcases Nat.lt_or_eq_of_le this with hlt | rfl
    · exact (hmono j r hlt hr).le
    · exact le_rfl
  classical
  let mx : Finset D → ℕ := fun E => (E.image gid).sup _root_.id
  refine ordE_eq_of_max hesurj mx (fun E hE => ?_) h.odL_image ?_
  · simp only [List.mem_map, List.mem_range] at hE
    obtain ⟨q, hq, rfl⟩ := hE
    obtain ⟨r, hr, e, -, hmax⟩ := hrep q hq
    have hrL : g r ∈ odL g n lst q := (h.mem_odL_iff hr q).2 e
    have hmx : mx (odL g n lst q) = gid (g r) := by
      apply le_antisymm
      · refine Finset.sup_le fun x hx => ?_
        obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
        obtain ⟨j, hj, rfl⟩ := h.surj d (h.odL_sub q hd)
        exact hmax j hj ((h.mem_odL_iff hj q).1 hd)
      · exact Finset.le_sup (f := _root_.id) (mem_image_of_mem gid hrL)
    rw [hidx, hmx]
    refine ⟨mem_image_of_mem gid hrL, fun x hx => ?_⟩
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
    obtain ⟨j, hj, rfl⟩ := h.surj d (h.odL_sub q hd)
    exact hmax j hj ((h.mem_odL_iff hj q).1 hd)
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {q q'} hq hq' hlt => ?_
    rw [List.mem_range] at hq hq'
    obtain ⟨r, hr, e, hl, hmax⟩ := hrep q hq
    obtain ⟨r', hr', e', hl', hmax'⟩ := hrep q' hq'
    have h1 : mx (odL g n lst q) = gid (g r) := by
      apply le_antisymm
      · refine Finset.sup_le fun x hx => ?_
        obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
        obtain ⟨j, hj, rfl⟩ := h.surj d (h.odL_sub q hd)
        exact hmax j hj ((h.mem_odL_iff hj q).1 hd)
      · exact Finset.le_sup (f := _root_.id) (mem_image_of_mem gid ((h.mem_odL_iff hr q).2 e))
    have h2 : mx (odL g n lst q') = gid (g r') := by
      apply le_antisymm
      · refine Finset.sup_le fun x hx => ?_
        obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
        obtain ⟨j, hj, rfl⟩ := h.surj d (h.odL_sub q' hd)
        exact hmax' j hj ((h.mem_odL_iff hj q').1 hd)
      · exact Finset.le_sup (f := _root_.id) (mem_image_of_mem gid ((h.mem_odL_iff hr' q').2 e'))
    rw [h1, h2]
    -- the last darts are ordered as their positions
    have hrr : r < r' := by
      by_contra hc
      have hle : r' ≤ r := by omega
      have := cnt_mono (odR lst) hle
      have e1 : odPos lst r = cnt (odR lst) r := by unfold odPos; rw [hl]
      have e2 : odPos lst r' = cnt (odR lst) r' := by unfold odPos; rw [hl']
      omega
    exact hmono r r' hrr hr'

/-- `saF` of the constant `1` counts. -/
lemma saF_one (key : ℕ → ℕ) (m k : ℕ) :
    saF key (fun _ => 1) m k = ((range m).filter fun j => key j = k).card := by
  unfold saF; simp

/-- **The size of the class at position `q`.** -/
theorem OdIn.odL_card (h : OdIn P X g n cid lst) (q : ℕ) :
    (odL g n lst q).card = ((range n).filter fun i => odPos lst i = q).card := by
  unfold odL
  refine card_image_of_injOn fun i hi j hj e => ?_
  simp only [coe_filter, Set.mem_ofPred_eq, mem_range] at hi hj
  exact h.inj i hi.1 j hj.1 e

/-- **A dart is in the union of the classes at a list of positions iff its position is in the
list.** -/
theorem OdIn.odL_left (h : OdIn P X g n cid lst) (L : List ℕ) {i : ℕ} (hi : i < n) :
    g i ∈ (L.map (odL g n lst)).toFinset.biUnion _root_.id ↔ odPos lst i ∈ L := by
  simp only [mem_biUnion, List.mem_toFinset, List.mem_map, _root_.id]
  constructor
  · rintro ⟨E, ⟨q, hq, rfl⟩, hm⟩
    rw [h.mem_odL_iff hi] at hm
    rw [hm]; exact hq
  · intro hm
    exact ⟨_, ⟨_, hm, rfl⟩, (h.mem_odL_iff hi _).2 rfl⟩

/-- **The rest of the piece.** -/
theorem OdIn.odL_right (h : OdIn P X g n cid lst) (L : List ℕ) {i : ℕ} (hi : i < n) :
    g i ∈ (P.image X \ (L.map (odL g n lst)).toFinset).biUnion _root_.id ↔
      odPos lst i ∉ L := by
  simp only [mem_biUnion, mem_sdiff, mem_image, List.mem_toFinset, List.mem_map, _root_.id]
  constructor
  · rintro ⟨E, ⟨⟨d, hd, rfl⟩, hnot⟩, hm⟩ hL
    obtain ⟨j, hj, rfl⟩ := h.surj d hd
    rw [← h.odL_pos hj, h.mem_odL_iff hi] at hm
    exact hnot ⟨_, hL, by rw [hm, h.odL_pos hj]⟩
  · intro hL
    refine ⟨X (g i), ⟨⟨g i, h.mem i hi, rfl⟩, ?_⟩, h.cls.self _ (h.mem i hi)⟩
    rintro ⟨q, hq, e⟩
    have : g i ∈ odL g n lst q := by rw [e]; exact h.cls.self _ (h.mem i hi)
    rw [h.mem_odL_iff hi] at this
    exact hL (this ▸ hq)

end Od

section TH

open MfDrv

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}
variable {P : Finset D} {X : D → Finset D} {g : ℕ → D} {n : ℕ} {cid lst : ℕ → ℕ}

/-- **The holes off `C` touched by the class at position `q`**, counted by hole index: the hole
`Hs[j]` is off `C` (`ht (j + 1) = 0`) and its owner (the position of some dart with its tail in
it, `own (j + 1) - 1`) is `q` — given that distinct classes touch disjoint sets of holes. -/
theorem OdIn.odL_tH_card (h : OdIn P X g n cid lst) {Hs : List (Finset V)}
    (hd : Hs.Pairwise Disjoint) {C : Finset V}
    (htH : ∀ d ∈ P, ∀ d' ∈ P, X d ≠ X d' → Disjoint (tH M Hs C (X d)) (tH M Hs C (X d')))
    {hp ht own : ℕ → ℕ} (hhp : ∀ i < n, hp i = hlab Hs (M.tail (g i)))
    (hht : ∀ j < Hs.length, (ht (j + 1) = 0 ↔ Disjoint (Hs.getD j ∅) C))
    (hown : ∀ j < Hs.length, (own (j + 1) = 0 ∧ ∀ i < n, hp i ≠ j + 1) ∨
      (∃ i < n, hp i = j + 1 ∧ own (j + 1) = odPos lst i + 1)) (q : ℕ) :
    (tH M Hs C (odL g n lst q)).card =
      ((range Hs.length).filter fun j => ht (j + 1) = 0 ∧ own (j + 1) = q + 1).card := by
  symm
  refine card_bij (fun j _ => Hs.getD j ∅) (fun j hj => ?_) (fun j1 hj1 j2 hj2 e => ?_)
    (fun H hH => ?_)
  · simp only [mem_filter, mem_range] at hj
    obtain ⟨hjl, h0, ho⟩ := hj
    rcases hown j hjl with ⟨e, -⟩ | ⟨i, hi, e1, e2⟩
    · omega
    · have hpos : odPos lst i = q := by omega
      rw [mem_tH]
      refine ⟨sm_getD_mem hjl, (hht j hjl).1 h0, g i, (h.mem_odL_iff hi q).2 hpos, ?_⟩
      rw [← hlab_eq_succ_iff hd hjl, ← hhp i hi, e1]
  · simp only [mem_filter, mem_range] at hj1 hj2
    by_contra hne
    obtain ⟨hl1, -, ho1⟩ := hj1
    obtain ⟨hl2, -, -⟩ := hj2
    rcases hown j1 hl1 with ⟨e', -⟩ | ⟨i, hi, e1, -⟩
    · omega
    · have hv : M.tail (g i) ∈ Hs.getD j1 ∅ := by
        rw [← hlab_eq_succ_iff hd hl1, ← hhp i hi, e1]
      have hdis : Disjoint (Hs.getD j1 ∅) (Hs.getD j2 ∅) := by
        rw [getD_eq_get hl1, getD_eq_get hl2]
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · exact List.pairwise_iff_getElem.1 hd j1 j2 hl1 hl2 hlt
        · exact (List.pairwise_iff_getElem.1 hd j2 j1 hl2 hl1 hlt).symm
      rw [e] at hdis hv
      exact disjoint_left.1 hdis hv hv
  · rw [mem_tH] at hH
    obtain ⟨hHs, hHC, d, hdL, hdH⟩ := hH
    obtain ⟨j, hjl, rfl⟩ := List.mem_iff_getElem.1 hHs
    have eg : Hs.getD j ∅ = Hs[j] := getD_eq_get hjl
    obtain ⟨i, hi, rfl⟩ := h.surj d (h.odL_sub q hdL)
    have hpi : odPos lst i = q := (h.mem_odL_iff hi q).1 hdL
    have hhi : hp i = j + 1 := by
      rw [hhp i hi, hlab_eq_succ_iff hd hjl, eg]; exact hdH
    refine ⟨j, ?_, eg⟩
    simp only [mem_filter, mem_range]
    refine ⟨hjl, (hht j hjl).2 (by rw [eg]; exact hHC), ?_⟩
    rcases hown j hjl with ⟨-, hno⟩ | ⟨i', hi', e1, e2⟩
    · exact absurd hhi (hno i hi)
    · rw [e2, ← hpi]
      congr 1
      have hv' : M.tail (g i') ∈ Hs[j] := by
        rw [← eg, ← hlab_eq_succ_iff hd hjl, ← hhp i' hi', e1]
      by_contra hne
      have hX : X (g i) ≠ X (g i') := by
        intro hX
        apply hne
        rw [h.odPos_eq_iff hi' hi]
        exact ((h.hid i hi i' hi').2 (by rw [hX]; exact h.cls.self _ (h.mem i' hi'))).symm
      have m1 : Hs[j] ∈ tH M Hs C (X (g i)) := by
        rw [mem_tH]
        exact ⟨hHs, hHC, g i, h.cls.self _ (h.mem i hi), hdH⟩
      have m2 : Hs[j] ∈ tH M Hs C (X (g i')) := by
        rw [mem_tH]
        exact ⟨hHs, hHC, g i', h.cls.self _ (h.mem i' hi'), hv'⟩
      exact disjoint_left.1 (htH _ (h.mem i hi) _ (h.mem i' hi') hX) m1 m2

end TH

end BKMNW

end PlanarFlow
