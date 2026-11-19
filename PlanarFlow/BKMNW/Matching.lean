module

public import PlanarFlow.BKMNW.DartNet
public import PlanarFlow.BKMNW.MaxFlow
public import PlanarFlow.BKMNW.Pendant
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Maximum bipartite matching in plane graphs

A corollary of the maximum-flow algorithm of Borradaile, Klein, Mozes, Nussbaum and Wulff-Nilsen
(SIAM J. Comput. 46(4), 2017; `PlanarFlow.BKMNW.algo`, correct by
`PlanarFlow.BKMNW.maxflow_plane`): maximum matchings, and the perfect-matching test, in plane
bipartite graphs.

Let `M` be a plane map whose vertices are coloured white (`W v`) and black, every dart joining a
white and a black vertex. A *matching* is a set of darts from white to black vertices, no two
with the same tail or the same head. The network: a pendant edge is attached at every vertex
(`PlanarFlow.CombMap.pendant`, which keeps the map plane, with transitive rotations and faces);
the darts from white to black vertices have capacity `1`, their reverses `0`; the new neighbour
of a white vertex is a source, joined to it by a dart of capacity `1`, and the new neighbour of a
black vertex is a sink, joined from it by a dart of capacity `1` (`mcap`, `mS`, `mT`). The
pendant darts are the vertex capacities.

* `exists_flow_of_matching`: every matching gives a flow of value its size.
* `matchOf_spec`: every flow gives a matching (`matchOf f`, the darts from white vertices
  carrying one unit) of size its value.
* `matchOf_max`: hence the matching of a maximum flow is a maximum matching, and
  `exists_perfect_iff` the graph has a perfect matching iff that matching covers all the white
  vertices and there are as many white as black vertices.
* `PlanarFlow.CombMap.pendant_rotTrans`, `PlanarFlow.CombMap.pendant_faceTrans`: pendant edges
  keep the rotations and the faces transitive, so `maxflow_plane` applies to the network.
* `matching_plane`: **the matching computed by the algorithm (`planeMatching`) is a maximum
  matching, and decides whether a perfect matching exists**, on every plane map with transitive
  rotations and faces.
* `matching_plane_ofRotation`: the same for plane rotation systems, with perfect matchings in the
  sense of Mathlib (`SimpleGraph.Subgraph.IsPerfectMatching`, `exists_isPerfect_ofRotation_iff`).
* `edgeRot_hyps`, `ofRotation_edgeRot_hyps`: the hypotheses of both theorems hold together for a
  single edge; the darts `e` at which the pendant edges are drawn exist on every plane map with a
  dart (`PlanarFlow.CombMap.exists_tail_eq`) and on every plane rotation system
  (`exists_dart_fst`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable {M : CombMap D V F} {W : V → Prop} [DecidablePred W]

variable (M W) in
/-- A matching: darts from white vertices, no two with the same tail or the same head. -/
def IsMatching (Mt : Finset D) : Prop :=
  (∀ d ∈ Mt, W (M.tail d)) ∧ (∀ d ∈ Mt, ∀ d' ∈ Mt, M.tail d = M.tail d' → d = d') ∧
    (∀ d ∈ Mt, ∀ d' ∈ Mt, M.head d = M.head d' → d = d')

variable (M W) in
/-- A perfect matching: a matching covering every vertex. -/
def IsPerfect (Mt : Finset D) : Prop :=
  IsMatching M W Mt ∧ (∀ v, W v → ∃ d ∈ Mt, M.tail d = v) ∧ (∀ v, ¬ W v → ∃ d ∈ Mt, M.head d = v)

variable (M W) in
/-- The capacities of the matching network on the map with pendant edges. -/
def mcap : D ⊕ (V × Bool) → ℤ
  | .inl d => if W (M.tail d) then 1 else 0
  | .inr (v, true) => if W v then 0 else 1
  | .inr (v, false) => if W v then 1 else 0

variable (W) in
/-- The sources: the pendant neighbours of the white vertices. -/
def mS : Finset (V ⊕ V) := (univ.filter W).image Sum.inr

variable (W) in
/-- The sinks: the pendant neighbours of the black vertices. -/
def mT : Finset (V ⊕ V) := (univ.filter fun v => ¬ W v).image Sum.inr

variable (M W) in
/-- The matching of a flow: the darts from white vertices carrying one unit. -/
def matchOf (f : D ⊕ (V × Bool) → ℤ) : Finset D :=
  univ.filter fun d => W (M.tail d) ∧ f (.inl d) = 1

lemma mS_mT_disjoint : Disjoint (mS W) (mT W) := by
  rw [disjoint_left]
  intro x hx hx'
  obtain ⟨v, hv, rfl⟩ := mem_image.1 hx
  obtain ⟨v', hv', h⟩ := mem_image.1 hx'
  cases h
  simp only [mem_filter, mem_univ, true_and] at hv hv'
  exact hv' hv

lemma mem_mS_or_mT (v : V) : Sum.inr v ∈ mS W ∨ Sum.inr v ∈ mT W := by
  by_cases h : W v
  · left; exact mem_image.2 ⟨v, by simp [h], rfl⟩
  · right; exact mem_image.2 ⟨v, by simp [h], rfl⟩

lemma inl_not_mem_mS (v : V) : (Sum.inl v : V ⊕ V) ∉ mS W := by simp [mS]

lemma inl_not_mem_mT (v : V) : (Sum.inl v : V ⊕ V) ∉ mT W := by simp [mT]

variable {e : V → D} (he : ∀ v, M.tail (e v) = v)

lemma pdiv_inr (g : D ⊕ (V × Bool) → ℤ) (v : V) :
    (M.pendant e he).div g (.inr v) = g (.inr (v, false)) := by
  unfold CombMap.div
  rw [sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp

lemma pdiv_inl (g : D ⊕ (V × Bool) → ℤ) (v : V) :
    (M.pendant e he).div g (.inl v) = M.div (fun d => g (.inl d)) v + g (.inr (v, true)) := by
  unfold CombMap.div
  rw [sum_filter, Fintype.sum_sum_type, Fintype.sum_prod_type, sum_filter]
  simp

lemma val_mS (g : D ⊕ (V × Bool) → ℤ) :
    val (M.pendant e he) (mS W) g = ∑ w with W w, g (.inr (w, false)) := by
  unfold val mS
  rw [sum_image fun _ _ _ _ h => Sum.inr.inj h]
  exact sum_congr rfl fun w _ => pdiv_inr he g w

/-- A sum of zeros and ones counts the ones. -/
lemma sum_eq_card_of_01 {s : Finset D} {g : D → ℤ} (h : ∀ d ∈ s, g d = 0 ∨ g d = 1) :
    ∑ d ∈ s, g d = ((s.filter fun d => g d = 1).card : ℤ) := by
  rw [← sum_boole]
  refine sum_congr rfl fun d hd => ?_
  rcases h d hd with h0 | h1
  · simp [h0]
  · simp [h1]

/-! ### Matchings give flows -/

/-- **Every matching gives a flow of value its size.** -/
theorem exists_flow_of_matching (hbip : ∀ d, W (M.tail d) ↔ ¬ W (M.head d)) {Mt : Finset D}
    (hMt : IsMatching M W Mt) :
    ∃ f, IsFlow (M.pendant e he) (mcap M W) (mS W) (mT W) f ∧
      val (M.pendant e he) (mS W) f = Mt.card := by
  classical
  let ind : D → ℤ := fun d => if d ∈ Mt then 1 else 0
  let cT : V → ℤ := fun v => ∑ d with M.tail d = v, ind d
  let cH : V → ℤ := fun v => ∑ d with M.head d = v, ind d
  have hind : ∀ d, 0 ≤ ind d ∧ ind d ≤ 1 := fun d => by simp only [ind]; split_ifs <;> simp
  have hindW : ∀ d, ¬ W (M.tail d) → ind d = 0 := fun d hd => by
    simp only [ind]; split_ifs with h
    · exact absurd (hMt.1 d h) hd
    · rfl
  have hcard : ∀ (p : D → Prop) [DecidablePred p],
      (∀ d d', d ∈ Mt → d' ∈ Mt → p d → p d' → d = d') → ∑ d with p d, ind d ≤ 1 := by
    intro p _ hp
    simp only [ind]
    rw [sum_boole]
    exact_mod_cast card_le_one.2 fun a ha b hb => by
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact hp a b ha.2 hb.2 ha.1 hb.1
  have hcT : ∀ v, cT v ≤ 1 := fun v =>
    hcard _ fun d d' hd hd' h1 h2 => hMt.2.1 d hd d' hd' (h1.trans h2.symm)
  have hcH : ∀ v, cH v ≤ 1 := fun v =>
    hcard _ fun d d' hd hd' h1 h2 => hMt.2.2 d hd d' hd' (h1.trans h2.symm)
  have hcT0 : ∀ v, 0 ≤ cT v := fun v => sum_nonneg fun d _ => (hind d).1
  have hcH0 : ∀ v, 0 ≤ cH v := fun v => sum_nonneg fun d _ => (hind d).1
  have hcHW : ∀ v, W v → cH v = 0 := fun v hv => sum_eq_zero fun d hd => by
    simp only [mem_filter, mem_univ, true_and] at hd
    exact hindW d fun h => (hbip d).1 h (hd ▸ hv)
  have hcTB : ∀ v, ¬ W v → cT v = 0 := fun v hv => sum_eq_zero fun d hd => by
    simp only [mem_filter, mem_univ, true_and] at hd
    exact hindW d (hd ▸ hv)
  have hdiv : ∀ v, M.div (ofNet M ind) v = cT v - cH v := fun v => by
    rw [div_ofNet ind]; rfl
  let f : D ⊕ (V × Bool) → ℤ := Sum.elim (ofNet M ind)
    (fun p => if p.2 then cH p.1 - cT p.1 else cT p.1 - cH p.1)
  refine ⟨f, ⟨⟨fun x => ?_, fun x => ?_⟩, fun x hxS hxT => ?_⟩, ?_⟩
  · rcases x with d | ⟨v, _ | _⟩
    · exact ofNet_antisymm ind d
    · simp [f]
    · simp [f]
  · rcases x with d | ⟨v, _ | _⟩
    · simp only [f, Sum.elim_inl, ofNet, mcap]
      split_ifs with h
      · linarith [(hind d).2, (hind (M.rev d)).1]
      · rw [hindW d h]; linarith [(hind (M.rev d)).1]
    · simp only [f, Sum.elim_inr, mcap, Bool.false_eq_true, ite_false]
      split_ifs with h
      · rw [hcHW v h]; linarith [hcT v]
      · rw [hcTB v h]; linarith [hcH0 v]
    · simp only [f, Sum.elim_inr, mcap, ite_true]
      split_ifs with h
      · rw [hcHW v h]; linarith [hcT0 v]
      · rw [hcTB v h]; linarith [hcH v]
  · rcases x with v | v
    · rw [pdiv_inl he]
      show M.div (ofNet M ind) v + (cH v - cT v) = 0
      rw [hdiv]; ring
    · rcases mem_mS_or_mT (W := W) v with h | h
      · exact absurd h hxS
      · exact absurd h hxT
  · rw [val_mS he]
    have h1 : ∑ w with W w, f (.inr (w, false)) = ∑ w with W w, M.div ind w := by
      refine sum_congr rfl fun w hw => ?_
      simp only [mem_filter, mem_univ, true_and] at hw
      simp only [f, Sum.elim_inr, Bool.false_eq_true, ite_false, hcHW w hw, sub_zero]
      rfl
    rw [h1, sum_div_eq_tail]
    have h2 : ∑ d with M.tail d ∈ univ.filter W, ind d = ∑ d, ind d :=
      sum_subset (subset_univ _) fun d _ hd => hindW d (by simpa using hd)
    rw [h2]
    simp only [ind]
    rw [sum_boole]
    congr 2
    ext d; simp

/-! ### Flows give matchings -/

/-- **Every flow gives a matching of size its value.** -/
theorem matchOf_spec (hbip : ∀ d, W (M.tail d) ↔ ¬ W (M.head d)) {f : D ⊕ (V × Bool) → ℤ}
    (hf : IsFlow (M.pendant e he) (mcap M W) (mS W) (mT W) f) :
    IsMatching M W (matchOf M W f) ∧
      val (M.pendant e he) (mS W) f = (matchOf M W f).card := by
  classical
  have hanti : ∀ x, f ((M.pendant e he).rev x) = - f x := hf.antisymm
  have hw01 : ∀ d, W (M.tail d) → 0 ≤ f (.inl d) ∧ f (.inl d) ≤ 1 := by
    intro d hd
    have h1 := hf.le_cap (.inl d)
    have h2 := hf.le_cap (.inl (M.rev d))
    have h3 := hanti (.inl d)
    have hb : ¬ W (M.tail (M.rev d)) := (hbip d).1 hd
    simp only [mcap, hd, hb, ite_true, ite_false] at h1 h2
    simp only [pendant_rev_inl] at h3
    constructor <;> linarith
  have hb01 : ∀ d, ¬ W (M.tail d) → -1 ≤ f (.inl d) ∧ f (.inl d) ≤ 0 := by
    intro d hd
    have h1 := hf.le_cap (.inl d)
    have h2 := hf.le_cap (.inl (M.rev d))
    have h3 := hanti (.inl d)
    have hw : W (M.tail (M.rev d)) := by
      by_contra h; exact hd ((hbip d).2 h)
    simp only [mcap, hd, hw, ite_true, ite_false] at h1 h2
    simp only [pendant_rev_inl] at h3
    constructor <;> linarith
  have hcons : ∀ v, M.div (fun d => f (.inl d)) v + f (.inr (v, true)) = 0 := fun v => by
    rw [← pdiv_inl he]
    exact hf.conserve _ (inl_not_mem_mS v) (inl_not_mem_mT v)
  have hpend : ∀ v, f (.inr (v, false)) = - f (.inr (v, true)) := fun v => hanti (.inr (v, true))
  have hdivW : ∀ v, W v → M.div (fun d => f (.inl d)) v ≤ 1 := fun v hv => by
    have h1 := hf.le_cap (.inr (v, false))
    simp only [mcap, hv, ite_true] at h1
    linarith [hcons v, hpend v]
  have hdivB : ∀ v, ¬ W v → -1 ≤ M.div (fun d => f (.inl d)) v := fun v hv => by
    have h1 := hf.le_cap (.inr (v, true))
    simp only [mcap, hv, ite_false] at h1
    linarith [hcons v]
  refine ⟨⟨fun d hd => (mem_filter.1 hd).2.1, fun d hd d' hd' htl => ?_,
    fun d hd d' hd' hhd => ?_⟩, ?_⟩
  · simp only [matchOf, mem_filter, mem_univ, true_and] at hd hd'
    -- the darts leaving the white vertex carry `0` or `1`, at most one unit in total
    have h01 : ∀ x ∈ univ.filter (fun x => M.tail x = M.tail d), f (.inl x) = 0 ∨ f (.inl x) = 1 :=
      fun x hx => by
        simp only [mem_filter, mem_univ, true_and] at hx
        have := hw01 x (hx ▸ hd.1); omega
    have hs := sum_eq_card_of_01 h01
    have hle := hdivW _ hd.1
    unfold CombMap.div at hle
    rw [hs] at hle
    have := card_le_one.1 (by exact_mod_cast hle) d (by simp [hd.2]) d' (by simp [htl, hd'.2])
    exact this
  · simp only [matchOf, mem_filter, mem_univ, true_and] at hd hd'
    -- the darts leaving the black vertex carry `0` or `-1`, at most one unit in total
    have hbB : ¬ W (M.head d) := (hbip d).1 hd.1
    have h01 : ∀ x ∈ univ.filter (fun x => M.tail x = M.head d),
        -f (.inl x) = 0 ∨ -f (.inl x) = 1 := fun x hx => by
      simp only [mem_filter, mem_univ, true_and] at hx
      have := hb01 x (hx ▸ hbB); omega
    have hs := sum_eq_card_of_01 h01
    have hle := hdivB _ hbB
    unfold CombMap.div at hle
    have hs' : ∑ x with M.tail x = M.head d, f (.inl x) =
        - ((univ.filter (fun x => M.tail x = M.head d)).filter
          (fun x => -f (.inl x) = 1)).card := by
      rw [← hs, sum_neg_distrib, neg_neg]
    rw [hs'] at hle
    have hrd : f (.inl (M.rev d)) = -1 := by
      have := hanti (.inl d); simp only [pendant_rev_inl] at this; rw [this, hd.2]
    have hrd' : f (.inl (M.rev d')) = -1 := by
      have := hanti (.inl d'); simp only [pendant_rev_inl] at this; rw [this, hd'.2]
    have hc : ((univ.filter (fun x => M.tail x = M.head d)).filter
        (fun x => -f (.inl x) = 1)).card ≤ 1 := by omega
    have := card_le_one.1 hc (M.rev d) (by simp [hrd]) (M.rev d') (by simp [hrd', hhd])
    exact M.rev_injective this
  · rw [val_mS he]
    have h1 : ∑ w with W w, f (.inr (w, false)) =
        ∑ w ∈ univ.filter W, M.div (fun d => f (.inl d)) w :=
      sum_congr rfl fun w _ => by rw [hpend w]; linarith [hcons w]
    rw [h1, sum_div_eq_tail]
    have h01 : ∀ d ∈ univ.filter (fun d => M.tail d ∈ univ.filter W),
        f (.inl d) = 0 ∨ f (.inl d) = 1 := fun d hd => by
      simp only [mem_filter, mem_univ, true_and] at hd
      have := hw01 d hd; omega
    rw [sum_eq_card_of_01 h01]
    congr 2
    ext d; simp [matchOf]

/-! ### Maximum matchings -/

/-- **The matching of a maximum flow is a maximum matching.** -/
theorem matchOf_max (hbip : ∀ d, W (M.tail d) ↔ ¬ W (M.head d)) {f : D ⊕ (V × Bool) → ℤ}
    (hf : IsMax (M.pendant e he) (mcap M W) (mS W) (mT W) f) :
    IsMatching M W (matchOf M W f) ∧
      ∀ Mt, IsMatching M W Mt → Mt.card ≤ (matchOf M W f).card := by
  obtain ⟨hm, hv⟩ := matchOf_spec he hbip hf.1
  refine ⟨hm, fun Mt hMt => ?_⟩
  obtain ⟨g, hg, hgv⟩ := exists_flow_of_matching he hbip hMt
  have := hf.2 g hg
  rw [hgv, hv] at this
  exact_mod_cast this

/-- A matching has at most as many darts as white vertices and as black vertices. -/
lemma IsMatching.card_le (hbip : ∀ d, W (M.tail d) ↔ ¬ W (M.head d)) {Mt : Finset D}
    (h : IsMatching M W Mt) :
    Mt.card = (Mt.image M.tail).card ∧ Mt.card = (Mt.image M.head).card ∧
      Mt.image M.tail ⊆ univ.filter W ∧ Mt.image M.head ⊆ univ.filter fun v => ¬ W v := by
  refine ⟨(card_image_of_injOn fun a ha b hb hab => h.2.1 a ha b hb hab).symm,
    (card_image_of_injOn fun a ha b hb hab => h.2.2 a ha b hb hab).symm, ?_, ?_⟩
  · intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hv
    simpa using h.1 d hd
  · intro v hv
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hv
    simpa using (hbip d).1 (h.1 d hd)

/-- **The perfect-matching test**: given a maximum flow, a perfect matching exists iff the
matching of the flow covers the white vertices and there are as many white as black
vertices. -/
theorem exists_perfect_iff (hbip : ∀ d, W (M.tail d) ↔ ¬ W (M.head d))
    {f : D ⊕ (V × Bool) → ℤ} (hf : IsMax (M.pendant e he) (mcap M W) (mS W) (mT W) f) :
    (∃ Mt, IsPerfect M W Mt) ↔ (matchOf M W f).card = (univ.filter W).card ∧
      (univ.filter W).card = (univ.filter fun v => ¬ W v).card := by
  classical
  obtain ⟨hm, hmax⟩ := matchOf_max he hbip hf
  obtain ⟨e1, e2, s1, s2⟩ := hm.card_le hbip
  constructor
  · rintro ⟨Mt, hMt, hW, hB⟩
    obtain ⟨f1, f2, t1, t2⟩ := hMt.card_le hbip
    have hT : Mt.image M.tail = univ.filter W :=
      Subset.antisymm t1 fun v hv => by
        obtain ⟨d, hd, rfl⟩ := hW v (by simpa using hv); exact mem_image_of_mem _ hd
    have hH : Mt.image M.head = univ.filter fun v => ¬ W v :=
      Subset.antisymm t2 fun v hv => by
        obtain ⟨d, hd, rfl⟩ := hB v (by simpa using hv); exact mem_image_of_mem _ hd
    have h1 := hmax Mt hMt
    have h2 := card_le_card s1
    rw [hT] at f1; rw [hH] at f2
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨matchOf M W f, hm, fun v hv => ?_, fun v hv => ?_⟩
    · have : (matchOf M W f).image M.tail = univ.filter W :=
        eq_of_subset_of_card_le s1 (by omega)
      have hv' : v ∈ (matchOf M W f).image M.tail := by rw [this]; simpa using hv
      obtain ⟨d, hd, rfl⟩ := mem_image.1 hv'
      exact ⟨d, hd, rfl⟩
    · have : (matchOf M W f).image M.head = univ.filter fun v => ¬ W v :=
        eq_of_subset_of_card_le s2 (by omega)
      have hv' : v ∈ (matchOf M W f).image M.head := by rw [this]; simpa using hv
      obtain ⟨d, hd, rfl⟩ := mem_image.1 hv'
      exact ⟨d, hd, rfl⟩

end BKMNW

namespace CombMap

/-! ### Pendant edges keep the rotations and the faces transitive -/

open BKMNW (ItReach)

variable {D V F : Type*} [DecidableEq D] {M : CombMap D V F} {e : V → D}
  (he : ∀ v, M.tail (e v) = v)

lemma pendant_rot_inl (d : D) : (M.pendant e he).rot (.inl d) =
    if M.rot d = e (M.tail d) then .inr (M.tail d, true) else .inl (M.rot d) := by
  show pNext M e (.inl (M.rev d)) = _
  simp only [pNext, head_rev]
  rfl

lemma pendant_next_inl (d : D) : (M.pendant e he).next (.inl d) =
    if M.next d = e (M.head d) then .inr (M.head d, true) else .inl (M.next d) := rfl

lemma pendant_reach_rot (d : D) :
    ItReach (M.pendant e he).rot (.inl d) (.inl (M.rot d)) := by
  by_cases h : M.rot d = e (M.tail d)
  · refine (ItReach.of_eq (y := .inr (M.tail d, true)) (by simp [pendant_rot_inl, h])).trans
      (ItReach.of_eq ?_)
    rw [h]; rfl
  · exact ItReach.of_eq (by simp [pendant_rot_inl, h])

lemma pendant_reach_rot_iterate (k : ℕ) (d : D) :
    ItReach (M.pendant e he).rot (.inl d) (.inl (M.rot^[k] d)) := by
  induction k generalizing d with
  | zero => exact ItReach.rfl'
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (pendant_reach_rot he d).trans (ih _)

lemma pendant_reach_next (d : D) :
    ItReach (M.pendant e he).next (.inl d) (.inl (M.next d)) := by
  by_cases h : M.next d = e (M.head d)
  · refine (ItReach.of_eq (y := .inr (M.head d, true)) (by simp [pendant_next_inl, h])).trans
      ((ItReach.of_eq rfl).trans (ItReach.of_eq ?_))
    rw [h]; rfl
  · exact ItReach.of_eq (by simp [pendant_next_inl, h])

lemma pendant_reach_next_iterate (k : ℕ) (d : D) :
    ItReach (M.pendant e he).next (.inl d) (.inl (M.next^[k] d)) := by
  induction k generalizing d with
  | zero => exact ItReach.rfl'
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact (pendant_reach_next he d).trans (ih _)

/-- **Pendant edges keep the rotations transitive.** -/
theorem pendant_rotTrans [Finite D] (hrot : M.RotTrans) : (M.pendant e he).RotTrans := by
  -- every dart at `inl v` reaches `inl (e v)` and is reached from it
  have up : ∀ x v, (M.pendant e he).tail x = .inl v →
      ItReach (M.pendant e he).rot x (.inl (e v)) := by
    rintro (d | ⟨w, _ | _⟩) v hx
    · obtain ⟨k, hk⟩ := hrot d (e v) (by rw [he]; exact Sum.inl.inj hx)
      exact hk ▸ pendant_reach_rot_iterate he k d
    · exact absurd hx (by simp)
    · cases Sum.inl.inj hx
      exact ItReach.of_eq rfl
  have down : ∀ x v, (M.pendant e he).tail x = .inl v →
      ItReach (M.pendant e he).rot (.inl (e v)) x := by
    rintro (d | ⟨w, _ | _⟩) v hx
    · obtain ⟨k, hk⟩ := hrot (e v) d (by rw [he]; exact (Sum.inl.inj hx).symm)
      exact hk ▸ pendant_reach_rot_iterate he k (e v)
    · exact absurd hx (by simp)
    · cases Sum.inl.inj hx
      obtain ⟨c, hc⟩ := Finite.injective_iff_surjective.1 M.rot_injective (e w)
      have hcw : M.tail c = w := by rw [← M.tail_rot, hc, he]
      obtain ⟨k, hk⟩ := hrot (e w) c (by rw [he, hcw])
      exact (hk ▸ pendant_reach_rot_iterate he k (e w)).trans
        (ItReach.of_eq (by simp [pendant_rot_inl, hc, hcw]))
  intro x y hxy
  rcases x with d | ⟨w, _ | _⟩
  · exact (up _ _ rfl).trans (down y _ hxy.symm)
  · rcases y with d' | ⟨w', _ | _⟩
    · exact absurd hxy (by simp)
    · cases Sum.inr.inj hxy
      exact ItReach.rfl'
    · exact absurd hxy (by simp)
  · exact (up _ _ rfl).trans (down y _ hxy.symm)

/-- **Pendant edges keep the faces transitive.** -/
theorem pendant_faceTrans [Finite D] (hface : M.FaceTrans) : (M.pendant e he).FaceTrans := by
  have up : ∀ x, ∃ d, M.face d = (M.pendant e he).face x ∧
      ItReach (M.pendant e he).next x (.inl d) := by
    rintro (d | ⟨w, _ | _⟩)
    · exact ⟨d, rfl, ItReach.rfl'⟩
    · exact ⟨e w, rfl, ItReach.of_eq rfl⟩
    · exact ⟨e w, rfl, (ItReach.of_eq rfl).trans (ItReach.of_eq rfl)⟩
  have down : ∀ d y, M.face d = (M.pendant e he).face y →
      ItReach (M.pendant e he).next (.inl d) y := by
    intro d y h
    have key : ∀ w, M.face d = M.face (e w) →
        ItReach (M.pendant e he).next (.inl d) (.inr (w, true)) := by
      intro w hw
      obtain ⟨c, hc⟩ := Finite.injective_iff_surjective.1 M.next_injective (e w)
      have hcw : M.head c = w := by rw [← M.tail_rev, ← M.tail_next, hc, he]
      obtain ⟨k, hk⟩ := hface d c (by rw [hw, ← hc, M.face_next])
      exact (hk ▸ pendant_reach_next_iterate he k d).trans
        (ItReach.of_eq (by simp [pendant_next_inl, hc, hcw]))
    rcases y with d' | ⟨w, _ | _⟩
    · obtain ⟨k, hk⟩ := hface d d' h
      exact hk ▸ pendant_reach_next_iterate he k d
    · exact (key w h).trans (ItReach.of_eq rfl)
    · exact key w h
  intro x y hxy
  obtain ⟨d, hd, h1⟩ := up x
  exact h1.trans (down d y (hd.trans hxy))

/-- On a plane map with at least one dart, every vertex is the tail of a dart: the darts at
which the pendant edges are drawn exist. -/
theorem exists_tail_eq [Fintype D] [Fintype V] [Fintype F] [Nonempty D] (hM : M.IsPlane) :
    ∃ e : V → D, ∀ v, M.tail (e v) = v := by
  have h : ∀ v, ∃ d, M.tail d = v := by
    intro v
    obtain ⟨d₀⟩ := ‹Nonempty D›
    rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).1 (hM.conn (M.tail d₀) v) with
      h | ⟨c, -, d, -, hd⟩
    · exact ⟨d₀, h.symm⟩
    · exact ⟨M.rev d, hd⟩
  choose e he using h
  exact ⟨e, he⟩

end CombMap

namespace BKMNW

open Finset CombMap

/-! ### Maximum matching by the algorithm -/

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {W : V → Prop} [DecidablePred W] {e : V → D}

lemma mcap_nonneg (x : D ⊕ (V × Bool)) : 0 ≤ mcap M W x := by
  rcases x with d | ⟨v, _ | _⟩ <;> simp only [mcap] <;> split_ifs <;> simp

variable (M W e) in
/-- **The matching computed by the algorithm**: the matching of the maximum flow computed by
`PlanarFlow.BKMNW.algo` on the map with a pendant edge at every vertex, drawn just before `e v`,
with the capacities `mcap`, the pendant neighbours of the white vertices as sources and those of
the black vertices as sinks. -/
noncomputable def planeMatching (he : ∀ v, M.tail (e v) = v) : Finset D :=
  matchOf M W (algo (M.pendant e he) (mcap M W) (mS W) (mT W))

/-- The algorithm computes a maximum flow of the matching network. -/
theorem algo_pendant_isMax (he : ∀ v, M.tail (e v) = v) (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) :
    IsMax (M.pendant e he) (mcap M W) (mS W) (mT W)
      (algo (M.pendant e he) (mcap M W) (mS W) (mT W)) :=
  maxflow_plane (pendant_isPlane he hM) (pendant_rotTrans he hrot) (pendant_faceTrans he hface)
    mcap_nonneg mS_mT_disjoint

/-- **Maximum bipartite matching in plane graphs.** On a plane map with transitive rotations and
faces whose darts all join a white and a black vertex, for any choice `e` of a dart leaving each
vertex (where the pendant edges are drawn; one exists as soon as the map has a dart,
`PlanarFlow.CombMap.exists_tail_eq`), the matching computed by the algorithm
(`planeMatching`) is a maximum matching, and a perfect matching exists iff it covers the white
vertices and there are as many white as black vertices. -/
theorem matching_plane (he : ∀ v, M.tail (e v) = v) (hM : M.IsPlane) (hrot : M.RotTrans)
    (hface : M.FaceTrans) (hbip : ∀ d, W (M.tail d) ↔ ¬ W (M.head d)) :
    IsMatching M W (planeMatching M W e he) ∧
      (∀ Mt, IsMatching M W Mt → Mt.card ≤ (planeMatching M W e he).card) ∧
      ((∃ Mt, IsPerfect M W Mt) ↔ (planeMatching M W e he).card = (univ.filter W).card ∧
        (univ.filter W).card = (univ.filter fun v => ¬ W v).card) := by
  have hmax := algo_pendant_isMax (W := W) he hM hrot hface
  exact ⟨(matchOf_max he hbip hmax).1, (matchOf_max he hbip hmax).2,
    exists_perfect_iff he hbip hmax⟩

end BKMNW

/-! ### Plane rotation systems -/

namespace BKMNW

open Finset CombMap

variable {X : Type*} [Fintype X] [DecidableEq X] {Γ : SimpleGraph X} [DecidableRel Γ.Adj]
  {R : Kasteleyn.RotationSystem Γ} {W : X → Prop} [DecidablePred W]

/-- **Perfect matchings of the graph**: for a 2-colouring of the graph of a rotation system, some
set of darts is a perfect matching (`IsPerfect`) iff the graph has a perfect matching in the sense
of Mathlib. -/
theorem exists_isPerfect_ofRotation_iff (hbip : ∀ a b, Γ.Adj a b → (W a ↔ ¬ W b)) :
    (∃ Mt, IsPerfect (CombMap.ofRotation R) W Mt) ↔ ∃ G' : Γ.Subgraph, G'.IsPerfectMatching := by
  classical
  have hd : ∀ d : Γ.Dart, W d.fst ↔ ¬ W d.snd := fun d => hbip _ _ d.adj
  constructor
  · rintro ⟨Mt, ⟨hW, htl, hhd⟩, hcW, hcB⟩
    let G' : Γ.Subgraph :=
      { verts := Set.univ
        Adj := fun a b => ∃ d ∈ Mt, (d.fst = a ∧ d.snd = b) ∨ (d.fst = b ∧ d.snd = a)
        adj_sub := by
          rintro a b ⟨d, -, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
          · exact d.adj
          · exact d.adj.symm
        edge_vert := fun _ => Set.mem_univ _
        symm := ⟨by
          rintro a b ⟨d, hdM, h | h⟩
          · exact ⟨d, hdM, .inr h⟩
          · exact ⟨d, hdM, .inl h⟩⟩ }
    refine ⟨G', SimpleGraph.Subgraph.isPerfectMatching_iff.2 fun v => ?_⟩
    by_cases hv : W v
    · obtain ⟨d, hdM, rfl⟩ := hcW v hv
      refine ⟨d.snd, ⟨d, hdM, .inl ⟨rfl, rfl⟩⟩, ?_⟩
      rintro w ⟨d', hd'M, ⟨h1, rfl⟩ | ⟨rfl, h2⟩⟩
      · rw [htl d' hd'M d hdM h1]
      · exact absurd (by rw [h2]; exact hv) ((hd d').1 (hW d' hd'M))
    · obtain ⟨d, hdM, hdv⟩ := hcB v hv
      refine ⟨d.fst, ⟨d, hdM, .inr ⟨rfl, hdv⟩⟩, ?_⟩
      rintro w ⟨d', hd'M, ⟨rfl, h2⟩ | ⟨rfl, h2⟩⟩
      · exact absurd (hW d' hd'M) hv
      · rw [hhd d' hd'M d hdM (h2.trans hdv.symm)]
  · rintro ⟨G', hG'⟩
    have hu := SimpleGraph.Subgraph.isPerfectMatching_iff.1 hG'
    refine ⟨univ.filter fun d : Γ.Dart => W d.fst ∧ G'.Adj d.fst d.snd,
      ⟨fun d h => (mem_filter.1 h).2.1, fun d h d' h' htl => ?_, fun d h d' h' hhd => ?_⟩,
      fun v hv => ?_, fun v hv => ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at h h'
      change d.fst = d'.fst at htl
      have e2 : d.snd = d'.snd := (hu d.fst).unique h.2 (htl ▸ h'.2)
      exact SimpleGraph.Dart.ext _ _ (Prod.ext htl e2)
    · simp only [mem_filter, mem_univ, true_and] at h h'
      change d.snd = d'.snd at hhd
      have e1 : d.fst = d'.fst := (hu d.snd).unique h.2.symm (hhd ▸ h'.2.symm)
      exact SimpleGraph.Dart.ext _ _ (Prod.ext e1 hhd)
    · obtain ⟨w, hw, -⟩ := hu v
      exact ⟨⟨(v, w), G'.adj_sub hw⟩, by simp [hv, hw], rfl⟩
    · obtain ⟨w, hw, -⟩ := hu v
      have hww : W w := by
        by_contra h
        exact hv ((hbip v w (G'.adj_sub hw)).2 h)
      exact ⟨⟨(w, v), (G'.adj_sub hw).symm⟩, by simp [hww, hw.symm], rfl⟩

/-- In a plane rotation system every vertex has a dart leaving it
(`Kasteleyn.RotationSystem.IsPlane.exists_dart`): the darts at which the pendant edges are drawn
exist. -/
theorem exists_dart_fst (hR : R.IsPlane) : ∃ e : X → Γ.Dart, ∀ v, (e v).fst = v := by
  choose e he using hR.exists_dart
  exact ⟨e, he⟩

/-- **Maximum bipartite matching in plane graphs, for rotation systems.** For a plane rotation
system of a graph `Γ` with a 2-colouring `W` (adjacent vertices have different colours), and any
choice `e` of a dart leaving each vertex (where the pendant edges are drawn; one always exists,
`exists_dart_fst`), the matching computed by the algorithm (`planeMatching`) is a maximum
matching, and `Γ` has a perfect matching iff that matching covers the white vertices and there are
as many white as black vertices. -/
theorem matching_plane_ofRotation (hR : R.IsPlane) (hbip : ∀ a b, Γ.Adj a b → (W a ↔ ¬ W b))
    {e : X → Γ.Dart} (he : ∀ v, (e v).fst = v) :
    IsMatching (CombMap.ofRotation R) W (planeMatching (CombMap.ofRotation R) W e he) ∧
      (∀ Mt, IsMatching (CombMap.ofRotation R) W Mt →
        Mt.card ≤ (planeMatching (CombMap.ofRotation R) W e he).card) ∧
      ((∃ G' : Γ.Subgraph, G'.IsPerfectMatching) ↔
        (planeMatching (CombMap.ofRotation R) W e he).card = (univ.filter W).card ∧
          (univ.filter W).card = (univ.filter fun v => ¬ W v).card) := by
  obtain ⟨h1, h2, h3⟩ := matching_plane (M := CombMap.ofRotation R) (W := W) he
    (CombMap.ofRotation_isPlane hR) (MSSP.ofRotation_rotTrans R) (ofRotation_faceTrans R)
    (fun d => hbip _ _ d.adj)
  exact ⟨h1, h2, (exists_isPerfect_ofRotation_iff hbip).symm.trans h3⟩

/-! ### The hypotheses can be met together: a single edge -/

/-- The rotation system of a single edge. -/
def edgeRot : Kasteleyn.RotationSystem (⊤ : SimpleGraph (Fin 2)) where
  rot := 1
  fst_rot _ := rfl
  sameCycle_of_fst_eq d d' h := by
    have : d = d' := by
      obtain ⟨⟨a, b⟩, hab⟩ := d
      obtain ⟨⟨a', b'⟩, hab'⟩ := d'
      simp only at h
      subst h
      have : b = b' := by
        simp only [SimpleGraph.top_adj] at hab hab'
        omega
      subst this
      rfl
    exact this ▸ Equiv.Perm.SameCycle.refl _ _

/-- A single edge is a plane graph. -/
theorem edgeRot_isPlane : edgeRot.IsPlane := by
  refine ⟨SimpleGraph.connected_top, ?_⟩
  have h1 : Fintype.card edgeRot.Face = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨edgeRot.face ⟨(0, 1), by decide⟩, fun y => ?_⟩
    obtain ⟨⟨⟨a, b⟩, hab⟩, rfl⟩ := edgeRot.face_surjective y
    refine edgeRot.face_eq_face_iff.2 ?_
    fin_cases a <;> fin_cases b
    · exact absurd hab (by decide)
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact ⟨-1, rfl⟩
    · exact absurd hab (by decide)
  rw [h1]
  decide

/-- **The hypotheses of `matching_plane_ofRotation` can be met together**: a single edge, with
one white and one black end. -/
theorem edgeRot_hyps : edgeRot.IsPlane ∧
    (∀ a b, (⊤ : SimpleGraph (Fin 2)).Adj a b → (a = 0 ↔ ¬ b = 0)) ∧
    ∃ e : Fin 2 → (⊤ : SimpleGraph (Fin 2)).Dart, ∀ v, (e v).fst = v := by
  refine ⟨edgeRot_isPlane, fun a b hab => ?_, exists_dart_fst edgeRot_isPlane⟩
  simp only [SimpleGraph.top_adj] at hab
  omega

/-- **The hypotheses of `matching_plane` can be met together**: the map of a single edge, with
one white and one black end. -/
theorem ofRotation_edgeRot_hyps : (CombMap.ofRotation edgeRot).IsPlane ∧
    (CombMap.ofRotation edgeRot).RotTrans ∧ (CombMap.ofRotation edgeRot).FaceTrans ∧
    (∀ d, (CombMap.ofRotation edgeRot).tail d = 0 ↔ ¬ (CombMap.ofRotation edgeRot).head d = 0) ∧
    ∃ e : Fin 2 → (⊤ : SimpleGraph (Fin 2)).Dart,
      ∀ v, (CombMap.ofRotation edgeRot).tail (e v) = v :=
  ⟨CombMap.ofRotation_isPlane edgeRot_isPlane, MSSP.ofRotation_rotTrans _,
    ofRotation_faceTrans _, fun d => edgeRot_hyps.2.1 _ _ d.adj, exists_dart_fst edgeRot_isPlane⟩

end BKMNW

end PlanarFlow
