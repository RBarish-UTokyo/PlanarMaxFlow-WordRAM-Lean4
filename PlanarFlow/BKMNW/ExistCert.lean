module

public import PlanarFlow.BKMNW.ExistComp

/-!
# Balanced splits of a piece map

A certificate of a split of the piece map on the darts `N` (`SCert`) is a simple path through the
holes, of at most `L` vertices, and a family of *items*: pairwise disjoint sets of darts, closed
under the steps of the piece map avoiding the new hole (so that every child made of items is a
union of components of the piece map with the new hole removed), covering the darts with an end
off the new hole, each of weight (`wtY`: one per dart plus extra weights) at most `A`. Grouping
the items gives the two children.

* `scert_core`: a piece map whose holes are not cut vertices has a certificate with two items,
  the two sides of Miller's cycle (`exists_core_cycle`).
* `scert_cut`: when a hole is a cut vertex with light components, the components at the hole.
* `scert_prune`: the components of a cut vertex other than a heavy one are deleted, their weight
  put on the hole; a certificate of the rest lifts.
* `exists_scert`: **every piece map has a certificate**, by recursion on the number of darts.
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
/-- The weight of a set of darts: one for every dart, and the extra weight `ex` of the darts
leaving vertices off `Y`. -/
def wtY (ex : D → ℕ) (Y : Finset V) (X : Finset D) : ℕ :=
  ∑ d ∈ X, (1 + if M.tail d ∈ Y then 0 else ex d)

lemma wtY_le (ex : D → ℕ) (Y : Finset V) (X : Finset D) :
    wtY M ex Y X ≤ ∑ d ∈ X, (1 + ex d) :=
  sum_le_sum fun d _ => by split_ifs <;> omega

variable (M) in
/-- **A certificate of a balanced split** of the piece map on the darts `N`: a simple path `ρ`
through the holes along darts of `Nρ` (its last vertex leaving a dart of `Nρ`), through at most
`L` vertices, and items (sets of darts of
`N` closed under the steps avoiding the new hole `newHole Hs ρ.mverts`, pairwise disjoint,
covering the darts with an end off the new hole), each of weight at most `A`. -/
def SCert (N Nρ : Finset D) (Hs : List (Finset V)) (ex : D → ℕ) (A L : ℕ) : Prop :=
  ∃ (ρ : HPath M) (I : Finset (Finset D)),
    ρ.Simple Hs ∧ (∀ e ∈ ρ.darts, e ∈ Nρ) ∧ ρ.k + 1 ≤ L ∧ (∃ x ∈ Nρ, M.tail x = ρ.p ρ.k) ∧
    (∀ X ∈ I, ∀ Y ∈ I, X ≠ Y → Disjoint X Y) ∧
    (∀ X ∈ I, X ⊆ N ∧ ∀ a ∈ X, ∀ b, AStep M N Hs (newHole Hs ρ.mverts) a b → b ∈ X) ∧
    (∀ d ∈ N, ¬ (M.tail d ∈ newHole Hs ρ.mverts ∧ M.head d ∈ newHole Hs ρ.mverts) →
      ∃ X ∈ I, d ∈ X) ∧
    (∀ X ∈ I, wtY M ex (newHole Hs ρ.mverts) X ≤ A)

/-- The new hole of a simple path through the holes: the vertices related to a vertex of the
path. -/
lemma mem_newHole_iff {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {ρ : HPath M}
    (hρ : ρ.Simple Hs) {v : V} : v ∈ newHole Hs ρ.mverts ↔ ∃ j ≤ ρ.k, HRel Hs v (ρ.p j) := by
  have hm : ∀ m ∈ ρ.mverts, ∃ j ≤ ρ.k, HRel Hs m (ρ.p j) := by
    intro m hm
    rcases ρ.mem_mverts.1 hm with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact ⟨j, hj, Or.inl rfl⟩
    · exact ⟨j + 1, hj, hρ.1 j hj⟩
  constructor
  · intro h
    rcases mem_newHole.1 h with h | ⟨H, hH, hHC, hv⟩
    · exact hm v h
    · obtain ⟨m, hmH, hmC⟩ := not_disjoint_iff.1 hHC
      obtain ⟨j, hj, hr⟩ := hm m hmC
      exact ⟨j, hj, hRel_trans' hd (Or.inr ⟨H, hH, hv, hmH⟩) hr⟩
  · rintro ⟨j, hj, h | ⟨H, hH, hv, hp⟩⟩
    · exact mem_newHole.2 (Or.inl (h ▸ ρ.p_mem_mverts hj))
    · exact mem_newHole.2 (Or.inr ⟨H, hH, not_disjoint_iff.2 ⟨_, hp, ρ.p_mem_mverts hj⟩, hv⟩)

/-- The new hole is closed under the relation of the holes. -/
lemma hClosed_newHole {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {ρ : HPath M}
    (hρ : ρ.Simple Hs) : HClosed Hs (newHole Hs ρ.mverts) := by
  intro a ha b hab
  obtain ⟨j, hj, h⟩ := (mem_newHole_iff hd hρ).1 ha
  exact (mem_newHole_iff hd hρ).2 ⟨j, hj, hRel_trans' hd (hRel_symm hab) h⟩

section SideItem

variable {τ : Perm D} {N : Finset D} (hσ : Stable τ N) (hB : Stable (revPerm M) N)

/-- The darts of the piece map with an end in a set `S` of its vertices. -/
noncomputable def sideItem (S : Finset (SVert τ N)) : Finset D :=
  (univ.filter fun x : SDart N =>
    Quotient.mk _ x ∈ S ∨ Quotient.mk _ ((psep M hσ hB).α x) ∈ S).map (Embedding.subtype _)

lemma mem_sideItem {S : Finset (SVert τ N)} {d : D} : d ∈ sideItem hσ hB S ↔
    ∃ h : d ∈ N, Quotient.mk _ (⟨d, h⟩ : SDart N) ∈ S ∨
      Quotient.mk _ ((psep M hσ hB).α ⟨d, h⟩) ∈ S := by
  simp only [sideItem, mem_map, mem_filter, mem_univ, true_and, Embedding.coe_subtype]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact ⟨x.2, hx⟩
  · rintro ⟨h, hx⟩; exact ⟨⟨d, h⟩, hx, rfl⟩

lemma sideItem_subset (S : Finset (SVert τ N)) : sideItem (M := M) hσ hB S ⊆ N :=
  fun _ h => ((mem_sideItem hσ hB).1 h).1

end SideItem

open Classical in
/-- **The certificate of a piece map whose holes are not cut vertices**, from Miller's theorem on
it (`exists_core_cycle`, its faces being small by `PMap.small_of_noCut`): the two items are the
darts with an end on either side. -/
theorem scert_core {N : Finset D} {Hs : List (Finset V)} {τ : Perm D} (hd : Hs.Pairwise Disjoint)
    (hloopM : ∀ d, M.head d ≠ M.tail d) (hN : PMap M N Hs τ) {x₀ : D} (hx₀ : x₀ ∈ N)
    (hnc : NoCut M N Hs) (ex : D → ℕ) {A : ℕ}
    (hA : 2 * (∑ d ∈ N, (1 + ex d)) + 2 + 9 * (6 * Nat.sqrt (2 * N.card) + 4) ≤ 3 * A) :
    SCert M N N Hs ex A (6 * Nat.sqrt (2 * N.card) + 4) := by
  have hσ := hN.stable
  have hB := hN.rev
  have hsmall := hN.small_of_noCut hd hloopM hx₀ hnc
  have hloop : ∀ x ∈ N, ¬ HRel Hs (M.head x) (M.tail x) := by
    rintro x hx (e | ⟨H, hH, h1, h2⟩)
    · exact hloopM x e
    · exact hN.inner x hx ⟨H, hH, h2, h1⟩
  obtain ⟨ρ, I, O, hsim, hdar, hlen, htouch, hIO, hon, hoff, hIO', hOI', hwI, hwO⟩ :=
    exists_core_cycle hσ hB hN.vert hx₀ hN.conn' hN.gap hloop hsmall (fun _ => 1)
      (fun _ => le_rfl) (fun q => ∑ x : SDart N with Quotient.mk _ x = q, ex x.1)
  set Ns := psep M hσ hB with hNs
  have hcls : ∀ x y : SDart N, (Quotient.mk (orbSetoid τ N) x = Quotient.mk _ y) ↔
      HRel Hs (M.tail x.1) (M.tail y.1) := fun x y => sVert_eq_iff.trans (hN.vert _ x.2 _ y.2)
  set h'' := newHole Hs ρ.mverts with hh''
  -- the darts whose class lies in a side are off the new hole
  have hoffI : ∀ x : SDart N, (Quotient.mk _ x ∈ I ∨ Quotient.mk _ x ∈ O) → M.tail x.1 ∉ h'' := by
    intro x hx h
    obtain ⟨j, hj, hr⟩ := (mem_newHole_iff hd hsim).1 h
    exact hoff x hx j hj hr
  have honI : ∀ x : SDart N, M.tail x.1 ∉ h'' → (Quotient.mk _ x ∈ I ∨ Quotient.mk _ x ∈ O) := by
    intro x hx
    by_contra h
    push Not at h
    obtain ⟨j, hj, hr⟩ := hon x h.1 h.2
    exact hx ((mem_newHole_iff hd hsim).2 ⟨j, hj, hr⟩)
  set XI : Finset D := sideItem hσ hB I with hXI
  set XO : Finset D := sideItem hσ hB O with hXO
  have hmemX : ∀ (S : Finset (SVert τ N)) (d : D), d ∈ sideItem hσ hB S ↔
      ∃ h : d ∈ N, Quotient.mk _ (⟨d, h⟩ : SDart N) ∈ S ∨
        Quotient.mk _ (Ns.α ⟨d, h⟩) ∈ S := fun S d => mem_sideItem hσ hB
  have hαv : ∀ x : SDart N, (Ns.α x).1 = M.rev x.1 := fun x => psep_α hσ hB x
  refine ⟨ρ, {XI, XO}, hsim, hdar, hlen, htouch ρ.k le_rfl, ?_, ?_, ?_, ?_⟩
  · -- the two items are disjoint
    have hdis : Disjoint XI XO := by
      refine disjoint_left.2 fun d h1 h2 => ?_
      obtain ⟨hdN, h1⟩ := (hmemX I d).1 h1
      obtain ⟨hdN', h2⟩ := (hmemX O d).1 h2
      rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
      · exact disjoint_left.1 hIO h1 h2
      · exact hIO' _ h1 h2
      · exact hOI' _ h2 h1
      · exact disjoint_left.1 hIO h1 h2
    intro X hX Y hY hXY
    simp only [mem_insert, mem_singleton] at hX hY
    rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
    · exact absurd rfl hXY
    · exact hdis
    · exact hdis.symm
    · exact absurd rfl hXY
  · -- the items are closed
    have hclos : ∀ (S S' : Finset (SVert τ N)),
        (∀ x : SDart N, Quotient.mk _ x ∈ S' → Quotient.mk _ (Ns.α x) ∉ S) →
        (∀ x : SDart N, M.tail x.1 ∉ h'' → (Quotient.mk _ x ∈ S ∨ Quotient.mk _ x ∈ S')) →
        ∀ a, a ∈ sideItem hσ hB S → ∀ b, AStep M N Hs h'' a b → b ∈ sideItem hσ hB S := by
      intro S S' hSS hcov a ha b hab
      obtain ⟨haN, ha⟩ := (hmemX S a).1 ha
      refine (hmemX S b).2 ⟨hab.1, ?_⟩
      rcases hab.2 with e | ⟨e, hah⟩
      · subst e
        have h1 : Ns.α ⟨a, haN⟩ = ⟨M.rev a, hab.1⟩ := Subtype.ext (hαv _)
        have h2 : Ns.α ⟨M.rev a, hab.1⟩ = ⟨a, haN⟩ := Subtype.ext (by rw [hαv, M.rev_rev])
        rw [h1] at ha; rw [h2]; tauto
      · have hab' : Quotient.mk (orbSetoid τ N) ⟨b, hab.1⟩ = Quotient.mk _ ⟨a, haN⟩ :=
          (hcls _ _).2 (hRel_symm e)
        rw [hab']
        rcases ha with h | h
        · exact Or.inl h
        · rcases hcov ⟨a, haN⟩ hah with h' | h'
          · exact Or.inl h'
          · exact absurd h (hSS _ h')
    intro X hX
    simp only [mem_insert, mem_singleton] at hX
    rcases hX with rfl | rfl
    · exact ⟨sideItem_subset hσ hB I, hclos I O hOI' fun x hx => honI x hx⟩
    · exact ⟨sideItem_subset hσ hB O, hclos O I hIO' fun x hx => (honI x hx).symm⟩
  · -- the items cover the darts with an end off the new hole
    intro d hd hnot
    have hrd : M.rev d ∈ N := hB d hd
    by_cases ht : M.tail d ∈ h''
    · have hh : M.head d ∉ h'' := fun h => hnot ⟨ht, h⟩
      have hα : Ns.α ⟨d, hd⟩ = ⟨M.rev d, hrd⟩ := Subtype.ext (hαv _)
      rcases honI ⟨M.rev d, hrd⟩ (by rw [CombMap.tail_rev]; exact hh) with h | h
      · exact ⟨XI, by simp, (hmemX I d).2 ⟨hd, Or.inr (by rw [hα]; exact h)⟩⟩
      · exact ⟨XO, by simp, (hmemX O d).2 ⟨hd, Or.inr (by rw [hα]; exact h)⟩⟩
    · rcases honI ⟨d, hd⟩ ht with h | h
      · exact ⟨XI, by simp, (hmemX I d).2 ⟨hd, Or.inl h⟩⟩
      · exact ⟨XO, by simp, (hmemX O d).2 ⟨hd, Or.inl h⟩⟩
  · -- the weights
    have hwt : ∀ (S S' : Finset (SVert τ N)), Disjoint S S' →
        (∀ x : SDart N, Quotient.mk _ x ∈ S' → Quotient.mk _ (Ns.α x) ∉ S) →
        (∀ x : SDart N, M.tail x.1 ∉ h'' → (Quotient.mk _ x ∈ S ∨ Quotient.mk _ x ∈ S')) →
        (∀ x : SDart N, Quotient.mk _ x ∈ S → M.tail x.1 ∉ h'') →
        wtY M ex h'' (sideItem hσ hB S) =
        (∑ x : SDart N with (Quotient.mk _ x ∈ S ∨ Quotient.mk _ (Ns.α x) ∈ S), 1) +
          ∑ q ∈ S, ∑ x : SDart N with Quotient.mk _ x = q, ex x.1 := by
      intro S S' hdSS hSS hcov hS
      rw [wtY, sideItem, sum_map, sum_add_distrib]
      congr 1
      rw [sum_fiberwise_eq_sum_filter univ S (fun x : SDart N => Quotient.mk _ x)
        (fun x => ex x.1)]
      have hite : ∀ x : SDart N, (if M.tail ((Embedding.subtype fun x => x ∈ N) x) ∈ h'' then 0
          else ex ((Embedding.subtype fun x => x ∈ N) x)) =
          if M.tail x.1 ∉ h'' then ex x.1 else 0 := fun x => by
        simp only [Embedding.coe_subtype]; split_ifs <;> simp_all
      simp_rw [hite]
      rw [← sum_filter, filter_filter]
      refine sum_congr ?_ fun _ _ => rfl
      ext x
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hx, ht⟩
        rcases hcov x ht with h | h
        · exact h
        · rcases hx with hx | hx
          · exact absurd hx (disjoint_left.1 hdSS.symm h)
          · exact absurd hx (hSS x h)
      · intro h; exact ⟨Or.inl h, hS x h⟩
    have htot : (∑ x : SDart N, 1) + ∑ q : SVert τ N,
        ∑ x : SDart N with Quotient.mk (orbSetoid τ N) x = q, ex x.1 =
        ∑ d ∈ N, (1 + ex d) := by
      rw [Finset.sum_fiberwise univ (fun x : SDart N => Quotient.mk (orbSetoid τ N) x)
        (fun x => ex x.1), ← sum_add_distrib, ← Finset.sum_coe_sort N (fun d => 1 + ex d)]
    intro X hX
    simp only [mem_insert, mem_singleton] at hX
    rcases hX with rfl | rfl
    · rw [hwt I O hIO hOI' (fun x hx => honI x hx) (fun x hx => hoffI x (Or.inl hx))]
      rw [htot] at hwI; omega
    · rw [hwt O I hIO.symm hIO' (fun x hx => (honI x hx).symm)
        (fun x hx => hoffI x (Or.inr hx))]
      rw [htot] at hwO; omega

/-! ### Components off a hole -/

variable (M) in
/-- The component of the dart `x` in the piece map on the darts `N` with the hole `g` removed. -/
noncomputable def comp (N : Finset D) (Hs : List (Finset V)) (g : Finset V) (x : D) :
    Finset D := by
  classical exact N.filter fun y => ReflTransGen (AStep M N Hs g) x y

section Comp

variable {N : Finset D} {Hs : List (Finset V)} {g : Finset V}

lemma mem_comp {x y : D} : y ∈ comp M N Hs g x ↔ y ∈ N ∧ ReflTransGen (AStep M N Hs g) x y := by
  classical simp [comp]

lemma self_mem_comp {x : D} (hx : x ∈ N) : x ∈ comp M N Hs g x := mem_comp.2 ⟨hx, .refl⟩

lemma comp_closed {x y z : D} (hy : y ∈ comp M N Hs g x) (h : AStep M N Hs g y z) :
    z ∈ comp M N Hs g x :=
  mem_comp.2 ⟨h.1, (mem_comp.1 hy).2.tail h⟩

lemma rtg_symm_aStep (hg : HClosed Hs g) {x y : D} (hx : x ∈ N)
    (h : ReflTransGen (AStep M N Hs g) x y) : ReflTransGen (AStep M N Hs g) y x := by
  induction h with
  | refl => exact .refl
  | tail h1 hst ih =>
    rename_i b c
    have hb : b ∈ N := by
      rcases h1.cases_tail with h | ⟨_, _, h⟩
      · exact h ▸ hx
      · exact h.1
    exact ReflTransGen.head (hst.symm hg hb) ih

lemma comp_eq_of_mem (hg : HClosed Hs g) {x y : D} (hx : x ∈ N) (hy : y ∈ comp M N Hs g x) :
    comp M N Hs g y = comp M N Hs g x := by
  have hxy := (mem_comp.1 hy).2
  have hyx := rtg_symm_aStep hg hx hxy
  ext z
  simp only [mem_comp]
  exact and_congr_right fun _ => ⟨fun h => hxy.trans h, fun h => hyx.trans h⟩

lemma comp_conn (hg : HClosed Hs g) {x : D} (hx : x ∈ N) :
    ∀ a ∈ comp M N Hs g x, ∀ b ∈ comp M N Hs g x,
      ReflTransGen (HStep M (comp M N Hs g x) Hs) a b := by
  have hfwd : ∀ z, ∀ y, ReflTransGen (AStep M N Hs g) z y →
      ReflTransGen (HStep M (comp M N Hs g z) Hs) z y := by
    intro z y h
    induction h with
    | refl => exact .refl
    | tail h1 hst ih =>
      exact ih.tail ⟨mem_comp.2 ⟨hst.1, h1.tail hst⟩, hst.hStep.2⟩
  intro a ha b hb
  have haN := (mem_comp.1 ha).1
  have h1 := hfwd a x (rtg_symm_aStep hg hx (mem_comp.1 ha).2)
  rw [comp_eq_of_mem hg hx ha] at h1
  exact h1.trans (hfwd x b (mem_comp.1 hb).2)

lemma comp_rev (hB : Stable (revPerm M) N) {x y : D} (hy : y ∈ comp M N Hs g x) :
    M.rev y ∈ comp M N Hs g x :=
  comp_closed hy ⟨hB _ (mem_comp.1 hy).1, Or.inl rfl⟩

lemma comp_disjoint (hg : HClosed Hs g) {x y : D} (hx : x ∈ N) (hy : y ∈ N)
    (hne : comp M N Hs g x ≠ comp M N Hs g y) :
    Disjoint (comp M N Hs g x) (comp M N Hs g y) := by
  refine disjoint_left.2 fun z h1 h2 => hne ?_
  rw [← comp_eq_of_mem hg hx h1, comp_eq_of_mem hg hy h2]

end Comp

/-- The new hole of a separator of one vertex in a hole is that hole. -/
lemma newHole_singleton {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {H : Finset V}
    (hH : H ∈ Hs) {a : V} (ha : a ∈ H) : newHole Hs {a} = H := by
  ext v
  rw [mem_newHole]
  constructor
  · rintro (h | ⟨H', hH', hm, hv⟩)
    · rw [mem_singleton.1 h]; exact ha
    · have ha' : a ∈ H' := by
        obtain ⟨b, hb, hb'⟩ := not_disjoint_iff.1 hm
        rw [mem_singleton.1 hb'] at hb; exact hb
      by_cases e : H' = H
      · exact e ▸ hv
      · exact absurd ha (disjoint_left.1 (disjoint_of_pairwise hd hH' hH e) ha')
  · intro hv
    exact Or.inr ⟨H, hH, not_disjoint_iff.2 ⟨a, ha, mem_singleton_self _⟩, hv⟩

/-- **The certificate of a cut at a hole**: when the hole `g` of the piece map splits it into
components of weight at most `A` each, the separator is a vertex of `g` and the items are the
components. -/
theorem scert_cut {N : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    {g : Finset V} (hg : g ∈ Hs) {x₀ : D} (hx₀ : x₀ ∈ N)
    (hx₀g : M.tail x₀ ∈ g) (ex : D → ℕ) {A L : ℕ}
    (hlight : ∀ x ∈ N, wtY M ex g (comp M N Hs g x) ≤ A) (hL : 1 ≤ L) :
    SCert M N N Hs ex A L := by
  classical
  have hgc := hClosed_of_mem hd hg
  set ρ := (SPath.point (M' := M) x₀ (M.tail x₀)).toH with hρ
  have hm : ρ.mverts = {M.tail x₀} := HPath.toH_point_mverts x₀ _
  have hh : newHole Hs ρ.mverts = g := by rw [hm]; exact newHole_singleton hd hg hx₀g
  refine ⟨ρ, N.image (comp M N Hs g), ⟨fun j hj => absurd hj (Nat.not_lt_zero _),
    fun i hi j hj _ => by simp [ρ, SPath.toH, SPath.point] at hi hj; omega⟩, fun e he => ?_,
    by simp [ρ, SPath.toH, SPath.point]; omega, ⟨x₀, hx₀, rfl⟩, ?_, ?_, ?_, ?_⟩
  · simp [ρ, SPath.toH_darts, SPath.point_darts'] at he
  · intro X hX Y hY hXY
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
    obtain ⟨y, hy, rfl⟩ := mem_image.1 hY
    exact comp_disjoint hgc hx hy hXY
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
    refine ⟨fun y hy => (mem_comp.1 hy).1, fun a ha b hab => ?_⟩
    rw [hh] at hab
    exact comp_closed ha hab
  · intro d hd _
    exact ⟨comp M N Hs g d, mem_image_of_mem _ hd, self_mem_comp hd⟩
  · intro X hX
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
    rw [hh]; exact hlight x hx

lemma wtY_mono {ex ex' : D → ℕ} (h : ∀ d, ex d ≤ ex' d) (Y : Finset V) (X : Finset D) :
    wtY M ex Y X ≤ wtY M ex' Y X :=
  sum_le_sum fun d _ => by split_ifs <;> simp [h d]

/-- **Lifting a certificate through a pruning**: if the darts `N \ K`, closed under the steps
avoiding `g` (a set of vertices related by the holes: a hole, or a vertex off the holes; for
instance the components off a hole other than the heavy one `K`), of weight at most `A`, are
deleted and their weight put on a dart `a₀` of `K` leaving `g`, a certificate for `K` gives one for
`N`: the deleted darts join the item of `g`, or form an item of their own when `g` lies on the
separator. -/
theorem scert_prune {N K : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    {g : Finset V} (hgc : HClosed Hs g) (hgr : ∀ u ∈ g, ∀ v ∈ g, HRel Hs u v) (hKN : K ⊆ N)
    (hK : Stable (revPerm M) K) (hcl : ∀ a ∈ K, ∀ b, AStep M N Hs g a b → b ∈ K)
    (hRcl : ∀ a ∈ N \ K, ∀ b, AStep M N Hs g a b → b ∈ N \ K)
    {a₀ : D} (ha₀ : a₀ ∈ K) (ha₀g : M.tail a₀ ∈ g) (ex : D → ℕ) {A L : ℕ}
    (hlight : ∑ d ∈ N \ K, (1 + ex d) ≤ A)
    {Nρ : Finset D}
    (hc : SCert M K Nρ Hs (fun d => ex d + if d = a₀ then ∑ d ∈ N \ K, (1 + ex d) else 0) A L) :
    SCert M N Nρ Hs ex A L := by
  classical
  obtain ⟨ρ, I, hs, hdar, hlen, htch, hdisj, hcls, hcov, hwt⟩ := hc
  set h'' := newHole Hs ρ.mverts with hh''
  set R := N \ K with hR
  set T := ∑ d ∈ R, (1 + ex d) with hT
  set ex' : D → ℕ := fun d => ex d + if d = a₀ then T else 0 with hex'
  have hhc := hClosed_newHole hd hs
  have hexle : ∀ d, ex d ≤ ex' d := fun d => by simp only [ex']; omega
  -- a step from `K` to the deleted darts pivots at `g`
  have hF1 : ∀ a ∈ K, ∀ b ∈ R, AStep M N Hs h'' a b → M.tail a ∈ g ∧ M.tail a ∉ h'' := by
    intro a ha b hb hab
    rcases hab.2 with e | ⟨e, hah⟩
    · exact absurd (e ▸ hK a ha) (mem_sdiff.1 hb).2
    · refine ⟨?_, hah⟩
      by_contra hag
      exact (mem_sdiff.1 hb).2 (hcl a ha b ⟨hab.1, Or.inr ⟨e, hag⟩⟩)
  have hKstep : ∀ a b, b ∈ K → AStep M N Hs h'' a b → AStep M K Hs h'' a b :=
    fun a b hb hab => ⟨hb, hab.2⟩
  have hRK : Disjoint R K := disjoint_sdiff_self_left
  by_cases hgh : M.tail a₀ ∈ h''
  · -- the hole `g` is on the separator: the deleted darts form an item
    have hgsub : ∀ v ∈ g, v ∈ h'' := fun v hv => hhc _ hgh _ (hgr _ ha₀g v hv)
    refine ⟨ρ, insert R I, hs, hdar, hlen, htch, ?_, ?_, ?_, ?_⟩
    · intro X hX Y hY hXY
      rcases mem_insert.1 hX with rfl | hX <;> rcases mem_insert.1 hY with rfl | hY
      · exact absurd rfl hXY
      · exact disjoint_of_subset_right (hcls Y hY).1 hRK
      · exact (disjoint_of_subset_right (hcls X hX).1 hRK).symm
      · exact hdisj X hX Y hY hXY
    · intro X hX
      rcases mem_insert.1 hX with rfl | hX
      · refine ⟨sdiff_subset, fun a ha b hab => ?_⟩
        rcases hab.2 with e | ⟨e, hah⟩
        · exact hRcl a ha b ⟨hab.1, Or.inl e⟩
        · exact hRcl a ha b ⟨hab.1, Or.inr ⟨e, fun h => hah (hgsub _ h)⟩⟩
      · refine ⟨(hcls X hX).1.trans hKN, fun a ha b hab => ?_⟩
        have haK := (hcls X hX).1 ha
        by_cases hbK : b ∈ K
        · exact (hcls X hX).2 a ha b (hKstep a b hbK hab)
        · have := hF1 a haK b (mem_sdiff.2 ⟨hab.1, hbK⟩) hab
          exact absurd (hgsub _ this.1) this.2
    · intro d hdN hnot
      by_cases hdK : d ∈ K
      · obtain ⟨X, hX, hdX⟩ := hcov d hdK hnot
        exact ⟨X, mem_insert_of_mem hX, hdX⟩
      · exact ⟨R, mem_insert_self _ _, mem_sdiff.2 ⟨hdN, hdK⟩⟩
    · intro X hX
      rcases mem_insert.1 hX with rfl | hX
      · exact (wtY_le ex h'' _).trans hlight
      · exact (wtY_mono hexle h'' X).trans (hwt X hX)
  · -- the deleted darts join the item of `g`
    have hgoff : ∀ v ∈ g, v ∉ h'' := fun v hv h =>
      hgh (hhc _ h _ (hgr v hv _ ha₀g))
    obtain ⟨X₀, hX₀, ha₀X⟩ := hcov a₀ ha₀ fun h => hgh h.1
    have hF3 : ∀ a ∈ K, M.tail a ∈ g → a ∈ X₀ := fun a ha hag =>
      (hcls X₀ hX₀).2 a₀ ha₀X a ⟨ha, Or.inr ⟨hgr _ ha₀g _ hag, hgh⟩⟩
    have hXX : ∀ X ∈ I, X ≠ X₀ → ∀ a ∈ X, M.tail a ∉ g := fun X hX hne a ha hag =>
      disjoint_left.1 (hdisj X hX X₀ hX₀ hne) ha (hF3 a ((hcls X hX).1 ha) hag)
    refine ⟨ρ, insert (X₀ ∪ R) (I.erase X₀), hs, hdar, hlen, htch, ?_, ?_, ?_, ?_⟩
    · intro X hX Y hY hXY
      have hside : ∀ Z ∈ I.erase X₀, Disjoint (X₀ ∪ R) Z := fun Z hZ => by
        obtain ⟨hZ0, hZ⟩ := mem_erase.1 hZ
        exact disjoint_union_left.2 ⟨(hdisj Z hZ X₀ hX₀ hZ0).symm,
          disjoint_of_subset_right (hcls Z hZ).1 hRK⟩
      rcases mem_insert.1 hX with rfl | hX <;> rcases mem_insert.1 hY with rfl | hY
      · exact absurd rfl hXY
      · exact hside Y hY
      · exact (hside X hX).symm
      · exact hdisj X (mem_erase.1 hX).2 Y (mem_erase.1 hY).2 hXY
    · intro X hX
      rcases mem_insert.1 hX with rfl | hX
      · refine ⟨union_subset ((hcls X₀ hX₀).1.trans hKN) sdiff_subset, fun a ha b hab => ?_⟩
        by_cases hbK : b ∈ K
        · rcases mem_union.1 ha with ha | ha
          · exact mem_union_left _ ((hcls X₀ hX₀).2 a ha b (hKstep a b hbK hab))
          · -- from the deleted darts into `K`: the pivot is in `g`
            rcases hab.2 with e | ⟨e, hah⟩
            · exact absurd hbK (mem_sdiff.1 (hRcl a ha b ⟨hab.1, Or.inl e⟩)).2
            · by_cases hag : M.tail a ∈ g
              · exact mem_union_left _ (hF3 b hbK (hgc _ hag _ e))
              · exact absurd hbK (mem_sdiff.1 (hRcl a ha b ⟨hab.1, Or.inr ⟨e, hag⟩⟩)).2
        · exact mem_union_right _ (mem_sdiff.2 ⟨hab.1, hbK⟩)
      · obtain ⟨hX0, hX⟩ := mem_erase.1 hX
        refine ⟨(hcls X hX).1.trans hKN, fun a ha b hab => ?_⟩
        by_cases hbK : b ∈ K
        · exact (hcls X hX).2 a ha b (hKstep a b hbK hab)
        · exact absurd (hF1 a ((hcls X hX).1 ha) b (mem_sdiff.2 ⟨hab.1, hbK⟩) hab).1
            (hXX X hX hX0 a ha)
    · intro d hdN hnot
      by_cases hdK : d ∈ K
      · obtain ⟨X, hX, hdX⟩ := hcov d hdK hnot
        by_cases e : X = X₀
        · exact ⟨X₀ ∪ R, mem_insert_self _ _, mem_union_left _ (e ▸ hdX)⟩
        · exact ⟨X, mem_insert_of_mem (mem_erase.2 ⟨e, hX⟩), hdX⟩
      · exact ⟨X₀ ∪ R, mem_insert_self _ _, mem_union_right _ (mem_sdiff.2 ⟨hdN, hdK⟩)⟩
    · intro X hX
      rcases mem_insert.1 hX with rfl | hX
      · have hdis : Disjoint X₀ R := (disjoint_of_subset_left (hcls X₀ hX₀).1 hRK.symm)
        rw [wtY, sum_union hdis, ← wtY, ← wtY]
        have h1 : wtY M ex' h'' X₀ = wtY M ex h'' X₀ + T := by
          simp only [wtY, ex']
          rw [show (∑ d ∈ X₀, (1 + if M.tail d ∈ h'' then 0 else ex d + if d = a₀ then T else 0))
              = ∑ d ∈ X₀, ((1 + if M.tail d ∈ h'' then 0 else ex d) +
                if d = a₀ then T else 0) from sum_congr rfl fun d hd => by
                  split_ifs with h1 h2 <;> simp_all <;> omega]
          rw [sum_add_distrib, sum_ite_eq' X₀ a₀]; simp [ha₀X]
        have h2 := wtY_le (M := M) ex h'' R
        have h3 : wtY M ex' h'' X₀ ≤ A := hwt X₀ hX₀
        show wtY M ex h'' X₀ + wtY M ex h'' R ≤ A
        omega
      · exact (wtY_mono hexle h'' X).trans (hwt X (mem_erase.1 hX).2)

lemma SCert.mono {N Nρ : Finset D} {Hs : List (Finset V)} {ex : D → ℕ} {A L L' : ℕ}
    (h : SCert M N Nρ Hs ex A L) (hL : L ≤ L') : SCert M N Nρ Hs ex A L' := by
  obtain ⟨ρ, I, h1, h2, h3, h4⟩ := h
  exact ⟨ρ, I, h1, h2, h3.trans hL, h4⟩

lemma SCert.mono_ρ {N Nρ Nρ' : Finset D} {Hs : List (Finset V)} {ex : D → ℕ} {A L : ℕ}
    (h : SCert M N Nρ Hs ex A L) (hN : Nρ ⊆ Nρ') : SCert M N Nρ' Hs ex A L := by
  obtain ⟨ρ, I, h1, h2, h3, ⟨x, hx, e⟩, h4⟩ := h
  exact ⟨ρ, I, h1, fun e he => hN (h2 e he), h3, ⟨x, hN hx, e⟩, h4⟩

/-- A connected set of darts leaving a set closed under the steps avoiding `g` leaves it at a dart
leaving `g`. -/
lemma exists_exit {N S : Finset D} {Hs : List (Finset V)} {g : Finset V}
    (hS : ∀ a ∈ S, ∀ b, AStep M N Hs g a b → b ∈ S) {x y : D} (hx : x ∈ S) (hy : y ∉ S)
    (h : ReflTransGen (HStep M N Hs) x y) : ∃ a ∈ S, M.tail a ∈ g := by
  have key : ∀ z, ReflTransGen (HStep M N Hs) x z → z ∈ S ∨ ∃ a ∈ S, M.tail a ∈ g := by
    intro z hz
    induction hz with
    | refl => exact Or.inl hx
    | tail _ hst ih =>
      rename_i c d _
      rcases ih with hc | h
      · rcases hst.2 with e | e
        · exact Or.inl (hS c hc d ⟨hst.1, Or.inl e⟩)
        · by_cases hcg : M.tail c ∈ g
          · exact Or.inr ⟨c, hc, hcg⟩
          · exact Or.inl (hS c hc d ⟨hst.1, Or.inr ⟨e, hcg⟩⟩)
      · exact Or.inr h
  rcases key y h with h | h
  · exact absurd h hy
  · exact h

/-- **Balanced splits of piece maps exist**: every nonempty piece map (`PMap`) on a map without
loops, with extra weights `ex` on its darts of total weight (one per dart plus the extra weights)
at most `W ≤ 2 A`, has a certificate of a split into items of weight at most `A`, along a path
through at most `6 √(2 n) + 4` vertices (`n` darts), when `2 W + 2 + 9 (6 √(2 n) + 4) ≤ 3 A`.
If a hole is a cut vertex with a heavy component (weight more than `W - A`), the other
components are deleted and their weight put on the hole (`scert_prune`); if a hole is a cut
vertex with no heavy component, the split is at the hole (`scert_cut`); if no hole is a cut
vertex, the split is by Miller's theorem (`scert_core`). -/
theorem exists_scert {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    (hloopM : ∀ d, M.head d ≠ M.tail d) {A W : ℕ} (hAW : W ≤ 2 * A) :
    ∀ (n : ℕ) (N : Finset D) (τ : Perm D) (ex : D → ℕ), N.card = n → PMap M N Hs τ →
      N.Nonempty → ∑ d ∈ N, (1 + ex d) ≤ W → 2 * W + 2 + 9 * (6 * Nat.sqrt (2 * n) + 4) ≤ 3 * A →
      SCert M N N Hs ex A (6 * Nat.sqrt (2 * n) + 4) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N τ ex hn hN hne hW hA
  have hAW' := hAW
  obtain ⟨x₀, hx₀⟩ := hne
  by_cases hnc : NoCut M N Hs
  · subst hn
    exact scert_core hd hloopM hN hx₀ hnc ex (by omega)
  simp only [NoCut, not_forall] at hnc
  obtain ⟨g, hg, x, hx, y, hy, hxg, hyg, hxy⟩ := hnc
  have hgc := hClosed_of_mem hd hg
  have hxyc : y ∉ comp M N Hs g x := fun h => hxy (mem_comp.1 h).2
  obtain ⟨a₁, ha₁, ha₁g⟩ := exists_exit (S := comp M N Hs g x)
    (fun a ha b hab => comp_closed ha hab) (self_mem_comp hx) hxyc (hN.conn x hx y hy)
  have ha₁N := (mem_comp.1 ha₁).1
  by_cases hheavy : ∃ z ∈ N, W < A + ∑ d ∈ comp M N Hs g z, (1 + ex d)
  · obtain ⟨z, hz, hzh⟩ := hheavy
    set K := comp M N Hs g z with hK
    have hKN : K ⊆ N := fun d hd => (mem_comp.1 hd).1
    have hKlt : K.card < N.card := by
      refine card_lt_card ⟨hKN, fun hNK => ?_⟩
      have hxK := hNK hx
      have hyK := hNK hy
      rw [hK] at hxK hyK
      have := comp_eq_of_mem hgc hz hxK
      rw [← this] at hyK
      exact hxyc hyK
    obtain ⟨w, hwN, hwK⟩ : ∃ w ∈ N, w ∉ K := by
      by_contra h; push Not at h; exact absurd (card_le_card h) (by omega)
    obtain ⟨a₀, ha₀, ha₀g⟩ := exists_exit (S := K) (fun a ha b hab => comp_closed ha hab)
      (self_mem_comp hz) hwK (hN.conn z hz w hwN)
    have hKr : Stable (revPerm M) K := fun d hd => comp_rev hN.rev hd
    have hKp : PMap M K Hs (ret τ K) := PMap.del hd hN hg hKN hKr
      (fun a ha b hab => comp_closed ha hab) (comp_conn hgc hz)
    set T := ∑ d ∈ N \ K, (1 + ex d) with hT
    have hsplit : ∑ d ∈ N, (1 + ex d) = ∑ d ∈ K, (1 + ex d) + T := by
      rw [hT, ← sum_union disjoint_sdiff, union_sdiff_of_subset hKN]
    have hlight : T ≤ A := by omega
    have hsumK : ∑ d ∈ K, (1 + (ex d + if d = a₀ then T else 0)) ≤ W := by
      have : ∑ d ∈ K, (1 + (ex d + if d = a₀ then T else 0)) =
          ∑ d ∈ K, (1 + ex d) + T := by
        rw [show (∑ d ∈ K, (1 + (ex d + if d = a₀ then T else 0))) =
          ∑ d ∈ K, ((1 + ex d) + if d = a₀ then T else 0) from
            sum_congr rfl fun d _ => by ring, sum_add_distrib, sum_ite_eq' K a₀]
        simp [ha₀]
      omega
    have hsq : Nat.sqrt (2 * K.card) ≤ Nat.sqrt (2 * n) := Nat.sqrt_le_sqrt (by omega)
    have hc := ih K.card (by omega) K (ret τ K) (fun d => ex d + if d = a₀ then T else 0) rfl hKp
      ⟨z, self_mem_comp hz⟩ hsumK (by omega)
    have hRcl : ∀ a ∈ N \ K, ∀ b, AStep M N Hs g a b → b ∈ N \ K := by
      intro a ha b hab
      refine mem_sdiff.2 ⟨hab.1, fun hbK => (mem_sdiff.1 ha).2 ?_⟩
      have := comp_closed hbK (hab.symm hgc (mem_sdiff.1 ha).1)
      exact this
    exact (scert_prune hd hgc (fun u hu v hv => Or.inr ⟨g, hg, hu, hv⟩) hKN hKr
      (fun a ha b hab => comp_closed ha hab) hRcl ha₀ ha₀g ex hlight hc).mono (by omega)
      |>.mono_ρ hKN
  · push Not at hheavy
    exact scert_cut hd hg ha₁N ha₁g ex (fun z hz => (wtY_le ex g _).trans (by
      have := hheavy z hz; omega)) (by omega)

end BKMNW

end PlanarFlow
