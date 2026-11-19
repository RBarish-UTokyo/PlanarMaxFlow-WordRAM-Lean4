module

public import PlanarFlow.BKMNW.ExistCert
public import PlanarFlow.BKMNW.ExistMillerD

/-!
# The certificate of a core piece map from a given separator

* `PlanarFlow.BKMNW.SCertOf`: the body of `SCert` for a named path `ρ` and named items `I`
  (`SCertOf.scert`).
* **`PlanarFlow.BKMNW.scert_core'`**: `scert_core` for the explicit path `corePath C` and the two
  explicit items `sideItem (coreI C Z)`, `sideItem (coreO C Z)`, from any separator `(C, Z)` of the
  stellar subdivision of the piece map meeting the natural weight bounds of `exists_core_cycle'`
  (weights `1` on the darts, `coreExW ex` on the vertices).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation CombMap PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- **The certificate `SCert` for a named path `ρ` and named items `I`.** -/
def SCertOf (N Nρ : Finset D) (Hs : List (Finset V)) (ex : D → ℕ) (A L : ℕ) (ρ : HPath M)
    (I : Finset (Finset D)) : Prop :=
  ρ.Simple Hs ∧ (∀ e ∈ ρ.darts, e ∈ Nρ) ∧ ρ.k + 1 ≤ L ∧ (∃ x ∈ Nρ, M.tail x = ρ.p ρ.k) ∧
    (∀ X ∈ I, ∀ Y ∈ I, X ≠ Y → Disjoint X Y) ∧
    (∀ X ∈ I, X ⊆ N ∧ ∀ a ∈ X, ∀ b, AStep M N Hs (newHole Hs ρ.mverts) a b → b ∈ X) ∧
    (∀ d ∈ N, ¬ (M.tail d ∈ newHole Hs ρ.mverts ∧ M.head d ∈ newHole Hs ρ.mverts) →
      ∃ X ∈ I, d ∈ X) ∧
    (∀ X ∈ I, wtY M ex (newHole Hs ρ.mverts) X ≤ A)

lemma SCertOf.scert {N Nρ : Finset D} {Hs : List (Finset V)} {ex : D → ℕ} {A L : ℕ}
    {ρ : HPath M} {I : Finset (Finset D)} (h : SCertOf M N Nρ Hs ex A L ρ I) :
    SCert M N Nρ Hs ex A L := ⟨ρ, I, h⟩

lemma scert_iff {N Nρ : Finset D} {Hs : List (Finset V)} {ex : D → ℕ} {A L : ℕ} :
    SCert M N Nρ Hs ex A L ↔ ∃ ρ I, SCertOf M N Nρ Hs ex A L ρ I := Iff.rfl

open Classical in
/-- The extra weight on a vertex of the piece map: the extra weights of its darts. -/
noncomputable def coreExW (τ : Perm D) (N : Finset D) (ex : D → ℕ) (q : SVert τ N) : ℕ :=
  ∑ x : SDart N with Quotient.mk _ x = q, ex x.1

open Classical PlanarSeparator.Map in
/-- **The certificate of a piece map whose holes are not cut vertices, from a given separator**
`(C, Z)` of the stellar subdivision of the piece map (the hypotheses of `exists_core_cycle'` with
weights `1` on the darts and `coreExW ex` on the vertices): the path is `corePath C`, the two
items the darts with an end in `coreI C Z`, in `coreO C Z`. -/
theorem scert_core' {N : Finset D} {Hs : List (Finset V)} {τ : Perm D} (hd : Hs.Pairwise Disjoint)
    (hloopM : ∀ d, M.head d ≠ M.tail d) (hN : PMap M N Hs τ) {x₀ : D} (hx₀ : x₀ ∈ N)
    (hnc : NoCut M N Hs) (ex : D → ℕ) {A : ℕ}
    (hA : 2 * (∑ d ∈ N, (1 + ex d)) + 2 + 9 * (6 * Nat.sqrt (2 * N.card) + 4) ≤ 3 * A)
    (C : (psep M hN.stable hN.rev).stellar.SCycle) (Z : Finset (psep M hN.stable hN.rev).stellar.Face)
    (hk : C.k ≤ 6 * Nat.sqrt (Fintype.card (SVert τ N) +
      Fintype.card (psep M hN.stable hN.rev).Face) + 4)
    (hsep : IsCycleSep C Z (sideIn C Z) (sideOut C Z))
    (hin : 3 * ∑ y ∈ sideIn C Z, coreWt hN.stable hN.rev (fun _ => 1)
        (coreExW τ N ex) y ≤
      2 * (∑ _x : SDart N, 1 + ∑ q, coreExW τ N ex q) + 2)
    (hout : 3 * ∑ y ∈ sideOut C Z, coreWt hN.stable hN.rev (fun _ => 1)
        (coreExW τ N ex) y ≤
      2 * (∑ _x : SDart N, 1 + ∑ q, coreExW τ N ex q) + 2) :
    SCertOf M N N Hs ex A (6 * Nat.sqrt (2 * N.card) + 4) (corePath hN.stable hN.rev C)
      {sideItem hN.stable hN.rev (coreI hN.stable hN.rev C Z),
        sideItem hN.stable hN.rev (coreO hN.stable hN.rev C Z)} := by
  have hσ := hN.stable
  have hB := hN.rev
  have hsmall := hN.small_of_noCut hd hloopM hx₀ hnc
  have hloop : ∀ x ∈ N, ¬ HRel Hs (M.head x) (M.tail x) := by
    rintro x hx (e | ⟨H, hH, h1, h2⟩)
    · exact hloopM x e
    · exact hN.inner x hx ⟨H, hH, h2, h1⟩
  obtain ⟨hsim, hdar, hlen, htouch, hIO, hon, hoff, hIO', hOI', hwI, hwO⟩ :=
    exists_core_cycle' hσ hB hN.vert hloop hsmall (fun _ => 1) (fun _ => le_rfl)
      (coreExW τ N ex) C Z hk hsep hin hout
  simp only [coreExW] at hwI hwO
  set ρ := corePath hσ hB C with hρ
  set I := coreI hσ hB C Z with hI
  set O := coreO hσ hB C Z with hO
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
  refine ⟨hsim, hdar, hlen, htouch ρ.k le_rfl, ?_, ?_, ?_, ?_⟩
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

end BKMNW

end PlanarFlow
