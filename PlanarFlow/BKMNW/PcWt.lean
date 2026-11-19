module

public import PlanarFlow.BKMNW.ExistOracleD

/-!
# The total weight of the certificate of a large piece

**`pcW_total`**: the weights `ex = pcExf + lmoved (pcExf) (pcLs)` of `pcertD` on the piece map
of the core `B₀` have total `∑_{d ∈ B₀} (1 + ex d) ≤ #P + K · nTouch` (the bound used inside
`pcert_of_core'`, stated on its own: the program of stage 5 uses `W₀ = #P + K nTouch` as the
bound `T₀` of `scProgT_execK`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation CombMap PlanarSeparator

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

open Classical in
/-- **The total weight of the certificate of a piece** (from the proof of `pcert_of_core'`). -/
theorem pcW_total {S T Q : Finset V}
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) (hne : (pdarts M (core M Q P) Hs).Nonempty)
    (K : ℕ) (pc : PcChoice D V) (hpc : pc.OK M Q P Hs) :
    ∑ d ∈ pdarts M (core M Q P) Hs, (1 + (pcExf M pc Q P Hs K d +
      lmoved (pcExf M pc Q P Hs K) (pcLs M pc Q P Hs) d)) ≤ P.card + K * nTouch M P Hs := by
  have hd := hP.disj
  have hHQ := hI.1
  set B₀ := pdarts M (core M Q P) Hs with hB₀
  obtain ⟨b₀, hb₀⟩ := hne
  have hQn : ∀ q ∈ Q, q ∉ hunion Hs := fun q hq h => disjoint_left.1 hHQ h hq
  have hB₀P : B₀ ⊆ P := fun d hd => (mem_core.1 (mem_pdarts.1 hd).1).1
  have hB₀Q : ∀ d ∈ B₀, M.tail d ∉ Q ∧ M.head d ∉ Q := fun d hd =>
    (mem_core.1 (mem_pdarts.1 hd).1).2
  -- the darts inside holes not touched by the core
  set Dg := P.filter fun d => Inner M Hs d ∧ ∀ b ∈ B₀, ¬ HRel Hs (M.tail b) (M.tail d) with hDg
  set Nf := P \ Dg with hNf
  have hB₀Nf : B₀ ⊆ Nf := fun d hd => mem_sdiff.2 ⟨hB₀P hd, fun h =>
    (mem_pdarts.1 hd).2 (mem_filter.1 h).2.1⟩
  -- the anchor vertex of a dart off the core
  set av : D → V := fun d => if M.tail d ∈ Q then M.head d else M.tail d with hav
  have hanc : ∀ d ∈ Nf \ B₀, M.tail d ∉ Q → ∃ b ∈ B₀, HRel Hs (M.tail b) (M.tail d) := by
    intro d hd htQ
    obtain ⟨hdNf, hdB⟩ := mem_sdiff.1 hd
    obtain ⟨hdP, hdD⟩ := mem_sdiff.1 hdNf
    by_cases hhQ : M.head d ∈ Q
    · exact exists_core_anchor hQdeg hP hHQ hb₀ hdP hhQ htQ
    · have hinner : Inner M Hs d := by
        by_contra h
        exact hdB (mem_pdarts.2 ⟨mem_core.2 ⟨hdP, htQ, hhQ⟩, h⟩)
      by_contra hno
      push Not at hno
      exact hdD (mem_filter.2 ⟨hdP, hinner, hno⟩)
  have hanc' : ∀ d ∈ Nf \ B₀, ∃ b ∈ B₀, HRel Hs (M.tail b) (av d) := by
    intro d hd
    by_cases htQ : M.tail d ∈ Q
    · have hrd : M.rev d ∈ Nf \ B₀ := by
        obtain ⟨hdNf, hdB⟩ := mem_sdiff.1 hd
        obtain ⟨hdP, hdD⟩ := mem_sdiff.1 hdNf
        refine mem_sdiff.2 ⟨mem_sdiff.2 ⟨hP.rev _ hdP, fun h => ?_⟩, fun h => ?_⟩
        · obtain ⟨H, hH, -, h2⟩ := (mem_filter.1 h).2.1
          rw [CombMap.head_rev] at h2
          exact hQn _ htQ (subset_hunion hH h2)
        · exact (hB₀Q _ h).2 (by rw [CombMap.head_rev]; exact htQ)
      have := hanc _ hrd (by rw [CombMap.tail_rev]; exact fun h => hQ5 d ⟨htQ, h⟩)
      simpa [av, htQ] using this
    · simpa [av, htQ] using hanc d hd htQ
  have havQ : ∀ d, av d ∉ Q := by
    intro d
    by_cases htQ : M.tail d ∈ Q
    · show (if M.tail d ∈ Q then M.head d else M.tail d) ∉ Q
      simp only [htQ, ↓reduceIte]; exact fun h => hQ5 d ⟨htQ, h⟩
    · show (if M.tail d ∈ Q then M.head d else M.tail d) ∉ Q
      simp only [htQ, ↓reduceIte]; exact not_false
  have hrevNf : ∀ d ∈ Nf \ B₀, M.rev d ∈ Nf \ B₀ := by
    intro d hdm
    obtain ⟨hdNf, hdB⟩ := mem_sdiff.1 hdm
    obtain ⟨hdP, hdD⟩ := mem_sdiff.1 hdNf
    refine mem_sdiff.2 ⟨mem_sdiff.2 ⟨hP.rev _ hdP, fun h => hdD ?_⟩, fun h => hdB ?_⟩
    · obtain ⟨-, h1, h2⟩ := mem_filter.1 h
      have hdi : Inner M Hs d := inner_rev.1 h1
      refine mem_filter.2 ⟨hdP, hdi, fun b hb hr => h2 b hb ?_⟩
      obtain ⟨H, hH, ht, hh⟩ := hdi
      rw [CombMap.tail_rev]
      exact hRel_trans' hd hr (Or.inr ⟨H, hH, ht, hh⟩)
    · have := stable_pdarts (revClosed_core hP.rev) Hs _ h
      rw [revPerm_apply, M.rev_rev] at this; exact this
  -- the pairs of darts off the core
  set Es := (Nf \ B₀).image fun d => ({d, M.rev d} : Finset D) with hEs
  have hEsrep : ∀ E ∈ Es, ∃ d ∈ Nf \ B₀, E = {d, M.rev d} := fun E hE => by
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hE; exact ⟨d, hd, rfl⟩
  set rep : Finset D → D := pc.rep with hrepdef
  have hrep : ∀ E ∈ Es, rep E ∈ Nf \ B₀ := by
    intro E hE
    obtain ⟨d, hd', rfl⟩ := mem_image.1 hE
    rcases hpc.rep d with h | h
    · rw [hrepdef, h]; exact hd'
    · rw [hrepdef, h]; exact hrevNf d hd'
  have hrepE : ∀ E ∈ Es, E = {rep E, M.rev (rep E)} := by
    intro E hE
    obtain ⟨d, -, rfl⟩ := mem_image.1 hE
    rcases hpc.rep d with h | h
    · rw [hrepdef, h]
    · rw [hrepdef, h, M.rev_rev, pair_comm]
  set anc : Finset D → D := fun E => pc.ancD P Hs (rep E) with hancdef
  have hancB : ∀ E ∈ Es, anc E ∈ B₀ := fun E hE =>
    (hpc.anc (rep E) (hanc' (rep E) (hrep E hE))).1
  have hancR : ∀ E ∈ Es, HRel Hs (M.tail (anc E)) (av (rep E)) := fun E hE =>
    (hpc.anc (rep E) (hanc' (rep E) (hrep E hE))).2
  have hlE := hpc.ord Es
  set Ls : List (Finset D × Finset V × D) :=
    (pc.ord Es).map fun E => (E, cls Hs (av (rep E)), anc E) with hLs
  -- the anchors of the holes
  set anch : Finset V → D := pc.anch P Hs with hanch
  have hhAspec : ∀ H, (∃ b ∈ B₀, M.tail b ∈ H) → anch H ∈ B₀ ∧ M.tail (anch H) ∈ H :=
    fun H h => hpc.anch H h
  set exf : D → ℕ := fun d => if d ∈ B₀ ∧ ∃ H ∈ Hs, M.tail d ∈ H ∧ anch H = d then K else 0
    with hexf
  have hexf0 : ∀ d, d ∉ B₀ → exf d = 0 := fun d hd => by simp [exf, hd]
  -- the attached sets
  have hmemLs : ∀ e ∈ Ls, ∃ E ∈ Es, e = (E, cls Hs (av (rep E)), anc E) := fun e he => by
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 he
    exact ⟨E, hlE.2 ▸ List.mem_toFinset.2 hE, rfl⟩
  have hEdisj : ∀ E ∈ Es, Disjoint E B₀ := by
    intro E hE
    rw [hrepE E hE]
    have h1 := hrep E hE
    have h2 := hrevNf _ h1
    refine disjoint_left.2 fun x hx hxB => ?_
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact (mem_sdiff.1 h1).2 hxB
    · exact (mem_sdiff.1 h2).2 hxB
  have hEw : ∀ E ∈ Es, ∑ d ∈ E, (1 + exf d) = E.card := fun E hE => by
    rw [card_eq_sum_ones]
    exact sum_congr rfl fun d hdE => by
      rw [hexf0 d (disjoint_left.1 (hEdisj E hE) hdE)]
  have hEsdisj : ∀ E ∈ Es, ∀ E' ∈ Es, E ≠ E' → Disjoint E E' := by
    intro E hE E' hE' hne
    refine disjoint_left.2 fun x hx hx' => hne ?_
    rw [hrepE E hE] at hx ⊢
    rw [hrepE E' hE'] at hx' ⊢
    simp only [mem_insert, mem_singleton] at hx hx'
    ext y
    simp only [mem_insert, mem_singleton]
    rcases hx with rfl | rfl <;> rcases hx' with h | h
    · rw [h]
    · rw [h, M.rev_rev]; tauto
    · rw [← h, M.rev_rev]; tauto
    · have := congrArg M.rev h; rw [M.rev_rev, M.rev_rev] at this; rw [this]
  have hpw : Ls.Pairwise fun e e' => Disjoint e.1 e'.1 := by
    rw [hLs, List.pairwise_map]
    exact hlE.1.pairwise_of_forall_ne fun E hE E' hE' hne =>
      hEsdisj E (hlE.2 ▸ List.mem_toFinset.2 hE) E' (hlE.2 ▸ List.mem_toFinset.2 hE') hne
  have hlun : B₀ ∪ lunion Ls = Nf := by
    ext x
    rw [mem_union, mem_lunion]
    constructor
    · rintro (h | ⟨e, he, hx⟩)
      · exact hB₀Nf h
      · obtain ⟨E, hE, rfl⟩ := hmemLs e he
        rw [hrepE E hE] at hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (mem_sdiff.1 (hrep E hE)).1
        · exact (mem_sdiff.1 (hrevNf _ (hrep E hE))).1
    · intro hx
      by_cases hxB : x ∈ B₀
      · exact Or.inl hxB
      · right
        have hxE : ({x, M.rev x} : Finset D) ∈ Es := mem_image_of_mem _ (mem_sdiff.2 ⟨hx, hxB⟩)
        exact ⟨_, List.mem_map.2 ⟨_, List.mem_toFinset.1 (hlE.2.symm ▸ hxE), rfl⟩, by simp⟩
  -- the total weight
  set W := P.card + K * nTouch M P Hs with hW
  have hsumEs : ∑ E ∈ Es, E.card ≤ (Nf \ B₀).card := by
    rw [← card_biUnion hEsdisj]
    refine card_le_card fun x hx => ?_
    obtain ⟨E, hE, hxE⟩ := mem_biUnion.1 hx
    rw [hrepE E hE] at hxE
    simp only [mem_insert, mem_singleton] at hxE
    rcases hxE with rfl | rfl
    · exact hrep E hE
    · exact hrevNf _ (hrep E hE)
  have hmoved : ∑ d ∈ B₀, lmoved exf Ls d ≤ (Nf \ B₀).card := by
    have e1 : ∀ d, lmoved exf Ls d =
        ∑ E ∈ Es, if d = anc E then ∑ x ∈ E, (1 + exf x) else 0 := fun d => by
      simp only [lmoved, hLs, List.map_map]
      rw [show (∑ E ∈ Es, if d = anc E then ∑ x ∈ E, (1 + exf x) else 0) =
          ((pc.ord Es).map fun E => if d = anc E then ∑ x ∈ E, (1 + exf x) else 0).sum from by
        conv_lhs => rw [← hlE.2]
        exact List.sum_toFinset _ hlE.1]
      rfl
    simp_rw [e1]
    rw [sum_comm]
    refine le_trans (sum_le_sum fun E hE => ?_) hsumEs
    rw [sum_ite_eq' B₀ (anc E)]
    simp only [hancB E hE, ↓reduceIte]
    rw [hEw E hE]
  have hexfsum : ∑ d ∈ B₀, exf d ≤ K * nTouch M P Hs := by
    set Bk := B₀.filter fun d => ∃ H ∈ Hs, M.tail d ∈ H ∧ anch H = d
    have h1 : ∑ d ∈ B₀, exf d = K * Bk.card := by
      rw [card_eq_sum_ones, mul_sum, mul_one, sum_filter]
      exact sum_congr rfl fun d hdB => by simp [exf, hdB]
    rw [h1]
    refine Nat.mul_le_mul_left _ ?_
    have hinj : Set.InjOn (fun d => cls Hs (M.tail d)) (Bk : Set D) := by
      intro x hx y hy e
      obtain ⟨-, H, hH, hxH, rfl⟩ := mem_filter.1 hx
      obtain ⟨-, H', hH', hyH', rfl⟩ := mem_filter.1 hy
      simp only at e
      rw [cls_of_mem hd hH hxH, cls_of_mem hd hH' hyH'] at e
      rw [e]
    rw [← card_image_of_injOn hinj]
    unfold nTouch
    refine (card_le_card fun H hH => ?_).trans (List.toFinset_card_le _)
    obtain ⟨d, hd', rfl⟩ := mem_image.1 hH
    obtain ⟨hdB, H, hH, hdH, -⟩ := mem_filter.1 hd'
    rw [List.mem_toFinset, List.mem_filter, cls_of_mem hd hH hdH]
    exact ⟨hH, by simpa using ⟨M.tail d, hdH, d, hB₀P hdB, rfl⟩⟩
  have htot : ∑ d ∈ B₀, (1 + (exf d + lmoved exf Ls d)) ≤ W := by
    rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul, mul_one]
    have hNfcard : B₀.card + (Nf \ B₀).card ≤ P.card := by
      rw [← card_union_of_disjoint disjoint_sdiff, union_sdiff_of_subset hB₀Nf]
      exact card_le_card sdiff_subset
    omega
  exact htot

end BKMNW

end PlanarFlow
