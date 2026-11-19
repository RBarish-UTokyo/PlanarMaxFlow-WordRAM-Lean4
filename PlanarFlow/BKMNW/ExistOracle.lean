module

public import PlanarFlow.BKMNW.ExistSplit

/-!
# The split of a large piece: the certificate of the whole piece

A certificate `PCert` of a piece: a short simple path through the holes along darts of its core,
and items of weight `hw` (darts, and `K` per hole off the path) at most `A`, closed under the
steps off the new hole and covering the darts of the piece map with an end off the new hole.

* `pcert_of_core`: the certificate of a piece with a nonempty core, from Miller's theorem on the
  core (`exists_scert`) with the pendant edges and darts inside holes attached.
* `pcert_of_empty`: the certificate of a piece with an empty core (only pendant edges).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

lemma mem_cls_iff {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {v w : V} :
    w ∈ cls Hs v ↔ HRel Hs v w := by
  by_cases hv : v ∈ hunion Hs
  · obtain ⟨H, hH, hvH⟩ := mem_hunion.1 hv
    rw [cls_of_mem hd hH hvH]
    exact ⟨fun hw => Or.inr ⟨H, hH, hvH, hw⟩, fun h => hClosed_of_mem hd hH v hvH w h⟩
  · rw [cls_of_not_mem hv, mem_singleton]
    exact ⟨by rintro rfl; exact Or.inl rfl, fun h => hRel_eq_of_not_mem hv (hRel_symm h)⟩

lemma hClosed_cls {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) (v : V) :
    HClosed Hs (cls Hs v) := fun a ha b hab =>
  (mem_cls_iff hd).2 (hRel_trans' hd ((mem_cls_iff hd).1 ha) hab)

lemma hRel_of_mem_cls {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) (v : V) :
    ∀ a ∈ cls Hs v, ∀ b ∈ cls Hs v, HRel Hs a b := fun a ha b hb =>
  hRel_trans' hd (hRel_symm ((mem_cls_iff hd).1 ha)) ((mem_cls_iff hd).1 hb)

/-- The piece map of the core of a piece meeting `CInv`. -/
lemma pmap_of_cinv {Q : Finset V} {P : Finset D} {Hs : List (Finset V)} (hI : CInv M Q P Hs) :
    ∃ σ : Perm D, PMap M (pdarts M (core M Q P) Hs) Hs σ := by
  obtain ⟨-, σ, hPI, hF, hc⟩ := hI
  exact ⟨σ, ⟨stable_pdarts hPI.rev Hs, hPI.stable, hPI.gap, hPI.vert, hc,
    fun x hx => (mem_pdarts.1 hx).2, hF⟩⟩

/-- **A pendant edge hangs at a vertex of the core**: in a connected piece with a dart in the piece
map of its core, the end off `Q` of a dart with an end in `Q` is related to the tail of a dart of
the piece map of the core. -/
lemma exists_core_anchor {S T Q : Finset V} (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q →
    M.tail d' = q → d = d') {P : Finset D} {Hs : List (Finset V)} (hP : PcOK M S T P Hs)
    (hHQ : Disjoint (hunion Hs) Q) {b₀ : D} (hb₀ : b₀ ∈ pdarts M (core M Q P) Hs) {d : D}
    (hd : d ∈ P) (hdQ : M.head d ∈ Q) (htQ : M.tail d ∉ Q) :
    ∃ b ∈ pdarts M (core M Q P) Hs, HRel Hs (M.tail b) (M.tail d) := by
  set a := M.tail d
  have hQn : ∀ q ∈ Q, q ∉ hunion Hs := fun q hq h => disjoint_left.1 hHQ h hq
  have hdp : d ∈ pdarts M P Hs := mem_pdarts.2 ⟨hd, fun h => by
    obtain ⟨H, hH, -, h2⟩ := h; exact hQn _ hdQ (subset_hunion hH h2)⟩
  have hb₀p : b₀ ∈ pdarts M P Hs := by
    rw [mem_pdarts] at hb₀ ⊢; exact ⟨(mem_core.1 hb₀.1).1, hb₀.2⟩
  have hcore : ∀ z ∈ pdarts M P Hs, M.tail z ∉ Q → M.head z ∉ Q →
      z ∈ pdarts M (core M Q P) Hs := fun z hz h1 h2 => by
    rw [mem_pdarts] at hz ⊢; exact ⟨mem_core.2 ⟨hz.1, h1, h2⟩, hz.2⟩
  have key : ∀ z, ReflTransGen (fun a b => b ∈ pdarts M P Hs ∧
      (b = M.rev a ∨ HRel Hs (M.tail a) (M.tail b))) d z →
      ((M.tail z ∈ Q ∧ HRel Hs (M.head z) a) ∨ (M.head z ∈ Q ∧ HRel Hs (M.tail z) a)) ∨
      ∃ b ∈ pdarts M (core M Q P) Hs, HRel Hs (M.tail b) a := by
    intro z hz
    induction hz with
    | refl => exact Or.inl (Or.inr ⟨hdQ, Or.inl rfl⟩)
    | tail _ hst ih =>
      rename_i c w _
      rcases ih with h | h
      · obtain ⟨hw, hcw⟩ := hst
        rcases hcw with e | e
        · subst e
          left
          rw [CombMap.tail_rev, CombMap.head_rev]
          tauto
        · rcases h with ⟨hcQ, hca⟩ | ⟨hcQ, hca⟩
          · -- the pendant vertex: no other dart leaves it
            have : M.tail w = M.tail c := hRel_eq_of_not_mem (hQn _ hcQ) (hRel_symm e)
            have hwc : w = c := hQdeg _ hcQ w c this rfl
            subst hwc; exact Or.inl (Or.inl ⟨hcQ, hca⟩)
          · have hwa : HRel Hs (M.tail w) a := hRel_trans' hP.disj (hRel_symm e) hca
            by_cases hwQ : M.tail w ∈ Q
            · exfalso
              have : M.tail w = a := hRel_eq_of_not_mem (hQn _ hwQ) (hRel_symm hwa) |>.symm
              exact htQ (this ▸ hwQ)
            · by_cases hwQ' : M.head w ∈ Q
              · exact Or.inl (Or.inr ⟨hwQ', hwa⟩)
              · exact Or.inr ⟨w, hcore w hw hwQ hwQ', hwa⟩
      · exact Or.inr h
  rcases key b₀ (hP.conn d hdp b₀ hb₀p) with h | h
  · exfalso
    have hc := mem_core.1 (mem_pdarts.1 hb₀).1
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · exact hc.2.1 h
    · exact hc.2.2 h
  · exact h

variable (M) in
/-- The weight of a set of darts in a split along the vertices `C`: its darts, and `K` for every
hole off `C` it touches. -/
noncomputable def hw (K : ℕ) (Hs : List (Finset V)) (C : Finset V) (X : Finset D) : ℕ := by
  classical
  exact X.card + K * (Hs.toFinset.filter fun H => Disjoint H C ∧ ∃ d ∈ X, M.tail d ∈ H).card

variable (M) in
/-- **The certificate of a split of a whole piece**: a simple path through the holes along darts
of the core, off `Q`, and items of weight `hw` at most `A`, covering the darts of `Nf` with an end
off the new hole; the darts of the piece off `Nf` are inside holes not touched by `Nf` (or met by
the path). -/
def PCert (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) (K A L : ℕ) : Prop :=
  ∃ (Nf : Finset D) (ρ : HPath M) (I : Finset (Finset D)),
    Nf ⊆ P ∧ (∀ d ∈ P \ Nf, Inner M Hs d ∧ (M.tail d ∉ newHole Hs ρ.mverts →
      ∀ x ∈ Nf, ¬ HRel Hs (M.tail x) (M.tail d))) ∧
    ρ.Simple Hs ∧ (∀ e ∈ ρ.darts, e ∈ pdarts M (core M Q P) Hs) ∧ ρ.k + 1 ≤ L ∧
    (∃ x ∈ P, M.tail x = ρ.p ρ.k) ∧ Disjoint ρ.mverts Q ∧
    (∀ X ∈ I, ∀ Y ∈ I, X ≠ Y → Disjoint X Y) ∧
    (∀ X ∈ I, X ⊆ Nf ∧ ∀ a ∈ X, ∀ b, AStep M Nf Hs (newHole Hs ρ.mverts) a b → b ∈ X) ∧
    (∀ d ∈ Nf, ¬ (M.tail d ∈ newHole Hs ρ.mverts ∧ M.head d ∈ newHole Hs ρ.mverts) →
      ∃ X ∈ I, d ∈ X) ∧
    (∀ X ∈ I, hw M K Hs ρ.mverts X ≤ A)

/-- A hole off the path through the holes is off the new hole. -/
lemma disjoint_newHole_of {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {C H : Finset V}
    (hH : H ∈ Hs) (hHC : Disjoint H C) : Disjoint H (newHole Hs C) := by
  refine disjoint_left.2 fun v hv hv' => ?_
  rcases mem_newHole.1 hv' with h | ⟨H', hH', hm, h⟩
  · exact disjoint_left.1 hHC hv h
  · by_cases e : H = H'
    · subst e; exact hm hHC
    · exact disjoint_left.1 (disjoint_of_pairwise hd hH hH' e) hv h

open Classical in
/-- **The holes touched by an item weigh at most its extra weight**, when every hole touched by
the darts `Nf` has an anchor dart of extra weight at least `K` in `Nf`. -/
lemma hw_le_wtY {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint) {Nf X : Finset D} {C : Finset V}
    (K : ℕ) (ex : D → ℕ) (hX : X ⊆ Nf)
    (hcl : ∀ a ∈ X, ∀ b, AStep M Nf Hs (newHole Hs C) a b → b ∈ X)
    (hanch : ∀ H ∈ Hs, (∃ d ∈ Nf, M.tail d ∈ H) → ∃ b ∈ Nf, M.tail b ∈ H ∧ K ≤ ex b) :
    hw M K Hs C X ≤ wtY M ex (newHole Hs C) X := by
  unfold hw wtY
  rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one]
  refine Nat.add_le_add_left ?_ _
  set Hf := Hs.toFinset.filter fun H => Disjoint H C ∧ ∃ d ∈ X, M.tail d ∈ H
  have hex : ∀ H ∈ Hf, ∃ b ∈ X, M.tail b ∈ H ∧ K ≤ ex b := by
    intro H hH
    obtain ⟨hHs, hHC, d, hdX, hdH⟩ := by simpa [Hf] using hH
    obtain ⟨b, hbN, hbH, hb⟩ := hanch H hHs ⟨d, hX hdX, hdH⟩
    have hoff : M.tail d ∉ newHole Hs C := fun h =>
      disjoint_left.1 (disjoint_newHole_of hd hHs hHC) hdH h
    exact ⟨b, hcl d hdX b ⟨hbN, Or.inr ⟨Or.inr ⟨H, hHs, hdH, hbH⟩, hoff⟩⟩, hbH, hb⟩
  rcases Hf.eq_empty_or_nonempty with h0 | ⟨H₀, hH₀⟩
  · rw [h0, card_empty, mul_zero]; exact Nat.zero_le _
  have : Nonempty D := ⟨(hex H₀ hH₀).choose⟩
  choose! f hfX hfH hfK using hex
  have hinj : Set.InjOn f (Hf : Set (Finset V)) := by
    intro H₁ h₁ H₂ h₂ e
    have h1 := hfH H₁ h₁
    have h2 := hfH H₂ h₂
    rw [e] at h1
    have hH₁ : H₁ ∈ Hs := List.mem_toFinset.1 (mem_filter.1 h₁).1
    have hH₂ : H₂ ∈ Hs := List.mem_toFinset.1 (mem_filter.1 h₂).1
    by_contra hne
    exact disjoint_left.1 (disjoint_of_pairwise hd hH₁ hH₂ hne) h1 h2
  calc K * Hf.card = ∑ H ∈ Hf, K := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ H ∈ Hf, ex (f H) := sum_le_sum fun H hH => hfK H hH
    _ = ∑ b ∈ Hf.image f, ex b := (sum_image hinj).symm
    _ ≤ ∑ d ∈ X.filter fun d => M.tail d ∉ newHole Hs C, ex d := by
        refine sum_le_sum_of_subset fun b hb => ?_
        obtain ⟨H, hH, rfl⟩ := mem_image.1 hb
        obtain ⟨hHs, hHC, -⟩ := by simpa [Hf] using hH
        refine mem_filter.2 ⟨hfX H hH, fun h => ?_⟩
        exact disjoint_left.1 (disjoint_newHole_of hd hHs hHC) (hfH H hH) h
    _ = ∑ d ∈ X, if M.tail d ∈ newHole Hs C then 0 else ex d := by
        rw [sum_filter]; exact sum_congr rfl fun d _ => by split_ifs <;> simp_all

open Classical in
/-- **The certificate of a piece with a nonempty core**: Miller's theorem on the core with its
cut-vertex holes pruned (`exists_scert`), the weight `K` on an anchor dart of every hole and the
pendant edges and darts inside the holes touched by the core attached (`scert_lift_list`). -/
theorem pcert_of_core {S T Q : Finset V} (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) (hne : (pdarts M (core M Q P) Hs).Nonempty)
    (K : ℕ) {A : ℕ} (hAW : P.card + K * nTouch M P Hs ≤ 2 * A)
    (hA : 2 * (P.card + K * nTouch M P Hs) + 2 + 9 * (6 * Nat.sqrt (2 * P.card) + 4) ≤ 3 * A)
    (hA2 : 2 ≤ A) :
    PCert M Q P Hs K A (6 * Nat.sqrt (2 * P.card) + 4) := by
  have hd := hP.disj
  have hHQ := hI.1
  set B₀ := pdarts M (core M Q P) Hs with hB₀
  obtain ⟨σ, hPM⟩ := pmap_of_cinv hI
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
      rw [if_pos htQ]; exact fun h => hQ5 d ⟨htQ, h⟩
    · show (if M.tail d ∈ Q then M.head d else M.tail d) ∉ Q
      rw [if_neg htQ]; exact htQ
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
  have : Nonempty D := ⟨b₀⟩
  choose! rep hrep hrepE using hEsrep
  choose! anc hancB hancR using fun E (hE : E ∈ Es) => hanc' (rep E) (hrep E hE)
  set Ls : List (Finset D × Finset V × D) :=
    Es.toList.map fun E => (E, cls Hs (av (rep E)), anc E) with hLs
  -- the anchors of the holes
  set anch : Finset V → D := fun H => if h : ∃ b ∈ B₀, M.tail b ∈ H then h.choose else b₀
    with hanch
  have hhAspec : ∀ H, (∃ b ∈ B₀, M.tail b ∈ H) → anch H ∈ B₀ ∧ M.tail (anch H) ∈ H := by
    intro H h
    simp only [anch, dif_pos h]
    exact h.choose_spec
  set exf : D → ℕ := fun d => if d ∈ B₀ ∧ ∃ H ∈ Hs, M.tail d ∈ H ∧ anch H = d then K else 0
    with hexf
  have hexf0 : ∀ d, d ∉ B₀ → exf d = 0 := fun d hd => by simp [exf, hd]
  -- the attached sets
  have hmemLs : ∀ e ∈ Ls, ∃ E ∈ Es, e = (E, cls Hs (av (rep E)), anc E) := fun e he => by
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 he
    exact ⟨E, mem_toList.1 hE, rfl⟩
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
  have hLsprop : ∀ e ∈ Ls, Stable (revPerm M) e.1 ∧ Disjoint e.1 B₀ ∧ HClosed Hs e.2.1 ∧
      (∀ u ∈ e.2.1, ∀ v ∈ e.2.1, HRel Hs u v) ∧ e.2.2 ∈ B₀ ∧ M.tail e.2.2 ∈ e.2.1 ∧
      (∀ d ∈ e.1, M.tail d ∈ e.2.1 ∨ M.tail d ∈ Q) ∧ ∑ d ∈ e.1, (1 + exf d) ≤ A := by
    intro e he
    obtain ⟨E, hE, rfl⟩ := hmemLs e he
    have hr := hrep E hE
    have hEeq := hrepE E hE
    refine ⟨?_, hEdisj E hE, hClosed_cls hd _, hRel_of_mem_cls hd _, hancB E hE,
      (mem_cls_iff hd).2 (hRel_symm (hancR E hE)), ?_, ?_⟩
    · rw [hEeq]; intro x hx
      simp only [mem_insert, mem_singleton] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (M.rev_rev _)
    · intro d hdE
      rw [hEeq] at hdE
      simp only [mem_insert, mem_singleton] at hdE
      set r := rep E
      have hrP : r ∈ P := (mem_sdiff.1 (mem_sdiff.1 hr).1).1
      rcases hdE with rfl | rfl
      · by_cases htQ : M.tail r ∈ Q
        · exact Or.inr htQ
        · left
          have : av r = M.tail r := by simp [av, htQ]
          rw [this]; exact mem_cls_self _ _
      · rw [CombMap.tail_rev]
        by_cases htQ : M.tail r ∈ Q
        · left
          have : av r = M.head r := by simp [av, htQ]
          rw [this]; exact mem_cls_self _ _
        · by_cases hhQ : M.head r ∈ Q
          · exact Or.inr hhQ
          · left
            have : av r = M.tail r := by simp [av, htQ]
            rw [this]
            -- a dart of the core off the piece map of the core is inside a hole
            have hin : Inner M Hs r := by
              by_contra h
              exact (mem_sdiff.1 hr).2 (mem_pdarts.2 ⟨mem_core.2 ⟨hrP, htQ, hhQ⟩, h⟩)
            obtain ⟨H, hH, h1, h2⟩ := hin
            exact (mem_cls_iff hd).2 (Or.inr ⟨H, hH, h1, h2⟩)
    · rw [hEw E hE, hEeq]; exact card_le_two.trans hA2
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
    exact (nodup_toList Es).pairwise_of_forall_ne fun E hE E' hE' hne =>
      hEsdisj E (mem_toList.1 hE) E' (mem_toList.1 hE') hne
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
        exact ⟨_, List.mem_map.2 ⟨_, mem_toList.2 hxE, rfl⟩, by simp⟩
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
      exact Finset.sum_map_toList Es _
    simp_rw [e1]
    rw [sum_comm]
    refine le_trans (sum_le_sum fun E hE => ?_) hsumEs
    rw [sum_ite_eq' B₀ (anc E), if_pos (hancB E hE), hEw E hE]
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
  -- the search and the lift
  have hsq : Nat.sqrt (2 * B₀.card) ≤ Nat.sqrt (2 * P.card) :=
    Nat.sqrt_le_sqrt (by have := card_le_card hB₀P; omega)
  have hc := exists_scert hd hloopM hAW B₀.card B₀ σ (fun d => exf d + lmoved exf Ls d) rfl hPM
    ⟨b₀, hb₀⟩ htot (by omega)
  have hc' := scert_lift_list hd hQdeg hHQ Ls B₀ exf (stable_pdarts (revClosed_core hP.rev) Hs)
    hLsprop hpw hc
  rw [hlun] at hc'
  obtain ⟨ρ, I, hs, hdar, hlen, ⟨xl, hxl, hxle⟩, hdisj, hcls, hcov, hwt⟩ := hc'
  have hρQ : Disjoint ρ.mverts Q := by
    refine disjoint_left.2 fun v hv hvQ => ?_
    rcases ρ.mem_mverts.1 hv with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rcases Nat.lt_or_ge j ρ.k with h | h
      · rw [← ρ.tail_d j h] at hvQ
        exact (hB₀Q _ (hdar _ (ρ.mem_darts.2 ⟨j, h, Or.inl rfl⟩))).1 hvQ
      · rw [show j = ρ.k by omega, ← hxle] at hvQ
        exact (hB₀Q _ hxl).1 hvQ
    · exact (hB₀Q _ (hdar _ (ρ.mem_darts.2 ⟨j, hj, Or.inl rfl⟩))).2 hvQ
  refine ⟨Nf, ρ, I, sdiff_subset, fun d hd' => ?_, hs, hdar, hlen.trans (by omega),
    ⟨xl, hB₀P hxl, hxle⟩, hρQ, hdisj, hcls, hcov, fun X hX => ?_⟩
  · -- the darts left out are inside holes not touched by `Nf`
    rw [sdiff_sdiff_right_self, inf_eq_inter, inter_eq_right.2 (filter_subset _ _)] at hd'
    obtain ⟨hdP, hdi, hdn⟩ := mem_filter.1 hd'
    refine ⟨hdi, fun _ x hx hr => ?_⟩
    by_cases hxB : x ∈ B₀
    · exact hdn x hxB hr
    · obtain ⟨b, hb, hbr⟩ := hanc' x (mem_sdiff.2 ⟨hx, hxB⟩)
      by_cases htQ : M.tail x ∈ Q
      · obtain ⟨H, hH, h1, -⟩ := hdi
        have := hRel_eq_of_not_mem (hQn _ htQ) (hRel_symm hr)
        exact hQn _ htQ (this ▸ subset_hunion hH h1)
      · have : av x = M.tail x := by simp [av, htQ]
        rw [this] at hbr
        exact hdn b hb (hRel_trans' hd hbr hr)
  · -- the weight of an item
    refine (hw_le_wtY hd K exf (hcls X hX).1 (hcls X hX).2 fun H hH ⟨d, hdN, hdH⟩ => ?_).trans
      (hwt X hX)
    -- a hole touched by `Nf` has an anchor
    have hHB : ∃ b ∈ B₀, M.tail b ∈ H := by
      by_cases hdB : d ∈ B₀
      · exact ⟨d, hdB, hdH⟩
      · obtain ⟨b, hb, hbr⟩ := hanc' d (mem_sdiff.2 ⟨hdN, hdB⟩)
        have htQ : M.tail d ∉ Q := fun h => hQn _ h (subset_hunion hH hdH)
        have : av d = M.tail d := by simp [av, htQ]
        rw [this] at hbr
        exact ⟨b, hb, hClosed_of_mem hd hH _ hdH _ (hRel_symm hbr)⟩
    obtain ⟨hAB, hAH⟩ := hhAspec H hHB
    have hex : exf (anch H) = K := by
      have hw : ∃ H' ∈ Hs, M.tail (anch H) ∈ H' ∧ anch H' = anch H := ⟨H, hH, hAH, rfl⟩
      simp only [exf]
      rw [if_pos ⟨hAB, hw⟩]
    exact ⟨anch H, hB₀Nf hAB, hAH, hex.ge⟩

/-- **The certificate of a piece with an empty core**: its piece map has only pendant edges, all
hanging at one vertex (or hole); the separator is that vertex, and the items the pendant edges. -/
theorem pcert_of_empty {S T Q : Finset V}
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) (hP0 : P.Nonempty)
    (hne : pdarts M (core M Q P) Hs = ∅) (K : ℕ) {A L : ℕ} (hA2 : 2 ≤ A) (hL : 1 ≤ L) :
    PCert M Q P Hs K A L := by
  classical
  have hd := hP.disj
  have hHQ := hI.1
  have hQn : ∀ q ∈ Q, q ∉ hunion Hs := fun q hq h => disjoint_left.1 hHQ h hq
  -- the darts of the piece map are pendant
  have hpend : ∀ d ∈ pdarts M P Hs, M.tail d ∈ Q ∨ M.head d ∈ Q := by
    intro d hd'
    by_contra h
    push Not at h
    have : d ∈ pdarts M (core M Q P) Hs := by
      rw [mem_pdarts] at hd' ⊢; exact ⟨mem_core.2 ⟨hd'.1, h.1, h.2⟩, hd'.2⟩
    rw [hne] at this; simp at this
  by_cases hpd : (pdarts M P Hs).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hpd
    -- a pendant dart leaving its attachment
    obtain ⟨y, hy, hyQ⟩ : ∃ y ∈ pdarts M P Hs, M.tail y ∉ Q := by
      by_cases h : M.tail y₀ ∈ Q
      · refine ⟨M.rev y₀, stable_pdarts hP.rev Hs _ hy₀, ?_⟩
        rw [CombMap.tail_rev]; exact fun h' => hQ5 y₀ ⟨h, h'⟩
      · exact ⟨y₀, hy₀, h⟩
    set a := M.tail y
    -- every dart of the piece map leaving a vertex off `Q` leaves the class of `a`
    have hatt : ∀ z ∈ pdarts M P Hs, M.tail z ∉ Q → HRel Hs (M.tail z) a := by
      intro z hz hzQ
      have key : ∀ w, ReflTransGen (fun a b => b ∈ pdarts M P Hs ∧
          (b = M.rev a ∨ HRel Hs (M.tail a) (M.tail b))) y w →
          (M.tail w ∉ Q → HRel Hs (M.tail w) a) ∧ (M.tail w ∈ Q → HRel Hs (M.head w) a) := by
        intro w hw
        induction hw with
        | refl => exact ⟨fun _ => Or.inl rfl, fun h => absurd h hyQ⟩
        | tail _ hst ih =>
          rename_i b c _
          obtain ⟨ih1, ih2⟩ := ih
          obtain ⟨hc, hbc⟩ := hst
          rcases hbc with e | e
          · subst e
            rw [CombMap.tail_rev, CombMap.head_rev]
            refine ⟨fun h => ?_, fun h => ?_⟩
            · by_cases hb : M.tail b ∈ Q
              · exact ih2 hb
              · exact absurd ((hpend _ hc).resolve_left h) (by rw [CombMap.head_rev]; exact hb)
            · by_cases hb : M.tail b ∈ Q
              · exact absurd ⟨hb, h⟩ (hQ5 b)
              · exact ih1 hb
          · by_cases hb : M.tail b ∈ Q
            · have : M.tail c = M.tail b := hRel_eq_of_not_mem (hQn _ hb) (hRel_symm e)
              have hcb : c = b := hQdeg _ hb c b this rfl
              subst hcb; exact ⟨ih1, ih2⟩
            · have hca : HRel Hs (M.tail c) a := hRel_trans' hd (hRel_symm e) (ih1 hb)
              refine ⟨fun _ => hca, fun h => ?_⟩
              exfalso
              -- `c` leaves a vertex of `Q` related to `a`, which is off `Q`
              have : M.tail c = a := by
                rcases hca with e' | ⟨H, hH, h1, -⟩
                · exact e'
                · exact absurd (subset_hunion hH h1) (hQn _ h)
              exact hyQ (this ▸ h)
      exact (key z (hP.conn y hy z hz)).1 hzQ
    set ρ := (SPath.point (M' := M) y a).toH with hρ
    have hm : ρ.mverts = {a} := HPath.toH_point_mverts y a
    have hh : ∀ v, v ∈ newHole Hs ρ.mverts ↔ HRel Hs v a := by
      intro v
      rw [mem_newHole_iff hd ⟨fun j hj => absurd hj (Nat.not_lt_zero _),
        fun i hi j hj _ => by simp [ρ, SPath.toH, SPath.point] at hi hj; omega⟩]
      simp [ρ, SPath.toH, SPath.point]
    set Nf := pdarts M P Hs
    refine ⟨Nf, ρ, Nf.image fun d => ({d, M.rev d} : Finset D), pdarts_subset _ _,
      fun d hd' => ?_, ⟨fun j hj => absurd hj (Nat.not_lt_zero _),
        fun i hi j hj _ => by simp [ρ, SPath.toH, SPath.point] at hi hj; omega⟩,
      fun e he => by simp [ρ, SPath.toH_darts, SPath.point_darts'] at he,
      by simp [ρ, SPath.toH, SPath.point]; omega, ⟨y, pdarts_subset _ _ hy, rfl⟩,
      by rw [hm]; exact disjoint_singleton_left.2 hyQ, ?_, ?_, ?_, ?_⟩
    · -- the darts off the piece map are inside holes
      obtain ⟨hdP, hdN⟩ := mem_sdiff.1 hd'
      have hdi : Inner M Hs d := by
        by_contra h; exact hdN (mem_pdarts.2 ⟨hdP, h⟩)
      refine ⟨hdi, fun hdh x hx hr => hdh ((hh _).2 ?_)⟩
      by_cases hxQ : M.tail x ∈ Q
      · obtain ⟨H, hH, h1, -⟩ := hdi
        have := hRel_eq_of_not_mem (hQn _ hxQ) (hRel_symm hr)
        exact absurd (this ▸ subset_hunion hH h1) (hQn _ hxQ)
      · exact hRel_trans' hd (hRel_symm hr) (hatt x hx hxQ)
    · intro X hX Y hY hXY
      obtain ⟨x, -, rfl⟩ := mem_image.1 hX
      obtain ⟨z, -, rfl⟩ := mem_image.1 hY
      refine disjoint_left.2 fun w hw hw' => hXY ?_
      simp only [mem_insert, mem_singleton] at hw hw'
      ext u; simp only [mem_insert, mem_singleton]
      rcases hw with rfl | rfl <;> rcases hw' with h | h
      · rw [h]
      · rw [h, M.rev_rev]; tauto
      · rw [← h, M.rev_rev]; tauto
      · have := congrArg M.rev h; rw [M.rev_rev, M.rev_rev] at this; rw [this]
    · intro X hX
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
      refine ⟨fun w hw => ?_, fun b hb c hbc => ?_⟩
      · simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact hx
        · exact stable_pdarts hP.rev Hs _ hx
      · simp only [mem_insert, mem_singleton] at hb ⊢
        rcases hbc.2 with e | ⟨e, hbh⟩
        · rcases hb with rfl | rfl
          · exact Or.inr e
          · exact Or.inl (by rw [e, M.rev_rev])
        · -- the pivot is the pendant vertex
          have hbN : b ∈ Nf := by
            rcases hb with rfl | rfl
            · exact hx
            · exact stable_pdarts hP.rev Hs _ hx
          have hbQ : M.tail b ∈ Q := by
            by_contra hbQ; exact hbh ((hh _).2 (hatt b hbN hbQ))
          have : M.tail c = M.tail b := hRel_eq_of_not_mem (hQn _ hbQ) (hRel_symm e)
          rw [hQdeg _ hbQ c b this rfl]; exact hb
    · intro d hd' _
      exact ⟨_, mem_image_of_mem _ hd', by simp⟩
    · intro X hX
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hX
      unfold hw
      have hnone : (Hs.toFinset.filter fun H => Disjoint H ρ.mverts ∧
          ∃ d ∈ ({x, M.rev x} : Finset D), M.tail d ∈ H) = ∅ := by
        refine filter_eq_empty_iff.2 fun H hH ⟨hHC, d, hdX, hdH⟩ => ?_
        have hdN : d ∈ Nf := by
          simp only [mem_insert, mem_singleton] at hdX
          rcases hdX with rfl | rfl
          · exact hx
          · exact stable_pdarts hP.rev Hs _ hx
        have hdQ : M.tail d ∉ Q := fun h => hQn _ h (subset_hunion (List.mem_toFinset.1 hH) hdH)
        have := hatt d hdN hdQ
        have hHa : a ∈ H := hClosed_of_mem hd (List.mem_toFinset.1 hH) _ hdH _ this
        rw [hm] at hHC
        exact disjoint_left.1 hHC hHa (mem_singleton_self _)
      rw [hnone, card_empty, mul_zero, add_zero]
      exact card_le_two.trans hA2
  · -- only darts inside holes
    rw [not_nonempty_iff_eq_empty] at hpd
    obtain ⟨x, hx⟩ := hP0
    have hxi : Inner M Hs x := by
      by_contra h
      have : x ∈ pdarts M P Hs := mem_pdarts.2 ⟨hx, h⟩
      rw [hpd] at this; simp at this
    obtain ⟨H, hH, h1, -⟩ := hxi
    set ρ := (SPath.point (M' := M) x (M.tail x)).toH with hρ
    have hm : ρ.mverts = {M.tail x} := HPath.toH_point_mverts x _
    refine ⟨∅, ρ, ∅, empty_subset _, fun d hd' => ⟨?_, fun _ _ h => by simp at h⟩,
      ⟨fun j hj => absurd hj (Nat.not_lt_zero _),
        fun i hi j hj _ => by simp [ρ, SPath.toH, SPath.point] at hi hj; omega⟩,
      fun e he => by simp [ρ, SPath.toH_darts, SPath.point_darts'] at he,
      by simp [ρ, SPath.toH, SPath.point]; omega, ⟨x, hx, rfl⟩,
      by rw [hm]; exact disjoint_singleton_left.2 fun h => hQn _ h (subset_hunion hH h1),
      by simp, by simp, by simp, by simp⟩
    rw [sdiff_empty] at hd'
    by_contra h
    have : d ∈ pdarts M P Hs := mem_pdarts.2 ⟨hd', h⟩
    rw [hpd] at this; simp at this

end BKMNW

end PlanarFlow
