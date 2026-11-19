module

public import PlanarFlow.BKMNW.ExistOracle

/-!
# The split of a large piece from its certificate

From a certificate `PCert` of a piece, the darts of the piece fall into classes: the items of
the certificate with the darts inside the new hole taken out, the pairs of darts inside the new
hole, and the darts inside the other holes (in pairs, or one class per hole). The classes are
closed under the steps of the children (`exists_cls`), and are grouped into two children of
weight `hw` at most `A` each (`exists_split_of_pcert`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

/-! ### Partitions by classes -/

/-- A class function on `P`: each dart of `P` lies in its class, a subset of `P`, which is the
class of each of its darts. -/
structure IsCls (P : Finset D) (c : D → Finset D) : Prop where
  self : ∀ d ∈ P, d ∈ c d
  sub : ∀ d ∈ P, c d ⊆ P
  eq : ∀ d ∈ P, ∀ e ∈ c d, c e = c d

namespace IsCls

variable {P : Finset D} {c : D → Finset D}

lemma eq_of_mem (h : IsCls P c) {X : Finset D} (hX : X ∈ P.image c) {e : D} (he : e ∈ X) :
    c e = X := by
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hX
  exact h.eq d hd e he

lemma disj (h : IsCls P c) {X Y : Finset D} (hX : X ∈ P.image c) (hY : Y ∈ P.image c)
    (hXY : X ≠ Y) : Disjoint X Y :=
  disjoint_left.2 fun _ he he' => hXY ((h.eq_of_mem hX he).symm.trans (h.eq_of_mem hY he'))

lemma biUnion_eq (h : IsCls P c) : (P.image c).biUnion id = P := by
  ext e
  simp only [mem_biUnion, mem_image, id]
  constructor
  · rintro ⟨_, ⟨d, hd, rfl⟩, he⟩; exact h.sub d hd he
  · intro he; exact ⟨_, ⟨e, he, rfl⟩, h.self e he⟩

lemma card_biUnion (h : IsCls P c) {G : Finset (Finset D)} (hG : G ⊆ P.image c) :
    (G.biUnion id).card = ∑ X ∈ G, X.card :=
  Finset.card_biUnion fun _ hX _ hY hXY => h.disj (hG (mem_coe.1 hX)) (hG (mem_coe.1 hY)) hXY

lemma nonempty (h : IsCls P c) {X : Finset D} (hX : X ∈ P.image c) : X.Nonempty := by
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hX
  exact ⟨d, h.self d hd⟩

end IsCls

/-! ### The holes touched by a set of darts -/

variable (M) in
/-- The holes off `C` touched by the darts `X`. -/
noncomputable def tH (Hs : List (Finset V)) (C : Finset V) (X : Finset D) :
    Finset (Finset V) := by
  classical exact Hs.toFinset.filter fun H => Disjoint H C ∧ ∃ d ∈ X, M.tail d ∈ H

section TH

variable {Hs : List (Finset V)} {C : Finset V}

lemma hw_eq (K : ℕ) (Hs : List (Finset V)) (C : Finset V) (X : Finset D) :
    hw M K Hs C X = X.card + K * (tH M Hs C X).card := rfl

lemma mem_tH {X : Finset D} {H : Finset V} :
    H ∈ tH M Hs C X ↔ H ∈ Hs ∧ Disjoint H C ∧ ∃ d ∈ X, M.tail d ∈ H := by
  classical simp [tH]

lemma tH_mono {X X' : Finset D} (h : X ⊆ X') : tH M Hs C X ⊆ tH M Hs C X' := fun H hH => by
  rw [mem_tH] at hH ⊢
  obtain ⟨a, b, d, hd, e⟩ := hH
  exact ⟨a, b, d, h hd, e⟩

lemma hw_mono (K : ℕ) {X X' : Finset D} (h : X ⊆ X') : hw M K Hs C X ≤ hw M K Hs C X' := by
  rw [hw_eq, hw_eq]
  exact Nat.add_le_add (card_le_card h) (Nat.mul_le_mul_left _ (card_le_card (tH_mono h)))

lemma tH_biUnion (G : Finset (Finset D)) : tH M Hs C (G.biUnion id) = G.biUnion (tH M Hs C) := by
  ext H
  simp only [mem_tH, mem_biUnion, id]
  constructor
  · rintro ⟨h1, h2, d, ⟨X, hX, hd⟩, e⟩; exact ⟨X, hX, h1, h2, d, hd, e⟩
  · rintro ⟨X, hX, h1, h2, d, hd, e⟩; exact ⟨h1, h2, d, ⟨X, hX, hd⟩, e⟩

lemma hw_biUnion_le (K : ℕ) (G : Finset (Finset D)) :
    hw M K Hs C (G.biUnion id) ≤ ∑ X ∈ G, hw M K Hs C X := by
  simp only [hw_eq, sum_add_distrib, ← mul_sum]
  refine Nat.add_le_add card_biUnion_le (Nat.mul_le_mul_left _ ?_)
  rw [tH_biUnion]
  exact card_biUnion_le

lemma nodup_filter_of (hd : Hs.Pairwise Disjoint) (q : Finset V → Bool)
    (hq : ∀ H, q H → H.Nonempty) : (Hs.filter q).Nodup := by
  refine (hd.filter q).imp_of_mem fun ha _ hab e => ?_
  subst e
  obtain ⟨v, hv⟩ := hq _ (List.mem_filter.1 ha).2
  exact disjoint_left.1 hab hv hv

open Classical in
lemma nTouch_eq_card (hd : Hs.Pairwise Disjoint) (X : Finset D) :
    nTouch M X Hs = (Hs.filter fun H => ∃ v ∈ H, Touch M X v).toFinset.card := by
  unfold nTouch
  rw [List.toFinset_card_of_nodup (nodup_filter_of hd _ fun H hH => by
    obtain ⟨v, hv, -⟩ := of_decide_eq_true hH; exact ⟨v, hv⟩)]

open Classical in
lemma card_tH_le_nTouch (X : Finset D) : (tH M Hs C X).card ≤ nTouch M X Hs := by
  unfold nTouch
  refine le_trans (card_le_card ?_) (List.toFinset_card_le _)
  intro H hH
  obtain ⟨h1, -, d, hd, e⟩ := mem_tH.1 hH
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨h1, _, e, d, hd, rfl⟩

open Classical in
lemma card_tH_eq (hd : Hs.Pairwise Disjoint) (X : Finset D) : (tH M Hs C X).card =
    (Hs.filter fun H => Disjoint H C ∧ ∃ v ∈ H, Touch M X v).length := by
  rw [← List.toFinset_card_of_nodup (nodup_filter_of hd _ fun H hH => by
    obtain ⟨-, v, hv, -⟩ := of_decide_eq_true hH; exact ⟨v, hv⟩)]
  congr 1
  ext H
  simp only [mem_tH, Touch]
  simp [and_comm]

open Classical in
/-- The holes of the children touched by a child: the holes off the separator it touches, and
the new hole. -/
lemma nTouch_ch_le (hd : Hs.Pairwise Disjoint) (X : Finset D) :
    nTouch M X (childHoles Hs C) ≤ (tH M Hs C X).card + 1 := by
  rw [card_tH_eq hd]
  unfold nTouch childHoles
  rw [List.filter_append, List.length_append, List.filter_filter]
  refine Nat.add_le_add (le_of_eq ?_) ((List.length_filter_le _ _).trans (by simp))
  congr 1
  refine List.filter_congr fun H _ => ?_
  rw [Bool.decide_and, Bool.and_comm]

end TH

/-! ### The classes of a certificate -/

lemma rev_mem_pair {d e : D} (he : e ∈ ({d, M.rev d} : Finset D)) :
    M.rev e ∈ ({d, M.rev d} : Finset D) := by
  rcases mem_insert.1 he with rfl | he
  · exact mem_insert_of_mem (mem_singleton_self _)
  · rw [mem_singleton.1 he, M.rev_rev]; exact mem_insert_self _ _

open Classical in
/-- **The classes of the darts of a piece from a certificate**: the items with the darts inside
the new hole taken out (the components of the steps off the new hole), the pairs of darts inside
the new hole, and the darts inside the other holes, by pairs (`K = 0`) or by hole (`K ≠ 0`). They
are closed under reversal and under the steps of the children, weigh at most `A`, and for
`K ≠ 0` two classes touch no common hole off the separator. -/
theorem exists_cls {S T : Finset V} {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) {K A : ℕ} {Nf : Finset D} {ρ : HPath M} {I : Finset (Finset D)}
    (hNf : Nf ⊆ P) (hout : ∀ d ∈ P \ Nf, Inner M Hs d ∧ (M.tail d ∉ newHole Hs ρ.mverts →
      ∀ x ∈ Nf, ¬ HRel Hs (M.tail x) (M.tail d))) (hρ : ρ.Simple Hs)
    (hIc : ∀ X ∈ I, X ⊆ Nf ∧ ∀ a ∈ X, ∀ b, AStep M Nf Hs (newHole Hs ρ.mverts) a b → b ∈ X)
    (hIcov : ∀ d ∈ Nf, ¬ (M.tail d ∈ newHole Hs ρ.mverts ∧ M.head d ∈ newHole Hs ρ.mverts) →
      ∃ X ∈ I, d ∈ X)
    (hIw : ∀ X ∈ I, hw M K Hs ρ.mverts X ≤ A) (hA2 : 2 ≤ A) (hKA : K ≠ 0 → P.card + K ≤ A) :
    ∃ c : D → Finset D, IsCls P c ∧ (∀ X ∈ P.image c, ∀ e ∈ X, M.rev e ∈ X) ∧
      (∀ X ∈ P.image c, hw M K Hs ρ.mverts X ≤ A) ∧
      (K ≠ 0 → ∀ X ∈ P.image c, ∀ X' ∈ P.image c, X ≠ X' →
        Disjoint (tH M Hs ρ.mverts X) (tH M Hs ρ.mverts X')) ∧
      (∀ a ∈ P, ∀ b ∈ P, ¬ Inner M (childHoles Hs ρ.mverts) a →
        ¬ Inner M (childHoles Hs ρ.mverts) b →
        (b = M.rev a ∨ (HRel Hs (M.tail a) (M.tail b) ∧ M.tail a ∉ newHole Hs ρ.mverts)) →
        b ∈ c a) ∧
      (∀ d ∈ P, M.tail d ∈ newHole Hs ρ.mverts → M.head d ∈ newHole Hs ρ.mverts →
        c d = {d, M.rev d}) := by
  have hd := hP.disj
  set C := ρ.mverts with hC
  set Y := newHole Hs C with hY
  have hYc : HClosed Hs Y := hClosed_newHole hd hρ
  set J := P.filter fun d => M.tail d ∈ Y ∧ M.head d ∈ Y with hJ
  set R := (P \ Nf) \ J with hR
  set N' := Nf \ J with hN'
  have hmJ : ∀ d, d ∈ J ↔ d ∈ P ∧ M.tail d ∈ Y ∧ M.head d ∈ Y := fun d => mem_filter
  have hrevP : ∀ d ∈ P, M.rev d ∈ P := hP.rev
  -- a hole met by a vertex of the new hole is inside it
  have hinY : ∀ H ∈ Hs, ∀ v ∈ H, v ∈ Y → ∀ w ∈ H, w ∈ Y := by
    intro H hH v hv hvY w hw
    by_cases hm : Disjoint H C
    · exact absurd hvY (disjoint_left.1 (disjoint_newHole_of hd hH hm) hv)
    · exact mem_newHole.2 (Or.inr ⟨H, hH, hm, hw⟩)
  have hJrev : ∀ d ∈ J, M.rev d ∈ J := fun d h => by
    rw [hmJ] at h ⊢
    rw [CombMap.tail_rev, CombMap.head_rev]
    exact ⟨hrevP _ h.1, h.2.2, h.2.1⟩
  have hR1 : ∀ d ∈ R, Inner M Hs d ∧ M.tail d ∉ Y ∧ ∀ x ∈ Nf, ¬ HRel Hs (M.tail x) (M.tail d) := by
    intro d h
    have h1 : d ∈ P \ Nf := (mem_sdiff.1 h).1
    have hdJ : d ∉ J := (mem_sdiff.1 h).2
    obtain ⟨hin, hno⟩ := hout d h1
    have htY : M.tail d ∉ Y := fun htY => by
      obtain ⟨H, hH, h1', h2'⟩ := hin
      exact hdJ ((hmJ d).2 ⟨(mem_sdiff.1 h1).1, htY, hinY H hH _ h1' htY _ h2'⟩)
    exact ⟨hin, htY, hno htY⟩
  have hNrev : ∀ d ∈ N', M.rev d ∈ N' := by
    intro d h
    obtain ⟨hdN, hdJ⟩ := mem_sdiff.1 h
    have hrJ : M.rev d ∉ J := fun h' => hdJ (by have := hJrev _ h'; rwa [M.rev_rev] at this)
    refine mem_sdiff.2 ⟨?_, hrJ⟩
    by_contra hrN
    have hrR : M.rev d ∈ R := mem_sdiff.2 ⟨mem_sdiff.2 ⟨hrevP _ (hNf hdN), hrN⟩, hrJ⟩
    obtain ⟨⟨H, hH, h1, h2⟩, -, hno⟩ := hR1 _ hrR
    rw [CombMap.tail_rev] at hno h1
    rw [CombMap.head_rev] at h2
    exact hno d hdN (Or.inr ⟨H, hH, h2, h1⟩)
  have hRrev : ∀ d ∈ R, M.rev d ∈ R := by
    intro d h
    obtain ⟨h1, hdJ⟩ := mem_sdiff.1 h
    obtain ⟨hdP, hdN⟩ := mem_sdiff.1 h1
    have hrJ : M.rev d ∉ J := fun h' => hdJ (by have := hJrev _ h'; rwa [M.rev_rev] at this)
    refine mem_sdiff.2 ⟨mem_sdiff.2 ⟨hrevP _ hdP, fun hrN => hdN ?_⟩, hrJ⟩
    have := (mem_sdiff.1 (hNrev _ (mem_sdiff.2 ⟨hrN, hrJ⟩))).1
    rwa [M.rev_rev] at this
  have hinch : ∀ d ∈ P, ¬ Inner M (childHoles Hs C) d → d ∈ N' := by
    intro d hdP hni
    have hdJ : d ∉ J := fun h => hni ⟨Y, List.mem_append_right _ (List.mem_singleton_self _),
      ((hmJ d).1 h).2.1, ((hmJ d).1 h).2.2⟩
    refine mem_sdiff.2 ⟨?_, hdJ⟩
    by_contra hdN
    obtain ⟨⟨H, hH, h1, h2⟩, htY, -⟩ := hR1 d (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hdP, hdN⟩, hdJ⟩)
    have hHC : Disjoint H C := by
      by_contra hm; exact htY (mem_newHole.2 (Or.inr ⟨H, hH, hm, h1⟩))
    exact hni ⟨H, List.mem_append_left _ (List.mem_filter.2 ⟨hH, by simpa using hHC⟩), h1, h2⟩
  -- the class function
  obtain ⟨c, hcJ, hcN, hcR0, hcR⟩ : ∃ c : D → Finset D, (∀ d ∈ J, c d = {d, M.rev d}) ∧
      (∀ d ∈ N', c d = comp M N' Hs Y d) ∧
      (K = 0 → ∀ d ∈ R, c d = {d, M.rev d}) ∧
      (K ≠ 0 → ∀ d ∈ R, c d = R.filter fun e => HRel Hs (M.tail d) (M.tail e)) := by
    refine ⟨fun d => if d ∈ J then {d, M.rev d} else if d ∈ Nf then comp M N' Hs Y d else
      if K = 0 then {d, M.rev d} else R.filter fun e => HRel Hs (M.tail d) (M.tail e),
      fun d h => ?_, fun d h => ?_, fun hK d h => ?_, fun hK d h => ?_⟩
    · simp only [h, ↓reduceIte]
    · obtain ⟨h1, h2⟩ := mem_sdiff.1 h
      simp only [h1, h2, ↓reduceIte]
    · obtain ⟨h1, h2⟩ := mem_sdiff.1 h
      simp only [h2, (mem_sdiff.1 h1).2, hK, ↓reduceIte]
    · obtain ⟨h1, h2⟩ := mem_sdiff.1 h
      simp only [h2, (mem_sdiff.1 h1).2, hK, ↓reduceIte]
  have hRP : R ⊆ P := fun d h => (mem_sdiff.1 (mem_sdiff.1 h).1).1
  have hN'P : N' ⊆ P := fun d h => hNf (mem_sdiff.1 h).1
  have htri : ∀ d ∈ P, d ∈ J ∨ d ∈ N' ∨ d ∈ R := by
    intro d hd
    by_cases h1 : d ∈ J
    · exact Or.inl h1
    by_cases h2 : d ∈ Nf
    · exact Or.inr (Or.inl (mem_sdiff.2 ⟨h2, h1⟩))
    exact Or.inr (Or.inr (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hd, h2⟩, h1⟩))
  have hpairP : ∀ d ∈ P, ({d, M.rev d} : Finset D) ⊆ P := fun d hdP e he => by
    rcases mem_insert.1 he with rfl | he
    · exact hdP
    · rw [mem_singleton.1 he]; exact hrevP _ hdP
  have hcls : IsCls P c := by
    refine ⟨fun d hdP => ?_, fun d hdP => ?_, fun d hdP e he => ?_⟩
    · rcases htri d hdP with h | h | h
      · rw [hcJ d h]; exact mem_insert_self _ _
      · rw [hcN d h]; exact self_mem_comp h
      · by_cases hK : K = 0
        · rw [hcR0 hK d h]; exact mem_insert_self _ _
        · rw [hcR hK d h]; exact mem_filter.2 ⟨h, Or.inl rfl⟩
    · rcases htri d hdP with h | h | h
      · rw [hcJ d h]; exact hpairP d hdP
      · rw [hcN d h]; exact fun e he => hN'P (mem_comp.1 he).1
      · by_cases hK : K = 0
        · rw [hcR0 hK d h]; exact hpairP d hdP
        · rw [hcR hK d h]; exact fun e he => hRP (mem_filter.1 he).1
    · rcases htri d hdP with h | h | h
      · rw [hcJ d h] at he ⊢
        rcases mem_insert.1 he with rfl | he
        · exact hcJ _ h
        · rw [mem_singleton.1 he, hcJ _ (hJrev d h), M.rev_rev, pair_comm]
      · rw [hcN d h] at he ⊢
        rw [hcN e (mem_comp.1 he).1, comp_eq_of_mem hYc h he]
      · by_cases hK : K = 0
        · rw [hcR0 hK d h] at he ⊢
          rcases mem_insert.1 he with rfl | he
          · exact hcR0 hK _ h
          · rw [mem_singleton.1 he, hcR0 hK _ (hRrev d h), M.rev_rev, pair_comm]
        · rw [hcR hK d h] at he ⊢
          obtain ⟨heR, hde⟩ := mem_filter.1 he
          rw [hcR hK e heR]
          ext x
          simp only [mem_filter]
          exact and_congr_right fun _ => ⟨fun h' => hRel_trans' hd hde h',
            fun h' => hRel_trans' hd (hRel_symm hde) h'⟩
  have hXP : ∀ X ∈ P.image c, X ⊆ P := fun X hX => by
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hX; exact hcls.sub d hd
  -- closed under reversal
  have hrevX : ∀ X ∈ P.image c, ∀ e ∈ X, M.rev e ∈ X := by
    intro X hX e he
    obtain ⟨d, hdP, rfl⟩ := mem_image.1 hX
    rcases htri d hdP with h | h | h
    · rw [hcJ d h] at he ⊢; exact rev_mem_pair he
    · rw [hcN d h] at he ⊢; exact comp_closed he ⟨hNrev _ (mem_comp.1 he).1, Or.inl rfl⟩
    · by_cases hK : K = 0
      · rw [hcR0 hK d h] at he ⊢; exact rev_mem_pair he
      · rw [hcR hK d h] at he ⊢
        obtain ⟨heR, hde⟩ := mem_filter.1 he
        obtain ⟨⟨H, hH, h1, h2⟩, -, -⟩ := hR1 e heR
        refine mem_filter.2 ⟨hRrev e heR, ?_⟩
        rw [CombMap.tail_rev]
        exact hRel_trans' hd hde (Or.inr ⟨H, hH, h1, h2⟩)
  -- a set of darts leaving the new hole touches no hole off the separator
  have htY0 : ∀ X : Finset D, (∀ e ∈ X, M.tail e ∈ Y) → tH M Hs C X = ∅ := by
    intro X hX
    refine eq_empty_of_forall_notMem fun H hH => ?_
    obtain ⟨hH, hHC, e, he, heH⟩ := mem_tH.1 hH
    exact disjoint_left.1 (disjoint_newHole_of hd hH hHC) heH (hX e he)
  -- the weights
  have hwt : ∀ X ∈ P.image c, hw M K Hs C X ≤ A := by
    intro X hX
    obtain ⟨d, hdP, rfl⟩ := mem_image.1 hX
    rcases htri d hdP with h | h | h
    · rw [hcJ d h, hw_eq, htY0, card_empty, mul_zero, add_zero]
      · exact card_le_two.trans hA2
      · intro e he
        rcases mem_insert.1 he with rfl | he
        · exact ((hmJ _).1 h).2.1
        · rw [mem_singleton.1 he, CombMap.tail_rev]; exact ((hmJ _).1 h).2.2
    · rw [hcN d h]
      obtain ⟨hdN, hdJ⟩ := mem_sdiff.1 h
      obtain ⟨X, hXI, hdX⟩ := hIcov d hdN fun h' => hdJ ((hmJ d).2 ⟨hdP, h'⟩)
      refine (hw_mono K fun e he => ?_).trans (hIw X hXI)
      have key : ∀ e, ReflTransGen (AStep M N' Hs Y) d e → e ∈ X := by
        intro e he
        induction he with
        | refl => exact hdX
        | tail _ hst ih => exact (hIc X hXI).2 _ ih _ ⟨(mem_sdiff.1 hst.1).1, hst.2⟩
      exact key e (mem_comp.1 he).2
    · by_cases hK : K = 0
      · rw [hcR0 hK d h, hw_eq, hK, zero_mul, add_zero]; exact card_le_two.trans hA2
      · rw [hcR hK d h, hw_eq]
        obtain ⟨⟨H₀, hH₀, h1, -⟩, -, -⟩ := hR1 d h
        have hto : ∀ H ∈ tH M Hs C (R.filter fun e => HRel Hs (M.tail d) (M.tail e)),
            H = H₀ := by
          intro H hH
          obtain ⟨hHs, -, e, he, heH⟩ := mem_tH.1 hH
          have heH₀ : M.tail e ∈ H₀ := hClosed_of_mem hd hH₀ _ h1 _ (mem_filter.1 he).2
          by_contra hne
          exact disjoint_left.1 (disjoint_of_pairwise hd hHs hH₀ hne) heH heH₀
        have hT : (tH M Hs C (R.filter fun e => HRel Hs (M.tail d) (M.tail e))).card ≤ 1 :=
          card_le_one.2 fun H hH H' hH' => by rw [hto H hH, hto H' hH']
        have hc : (R.filter fun e => HRel Hs (M.tail d) (M.tail e)).card ≤ P.card :=
          card_le_card ((filter_subset _ _).trans hRP)
        calc _ ≤ P.card + K * 1 := Nat.add_le_add hc (Nat.mul_le_mul_left _ hT)
          _ ≤ A := by simpa using hKA hK
  -- two classes touch no common hole off the separator
  have htdisj : K ≠ 0 → ∀ X ∈ P.image c, ∀ X' ∈ P.image c, X ≠ X' →
      Disjoint (tH M Hs C X) (tH M Hs C X') := by
    intro hK X hX X' hX' hne
    refine disjoint_left.2 fun H h1 h2 => hne ?_
    obtain ⟨hH, hHC, x, hx, hxH⟩ := mem_tH.1 h1
    obtain ⟨-, -, x', hx', hx'H⟩ := mem_tH.1 h2
    have hoffY : ∀ v ∈ H, v ∉ Y := fun v hv =>
      disjoint_left.1 (disjoint_newHole_of hd hH hHC) hv
    have hxx' : HRel Hs (M.tail x) (M.tail x') := Or.inr ⟨H, hH, hxH, hx'H⟩
    rw [← hcls.eq_of_mem hX hx, ← hcls.eq_of_mem hX' hx']
    have hxJ : x ∉ J := fun h => hoffY _ hxH ((hmJ x).1 h).2.1
    have hx'J : x' ∉ J := fun h => hoffY _ hx'H ((hmJ x').1 h).2.1
    rcases htri x (hXP X hX hx) with h | h | h
    · exact absurd h hxJ
    · rcases htri x' (hXP X' hX' hx') with h' | h' | h'
      · exact absurd h' hx'J
      · have : x' ∈ comp M N' Hs Y x :=
          comp_closed (self_mem_comp h) ⟨h', Or.inr ⟨hxx', hoffY _ hxH⟩⟩
        rw [hcN x h, hcN x' h', comp_eq_of_mem hYc h this]
      · exact absurd hxx' ((hR1 x' h').2.2 x (mem_sdiff.1 h).1)
    · rcases htri x' (hXP X' hX' hx') with h' | h' | h'
      · exact absurd h' hx'J
      · exact absurd (hRel_symm hxx') ((hR1 x h).2.2 x' (mem_sdiff.1 h').1)
      · rw [hcR hK x h, hcR hK x' h']
        ext e
        simp only [mem_filter]
        exact and_congr_right fun _ => ⟨fun h'' => hRel_trans' hd (hRel_symm hxx') h'',
          fun h'' => hRel_trans' hd hxx' h''⟩
  refine ⟨c, hcls, hrevX, hwt, htdisj, fun a haP b hbP ha hb hst => ?_,
    fun d hdP h1 h2 => hcJ d ((hmJ d).2 ⟨hdP, h1, h2⟩)⟩
  have ha' := hinch a haP ha
  rw [hcN a ha']
  exact comp_closed (self_mem_comp ha') ⟨hinch b hbP hb, hst⟩

/-! ### Grouping the classes into two children -/

open Classical in
/-- **The split of a piece from a certificate**: the classes of `exists_cls` grouped into two
children of weight `hw` at most `A` (`exists_two_groups`), and the separator cut into its parts
off the holes (`exists_segs`). There are two classes at least: for `K = 0` since the piece weighs
more than `A`, and for `K ≠ 0` since the piece touches six holes, so that either five holes off the
separator weigh more than `A`, or the separator meets two holes and has a dart. -/
theorem exists_split_of_pcert {S T Q : Finset V} {κ : ℕ} (hSTQ : S ∪ T ⊆ Q) {P : Finset D}
    {Hs : List (Finset V)} (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) {K A L : ℕ}
    (hc : PCert M Q P Hs K A L) (hA2 : 2 ≤ A) (hKA : K ≠ 0 → P.card + K ≤ A)
    (hW : 2 * (P.card + K * nTouch M P Hs) ≤ 3 * A) (hnT : nTouch M P Hs ≤ 6)
    (hbig : K = 0 → A < P.card) (hhole : K ≠ 0 → nTouch M P Hs = 6 ∧ A < 5 * K)
    (hshort : ∀ k, k + 1 ≤ L → k ^ 2 ≤ κ ^ 2 * P.card ∧ 2 * k ≤ P.card) :
    ∃ l r π, SplitOK M S T κ 6 P Hs l r π ∧ CInv M Q l (childHoles Hs π.path.mverts) ∧
      CInv M Q r (childHoles Hs π.path.mverts) ∧ hw M K Hs π.path.mverts l ≤ A ∧
      hw M K Hs π.path.mverts r ≤ A := by
  obtain ⟨Nf, ρ, I, hNf, hout, hρ, hρB, hρL, hlast, hρQ, -, hIc, hIcov, hIw⟩ := hc
  have hd := hP.disj
  obtain ⟨c, hcls, hrevX, hwt, htdisj, hclo, hcJ⟩ :=
    exists_cls hP hNf hout hρ hIc hIcov hIw hA2 hKA
  set C := ρ.mverts with hC
  set Y := newHole Hs C with hY
  set Z := P.image c with hZ
  have hρP : ∀ e ∈ ρ.darts, e ∈ P := fun e he => (mem_core.1 (mem_pdarts.1 (hρB e he)).1).1
  have hXP : ∀ X ∈ Z, X ⊆ P := fun X hX => by
    obtain ⟨d, hd, rfl⟩ := mem_image.1 hX; exact hcls.sub d hd
  -- the total weight
  have hsum : ∑ X ∈ Z, hw M K Hs C X ≤ P.card + K * nTouch M P Hs := by
    simp only [hw_eq, sum_add_distrib, ← mul_sum]
    rw [← hcls.card_biUnion subset_rfl, hcls.biUnion_eq]
    refine Nat.add_le_add_left ?_ _
    rcases eq_or_ne K 0 with hK | hK
    · simp [hK]
    refine Nat.mul_le_mul_left _ ?_
    rw [← Finset.card_biUnion fun X hX X' hX' hne =>
      htdisj hK X (mem_coe.1 hX) X' (mem_coe.1 hX') hne, ← tH_biUnion, hcls.biUnion_eq]
    exact card_tH_le_nTouch P
  -- at least two classes
  have hlow : A < hw M K Hs C P → 2 ≤ Z.card := by
    intro h
    by_contra h'
    have h1 : Z.card ≤ 1 := by omega
    have h2 := hw_biUnion_le (M := M) (Hs := Hs) (C := C) K Z
    rw [hcls.biUnion_eq] at h2
    have h3 : ∑ X ∈ Z, hw M K Hs C X ≤ Z.card * A := by
      simpa using sum_le_card_nsmul Z _ A hwt
    nlinarith
  have h2 : 2 ≤ Z.card := by
    rcases eq_or_ne K 0 with hK | hK
    · apply hlow; rw [hw_eq, hK, zero_mul, add_zero]; exact hbig hK
    obtain ⟨h6, h5K⟩ := hhole hK
    by_cases ht : 5 ≤ (tH M Hs C P).card
    · apply hlow
      rw [hw_eq]
      have := Nat.mul_le_mul_left K ht
      linarith
    push Not at ht
    -- the holes touched by the piece
    set Fall := (Hs.filter fun H => ∃ v ∈ H, Touch M P v).toFinset with hFall
    have hF6 : Fall.card = 6 := by rw [← nTouch_eq_card hd]; exact h6
    have hHs : ∀ H ∈ Fall, H ∈ Hs ∧ ∃ v ∈ H, Touch M P v := fun H hH => by
      simpa [hFall] using hH
    have hdisj : ∀ {H H'}, H ∈ Fall → H' ∈ Fall → H ≠ H' → Disjoint H H' := fun h h' hne =>
      disjoint_of_pairwise hd (hHs _ h).1 (hHs _ h').1 hne
    -- two of them are met by the separator
    have hmet : 1 < (Fall.filter fun H => ¬ Disjoint H C).card := by
      have := card_filter_add_card_filter_not (s := Fall) (fun H => Disjoint H C)
      have hsub : (Fall.filter fun H => Disjoint H C).card ≤ (tH M Hs C P).card := by
        refine card_le_card fun H hH => ?_
        obtain ⟨hH1, hH2⟩ := mem_filter.1 hH
        obtain ⟨hHs', v, hv, x, hx, rfl⟩ := hHs H hH1
        exact mem_tH.2 ⟨hHs', hH2, x, hx, hv⟩
      omega
    obtain ⟨H₁, hH₁, H₂, hH₂, hne⟩ := one_lt_card.1 hmet
    rw [mem_filter] at hH₁ hH₂
    -- so the separator has a dart
    have hk : 0 < ρ.k := by
      by_contra hk0
      have hm : ∀ v ∈ C, v = ρ.p 0 := by
        intro v hv
        rcases ρ.mem_mverts.1 hv with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
        · rw [show j = 0 by omega]
        · omega
      obtain ⟨v₁, hv₁, hv₁C⟩ := not_disjoint_iff.1 hH₁.2
      obtain ⟨v₂, hv₂, hv₂C⟩ := not_disjoint_iff.1 hH₂.2
      rw [hm v₁ hv₁C] at hv₁
      rw [hm v₂ hv₂C] at hv₂
      exact disjoint_left.1 (hdisj hH₁.1 hH₂.1 hne) hv₁ hv₂
    have he₀ : ρ.d 0 ∈ ρ.darts := ρ.mem_darts.2 ⟨0, hk, Or.inl rfl⟩
    have he₀P := hρP _ he₀
    obtain ⟨ht₀, hh₀⟩ := ρ.ends_mem he₀
    have hce₀ : c (ρ.d 0) = {ρ.d 0, M.rev (ρ.d 0)} :=
      hcJ _ he₀P (subset_newHole ht₀) (subset_newHole hh₀)
    -- a touched hole avoids the ends of that dart
    obtain ⟨a, ha, b, hb, c', hc', hab, hac, hbc⟩ := two_lt_card.1 (by omega : 2 < Fall.card)
    have hfree : ∃ H ∈ Fall, M.tail (ρ.d 0) ∉ H ∧ M.head (ρ.d 0) ∉ H := by
      by_contra hcon
      have hc : ∀ H ∈ Fall, M.tail (ρ.d 0) ∉ H → M.head (ρ.d 0) ∈ H := fun H hH h => by
        by_contra h'; exact hcon ⟨H, hH, h, h'⟩
      have d1 : ∀ v, v ∈ a → v ∉ b := fun v hv => disjoint_left.1 (hdisj ha hb hab) hv
      have d2 : ∀ v, v ∈ a → v ∉ c' := fun v hv => disjoint_left.1 (hdisj ha hc' hac) hv
      have d3 : ∀ v, v ∈ b → v ∉ c' := fun v hv => disjoint_left.1 (hdisj hb hc' hbc) hv
      by_cases hxa : M.tail (ρ.d 0) ∈ a
      · exact d3 _ (hc b hb (d1 _ hxa)) (hc c' hc' (d2 _ hxa))
      have hya := hc a ha hxa
      by_cases hxb : M.tail (ρ.d 0) ∈ b
      · exact d2 _ hya (hc c' hc' (d3 _ hxb))
      · exact d1 _ hya (hc b hb hxb)
    obtain ⟨H, hH, hxH, hyH⟩ := hfree
    obtain ⟨-, v, hv, f, hf, rfl⟩ := hHs H hH
    have hfne : f ∉ ({ρ.d 0, M.rev (ρ.d 0)} : Finset D) := by
      intro h
      rcases mem_insert.1 h with h | h
      · rw [h] at hv; exact hxH hv
      · rw [mem_singleton.1 h, CombMap.tail_rev] at hv; exact hyH hv
    refine one_lt_card.2 ⟨c (ρ.d 0), mem_image_of_mem c he₀P, c f, mem_image_of_mem c hf,
      fun h => ?_⟩
    have := hcls.self f hf
    rw [← h, hce₀] at this
    exact hfne this
  -- the grouping
  obtain ⟨G, hGZ, hGne, hGcne, hGA, hGcA⟩ := exists_two_groups Z (hw M K Hs C) h2 hwt hsum hW
  have hGc : Z \ G ⊆ Z := sdiff_subset
  have hrevG : ∀ G' ⊆ Z, RevClosed M (G'.biUnion id) := fun G' hG' e he => by
    obtain ⟨X, hX, he⟩ := mem_biUnion.1 he
    exact mem_biUnion.2 ⟨X, hX, hrevX X (hG' hX) e he⟩
  have hclG : ∀ G' ⊆ Z, ∀ a ∈ G'.biUnion id, ∀ b ∈ P, ¬ Inner M (childHoles Hs C) a →
      ¬ Inner M (childHoles Hs C) b →
      (b = M.rev a ∨ (HRel Hs (M.tail a) (M.tail b) ∧ M.tail a ∉ Y)) → b ∈ G'.biUnion id := by
    intro G' hG' a ha b hb h1 h2 hst
    obtain ⟨X, hX, haX⟩ := mem_biUnion.1 ha
    refine mem_biUnion.2 ⟨X, hX, ?_⟩
    rw [← hcls.eq_of_mem (hG' hX) haX]
    exact hclo a (hXP X (hG' hX) haX) b hb h1 h2 hst
  have hposG : ∀ G' ⊆ Z, G'.Nonempty → 0 < (G'.biUnion id).card := fun G' hG' ⟨X, hX⟩ => by
    obtain ⟨e, he⟩ := hcls.nonempty (hG' hX)
    exact card_pos.2 ⟨e, mem_biUnion.2 ⟨X, hX, he⟩⟩
  have hlr : G.biUnion id ∪ (Z \ G).biUnion id = P := by
    rw [← union_biUnion, union_sdiff_of_subset hGZ, hcls.biUnion_eq]
  have hlrd : Disjoint (G.biUnion id) ((Z \ G).biUnion id) := by
    refine disjoint_left.2 fun e h1 h2 => ?_
    obtain ⟨X, hX, he⟩ := mem_biUnion.1 h1
    obtain ⟨X', hX', he'⟩ := mem_biUnion.1 h2
    have hne : X ≠ X' := fun h => (mem_sdiff.1 hX').2 (h ▸ hX)
    exact disjoint_left.1 (hcls.disj (hGZ hX) (hGc hX') hne) he he'
  -- the parts of the separator
  obtain ⟨segs, hsok, hslen, hsσ⟩ := exists_segs ρ hρ hρP hlast
  have hshort' : HSep.Short κ 6 P.card ⟨ρ, segs⟩ := by
    refine ⟨show segs.length ≤ 6 + 1 by omega, fun σ hσ => hshort σ.k ?_⟩
    have := (hsσ σ hσ).1
    omega
  obtain ⟨hsplit, hIl, hIr⟩ := split_of_closed (π := ⟨ρ, segs⟩) hSTQ hP hI hρ hρB hρQ hsok
    (fun σ hσ => (hsσ σ hσ).2) hshort' hlr hlrd (hposG G hGZ hGne) (hposG _ hGc hGcne)
    (hrevG G hGZ) (hrevG _ hGc) (hclG G hGZ) (hclG _ hGc)
  exact ⟨_, _, ⟨ρ, segs⟩, hsplit, hIl, hIr, (hw_biUnion_le K G).trans hGA,
    (hw_biUnion_le K _).trans hGcA⟩

/-! ### The splits of the large pieces -/

/-- **The certificate of a nonempty piece**, by `pcert_of_core` or `pcert_of_empty`. -/
theorem pcert {S T Q : Finset V} (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) (hP0 : P.Nonempty) (K : ℕ) {A : ℕ}
    (hA : 2 * (P.card + K * nTouch M P Hs) + 2 + 9 * (6 * Nat.sqrt (2 * P.card) + 4) ≤ 3 * A)
    (hA2 : 2 ≤ A) :
    PCert M Q P Hs K A (6 * Nat.sqrt (2 * P.card) + 4) := by
  by_cases hne : (pdarts M (core M Q P) Hs).Nonempty
  · exact pcert_of_core hloopM hQdeg hQ5 hP hI hne K (by omega) hA hA2
  · exact pcert_of_empty hQdeg hQ5 hP hI hP0 (not_nonempty_iff_eq_empty.1 hne) K hA2 (by omega)

/-- The size bounds on large pieces: above `100000` darts, `216 √(2 m) + 164 ≤ m`. -/
lemma sqrt_bound {m : ℕ} (hm : 100000 < m) : 216 * Nat.sqrt (2 * m) + 164 ≤ m := by
  have h := Nat.sqrt_le' (2 * m)
  by_contra h'
  push Not at h'
  nlinarith

/-- The parts of the separators of large pieces are short, with `κ = 9`. -/
lemma short_bound {m k : ℕ} (hm : 100000 < m) (hk : k + 1 ≤ 6 * Nat.sqrt (2 * m) + 4) :
    k ^ 2 ≤ 9 ^ 2 * m ∧ 2 * k ≤ m := by
  have h := Nat.sqrt_le' (2 * m)
  have hb := sqrt_bound hm
  set r := Nat.sqrt (2 * m)
  have hk' : k ≤ 6 * r + 3 := by omega
  refine ⟨?_, by omega⟩
  have : k ^ 2 ≤ (6 * r + 3) ^ 2 := Nat.pow_le_pow_left hk' 2
  nlinarith

/-- **The splits of the large pieces touching at most five holes**: by `exists_split_of_pcert`
with `K = 0`, each child has at most three quarters of the darts. -/
theorem split_size {S T Q : Finset V} (hSTQ : S ∪ T ⊆ Q) (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) (hs : 100000 < P.card)
    (ht : nTouch M P Hs ≤ 5) :
    ∃ l r π, SplitOK M S T 9 6 P Hs l r π ∧ CInv M Q l (childHoles Hs π.path.mverts) ∧
      CInv M Q r (childHoles Hs π.path.mverts) ∧ 4 * l.card ≤ 3 * P.card ∧
      4 * r.card ≤ 3 * P.card := by
  have hb := sqrt_bound hs
  set L := 6 * Nat.sqrt (2 * P.card) + 4 with hL
  set A := (2 * P.card + 2 + 9 * L) / 3 + 1 with hA
  have hP0 : P.Nonempty := card_pos.1 (by omega)
  have hc := pcert hloopM hQdeg hQ5 hP hI hP0 0 (A := A) (by simp only [zero_mul]; omega)
    (by omega)
  obtain ⟨l, r, π, h1, h2, h3, h4, h5⟩ := exists_split_of_pcert (κ := 9) hSTQ hP hI hc (by omega)
    (fun h => absurd rfl h) (by simp only [zero_mul]; omega) (by omega) (fun _ => by omega)
    (fun h => absurd rfl h) (fun k hk => short_bound hs hk)
  rw [hw_eq, zero_mul, add_zero] at h4 h5
  exact ⟨l, r, π, h1, h2, h3, by omega, by omega⟩

/-- **The splits of the large pieces touching six holes**: by `exists_split_of_pcert` with a
weight `K` on the holes larger than a fifth of `A`, each child touches at most four holes off the
separator, and at most five holes. -/
theorem split_hole {S T Q : Finset V} (hSTQ : S ∪ T ⊆ Q) (hloopM : ∀ d, M.head d ≠ M.tail d)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) (hs : 100000 < P.card)
    (ht : nTouch M P Hs = 6) :
    ∃ l r π, SplitOK M S T 9 6 P Hs l r π ∧ CInv M Q l (childHoles Hs π.path.mverts) ∧
      CInv M Q r (childHoles Hs π.path.mverts) ∧
      nTouch M l (childHoles Hs π.path.mverts) ≤ 5 ∧
      nTouch M r (childHoles Hs π.path.mverts) ≤ 5 := by
  have hb := sqrt_bound hs
  set L := 6 * Nat.sqrt (2 * P.card) + 4 with hL
  set K := P.card + 3 * L + 2 with hK
  set A := (2 * (P.card + 6 * K) + 2 + 9 * L) / 3 + 1 with hA
  have hP0 : P.Nonempty := card_pos.1 (by omega)
  have hc := pcert hloopM hQdeg hQ5 hP hI hP0 K (A := A) (by rw [ht]; omega) (by omega)
  have hK0 : K ≠ 0 := by omega
  obtain ⟨l, r, π, h1, h2, h3, h4, h5⟩ := exists_split_of_pcert (κ := 9) hSTQ hP hI hc (by omega)
    (fun _ => by omega) (by rw [ht]; omega) (by omega) (fun h => absurd h hK0)
    (fun _ => ⟨ht, by omega⟩) (fun k hk => short_bound hs hk)
  have hfew : ∀ X : Finset D, hw M K Hs π.path.mverts X ≤ A →
      nTouch M X (childHoles Hs π.path.mverts) ≤ 5 := by
    intro X hX
    refine (nTouch_ch_le hP.disj X).trans ?_
    rw [hw_eq] at hX
    by_contra h
    have h' : 5 ≤ (tH M Hs π.path.mverts X).card := by omega
    have := Nat.mul_le_mul_left K h'
    have : A < 5 * K := by omega
    linarith
  exact ⟨l, r, π, h1, h2, h3, hfew l h4, hfew r h5⟩

/-- **Balanced decompositions from the invariant at the root**: on a plane map without loops
whose terminals are among the vertices `Q` of degree one (no dart joining two of them), with the
invariant `CInv` at the whole map, a decomposition `BalDecA` with `κ = 9`, `η = 6` and
`s = 100000` exists. -/
theorem exists_balDecA_of_cinv (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hloop : ∀ d, M.head d ≠ M.tail d) {S T Q : Finset V} (hSTQ : S ∪ T ⊆ Q)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) (hroot : CInv M Q univ []) :
    ∃ τ : ADec M, BalDecA M S T 9 6 100000 τ :=
  exists_balDecA_of_split hM hrot hface hloop (fun t ht => hQdeg t (hSTQ ht)) (by norm_num)
    (CInv M Q) hroot
    (fun _ _ hP hI hs ht => split_size hSTQ hloop hQdeg hQ5 hP hI hs ht)
    (fun _ _ hP hI hs ht => split_hole hSTQ hloop hQdeg hQ5 hP hI hs ht)

end BKMNW

end PlanarFlow
