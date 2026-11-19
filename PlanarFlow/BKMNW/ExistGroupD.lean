module

public import PlanarFlow.BKMNW.ExistGroup
public import PlanarFlow.BKMNW.ExistSegsD

/-!
# The classes and the two groups of a split, as functions

* `PlanarFlow.BKMNW.clsF`: the class function of `exists_cls` (the pairs of darts inside the new
  hole, the components off the new hole of the darts of `Nf`, and the darts inside the other holes
  by pairs or by hole); **`exists_cls'`**: the conclusion of `exists_cls` for it.
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
/-- **The class function of a split** from the darts `Nf` attached to the certificate and the path
`ρ` (new hole `Y = newHole Hs ρ.mverts`, `J` the darts of `P` with both ends in `Y`): `{d, rev d}`
on `J`; the component off `Y` in `Nf \ J` on `Nf`; on the rest `{d, rev d}` if `K = 0`, the darts
of the rest at the same hole otherwise. -/
noncomputable def clsF (P Nf : Finset D) (Hs : List (Finset V)) (K : ℕ) (ρ : HPath M) (d : D) :
    Finset D :=
  if d ∈ P.filter (fun d => M.tail d ∈ newHole Hs ρ.mverts ∧ M.head d ∈ newHole Hs ρ.mverts) then
    {d, M.rev d}
  else if d ∈ Nf then
    comp M (Nf \ P.filter (fun d => M.tail d ∈ newHole Hs ρ.mverts ∧
      M.head d ∈ newHole Hs ρ.mverts)) Hs (newHole Hs ρ.mverts) d
  else if K = 0 then {d, M.rev d}
  else ((P \ Nf) \ P.filter (fun d => M.tail d ∈ newHole Hs ρ.mverts ∧
      M.head d ∈ newHole Hs ρ.mverts)).filter fun e => HRel Hs (M.tail d) (M.tail e)

open Classical in
/-- **`exists_cls` for the explicit class function `clsF`.** -/
theorem exists_cls' {S T : Finset V} {P : Finset D} {Hs : List (Finset V)}
    (hP : PcOK M S T P Hs) {K A : ℕ} {Nf : Finset D} {ρ : HPath M} {I : Finset (Finset D)}
    (hNf : Nf ⊆ P) (hout : ∀ d ∈ P \ Nf, Inner M Hs d ∧ (M.tail d ∉ newHole Hs ρ.mverts →
      ∀ x ∈ Nf, ¬ HRel Hs (M.tail x) (M.tail d))) (hρ : ρ.Simple Hs)
    (hIc : ∀ X ∈ I, X ⊆ Nf ∧ ∀ a ∈ X, ∀ b, AStep M Nf Hs (newHole Hs ρ.mverts) a b → b ∈ X)
    (hIcov : ∀ d ∈ Nf, ¬ (M.tail d ∈ newHole Hs ρ.mverts ∧ M.head d ∈ newHole Hs ρ.mverts) →
      ∃ X ∈ I, d ∈ X)
    (hIw : ∀ X ∈ I, hw M K Hs ρ.mverts X ≤ A) (hA2 : 2 ≤ A) (hKA : K ≠ 0 → P.card + K ≤ A) :
    IsCls P (clsF M P Nf Hs K ρ) ∧ (∀ X ∈ P.image (clsF M P Nf Hs K ρ), ∀ e ∈ X, M.rev e ∈ X) ∧
      (∀ X ∈ P.image (clsF M P Nf Hs K ρ), hw M K Hs ρ.mverts X ≤ A) ∧
      (K ≠ 0 → ∀ X ∈ P.image (clsF M P Nf Hs K ρ), ∀ X' ∈ P.image (clsF M P Nf Hs K ρ), X ≠ X' →
        Disjoint (tH M Hs ρ.mverts X) (tH M Hs ρ.mverts X')) ∧
      (∀ a ∈ P, ∀ b ∈ P, ¬ Inner M (childHoles Hs ρ.mverts) a →
        ¬ Inner M (childHoles Hs ρ.mverts) b →
        (b = M.rev a ∨ (HRel Hs (M.tail a) (M.tail b) ∧ M.tail a ∉ newHole Hs ρ.mverts)) →
        b ∈ clsF M P Nf Hs K ρ a) ∧
      (∀ d ∈ P, M.tail d ∈ newHole Hs ρ.mverts → M.head d ∈ newHole Hs ρ.mverts →
        clsF M P Nf Hs K ρ d = {d, M.rev d}) := by
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
  set c : D → Finset D := clsF M P Nf Hs K ρ with hcdef
  have hceq : ∀ d, c d = if d ∈ J then {d, M.rev d} else if d ∈ Nf then comp M N' Hs Y d else
      if K = 0 then {d, M.rev d} else R.filter fun e => HRel Hs (M.tail d) (M.tail e) :=
    fun d => rfl
  obtain ⟨hcJ, hcN, hcR0, hcR⟩ : (∀ d ∈ J, c d = {d, M.rev d}) ∧
      (∀ d ∈ N', c d = comp M N' Hs Y d) ∧
      (K = 0 → ∀ d ∈ R, c d = {d, M.rev d}) ∧
      (K ≠ 0 → ∀ d ∈ R, c d = R.filter fun e => HRel Hs (M.tail d) (M.tail e)) := by
    refine ⟨fun d h => ?_, fun d h => ?_, fun hK d h => ?_, fun hK d h => ?_⟩ <;> rw [hceq]
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
  refine ⟨hcls, hrevX, hwt, htdisj, fun a haP b hbP ha hb hst => ?_,
    fun d hdP h1 h2 => hcJ d ((hmJ d).2 ⟨hdP, h1, h2⟩)⟩
  have ha' := hinch a haP ha
  rw [hcN a ha']
  exact comp_closed (self_mem_comp ha') ⟨hinch b hbP hb, hst⟩

/-! ### Two groups by a linear scan -/

section TwoGroups

variable {ι : Type*} [DecidableEq ι]

/-- The longest prefix of `l` whose running sum of `ω`, started at `s`, stays at most `A`. -/
def pfx (ω : ι → ℕ) (A : ℕ) : List ι → ℕ → List ι
  | [], _ => []
  | i :: l, s => if s + ω i ≤ A then i :: pfx ω A l (s + ω i) else []

lemma pfx_spec (ω : ι → ℕ) (A : ℕ) : ∀ (l : List ι) (s : ℕ), ∃ t, l = pfx ω A l s ++ t ∧
    (s ≤ A → s + ((pfx ω A l s).map ω).sum ≤ A) ∧
    (∀ j t', t = j :: t' → A < s + ((pfx ω A l s).map ω).sum + ω j)
  | [], s => ⟨[], by simp [pfx], fun h => by simpa [pfx] using h, by simp⟩
  | i :: l, s => by
    by_cases h : s + ω i ≤ A
    · obtain ⟨t, h1, h2, h3⟩ := pfx_spec ω A l (s + ω i)
      refine ⟨t, ?_, fun _ => ?_, fun j t' ht => ?_⟩
      · simp only [pfx, h, ↓reduceIte, List.cons_append]; exact congrArg _ h1
      · have := h2 h; simp only [pfx, h, ↓reduceIte, List.map_cons, List.sum_cons]; omega
      · have := h3 j t' ht; simp only [pfx, h, ↓reduceIte, List.map_cons, List.sum_cons]; omega
    · refine ⟨i :: l, by simp [pfx, h], fun _ => by simp [pfx, h]; omega, fun j t' ht => ?_⟩
      simp only [List.cons.injEq] at ht
      obtain ⟨rfl, -⟩ := ht
      simp [pfx, h]; omega

/-- **The first group of a split into two**, by a scan of the list of items: a single item of
weight above `A / 2` if there is one, otherwise the longest prefix of weight at most `A` (the
first item alone if that is the whole list). -/
def twoGroupsL (ω : ι → ℕ) (A : ℕ) (l : List ι) : List ι :=
  match l.find? (fun i => decide (A < 2 * ω i)) with
  | some i => [i]
  | none => if (pfx ω A l 0).length = l.length then l.take 1 else pfx ω A l 0

lemma sum_toFinset_nodup {l : List ι} (hl : l.Nodup) (ω : ι → ℕ) :
    ∑ i ∈ l.toFinset, ω i = (l.map ω).sum := List.sum_toFinset ω hl

/-- **Two groups by a scan** (`exists_two_groups` for the explicit `twoGroupsL`): items of the
nodup list `l` of weight at most `A` each, of total at most `W` with `2 W ≤ 3 A`, at least two of
them, split into the nonempty groups `S = (twoGroupsL ω A l).toFinset` and `J \ S` of weight at
most `A` each. -/
theorem twoGroups_spec (ω : ι → ℕ) {A W : ℕ} {l : List ι} (hl : l.Nodup) (hJ : 2 ≤ l.length)
    (hω : ∀ i ∈ l, ω i ≤ A) (hW : (l.map ω).sum ≤ W) (hAW : 2 * W ≤ 3 * A) :
    (twoGroupsL ω A l).toFinset ⊆ l.toFinset ∧ (twoGroupsL ω A l).toFinset.Nonempty ∧
      (l.toFinset \ (twoGroupsL ω A l).toFinset).Nonempty ∧
      ∑ i ∈ (twoGroupsL ω A l).toFinset, ω i ≤ A ∧
      ∑ i ∈ l.toFinset \ (twoGroupsL ω A l).toFinset, ω i ≤ A := by
  have htot : ∑ i ∈ l.toFinset, ω i ≤ W := by rw [sum_toFinset_nodup hl]; exact hW
  -- a subset given as a sublist
  have key : ∀ S : Finset ι, S ⊆ l.toFinset → S.Nonempty → (l.toFinset \ S).Nonempty →
      ∑ i ∈ S, ω i ≤ A → ∑ i ∈ S, ω i + A ≥ ∑ i ∈ l.toFinset, ω i →
      S ⊆ l.toFinset ∧ S.Nonempty ∧ (l.toFinset \ S).Nonempty ∧ ∑ i ∈ S, ω i ≤ A ∧
        ∑ i ∈ l.toFinset \ S, ω i ≤ A := by
    intro S hS h1 h2 h3 h4
    refine ⟨hS, h1, h2, h3, ?_⟩
    have := sum_sdiff hS (f := ω)
    omega
  have hsing : ∀ i ∈ l, ({i} : Finset ι) ⊆ l.toFinset ∧ (l.toFinset \ {i}).Nonempty := by
    intro i hi
    refine ⟨singleton_subset_iff.2 (List.mem_toFinset.2 hi), ?_⟩
    rw [← card_pos, card_sdiff_of_subset (singleton_subset_iff.2 (List.mem_toFinset.2 hi)),
      card_singleton, List.toFinset_card_of_nodup hl]
    omega
  unfold twoGroupsL
  rcases hf : l.find? (fun i => decide (A < 2 * ω i)) with _ | i
  · -- no heavy item
    simp only
    have hlight : ∀ i ∈ l, 2 * ω i ≤ A := by
      intro i hi
      have := List.find?_eq_none.1 hf i hi
      simp only [decide_eq_true_eq, not_lt] at this; exact this
    obtain ⟨t, hlt, hsum, hmax⟩ := pfx_spec ω A l 0
    set p := pfx ω A l 0 with hp
    have hpn : (p ++ t).Nodup := hlt ▸ hl
    have hpnd : p.Nodup := (List.nodup_append.1 hpn).1
    have htnd : t.Nodup := (List.nodup_append.1 hpn).2.1
    have hdisj : ∀ a ∈ p, ∀ b ∈ t, a ≠ b := (List.nodup_append.1 hpn).2.2
    have hpsub : p.toFinset ⊆ l.toFinset := fun x hx => by
      rw [List.mem_toFinset] at hx ⊢; rw [hlt]; exact List.mem_append_left _ hx
    have hsdiff : l.toFinset \ p.toFinset = t.toFinset := by
      ext x
      simp only [mem_sdiff, List.mem_toFinset]
      constructor
      · rintro ⟨hx, hxp⟩
        rw [hlt] at hx
        rcases List.mem_append.1 hx with h | h
        · exact absurd h hxp
        · exact h
      · intro hx
        exact ⟨by rw [hlt]; exact List.mem_append_right _ hx, fun hxp => hdisj x hxp x hx rfl⟩
    have hsplit : (l.map ω).sum = (p.map ω).sum + (t.map ω).sum := by
      rw [hlt, List.map_append, List.sum_append]
    by_cases hall : p.length = l.length
    · simp only [hall, ↓reduceIte]
      have ht0 : t = [] := by
        have := congrArg List.length hlt
        rw [List.length_append] at this
        exact List.eq_nil_of_length_eq_zero (by omega)
      obtain ⟨i, l', rfl⟩ : ∃ i l', l = i :: l' := by
        cases l with
        | nil => simp at hJ
        | cons i l' => exact ⟨i, l', rfl⟩
      have hi : i ∈ i :: l' := List.mem_cons_self
      have h1 : (List.take 1 (i :: l')).toFinset = {i} := by simp
      rw [h1]
      obtain ⟨hs1, hs2⟩ := hsing i hi
      refine key {i} hs1 (singleton_nonempty _) hs2 (by simpa using hω i hi) ?_
      rw [sum_toFinset_nodup hl, hsplit, ht0]
      have := hsum (Nat.zero_le _)
      simp only [List.map_nil, List.sum_nil]
      omega
    · simp only [hall, ↓reduceIte]
      obtain ⟨j, t', rfl⟩ : ∃ j t', t = j :: t' := by
        cases t with
        | nil => exact absurd (by rw [hlt, List.append_nil]) hall
        | cons j t' => exact ⟨j, t', rfl⟩
      have hjl : j ∈ l := by rw [hlt]; exact List.mem_append_right _ List.mem_cons_self
      have hm := hmax j t' rfl
      have hjA := hlight j hjl
      have hpne : p.toFinset.Nonempty := by
        rcases p with _ | ⟨a, p'⟩
        · simp only [List.map_nil, List.sum_nil] at hm
          exact absurd (hω j hjl) (by omega)
        · exact ⟨a, by simp⟩
      refine key _ hpsub hpne (by rw [hsdiff]; exact ⟨j, by simp⟩)
        (by rw [sum_toFinset_nodup hpnd]; have := hsum (Nat.zero_le _); omega) ?_
      rw [sum_toFinset_nodup hpnd, sum_toFinset_nodup hl, hsplit]
      have hjt : ω j ≤ (List.map ω (j :: t')).sum := by simp
      have hsum2 : (l.map ω).sum ≤ W := hW
      rw [hsplit] at hsum2
      omega
  · -- a heavy item
    simp only
    have hi : i ∈ l := List.mem_of_find?_eq_some hf
    have hih : A < 2 * ω i := by simpa using List.find?_some hf
    have h1 : [i].toFinset = {i} := by simp
    rw [h1]
    obtain ⟨hs1, hs2⟩ := hsing i hi
    refine key {i} hs1 (singleton_nonempty _) hs2 (by simpa using hω i hi) ?_
    simp only [sum_singleton]
    omega

end TwoGroups

open Classical in
/-- The parts off the holes of a path through the holes (`runsF`; empty if the path is not
simple). -/
noncomputable def segsF (ρ : HPath M) (Hs : List (Finset V)) : List (SPath M) :=
  if h : ρ.Simple Hs then ρ.runsF h 0 else []

/-- The body of `PCert` for named `Nf`, `ρ`, `I`. -/
def PCertOf (Q : Finset V) (P : Finset D) (Hs : List (Finset V)) (K A L : ℕ) (Nf : Finset D)
    (ρ : HPath M) (I : Finset (Finset D)) : Prop :=
    Nf ⊆ P ∧ (∀ d ∈ P \ Nf, Inner M Hs d ∧ (M.tail d ∉ newHole Hs ρ.mverts →
      ∀ x ∈ Nf, ¬ HRel Hs (M.tail x) (M.tail d))) ∧
    ρ.Simple Hs ∧ (∀ e ∈ ρ.darts, e ∈ pdarts M (core M Q P) Hs) ∧ ρ.k + 1 ≤ L ∧
    (∃ x ∈ P, M.tail x = ρ.p ρ.k) ∧ Disjoint ρ.mverts Q ∧
    (∀ X ∈ I, ∀ Y ∈ I, X ≠ Y → Disjoint X Y) ∧
    (∀ X ∈ I, X ⊆ Nf ∧ ∀ a ∈ X, ∀ b, AStep M Nf Hs (newHole Hs ρ.mverts) a b → b ∈ X) ∧
    (∀ d ∈ Nf, ¬ (M.tail d ∈ newHole Hs ρ.mverts ∧ M.head d ∈ newHole Hs ρ.mverts) →
      ∃ X ∈ I, d ∈ X) ∧
    (∀ X ∈ I, hw M K Hs ρ.mverts X ≤ A)

lemma PCertOf.pcert {Q : Finset V} {P : Finset D} {Hs : List (Finset V)} {K A L : ℕ}
    {Nf : Finset D} {ρ : HPath M} {I : Finset (Finset D)} (h : PCertOf (M := M) Q P Hs K A L Nf ρ I) :
    PCert M Q P Hs K A L := ⟨Nf, ρ, I, h⟩

variable (M) in
/-- **The split of a piece from a named certificate**: the classes `clsF` (listed by `lc`), the
first group `twoGroupsL` of them and the rest, and the separator `ρ` with its parts `segsF`. -/
noncomputable def splitOf (P : Finset D) (Hs : List (Finset V)) (K A : ℕ) (Nf : Finset D)
    (ρ : HPath M) (lc : List (Finset D)) : Finset D × Finset D × HSep M :=
  ((twoGroupsL (hw M K Hs ρ.mverts) A lc).toFinset.biUnion id,
    (P.image (clsF M P Nf Hs K ρ) \ (twoGroupsL (hw M K Hs ρ.mverts) A lc).toFinset).biUnion id,
    ⟨ρ, segsF ρ Hs⟩)

open Classical in
/-- **`exists_split_of_pcert` for a named certificate**: from `PCertOf … Nf ρ I` and a nodup list
`lc` of the classes `P.image (clsF M P Nf Hs K ρ)`, the split `splitOf M P Hs K A Nf ρ lc`
meets the conclusion of `exists_split_of_pcert`. -/
theorem exists_split_of_pcert' {S T Q : Finset V} {κ : ℕ} (hSTQ : S ∪ T ⊆ Q) {P : Finset D}
    {Hs : List (Finset V)} (hP : PcOK M S T P Hs) (hI : CInv M Q P Hs) {K A L : ℕ}
    {Nf : Finset D} {ρ : HPath M} {I : Finset (Finset D)}
    (hc : PCertOf (M := M) Q P Hs K A L Nf ρ I) {lc : List (Finset D)}
    (hlc : lc.Nodup ∧ lc.toFinset = P.image (clsF M P Nf Hs K ρ)) (hA2 : 2 ≤ A)
    (hKA : K ≠ 0 → P.card + K ≤ A)
    (hW : 2 * (P.card + K * nTouch M P Hs) ≤ 3 * A) (hnT : nTouch M P Hs ≤ 6)
    (hbig : K = 0 → A < P.card) (hhole : K ≠ 0 → nTouch M P Hs = 6 ∧ A < 5 * K)
    (hshort : ∀ k, k + 1 ≤ L → k ^ 2 ≤ κ ^ 2 * P.card ∧ 2 * k ≤ P.card) :
    SplitOK M S T κ 6 P Hs (splitOf M P Hs K A Nf ρ lc).1 (splitOf M P Hs K A Nf ρ lc).2.1
        (splitOf M P Hs K A Nf ρ lc).2.2 ∧
      CInv M Q (splitOf M P Hs K A Nf ρ lc).1 (childHoles Hs ρ.mverts) ∧
      CInv M Q (splitOf M P Hs K A Nf ρ lc).2.1 (childHoles Hs ρ.mverts) ∧
      hw M K Hs ρ.mverts (splitOf M P Hs K A Nf ρ lc).1 ≤ A ∧
      hw M K Hs ρ.mverts (splitOf M P Hs K A Nf ρ lc).2.1 ≤ A := by
  simp only [splitOf]
  obtain ⟨hNf, hout, hρ, hρB, hρL, hlast, hρQ, -, hIc, hIcov, hIw⟩ := hc
  have hd := hP.disj
  obtain ⟨hcls, hrevX, hwt, htdisj, hclo, hcJ⟩ :=
    exists_cls' hP hNf hout hρ hIc hIcov hIw hA2 hKA
  set c := clsF M P Nf Hs K ρ with hcdef
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
  have hlZ : lc.toFinset = Z := hlc.2
  have hlen : 2 ≤ lc.length := by
    rw [← List.toFinset_card_of_nodup hlc.1, hlZ]; exact h2
  obtain ⟨hGZ, hGne, hGcne, hGA, hGcA⟩ := twoGroups_spec (hw M K Hs C) hlc.1 hlen
    (fun X hX => hwt X (hlZ ▸ List.mem_toFinset.2 hX))
    (by rw [← sum_toFinset_nodup hlc.1, hlZ]; exact hsum) hW
  rw [hlZ] at hGZ hGcne hGcA
  set G := (twoGroupsL (hw M K Hs C) A lc).toFinset with hGdef
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
  obtain ⟨hsok, hslen, hsσ⟩ := exists_segs' ρ hρ hρP hlast
  set segs := ρ.runsF hρ 0 with hsegs
  have hshort' : HSep.Short κ 6 P.card ⟨ρ, segs⟩ := by
    refine ⟨show segs.length ≤ 6 + 1 by omega, fun σ hσ => hshort σ.k ?_⟩
    have := (hsσ σ hσ).1
    omega
  obtain ⟨hsplit, hIl, hIr⟩ := split_of_closed (π := ⟨ρ, segs⟩) hSTQ hP hI hρ hρB hρQ hsok
    (fun σ hσ => (hsσ σ hσ).2) hshort' hlr hlrd (hposG G hGZ hGne) (hposG _ hGc hGcne)
    (hrevG G hGZ) (hrevG _ hGc) (hclG G hGZ) (hclG _ hGc)
  rw [show segsF ρ Hs = segs by simp only [segsF, hρ, ↓reduceDIte, hsegs]]
  exact ⟨hsplit, hIl, hIr, (hw_biUnion_le K G).trans hGA,
    (hw_biUnion_le K _).trans hGcA⟩

end BKMNW

end PlanarFlow
