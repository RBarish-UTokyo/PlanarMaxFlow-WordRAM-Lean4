module

public import PlanarFlow.BKMNW.Exist

/-!
# The parts of a separator off the holes

A simple path through the holes (`PlanarFlow.BKMNW.HPath.Simple`) is cut by its vertices in the
holes into maximal runs of vertices off the holes; each run is a simple path of `M`
(`HPath.run`). `exists_segs` gives the list of the runs as the parts of the separator off the
holes (`PlanarFlow.BKMNW.HSep.SegOK`): at most one more than the number of holes touching the
piece (the path meets each hole at most once), each of at most as many darts as the path.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
variable {M : CombMap D V F}

namespace HPath

variable {Hs : List (Finset V)} (ρ : HPath M)

/-- The vertices of the path at the indices `a, …, b`, when none is in a hole: a simple path of
`M`. -/
def run (hρ : ρ.Simple Hs) (a b : ℕ) (hb : b ≤ ρ.k) (hab : a ≤ b)
    (hoff : ∀ j, a ≤ j → j ≤ b → ρ.p j ∉ hunion Hs) : SPath M where
  k := b - a
  d i := ρ.d (a + i)
  p i := ρ.p (a + i)
  tail_d i hi := ρ.tail_d _ (by omega)
  head_d i hi := by
    have h := hρ.1 (a + i) (by omega)
    rw [show a + (i + 1) = a + i + 1 by ring]
    exact hRel_eq_of_not_mem (hoff _ (by omega) (by omega)) h
  inj i hi j hj h := by
    have := hρ.2 (a + i) (by omega) (a + j) (by omega) (Or.inl h)
    omega

lemma run_verts (hρ : ρ.Simple Hs) {a b : ℕ} (hb : b ≤ ρ.k) (hab : a ≤ b)
    (hoff : ∀ j, a ≤ j → j ≤ b → ρ.p j ∉ hunion Hs) {v : V} :
    v ∈ (ρ.run hρ a b hb hab hoff).verts ↔ ∃ j, a ≤ j ∧ j ≤ b ∧ ρ.p j = v := by
  rw [SPath.verts, SPath.mem_init]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨a + t, by omega, by simp [run] at ht; omega, rfl⟩
  · rintro ⟨j, h1, h2, rfl⟩; exact ⟨j - a, by simp [run]; omega, by simp [run]; congr 1; omega⟩

/-- **The runs off the holes from the index `s` on**: simple paths of `M` with darts on the path,
pairwise disjoint, off the holes, covering the vertices `p j` off the holes with `s ≤ j`, at most
one more than the vertices `p j` in the holes with `s ≤ j`. -/
lemma exists_runs (hρ : ρ.Simple Hs) : ∀ (n s : ℕ), ρ.k + 1 - s = n →
    ∃ L : List (SPath M),
      (∀ σ ∈ L, σ.k ≤ ρ.k ∧ Disjoint σ.verts (hunion Hs) ∧
        (∀ v ∈ σ.verts, ∃ j, s ≤ j ∧ j ≤ ρ.k ∧ ρ.p j = v) ∧
        (∀ e ∈ σ.darts, e ∈ ρ.darts) ∧ ∃ b ≤ ρ.k, σ.p σ.k = ρ.p b) ∧
      L.Pairwise (fun σ τ => Disjoint σ.verts τ.verts) ∧
      (∀ j, s ≤ j → j ≤ ρ.k → ρ.p j ∉ hunion Hs → ∃ σ ∈ L, ρ.p j ∈ σ.verts) ∧
      L.length ≤ ((Icc s ρ.k).filter fun j => ρ.p j ∈ hunion Hs).card + 1 ∧
      (ρ.k < s → L = []) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn
  by_cases hs : ρ.k < s
  · refine ⟨[], by simp, List.Pairwise.nil, fun j hj hj' _ => by omega, by simp, fun _ => rfl⟩
  push Not at hs
  by_cases hps : ρ.p s ∈ hunion Hs
  · obtain ⟨L, h1, h2, h3, h4, -⟩ := ih (ρ.k + 1 - (s + 1)) (by omega) (s + 1) rfl
    refine ⟨L, fun σ hσ => ?_, h2, fun j hj hj' hp => ?_, ?_, fun h => absurd h (by omega)⟩
    · obtain ⟨a1, a2, a3, a4, a5⟩ := h1 σ hσ
      exact ⟨a1, a2, fun v hv => by obtain ⟨j, hj, hj', e⟩ := a3 v hv; exact ⟨j, by omega, hj', e⟩,
        a4, a5⟩
    · rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · exact absurd hps hp
      · exact h3 j hj hj' hp
    · refine h4.trans (Nat.add_le_add_right (card_le_card fun j hj => ?_) 1)
      simp only [mem_filter, mem_Icc] at hj ⊢; exact ⟨⟨by omega, hj.1.2⟩, hj.2⟩
  -- the run starting at `s`
  have hex : ∃ b, s ≤ b ∧ (ρ.k ≤ b ∨ ρ.p (b + 1) ∈ hunion Hs) := ⟨ρ.k, hs, Or.inl le_rfl⟩
  set b := Nat.find hex with hbdef
  obtain ⟨hb1, hb2⟩ := Nat.find_spec hex
  have hbk : b ≤ ρ.k := Nat.find_le ⟨hs, Or.inl le_rfl⟩
  have hoff : ∀ j, s ≤ j → j ≤ b → ρ.p j ∉ hunion Hs := by
    intro j hj hjb hpj
    rcases Nat.eq_or_lt_of_le hj with rfl | hj'
    · exact hps hpj
    · exact Nat.find_min hex (show j - 1 < b by omega)
        ⟨by omega, Or.inr (by rw [show j - 1 + 1 = j by omega]; exact hpj)⟩
  set σ0 := ρ.run hρ s b hbk hb1 hoff with hσ0
  obtain ⟨L, h1, h2, h3, h4, h5⟩ := ih (ρ.k + 1 - (b + 2)) (by omega) (b + 2) rfl
  have hv0 : ∀ v, v ∈ σ0.verts ↔ ∃ j, s ≤ j ∧ j ≤ b ∧ ρ.p j = v :=
    fun v => ρ.run_verts hρ hbk hb1 hoff
  refine ⟨σ0 :: L, fun σ hσ => ?_, ?_, fun j hj hj' hp => ?_, ?_, fun h => absurd h (by omega)⟩
  · rcases List.mem_cons.1 hσ with rfl | hσ
    · refine ⟨by simp [σ0, HPath.run]; omega, disjoint_left.2 fun v hv hvH => ?_,
        fun v hv => ?_, fun e he => ?_, b, hbk, ?_⟩
      · obtain ⟨j, hj, hjb, rfl⟩ := (hv0 v).1 hv; exact hoff j hj hjb hvH
      · obtain ⟨j, hj, hjb, rfl⟩ := (hv0 v).1 hv; exact ⟨j, hj, by omega, rfl⟩
      · obtain ⟨i, hi, rfl | rfl⟩ := SPath.mem_darts _ |>.1 he
        · exact ρ.mem_darts.2 ⟨s + i, by simp [σ0, HPath.run] at hi; omega, Or.inl rfl⟩
        · exact ρ.mem_darts.2 ⟨s + i, by simp [σ0, HPath.run] at hi; omega, Or.inr rfl⟩
      · simp only [σ0, HPath.run]; congr 1; omega
    · obtain ⟨a1, a2, a3, a4, a5⟩ := h1 σ hσ
      exact ⟨a1, a2, fun v hv => by obtain ⟨j, hj, hj', e⟩ := a3 v hv; exact ⟨j, by omega, hj', e⟩,
        a4, a5⟩
  · refine List.Pairwise.cons (fun τ hτ => disjoint_left.2 fun v hv hv' => ?_) h2
    obtain ⟨i, hi, hib, rfl⟩ := (hv0 v).1 hv
    obtain ⟨j, hj, hjk, e⟩ := (h1 τ hτ).2.2.1 _ hv'
    have := hρ.2 j hjk i (by omega) (Or.inl e)
    omega
  · by_cases hjb : j ≤ b
    · exact ⟨σ0, List.mem_cons_self .., (hv0 _).2 ⟨j, hj, hjb, rfl⟩⟩
    · by_cases hjb1 : j = b + 1
      · subst hjb1
        rcases hb2 with h | h
        · omega
        · exact absurd h hp
      · obtain ⟨σ, hσ, hm⟩ := h3 j (by omega) hj' hp
        exact ⟨σ, List.mem_cons_of_mem _ hσ, hm⟩
  · rw [List.length_cons]
    by_cases hbk' : b = ρ.k
    · rw [h5 (by omega)]; simp
    · have hb2' : ρ.p (b + 1) ∈ hunion Hs := by
        rcases hb2 with h | h
        · omega
        · exact h
      have hsub : insert (b + 1) ((Icc (b + 2) ρ.k).filter fun j => ρ.p j ∈ hunion Hs) ⊆
          (Icc s ρ.k).filter fun j => ρ.p j ∈ hunion Hs := by
        intro j hj
        simp only [mem_insert, mem_filter, mem_Icc] at hj ⊢
        rcases hj with rfl | hj
        · exact ⟨⟨by omega, by omega⟩, hb2'⟩
        · exact ⟨⟨by omega, hj.1.2⟩, hj.2⟩
      have := card_le_card hsub
      rw [card_insert_of_notMem (by simp)] at this
      omega

end HPath

/-- A path through the holes meets at most as many holes as touch the piece of its darts. -/
lemma card_holeIdx_le {P : Finset D} {Hs : List (Finset V)} (ρ : HPath M) (hρ : ρ.Simple Hs)
    (hρP : ∀ e ∈ ρ.darts, e ∈ P) (hlast : ∃ x ∈ P, M.tail x = ρ.p ρ.k) :
    ((Icc 0 ρ.k).filter fun j => ρ.p j ∈ hunion Hs).card ≤ nTouch M P Hs := by
  classical
  have hch : ∀ j ∈ (Icc 0 ρ.k).filter (fun j => ρ.p j ∈ hunion Hs), ∃ H ∈ Hs, ρ.p j ∈ H :=
    fun j hj => mem_hunion.1 (mem_filter.1 hj).2
  choose! f hf using hch
  have htouch : ∀ j ∈ (Icc 0 ρ.k).filter (fun j => ρ.p j ∈ hunion Hs),
      ∃ v ∈ f j, Touch M P v := by
    intro j hj
    have hjk := (mem_Icc.1 (mem_filter.1 hj).1).2
    refine ⟨ρ.p j, (hf j hj).2, ?_⟩
    rcases Nat.lt_or_ge j ρ.k with h | h
    · exact ⟨ρ.d j, hρP _ (ρ.mem_darts.2 ⟨j, h, Or.inl rfl⟩), ρ.tail_d j h⟩
    · obtain ⟨x, hx, e⟩ := hlast
      exact ⟨x, hx, by rw [e, show j = ρ.k by omega]⟩
  have hinj : Set.InjOn f ((Icc 0 ρ.k).filter fun j => ρ.p j ∈ hunion Hs) := by
    intro i hi j hj e
    have hi' := hf i hi
    have hj' := hf j hj
    exact hρ.2 i (mem_Icc.1 (mem_filter.1 hi).1).2 j (mem_Icc.1 (mem_filter.1 hj).1).2
      (Or.inr ⟨f i, hi'.1, hi'.2, by rw [e]; exact hj'.2⟩)
  rw [← card_image_of_injOn hinj]
  unfold nTouch
  refine (card_le_card fun H hH => ?_).trans (List.toFinset_card_le _)
  obtain ⟨j, hj, rfl⟩ := mem_image.1 hH
  rw [List.mem_toFinset, List.mem_filter]
  exact ⟨(hf j hj).1, by simpa using htouch j hj⟩

/-- **The parts of a separator off the holes**: the runs of a simple path through the holes off the
holes, at most one more than the holes touching the piece, each of at most as many darts as the
path, with their darts in the piece and their last vertex touched by it. -/
theorem exists_segs {P : Finset D} {Hs : List (Finset V)} (ρ : HPath M) (hρ : ρ.Simple Hs)
    (hρP : ∀ e ∈ ρ.darts, e ∈ P) (hlast : ∃ x ∈ P, M.tail x = ρ.p ρ.k) :
    ∃ segs : List (SPath M), HSep.SegOK ⟨ρ, segs⟩ Hs ∧ segs.length ≤ nTouch M P Hs + 1 ∧
      ∀ σ ∈ segs, σ.k ≤ ρ.k ∧ (∀ e ∈ σ.darts, e ∈ P) ∧ ∃ x ∈ P, M.tail x = σ.p σ.k := by
  obtain ⟨L, h1, h2, h3, h4, -⟩ := ρ.exists_runs hρ _ 0 rfl
  refine ⟨L, ⟨fun σ hσ => (h1 σ hσ).2.1, List.pairwise_map.2 h2, ?_⟩,
    h4.trans (Nat.add_le_add_right (card_holeIdx_le ρ hρ hρP hlast) 1), fun σ hσ => ?_⟩
  · ext v
    simp only [mem_union, mem_hunion, List.mem_map]
    constructor
    · rintro (h | ⟨_, ⟨σ, hσ, rfl⟩, hv⟩)
      · exact Or.inl h
      · obtain ⟨j, -, hj, rfl⟩ := (h1 σ hσ).2.2.1 v hv
        exact Or.inr (ρ.p_mem_mverts hj)
    · rintro (h | h)
      · exact Or.inl h
      · by_cases hvH : v ∈ hunion Hs
        · exact Or.inl (mem_hunion.1 hvH)
        · right
          rcases ρ.mem_mverts.1 h with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
          · obtain ⟨σ, hσ, hm⟩ := h3 j (Nat.zero_le _) hj hvH
            exact ⟨_, ⟨σ, hσ, rfl⟩, hm⟩
          · have hr := hρ.1 j hj
            have hp : ρ.p (j + 1) ∉ hunion Hs := by
              intro hp
              rcases hr with e | ⟨H, hH, h1, -⟩
              · exact hvH (e ▸ hp)
              · exact hvH (subset_hunion hH h1)
            rw [hRel_eq_of_not_mem hp hr]
            obtain ⟨σ, hσ, hm⟩ := h3 (j + 1) (Nat.zero_le _) hj hp
            exact ⟨_, ⟨σ, hσ, rfl⟩, hm⟩
  · obtain ⟨a1, -, -, a4, b, hb, e⟩ := h1 σ hσ
    refine ⟨a1, fun e he => hρP _ (a4 e he), ?_⟩
    rw [e]
    rcases Nat.lt_or_ge b ρ.k with h | h
    · exact ⟨ρ.d b, hρP _ (ρ.mem_darts.2 ⟨b, h, Or.inl rfl⟩), ρ.tail_d b h⟩
    · obtain ⟨x, hx, e'⟩ := hlast
      exact ⟨x, hx, by rw [e', show b = ρ.k by omega]⟩

end BKMNW

end PlanarFlow
