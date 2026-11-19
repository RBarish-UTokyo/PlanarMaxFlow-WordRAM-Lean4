module

public import PlanarFlow.BKMNW.ExistSegs

/-!
# The parts of a separator off the holes, as a function

`HPath.runsF hρ s`: the maximal runs off the holes of a simple path through the holes, from the
index `s` on, by well-founded recursion (`HPath.runEnd`: the end of a run, by `Nat.find`).
**`exists_runs'`**, **`exists_segs'`**: the conclusions of `exists_runs`, `exists_segs` for these
lists.
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

/-- A run off the holes from `s` ends somewhere. -/
lemma runEx (Hs : List (Finset V)) (s : ℕ) (hs : s ≤ ρ.k) :
    ∃ b, s ≤ b ∧ (ρ.k ≤ b ∨ ρ.p (b + 1) ∈ hunion Hs) := ⟨ρ.k, hs, Or.inl le_rfl⟩

/-- **The end of the run from `s`**: the least `b ≥ s` with `b = k` or `p (b + 1)` in a hole. -/
def runEnd (Hs : List (Finset V)) (s : ℕ) (hs : s ≤ ρ.k) : ℕ := Nat.find (ρ.runEx Hs s hs)

lemma runEnd_ge (Hs : List (Finset V)) (s : ℕ) (hs : s ≤ ρ.k) : s ≤ ρ.runEnd Hs s hs :=
  (Nat.find_spec (ρ.runEx Hs s hs)).1

lemma runEnd_next (Hs : List (Finset V)) (s : ℕ) (hs : s ≤ ρ.k) :
    ρ.k ≤ ρ.runEnd Hs s hs ∨ ρ.p (ρ.runEnd Hs s hs + 1) ∈ hunion Hs :=
  (Nat.find_spec (ρ.runEx Hs s hs)).2

lemma runEnd_le (Hs : List (Finset V)) (s : ℕ) (hs : s ≤ ρ.k) : ρ.runEnd Hs s hs ≤ ρ.k :=
  Nat.find_le ⟨hs, Or.inl le_rfl⟩

lemma runEnd_off (Hs : List (Finset V)) (s : ℕ) (hs : s ≤ ρ.k) (hps : ρ.p s ∉ hunion Hs) :
    ∀ j, s ≤ j → j ≤ ρ.runEnd Hs s hs → ρ.p j ∉ hunion Hs := by
  intro j hj hjb hpj
  rcases Nat.eq_or_lt_of_le hj with rfl | hj'
  · exact hps hpj
  · have hjb' : j ≤ Nat.find (ρ.runEx Hs s hs) := hjb
    exact Nat.find_min (ρ.runEx Hs s hs) (show j - 1 < Nat.find (ρ.runEx Hs s hs) by omega)
      ⟨by omega, Or.inr (by rw [show j - 1 + 1 = j by omega]; exact hpj)⟩

/-- **The runs off the holes from the index `s` on**, as a list: skip the vertices in the holes,
take the run up to `runEnd`, continue two indices later. -/
def runsF (hρ : ρ.Simple Hs) (s : ℕ) : List (SPath M) :=
  if hs : ρ.k < s then []
  else if hps : ρ.p s ∈ hunion Hs then runsF hρ (s + 1)
  else ρ.run hρ s (ρ.runEnd Hs s (by omega)) (ρ.runEnd_le Hs s (by omega))
      (ρ.runEnd_ge Hs s (by omega)) (ρ.runEnd_off Hs s (by omega) hps) ::
    runsF hρ (ρ.runEnd Hs s (by omega) + 2)
termination_by ρ.k + 1 - s
decreasing_by
  · omega
  · have := ρ.runEnd_ge Hs s (by omega); omega

lemma runsF_of_lt (hρ : ρ.Simple Hs) {s : ℕ} (hs : ρ.k < s) : ρ.runsF hρ s = [] := by
  rw [runsF]; simp [hs]

lemma runsF_of_mem (hρ : ρ.Simple Hs) {s : ℕ} (hs : s ≤ ρ.k) (hps : ρ.p s ∈ hunion Hs) :
    ρ.runsF hρ s = ρ.runsF hρ (s + 1) := by
  rw [runsF]; simp [show ¬ ρ.k < s by omega, hps]

lemma runsF_of_not_mem (hρ : ρ.Simple Hs) {s : ℕ} (hs : s ≤ ρ.k) (hps : ρ.p s ∉ hunion Hs) :
    ρ.runsF hρ s = ρ.run hρ s (ρ.runEnd Hs s hs) (ρ.runEnd_le Hs s hs) (ρ.runEnd_ge Hs s hs)
      (ρ.runEnd_off Hs s hs hps) :: ρ.runsF hρ (ρ.runEnd Hs s hs + 2) := by
  rw [runsF]; simp [show ¬ ρ.k < s by omega, hps]

/-- **`exists_runs` for the explicit list `runsF hρ s`.** -/
lemma exists_runs' (hρ : ρ.Simple Hs) : ∀ (n s : ℕ), ρ.k + 1 - s = n →
      (∀ σ ∈ ρ.runsF hρ s, σ.k ≤ ρ.k ∧ Disjoint σ.verts (hunion Hs) ∧
        (∀ v ∈ σ.verts, ∃ j, s ≤ j ∧ j ≤ ρ.k ∧ ρ.p j = v) ∧
        (∀ e ∈ σ.darts, e ∈ ρ.darts) ∧ ∃ b ≤ ρ.k, σ.p σ.k = ρ.p b) ∧
      (ρ.runsF hρ s).Pairwise (fun σ τ => Disjoint σ.verts τ.verts) ∧
      (∀ j, s ≤ j → j ≤ ρ.k → ρ.p j ∉ hunion Hs → ∃ σ ∈ ρ.runsF hρ s, ρ.p j ∈ σ.verts) ∧
      (ρ.runsF hρ s).length ≤ ((Icc s ρ.k).filter fun j => ρ.p j ∈ hunion Hs).card + 1 ∧
      (ρ.k < s → ρ.runsF hρ s = []) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn
  by_cases hs : ρ.k < s
  · rw [runsF_of_lt ρ hρ hs]
    refine ⟨by simp, List.Pairwise.nil, fun j hj hj' _ => by omega, by simp, fun _ => rfl⟩
  push Not at hs
  have hs' : ¬ ρ.k < s := by omega
  by_cases hps : ρ.p s ∈ hunion Hs
  · rw [runsF_of_mem ρ hρ hs hps]
    obtain ⟨h1, h2, h3, h4, -⟩ := ih (ρ.k + 1 - (s + 1)) (by omega) (s + 1) rfl
    set L := ρ.runsF hρ (s + 1)
    refine ⟨ fun σ hσ => ?_, h2, fun j hj hj' hp => ?_, ?_, fun h => absurd h (by omega)⟩
    · obtain ⟨a1, a2, a3, a4, a5⟩ := h1 σ hσ
      exact ⟨a1, a2, fun v hv => by obtain ⟨j, hj, hj', e⟩ := a3 v hv; exact ⟨j, by omega, hj', e⟩,
        a4, a5⟩
    · rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · exact absurd hps hp
      · exact h3 j hj hj' hp
    · refine h4.trans (Nat.add_le_add_right (card_le_card fun j hj => ?_) 1)
      simp only [mem_filter, mem_Icc] at hj ⊢; exact ⟨⟨by omega, hj.1.2⟩, hj.2⟩
  -- the run starting at `s`
  rw [runsF_of_not_mem ρ hρ hs hps]
  set b := ρ.runEnd Hs s hs with hbdef
  have hb1 : s ≤ b := ρ.runEnd_ge Hs s hs
  have hb2 : ρ.k ≤ b ∨ ρ.p (b + 1) ∈ hunion Hs := ρ.runEnd_next Hs s hs
  have hbk : b ≤ ρ.k := ρ.runEnd_le Hs s hs
  have hoff : ∀ j, s ≤ j → j ≤ b → ρ.p j ∉ hunion Hs := ρ.runEnd_off Hs s hs hps
  set σ0 := ρ.run hρ s b hbk hb1 hoff with hσ0
  obtain ⟨h1, h2, h3, h4, h5⟩ := ih (ρ.k + 1 - (b + 2)) (by omega) (b + 2) rfl
  set L := ρ.runsF hρ (b + 2)
  have hv0 : ∀ v, v ∈ σ0.verts ↔ ∃ j, s ≤ j ∧ j ≤ b ∧ ρ.p j = v :=
    fun v => ρ.run_verts hρ hbk hb1 hoff
  refine ⟨fun σ hσ => ?_, ?_, fun j hj hj' hp => ?_, ?_, fun h => absurd h (by omega)⟩
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

/-- **`exists_segs` for the explicit list of runs `runsF hρ 0`.** -/
theorem exists_segs' {P : Finset D} {Hs : List (Finset V)} (ρ : HPath M) (hρ : ρ.Simple Hs)
    (hρP : ∀ e ∈ ρ.darts, e ∈ P) (hlast : ∃ x ∈ P, M.tail x = ρ.p ρ.k) :
    HSep.SegOK ⟨ρ, ρ.runsF hρ 0⟩ Hs ∧ (ρ.runsF hρ 0).length ≤ nTouch M P Hs + 1 ∧
      ∀ σ ∈ ρ.runsF hρ 0, σ.k ≤ ρ.k ∧ (∀ e ∈ σ.darts, e ∈ P) ∧ ∃ x ∈ P, M.tail x = σ.p σ.k := by
  obtain ⟨h1, h2, h3, h4, -⟩ := ρ.exists_runs' hρ _ 0 rfl
  set L := ρ.runsF hρ 0
  refine ⟨⟨fun σ hσ => (h1 σ hσ).2.1, List.pairwise_map.2 h2, ?_⟩,
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
