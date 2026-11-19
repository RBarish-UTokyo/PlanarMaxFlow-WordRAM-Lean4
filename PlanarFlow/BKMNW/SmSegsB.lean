module

public import PlanarFlow.BKMNW.SmSegsA

/-!
# `SegsOut` for the small separator: the meaning

* `cnt_pos_iff`, `cnt_eq_zero_iff`;
* **`segsOut_sm`** (pure): at a node of `smD` (`smD_node_segs`), the four words written by
  `smSegs` from the flags of the path's darts and of the holes met are `SegsOut`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

lemma cnt_pos_iff {F : ℕ → ℕ} {n : ℕ} : 0 < cnt F n ↔ ∃ j < n, 0 < F j := by
  unfold cnt
  rw [card_pos]
  constructor
  · rintro ⟨j, hj⟩
    obtain ⟨h1, h2⟩ := mem_filter.1 hj
    exact ⟨j, mem_range.1 h1, h2⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, mem_filter.2 ⟨mem_range.2 hj, h⟩⟩

lemma cnt_eq_zero_iff {F : ℕ → ℕ} {n : ℕ} : cnt F n = 0 ↔ ∀ j < n, F j = 0 := by
  constructor
  · intro h j hj
    by_contra hne
    have := cnt_pos_iff.2 ⟨j, hj, Nat.pos_of_ne_zero hne⟩
    omega
  · intro h
    by_contra hne
    obtain ⟨j, hj, hp⟩ := cnt_pos_iff.1 (Nat.pos_of_ne_zero hne)
    rw [h j hj] at hp
    omega

/-- **The parts of a node of `smD` from the words of `smSegs`.** -/
theorem segsOut_sm {gid : D → ℕ} {pk : Finset D → D} {S T : Finset V} (hpk : PkMin gid pk)
    {P : Finset D} {Hs : List (Finset V)} (hrc : RevClosed M P) {l r : ADec M} {π : HSep M}
    (hsm : smD M pk S T P Hs = .node l r π) {en : ℕ → D} {m : ℕ}
    (hem : ∀ i < m, en i ∈ pdarts M P Hs) (hes : ∀ y ∈ pdarts M P Hs, ∃ i < m, en i = y)
    (hmono : ∀ i j, i < j → j < m → gid (en i) < gid (en j)) {PF HF mem : ℕ → ℕ}
    (hPF : ∀ i < m, PF i = bf (en i ∈ π.path.darts.toFinset))
    (hHF : ∀ j < Hs.length, HF j = bf (¬ Disjoint (Hs.getD j ∅) π.path.mverts))
    {lo hi Gb : ℕ} (hlo : lo ≤ Gb) (hhi : Gb + 4 ≤ hi)
    (m0 : mem Gb = sgS (cnt PF m) (cnt HF Hs.length)) (m1 : mem (Gb + 1) = 0)
    (m2 : mem (Gb + 2) = sgK (cnt PF m) (cnt HF Hs.length))
    (m3 : ∀ i < m, 0 < PF i → cnt PF i = 0 → mem (Gb + 3) = i) :
    SegsOut M en m π lo hi Gb mem := by
  have hpk' : ∀ X : Finset D, X.Nonempty → pk X ∈ X := fun X hX => (hpk X hX).1
  -- the holes met
  have hH : 0 < cnt HF Hs.length ↔ ∃ H ∈ Hs, ¬ Disjoint H π.path.mverts := by
    rw [cnt_pos_iff]
    constructor
    · rintro ⟨j, hj, h⟩
      rw [hHF j hj] at h
      by_cases h' : Disjoint (Hs.getD j ∅) π.path.mverts
      · unfold bf at h; rw [iteF (not_not.2 h')] at h; omega
      · exact ⟨_, sm_getD_mem hj, h'⟩
    · rintro ⟨H, hH, h⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hH
      refine ⟨j, hj, ?_⟩
      rw [hHF j hj, getD_eq_get hj]
      unfold bf; simp [h]
  -- the darts
  have hP0 : π.path.darts.toFinset = ∅ → cnt PF m = 0 := fun h => by
    rw [cnt_eq_zero_iff]
    intro j hj
    rw [hPF j hj, h]; rfl
  have hP1 : ∀ x ∈ pdarts M P Hs, π.path.darts.toFinset = {x, M.rev x} → 0 < cnt PF m :=
    fun x hx h => by
      obtain ⟨i, hi, rfl⟩ := hes x hx
      rw [cnt_pos_iff]
      refine ⟨i, hi, ?_⟩
      rw [hPF i hi, h]; unfold bf; rw [iteT (mem_insert_self _ _)]; omega
  unfold SegsOut
  rcases smD_node_segs hpk' hrc hsm with ⟨hs, hd, hm⟩ | ⟨⟨x, hx, hd⟩, hm, y, v, hs⟩ |
    ⟨hd, hm, y, v, hs⟩ | ⟨hm, x, hx, hxe, hrx, hxP, hd, hs⟩
  · -- no parts
    have h1 := hP0 hd
    have h2 := hH.2 hm
    rw [hs, m0, sgS_eq, iteT ⟨h1, h2⟩]
    refine ⟨hlo, rfl, by simp only [List.length_nil, List.map_nil, List.sum_nil]; omega,
      fun j hj => absurd hj (by simp)⟩
  · -- one part without darts (peel)
    have h1 := hP1 x hx hd
    have h2 := hH.2 hm
    rw [hs, m0, sgS_eq, iteF (by omega)]
    refine ⟨hlo, rfl, by simp [SPath.point]; omega, fun j hj => ?_⟩
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    refine ⟨by simpa using m1, ?_, fun l hl => absurd hl (by simp [SPath.point])⟩
    rw [show Gb + 1 + [SPath.point (M' := M) y v].length + 0 = Gb + 2 by simp, m2, sgK_eq,
      iteF (by omega)]
    rfl
  · -- one part without darts (a pendant edge at a terminal)
    have h1 := hP0 hd
    have h2 : cnt HF Hs.length = 0 := by
      by_contra h
      obtain ⟨H, hH', hd'⟩ := hH.1 (by omega)
      exact hd' (hm H hH')
    rw [hs, m0, sgS_eq, iteF (by omega)]
    refine ⟨hlo, rfl, by simp [SPath.point]; omega, fun j hj => ?_⟩
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    refine ⟨by simpa using m1, ?_, fun l hl => absurd hl (by simp [SPath.point])⟩
    rw [show Gb + 1 + [SPath.point (M' := M) y v].length + 0 = Gb + 2 by simp, m2, sgK_eq,
      iteF (by omega)]
    rfl
  · -- one part with one dart (an edge)
    have h1 := hP1 x hxP hd
    have h2 : cnt HF Hs.length = 0 := by
      by_contra h
      obtain ⟨H, hH', hd'⟩ := hH.1 (by omega)
      exact hd' (hm H hH')
    obtain ⟨i₀, hi₀, hei⟩ := hes x hxP
    have hgid : gid x < gid (M.rev x) := by
      have := (hpk _ ⟨_, hrx⟩).2 _ hrx
      rw [← hxe] at this
      rcases this.lt_or_eq with h | h
      · exact h
      · exfalso
        obtain ⟨i₁, hi₁, hei₁⟩ := hes (M.rev x) (stable_pdarts hrc Hs _ hxP)
        have hne : M.rev x ≠ x := M.rev_ne x
        rcases lt_trichotomy i₀ i₁ with hlt | rfl | hlt
        · have := hmono _ _ hlt hi₁; rw [hei, hei₁] at this; omega
        · exact hne (hei₁.symm.trans hei)
        · have := hmono _ _ hlt hi₀; rw [hei, hei₁] at this; omega
    have hP₀ : 0 < PF i₀ := by
      rw [hPF i₀ hi₀, hd, hei]; unfold bf; rw [iteT (mem_insert_self _ _)]; omega
    have hc0 : cnt PF i₀ = 0 := by
      rw [cnt_eq_zero_iff]
      intro j hj
      rw [hPF j (by omega), hd]
      unfold bf
      rw [iteF]
      intro hjm
      simp only [mem_insert, mem_singleton] at hjm
      rcases hjm with h | h
      · have := hmono j i₀ hj hi₀; rw [h, hei] at this; omega
      · have := hmono j i₀ hj hi₀; rw [h, hei] at this; omega
    have hm3 := m3 i₀ hi₀ hP₀ hc0
    rw [hs, m0, sgS_eq, iteF (by omega)]
    refine ⟨hlo, rfl, by simp [SPath.ofDart]; omega, fun j hj => ?_⟩
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    refine ⟨by simpa using m1, ?_, fun l hl => ?_⟩
    · rw [show Gb + 1 + [SPath.ofDart x hx].length + 0 = Gb + 2 by simp, m2, sgK_eq,
        iteT ⟨h1, h2⟩]
      rfl
    · have hl0 : l = 0 := by simp [SPath.ofDart] at hl; omega
      subst hl0
      rw [show Gb + 1 + 2 * [SPath.ofDart x hx].length +
          (([SPath.ofDart x hx].take 0).map SPath.k).sum + 0 = Gb + 3 by simp, hm3]
      exact ⟨hi₀, hei⟩

end MfDrv

end BKMNW

end PlanarFlow
