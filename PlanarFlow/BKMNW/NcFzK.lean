module

public import PlanarFlow.BKMNW.NcFzJ

/-!
# `fzP` at a node call: the facts on the parts and the pendant flow

* `segsP_p0` (the start vertex of a transported part), `map_k_segsP`, `take_map_k_segsP`;
* **`segsL_of`**: at a call with a frame, `SegsOut'` (top-level darts) gives `SegsL` of the
  piece map on the frame's dart order (`layEn`) for the parts `segsP h π.segs _`;
* **`frFlow_pseudo`**: `frFlow f₁ Del` is a pseudoflow of the map with pendant edges for
  `frCap U f₁ Del` (the step of `fixFrozen_spec`'s proof, exposed).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine MfDrv NsStep

section Parts

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F} {P : Finset D} {Hs : List (Finset V)}
  {σ : Perm D}

/-- **The start vertex of a transported part.** -/
theorem segsP_p0 (h : PieceInv M P Hs σ) :
    ∀ (L : List (SPath M)) (hL : ∀ π ∈ L, SegIn M P Hs π) (j : ℕ) (πj : SPath (pmap h)),
      (segsP h L hL)[j]? = some πj →
      ∃ hj : j < L.length, ∀ (x : D) (hx : x ∈ pdarts M P Hs), M.tail x = (L[j]).p 0 →
        (pmap h).tail ⟨x, hx⟩ = πj.p 0
  | [], _, j, πj, e => by simp [segsP] at e
  | π :: L, hL, 0, πj, e => by
      simp only [segsP, List.getElem?_cons_zero, Option.some.injEq] at e
      subst e
      refine ⟨by simp, fun x hx hxt => ?_⟩
      apply Quotient.sound
      show σ.SameCycle x _
      refine (h.vert _ hx _ (SPath.pdart π _ _ 0).2).2 (Or.inl ?_)
      rw [SPath.tail_pdart (hj := Nat.zero_le _)]
      · exact hxt
      · exact (hL π (List.mem_cons_self ..)).1.choose_spec
  | π :: L, hL, j + 1, πj, e => by
      simp only [segsP, List.getElem?_cons_succ] at e
      obtain ⟨hj, h1⟩ := segsP_p0 h L _ j πj e
      exact ⟨by simp; omega, fun x hx hxt => h1 x hx (by simpa using hxt)⟩

lemma map_k_segsP (h : PieceInv M P Hs σ) :
    ∀ (L : List (SPath M)) (hL : ∀ π ∈ L, SegIn M P Hs π),
      (segsP h L hL).map SPath.k = L.map SPath.k
  | [], _ => rfl
  | π :: L, hL => by
      rw [segsP, List.map_cons, List.map_cons, map_k_segsP h L]
      rfl

lemma take_map_k_segsP (h : PieceInv M P Hs σ) (L : List (SPath M))
    (hL : ∀ π ∈ L, SegIn M P Hs π) (j : ℕ) :
    ((segsP h L hL).take j).map SPath.k = (L.take j).map SPath.k := by
  rw [List.map_take, List.map_take, map_k_segsP]

end Parts

section Call

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The parts in the piece map's layout** (see the module docstring). -/
theorem segsL_of {l r : ADec M} {π : HSep M} {Hs : List (Finset V)} {σ : Perm D}
    (h : SCond M l r π Hs σ) {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
    (hL : Lay M gid u S T Z (.node l r π, Hs, σ) m en d mem) (hm : 0 < m) {lo hi Gb : ℕ}
    (hS : SegsOut' M en m π lo hi Gb mem) :
    SegsL (pmap h.1) (layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm) m
      (segsP h.1 π.segs h.2) lo hi Gb mem := by
  obtain ⟨⟨s1, s2, s3, s4⟩, t1, t2⟩ := hS
  have hlen := length_segsP h.1 π.segs h.2
  have hmk := map_k_segsP h.1 π.segs h.2
  refine ⟨s1, by rw [hlen]; exact s2, by rw [hlen, hmk]; exact t1, fun j hj => ?_⟩
  have hj' : j < π.segs.length := hlen ▸ hj
  obtain ⟨u1, u2, u3⟩ := s4 j hj'
  obtain ⟨v1, v2⟩ := t2 j hj'
  have hget : (segsP h.1 π.segs h.2)[j]? = some (segsP h.1 π.segs h.2)[j] :=
    List.getElem?_eq_getElem hj
  obtain ⟨hj2, k1, k2⟩ := segsP_get h.1 π.segs h.2 j _ hget
  obtain ⟨hj3, p1⟩ := segsP_p0 h.1 π.segs h.2 j _ hget
  rw [hlen, take_map_k_segsP, hmk]
  refine ⟨u1, by rw [k1]; exact u2, fun q hq => ?_, v1, ?_⟩
  · rw [k1] at hq
    obtain ⟨w1, w2⟩ := u3 q hq
    exact ⟨w1, Subtype.ext ((layEn_val w1).trans (w2.trans (k2 q (k1 ▸ hq)).symm))⟩
  · have hx := hL.en_mem _ v1
    rw [show layEn (pdarts M (l.piece ∪ r.piece) Hs) en m hL.en_mem hm
      (mem (Gb + 1 + 2 * π.segs.length + (π.segs.map SPath.k).sum + j)) = ⟨_, hx⟩ from
      Subtype.ext (layEn_val v1)]
    exact p1 _ hx v2

end Call

section Pseudo

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The initial flow of the pendant run is a pseudoflow.** -/
theorem frFlow_pseudo (e : V → D) (he : ∀ v, M.tail (e v) = v) {U f₁ : D → ℤ}
    (hf₁ : IsPseudo M U f₁) (Del : Finset V) :
    IsPseudo (M.pendant e he) (frCap M U f₁ Del) (frFlow M f₁ Del) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro (d | ⟨v, _ | _⟩)
    · show frFlow M f₁ Del (.inl (M.rev d)) = _
      simp only [frFlow, rev_mem_incSet, hf₁.antisymm d]
      split_ifs <;> simp
    · show frFlow M f₁ Del (.inr (v, true)) = _
      simp [frFlow]
    · show frFlow M f₁ Del (.inr (v, false)) = _
      simp [frFlow]
  · rintro (d | ⟨v, _ | _⟩)
    · simp only [frFlow, frCap]; split_ifs
      · exact le_rfl
      · exact hf₁.le_cap d
    · exact le_max_left _ _
    · exact le_max_left _ _

lemma frCap_nonneg {U f₁ : D → ℤ} (hU : ∀ d, 0 ≤ U d) (Del : Finset V) (x : D ⊕ (V × Bool)) :
    0 ≤ frCap M U f₁ Del x := by
  rcases x with d | ⟨v, _ | _⟩
  · simp only [frCap]; split_ifs
    · exact le_rfl
    · exact hU d
  · exact le_max_right _ _
  · exact le_max_right _ _

end Pseudo

end NcFz

end BKMNW

end PlanarFlow
