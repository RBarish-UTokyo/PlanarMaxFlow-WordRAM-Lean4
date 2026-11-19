module

public import PlanarFlow.Monge.FRTree

/-!
# The bipartite Monge heap with lazy extraction: the mathematics

This file is the mathematical layer of the bipartite Monge heap of Fakcharoenphol and Rao, in
the form with *lazy extraction* (a target leaves a half block only when the item of that half
block is popped from the global heap; a pop of an already settled target settles nothing).

A half block has the targets (rows) `ρ < nr` and the sources (columns) `σ < nc`; the entry
`E ρ σ = e σ + F ρ σ` is the reduced key offered to `ρ` by the active source `σ`, and `E` is
anti-Monge (`PlanarFlow.Monge.FR.AntiM`). The state of the heap is an **owner map** `own`
(`OwnOK`): every row has an active owner that is not worse than any active source there, and the
owners are antitone in the rows (later rows have earlier owners). The maximal intervals of rows
with the same owner, minus the extracted rows `X`, are the *triplets* of the heap; the item of
the half block is the least `E ρ (own ρ)` over the rows not extracted.

* `own_order_left`, `own_order_right`, `beat_convex`: the rows where a new source is strictly
  better than the owners form an interval, with the earlier owners after it and the later ones
  before it.
* `OwnOK.activate`: activating a source `a` (the rows where it is strictly better change owner)
  keeps the owner map.
* `MHInv`: the invariant with lazy extraction, at the popped key `κ`: the extracted rows keep the
  value they had when they were popped (`frz`). `MHInv.activate`: a source whose values are all at
  least `κ` (Dijkstra with a feasible price function) never changes the owner of an extracted row,
  so the new triplets never contain an extracted row. `MHInv.extract`, `MHInv.raise`.
* `MHInv.lower`: the least value over the rows not extracted is a lower bound of every arc from
  an active source to a row not extracted.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Monge

namespace FR

variable {nr nc : ℕ} {E : ℕ → ℕ → ℝ}

/-- **An owner map** of the active sources `Act`: every row `< nr` has an active owner, not worse
than any active source at this row; the owners are antitone in the rows. -/
structure OwnOK (nr nc : ℕ) (E : ℕ → ℕ → ℝ) (Act : ℕ → Prop) (own : ℕ → ℕ) : Prop where
  lt : ∀ σ, Act σ → σ < nc
  act : ∀ ρ < nr, Act (own ρ)
  best : ∀ ρ < nr, ∀ σ, Act σ → E ρ (own ρ) ≤ E ρ σ
  anti : ∀ ρ ρ', ρ ≤ ρ' → ρ' < nr → own ρ' ≤ own ρ

/-- The owner map after the activation of `a`: the rows where `a` is strictly better change
owner. -/
noncomputable def newOwn (E : ℕ → ℕ → ℝ) (own : ℕ → ℕ) (a : ℕ) (ρ : ℕ) : ℕ :=
  if E ρ a < E ρ (own ρ) then a else own ρ

/-- A later source strictly better at a row is strictly better at the earlier rows. -/
lemma later_down (hA : AntiM nr nc E) {σ σ' ρ ρ' : ℕ} (hσ : σ < σ') (hσ' : σ' < nc)
    (hρ : ρ' ≤ ρ) (hρn : ρ < nr) (h : E ρ σ' < E ρ σ) : E ρ' σ' < E ρ' σ := by
  by_contra h'
  exact absurd (antiM_after hA hσ hσ' hρ hρn (not_lt.1 h')) (not_le.2 h)

/-- An earlier source strictly better at a row is strictly better at the later rows. -/
lemma earlier_up (hA : AntiM nr nc E) {σ σ' ρ ρ' : ℕ} (hσ : σ < σ') (hσ' : σ' < nc)
    (hρ : ρ ≤ ρ') (hρn : ρ' < nr) (h : E ρ σ < E ρ σ') : E ρ' σ < E ρ' σ' := by
  by_contra h'
  exact absurd (antiM_before hA hσ hσ' hρ hρn (not_lt.1 h')) (not_le.2 h)

/-- **Before a row where `a` beats the owners**, the rows where it does not have later
owners. -/
theorem own_order_left (hA : AntiM nr nc E) {Act : ℕ → Prop} {own : ℕ → ℕ}
    (h : OwnOK nr nc E Act own) {a : ℕ} (hna : ¬ Act a) (ha : a < nc) {ρ ρ' : ℕ} (hρ : ρ < nr)
    (hρ' : ρ' < ρ) (hb : E ρ a < E ρ (own ρ)) (hnb : ¬ E ρ' a < E ρ' (own ρ')) :
    a < own ρ' := by
  have hu := h.act ρ' (by omega)
  rcases Nat.lt_trichotomy a (own ρ') with h1 | h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hu) hna
  · -- the owner `u` of `ρ'` is earlier than `a`; `a` beats it at `ρ`, hence at `ρ'`
    exfalso
    have hbu : E ρ a < E ρ (own ρ') := lt_of_lt_of_le hb (h.best ρ hρ _ hu)
    exact hnb (later_down hA h1 ha hρ'.le hρ hbu)

/-- **After a row where `a` beats the owners**, the rows where it does not have earlier
owners. -/
theorem own_order_right (hA : AntiM nr nc E) {Act : ℕ → Prop} {own : ℕ → ℕ}
    (h : OwnOK nr nc E Act own) {a : ℕ} (hna : ¬ Act a) (ha : a < nc) {ρ ρ' : ℕ} (hρ' : ρ' < nr)
    (hρ : ρ < ρ') (hb : E ρ a < E ρ (own ρ)) (hnb : ¬ E ρ' a < E ρ' (own ρ')) : own ρ' < a := by
  have hu := h.act ρ' hρ'
  rcases Nat.lt_trichotomy (own ρ') a with h1 | h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hu) hna
  · exfalso
    have hbu : E ρ a < E ρ (own ρ') := lt_of_lt_of_le hb (h.best ρ (by omega) _ hu)
    exact hnb (earlier_up hA h1 (h.lt _ hu) hρ.le hρ' hbu)

/-- **The rows where a new source beats the owners form an interval.** -/
theorem beat_convex (hA : AntiM nr nc E) {Act : ℕ → Prop} {own : ℕ → ℕ}
    (h : OwnOK nr nc E Act own) {a : ℕ} (hna : ¬ Act a) (ha : a < nc) {ρ₁ ρ₂ ρ₃ : ℕ}
    (h12 : ρ₁ ≤ ρ₂) (h23 : ρ₂ ≤ ρ₃) (h3 : ρ₃ < nr) (b₁ : E ρ₁ a < E ρ₁ (own ρ₁))
    (b₃ : E ρ₃ a < E ρ₃ (own ρ₃)) : E ρ₂ a < E ρ₂ (own ρ₂) := by
  by_contra hnb
  rcases Nat.eq_or_lt_of_le h12 with e | h12'
  · exact hnb (e ▸ b₁)
  rcases Nat.eq_or_lt_of_le h23 with e | h23'
  · exact hnb (e ▸ b₃)
  have l := own_order_left hA h hna ha h3 h23' b₃ hnb
  have r := own_order_right hA h hna ha (by omega) h12' b₁ hnb
  omega

/-- **Activating a source keeps the owner map.** -/
theorem OwnOK.activate (hA : AntiM nr nc E) {Act : ℕ → Prop} {own : ℕ → ℕ}
    (h : OwnOK nr nc E Act own) {a : ℕ} (hna : ¬ Act a) (ha : a < nc) :
    OwnOK nr nc E (fun σ => Act σ ∨ σ = a) (newOwn E own a) := by
  refine ⟨fun σ hσ => ?_, fun ρ hρ => ?_, fun ρ hρ σ hσ => ?_, fun ρ ρ' hle hρ' => ?_⟩
  · rcases hσ with hσ | rfl
    · exact h.lt σ hσ
    · exact ha
  · unfold newOwn; split_ifs
    · exact Or.inr rfl
    · exact Or.inl (h.act ρ hρ)
  · unfold newOwn
    split_ifs with hb
    · rcases hσ with hσ | rfl
      · exact hb.le.trans (h.best ρ hρ σ hσ)
      · exact le_rfl
    · rcases hσ with hσ | rfl
      · exact h.best ρ hρ σ hσ
      · exact not_lt.1 hb
  · unfold newOwn
    by_cases b : E ρ a < E ρ (own ρ)
    · by_cases b' : E ρ' a < E ρ' (own ρ')
      · rw [iteT b, iteT b']
      · rw [iteT b, iteF b']
        rcases Nat.eq_or_lt_of_le hle with e | hlt
        · exact absurd (e ▸ b) b'
        · exact (own_order_right hA h hna ha hρ' hlt b b').le
    · by_cases b' : E ρ' a < E ρ' (own ρ')
      · rw [iteF b, iteT b']
        rcases Nat.eq_or_lt_of_le hle with e | hlt
        · exact absurd (e ▸ b') b
        · exact (own_order_left hA h hna ha hρ' hlt b' b).le
      · rw [iteF b, iteF b']; exact h.anti ρ ρ' hle hρ'

/-! ### Lazy extraction -/

/-- **The invariant of a half block with lazy extraction**, at the popped key `κ`: an owner map,
and the extracted rows `X` kept their value, at most `κ`. -/
structure MHInv (nr nc : ℕ) (E : ℕ → ℕ → ℝ) (Act : ℕ → Prop) (own : ℕ → ℕ) (X : ℕ → Prop)
    (κ : ℝ) : Prop where
  ok : OwnOK nr nc E Act own
  frz : ∀ ρ < nr, X ρ → E ρ (own ρ) ≤ κ

/-- **Activating a source whose values are all at least `κ`** keeps the invariant, and changes
the owner of no extracted row: the new triplet contains no extracted row. -/
theorem MHInv.activate (hA : AntiM nr nc E) {Act : ℕ → Prop} {own : ℕ → ℕ} {X : ℕ → Prop}
    {κ : ℝ} (h : MHInv nr nc E Act own X κ) {a : ℕ} (hna : ¬ Act a) (ha : a < nc)
    (hκ : ∀ ρ < nr, κ ≤ E ρ a) :
    MHInv nr nc E (fun σ => Act σ ∨ σ = a) (newOwn E own a) X κ ∧
      ∀ ρ < nr, X ρ → newOwn E own a ρ = own ρ := by
  have hkeep : ∀ ρ < nr, X ρ → newOwn E own a ρ = own ρ := fun ρ hρ hX => by
    unfold newOwn
    rw [iteF (not_lt.2 ((h.frz ρ hρ hX).trans (hκ ρ hρ)))]
  exact ⟨⟨h.ok.activate hA hna ha, fun ρ hρ hX => by rw [hkeep ρ hρ hX]; exact h.frz ρ hρ hX⟩,
    hkeep⟩

/-- **Extracting a row whose value is at most the new popped key `κ'`** keeps the invariant. -/
theorem MHInv.extract {Act : ℕ → Prop} {own : ℕ → ℕ} {X : ℕ → Prop} {κ κ' : ℝ}
    (h : MHInv nr nc E Act own X κ) (hκ : κ ≤ κ') {ρ₀ : ℕ} (h₀ : E ρ₀ (own ρ₀) ≤ κ') :
    MHInv nr nc E Act own (fun ρ => X ρ ∨ ρ = ρ₀) κ' :=
  ⟨h.ok, fun ρ hρ hX => by
    rcases hX with hX | rfl
    · exact (h.frz ρ hρ hX).trans hκ
    · exact h₀⟩

/-- Raising the popped key keeps the invariant. -/
theorem MHInv.raise {Act : ℕ → Prop} {own : ℕ → ℕ} {X : ℕ → Prop} {κ κ' : ℝ}
    (h : MHInv nr nc E Act own X κ) (hκ : κ ≤ κ') : MHInv nr nc E Act own X κ' :=
  ⟨h.ok, fun ρ hρ hX => (h.frz ρ hρ hX).trans hκ⟩

/-- **The item of a half block bounds every arc into a row not extracted**: if `m` is at most
the value of every row not extracted, it is at most `E ρ σ` for every such row and every active
source. -/
theorem MHInv.lower {Act : ℕ → Prop} {own : ℕ → ℕ} {X : ℕ → Prop} {κ m : ℝ}
    (h : MHInv nr nc E Act own X κ) (hm : ∀ ρ < nr, ¬ X ρ → m ≤ E ρ (own ρ)) {ρ σ : ℕ}
    (hρ : ρ < nr) (hX : ¬ X ρ) (hσ : Act σ) : m ≤ E ρ σ :=
  (hm ρ hρ hX).trans (h.ok.best ρ hρ σ hσ)

end FR

end Monge

end PlanarFlow
