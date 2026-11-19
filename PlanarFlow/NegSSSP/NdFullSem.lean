module

public import PlanarFlow.NegSSSP.NdFull
public import PlanarFlow.NegSSSP.KEncConcrete
public import PlanarFlow.NegSSSP.Enc.NodeDec

/-!
# The full branch of the node step: the semantic side

* **`nd_full_pot`**: the outcome of the fixed node (`node_exec_fixedD`: a `PotOut` outcome `o`
  of the union of the two dense distance graphs, and the step of the recursion for any
  Bellman–Ford returning `o`) is a `PotOut` outcome of the piece `P₀ ∪ P₁`: the reference
  Bellman–Ford `bfRef` patched to return `o` on the two graphs meets `BFDDGSpec`, so
  `step_potOut` applies.
* **`msplit_cut`**: in the large case the machine's split is the cut pair of the large
  component (`cutPair P K A₀`, from the side array that `BigOut` describes).
* **`cut_parts`**: the two parts of a cut pair are `side N K Z ∪ R₀` and `side N K Zᶜ ∪ R₁` with
  `R₀`, `R₁` (one of them `P \ K`, the other `∅`) sharing no vertex with `K`; **`cut_bdry`**:
  the shared vertices of the parts are those of the cut; **`cut_k_sq`**: the face length bound
  `C.k² ≤ 1200 m` of the instances.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset BKMNW

section Pot

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {N : CombMap D V F}

/-- **The outcome of the fixed node is a `PotOut` outcome of the piece** (see the module
docstring); `Q` and `R` carry the machine facts of the two cases. -/
theorem nd_full_pot {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {P₀ P₁ : Finset D} {ℓ : D → ℤ} {δ₀ δ₁ : V → ℤ} (hδ₀ : (pg N P₀ ℓ).IsPot δ₀)
    (hδ₁ : (pg N P₁ ℓ).IsPot δ₁) {o : Option (V → ℤ)} {Q : Prop} {R : (V → ℤ) → Prop}
    (hpo : PotOut ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).join
      (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁))) o)
    (hst : ∀ bf : DDG V → DDG V → Option (V → ℤ),
      bf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) =
        o →
      (step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = none ∧ Q) ∨
      (∃ f, step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = some f ∧ R f)) :
    (PotOut (pg N (P₀ ∪ P₁) ℓ) none ∧ Q) ∨ (∃ f, (pg N (P₀ ∪ P₁) ℓ).IsPot f ∧ R f) := by
  classical
  set H₀ := childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁) with hH₀
  set H₁ := childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁) with hH₁
  let bf : DDG V → DDG V → Option (V → ℤ) := fun A B =>
    if A = H₀ ∧ B = H₁ then o else bfRef A B
  have hbf : BFDDGSpec bf := fun A B => by
    by_cases h : A = H₀ ∧ B = H₁
    · obtain ⟨rfl, rfl⟩ := h
      simp only [bf, and_self, ite_true]
      exact hpo
    · simp only [bf, h, ite_false]
      exact bfRef_spec A B
  have he : bf H₀ H₁ = o := by simp [bf]
  have hp := step_potOut (fr := fr) (ℓ := ℓ) hmssp hbf hfr hδ₀ hδ₁
  rcases hst bf he with ⟨h1, h2⟩ | ⟨f, h1, h2⟩
  · left
    rw [h1] at hp
    exact ⟨hp, h2⟩
  · right
    rw [h1] at hp
    exact ⟨f, hp, h2⟩

end Pot

section Cut

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- **The parts of a cut pair**: `A₀ ∪ R₀` and `(K \ A₀) ∪ R₁`, one of `R₀`, `R₁` being `P \ K`
and the other `∅`. -/
theorem cut_parts (P K A₀ : Finset D) :
    ∃ R₀ R₁ : Finset D, (cutPair P K A₀).1 = A₀ ∪ R₀ ∧ (cutPair P K A₀).2 = (K \ A₀) ∪ R₁ ∧
      (R₀ = P \ K ∨ R₀ = ∅) ∧ (R₁ = P \ K ∨ R₁ = ∅) := by
  unfold cutPair
  split_ifs
  · exact ⟨P \ K, ∅, rfl, by simp, Or.inl rfl, Or.inr rfl⟩
  · exact ⟨∅, P \ K, by simp, rfl, Or.inr rfl, Or.inl rfl⟩

theorem disj_R {P K R : Finset D} (hRd : Disjoint (verts N (P \ K)) (verts N K))
    (hR : R = P \ K ∨ R = ∅) : Disjoint (verts N R) (verts N K) := by
  rcases hR with rfl | rfl
  · exact hRd
  · simp [verts]

/-- **The shared vertices of the parts of a cut pair are those of the cut.** -/
theorem cut_bdry {P K A₀ : Finset D} (hA : A₀ ⊆ K)
    (hRd : Disjoint (verts N (P \ K)) (verts N K)) :
    bdry N (cutPair P K A₀).1 (cutPair P K A₀).2 = bdry N A₀ (K \ A₀) := by
  have hv₀ : Disjoint (verts N (P \ K)) (verts N A₀) := hRd.mono_right (verts_mono hA)
  have hv₁ : Disjoint (verts N (P \ K)) (verts N (K \ A₀)) := hRd.mono_right (verts_mono sdiff_subset)
  unfold cutPair
  split_ifs
  · exact bdry_union_right hv₁
  · rw [bdry_comm, bdry_union_right hv₀, bdry_comm]

/-- The face length bound of the cut. -/
theorem cut_k_sq {P K : Finset D} {c : ℕ} (hs : 1000000 < P.card) (hKP : K ⊆ P)
    (hc : c ≤ 6 * Nat.sqrt (12 * K.card) + 4) : c ^ 2 ≤ 1200 * P.card := by
  have hK : K.card ≤ P.card := card_le_card hKP
  have hc' : c ≤ 6 * Nat.sqrt (12 * P.card) + 4 :=
    hc.trans (by have := Nat.sqrt_le_sqrt (Nat.mul_le_mul_left 12 hK); omega)
  exact (Nat.pow_le_pow_left (by omega) 2).trans (succ_sq_cut_le (by omega) hc')

end Cut

namespace Frame

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {g : GIds D V} {N : CombMap D V F}

/-- **In the large case the machine's split is the cut pair** of the large component. -/
theorem msplit_cut {P K A₀ : Finset D} (hs : 1000000 < P.card) (hKP : K ⊆ P)
    (hRd : Disjoint (verts N (P \ K)) (verts N K)) (hbig : 3 * P.card / 4 < K.card)
    (hcut : CutOK N K A₀)
    (hside : ∀ x < P.card, (spFin g N P).nmem (spB0 (ck N P) + 41 * ck N P + 4 + x) =
      if cδ g N P x ∈ (cutPair P K A₀).1 then 0 else 1) :
    msplit g N P = cutPair P K A₀ := by
  obtain ⟨hu, hd, -⟩ := splitF_cutPair hs hKP hRd hbig hcut
  have e1 : (msplit g N P).1 = (cutPair P K A₀).1 := by
    ext d
    simp only [msplit, mem_filter]
    constructor
    · rintro ⟨hdP, h0⟩
      obtain ⟨hx, hδ⟩ := cδ_idxOf (g := g) (N := N) hdP
      rw [hside _ hx, hδ] at h0
      split_ifs at h0 with h
      exact h
    · intro h
      have hdP : d ∈ P := hu ▸ mem_union_left _ h
      obtain ⟨hx, hδ⟩ := cδ_idxOf (g := g) (N := N) hdP
      refine ⟨hdP, ?_⟩
      rw [hside _ hx, hδ]
      simp only [h, ite_true]
  have e2 : (msplit g N P).2 = (cutPair P K A₀).2 := by
    ext d
    simp only [msplit, mem_filter]
    constructor
    · rintro ⟨hdP, h0⟩
      obtain ⟨hx, hδ⟩ := cδ_idxOf (g := g) (N := N) hdP
      rw [hside _ hx, hδ] at h0
      have h1 : d ∉ (cutPair P K A₀).1 := fun h => h0 (by simp only [h, ite_true])
      rw [← hu] at hdP
      rcases mem_union.1 hdP with h | h
      · exact absurd h h1
      · exact h
    · intro h
      have hdP : d ∈ P := hu ▸ mem_union_right _ h
      obtain ⟨hx, hδ⟩ := cδ_idxOf (g := g) (N := N) hdP
      refine ⟨hdP, ?_⟩
      have h1 : d ∉ (cutPair P K A₀).1 := fun h' => disjoint_left.1 hd h' h
      rw [hside _ hx, hδ]
      simp only [h1, ite_false]
      exact one_ne_zero
  exact Prod.ext e1 e2

end Frame

end NegSSSP

end PlanarFlow
