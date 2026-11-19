module

public import PlanarFlow.NegSSSP.FaceSplit

/-!
# The split by a short simple cycle, from a given separator of the subdivided piece

`PlanarFlow.NegSSSP.exists_cycle_cut` takes the simple cycle `C` and the faces `Z` of the
stellar subdivision `kst N K` of the piece map from `exists_short_cycle_separator_card`; here
they are arguments (`exists_cycle_cut_of`), with the parts `side N K Z` and `side N K Zᶜ`
explicit, so that a separator computed by the machine
(`PlanarSeparator.MillerProg.sepOut_sep`) gives the split. The proof is that of
`exists_cycle_cut`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW

section Cut

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

variable {N : CombMap D V F}

open Classical in
/-- **The split of a connected piece by a given short simple cycle** of its subdivided piece map
`kst N K`, with the conclusion of `exists_short_cycle_separator_card` for the old darts of `K`:
the parts `side N K Z` and `side N K Zᶜ` meet the conclusion of `exists_cycle_cut` with
`c = C.k`. -/
theorem exists_cycle_cut_of (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {K : Finset D} (hKr : K ⊆ reps N) (hK0 : K.Nonempty) (hK : DConn N K)
    {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}
    (hk : C.k ≤ 6 * Nat.sqrt (3 * Fintype.card (SVert (kσ N K) (rcl N K) ⊕ (kmap N K).Face)) + 4)
    (hsep : IsCycleSep C Z (sideIn C Z) (sideOut C Z))
    (hin : 3 * #{δ ∈ (K.subtype (· ∈ rcl N K)).image old | (kst N K).face δ ∈ Z ∧ ¬ C.Mem δ} ≤
      2 * #((K.subtype (· ∈ rcl N K)).image old) + 6 * C.k)
    (hout : 3 * #{δ ∈ (K.subtype (· ∈ rcl N K)).image old | (kst N K).face δ ∉ Z ∧ ¬ C.Mem δ} ≤
      2 * #((K.subtype (· ∈ rcl N K)).image old) + 6 * C.k) :
    side N K Z ∪ side N K Zᶜ = K ∧ Disjoint (side N K Z) (side N K Zᶜ) ∧
      C.k ≤ 6 * Nat.sqrt (12 * K.card) + 4 ∧
      3 * (side N K Z).card ≤ 2 * K.card + 12 * C.k ∧
      3 * (side N K Zᶜ).card ≤ 2 * K.card + 12 * C.k ∧
      (bdry N (side N K Z) (side N K Zᶜ)).card ≤ C.k ∧
      ∀ R : Finset D, Disjoint (verts N R) (verts N K) →
        OneFace N (side N K Z ∪ R) (bdry N (side N K Z) (side N K Zᶜ)) (18 * K.card) C.k ∧
        OneFace N (side N K Zᶜ ∪ R) (bdry N (side N K Z) (side N K Zᶜ)) (18 * K.card) C.k := by
  classical
  obtain ⟨ψ, hψ⟩ := exists_kψ hrot hK0
  have hS := kmap_isPlane hM hrot hface hK0 hK
  have hl := kmap_loopless hrot hKr
  obtain ⟨x₀, hx₀⟩ := hK0
  have hx₀' : x₀ ∈ rcl N K := subset_rcl K hx₀
  set S' : Finset (StDart (SDart (rcl N K))) := (K.subtype (· ∈ rcl N K)).image old with hS'
  have hS'card : S'.card = K.card := by
    rw [hS', card_image_of_injective _ (fun a b h => StDart.old.inj h), card_subtype,
      filter_true_of_mem fun d hd => subset_rcl K hd]
  change 3 * (S'.filter fun δ => (kst N K).face δ ∈ Z ∧ ¬ C.Mem δ).card ≤ _ at hin
  change 3 * (S'.filter fun δ => (kst N K).face δ ∉ Z ∧ ¬ C.Mem δ).card ≤ _ at hout
  -- the length of the cycle
  have hk' : C.k ≤ 6 * Nat.sqrt (12 * K.card) + 4 := by
    have h1 : Fintype.card (SVert (kσ N K) (rcl N K)) + Fintype.card (kmap N K).Face ≤
        2 * (rcl N K).card := card_pieceSep_le _ _
    have h2 := card_rcl_le (N := N) K
    change C.k ≤ 6 * Nat.sqrt (3 * Fintype.card (SVert (kσ N K) (rcl N K) ⊕
      (kmap N K).Face)) + 4 at hk
    rw [Fintype.card_sum] at hk
    have h3 : 3 * (Fintype.card (SVert (kσ N K) (rcl N K)) + Fintype.card (kmap N K).Face) ≤
        12 * K.card := by omega
    exact hk.trans (by have := Nat.sqrt_le_sqrt h3; omega)
  -- counting the darts of a side
  have hcount : ∀ W : Finset (kst N K).Face,
      (side N K W).card ≤ (S'.filter fun δ => (kst N K).face δ ∈ W).card := by
    intro W
    refine card_le_card_of_injOn
      (fun d => if h : d ∈ rcl N K then old ⟨d, h⟩ else old ⟨x₀, hx₀'⟩) ?_ ?_
    · intro d hd
      obtain ⟨hdK, h, hW⟩ := mem_side.1 hd
      simp only [h, ↓reduceDIte, mem_coe, mem_filter, hS', mem_image, mem_subtype]
      exact ⟨⟨⟨d, h⟩, hdK, rfl⟩, hW⟩
    · intro a ha b hb hab
      obtain ⟨-, h, -⟩ := mem_side.1 ha
      obtain ⟨-, h', -⟩ := mem_side.1 hb
      simp only [h, h', ↓reduceDIte] at hab
      exact congrArg Subtype.val (StDart.old.inj hab)
  have hmem : (univ.filter C.Mem).card ≤ 2 * C.k := by
    have hsub : univ.filter C.Mem ⊆
        (range C.k).image C.d ∪ (range C.k).image fun i => (kst N K).α (C.d i) := by
      intro δ hδ
      obtain ⟨i, hi, h | h⟩ := (mem_filter.1 hδ).2
      · exact mem_union_left _ (mem_image.2 ⟨i, mem_range.2 hi, h.symm⟩)
      · exact mem_union_right _ (mem_image.2 ⟨i, mem_range.2 hi, h.symm⟩)
    have h1 := card_le_card hsub
    have h2 := card_union_le ((range C.k).image C.d)
      ((range C.k).image fun i => (kst N K).α (C.d i))
    have h3 := card_image_le (s := range C.k) (f := C.d)
    have h4 := card_image_le (s := range C.k) (f := fun i => (kst N K).α (C.d i))
    rw [card_range] at h3 h4
    omega
  have hZ : (side N K Z).card ≤
      (S'.filter fun δ => (kst N K).face δ ∈ Z ∧ ¬ C.Mem δ).card + 2 * C.k := by
    refine (hcount Z).trans ((card_le_card ?_).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left hmem _)))
    intro δ hδ
    obtain ⟨h1, h2⟩ := mem_filter.1 hδ
    by_cases hm : C.Mem δ
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hm⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨h1, h2, hm⟩)
  have hZc : (side N K Zᶜ).card ≤
      (S'.filter fun δ => (kst N K).face δ ∉ Z ∧ ¬ C.Mem δ).card + 2 * C.k := by
    refine (hcount Zᶜ).trans ((card_le_card ?_).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left hmem _)))
    intro δ hδ
    obtain ⟨h1, h2⟩ := mem_filter.1 hδ
    by_cases hm : C.Mem δ
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hm⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨h1, mem_compl.1 h2, hm⟩)
  -- the vertices shared by the two sides
  have hbK : bdry N (side N K Z) (side N K Zᶜ) ⊆ verts N K := fun v hv =>
    verts_mono (side_subset Z) (mem_inter.1 hv).1
  have hbcard : (bdry N (side N K Z) (side N K Zᶜ)).card ≤ C.k := by
    rw [← C.card_verts]
    refine card_le_card_of_injOn (fun v => Sum.inl (ψ v)) (fun v hv => ?_) (fun v hv w hw h => ?_)
    · exact mem_cycle_of_bdry hψ hsep hv
    · exact kψ_inj hrot hψ (hbK hv) (hbK hw) (Sum.inl.inj h)
  refine ⟨?_, ?_, hk', ?_, ?_, hbcard, fun R hR => ⟨?_, ?_⟩⟩
  · ext d
    simp only [mem_union, mem_side, mem_compl]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      by_cases hz : (kst N K).face (old ⟨d, subset_rcl K h⟩) ∈ Z
      · exact Or.inl ⟨h, subset_rcl K h, hz⟩
      · exact Or.inr ⟨h, subset_rcl K h, hz⟩
  · refine disjoint_left.2 fun d h0 h1 => ?_
    obtain ⟨-, h, hz⟩ := mem_side.1 h0
    obtain ⟨-, h', hz'⟩ := mem_side.1 h1
    exact mem_compl.1 hz' hz
  · rw [hS'card] at hin; omega
  · rw [hS'card] at hout; omega
  · exact side_oneFace hM hrot hface hKr ⟨x₀, hx₀⟩ hK hψ hsep.bd
      (fun b hb => ⟨(mem_inter.1 hb).1, mem_cycle_of_bdry hψ hsep hb⟩) hR
  · exact side_oneFace hM hrot hface hKr ⟨x₀, hx₀⟩ hK hψ (bd_compl hsep.bd)
      (fun b hb => ⟨(mem_inter.1 hb).2, mem_cycle_of_bdry hψ hsep hb⟩) hR


end Cut

end NegSSSP

end PlanarFlow
