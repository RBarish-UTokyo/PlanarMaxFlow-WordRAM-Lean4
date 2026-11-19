module

public import PlanarSeparator.MillerFace

/-!
# Miller's theorem with weights on vertices and faces, from a given cycle of the subdivision

The proofs of `PlanarSeparator.Map.exists_short_cycle_separator_face`, `…_dart` and `…_card`
take the cycle `C'` and the faces `Z'` of the stellar subdivision from Miller's theorem
(`exists_short_cycle_separator_stellar`) and return a set `Z` of faces of `M` obtained from `Z'`.
Here `Z` is explicit (`faceSepZ Z' t₁ t₂`): the majority faces `maj Z'` (two of their three
triangles in `Z'`) if some dart leaves them; otherwise the face of a triangle `t₁` of `Z'` (if no
face is a majority face) or of a triangle `t₂` off `Z'` (if every face is). The conclusions
hold for any cycle `C'` and faces `Z'` with the conclusion of the stellar theorem, in particular
for those computed by the machine (`PlanarSeparator/Machine/SepIn.lean`), and for any such `t₁`,
`t₂`. The proofs are those of `PlanarSeparator/MillerFace.lean`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarSeparator

open Finset StDart

namespace Map

variable {D P : Type*} {M : Map D P}

section Fallback

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]
  (htri : ∀ δ : D, M.IsTriangle δ) (hl : ∀ d, M.vert (M.α d) ≠ M.vert d)
  {C' : M.stellar.SCycle} {Z' : Finset M.stellar.Face}
  (hbd' : ∀ x, (M.stellar.face x ∈ Z' ↔ M.stellar.face (M.stellar.α x) ∈ Z') ↔ ¬ C'.Mem x)

include htri hl hbd'


/-- **The degenerate case, at a given triangle** (`exists_of_maj_eq_empty` with the triangle `t`
of `Z'` given): the boundary of the face of `t` separates. -/
lemma exists_of_maj_eq_empty_at (hM : M.IsPlane) (hmaj : maj Z' = ∅) {w : P ⊕ M.Face → ℝ}
    (hw : ∀ x, 0 ≤ w x) {t : D} (ht : M.stTri t ∈ Z') :
    ∃ (C : M.SCycle), C.k = 3 ∧ ∀ Z, Z = {M.face t} →
      (∀ d, (M.face d ∈ Z ↔ M.face (M.α d) ∈ Z) ↔ ¬ C.Mem d) ∧
      ∑ v ∈ sideIn C Z, w (.inl v) + ∑ f ∈ Z \ C.along, w (.inr f) = 0 ∧
      ∑ v ∈ sideOut C Z, w (.inl v) + ∑ f ∈ Zᶜ \ C.along, w (.inr f) ≤
        ∑ x ∈ sideOut C' Z', w x := by
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  have hnm : ∀ e, M.face e ∉ maj Z' := fun e => by rw [hmaj]; exact notMem_empty _
  have hn1 : ∀ {e}, M.stTri e ∈ Z' → M.stTri (M.φ e) ∉ Z' := fun he h =>
    hnm _ (mem_maj.2 ⟨_, rfl, he, h⟩)
  have hn2 : ∀ {e}, M.stTri e ∈ Z' → M.stTri (M.φ (M.φ e)) ∉ Z' := fun he h =>
    hnm _ (mem_maj.2 ⟨M.φ (M.φ _), by rw [face_φ, face_φ], h, by rw [h3]; exact he⟩)
  have hs1 : ∀ {e}, M.stTri e ∈ Z' → C'.Mem (down (M.φ e)) := fun {e} he => by
    by_contra h
    exact hn1 he (((bd_spoke hbd' _).2 h).1 he)
  have hs2 : ∀ {e}, M.stTri e ∈ Z' → C'.Mem (down e) := fun {e} he => by
    by_contra h
    have hb := (bd_spoke hbd' (M.φ (M.φ e))).2 (by rwa [h3])
    rw [h3] at hb
    exact hn2 he (hb.2 he)
  -- `Z'` consists of the triangles on `t` and `α t`
  have hZ' : ∀ F ∈ Z', F = M.stTri t ∨ F = M.stTri (M.α t) := by
    by_cases h0 : C'.Mem (old t)
    · rcases eq_one hbd' hM h0 (hs2 ht) (hs1 ht) with h | h
      · intro F hF
        rw [h] at hF
        exact Or.inl (mem_singleton.1 hF)
      · exact absurd (h ▸ ht) (by simp)
    · have hαt : M.stTri (M.α t) ∈ Z' := ((bd_old hbd' t).2 h0).1 ht
      rcases eq_two htri hbd' hM (hs2 ht) (hs1 ht) (hs2 hαt) (hs1 hαt) with h | h
      · intro F hF
        rw [h] at hF
        simpa using hF
      · exact absurd (h ▸ ht) (by simp)
  set K : Finset (P ⊕ M.Face) :=
    {.inl (M.vert t), .inl (M.vert (M.α t)), .inr (M.face t), .inr (M.face (M.α t))} with hKdef
  have hK : ∀ y, M.stellar.face y ∈ Z' → M.stellar.vert y ∈ K := by
    intro y hy
    rcases hZ' _ hy with h | h <;> rcases eq_of_stellar_face h with rfl | rfl | rfl <;>
      simp [K, M.α_α, M.vert_σ]
  have hC'K : ∀ x ∈ C'.verts, x ∈ K := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := C'.mem_verts.1 hx
    have := (hbd' (C'.d i)).not.2 (not_not.2 (C'.mem_d hi))
    by_cases h : M.stellar.face (C'.d i) ∈ Z'
    · exact hK _ h
    · have h' : M.stellar.face (M.stellar.σ (C'.d i)) ∈ Z' := by rw [face_σ]; tauto
      rw [← M.stellar.vert_σ]
      exact hK _ h'
  have hout : ∀ x ∉ K, x ∈ sideOut C' Z' := fun x hx =>
    mem_sideOut.2 ⟨fun h => hx (hC'K x h), fun h => by
      obtain ⟨-, y, rfl, hy⟩ := mem_sideIn.1 h
      exact hx (hK y hy)⟩
  -- the boundary of the face of `t`
  set C := triCycle hl (htri t) with hC
  have hC0 : C.Mem t := C.mem_d (i := 0) C.pos
  refine ⟨C, rfl, fun Z hZ => ?_⟩
  subst hZ
  refine ⟨bd_triCycle hl (htri t) htri, ?_, ?_⟩
  · have e1 : sideIn C {M.face t} = ∅ := by
      ext v
      simp only [notMem_empty, iff_false]
      intro hv
      obtain ⟨hvC, d, rfl, hd⟩ := mem_sideIn.1 hv
      exact hvC (C.mem_verts_of_mem ((mem_triCycle hl (htri t)).2 (Or.inl (mem_singleton.1 hd))))
    have e2 : ({M.face t} : Finset M.Face) \ C.along = ∅ := by
      rw [sdiff_eq_empty_iff_subset, singleton_subset_iff]
      exact SCycle.mem_along.2 ⟨t, rfl, hC0⟩
    rw [e1, e2, sum_empty, sum_empty, add_zero]
  · rw [← sum_disjSum]
    refine sum_le_sum_of_subset_of_nonneg (fun x hx => hout x ?_) fun x _ _ => hw x
    rcases x with v | f
    · have hvC := (mem_sideOut.1 (by simpa using hx)).1
      intro hK'
      simp only [hKdef, mem_insert, mem_singleton, Sum.inl.injEq, reduceCtorEq, or_false]
        at hK'
      rcases hK' with rfl | rfl
      · exact hvC (C.mem_verts.2 ⟨0, C.pos, rfl⟩)
      · exact hvC (C.mem_verts.2 ⟨1, show 1 < 3 by norm_num, M.vert_φ t⟩)
    · have hx' : f ≠ M.face t ∧ f ∉ C.along := by simpa using hx
      intro hK'
      simp only [hKdef, mem_insert, mem_singleton, Sum.inr.injEq, reduceCtorEq, false_or]
        at hK'
      rcases hK' with rfl | rfl
      · exact hx'.1 rfl
      · exact hx'.2 (SCycle.mem_along.2 ⟨M.α t, rfl, (C.mem_α_iff).2 hC0⟩)


end Fallback

section Main

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

open Classical in
/-- **The faces of `M` from the faces `Z'` of the stellar subdivision**: the majority faces if
some dart leaves them, otherwise the face of `t₁` (no majority face) or of `t₂` (all faces). -/
noncomputable def faceSepZ (Z' : Finset M.stellar.Face) (t₁ t₂ : D) : Finset M.Face :=
  if ∃ d₀, M.face d₀ ∈ maj Z' ∧ M.face (M.α d₀) ∉ maj Z' then maj Z'
  else if maj Z' = ∅ then {M.face t₁} else {M.face t₂}

/-- **`exists_short_cycle_separator_face` from a given separating cycle of the stellar
subdivision**, with the explicit faces `faceSepZ Z' t₁ t₂`, for a triangle `t₁` in `Z'` and a
triangle `t₂` off `Z'`. -/
theorem face_sep_of (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ)
    (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) {w : P ⊕ M.Face → ℝ} (hw : ∀ x, 0 ≤ w x)
    {C' : M.stellar.SCycle} {Z' : Finset M.stellar.Face}
    (hk' : C'.k ≤ 6 * Nat.sqrt (Fintype.card P + Fintype.card M.Face) + 4)
    (hsep' : IsCycleSep C' Z' (sideIn C' Z') (sideOut C' Z'))
    (hin' : ∑ x ∈ sideIn C' Z', w x ≤ 2 / 3) (hout' : ∑ x ∈ sideOut C' Z', w x ≤ 2 / 3)
    {t₁ t₂ : D} (ht₁ : M.stTri t₁ ∈ Z') (ht₂ : M.stTri t₂ ∉ Z') :
    ∃ C : M.SCycle, C.k ≤ 6 * Nat.sqrt (3 * Fintype.card P) + 4 ∧
      IsCycleSep C (faceSepZ Z' t₁ t₂) (sideIn C (faceSepZ Z' t₁ t₂))
        (sideOut C (faceSepZ Z' t₁ t₂)) ∧
      ∑ v ∈ sideIn C (faceSepZ Z' t₁ t₂), w (.inl v) +
        ∑ f ∈ faceSepZ Z' t₁ t₂ \ C.along, w (.inr f) ≤ 2 / 3 ∧
      ∑ v ∈ sideOut C (faceSepZ Z' t₁ t₂), w (.inl v) +
        ∑ f ∈ (faceSepZ Z' t₁ t₂)ᶜ \ C.along, w (.inr f) ≤ 2 / 3 := by
  classical
  have h3 : ∀ d : D, M.φ (M.φ (M.φ d)) = d := fun d => (htri d).φ_three
  have hsq := Nat.sqrt_le_sqrt
    (h := (card_add_card_face hM htri).le.trans' (Nat.le_add_right _ 4))
  have hbd' := hsep'.bd
  have hbdc' := bd_compl hbd'
  have hex' := (isPlane_stellar hM).exists_dart
  have hconn' := (isPlane_stellar hM).connected
  by_cases hnd : ∃ d₀, M.face d₀ ∈ maj Z' ∧ M.face (M.α d₀) ∉ maj Z'
  · obtain ⟨d₀, hd₀, hd₀'⟩ := hnd
    have hW : FConn (maj Z') := fConn_maj (fConn_of_bd hconn' hbd')
    have hWc : FConn (maj Z')ᶜ := by
      rw [← maj_compl h3]
      exact fConn_maj (fConn_of_bd hconn' hbdc')
    obtain ⟨C, -, hbd⟩ := hM.exists_scycle_bd hW hWc hd₀ hd₀'
    have hbdc := bd_compl hbd
    rw [← maj_compl h3] at hbdc
    have hne : maj Z' ≠ univ := fun h => hd₀' (h ▸ mem_univ _)
    have hne' : maj Z'ᶜ ≠ univ := by
      rw [maj_compl h3]
      intro h
      have : M.face d₀ ∈ (maj Z')ᶜ := by rw [h]; exact mem_univ _
      exact mem_compl.1 this hd₀
    have hZ : faceSepZ Z' t₁ t₂ = maj Z' := ite_eq_left ⟨d₀, hd₀, hd₀'⟩
    rw [hZ]
    refine ⟨C, ?_, isCycleSep_of_bd hbd, ?_, ?_⟩
    · have hsub : C.verts.map Function.Embedding.inl ⊆ C'.verts := by
        intro x hx
        obtain ⟨v, hv, rfl⟩ := mem_map.1 hx
        obtain ⟨i, hi, rfl⟩ := C.mem_verts.1 hv
        by_contra h
        exact (hbd _).1 (face_mem_maj_iff_α hbd' h3 h rfl) (C.mem_d hi)
      have := card_le_card hsub
      rw [card_map, C.card_verts, C'.card_verts] at this
      omega
    · exact (sum_le_sum_sideIn htri hbd' hbd hM hne hw).trans hin'
    · have := sum_le_sum_sideIn htri hbdc' hbdc hM hne' hw
      rw [maj_compl h3, sideIn_compl hM.exists_dart hbd, sideIn_compl hex' hbd'] at this
      exact this.trans hout'
  · push Not at hnd
    have hb : ∀ d, bdc (maj Z') d = 0 := fun d => by
      rw [bdc_eq_zero_iff]
      exact ⟨hnd d, fun h => by have := hnd (M.α d) h; rwa [M.α_α] at this⟩
    rcases eq_empty_or_univ_of_bdc hM.connected hb with h | h
    · obtain ⟨C, hk, hC⟩ := exists_of_maj_eq_empty_at htri hl hbd' hM h hw ht₁
      have hZ : faceSepZ Z' t₁ t₂ = {M.face t₁} := by
        unfold faceSepZ; rw [ite_eq_right (by push Not; exact hnd)]; exact ite_eq_left h
      obtain ⟨hbd, hin, hout⟩ := hC _ hZ
      rw [hZ] at hbd hin hout ⊢
      exact ⟨C, by omega, isCycleSep_of_bd hbd, by rw [hin]; norm_num, hout.trans hout'⟩
    · have h' : maj Z'ᶜ = ∅ := by rw [maj_compl h3, h, compl_univ]
      obtain ⟨C, hk, hC⟩ := exists_of_maj_eq_empty_at htri hl hbdc' hM h' hw
        (Z' := Z'ᶜ) (t := t₂) (mem_compl.2 ht₂)
      have hne : maj Z' ≠ ∅ := by
        rw [h]; exact (univ_nonempty_iff.2 ⟨M.face t₂⟩).ne_empty
      have hZ : faceSepZ Z' t₁ t₂ = {M.face t₂} := by
        unfold faceSepZ; rw [ite_eq_right (by push Not; exact hnd)]; exact ite_eq_right hne
      obtain ⟨hbd, hin, hout⟩ := hC _ hZ
      rw [sideOut_compl hex' hbd'] at hout
      rw [hZ] at hbd hin hout ⊢
      exact ⟨C, by omega, isCycleSep_of_bd hbd, by rw [hin]; norm_num, hout.trans hin'⟩


end Main

section Darts

variable [Fintype D] [DecidableEq D] [Fintype P] [DecidableEq P]

variable (M) in
/-- The weights of the faces from weights on the darts (none on the vertices). -/
noncomputable def wF (w : D → ℝ) : P ⊕ M.Face → ℝ :=
  Sum.elim (fun _ => 0) (fun f => ∑ d with M.face d = f, w d)

/-- The uniform weight on a set of darts. -/
noncomputable def wS (S : Finset D) : D → ℝ := fun d => if d ∈ S then 1 / (#S : ℝ) else 0

/-- **`exists_short_cycle_separator_dart` from a given separating cycle of the stellar
subdivision** for the face weights `wF M w`, with the explicit faces `faceSepZ Z' t₁ t₂`. -/
theorem dart_sep_of (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ)
    (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) {w : D → ℝ} (hw : ∀ d, 0 ≤ w d)
    (h1 : ∑ d, w d ≤ 1) {C' : M.stellar.SCycle} {Z' : Finset M.stellar.Face}
    (hk' : C'.k ≤ 6 * Nat.sqrt (Fintype.card P + Fintype.card M.Face) + 4)
    (hsep' : IsCycleSep C' Z' (sideIn C' Z') (sideOut C' Z'))
    (hin' : ∑ x ∈ sideIn C' Z', wF M w x ≤ 2 / 3) (hout' : ∑ x ∈ sideOut C' Z', wF M w x ≤ 2 / 3)
    {t₁ t₂ : D} (ht₁ : M.stTri t₁ ∈ Z') (ht₂ : M.stTri t₂ ∉ Z') :
    ∃ C : M.SCycle, C.k ≤ 6 * Nat.sqrt (3 * Fintype.card P) + 4 ∧
      IsCycleSep C (faceSepZ Z' t₁ t₂) (sideIn C (faceSepZ Z' t₁ t₂))
        (sideOut C (faceSepZ Z' t₁ t₂)) ∧
      ∑ d with M.face d ∈ faceSepZ Z' t₁ t₂ \ C.along, w d ≤ 2 / 3 ∧
      ∑ d with M.face d ∈ (faceSepZ Z' t₁ t₂)ᶜ \ C.along, w d ≤ 2 / 3 := by
  classical
  classical
  set W : P ⊕ M.Face → ℝ := wF M w with hWdef
  have hW : ∀ x, 0 ≤ W x := by
    rintro (v | f)
    · exact le_rfl
    · exact sum_nonneg fun d _ => hw d
  have hfib : ∀ F : Finset M.Face, ∑ f ∈ F, W (.inr f) = ∑ d with M.face d ∈ F, w d := by
    intro F
    rw [← sum_fiberwise_of_maps_to (s := ({d | M.face d ∈ F} : Finset D)) (t := F)
      (g := M.face) (fun d hd => (mem_filter.1 hd).2)]
    refine sum_congr rfl fun f hf => ?_
    simp only [W, wF, Sum.elim_inr]
    rw [filter_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext d
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro rfl; exact ⟨hf, rfl⟩
    · exact fun h => h.2
  have h1' : ∑ x, W x ≤ 1 := by
    rw [Fintype.sum_sum_type, hfib univ]
    have e : ∑ v : P, W (.inl v) = 0 := sum_eq_zero fun _ _ => rfl
    rw [e, zero_add]
    simpa using h1
  obtain ⟨C, hk, hsep, hin, hout⟩ := face_sep_of hM htri hl hW hk' hsep' hin' hout' ht₁ ht₂
  set Z := faceSepZ Z' t₁ t₂ with hZdef
  refine ⟨C, hk, hsep, ?_, ?_⟩
  · rw [← hfib]
    have := sum_nonneg fun v (_ : v ∈ sideIn C Z) => hW (.inl v)
    linarith
  · rw [← hfib]
    have := sum_nonneg fun v (_ : v ∈ sideOut C Z) => hW (.inl v)
    linarith

open Classical in
/-- **`exists_short_cycle_separator_card` from a given separating cycle of the stellar
subdivision** for the face weights `wF M (wS S)`, with the explicit faces `faceSepZ Z' t₁ t₂`:
among the darts of `S` off `C`, those with their face in it and those with their face off it
number at most `2/3 #S + 2 C.k` each. -/
theorem card_sep_of (hM : M.IsPlane) (htri : ∀ δ : D, M.IsTriangle δ)
    (hl : ∀ d, M.vert (M.α d) ≠ M.vert d) (S : Finset D) {C' : M.stellar.SCycle}
    {Z' : Finset M.stellar.Face}
    (hk' : C'.k ≤ 6 * Nat.sqrt (Fintype.card P + Fintype.card M.Face) + 4)
    (hsep' : IsCycleSep C' Z' (sideIn C' Z') (sideOut C' Z'))
    (hin' : ∑ x ∈ sideIn C' Z', wF M (wS S) x ≤ 2 / 3)
    (hout' : ∑ x ∈ sideOut C' Z', wF M (wS S) x ≤ 2 / 3)
    {t₁ t₂ : D} (ht₁ : M.stTri t₁ ∈ Z') (ht₂ : M.stTri t₂ ∉ Z') :
    ∃ C : M.SCycle, C.k ≤ 6 * Nat.sqrt (3 * Fintype.card P) + 4 ∧
      IsCycleSep C (faceSepZ Z' t₁ t₂) (sideIn C (faceSepZ Z' t₁ t₂))
        (sideOut C (faceSepZ Z' t₁ t₂)) ∧
      3 * #{d ∈ S | M.face d ∈ faceSepZ Z' t₁ t₂ ∧ ¬ C.Mem d} ≤ 2 * #S + 6 * C.k ∧
      3 * #{d ∈ S | M.face d ∉ faceSepZ Z' t₁ t₂ ∧ ¬ C.Mem d} ≤ 2 * #S + 6 * C.k := by
  classical
  classical
  set w : D → ℝ := wS S with hwdef
  have hw : ∀ d, 0 ≤ w d := fun d => by
    simp only [w, wS]
    split_ifs <;> positivity
  have hsum : ∀ T : Finset D, ∑ d ∈ T, w d = #(T ∩ S) * (1 / (#S : ℝ)) := by
    intro T
    simp only [w, wS]
    rw [← sum_filter, sum_const, nsmul_eq_mul, filter_mem_eq_inter]
  have h1 : ∑ d, w d ≤ 1 := by
    rw [hsum, univ_inter]
    rcases Nat.eq_zero_or_pos #S with h | h
    · rw [h]; norm_num
    · rw [mul_one_div, div_self (by positivity)]
  obtain ⟨C, hk, hsep, hin, hout⟩ := dart_sep_of hM htri hl hw h1 hk' hsep' hin' hout' ht₁ ht₂
  set Z := faceSepZ Z' t₁ t₂ with hZdef
  -- the darts of `S` with their face in a set not along `C`
  have hpart : ∀ Y : Finset M.Face, ∑ d with M.face d ∈ Y, w d ≤ 2 / 3 →
      3 * #{d ∈ S | M.face d ∈ Y} ≤ 2 * #S := by
    intro Y hY
    rw [hsum] at hY
    have e : ({d | M.face d ∈ Y} : Finset D) ∩ S = {d ∈ S | M.face d ∈ Y} := by
      ext d
      simp [and_comm]
    rw [e] at hY
    rcases Nat.eq_zero_or_pos #S with h | h
    · rw [h, card_eq_zero.2 (by rw [card_eq_zero.1 h]; rfl)]
    · have hS : (0 : ℝ) < #S := by exact_mod_cast h
      rw [mul_one_div, div_le_iff₀ hS] at hY
      exact_mod_cast (by linarith : (3 * #{d ∈ S | M.face d ∈ Y} : ℝ) ≤ 2 * #S)
  have hbd := hsep.bd
  have h1' := card_le_of_along htri (C := C) S Z
  have h2' := card_le_of_along htri (C := C) S Zᶜ
  have h3' := card_inter_along_le hbd
  have h4' := card_inter_along_le (bd_compl hbd)
  have h5 := hpart _ hin
  have h6 := hpart _ hout
  refine ⟨C, hk, hsep, by omega, le_trans (Nat.mul_le_mul_left 3 (card_le_card
    (t := ({d ∈ S | M.face d ∈ Zᶜ ∧ ¬ C.Mem d} : Finset D)) fun d hd => ?_)) (by omega)⟩
  simp only [mem_filter, mem_compl] at hd ⊢
  exact hd


end Darts

end Map

end PlanarSeparator
