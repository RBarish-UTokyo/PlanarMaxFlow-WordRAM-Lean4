module

public import PlanarFlow.BKMNW.MsEncD

/-!
# The composed MSSP encoder, part E: auxiliary facts of the semantic link

* `cF_le_nD'` (`#CutF ≤ nD`), `kRank_corner` (the slot of the `r`-th corner is `r`),
  `pend_head`, `mσ_pend` (the pendant dart of a root), `knVM_le`;
* clipping: `KInMS.clip`, `KOut.clip`, `KInit.clip` — Klein's input predicates survive replacing
  every input word by `min (word, Wb)` when all the words they read are `≤ Wb`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NsStep
  CombMap NegSSSP

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **`#CutF ≤ nD`.** -/
lemma cF_le_nD' (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) : Fintype.card (CutF M Pa.darts) ≤ mnD Pa en m := by
  classical
  have h' := enumOK_dual_of hM hrot h (Pa.d 0)
  have hS : Fintype.card {v : V // v ∉ cutS M Pa.darts} ≤ nEc Pa.darts en m := by
    rw [Fintype.card_subtype]
    have hsub : (univ.filter fun v : V => v ∉ cutS M Pa.darts) ⊆
        (univ.filter fun e : D => e ∉ Pa.darts).image M.tail := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and] at hv
      obtain ⟨d, hd⟩ := h'.fsurj v
      refine mem_image.2 ⟨d, ?_, hd⟩
      simp only [mem_filter, mem_univ, true_and]
      intro hdL; exact hv (hd ▸ tail_mem_cutS hdL)
    have := (card_le_card hsub).trans card_image_le
    rw [card_filter_en h] at this
    exact this
  have hT := card_cutT_eq h Pa
  have hT1 : 1 ≤ nTc M Pa.darts en m := by
    rw [← hT]; exact Fintype.card_pos_iff.2 ⟨fixT0 Pa hk⟩
  have eD : mnD Pa en m = nEc Pa.darts en m + 4 * nTc M Pa.darts en m := rfl
  simp only [CutF, Fintype.card_sum, Fintype.card_unit]
  omega

/-- **The slot of the `r`-th corner is `r`**: below the `r`-th element of a strictly increasing
list, exactly `r` numbers are in the list. -/
lemma kRank_corner {L : List ℕ} (hinc : ∀ r r', r < r' → r' < L.length → L.getD r 0 < L.getD r' 0)
    {r : ℕ} (hr : r < L.length) :
    Klein.kRank (fun j => decide (j ∈ L)) (L.getD r 0) = r := by
  unfold Klein.kRank
  have hmono : ∀ a b, a < L.length → b < L.length → L.getD a 0 < L.getD b 0 → a < b := by
    intro a b ha hb hab
    rcases Nat.lt_trichotomy a b with h1 | h1 | h1
    · exact h1
    · subst h1; omega
    · have := hinc b a h1 ha; omega
  have : ((range (L.getD r 0)).filter fun j => decide (j ∈ L) = true) =
      (range r).image (fun r' => L.getD r' 0) := by
    ext x
    simp only [mem_filter, mem_range, decide_eq_true_eq, mem_image]
    constructor
    · rintro ⟨hx, hxL⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hxL
      refine ⟨i, ?_, by rw [List.getD_eq_getElem _ _ hi]⟩
      have : L.getD i 0 < L.getD r 0 := by rw [List.getD_eq_getElem _ _ hi]; exact hx
      exact hmono i r hi hr this
    · rintro ⟨i, hi, rfl⟩
      refine ⟨hinc i r hi hr, ?_⟩
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  rw [this, card_image_of_injOn, card_range]
  intro a ha b hb e
  simp only [coe_range, Set.mem_Iio] at ha hb
  rcases Nat.lt_trichotomy a b with h1 | h1 | h1
  · have := hinc a b h1 (by omega); simp only at e; omega
  · exact h1
  · have := hinc b a h1 (by omega); simp only at e; omega

/-- The head of the pendant dart of a root is the copy of its face. -/
lemma pend_head (Pa : SPath M) (t : CutT M Pa.darts) :
    (mN Pa).head (Sum.inr (Sum.inl t)) = (Sum.inl (M.face t.1) : CutV M Pa.darts) := rfl

lemma mσ_pend {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k)
    (t : CutT M Pa.darts) :
    (mσ h Pa hk (Sum.inr (Sum.inl t)) : ℕ) = nEc Pa.darts en m + cT M Pa.darts en (ixOf en m t.1) := by
  rw [enEq_cut Pa.rev_mem_darts' h (cD0 Pa hk)]; rfl

lemma kmF_le (B nD n k t : ℕ) {j : ℕ} (hj : j < 43) :
    kmF B nD n k t j ≤ t + k + 7 * n + 9 * nD + B + 15 := by
  interval_cases j <;> simp only [kmF, kmCo, List.getD_cons_succ, List.getD_cons_zero] <;> omega

/-- **The parameters of `kNFM` are bounded.** -/
lemma knVM_le (B nD n k t Hc β len : ℕ) {j : ℕ} (hj : j < 48) :
    KleinFix.knVM B nD n k t Hc β len j ≤
      t + k + 7 * n + 9 * nD + 2 * B + 16 * (n + 1) + 2 * Hc + 16 + β + len := by
  unfold KleinFix.knVM KleinFix.knV
  split_ifs with h1 h2 h3 h4 h5
  · have := kmV_eq B nD n k t h2; have := kmF_le B nD n k t h2; omega
  all_goals omega

/-! ### Clipping -/

section Clip

variable {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y]

lemma min_of_le {a b : ℕ} (h : a ≤ b) : min a b = a := min_eq_left h

/-- Klein's words with the piece survive clipping at `Wb`. -/
lemma KInMS.clip {Q : CombMap D' X Y} {S : Finset D'} {ℓ : D' → ℤ} {nD : ℕ} {σ : D' ≃ Fin nD}
    {ιv : X → ℕ} {ιg : D' → ℕ} {ιf : Y → ℕ} {ιe : D' → ℕ} {mem : ℕ → ℕ} {β Wb : ℕ}
    (h : KInMS Q S ℓ σ ιv ιg ιf ιe mem β) (hσ : nD ≤ Wb) (hv : ∀ x, ιv x ≤ Wb)
    (hg : ∀ d, ιg d ≤ Wb) (hf : ∀ y, ιf y ≤ Wb) (he : ∀ d, ιe d ≤ Wb) (h1 : 1 ≤ Wb)
    (hl : ∀ d ∈ S, (ℓ d).toNat ≤ Wb) :
    KInMS Q S ℓ σ ιv ιg ιf ιe (fun a => min (mem a) Wb) β := by
  have hs : ∀ d : D', (σ d : ℕ) ≤ Wb := fun d => by have := (σ d).2; omega
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
    fun d => ?_, fun d hd => ?_, fun d => ?_⟩
  · simp only [h.rv d, min_of_le (hs _)]
  · simp only [h.nf d, min_of_le (hf _)]
  · simp only [h.ne d, min_of_le (he _)]
  · simp only [h.ng d, min_of_le (hg _)]
  · simp only [h.nt d, min_of_le (hv _)]
  · simp only [h.nh d, min_of_le (hv _)]
  · simp only [h.is d]; split_ifs <;> omega
  · simp only [h.ln d hd, min_of_le (hl d hd)]
  · rcases h.ed d with e | e
    · left; simp only [e, min_of_le (hs _)]
    · right; simp only [e, min_of_le (hs _)]

/-- The out-lists survive clipping at `Wb ≥ nD`. -/
lemma KOut.clip {N : CombMap D' X Y} {S : Finset D'} {nD : ℕ} {σ : D' ≃ Fin nD} {ιv : X → ℕ}
    {n k Wb : ℕ} {Pk Pk' : Input} (h : Klein.KOut N S σ ιv n k Pk)
    (hcl : ∀ i, Pk'.data.getD i 0 = min (Pk.data.getD i 0) Wb) (hnD : nD ≤ Wb) :
    Klein.KOut N S σ ιv n k Pk' := by
  intro x
  obtain ⟨ds, hnd, hm, h1, h2, h3⟩ := h x
  have eE : Pk'.data.getD (Klein.iOE nD n k + ιv x) 0 = Pk.data.getD (Klein.iOE nD n k + ιv x) 0 := by
    rw [hcl]; exact min_of_le (by omega)
  have eB : Pk'.data.getD (Klein.iOB nD n k + ιv x) 0 = Pk.data.getD (Klein.iOB nD n k + ιv x) 0 := by
    rw [hcl]; exact min_of_le (by omega)
  refine ⟨ds, hnd, hm, by rw [eE, eB]; exact h1, by rw [eE]; exact h2, fun i hi => ?_⟩
  rw [eB, hcl, h3 i hi]
  have := (σ ds[i]).2
  exact min_of_le (by omega)

end Clip

/-- Klein's initial trees survive clipping at `Wb`. -/
lemma KInit.clip {D' X Y : Type*} [Fintype D'] [DecidableEq D'] [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] {N : CombMap D' X Y} {nD : ℕ} {σ : D' ≃ Fin nD}
    {ιv : X → ℕ} {ιf : Y → ℕ} {n k Wb : ℕ} {T : STFlow.DTree N.dual} {C : STFlow.DTree N}
    {vs ts : List X} {fs cs : List Y} {Pk Pk' : Input}
    (h : Klein.KInit N σ ιv ιf n k T C vs ts fs cs Pk)
    (hcl : ∀ i, Pk'.data.getD i 0 = min (Pk.data.getD i 0) Wb) (hnD : nD ≤ Wb)
    (hv : ∀ x, ιv x ≤ Wb) (hf : ∀ y, ιf y ≤ Wb) (l0 : vs.length ≤ Wb) (l1 : ts.length ≤ Wb)
    (l2 : fs.length ≤ Wb) (l3 : cs.length ≤ Wb) :
    Klein.KInit N σ ιv ιf n k T C vs ts fs cs Pk' := by
  have hs : ∀ d : D', (σ d : ℕ) ≤ Wb := fun d => by have := (σ d).2; omega
  refine ⟨h.oT, h.oC, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [hcl, h.iv i hi]; exact min_of_le (hv _)
  · rw [hcl, h.it i hi]; exact min_of_le (hs _)
  · rw [hcl, h.if_ i hi]; exact min_of_le (hf _)
  · rw [hcl, h.ic i hi]; exact min_of_le (hs _)
  · rw [hcl, h.l0]; exact min_of_le l0
  · rw [hcl, h.l1]; exact min_of_le l1
  · rw [hcl, h.l2]; exact min_of_le l2
  · rw [hcl, h.l3]; exact min_of_le l3

end MsEnc

end BKMNW

end PlanarFlow
