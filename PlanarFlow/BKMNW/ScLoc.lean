module

public import PlanarFlow.BKMNW.ScTouch
public import PlanarFlow.BKMNW.SepCE
public import PlanarFlow.BKMNW.LocalE

/-!
# The certificate of the piece map of the core does not depend on the enumeration

The headline's choices `scChoiceE M (sepC M eG N₀ Bz) eG N₀ Hs A W` use the global enumeration
`eG` (`gid (eG i) = i`); the machine (`scProgT_execK`, stage 5 of the large-piece separator)
computes the certificate for the enumeration `e'` of the piece map of the core (stage 2),
increasing in `gid`. Every choice of `scertD` is made on a subset of the darts of the piece map
of the core (the separator `sepC` by the ranks, `sepC_congr_gid`; the heavy component and the
anchors by the first dart, `findE_congr_gid`), so the certificates agree:

* **`findE_congr_gid`** (two enumerations increasing in `gid` covering `X` find the same dart);
* **`scertD_enum`**: for `N ⊆ B`, `B` covered by two enumerations `e`, `e'` increasing in `gid`,
  `scertD (scChoiceE M (sepC M e n Bz) e n Hs A W) Hs N τ ex =
   scertD (scChoiceE M (sepC M e' n' Bz) e' n' Hs A W) Hs N τ ex`;
* **`scertD_gidLoc`**: the same with the global enumeration (`gid (eG i) = i`, onto).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit Relation CombMap

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **Two enumerations increasing in `gid` and covering `X` find the same first dart of `X`.** -/
theorem findE_congr_gid {gid : D → ℕ} {f f' : ℕ → D} {n n' : ℕ} {X : Finset D}
    (hf : ∀ i j, i < j → j < n → gid (f i) < gid (f j)) (hX : ∀ d ∈ X, ∃ i < n, f i = d)
    (hf' : ∀ i j, i < j → j < n' → gid (f' i) < gid (f' j)) (hX' : ∀ d ∈ X, ∃ i < n', f' i = d) :
    findE f n X = findE f' n' X := by
  by_cases hne : X.Nonempty
  · obtain ⟨d, hd, hmin⟩ := X.exists_min_image gid hne
    rw [findE_eq_min hf hX hd hmin, findE_eq_min hf' hX' hd hmin]
  · rw [not_nonempty_iff_eq_empty] at hne
    subst hne
    rw [findE_eq_none (fun i _ => Finset.notMem_empty _),
      findE_eq_none (fun i _ => Finset.notMem_empty _)]

/-- **The certificate does not depend on the enumeration** (both increasing in `gid` and covering
the darts `B ⊇ N`). -/
theorem scertD_enum {gid : D → ℕ} {e e' : ℕ → D} {n n' : ℕ} {B : Finset D} (Bz A W : ℕ)
    (hm : ∀ i j, i < j → j < n → gid (e i) < gid (e j))
    (hm' : ∀ i j, i < j → j < n' → gid (e' i) < gid (e' j))
    (hs : ∀ d ∈ B, ∃ i < n, e i = d) (hs' : ∀ d ∈ B, ∃ i < n', e' i = d)
    (Hs : List (Finset V)) :
    ∀ (k : ℕ) (N : Finset D) (τ : Perm D) (ex : D → ℕ), N.card = k → N ⊆ B →
      scertD (scChoiceE M (sepC M e n Bz) e n Hs A W) Hs N τ ex =
        scertD (scChoiceE M (sepC M e' n' Bz) e' n' Hs A W) Hs N τ ex := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro N τ ex hk hNB
    have hfind : ∀ X ⊆ B, findE e n X = findE e' n' X := fun X hX =>
      findE_congr_gid hm (fun d hd => hs d (hX hd)) hm' (fun d hd => hs' d (hX hd))
    conv_lhs => rw [scertD]
    conv_rhs => rw [scertD]
    by_cases h : NoCut M N Hs
    · simp only [h, ↓reduceIte]
      have hsep : sepC M e n Bz N = sepC M e' n' Bz N :=
        sepC_congr_gid M Bz hm hm' (fun d hd => hs d (hNB hd)) (fun d hd => hs' d (hNB hd))
      have hsep' : (scChoiceE M (sepC M e n Bz) e n Hs A W).sep N =
          (scChoiceE M (sepC M e' n' Bz) e' n' Hs A W).sep N := hsep
      rw [hsep']
    simp only [h, ↓reduceIte]
    have hhole : (scChoiceE M (sepC M e n Bz) e n Hs A W).hole N =
        (scChoiceE M (sepC M e' n' Bz) e' n' Hs A W).hole N := rfl
    rw [hhole]
    rcases hh : (scChoiceE M (sepC M e' n' Bz) e' n' Hs A W).hole N with _ | g
    · rfl
    · simp only
      have hheavy : (scChoiceE M (sepC M e n Bz) e n Hs A W).heavy N g ex =
          (scChoiceE M (sepC M e' n' Bz) e' n' Hs A W).heavy N g ex :=
        hfind _ ((filter_subset _ _).trans hNB)
      rw [hheavy]
      rcases hz : (scChoiceE M (sepC M e' n' Bz) e' n' Hs A W).heavy N g ex with _ | z
      · simp only
        have ha : (scChoiceE M (sepC M e n Bz) e n Hs A W).anchor N g =
            (scChoiceE M (sepC M e' n' Bz) e' n' Hs A W).anchor N g :=
          hfind _ ((filter_subset _ _).trans hNB)
        rw [ha]
      · simp only
        have ha : (scChoiceE M (sepC M e n Bz) e n Hs A W).anchor (comp M N Hs g z) g =
            (scChoiceE M (sepC M e' n' Bz) e' n' Hs A W).anchor (comp M N Hs g z) g :=
          hfind _ ((filter_subset _ _).trans (comp_subset.trans hNB))
        rw [ha]
        rcases ha0 : (scChoiceE M (sepC M e' n' Bz) e' n' Hs A W).anchor (comp M N Hs g z) g
          with _ | a₀
        · rfl
        · simp only
          by_cases hK : (comp M N Hs g z).card < N.card
          · simp only [hK, ↓reduceDIte]
            rw [ih _ (hk ▸ hK) (comp M N Hs g z) _ _ rfl (comp_subset.trans hNB)]
          · simp only [hK, ↓reduceDIte]

/-- **The headline's certificate is the local one**: the global enumeration `eG`
(`gid (eG i) = i`, onto) and an enumeration `e'` of `B ⊇ N` increasing in `gid` give the same
certificate. -/
theorem scertD_gidLoc {gid : D → ℕ} {eG e' : ℕ → D} {N₀ n' : ℕ} {B : Finset D} (Bz A W : ℕ)
    (he : ∀ i < N₀, gid (eG i) = i) (hesurj : ∀ d, ∃ i < N₀, eG i = d)
    (hm' : ∀ i j, i < j → j < n' → gid (e' i) < gid (e' j)) (hs' : ∀ d ∈ B, ∃ i < n', e' i = d)
    (Hs : List (Finset V)) {N : Finset D} (hNB : N ⊆ B) (τ : Perm D) (ex : D → ℕ) :
    scertD (scChoiceE M (sepC M eG N₀ Bz) eG N₀ Hs A W) Hs N τ ex =
      scertD (scChoiceE M (sepC M e' n' Bz) e' n' Hs A W) Hs N τ ex :=
  scertD_enum Bz A W (fun i j h hj => by rw [he i (by omega), he j hj]; exact h) hm'
    (fun d _ => hesurj d) hs' Hs _ N τ ex rfl hNB

end BKMNW

end PlanarFlow
