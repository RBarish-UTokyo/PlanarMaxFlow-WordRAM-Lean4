module

public import PlanarFlow.BKMNW.MbSep

/-!
# Miller's separator `sepC` does not depend on which `gid`-increasing enumeration numbers it

`sepC M e n Bz` (`MbSep.lean`) numbers the darts of a piece map `N` by their ranks in the
enumeration `e` (`cNe e n N`). A program enumerates only the darts of the current piece (in the
increasing order of the global numbering `gid`), while the decomposition of the headline uses one
global enumeration: both give the same ranks on `N`, hence the same separator.

* `eIdx_lt_iff_gid`, **`eRk_eq_gid`** (the rank of a dart of `N` is the number of darts of `N`
  of smaller `gid`);
* `cNe_congr`, **`sepC_congr`** (equal ranks on `N` ⟹ equal separators on `N`),
  **`sepC_congr_gid`** (two `gid`-increasing enumerations covering `N`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

lemma eIdx_lt_iff_gid {gid : D → ℕ} {e : ℕ → D} {n : ℕ}
    (hmono : ∀ i j, i < j → j < n → gid (e i) < gid (e j)) {x y : D}
    (hx : ∃ i, i < n ∧ e i = x) (hy : ∃ i, i < n ∧ e i = y) :
    eIdx e n x < eIdx e n y ↔ gid x < gid y := by
  obtain ⟨a1, a2⟩ := eIdx_spec hx
  obtain ⟨b1, b2⟩ := eIdx_spec hy
  constructor
  · intro h
    have := hmono _ _ h b1
    rwa [a2, b2] at this
  · intro h
    by_contra hc
    rcases Nat.lt_or_ge (eIdx e n y) (eIdx e n x) with h' | h'
    · have := hmono _ _ h' a1; rw [a2, b2] at this; omega
    · have he : eIdx e n x = eIdx e n y := by omega
      have : x = y := by rw [← a2, ← b2, he]
      subst this; omega

/-- **The rank of a dart is the number of darts of smaller `gid`** (`e` increasing in `gid`,
covering `N`). -/
lemma eRk_eq_gid {gid : D → ℕ} {e : ℕ → D} {n : ℕ}
    (hmono : ∀ i j, i < j → j < n → gid (e i) < gid (e j)) {N : Finset D}
    (hsurj : ∀ d ∈ N, ∃ i, i < n ∧ e i = d) {d : D} (hd : d ∈ N) :
    eRk e n N d = #(N.filter fun y => gid y < gid d) := by
  unfold eRk
  congr 1
  apply filter_congr
  intro y hy
  exact eIdx_lt_iff_gid hmono (hsurj y hy) (hsurj d hd)

lemma cNe_congr {e e' : ℕ → D} {n n' : ℕ} {N : Finset D}
    (hs : ∀ d ∈ N, ∃ i, i < n ∧ e i = d) (hs' : ∀ d ∈ N, ∃ i, i < n' ∧ e' i = d)
    (h : ∀ d ∈ N, eRk e n N d = eRk e' n' N d) : cNe e n N = cNe e' n' N := by
  ext x
  rw [cNe_apply hs, cNe_apply hs', h x.1 x.2]

variable (M) in
/-- **Equal ranks on `N` give the same separator on `N`.** -/
theorem sepC_congr {e e' : ℕ → D} {n n' : ℕ} (Bz : ℕ) {N : Finset D}
    (hs : ∀ d ∈ N, ∃ i, i < n ∧ e i = d) (hs' : ∀ d ∈ N, ∃ i, i < n' ∧ e' i = d)
    (h : ∀ d ∈ N, eRk e n N d = eRk e' n' N d) : sepC M e n Bz N = sepC M e' n' Bz N := by
  unfold sepC
  rw [cNe_congr hs hs' h]

variable (M) in
/-- **Two `gid`-increasing enumerations covering `N` give the same separator on `N`.** -/
theorem sepC_congr_gid {gid : D → ℕ} {e e' : ℕ → D} {n n' : ℕ} (Bz : ℕ) {N : Finset D}
    (hm : ∀ i j, i < j → j < n → gid (e i) < gid (e j))
    (hm' : ∀ i j, i < j → j < n' → gid (e' i) < gid (e' j))
    (hs : ∀ d ∈ N, ∃ i, i < n ∧ e i = d) (hs' : ∀ d ∈ N, ∃ i, i < n' ∧ e' i = d) :
    sepC M e n Bz N = sepC M e' n' Bz N :=
  sepC_congr M Bz hs hs' fun d hd => by rw [eRk_eq_gid hm hs hd, eRk_eq_gid hm' hs' hd]

end BKMNW

end PlanarFlow
