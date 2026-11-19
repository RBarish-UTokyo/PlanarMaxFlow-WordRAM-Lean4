module

public import PlanarFlow.BKMNW.HoleProg

/-!
# The choices of the global enumeration from a local one

`pcChoiceE`/`scChoiceE` choose "the first dart (by index) of a set" for the global enumeration `e`
(`gid (e i) = i`). A program working on a piece sees its darts through a local enumeration `g`,
increasing in `gid`. **For a set inside the piece the first dart is the same**: the one of least
`gid`.

* **`findE_eq_min`**: `f` increasing in `gid` on `[0, n)` and covering `X`, `d ∈ X` of least `gid`
  ⟹ `findE f n X = some d`;
* **`findE_gidLoc`**: `findE e N X = findE g n' X` for `X` covered by `g` (`e` the global
  enumeration, `gid (e i) = i`, onto), and **`firstE_gidLoc`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

open Finset

variable {D : Type*} [DecidableEq D]

/-- **The first dart of a set for an enumeration increasing in `gid` is its dart of least
`gid`.** -/
theorem findE_eq_min {gid : D → ℕ} {f : ℕ → D} {n : ℕ} {X : Finset D}
    (hmono : ∀ i j, i < j → j < n → gid (f i) < gid (f j)) (hcov : ∀ d ∈ X, ∃ i < n, f i = d)
    {d : D} (hd : d ∈ X) (hmin : ∀ d' ∈ X, gid d ≤ gid d') : findE f n X = some d := by
  obtain ⟨i, hi, rfl⟩ := hcov d hd
  unfold findE
  have h := find?_getD 0 (fun j => decide (f j ∈ X)) (List.range n) i (by simpa using hi)
    (by simp [List.getD_eq_getElem?_getD, List.getElem?_range hi, hd]) (fun j hj => by
      have hjn : j < n := by omega
      simp only [List.getD_eq_getElem?_getD, List.getElem?_range hjn, Option.getD_some,
        decide_eq_false_iff_not]
      intro hX
      have := hmin _ hX
      have := hmono j i hj hi
      omega)
  rw [h]
  simp [List.getD_eq_getElem?_getD, List.getElem?_range hi]

lemma findE_eq_none {f : ℕ → D} {n : ℕ} {X : Finset D} (h : ∀ i < n, f i ∉ X) :
    findE f n X = none := by
  unfold findE
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro i hi
  simpa using h i (List.mem_range.1 hi)

/-- **Global and local first darts agree** on a set covered by the local enumeration. -/
theorem findE_gidLoc {gid : D → ℕ} {e g : ℕ → D} {N n' : ℕ} {X : Finset D}
    (he : ∀ i < N, gid (e i) = i) (hesurj : ∀ d, ∃ i < N, e i = d)
    (hg : ∀ i j, i < j → j < n' → gid (g i) < gid (g j)) (hX : ∀ d ∈ X, ∃ i < n', g i = d) :
    findE e N X = findE g n' X := by
  by_cases hne : X.Nonempty
  · obtain ⟨d, hd, hmin⟩ := X.exists_min_image gid hne
    have hemono : ∀ i j, i < j → j < N → gid (e i) < gid (e j) := fun i j hij hj => by
      rw [he i (by omega), he j hj]; exact hij
    rw [findE_eq_min hemono (fun d _ => hesurj d) hd hmin, findE_eq_min hg hX hd hmin]
  · rw [not_nonempty_iff_eq_empty] at hne
    subst hne
    rw [findE_eq_none (fun i _ => Finset.notMem_empty _), findE_eq_none (fun i _ => Finset.notMem_empty _)]

theorem firstE_gidLoc {gid : D → ℕ} {e g : ℕ → D} {N n' : ℕ} {X : Finset D} (d₀ : D)
    (he : ∀ i < N, gid (e i) = i) (hesurj : ∀ d, ∃ i < N, e i = d)
    (hg : ∀ i j, i < j → j < n' → gid (g i) < gid (g j)) (hX : ∀ d ∈ X, ∃ i < n', g i = d) :
    firstE e N X d₀ = firstE g n' X d₀ := by
  unfold firstE; rw [findE_gidLoc he hesurj hg hX]

end BKMNW

end PlanarFlow
