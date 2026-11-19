module

public import PlanarFlow.BKMNW.SmXA
public import PlanarFlow.BKMNW.ChoiceE

/-!
# The choice of the enumeration picks the dart of least `gid`

`mfDriveFrameX_cMach` and its variants assume `PkMin gid pc.pick` (the small decomposition's
choice is the dart of least global number). For `pc = pcChoiceE … e n d₀` with an enumeration
numbered by `gid` (`gid (e i) = i`) this holds: `findE_first` (the dart found is the first index
in `X`), **`pkMin_pcChoiceE`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The dart found by `findE` is at the first index whose dart is in `X`. -/
lemma findE_first {e : ℕ → D} {n : ℕ} {X : Finset D} {d : D} (h : findE e n X = some d) :
    ∃ i < n, e i = d ∧ ∀ j < i, e j ∉ X := by
  unfold findE at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [List.find?_range_eq_some] at hi
  obtain ⟨-, h2, h3⟩ := hi
  refine ⟨i, List.mem_range.1 h2, rfl, fun j hj hX => ?_⟩
  have := h3 j hj
  simp [hX] at this

variable (M) in
/-- **The choice of the enumeration picks the dart of least `gid`** when `gid (e i) = i`. -/
theorem pkMin_pcChoiceE {gid : D → ℕ} {Q : Finset V} {e : ℕ → D} {n : ℕ}
    (hsurj : ∀ d, ∃ i < n, e i = d) (hgid : ∀ i < n, gid (e i) = i) (d₀ : D) :
    PkMin gid (pcChoiceE M Q e n d₀).pick := by
  intro X ⟨y, hy⟩
  obtain ⟨j, hj, rfl⟩ := hsurj y
  obtain ⟨d, hd⟩ := findE_isSome hj hy
  have hpick : (pcChoiceE M Q e n d₀).pick X = d := by
    show firstE e n X d₀ = d
    unfold firstE; rw [hd]; rfl
  rw [hpick]
  refine ⟨findE_some hd, fun z hz => ?_⟩
  obtain ⟨i, hi, rfl, hmin⟩ := findE_first hd
  obtain ⟨k, hk, rfl⟩ := hsurj z
  rw [hgid i hi, hgid k hk]
  by_contra hlt
  exact hmin k (by omega) hz

end MfDrv

end BKMNW

end PlanarFlow
