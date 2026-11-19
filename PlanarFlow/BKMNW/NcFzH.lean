module

public import PlanarFlow.BKMNW.NcFzG
public import PlanarFlow.BKMNW.FixFrozen

/-!
# The meaning of `pfP`: the frame of the map with pendant edges

* **`MFr M' en m Z cap f d mem`**: a frame of a map `M'` with any dart type (no call of the
  decomposition): `m` darts numbered by `en` (bijectively onto the darts), the header `m` and the
  offset `Z`, `RV` (the reverse), `SG` (the rotation `next ∘ rev`), `CP = cap ≤ Z`, `FL = Z + f`.
  The arrays `GID`, `KR`, `HL` of the frames are not part of it (FixConservationOnPath does
  not read them).
* **`PfMean`**: the meaning of the input of `pfP` for a map `M₀` with a frame numbering `en₀`
  (`RV`, `SG`, the vertices = the orbits of `SG`, `CP = U`, `F1 = Z + f₁`, `DF = [tail ∈ Del]`).
* **`pend_frame`**: after `pfP` (`PfRes`), the memory at `d' = S + 12 + 16 m` is a frame
  (`MFr`) of **`M₀.pendant e he`** (for the choice `e v = en₀ (olab SG i)`, `i` any dart at `v`)
  with `m + 2n` darts (`n` = the number of vertices), offset `Z' = m Z`, capacities
  **`frCap M₀ U f₁ Del`** and flow **`frFlow M₀ f₁ Del`** (FixFrozen.lean), the numbering
  `en' i = inl (en₀ i)` (`i < m`), `inr (v_t, true)` (`m + t`), `inr (v_t, false)` (`m + n + t`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset WordRAM WordRAM.Machine OrbLab MfDrv CombMap

/-- **A frame of a map** with any dart type (see the module docstring). -/
structure MFr {D' V' F' : Type*} (M' : CombMap D' V' F') (en : ℕ → D') (m Z : ℕ)
    (cap f : D' → ℤ) (d : ℕ) (mem : ℕ → ℕ) : Prop where
  hm : mem d = m
  hz : mem (d + 3) = Z
  inj : ∀ i < m, ∀ j < m, en i = en j → i = j
  surj : ∀ y, ∃ i < m, en i = y
  rv : ∀ i < m, mem (d + 4 + m + i) < m ∧ en (mem (d + 4 + m + i)) = M'.rev (en i)
  sg : ∀ i < m, mem (d + 4 + 2 * m + i) < m ∧
    en (mem (d + 4 + 2 * m + i)) = M'.next (M'.rev (en i))
  cp : ∀ i < m, (mem (d + 4 + 3 * m + i) : ℤ) = cap (en i) ∧ mem (d + 4 + 3 * m + i) ≤ Z
  fl : ∀ i < m, (mem (d + 4 + 6 * m + i) : ℤ) = Z + f (en i)

variable {D₀ V₀ F₀ : Type*} [Fintype D₀] [DecidableEq D₀] [Fintype V₀] [DecidableEq V₀]
  {M₀ : CombMap D₀ V₀ F₀}

/-- **The meaning of the input of `pfP`** for a map `M₀` numbered by `en₀`. -/
structure PfMean (c : Config) (M₀ : CombMap D₀ V₀ F₀) (en₀ : ℕ → D₀) (d m Z F1b DFb CPb : ℕ)
    (U f₁ : D₀ → ℤ) (Del : Finset V₀) : Prop where
  inj : ∀ i < m, ∀ j < m, en₀ i = en₀ j → i = j
  surj : ∀ y, ∃ i < m, en₀ i = y
  rv : ∀ i < m, en₀ (c.nmem (d + 4 + m + i)) = M₀.rev (en₀ i)
  sg : ∀ i < m, en₀ (sgF d m c.nmem i) = M₀.next (M₀.rev (en₀ i))
  vert : ∀ i < m, ∀ j < m,
    (M₀.tail (en₀ i) = M₀.tail (en₀ j) ↔ olab (sgF d m c.nmem) i = olab (sgF d m c.nmem) j)
  vsurj : ∀ v, ∃ y, M₀.tail y = v
  cp : ∀ i < m, (c.nmem (CPb + i) : ℤ) = U (en₀ i)
  f1 : ∀ i < m, (c.nmem (F1b + i) : ℤ) = Z + f₁ (en₀ i)
  df : ∀ i < m, c.nmem (DFb + i) = if M₀.tail (en₀ i) ∈ Del then 1 else 0
  ub : ∀ y, 0 ≤ U y ∧ U y ≤ Z
  fb : ∀ y, -(Z : ℤ) ≤ f₁ y ∧ f₁ y ≤ Z

section Mean

variable {c c' : Config} {W d m Z S F1b DFb CPb n : ℕ} {en₀ : ℕ → D₀} {U f₁ : D₀ → ℤ}
  {Del : Finset V₀}

/-- The flag `Q` is `[the dart touches Del]`. -/
lemma PfMean.qF_eq (hI : PfIn c W d m Z S F1b DFb CPb)
    (hM : PfMean c M₀ en₀ d m Z F1b DFb CPb U f₁ Del) {i : ℕ} (hi : i < m) :
    qF c.nmem DFb (d + 4 + m) i = if en₀ i ∈ incSet M₀ Del then 1 else 0 := by
  have hr := hI.rv i hi
  have hhead : M₀.head (en₀ i) = M₀.tail (en₀ (c.nmem (d + 4 + m + i))) := by
    rw [hM.rv i hi]; rfl
  unfold qF
  rw [hM.df i hi, hM.df _ hr]
  simp only [incSet, mem_filter, mem_univ, true_and, hhead]
  split_ifs <;> simp_all

/-- The flow array of the fake frame: `x0F − Z = [dart touches Del] · f₁`. -/
lemma PfMean.x0F_eq (hI : PfIn c W d m Z S F1b DFb CPb)
    (hM : PfMean c M₀ en₀ d m Z F1b DFb CPb U f₁ Del) {i : ℕ} (hi : i < m) :
    ((x0F c.nmem F1b DFb (d + 4 + m) Z i : ℕ) : ℤ) - Z =
      if en₀ i ∈ incSet M₀ Del then f₁ (en₀ i) else 0 := by
  have hq := hM.qF_eq hI hi
  have hf := hM.f1 i hi
  unfold x0F
  rw [hq]
  split_ifs with h
  · simp only [Nat.mul_one]
    have : Z ≤ c.nmem (F1b + i) + Z := by omega
    push_cast [Nat.sub_eq_of_eq_add (show c.nmem (F1b + i) + Z = c.nmem (F1b + i) + Z from rfl)]
    omega
  · simp

/-- **A sum over the darts at the vertex of `en₀ i`** is a sum over the indices with the same
orbit label. -/
lemma PfMean.sum_vert (hM : PfMean c M₀ en₀ d m Z F1b DFb CPb U f₁ Del) (g : D₀ → ℤ) {i : ℕ}
    (hi : i < m) :
    ∑ y with M₀.tail y = M₀.tail (en₀ i), g y =
      ∑ j ∈ (range m).filter (fun j => olab (sgF d m c.nmem) j = olab (sgF d m c.nmem) i),
        g (en₀ j) := by
  symm
  refine Finset.sum_bij (fun j _ => en₀ j) (fun j hj => ?_) (fun a ha b hb e => ?_)
    (fun y hy => ?_) (fun j hj => rfl)
  · obtain ⟨h1, h2⟩ := mem_filter.1 hj
    simp only [mem_filter, mem_univ, true_and]
    exact (hM.vert j (mem_range.1 h1) i hi).2 h2
  · exact hM.inj a (mem_range.1 (mem_filter.1 ha).1) b (mem_range.1 (mem_filter.1 hb).1) e
  · obtain ⟨j, hj, rfl⟩ := hM.surj y
    simp only [mem_filter, mem_univ, true_and] at hy
    exact ⟨j, mem_filter.2 ⟨mem_range.2 hj, (hM.vert j hj i hi).1 hy⟩, rfl⟩

/-- **The frozen outflow from `DV` and `DG`.** -/
lemma PfMean.frozen_eq (hI : PfIn c W d m Z S F1b DFb CPb)
    (hM : PfMean c M₀ en₀ d m Z F1b DFb CPb U f₁ Del) {i : ℕ} (hi : i < m) :
    ((dvS (olab (sgF d m c.nmem)) (fun j => x0F c.nmem F1b DFb (d + 4 + m) Z j) m
        (olab (sgF d m c.nmem) i) : ℕ) : ℤ) -
      Z * (dvC (olab (sgF d m c.nmem)) m (olab (sgF d m c.nmem) i) : ℕ) =
      frozenOut M₀ f₁ Del (M₀.tail (en₀ i)) := by
  have e1 : frozenOut M₀ f₁ Del (M₀.tail (en₀ i)) =
      ∑ y with M₀.tail y = M₀.tail (en₀ i), (if y ∈ incSet M₀ Del then f₁ y else 0) := by
    unfold frozenOut
    rw [Finset.sum_filter, Finset.sum_filter]
    refine sum_congr rfl fun y _ => ?_
    by_cases h1 : M₀.tail y = M₀.tail (en₀ i) <;> by_cases h2 : y ∈ incSet M₀ Del <;> simp [h1, h2]
  rw [e1, hM.sum_vert _ hi]
  unfold dvS dvC
  rw [Nat.cast_sum, card_eq_sum_ones, Nat.cast_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 (mem_filter.1 hj).1
  rw [← hM.x0F_eq hI hj']
  simp

/-- The number of darts. -/
lemma PfMean.card_le (hM : PfMean c M₀ en₀ d m Z F1b DFb CPb U f₁ Del) :
    Fintype.card D₀ ≤ m := by
  have : (univ : Finset D₀) ⊆ (range m).image en₀ := fun y _ => by
    obtain ⟨i, hi, rfl⟩ := hM.surj y
    exact mem_image_of_mem _ (mem_range.2 hi)
  have := card_le_card this
  rw [card_univ] at this
  exact this.trans (card_image_le.trans (by simp))

/-- **The frozen outflow is at most `m Z`** in absolute value. -/
lemma PfMean.frozen_abs (hM : PfMean c M₀ en₀ d m Z F1b DFb CPb U f₁ Del) (v : V₀) :
    |frozenOut M₀ f₁ Del v| ≤ (m : ℤ) * Z := by
  unfold frozenOut
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have h1 : ∑ y with M₀.tail y = v ∧ y ∈ incSet M₀ Del, |f₁ y| ≤ ∑ _y : D₀, (Z : ℤ) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun y _ _ => abs_nonneg _).trans
      (sum_le_sum fun y _ => abs_le.2 ⟨(hM.fb y).1, (hM.fb y).2⟩)
  simp only [sum_const, card_univ, nsmul_eq_mul] at h1
  have h2 : ((Fintype.card D₀ : ℕ) : ℤ) ≤ m := by exact_mod_cast hM.card_le
  have hZ : (0 : ℤ) ≤ Z := by positivity
  nlinarith

end Mean

end NcFz

end BKMNW

end PlanarFlow
