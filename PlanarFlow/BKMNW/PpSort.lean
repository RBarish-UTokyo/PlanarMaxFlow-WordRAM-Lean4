module

public import PlanarFlow.BKMNW.PpIdx

/-!
# The input conventions of the max-flow program from sorted slots

The preprocessing program lists the valid slots (`ValidS`) sorted by their keys (`keyS`, the
number of the tail), `SRT[i]` for `i < N`, and the inverse `POS[SRT[i]] = i`. The darts are then
numbered by `en i = enc⁻¹ (SRT[i])` and `gid y = POS[enc y]`. This file proves that the arrays

* `REV[i] = POS[revS SRT[i]]`, `SIG[i] = POS[rotS SRT[i]]`, `RT[i] = POS[rtS SRT[i]]`,
* `CAP[i] = capS SRT[i]`, `KR[i] = krS SRT[i]`, `VT[i] = keyS SRT[i]`

meet the input conventions of the max-flow program (`MfMainGoal`, `MfMainSpec`) for the
preprocessed map with the explicit pendant darts `LP M hrot` and the vertex numbering `νX`:
`sortConv` (onto, `gid (en i) = i`, `Fintype.card = N`, `TailSorted`, and the six arrays).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap PlanarSeparator.StDart MfDrv

variable {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable (M : CombMap (Fin n) V F) (hrot : M.RotTrans)

/-- The data of a sorted list of the valid slots. -/
structure Sorted (vn : V → ℕ) (K N : ℕ) (srt pos : ℕ → ℕ) : Prop where
  valid : ∀ i < N, ValidS M (srt i)
  all : ∀ s, ValidS M s → ∃ i < N, srt i = s
  pos_srt : ∀ i < N, pos (srt i) = i
  sorted : ∀ i j, i < j → j < N → keyS M vn K (srt i) ≤ keyS M vn K (srt j)

variable {M}

namespace Sorted

variable {vn : V → ℕ} {K N : ℕ} {srt pos : ℕ → ℕ} (h : Sorted M vn K N srt pos)
include h

lemma pos_valid {s : ℕ} (hs : ValidS M s) : pos s < N ∧ srt (pos s) = s := by
  obtain ⟨i, hi, rfl⟩ := h.all s hs
  rw [h.pos_srt i hi]; exact ⟨hi, rfl⟩

end Sorted

variable [Nonempty (TDart M ⊕ (PVert M × Bool))]

/-- The numbering of the darts by the sorted slots. -/
noncomputable def enS (srt : ℕ → ℕ) (i : ℕ) : TDart M ⊕ (PVert M × Bool) :=
  invFun (enc M) (srt i)

/-- The global number of a dart: the position of its slot. -/
noncomputable def gidS (pos : ℕ → ℕ) (y : TDart M ⊕ (PVert M × Bool)) : ℕ := pos (enc M y)

variable {vn : V → ℕ} {K N : ℕ} {srt pos : ℕ → ℕ}

include hrot in
lemma enc_enS (h : Sorted M vn K N srt pos) {i : ℕ} (hi : i < N) :
    enc M (enS (M := M) srt i) = srt i := by
  obtain ⟨y, hy⟩ := valid_enc M (h.valid i hi)
  unfold enS; rw [← hy, leftInverse_invFun (enc_injective M hrot) y]

include hrot in
lemma enS_pos_enc (h : Sorted M vn K N srt pos) (y : TDart M ⊕ (PVert M × Bool)) :
    pos (enc M y) < N ∧ enS (M := M) srt (pos (enc M y)) = y := by
  obtain ⟨h1, h2⟩ := h.pos_valid (enc_valid M hrot y)
  refine ⟨h1, ?_⟩
  unfold enS; rw [h2, leftInverse_invFun (enc_injective M hrot) y]

include hrot in
/-- **An operation commuting with the slots is carried to the positions.** -/
lemma pos_op (h : Sorted M vn K N srt pos) {f : TDart M ⊕ (PVert M × Bool) → TDart M ⊕ (PVert M × Bool)}
    {fS : ℕ → ℕ} (hf : ∀ y, enc M (f y) = fS (enc M y)) {i : ℕ} (hi : i < N) :
    pos (fS (srt i)) < N ∧ enS (M := M) srt (pos (fS (srt i))) = f (enS srt i) := by
  rw [← enc_enS hrot h hi, ← hf]
  exact enS_pos_enc hrot h _

variable (cpN : Fin n → ℕ) (S T : Finset V)

include hrot in
/-- **The input conventions of the max-flow program from the sorted slots.** -/
theorem sortConv (h : Sorted M vn K N srt pos) :
    Fintype.card (TDart M ⊕ (PVert M × Bool)) = N ∧
    (∀ y, ∃ i < N, enS (M := M) srt i = y) ∧
    (∀ i < N, gidS (M := M) pos (enS srt i) = i) ∧
    TailSorted (LP M hrot) (gidS pos) (νX M vn K) ∧
    (∀ i < N, pos (revS M (srt i)) < N ∧
      enS (M := M) srt (pos (revS M (srt i))) = (LP M hrot).rev (enS srt i)) ∧
    (∀ i < N, pos (rotS M (srt i)) < N ∧
      enS (M := M) srt (pos (rotS M (srt i))) = rotPerm (LP M hrot) (enS srt i)) ∧
    (∀ i < N, ((capS M cpN S T (srt i) : ℕ) : ℤ) =
      preCap (hrot := nlMap_rotTrans) (fun y => (cpN y.1 : ℤ)) (nlTerm M S) (nlTerm M T)
        (enS srt i)) ∧
    (∀ i < N, krS M S T (srt i) = lrk (preTerm (hrot := nlMap_rotTrans) (nlTerm M S))
      (preTerm (hrot := nlMap_rotTrans) (nlTerm M T)) (hunion []) ((LP M hrot).tail (enS srt i))) ∧
    (∀ i < N, keyS M vn K (srt i) = νX M vn K ((LP M hrot).tail (enS srt i))) ∧
    (∀ i < N, enS (M := M) srt i ∈ pdarts (LP M hrot) (core (LP M hrot) (pendQ _) univ) [] →
      pos (rtS M (srt i)) < N ∧
      enS (M := M) srt (pos (rtS M (srt i))) = rootRot (LP M hrot) (pendQ _) (enS srt i)) := by
  have hE := fun {i : ℕ} (hi : i < N) => enc_enS hrot h hi
  refine ⟨?_, fun y => ⟨_, (enS_pos_enc hrot h y).1, (enS_pos_enc hrot h y).2⟩,
    fun i hi => by unfold gidS; rw [hE hi, h.pos_srt i hi], ?_,
    fun i hi => pos_op hrot h (enc_rev M hrot) hi,
    fun i hi => pos_op hrot h (enc_rot M hrot) hi,
    fun i hi => by rw [← hE hi]; exact enc_cap (M := M) (cpN := cpN) (S := S) (T := T) _,
    fun i hi => by rw [← hE hi]; exact enc_kr (M := M) (hrot := hrot) (S := S) (T := T) _,
    fun i hi => by rw [← hE hi]; exact enc_key (M := M) (hrot := hrot) (vn := vn) (K := K) _, ?_⟩
  · -- the cardinality
    have hb : Bijective (fun i : Fin N => enS (M := M) srt i.1) := by
      refine ⟨fun i j e => ?_, fun y => ?_⟩
      · have e' := congrArg (enc M) e
        simp only [hE i.2, hE j.2] at e'
        have := h.pos_srt i i.2
        rw [e', h.pos_srt j j.2] at this
        exact Fin.ext this.symm
      · obtain ⟨h1, h2⟩ := enS_pos_enc hrot h y
        exact ⟨⟨_, h1⟩, h2⟩
    rw [← Fintype.card_of_bijective hb, Fintype.card_fin]
  · -- the tails are sorted
    intro a b hab
    obtain ⟨ha, ea⟩ := enS_pos_enc hrot h a
    obtain ⟨hb, eb⟩ := enS_pos_enc hrot h b
    unfold gidS at hab
    have k := h.sorted _ _ hab hb
    rw [h.pos_valid (enc_valid M hrot a) |>.2, h.pos_valid (enc_valid M hrot b) |>.2,
      enc_key (M := M) (hrot := hrot) (vn := vn) (K := K),
      enc_key (M := M) (hrot := hrot) (vn := vn) (K := K)] at k
    exact k
  · -- the root rotation on the core
    intro i hi hc
    rw [pdarts_nil, mem_core_pendant (pe_tail M hrot)] at hc
    obtain ⟨t, ht⟩ : ∃ t, enS (M := M) srt i = .inl t := by
      rcases hy : enS (M := M) srt i with t | t
      · exact ⟨t, rfl⟩
      · rw [hy] at hc; simp at hc
    have hR : ∀ y, y.isLeft → enc M (rootRot (LP M hrot) (pendQ _) y) = rtS M (enc M y) := by
      intro y hy
      rcases y with t | t
      · exact enc_rt M hrot t
      · simp at hy
    rw [← hE hi, ← hR _ (by rw [ht]; rfl)]
    exact enS_pos_enc hrot h _

end Pp

end BKMNW

end PlanarFlow
