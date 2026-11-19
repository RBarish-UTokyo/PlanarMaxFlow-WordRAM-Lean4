module

public import PlanarFlow.BKMNW.PpPP

/-!
# Reading the flow from the output frame

* `strictMono_id`: a strictly increasing map of `[0, m)` onto `[0, N)` is the identity, `m = N`;
* **`lay_en_eq`**: the numbering of the root's frame (`Lay`, increasing in `gid`, onto the darts)
  is the numbering `enS` of the sorted slots;
* **`nlRunX_eq`**: on a dart that is not a loop, the algorithm on the preprocessed map with
  explicit pendant darts (`nlRunX`) is the flow of the root call (`arunL`) on the dart `old x`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap PlanarSeparator.StDart MfDrv

/-- **A strictly increasing map of `[0, m)` onto `[0, N)` is the identity.** -/
lemma strictMono_id {g : ℕ → ℕ} {m N : ℕ} (hmono : ∀ i j, i < j → j < m → g i < g j)
    (hlt : ∀ i < m, g i < N) (hon : ∀ k < N, ∃ i < m, g i = k) : m = N ∧ ∀ i < m, g i = i := by
  have hge : ∀ i < m, i ≤ g i := by
    intro i hi
    induction i with
    | zero => omega
    | succ i ih => have := hmono i (i + 1) (by omega) hi; have := ih (by omega); omega
  have hmN : m ≤ N := by
    rcases Nat.eq_zero_or_pos m with h | h
    · omega
    · have := hge (m - 1) (by omega); have := hlt (m - 1) (by omega); omega
  have hNm : N ≤ m := by
    have hsub : range N ⊆ (range m).image g := fun k hk => by
      obtain ⟨i, hi, e⟩ := hon k (mem_range.1 hk)
      exact mem_image.2 ⟨i, mem_range.2 hi, e⟩
    have := card_le_card hsub
    rw [card_range] at this
    exact this.trans (card_image_le.trans (card_range m).le)
  have hmN' : m = N := le_antisymm hmN hNm
  refine ⟨le_antisymm hmN hNm, fun i hi => le_antisymm ?_ (hge i hi)⟩
  -- downward: `g i ≤ i`
  have key : ∀ k, k < m → g (m - 1 - k) ≤ m - 1 - k := by
    intro k
    induction k with
    | zero => intro h; have := hlt (m - 1) (by omega); rw [Nat.sub_zero]; omega
    | succ k ih =>
      intro h
      have := ih (by omega)
      have := hmono (m - 1 - (k + 1)) (m - 1 - k) (by omega) (by omega)
      omega
  have := key (m - 1 - i) (by omega)
  rwa [show m - 1 - (m - 1 - i) = i by omega] at this

variable {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable {M : CombMap (Fin n) V F} (hrot : M.RotTrans)
variable [Nonempty (TDart M ⊕ (PVert M × Bool))]

include hrot in
/-- **The numbering of the root frame is the numbering of the sorted slots.** -/
theorem lay_en_eq {vn : V → ℕ} {K N : ℕ} {srt pos : ℕ → ℕ} (h : Sorted M vn K N srt pos)
    {u : TDart M ⊕ (PVert M × Bool) → ℤ} {S T : Finset (PVert M ⊕ PVert M)} {Z : ℕ}
    {x : MCall (LP M hrot)} (hx : x.1.piece = univ) (hH : x.2.1 = []) {m : ℕ}
    {en : ℕ → TDart M ⊕ (PVert M × Bool)} {dd : ℕ} {mem : ℕ → ℕ}
    (hL : Lay (LP M hrot) (gidS pos) u S T Z x m en dd mem) :
    m = N ∧ ∀ i < m, en i = enS (M := M) srt i := by
  have hall : ∀ y, y ∈ pdarts (LP M hrot) x.1.piece x.2.1 := fun y => by
    rw [hx, hH, pdarts_univ_nil]; exact mem_univ _
  obtain ⟨e1, e2⟩ := strictMono_id (g := fun i => gidS (M := M) pos (en i)) (m := m) (N := N)
    (fun i j hij hj => hL.en_mono i j hij hj)
    (fun i hi => (enS_pos_enc hrot h (en i)).1)
    (fun k hk => by
      obtain ⟨i, hi, ei⟩ := hL.en_surj (enS (M := M) srt k) (hall _)
      refine ⟨i, hi, ?_⟩
      show gidS pos (en i) = k
      rw [ei]; unfold gidS; rw [enc_enS hrot h hk, h.pos_srt k hk])
  refine ⟨e1, fun i hi => ?_⟩
  have hg : gidS (M := M) pos (en i) = i := e2 i hi
  have := (enS_pos_enc hrot h (en i)).2
  unfold gidS at hg
  rw [hg] at this
  exact this.symm

section Run

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

set_option synthInstance.maxHeartbeats 400000 in
/-- **The algorithm on a dart that is not a loop is the flow of the root call.** -/
theorem nlRunX_eq {M : CombMap D V F} (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (e : PVert M → TDart M) (he : ∀ w, (tnlMap M).tail (e w) = w) (u : D → ℤ) (S T : Finset V)
    (τ : ADec (lpreMapX M e he)) (O : PlaneOracles.{0}) (hτ : τ.piece = univ) (x : D)
    (hx : x ∈ nlDarts M) :
    nlRunX M e he u S T τ O x =
      arunL (lpreMapX M e he) O (preCap (hrot := nlMap_rotTrans) (fun y => u y.1) (nlTerm M S)
        (nlTerm M T)) (preTerm (hrot := nlMap_rotTrans) (nlTerm M S))
        (preTerm (hrot := nlMap_rotTrans) (nlTerm M T)) τ [] (rotPerm (lpreMapX M e he))
        ⟨.inl (old ⟨x, hx⟩), by rw [hτ, pdarts_univ_nil]; exact mem_univ _⟩ := by
  have hne : Nonempty (SDart (nlDarts M)) := ⟨⟨x, hx⟩⟩
  have hP := nlMap_isPlane hM hrot hface hx
  have hT := triMap_isPlane hP nlMap_rotTrans nlMap_faceTrans
  have hL : (lpreMapX M e he).IsPlane := CombMap.pendant_isPlane he hT
  have hLr : (lpreMapX M e he).RotTrans :=
    CombMap.pendant_rotTrans he (triMap_rotTrans nlMap_rotTrans)
  have hLf : (lpreMapX M e he).FaceTrans :=
    CombMap.pendant_faceTrans he (triMap_faceTrans nlMap_rotTrans)
  have hNe : Nonempty (TDart M ⊕ (PVert M × Bool)) := ⟨.inl (old ⟨x, hx⟩)⟩
  have hroot : PieceInv (lpreMapX M e he) τ.piece [] (rotPerm (lpreMapX M e he)) := by
    rw [hτ]; exact pieceInv_root hL hLr hLf hNe
  have hcond : PieceInv (lpreMapX M e he) τ.piece [] (rotPerm (lpreMapX M e he)) ∧
      (∀ d, d ∈ τ.piece) ∧ Nonempty (TDart M ⊕ (PVert M × Bool)) :=
    ⟨hroot, fun d => by rw [hτ]; exact mem_univ _, hNe⟩
  unfold nlRunX nlExt
  rw [ppDiteT hx]
  unfold runL
  rw [ppDiteT hcond]
  beta_reduce
  unfold Emb.ext
  have hm : (Sum.inl (old ⟨x, hx⟩) : TDart M ⊕ (PVert M × Bool)) ∈
      pdarts (lpreMapX M e he) τ.piece [] := by rw [hτ, pdarts_univ_nil]; exact mem_univ _
  exact (Emb.inj (rootEmb hcond.1 ⟨Classical.choice hcond.2.2, mem_pdarts_nil hcond.2.1 _⟩)).extend_apply _ _ (⟨_, hm⟩ : SDart (pdarts (lpreMapX M e he) τ.piece []))

end Run

end Pp

end BKMNW

end PlanarFlow
