module

public import PlanarFlow.BKMNW.MsStC

/-!
# The Klein start of an MSSP call, part C: the words of the lengths are the isolating lengths

* **`cl_cutLen`**: the copy lengths written by `msB2` (`CL[cE i] = LEN[i]` off the path, `0`
  elsewhere below `nD`) are the lengths `cutLen ℓ` of the cut, by the numbers `σ d = cutIx d`;
* **`ln_kLen`**: the word `CL N₁ + WM N₃ + N₂ + σ d` written by `msB3` (with `WM = #CutF + treeW C`)
  is the isolating length `kLen (ccut …) (treeW C) σ d` of `mssp_explicit` (as a natural word),
  `#CutV = cV`, `#CutD = nD`, `#CutF = cF` (`card_cutD`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset Function NsStep CombMap

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **The copy lengths are the lengths of the cut.** -/
theorem cl_cutLen {en : ℕ → D} {m : ℕ} (h : EnumOK M en m) (Pa : SPath M) (hk : 0 < Pa.k)
    {ℓ : D → ℤ} (hnn : ∀ e, 0 ≤ ℓ e) {CL Lb : ℕ} (mem lmem : ℕ → ℕ)
    (hln : ∀ i < m, (lmem (Lb + i) : ℤ) = ℓ (en i))
    (hcp : ∀ i < m, en i ∉ Pa.darts → mem (CL + cE Pa.darts en i) = lmem (Lb + i))
    (hz : ∀ j < nEc Pa.darts en m + 4 * nTc M Pa.darts en m,
      (∀ i < m, en i ∉ Pa.darts → cE Pa.darts en i ≠ j) → mem (CL + j) = 0)
    (d : CutD M Pa.darts) :
    (mem (CL + StEnc.enEq (cQ h Pa hk) d) : ℤ) = cutLen M Pa.darts ℓ d := by
  rw [enEq_cut Pa.rev_mem_darts' h (cD0 Pa hk)]
  rcases d with ⟨e, he⟩ | t | t | t | t
  · show (mem (CL + cE Pa.darts en (ixOf en m e)) : ℤ) = ℓ e
    have hi := ixOf_lt h e
    have hen := en_ixOf h e
    rw [hcp _ hi (by rw [hen]; exact he), hln _ hi, hen]
  all_goals
    have hlt := cutIx_lt (L := Pa.darts) h (M := M) (en := en) (m := m)
    simp only [cutLen, Nat.cast_eq_zero]
    refine hz _ ?_ fun i hi hn => ?_
  all_goals first
    | (have := hlt (.inr (.inl t)); exact this)
    | (have := hlt (.inr (.inr (.inl t))); exact this)
    | (have := hlt (.inr (.inr (.inr (.inl t)))); exact this)
    | (have := hlt (.inr (.inr (.inr (.inr t)))); exact this)
    | (have := cnt_lt (fun j => en j ∉ Pa.darts) hi hn; simp only [cutIx, nEc, cE] at this ⊢; omega)

/-- **The words of the lengths are the isolating lengths.** -/
theorem ln_kLen (hM : M.IsPlane) (hrot : M.RotTrans) {en : ℕ → D} {m : ℕ} (h : EnumOK M en m)
    (Pa : SPath M) (hk : 0 < Pa.k) {ℓ : D → ℤ} (hnn : ∀ e, e ∉ Pa.darts → 0 ≤ ℓ e)
    (hnn' : ∀ e, 0 ≤ ℓ e) {cV cF : ℕ} (τv : CutV M Pa.darts ≃ Fin cV)
    (τf : CutF M Pa.darts ≃ Fin cF) (C : STFlow.DTree (cutMap Pa.rev_mem_darts').dual.dual)
    (mem : ℕ → ℕ) {CL WM : ℕ}
    (hCL : ∀ d, (mem (CL + StEnc.enEq (cQ h Pa hk) d) : ℤ) = cutLen M Pa.darts ℓ d)
    (hWM : ∀ d, (mem (WM + StEnc.enEq (cQ h Pa hk) d) : ℤ) = cF + MSSP.treeW C d)
    (d : CutD M Pa.darts) :
    mem (CL + StEnc.enEq (cQ h Pa hk) d) *
        MSSP.isoN1 cV (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) cF +
      mem (WM + StEnc.enEq (cQ h Pa hk) d) * MSSP.isoN3 cV (nEc Pa.darts en m +
        4 * nTc M Pa.darts en m) +
      MSSP.isoN2 cV (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) cF +
      (StEnc.enEq (cQ h Pa hk) d : ℕ) =
    (MsCall.kLen (ccut hM hrot Pa hk ℓ hnn) (MSSP.treeW C) (StEnc.enEq (cQ h Pa hk)) d).toNat := by
  have eV : Fintype.card (CutV M Pa.darts) = cV := by rw [Fintype.card_congr τv, Fintype.card_fin]
  have eF : Fintype.card (CutF M Pa.darts) = cF := by rw [Fintype.card_congr τf, Fintype.card_fin]
  have eD : Fintype.card (CutD M Pa.darts) = nEc Pa.darts en m + 4 * nTc M Pa.darts en m :=
    card_cutD h
  simp only [MsCall.kLen, MSSP.isoLen, eV, eF, eD, ccut_len]
  have h1 := hCL d
  have h2 := hWM d
  rw [← h1, show (MSSP.treeW C d + (cF : ℤ)) = (mem (WM + StEnc.enEq (cQ h Pa hk) d) : ℤ) by
    rw [h2]; ring]
  have : ((MSSP.isoN1 cV (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) cF : ℕ) : ℤ) *
      (mem (CL + StEnc.enEq (cQ h Pa hk) d) : ℤ) +
      (MSSP.isoN2 cV (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) cF : ℤ) +
      (MSSP.isoN3 cV (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) : ℤ) *
      (mem (WM + StEnc.enEq (cQ h Pa hk) d) : ℤ) + ((StEnc.enEq (cQ h Pa hk) d : ℕ) : ℤ) =
      ((mem (CL + StEnc.enEq (cQ h Pa hk) d) *
        MSSP.isoN1 cV (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) cF +
      mem (WM + StEnc.enEq (cQ h Pa hk) d) * MSSP.isoN3 cV (nEc Pa.darts en m +
        4 * nTc M Pa.darts en m) +
      MSSP.isoN2 cV (nEc Pa.darts en m + 4 * nTc M Pa.darts en m) cF +
      (StEnc.enEq (cQ h Pa hk) d : ℕ) : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

end MsEnc

end BKMNW

end PlanarFlow
