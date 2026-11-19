module

public import PlanarFlow.NegSSSP.Enc.FeC2
public import PlanarFlow.NegSSSP.KEncNatA

/-!
# The composed encoder, phase C: bounds on the isolating lengths, the residues

* `feIsoB nV nD nF W₀`: `N₁ W₀ + N₂ + 2 N₃ nF + nD`; `srcIso_le`: **every isolating length is at
  most `feIsoB #V' #D' #F' (srcW S ℓ)`** (lengths `≥ 0`, at most `srcW` everywhere, e.g. zero off
  the piece, `|w| ≤ #F'`); `tripW_srcIso_le`: `tripW ≤ #D' · Lmax`; `kcnHc_mono`.
* `faceLen_le_srcW`: the lengths of a one-face instance are at most `srcW`.
* `feEnc`, **`feEnc_exec`**: `encResProg_fd` with its registers: the isolating lengths at `ISO`,
  **the residues of Klein's real constants at `RK` (`KSlotN.res`)**, `Hc = kcnHc …` in `r2125`,
  `fdHI ≤ Hc`, from the lengths at `SL`, the weights at `WW`, the flags in the slot and the reach
  bits at `RD`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The bound of the isolating lengths. -/
def feIsoB (nV nD nF W₀ : ℕ) : ℕ :=
  MSSP.isoN1 nV nD nF * W₀ + MSSP.isoN2 nV nD nF + MSSP.isoN3 nV nD * (2 * nF) + nD

lemma kcnHc_mono {nV nF a b k : ℕ} (h : a ≤ b) : kcnHc nV nF a k ≤ kcnHc nV nF b k := by
  unfold kcnHc; gcongr

section Bounds

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {k : ℕ} {S : Finset D} {ℓ : D → ℤ}

/-- **Every isolating length is at most `feIsoB`.** -/
theorem srcIso_le (hnn : ∀ d, 0 ≤ ℓ d) (hle : ∀ d, ℓ d ≤ srcW S ℓ)
    {w : SrcD D k → ℤ} (hwB : ∀ d, |w d| ≤ Fintype.card (SrcF F k))
    (σ : SrcD D k ≃ Fin (Fintype.card (SrcD D k))) (d : SrcD D k) :
    (srcIso (V := V) (F := F) k S ℓ w σ d).toNat ≤
      feIsoB (Fintype.card (SrcV V k)) (Fintype.card (SrcD D k)) (Fintype.card (SrcF F k))
        (srcW S ℓ).toNat := by
  have h0 := srcIso_nonneg (V := V) (F := F) (S := S) hnn hwB σ d
  have hW : 0 ≤ srcW S ℓ := by
    have := sum_nonneg fun d (_ : d ∈ S) => hnn d
    unfold srcW; omega
  have hl : srcLen ℓ (srcW S ℓ) d ≤ srcW S ℓ := by
    rcases d with d | ⟨i, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [srcLen, hle, hW]
  have hl0 : 0 ≤ srcLen ℓ (srcW S ℓ) d := by
    rcases d with d | ⟨i, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [srcLen, hnn, hW]
  have hw := abs_le.1 (hwB d)
  have hσ := (σ d).2
  unfold srcIso MSSP.isoLen at *
  unfold feIsoB
  set n1 := MSSP.isoN1 (Fintype.card (SrcV V k)) (Fintype.card (SrcD D k))
    (Fintype.card (SrcF F k))
  set n3 := MSSP.isoN3 (Fintype.card (SrcV V k)) (Fintype.card (SrcD D k))
  have e1 : (n1 : ℤ) * srcLen ℓ (srcW S ℓ) d ≤ n1 * (srcW S ℓ).toNat := by
    rw [Int.toNat_of_nonneg hW]; exact mul_le_mul_of_nonneg_left hl (by positivity)
  have e2 : (n3 : ℤ) * (w d + Fintype.card (SrcF F k)) ≤ n3 * (2 * Fintype.card (SrcF F k)) :=
    mul_le_mul_of_nonneg_left (by omega) (by positivity)
  rw [Int.toNat_le]
  push_cast
  linarith

/-- **The total length of the piece is at most `#D' · Lmax`.** -/
theorem tripW_srcIso_le (hnn : ∀ d, 0 ≤ ℓ d) {w : SrcD D k → ℤ}
    (hwB : ∀ d, |w d| ≤ Fintype.card (SrcF F k))
    (σ : SrcD D k ≃ Fin (Fintype.card (SrcD D k))) {Lmax : ℕ}
    (hL : ∀ d, (srcIso (V := V) (F := F) k S ℓ w σ d).toNat ≤ Lmax) (S' : Finset (SrcD D k)) :
    (tripW S' (srcIso (V := V) (F := F) k S ℓ w σ)).toNat ≤ Fintype.card (SrcD D k) * Lmax := by
  have h1 : tripW S' (srcIso (V := V) (F := F) k S ℓ w σ) ≤ ∑ _d ∈ S', (Lmax : ℤ) := by
    unfold tripW
    refine sum_le_sum fun d _ => ?_
    have h0 := srcIso_nonneg (V := V) (F := F) (S := S) hnn hwB σ d
    rw [abs_of_nonneg h0]
    have := hL d
    omega
  rw [sum_const, nsmul_eq_mul] at h1
  have h2 : (S'.card : ℤ) ≤ Fintype.card (SrcD D k) := by exact_mod_cast card_le_univ S'
  have h3 : (S'.card : ℤ) * Lmax ≤ Fintype.card (SrcD D k) * Lmax :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  omega

end Bounds

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **The lengths of a one-face instance are at most `srcW`.** -/
lemma faceLen_le_srcW {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (y : fd.DQ) : faceLen fd.P' fd.e ℓ y ≤ srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) := by
  classical
  have hnn := faceLen_nonneg fd.P' fd.e ℓ
  unfold srcW
  by_cases hy : y ∈ fd.P'.image fd.e
  · have := single_le_sum (f := faceLen fd.P' fd.e ℓ) (fun z _ => hnn z) hy
    omega
  · have h0 : faceLen fd.P' fd.e ℓ y = 0 := by
      unfold faceLen
      refine dite_eq_right_iff.2 fun h => absurd ?_ hy
      obtain ⟨d, hd, rfl⟩ := h
      exact mem_image_of_mem _ hd
    have := sum_nonneg fun z (_ : z ∈ fd.P'.image fd.e) => hnn z
    omega

end NegSSSP

end PlanarFlow
