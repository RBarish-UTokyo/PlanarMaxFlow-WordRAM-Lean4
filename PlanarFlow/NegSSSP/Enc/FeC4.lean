module

public import PlanarFlow.NegSSSP.Enc.FeC3

/-!
# The composed encoder, phase C: the residues of the real constants

* `feEnc`, **`feEnc_exec`**: `encResProg_fd` with its registers: the isolating lengths at `ISO`,
  **the residues of Klein's real constants at `RK` (`KSlotN.res`)** modulo `2 Hc + 1`,
  `Hc = kcnHc A FN (tripW …) k ≤ kcnHc A FN (N Lmax) k`, `fdHI ≤ Hc`, from the lengths at `SL`,
  the weights at `WW`, the flags in the slot and the reach bits at `RD`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-! ### The residues on the machine -/

/-- The registers of `encResProg`. -/
def feEncRegs (p : FeP) : List (ℕ × ℕ) :=
  [(2200, p.N), (2201, p.SL), (2202, p.WW), (2203, p.ISO), (2204, p.A), (2205, p.N),
    (2206, p.FN), (2100, p.N), (2101, p.ISO), (2102, p.β + 6 * p.N), (2103, p.RD), (2104, p.RK),
    (2105, p.A), (2106, p.k), (2107, p.FN)]

/-- **The isolating lengths and the residues of the real constants.** -/
def feEnc (p : FeP) : Stmt := .seq (feSet (feEncRegs p)) encResProg

theorem feEnc_natOnly (p : FeP) : natOnly (feEnc p) = true := by
  simp only [feEnc, natOnly, feSet_natOnly, encResProg_natOnly, Bool.and_self]

set_option maxHeartbeats 2000000 in
open Classical in
/-- **The real part of the slot on the machine** (see the module docstring). -/
theorem feEnc_exec {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ₀ : fd.DQ ≃ Fin (Fintype.card fd.DQ)) (p : FeP) (hD : p.nD = Fintype.card fd.DQ)
    (hk : p.k = fd.k) (hV : p.nV = Fintype.card fd.VQ) (hF : p.nF = Fintype.card fd.FQ)
    (hW : p.END ≤ W)
    (hLm : feIsoB p.A p.N p.FN (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat ≤ p.Lmax)
    (hLW : p.Lmax ≤ W) (hH : 2 * kcnHc p.A p.FN (p.N * p.Lmax) p.k + 1 ≤ W)
    {w : SrcD fd.DQ fd.k → ℤ} (hwB : ∀ d, |w d| ≤ Fintype.card (SrcF fd.FQ fd.k))
    (c : Config) (hc : WordsBounded W c)
    (hSL : ∀ d : SrcD fd.DQ fd.k, c.nmem (p.SL + srcNum σ₀ d) = (srcLen (faceLen fd.P' fd.e ℓ)
      (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)) d).toNat)
    (hWW : ∀ d, c.nmem (p.WW + srcNum σ₀ d) = (w d + Fintype.card (SrcF fd.FQ fd.k)).toNat)
    (hfl : ∀ d, c.nmem (p.β + 6 * p.N + srcNum σ₀ d) =
      if d ∈ srcPiece fd.k (fd.P'.image fd.e) then 1 else 0)
    (hrb : ∀ d, c.nmem (p.RD + srcNum σ₀ d) =
      if MSSP.Reach (MSSP.pieceGraph (srcMap fd.inst.cycle) (srcPiece fd.k (fd.P'.image fd.e))
        (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
          (srcNum σ₀))) (tripDst (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)
        ((srcMap fd.inst.cycle).tail d) then 1 else 0) :
    ∃ c' t, Exec P W (feEnc p) c c' t ∧ t ≤ 15 + (47 * p.N + 58) ∧
      (∀ d, c'.nmem (p.ISO + srcNum σ₀ d) = (srcIso (V := fd.VQ) (F := fd.FQ) fd.k
        (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀) d).toNat) ∧
      (∀ a < 3 * p.N + 3, c'.nmem (p.RK + a) =
        resW (2 * kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e))
          (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
            (srcNum σ₀))).toNat fd.k + 1)
          (kConst (SrcV fd.VQ fd.k) (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle)
            (srcPiece fd.k (fd.P'.image fd.e))
            (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
              (srcNum σ₀)) (srcNum σ₀) a : ℝ)) ∧
      fdHI fd ℓ (srcNum σ₀) w ≤ (kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e))
          (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
            (srcNum σ₀))).toNat fd.k : ℝ) ∧
      kcnHc p.A p.FN (tripW (srcPiece fd.k (fd.P'.image fd.e))
          (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w
            (srcNum σ₀))).toNat fd.k ≤ kcnHc p.A p.FN (p.N * p.Lmax) p.k ∧
      (∀ a, (a < p.ISO ∨ p.ISO + p.N ≤ a) → (a < p.RK ∨ p.RK + 3 * p.N + 3 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨cD, cV, cF⟩ := fe_cards (k := fd.k) (D := fd.DQ) (V := fd.VQ) (F := fd.FQ) p hD hk hV hF
  have hnnQ : ∀ y, 0 ≤ faceLen fd.P' fd.e ℓ y := fun y => faceLen_nonneg _ _ _ y
  have hIso : ∀ d, (srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e)
      (faceLen fd.P' fd.e ℓ) w (srcNum σ₀) d).toNat ≤ p.Lmax := fun d => by
    have := srcIso_le (V := fd.VQ) (F := fd.FQ) (S := fd.P'.image fd.e) hnnQ
      (faceLen_le_srcW fd ℓ) hwB (srcNum σ₀) d
    rw [cD, cV, cF] at this; omega
  have hTW := tripW_srcIso_le (V := fd.VQ) (F := fd.FQ) (S := fd.P'.image fd.e) hnnQ hwB
    (srcNum σ₀) hIso (srcPiece fd.k (fd.P'.image fd.e))
  rw [cD] at hTW
  have hHle := kcnHc_mono (nV := p.A) (nF := p.FN) (k := p.k) hTW
  have hSW1 : 1 ≤ (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat := by
    have := sum_nonneg fun z (_ : z ∈ fd.P'.image fd.e) => hnnQ z
    unfold srcW; omega
  have hN1 : MSSP.isoN1 p.A p.N p.FN ≤ W := by
    have : MSSP.isoN1 p.A p.N p.FN ≤ MSSP.isoN1 p.A p.N p.FN *
        (srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ)).toNat := Nat.le_mul_of_pos_right _ hSW1
    unfold feIsoB at hLm; omega
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ : p.β + 6 * p.N + p.N ≤ p.SL ∧ p.SL + p.N ≤ p.WW ∧
      p.WW + p.N ≤ p.RD ∧ p.RD + p.N ≤ p.ISO ∧ p.ISO + p.N = p.RK ∧
      p.RK + 3 * p.N + 3 ≤ W := by
    have hE := p.eqs; have hsl := p.slot_le; clear * - hE hsl hW; omega
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hr₁, hm₁, hrm₁, ho₁⟩ :=
    feSet_exec (P := P) (feEncRegs p) (by
      intro q hq; simp only [feEncRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      have hA : p.A ≤ p.RK := by have := p.eqs; clear * - this; omega
      have hF' : p.FN ≤ p.RK := by have := p.eqs; clear * - this; omega
      have hk' : p.k ≤ p.RK := by have := p.eqs; clear * - this; omega
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> simp only <;> clear * - l1 l2 l3 l4 l5 l6 hA hF' hk' <;> omega) c hc
  have hm' : ∀ a, c₁.nmem a = c.nmem a := fun a => by rw [hm₁]
  have hHW : 2 * kcnHc (Fintype.card (SrcV fd.VQ fd.k)) (Fintype.card (SrcF fd.FQ fd.k))
      (tripW (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k
        (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀))).toNat fd.k + 1 ≤ W := by
    rw [cV, cF]; rw [hk] at hH hHle; omega
  rw [← cD] at l1 l2 l3 l4 l5 l6
  obtain ⟨c₂, k₂, e₂, hk₂, hI, hR, h25, -, hHI, hm₂, -, hr₂, hrm₂, ho₂⟩ :=
    encResProg_fd (P := P) fd ℓ (srcNum σ₀) hwB (SLb := p.SL) (WWb := p.WW) (ISb := p.ISO)
      (Sb := p.β + 6 * p.N) (Rb := p.RD) (Ob := p.RK)
      ⟨by omega, by omega, by omega, by omega, by omega⟩
      ⟨by rw [← cD]; omega, by omega, by omega, by omega, by rw [← cD]; omega, by omega,
        by omega⟩
      (by rw [← cD]; omega) (by omega) (by rw [cV, cD, cF]; exact hN1)
      (fun d => le_trans (hIso d) hLW) hHW c₁ e₁.wb_right
      (by rw [hn₁, cD]; simp [feEncRegs, feSetV]) (by rw [hn₁]; simp [feEncRegs, feSetV])
      (by rw [hn₁]; simp [feEncRegs, feSetV]) (by rw [hn₁]; simp [feEncRegs, feSetV])
      (by rw [hn₁, cV]; simp [feEncRegs, feSetV]) (by rw [hn₁, cD]; simp [feEncRegs, feSetV])
      (by rw [hn₁, cF]; simp [feEncRegs, feSetV]) (by rw [hn₁, cD]; simp [feEncRegs, feSetV])
      (by rw [hn₁]; simp [feEncRegs, feSetV]) (by rw [hn₁]; simp [feEncRegs, feSetV])
      (by rw [hn₁]; simp [feEncRegs, feSetV]) (by rw [hn₁]; simp [feEncRegs, feSetV])
      (by rw [hn₁, cV]; simp [feEncRegs, feSetV]) (by rw [hn₁]; simp [feEncRegs, feSetV, hk])
      (by rw [hn₁, cF]; simp [feEncRegs, feSetV])
      (fun d => by rw [hm']; exact hSL d) (fun d => by rw [hm']; exact hWW d)
      (fun d => by
        rw [hm', hfl d]
        by_cases h : d ∈ srcPiece fd.k (fd.P'.image fd.e) <;> simp [h])
      (fun d _ => by
        rw [hm', hrb d]
        by_cases h : MSSP.Reach (MSSP.pieceGraph (srcMap fd.inst.cycle)
          (srcPiece fd.k (fd.P'.image fd.e)) (srcIso (V := fd.VQ) (F := fd.FQ) fd.k
            (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w (srcNum σ₀)))
          (tripDst (srcMap fd.inst.cycle) fd.k (srcG fd.inst.cycle) 0)
          ((srcMap fd.inst.cycle).tail d) <;> simp [h])
  rw [cV, cF] at h25
  rw [h25] at hR hHI
  have hHle' := hHle
  rw [hk] at hHle'
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by simp [feEncRegs] at hk₁; rw [cD] at hk₂; omega,
    hI, ?_, hHI, le_of_le_of_eq hHle' (by rw [hk]), fun a h1 h2 => ?_, by rw [hr₂, hr₁], by rw [hrm₂, hrm₁],
    by rw [ho₂, ho₁]⟩
  · intro a ha; rw [← cD] at ha; exact hR a ha
  · rw [← cD] at h1 h2; rw [hm₂ a h1 h2, hm']

end NegSSSP

end PlanarFlow
