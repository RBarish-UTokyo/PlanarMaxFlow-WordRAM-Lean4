module

public import PlanarFlow.NegSSSP.KEncNatC
public import PlanarFlow.NegSSSP.KEncNatI

/-!
# The real part of the natural slot of a one-face instance, from the lengths and the weights

`isoProg` (`KEncNatI.lean`) then `kcnProg` (`KEncNatC.lean`), on the map with the sources copied
of a one-face instance `fd` (`Klein.srcMap fd.inst.cycle`), for its isolating lengths
`Klein.srcIso … ℓ w σ` (the lengths `faceLen fd.P' fd.e ℓ` with the sources copied, an
isolating weight `w`, `|w| ≤ #F'`, the numbering `σ` of the encoding):

* `encResProg := isoProg ; kcnProg` (natural words only, `encResProg_natOnly`).
* `encResProg_fd`: from the lengths with the sources copied (`SL[σ d]`), the shifted weights
  (`WW[σ d] = w d + #F'`, as `iwProg_treeW` writes them), the flags of the piece and the reach
  bits from the target of the first move (by `σ`), within `47 #D' + 58` steps it writes **the
  isolating lengths** (`(srcIso … d).toNat` at `ISb + σ d`) and **the field `res` of
  `KSlotN`** for these lengths (`RkN = Ob`, modulus `2 Hc + 1`), with
  `Hc = kcnHc #V' #F' (tripW …).toNat k` in `r2125` and **`fdHI fd ℓ σ w ≤ Hc`** — the inputs
  `Hc ≥ fdHI` and `KSlotN.res` of `kpartN_exec` / `node_exec_natN`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- **The isolating lengths, then the residues of the real constants.** -/
def encResProg : Stmt := .seq isoProg kcnProg

/-- **`encResProg` has no real instruction** (checked by the kernel). -/
theorem encResProg_natOnly : Klein.natOnly encResProg = true := by kernel_rfl

/-- The lengths with the sources copied are nonnegative. -/
lemma srcLen_nonneg {D : Type*} [Fintype D] {k : ℕ} {S : Finset D} {ℓ : D → ℤ}
    (hnn : ∀ d, 0 ≤ ℓ d) (d : Klein.SrcD D k) : 0 ≤ Klein.srcLen ℓ (Klein.srcW S ℓ) d := by
  have hW : 0 ≤ Klein.srcW S ℓ := by
    have := sum_nonneg fun d (_ : d ∈ S) => hnn d
    unfold Klein.srcW; omega
  rcases d with d | ⟨i, _ | _ | _ | _ | _ | _ | _ | _⟩ <;> simp [Klein.srcLen, hnn, hW]

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F} {P : Input} {W : ℕ}

set_option maxHeartbeats 1000000 in
/-- **The real part of the natural slot of a one-face instance** (see the module docstring).
Layout: the lengths `SL` at `SLb`, the weights `WW` at `WWb`, the isolating lengths written at
`ISb`, the flags at `Sb`, the reach bits at `Rb` (each `#D'` words), the output
`[Ob, Ob + 3 #D' + 3)`; the registers `2200 … 2206` and `2100 … 2107` hold the bases and the
sizes. -/
theorem encResProg_fd {X : Finset D} {B : Finset V} (fd : FaceData N X B) (ℓ : D → ℤ)
    (σ : Klein.SrcD fd.DQ fd.k ≃ Fin (Fintype.card (Klein.SrcD fd.DQ fd.k)))
    {w : Klein.SrcD fd.DQ fd.k → ℤ} (hwB : ∀ d, |w d| ≤ Fintype.card (Klein.SrcF fd.FQ fd.k))
    {SLb WWb ISb Sb Rb Ob : ℕ}
    (hIL : ISLay (Fintype.card (Klein.SrcD fd.DQ fd.k)) SLb WWb ISb W)
    (hKL : KNLay (Fintype.card (Klein.SrcD fd.DQ fd.k)) ISb Sb Rb Ob W)
    (hSI : Sb + Fintype.card (Klein.SrcD fd.DQ fd.k) ≤ ISb ∨
      ISb + Fintype.card (Klein.SrcD fd.DQ fd.k) ≤ Sb)
    (hRI : Rb + Fintype.card (Klein.SrcD fd.DQ fd.k) ≤ ISb ∨
      ISb + Fintype.card (Klein.SrcD fd.DQ fd.k) ≤ Rb)
    (hN1 : MSSP.isoN1 (Fintype.card (Klein.SrcV fd.VQ fd.k))
      (Fintype.card (Klein.SrcD fd.DQ fd.k)) (Fintype.card (Klein.SrcF fd.FQ fd.k)) ≤ W)
    (hIW : ∀ d, (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e)
      (faceLen fd.P' fd.e ℓ) w σ d).toNat ≤ W)
    (hH : 2 * kcnHc (Fintype.card (Klein.SrcV fd.VQ fd.k)) (Fintype.card (Klein.SrcF fd.FQ fd.k))
      (Klein.tripW (Klein.srcPiece fd.k (fd.P'.image fd.e))
        (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e)
          (faceLen fd.P' fd.e ℓ) w σ)).toNat fd.k + 1 ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (g00 : c.nreg 2200 = Fintype.card (Klein.SrcD fd.DQ fd.k)) (g01 : c.nreg 2201 = SLb)
    (g02 : c.nreg 2202 = WWb) (g03 : c.nreg 2203 = ISb)
    (g04 : c.nreg 2204 = Fintype.card (Klein.SrcV fd.VQ fd.k))
    (g05 : c.nreg 2205 = Fintype.card (Klein.SrcD fd.DQ fd.k))
    (g06 : c.nreg 2206 = Fintype.card (Klein.SrcF fd.FQ fd.k))
    (h00 : c.nreg 2100 = Fintype.card (Klein.SrcD fd.DQ fd.k)) (h01 : c.nreg 2101 = ISb)
    (h02 : c.nreg 2102 = Sb) (h03 : c.nreg 2103 = Rb) (h04 : c.nreg 2104 = Ob)
    (h05 : c.nreg 2105 = Fintype.card (Klein.SrcV fd.VQ fd.k)) (h06 : c.nreg 2106 = fd.k)
    (h07 : c.nreg 2107 = Fintype.card (Klein.SrcF fd.FQ fd.k))
    (hSL : ∀ d, c.nmem (SLb + σ d) =
      (Klein.srcLen (faceLen fd.P' fd.e ℓ) (Klein.srcW (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ))
        d).toNat)
    (hWW : ∀ d, c.nmem (WWb + σ d) = (w d + Fintype.card (Klein.SrcF fd.FQ fd.k)).toNat)
    (hfl : ∀ d, 0 < c.nmem (Sb + σ d) ↔ d ∈ Klein.srcPiece fd.k (fd.P'.image fd.e))
    (hrb : ∀ d ∈ Klein.srcPiece fd.k (fd.P'.image fd.e), 0 < c.nmem (Rb + σ d) ↔
      MSSP.Reach (MSSP.pieceGraph (Klein.srcMap fd.inst.cycle)
        (Klein.srcPiece fd.k (fd.P'.image fd.e))
        (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e)
          (faceLen fd.P' fd.e ℓ) w σ))
        (Klein.tripDst (Klein.srcMap fd.inst.cycle) fd.k (Klein.srcG fd.inst.cycle) 0)
        ((Klein.srcMap fd.inst.cycle).tail d)) :
    ∃ c' t, Exec P W encResProg c c' t ∧ t ≤ 47 * Fintype.card (Klein.SrcD fd.DQ fd.k) + 58 ∧
      (∀ d, c'.nmem (ISb + σ d) = (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k
        (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w σ d).toNat) ∧
      (∀ a < 3 * Fintype.card (Klein.SrcD fd.DQ fd.k) + 3, c'.nmem (Ob + a) =
        Klein.resW (2 * c'.nreg 2125 + 1)
          (Klein.kConst (Klein.SrcV fd.VQ fd.k) (Klein.srcMap fd.inst.cycle) fd.k
            (Klein.srcG fd.inst.cycle) (Klein.srcPiece fd.k (fd.P'.image fd.e))
            (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e)
              (faceLen fd.P' fd.e ℓ) w σ) σ a : ℝ)) ∧
      c'.nreg 2125 = kcnHc (Fintype.card (Klein.SrcV fd.VQ fd.k))
        (Fintype.card (Klein.SrcF fd.FQ fd.k))
        (Klein.tripW (Klein.srcPiece fd.k (fd.P'.image fd.e))
          (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e)
            (faceLen fd.P' fd.e ℓ) w σ)).toNat fd.k ∧
      c'.nreg 2126 = 2 * c'.nreg 2125 + 1 ∧
      fdHI fd ℓ σ w ≤ (c'.nreg 2125 : ℝ) ∧
      (∀ a, (a < ISb ∨ ISb + Fintype.card (Klein.SrcD fd.DQ fd.k) ≤ a) →
        (a < Ob ∨ Ob + 3 * Fintype.card (Klein.SrcD fd.DQ fd.k) + 3 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r < 2110 ∨ (2140 ≤ r ∧ r < 2210) ∨ 2218 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  have hk := fd.inst.cycle.two_le
  have hV1 : 1 ≤ Fintype.card (Klein.SrcV fd.VQ fd.k) := by
    have : 0 < Fintype.card (Klein.SrcV fd.VQ fd.k) :=
      Fintype.card_pos_iff.2 ⟨.inr (⟨0, by omega⟩, false)⟩
    omega
  have hnnQ : ∀ y, 0 ≤ faceLen fd.P' fd.e ℓ y := fun y => faceLen_nonneg _ _ _ y
  have hSLn := srcLen_nonneg (k := fd.k) (S := fd.P'.image fd.e) hnnQ
  -- 1. the isolating lengths
  have hwd : ∀ j < Fintype.card (Klein.SrcD fd.DQ fd.k),
      isoWord (Fintype.card (Klein.SrcV fd.VQ fd.k)) (Fintype.card (Klein.SrcD fd.DQ fd.k))
        (Fintype.card (Klein.SrcF fd.FQ fd.k)) (fun j => c.nmem (SLb + j))
        (fun j => c.nmem (WWb + j)) j ≤ W := by
    intro j hj
    have e := isoWord_isoLen (n := Fintype.card (Klein.SrcV fd.VQ fd.k))
      (m := Fintype.card (Klein.SrcD fd.DQ fd.k)) σ (SL := fun j => c.nmem (SLb + j))
      (WW := fun j => c.nmem (WWb + j)) hSLn hwB hSL hWW (σ.symm ⟨j, hj⟩)
    simp only [Equiv.apply_symm_apply] at e
    rw [e]
    exact hIW _
  obtain ⟨c₁, t₁, e₁, ht₁, hI₁, hm₁, hn₁, hr₁, hrm₁, ho₁⟩ :=
    isoProg_exec (P := P) hIL hV1 hN1 hwd c hc g00 g01 g02 g03 g04 g05 g06 (fun _ _ => rfl)
      (fun _ _ => rfl)
  have hIso : ∀ d, c₁.nmem (ISb + σ d) = (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k
      (fd.P'.image fd.e) (faceLen fd.P' fd.e ℓ) w σ d).toNat := fun d =>
    (hI₁ _ (σ d).2).trans (isoWord_isoLen σ hSLn hwB hSL hWW d)
  -- 2. the residues of the constants
  have hfl₁ : ∀ d, 0 < c₁.nmem (Sb + σ d) ↔ d ∈ Klein.srcPiece fd.k (fd.P'.image fd.e) :=
    fun d => by rw [hm₁ _ (by have := (σ d).2; omega)]; exact hfl d
  have hrb₁ : ∀ d ∈ Klein.srcPiece fd.k (fd.P'.image fd.e), 0 < c₁.nmem (Rb + σ d) ↔
      MSSP.Reach (MSSP.pieceGraph (Klein.srcMap fd.inst.cycle)
        (Klein.srcPiece fd.k (fd.P'.image fd.e))
        (Klein.srcIso (V := fd.VQ) (F := fd.FQ) fd.k (fd.P'.image fd.e)
          (faceLen fd.P' fd.e ℓ) w σ))
        (Klein.tripDst (Klein.srcMap fd.inst.cycle) fd.k (Klein.srcG fd.inst.cycle) 0)
        ((Klein.srcMap fd.inst.cycle).tail d) :=
    fun d hd => by rw [hm₁ _ (by have := (σ d).2; omega)]; exact hrb d hd
  obtain ⟨c₂, t₂, e₂, ht₂, hres, h25, h26, hHI, hm₂, hn₂, hr₂, hrm₂, ho₂⟩ :=
    kcnProg_kslot (P := P) (W := W) (Wd := W) (M := Klein.srcMap fd.inst.cycle)
      (g := Klein.srcG fd.inst.cycle)
      (fun d _ => srcIso_nonneg hnnQ hwB σ d) σ hKL le_rfl hH c₁ e₁.wb_right
      ((hn₁ _ (by omega)).trans h00) ((hn₁ _ (by omega)).trans h01)
      ((hn₁ _ (by omega)).trans h02) ((hn₁ _ (by omega)).trans h03)
      ((hn₁ _ (by omega)).trans h04) ((hn₁ _ (by omega)).trans h05)
      ((hn₁ _ (by omega)).trans h06) ((hn₁ _ (by omega)).trans h07) hfl₁ hrb₁
      (fun d _ => hIso d)
  have hOb := hKL.dL
  refine ⟨c₂, t₁ + t₂, Exec.seq e₁ e₂, by omega, fun d => ?_, ?_, h25, by rw [h26, h25], ?_,
    fun a ha ha' => ?_, fun r hr => ?_, by rw [hr₂, hr₁], by rw [hrm₂, hrm₁],
    by rw [ho₂, ho₁]⟩
  · rw [hm₂ _ (by have := (σ d).2; omega)]; exact hIso d
  · rw [h25]; exact hres
  · rw [h25]; exact hHI
  · rw [hm₂ a ha', hm₁ a ha]
  · rw [hn₂ r (by omega), hn₁ r (by omega)]

end NegSSSP

end PlanarFlow
