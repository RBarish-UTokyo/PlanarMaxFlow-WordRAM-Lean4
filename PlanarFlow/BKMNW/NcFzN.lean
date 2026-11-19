module

public import PlanarFlow.BKMNW.NcFzM

/-!
# `FzHypF` for `fzP` from a frozen-fix program meeting `FixFrameSpec`

**`fzHypF_of_frame`**: `FixFrameSpec fixC msP Scr Rm wzm C C₀ fxT fxR wzf` and the cost
hypothesis

  `∀ m xf k L, 1 ≤ m → m ≤ L → pfT m + 3 + fxT m xf k + (24 m + 40) ≤ (cMachS C C₀).fixRun m xf k (3L)`

give `Pp.FzHypF (fzP fixC) msP Scr Rm wzm C C₀ (fzWz wzf) (fzRN fxR)` (zero area
`fzWz wzf m Z = Σ_{m' ≤ 3m} wzf m' (m Z)`, room `fzRN fxR N Z = Σ_{m ≤ N} fzRc fxR Z m`).

**`fzCost_le`**: the cost hypothesis holds as soon as `fxT` fits in `fixRun` with only `2L` of the
linear bookkeeping (`1 ≤ C`): `pfP` and the copy-back (`269 m + 343` steps) are paid by the
remaining `lin L = 10¹⁵ C L`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver MfDrv
  PlanarSeparator.StDart NcStep

/-- The room function of `fzP` for `FzHypF`. -/
def fzRN (fxR : ℕ → ℕ → ℕ) (N Z : ℕ) : ℕ := ∑ m ∈ range (N + 1), fzRc fxR Z m

lemma card_le_psize {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] (M : CombMap D V F) (σ : Perm D) (B : Finset D) :
    B.card ≤ psize M σ B := by
  unfold psize; omega

/-- **The cost hypothesis from a bound with `2L` bookkeeping.** -/
theorem fzCost_le {C C₀ : ℕ} (hC : 1 ≤ C) {fxT : ℕ → ℕ → ℕ → ℕ}
    (h : ∀ m xf k L, 1 ≤ m → m ≤ L → fxT m xf k ≤ (cMachS C C₀).mssp m k +
      k * ((cMachS C C₀).fr xf (2 * k) + (cMachS C C₀).lin xf) + (cMachS C C₀).negsssp m +
      (cMachS C C₀).lin (2 * L)) :
    ∀ m xf k L, 1 ≤ m → m ≤ L →
      pfT m + 3 + fxT m xf k + (24 * m + 40) ≤ (cMachS C C₀).fixRun m xf k (3 * L) := by
  intro m xf k L hm hL
  have h1 := h m xf k L hm hL
  unfold SubCosts.fixRun pfT
  have e1 : (cMachS C C₀).lin (3 * L) = (cMachS C C₀).lin (2 * L) + csK * (C * L) := by
    show csK * (C * (3 * L)) = csK * (C * (2 * L)) + csK * (C * L); ring
  have e2 : 269 * m + 343 ≤ csK * (C * L) := by
    have : L ≤ C * L := Nat.le_mul_of_pos_left L hC
    have : 1000 * L ≤ csK * (C * L) := Nat.mul_le_mul (by unfold csK; norm_num) this
    omega
  omega

/-- **`FzHypF` for `fzP`** (see the module docstring). -/
theorem fzHypF_of_frame {fixC msP : Stmt} {Scr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ}
    {wzm : ℕ → ℕ → ℕ} {C C₀ : ℕ} {fxT : ℕ → ℕ → ℕ → ℕ} {fxR wzf : ℕ → ℕ → ℕ}
    (hFF : FixFrameSpec fixC msP Scr Rm wzm C C₀ fxT fxR wzf)
    (hT : ∀ m xf k L, 1 ≤ m → m ≤ L →
      pfT m + 3 + fxT m xf k + (24 * m + 40) ≤ (cMachS C C₀).fixRun m xf k (3 * L)) :
    Pp.FzHypF (fzP fixC) msP Scr Rm wzm C C₀ (fzWz wzf) (fzRN fxR) := by
  intro hMS D V F _ _ _ _ _ _ M hM hrot hft ep hep u hu S T hST hne N en d₀ gid ν hN hsurj hgid
    hν hQ hTS L pc sc gS gH τ u' S' T' Reach c I W Z Wz hW1 hW2 hW3
  refine ⟨fzTc fxT, fzRc fxR Z, fzP_spec hFF hMS L gid u' S' T' Z I W,
    fun m hm => sum_ge (f := fun m => fzRc fxR Z m) (by omega), ?_⟩
  intro l r π Hs σ h j πj hR hπj
  have hπj' : (segsP h.1 π.segs h.2)[j]? = some πj := hπj
  unfold fzTc
  simp only [partFK_node h hπj']
  have hpos : 0 < (pdarts L (l.piece ∪ r.piece) Hs).card := by
    obtain ⟨y, -⟩ := Quotient.exists_rep (πj.p 0)
    exact Finset.card_pos.2 ⟨y.1, y.2⟩
  exact hT _ _ _ _ hpos (card_le_psize L σ _)

/-- **`C2SHypF` for `c2sP (fzP fixC) pbP`** from a frozen-fix program meeting `FixFrameSpec`. -/
theorem c2sHypF_of_frame {fixC msP : Stmt} {Scr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ}
    {wzm : ℕ → ℕ → ℕ} {C C₀ : ℕ} {fxT : ℕ → ℕ → ℕ → ℕ} {fxR wzf : ℕ → ℕ → ℕ}
    (hFF : FixFrameSpec fixC msP Scr Rm wzm C C₀ fxT fxR wzf)
    (hT : ∀ m xf k L, 1 ≤ m → m ≤ L →
      pfT m + 3 + fxT m xf k + (24 * m + 40) ≤ (cMachS C C₀).fixRun m xf k (3 * L))
    (hC : 1 ≤ C) :
    Pp.C2SHypF (c2sP (fzP fixC) pbP) msP Scr Rm wzm C C₀
      (fun m Z => wzc m Z + fzWz wzf m Z) (Pp.c2sRC (fzRN fxR)) :=
  Pp.c2sHypF_of_fz (fzHypF_of_frame hFF hT) hC

/-- **`S2CHypF` for `s2cP (fzP fixC) pbP`** from a frozen-fix program meeting `FixFrameSpec`. -/
theorem s2cHypF_of_frame {fixC msP : Stmt} {Scr : ℕ → Prop} {Rm : ℕ → ℕ → ℕ → ℕ}
    {wzm : ℕ → ℕ → ℕ} {C C₀ : ℕ} {fxT : ℕ → ℕ → ℕ → ℕ} {fxR wzf : ℕ → ℕ → ℕ}
    (hFF : FixFrameSpec fixC msP Scr Rm wzm C C₀ fxT fxR wzf)
    (hT : ∀ m xf k L, 1 ≤ m → m ≤ L →
      pfT m + 3 + fxT m xf k + (24 * m + 40) ≤ (cMachS C C₀).fixRun m xf k (3 * L))
    (hC : 1 ≤ C) :
    Pp.S2CHypF (s2cP (fzP fixC) pbP) msP Scr Rm wzm C C₀
      (fun m Z => wzc m Z + fzWz wzf m Z) (Pp.c2sRC (fzRN fxR)) :=
  Pp.s2cHypF_of_fz (fzHypF_of_frame hFF hT) hC

end NcFz

end BKMNW

end PlanarFlow
