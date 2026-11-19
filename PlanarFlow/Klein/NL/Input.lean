module

public import PlanarFlow.Klein.ProgInput

/-!
# The input of Klein's program without the lengths

`Klein.KInput` asks, besides the arrays describing the map, that the array `LN` hold the lengths
`(ℓ d).toNat` of the darts of the piece (`KInput.ln`). No program reads `LN` and no proof uses
`KInput.ln`; but the lengths can be large (the isolating lengths are cubic in the size of the
map), and every input word is bounded by the word bound of Klein's run, which is also the size
of its work space. `KInputNL` is `KInput` without `ln` (the parameter `ℓ` is kept, unused, so
that the copies of the proofs in `PlanarFlow/Klein/NL/` read as the originals);
`KInput.toNL` forgets `ln`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace Klein

open WordRAM WordRAM.Machine

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The input describes the map** (`KInput` without the lengths `ln`). -/
structure KInputNL (M : CombMap D V F) (S : Finset D) (ℓ : D → ℤ) {nD : ℕ} (σ : D ≃ Fin nD)
    (ιv : V → ℕ) (ιg : D → ℕ) (ιf : F → ℕ) (ιe : D → ℕ) (P : Input) : Prop where
  rv : ∀ d, P.data.getD (iRV nD + σ d) 0 = σ (M.rev d)
  nf : ∀ d, P.data.getD (iNF nD + σ d) 0 = ιf (M.face d)
  ne : ∀ d, P.data.getD (iNE nD + σ d) 0 = ιe d
  ng : ∀ d, P.data.getD (iNG nD + σ d) 0 = ιg d
  nt : ∀ d, P.data.getD (iNT nD + σ d) 0 = ιv (M.tail d)
  nh : ∀ d, P.data.getD (iNH nD + σ d) 0 = ιv (M.head d)
  is : ∀ d, P.data.getD (iIS nD + σ d) 0 = if d ∈ S then 1 else 0
  ed : ∀ d, P.data.getD (iED nD + ιe d) 0 = σ d ∨ P.data.getD (iED nD + ιe d) 0 = σ (M.rev d)

/-- Forget the lengths (for any `ℓ'`: the parameter is unused). -/
theorem KInput.toNL {M : CombMap D V F} {S : Finset D} {ℓ ℓ' : D → ℤ} {nD : ℕ}
    {σ : D ≃ Fin nD} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} {P : Input}
    (h : KInput M S ℓ σ ιv ιg ιf ιe P) : KInputNL M S ℓ' σ ιv ιg ιf ιe P :=
  ⟨h.rv, h.nf, h.ne, h.ng, h.nt, h.nh, h.is, h.ed⟩

end Klein

end PlanarFlow
