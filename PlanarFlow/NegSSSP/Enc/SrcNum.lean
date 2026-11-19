module

public import PlanarFlow.NegSSSP.NL.KEncNatNL

/-!
# An explicit numbering of the darts of the map with the sources copied

The encoding of a one-face instance is given for a numbering `σ` of the darts of the map with
the sources copied (`Klein.SrcD D k = D ⊕ (Fin k × SrcKind)`), and the programs writing it need
the number of every dart as a formula. `srcNum σ₀`: the original darts keep their numbers
`σ₀ d < nD`, the dart of kind `κ` added at the vertex `i` of the face gets `nD + (κ + 8 i)`
(`kindIdx`, eight kinds), as an equivalence with `Fin (Fintype.card (SrcD D k))` (the type of
the numberings of `FEncNat`/`FEncNatNL`): `srcNum_inl`, `srcNum_inr`.
-/

@[expose] public section

namespace PlanarFlow

namespace Klein

/-- The index of a kind of added dart. -/
def kindIdx : SrcKind → Fin 8
  | .ring => 0 | .ringR => 1 | .down => 2 | .up => 3 | .out => 4 | .outR => 5 | .side => 6
  | .sideR => 7

/-- The kind of an index. -/
def kindOf : Fin 8 → SrcKind
  | ⟨0, _⟩ => .ring | ⟨1, _⟩ => .ringR | ⟨2, _⟩ => .down | ⟨3, _⟩ => .up | ⟨4, _⟩ => .out
  | ⟨5, _⟩ => .outR | ⟨6, _⟩ => .side | ⟨_ + 7, _⟩ => .sideR

/-- The kinds of added darts, numbered. -/
def kindEquiv : SrcKind ≃ Fin 8 where
  toFun := kindIdx
  invFun := kindOf
  left_inv κ := by cases κ <;> rfl
  right_inv i := by
    rcases i with ⟨i, hi⟩
    interval_cases i <;> rfl

variable {D : Type*} [Fintype D] {k : ℕ}

lemma card_srcD (k : ℕ) : Fintype.card (SrcD D k) = Fintype.card D + k * 8 := by
  simp [Fintype.card_sum, Fintype.card_prod, card_srcKind]

/-- **The explicit numbering of the darts of the map with the sources copied.** -/
def srcNum (σ₀ : D ≃ Fin (Fintype.card D)) : SrcD D k ≃ Fin (Fintype.card (SrcD D k)) :=
  ((Equiv.sumCongr σ₀ ((Equiv.refl (Fin k)).prodCongr kindEquiv)).trans
    ((Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv)).trans
    (finCongr (card_srcD k).symm)

lemma srcNum_inl (σ₀ : D ≃ Fin (Fintype.card D)) (d : D) :
    (srcNum (k := k) σ₀ (.inl d) : ℕ) = σ₀ d := by
  simp [srcNum]

lemma srcNum_inr (σ₀ : D ≃ Fin (Fintype.card D)) (i : Fin k) (κ : SrcKind) :
    (srcNum σ₀ (.inr (i, κ)) : ℕ) = Fintype.card D + ((kindIdx κ : ℕ) + 8 * i) := by
  simp [srcNum, kindEquiv, finProdFinEquiv]

end Klein

end PlanarFlow
