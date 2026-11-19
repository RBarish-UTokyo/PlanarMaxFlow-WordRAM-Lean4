module

public import PlanarFlow.NegSSSP.Enc.ParT

/-!
# Memory facts of the composed encoder

* `ClampAg m m' Bd x`: the word at `x` kept, or clamped to `Bd` (`min`); `ClampAg.eq`: a word
  `≤ Bd` survives.
* `SrcArrM`: the words written by `srcArrProg` (the hypotheses `hw`, `hbx` of `srcArr_kinput`).
  `SrcArrM.of`: they survive any change that keeps (or clamps to `Bd ≥ 2 ae`) the words of
  `[β, β + 8 N + 2 ae + k)`, of `[β + 9 N + 14 ae + k + 4, + k)` and keeps `[SLb, SLb + N)`.
* `SrcArrM.arrays`: the arrays by the numbers `srcNum σ₀ d` of the darts of the map with the
  sources copied: `RV`, `NF`, `NT`, `NH`, `IS`, the lengths `SL`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein

/-- The word at `x` is kept or clamped to `Bd`. -/
def ClampAg (m m' : ℕ → ℕ) (Bd x : ℕ) : Prop := m' x = m x ∨ m' x = min (m x) Bd

lemma ClampAg.eq {m m' : ℕ → ℕ} {Bd x v : ℕ} (h : ClampAg m m' Bd x) (hx : m x = v)
    (hv : v ≤ Bd) : m' x = v := by
  rcases h with h | h <;> rw [h, hx]; exact min_eq_left hv

lemma ClampAg.of_eq {m m' : ℕ → ℕ} {Bd x : ℕ} (h : m' x = m x) : ClampAg m m' Bd x := Or.inl h

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

variable (M k g S ℓ σ₀ νv₀ τ₀) in
/-- **The words written by `srcArrProg`** (the hypotheses of `srcArr_kinput`). -/
def SrcArrM (β SLb N a ae : ℕ) (m : ℕ → ℕ) : Prop :=
  (∀ d : SrcD D k, DWT β N ae a SLb m (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d) ∧
      m (β + N + (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).x) =
        (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).fc) ∧
    (∀ i < k, m (β + 8 * N + 2 * ae + i) = Fintype.card D + 8 * i ∧
      m (β + 9 * N + 14 * ae + k + 4 + i) = νv₀ (M.tail (g i)))

lemma semT_bounds {N a ae : ℕ} (hN : N = Fintype.card D + 8 * k) (ha : a = Fintype.card V + 2 * k)
    (hae : ae = a + N + (Fintype.card F + 2 * k)) (d : SrcD D k) :
    (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).x < N ∧ (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).rv < N ∧
      (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).tl < a ∧
      (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).hd < a ∧
      (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).fc < ae ∧
      (semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d).is ≤ 1 := by
  have cV : Fintype.card (SrcV V k) = a := by rw [card_srcV, ha]
  have cD : Fintype.card (SrcD D k) = N := by rw [card_srcD, hN]; ring
  have cF : Fintype.card (SrcF F k) = Fintype.card F + 2 * k := card_srcF
  have h1 := (srcNum σ₀ d).2
  have h2 := (srcNum σ₀ (srcRev M k d)).2
  have h3 := (srcVNum (k := k) νv₀ (srcTail M k g d)).2
  have h4 := (srcVNum (k := k) νv₀ (srcTail M k g (srcRev M k d))).2
  have h5 := (srcFNum (k := k) τ₀ (srcFace M k g d)).2
  simp only [semT]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by split_ifs <;> omega⟩

/-- **The words of `srcArrProg` survive** a change keeping (or clamping to `Bd ≥ 2 ae`) the
slot words written by it and keeping the lengths. -/
theorem SrcArrM.of {β SLb N a ae Bd : ℕ} {m m' : ℕ → ℕ}
    (hN : N = Fintype.card D + 8 * k) (ha : a = Fintype.card V + 2 * k)
    (hae : ae = a + N + (Fintype.card F + 2 * k)) (hBd : 2 * ae ≤ Bd)
    (h : SrcArrM M k g S ℓ σ₀ νv₀ τ₀ β SLb N a ae m)
    (h1 : ∀ j < 8 * N + 2 * ae + k, ClampAg m m' Bd (β + j))
    (h2 : ∀ i < k, ClampAg m m' Bd (β + 9 * N + 14 * ae + k + 4 + i))
    (h3 : ∀ j < N, m' (SLb + j) = m (SLb + j)) :
    SrcArrM M k g S ℓ σ₀ νv₀ τ₀ β SLb N a ae m' := by
  obtain ⟨hw, hbx⟩ := h
  refine ⟨fun d => ?_, fun i hi => ?_⟩
  · obtain ⟨⟨wrv, wne, wng, wnt, wnh, wis, wln, wed, wsl⟩, wnf⟩ := hw d
    obtain ⟨bx, brv, btl, bhd, bfc, bis⟩ := semT_bounds (M := M) (g := g) (S := S) (ℓ := ℓ)
      (σ₀ := σ₀) (νv₀ := νv₀) (τ₀ := τ₀) hN ha hae d
    set w := semT M k g S ℓ σ₀ νv₀ τ₀ (a + N) d
    have hmin : min w.x w.rv < N := by omega
    refine ⟨⟨(h1 _ (by omega)).eq wrv (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · have := h1 (2 * N + w.x) (by omega)
      rw [← Nat.add_assoc] at this
      exact this.eq wne (by omega)
    · have := h1 (3 * N + w.x) (by omega)
      rw [← Nat.add_assoc] at this
      exact this.eq wng (by omega)
    · have := h1 (4 * N + w.x) (by omega)
      rw [← Nat.add_assoc] at this
      exact this.eq wnt (by omega)
    · have := h1 (5 * N + w.x) (by omega)
      rw [← Nat.add_assoc] at this
      exact this.eq wnh (by omega)
    · have := h1 (6 * N + w.x) (by omega)
      rw [← Nat.add_assoc] at this
      exact this.eq wis (by omega)
    · have := h1 (7 * N + w.x) (by omega)
      rw [← Nat.add_assoc] at this
      exact this.eq wln (by omega)
    · have := h1 (8 * N + (ae + min w.x w.rv)) (by omega)
      rw [← Nat.add_assoc] at this
      exact this.eq wed (by omega)
    · rw [h3 _ bx]; exact wsl
    · have := h1 (N + w.x) (by omega)
      rw [← Nat.add_assoc] at this
      exact this.eq wnf (by omega)
  · obtain ⟨b1, b2⟩ := hbx i hi
    refine ⟨?_, (h2 i hi).eq b2 (by have := (νv₀ (M.tail (g i))).2; omega)⟩
    have := h1 (8 * N + 2 * ae + i) (by omega)
    rw [← Nat.add_assoc, ← Nat.add_assoc] at this
    exact this.eq b1 (by omega)

/-- **The arrays of the map with the sources copied**, by the numbers `srcNum σ₀ d`. -/
theorem SrcArrM.arrays (hf : MSSP.FaceCycle M k g) {β SLb N a ae : ℕ} {m : ℕ → ℕ}
    (h : SrcArrM M k g S ℓ σ₀ νv₀ τ₀ β SLb N a ae m) (d : SrcD D k) :
    m (β + srcNum σ₀ d) = srcNum σ₀ ((srcMap hf).rev d) ∧
      m (β + N + srcNum σ₀ d) = a + N + srcFNum τ₀ ((srcMap hf).face d) ∧
      m (β + 4 * N + srcNum σ₀ d) = srcVNum νv₀ ((srcMap hf).tail d) ∧
      m (β + 5 * N + srcNum σ₀ d) = srcVNum νv₀ ((srcMap hf).head d) ∧
      m (β + 6 * N + srcNum σ₀ d) = (if d ∈ srcPiece k S then 1 else 0) ∧
      m (SLb + srcNum σ₀ d) = (srcLen ℓ (srcW S ℓ) d).toNat := by
  obtain ⟨⟨wrv, -, -, wnt, wnh, wis, -, -, wsl⟩, wnf⟩ := h.1 d
  refine ⟨wrv, wnf, wnt, wnh, ?_, wsl⟩
  exact wis.trans (by simp [semT, mem_srcPiece])

end NegSSSP

end PlanarFlow
