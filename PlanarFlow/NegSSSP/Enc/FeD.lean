module

public import PlanarFlow.NegSSSP.Enc.FeC4

/-!
# The composed encoder, phase D: the depth orders of the initial tree `T`

* `feTo`, **`feTo_exec`**: `toProg` with its registers on the parent array `PA` of a tree
  `T : DTree M'.dual` rooted at the first root: the order `vs` of all the vertices and `ys` of the
  non-root vertices by nondecreasing depth (`Klein.Orders T vs ys`), `IV = τ vs`,
  `IT = σ (T.par ys)` and the two lengths `HD` in the slot (the fields `oT`, `iv`, `it`, `l0`,
  `l1` of `Klein.KInit`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {σ₀ : D ≃ Fin (Fintype.card D)} {νv₀ : V ≃ Fin (Fintype.card V)}
  {τ₀ : F ≃ Fin (Fintype.card F)}

/-- The registers of `toProg` for the tree `T`. -/
def feToRegs (p : FeP) : List (ℕ × ℕ) :=
  [(1600, p.A), (1601, p.nV), (1602, p.PA), (1603, p.β + 4 * p.N), (1604, 0), (1605, p.ZS),
    (1606, p.ZS + p.A), (1607, p.ZS + 2 * p.A), (1608, p.ZS + 3 * p.A + 1),
    (1609, p.ZS + 4 * p.A + 1), (1610, p.ZS + 5 * p.A + 1), (1611, p.ZS + 6 * p.A + 1),
    (1612, p.ZS + 7 * p.A + 1), (1613, p.β + iIV p.N p.NN p.k), (1614, p.β + iIT p.N p.NN p.k),
    (1615, p.β + iHD p.N p.NN p.k)]

/-- **The depth orders of `T`.** -/
def feTo (p : FeP) : Stmt := .seq (feSet (feToRegs p)) toProg

theorem feTo_natOnly (p : FeP) : natOnly (feTo p) = true := by
  have h : natOnly toProg = true := by kernel_rfl
  simp only [feTo, natOnly, feSet_natOnly, h, Bool.and_self]

set_option maxHeartbeats 2000000 in
/-- **The depth orders of the initial tree on the machine.** -/
theorem feTo_exec (hf : MSSP.FaceCycle M k g) (p : FeP) (hD : p.nD = Fintype.card D)
    (hk : p.k = k) (hV : p.nV = Fintype.card V) (hF : p.nF = Fintype.card F) (hW : p.END ≤ W)
    (T : STFlow.DTree (srcMap hf).dual) (hTr : T.root = tripSrc (srcMap hf) k (srcG hf) 0)
    (c : Config) (hc : WordsBounded W c)
    (hPD : ∀ y, y ≠ T.root → c.nmem (p.PA + srcVNum νv₀ y) = srcNum σ₀ (T.par y))
    (hPDr : c.nmem (p.PA + p.nV) < p.N)
    (hNT : ∀ d, c.nmem (p.β + 4 * p.N + srcNum σ₀ d) = srcVNum νv₀ ((srcMap hf).tail d)) :
    ∃ c' t, Exec P W (feTo p) c c' t ∧ t ≤ 16 + toCost p.A ∧
      ∃ ys : List (SrcV V k),
        Orders T ((List.finRange (Fintype.card (SrcV V k))).map (srcVNum νv₀).symm) ys ∧
        (∀ i (h : i < ((List.finRange (Fintype.card (SrcV V k))).map (srcVNum νv₀).symm).length),
          c'.nmem (p.β + iIV p.N p.NN p.k + i) =
            srcVNum νv₀ ((List.finRange (Fintype.card (SrcV V k))).map (srcVNum νv₀).symm)[i]) ∧
        (∀ i (h : i < ys.length), c'.nmem (p.β + iIT p.N p.NN p.k + i) = srcNum σ₀ (T.par ys[i])) ∧
        c'.nmem (p.β + iHD p.N p.NN p.k) = Fintype.card (SrcV V k) ∧
        c'.nmem (p.β + iHD p.N p.NN p.k + 1) = ys.length ∧
        (∀ a, (a < p.ZS ∨ p.ZS + 8 * p.A + 1 ≤ a) →
          (a < p.β + iIV p.N p.NN p.k ∨ p.β + iHD p.N p.NN p.k + 2 ≤ a) → c'.nmem a = c.nmem a) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨cD, cV, -⟩ := fe_cards p hD hk hV hF
  obtain ⟨ru, -, -, -⟩ := fe_roots (σ₀ := σ₀) (νv₀ := νv₀) hf
  have hr : (srcVNum νv₀ T.root : ℕ) = p.nV := by rw [hTr, ru, hV]
  obtain ⟨l1, l2, l3, l4, l5⟩ : p.β + (9 * p.N + 7 * p.NN + p.k + 4) ≤ p.PA ∧
      p.PA + p.A ≤ p.ZS ∧ p.ZS + 8 * p.A + 1 ≤ W ∧ p.nV < p.A ∧ p.A ≤ p.NN := by
    have h2 := hf.two_le
    have hE := p.eqs; have hsl := p.slot_le; clear * - hE hsl hW hk h2; omega
  obtain ⟨c₁, k₁, e₁, hk₁, hn₁, hr₁, hm₁, hrm₁, ho₁⟩ :=
    feSet_exec (P := P) (feToRegs p) (by
      intro q hq; simp only [feToRegs, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> simp only [iIV, iIT, iHD] <;> clear * - l1 l2 l3 l4 l5 <;>
        omega) c hc
  have hm' : ∀ a, c₁.nmem a = c.nmem a := fun a => by rw [hm₁]
  have hL : ToLay (Fintype.card (SrcV V k)) (Fintype.card (SrcD D k)) (srcVNum νv₀ T.root) p.ZS
      p.PA (p.β + 4 * p.N) (p.β + iIV p.N p.NN p.k) (p.β + iIT p.N p.NN p.k)
      (p.β + iHD p.N p.NN p.k) 0 W := by
    rw [hr, cV, cD]
    refine ⟨by omega, l4, by omega, by omega, ?_, ?_, ?_, ?_, by omega, by omega, by omega, ?_,
      by omega⟩
    all_goals (simp only [iIV, iIT, iHD]; clear * - l1 l2 l3 l4 l5; omega)
  have hR : ToRegs (Fintype.card (SrcV V k)) (srcVNum νv₀ T.root) p.ZS p.PA (p.β + 4 * p.N)
      (p.β + iIV p.N p.NN p.k) (p.β + iIT p.N p.NN p.k) (p.β + iHD p.N p.NN p.k) 0 c₁ := by
    rw [hr, cV]
    exact ⟨by rw [hn₁]; simp [feToRegs, feSetV], by rw [hn₁]; simp [feToRegs, feSetV],
      by rw [hn₁]; simp [feToRegs, feSetV], by rw [hn₁]; simp [feToRegs, feSetV],
      by rw [hn₁]; simp [feToRegs, feSetV], by rw [hn₁]; simp [feToRegs, feSetV],
      by rw [hn₁]; simp [feToRegs, feSetV], by rw [hn₁]; simp [feToRegs, feSetV],
      by rw [hn₁]; simp [feToRegs, feSetV], by rw [hn₁]; simp [feToRegs, feSetV],
      by rw [hn₁]; simp [feToRegs, feSetV], by rw [hn₁]; simp [feToRegs, feSetV],
      by rw [hn₁]; simp [feToRegs, feSetV], by rw [hn₁]; simp [feToRegs, feSetV],
      by rw [hn₁]; simp [feToRegs, feSetV], by rw [hn₁]; simp [feToRegs, feSetV]⟩
  obtain ⟨c₂, k₂, e₂, hk₂, ys, hOr, hIV, hIT, hH0, hH1, hm₂, -, hr₂, hrm₂, ho₂⟩ :=
    toProg_orders (P := P) T (srcNum σ₀) (srcVNum νv₀) hL c₁ e₁.wb_right hR
      (fun y hy => by rw [hm']; exact hPD y hy)
      (by rw [hm', hr, cD]; exact hPDr)
      (fun d => by rw [hm', Nat.zero_add]; exact hNT d)
  refine ⟨c₂, k₁ + k₂, Exec.seq e₁ e₂, by simp [feToRegs] at hk₁; rw [cV] at hk₂; omega, ys,
    hOr, fun i h => by rw [hIV i h, Nat.zero_add], hIT, by rw [hH0]; simp, hH1,
    fun a h1 h2 => by rw [cV] at hm₂; rw [hm₂ a h1 h2, hm'], by rw [hr₂, hr₁],
    by rw [hrm₂, hrm₁], by rw [ho₂, ho₁]⟩

end NegSSSP

end PlanarFlow
