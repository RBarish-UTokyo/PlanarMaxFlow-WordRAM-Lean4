module

public import PlanarFlow.BKMNW.StDkRun

/-!
# The initial dual tree of the s-t flow from the parent words in memory

`NegSSSP.stdP_exec` on the dual map `M.dual` (vertices the faces of `M`) leaves, for every face
`x ≠ o`, a parent word `PAR[ιF x] = σ d` of a tight dart `d` into `x`. Here:

* **`stTree_of_par`**: such words define a dual tree `T₀ : DTree M` rooted at `o` whose parent darts
  are the words (`PAR[ιF x] = σ (T₀.par x)`) and whose state meets `LInv c ε s t` for all `s`, `t`
  (`c ≥ 0`, `ε ≥ 1`, `N ≥ (F + 1) Σ ε + 1`, lengths `N c + ε`): the tree of `STFlow.st_sNFM`,
  with parent darts read from memory (the input of the orders `KInit`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **The tree of the parent words.** -/
theorem stTree_of_par (hM : M.IsPlane) {c ε : D → ℤ} (hc : ∀ d, 0 ≤ c d) (hε : ∀ d, 1 ≤ ε d)
    {N : ℤ} (hN : (Fintype.card F + 1) * ∑ d, ε d + 1 ≤ N) (o : F) (d₀ : D) {nD : ℕ}
    (σ : D ≃ Fin nD) {ιF : F → ℕ} {mem : ℕ → ℕ} {Pb : ℕ}
    (hpar : ∀ x, x ≠ o → ∃ d, mem (Pb + ιF x) = σ d ∧ M.face (M.rev d) = x ∧
      MSSP.dist (dG M fun d => N * c d + ε d) o (M.face d) + (N * c d + ε d) =
        MSSP.dist (dG M fun d => N * c d + ε d) o x) :
    ∃ T₀ : DTree M, T₀.root = o ∧ (∀ x, x ≠ o → mem (Pb + ιF x) = σ (T₀.par x)) ∧
      ∀ s t, LInv c ε s t (tSt M c ε T₀) := by
  classical
  let par : F → D := fun x => if h : x = o then d₀ else (hpar x h).choose
  have hspec : ∀ x (h : x ≠ o), mem (Pb + ιF x) = σ (par x) ∧ M.face (M.rev (par x)) = x ∧
      MSSP.dist (dG M fun d => N * c d + ε d) o (M.face (par x)) + (N * c (par x) + ε (par x)) =
        MSSP.dist (dG M fun d => N * c d + ε d) o x := fun x h => by
    simp only [par, h, ↓reduceDIte]
    exact (hpar x h).choose_spec
  have hhp : ∀ x, x ≠ o → M.face (M.rev (par x)) = x := fun x h => (hspec x h).2.1
  obtain ⟨hdec, -⟩ := linv_of_dist hM hc hε hN o par hhp (fun x h => (hspec x h).2.2)
    (M.tail d₀) (M.tail d₀)
  refine ⟨treeOf M o par hhp _ hdec, rfl, fun x h => (hspec x h).1, fun s t => ?_⟩
  obtain ⟨hdec', hI⟩ := linv_of_dist hM hc hε hN o par hhp (fun x h => (hspec x h).2.2) s t
  exact hI

end STFlow

end PlanarFlow
