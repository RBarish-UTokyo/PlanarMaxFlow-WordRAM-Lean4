module

public import PlanarFlow.BKMNW.NcTopS
public import PlanarFlow.BKMNW.NcCost

/-!
# The step bounds of `c2sP` and `s2cP` against `(cMachS C C₀).c2sRun`

* `pcoreB_le_mlg` (`pcoreB V F m (4m+1) ≤ 2.3·10⁸ m lg m` when the map has at most `m` vertices
  and at most `m` faces — no Euler formula needed), `stCostZ_le_mlg`
  (`stCostZ m (4 pcoreB … + 3) ≤ 2.5·10¹⁰ m lg m`), `hdCost_le` (`hdCost m ≤ 1000 m lg m`);
* **`c2sT_le`**, **`s2cT_le`**: at a node call (its piece has `m ≥ 1` darts), if the parameter
  programs run within `fzT x j ≤ (cMachS C C₀).fixRun m x k (3 N)` and
  `pbT x j ≤ (cMachS C C₀).pushRun m nf N`, then the steps of `c2sP`/`s2cP` are at most
  **`(cMachS C C₀).c2sRun m nf N x k`** (the head, the s-t flow call and the linear passes fit in
  the `stflow m = 10¹⁵ · 504000000 · m lg m` term).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep StCall STFlow NegSSSP

universe w

/-- **`pcoreB` is `O(m lg m)`** when the map has at most `m` vertices and faces. -/
lemma pcoreB_le_mlg (V' F' : Type*) [Fintype V'] [Fintype F'] {m : ℕ} (hm : 1 ≤ m)
    (hV : Fintype.card V' ≤ m) (hF : Fintype.card F' ≤ m) :
    pcoreB V' F' m (4 * m + 1) ≤ 230000000 * (m * lg m) := by
  have hl1 := one_le_lg m
  have e3 : m ≤ m * lg m := Nat.le_mul_of_pos_right m (by omega)
  have hops : STFlow.pstOps (Fintype.card V') (Fintype.card F') m ≤ 176 * m := by
    unfold STFlow.pstOps; omega
  have hext : STFlow.pstExt (Fintype.card V') (Fintype.card F') m ≤ 500 * m := by
    unfold STFlow.pstExt; omega
  have hlog := log_four_le hm
  have hcost : DynTree.opCostE (4 * m + 1) ≤ 1300000 * lg m := by
    unfold DynTree.opCostE; omega
  have hprod : STFlow.pstOps (Fintype.card V') (Fintype.card F') m * DynTree.opCostE (4 * m + 1) ≤
      176 * m * (1300000 * lg m) := Nat.mul_le_mul hops hcost
  have e4 : 176 * m * (1300000 * lg m) = 228800000 * (m * lg m) := by ring
  unfold pcoreB
  omega

/-- **The s-t flow call is `O(m lg m)`** when the map has at most `m` vertices and faces. -/
lemma stCostZ_le_mlg (V' F' : Type*) [Fintype V'] [Fintype F'] {m : ℕ} (hm : 1 ≤ m)
    (hV : Fintype.card V' ≤ m) (hF : Fintype.card F' ≤ m) :
    stCostZ m (4 * pcoreB V' F' m (4 * m + 1) + 3) ≤ 25000000000 * (m * lg m) := by
  have h1 := stCostZ_le hm (4 * pcoreB V' F' m (4 * m + 1) + 3)
  have h2 := pcoreB_le_mlg V' F' hm hV hF
  have e3 : m ≤ m * lg m := Nat.le_mul_of_pos_right m (one_le_lg m)
  omega

/-- **The head is `O(m lg m)`.** -/
lemma hdCost_le {m : ℕ} (hm : 1 ≤ m) : hdCost m ≤ 1000 * (m * lg m) := by
  have hl1 := one_le_lg m
  have e3 : m ≤ m * lg m := Nat.le_mul_of_pos_right m (by omega)
  have e4 : lg m ≤ m * lg m := Nat.le_mul_of_pos_left _ (by omega)
  have e5 : (30 * m + 10) * lg m = 30 * (m * lg m) + 10 * lg m := by ring
  unfold hdCost hfCost rbCost
  omega

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- The vertices and faces of a piece map are at most its darts. -/
lemma piece_cards_le {P : Finset D} {Hs : List (Finset V)} {σ : Perm D} :
    Fintype.card (SVert σ (pdarts M P Hs)) ≤ (pdarts M P Hs).card ∧
      Fintype.card (SFace σ (pdarts M P Hs) (revPerm M)) ≤ (pdarts M P Hs).card := by
  constructor
  · have := Fintype.card_le_of_surjective _ (Quotient.mk_surjective (s := orbSetoid σ (pdarts M P Hs)))
    rwa [Fintype.card_coe] at this
  · have := Fintype.card_le_of_surjective _
      (Quotient.mk_surjective (s := orbSetoid (σ * revPerm M) (pdarts M P Hs)))
    rwa [Fintype.card_coe] at this

/-- **The steps of `c2sP` are within `(cMachS C C₀).c2sRun`** at a call with a dart, given the
budgets of the parameter programs. -/
theorem c2sT_le (C C₀ : ℕ) {fzT pbT : MCall M → ℕ → ℕ} (x : MCall M) (j i : ℕ)
    (hm : 1 ≤ (pdarts M x.1.piece x.2.1).card) {nf N xf k : ℕ}
    (hfz : fzT x j ≤ (cMachS C C₀).fixRun (pdarts M x.1.piece x.2.1).card xf k (3 * N))
    (hpb : pbT x j ≤ (cMachS C C₀).pushRun (pdarts M x.1.piece x.2.1).card nf N) :
    c2sT fzT pbT x j i ≤ (cMachS C C₀).c2sRun (pdarts M x.1.piece x.2.1).card nf N xf k := by
  obtain ⟨hV, hF⟩ := piece_cards_le (M := M) (P := x.1.piece) (Hs := x.2.1) (σ := x.2.2)
  generalize hmd : (pdarts M x.1.piece x.2.1).card = m at hm hfz hpb hV hF ⊢
  have h1 := stCostZ_le_mlg _ _ hm hV hF
  have h2 := hdCost_le hm
  have e3 : m ≤ m * lg m := Nat.le_mul_of_pos_right m (one_le_lg m)
  unfold c2sT tailT
  rw [hmd]
  show _ ≤ csK * (504000000 * (m * lg m)) + _ + _ + 2 * (cMachS C C₀).lin N
  unfold csK
  omega

/-- **The steps of `s2cP` are within `(cMachS C C₀).c2sRun`** under the same hypotheses. -/
theorem s2cT_le (C C₀ : ℕ) {fzT pbT : MCall M → ℕ → ℕ} (x : MCall M) (j i : ℕ)
    (hm : 1 ≤ (pdarts M x.1.piece x.2.1).card) {nf N xf k : ℕ}
    (hfz : fzT x j ≤ (cMachS C C₀).fixRun (pdarts M x.1.piece x.2.1).card xf k (3 * N))
    (hpb : pbT x j ≤ (cMachS C C₀).pushRun (pdarts M x.1.piece x.2.1).card nf N) :
    s2cT fzT pbT x j i ≤ (cMachS C C₀).c2sRun (pdarts M x.1.piece x.2.1).card nf N xf k := by
  obtain ⟨hV, hF⟩ := piece_cards_le (M := M) (P := x.1.piece) (Hs := x.2.1) (σ := x.2.2)
  generalize hmd : (pdarts M x.1.piece x.2.1).card = m at hm hfz hpb hV hF ⊢
  have h1 := stCostZ_le_mlg _ _ hm hV hF
  have h2 := hdCost_le hm
  have e3 : m ≤ m * lg m := Nat.le_mul_of_pos_right m (one_le_lg m)
  unfold s2cT c2sT tailT
  rw [hmd]
  show _ ≤ csK * (504000000 * (m * lg m)) + _ + _ + 2 * (cMachS C C₀).lin N
  unfold csK
  omega

end NcStep

end BKMNW

end PlanarFlow
