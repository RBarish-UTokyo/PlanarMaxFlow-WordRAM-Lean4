module

public import PlanarFlow.NegSSSP.DriverRun

/-!
# The driver on the decomposition of any split meeting `SplitF`

`drive_negDecM_mach` (`DriverRun.lean`) runs the recursion on `negDecM N ord cut`, the
decomposition by `splitM N ord cut` for **one fixed** cut function `cut` meeting `CutsOK`. The
split program of the machine computes, at each piece, a cut `A₀` of its large component meeting
`CutOK` (`splitProg_splitM`), but nothing makes these cuts the values of one function of the
component alone (the same component could be cut differently from two pieces). The cost bound of
the recursion, however, holds for **any** decomposition by simple cycles (`fdecCost_le`), and
`decM split` is one as soon as every split of a piece of kept darts with more than `10⁶` darts
meets `SplitF` (`decM_fDec`). So the driver may run on `decM split` for the split computed by the
machine itself, `split P` being the split of the machine at the frame of `P`, provided the frame
of `P` is a function of `P` (`Frame.InP.content`) and the split program is deterministic
(`Frame.exec_agree`); at each piece, `SplitF` follows from `splitM_splitF` with the order and
the cut of that piece alone.

* **`drive_split_mach`**: the whole recursion for negative lengths on the dual map as one run of
  the driver on `decM split (#D) (reps M.dual)`, for any `split` meeting `SplitF` on the pieces of
  kept darts with more than `10⁶` darts, within
  `(A + B + 80) · (cMach C C₀).negsssp (#D) + B + 22` steps (the bound of `drive_negDecM_mach`).
* `splitF_of_local`: `SplitF` of a split equal to `splitM N ord cut P` for an order listing the
  darts of `P` and a cut of the large component meeting `CutOK` (the other cuts by `cutC`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

namespace Driver

open Finset WordRAM WordRAM.Machine BKMNW

universe w

variable {I : Input} {W Hb : ℕ} {testS leafS splitS nodeS : Stmt} {G : Config → Prop}

/-- **The whole recursion for negative lengths on the dual map, on the decomposition of any split
meeting `SplitF`**, within `(A + B + 80) · (cMach C C₀).negsssp n + B + 22` steps, `n` the darts,
when the subprograms cost at most `A · (cNegMach C).leaf m + B` at a leaf and
`A · (cNegMach C).node … + B` at a node. -/
theorem drive_split_mach (C C₀ : ℕ) {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] [Fintype F] [DecidableEq F] {M : CombMap D V F}
    {split : Finset D → Finset D × Finset D}
    (hsplit : ∀ P ⊆ reps M.dual, 1000000 < P.card →
      SplitF M.dual P (split P).1 (split P).2) {ℓ₀ : D → ℤ}
    (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d)
    {InP : ℕ → Finset D → ℕ → ℕ → Config → Prop}
    {Res : Finset D → Option (F → ℤ) → ℕ → ℕ → Config → Prop}
    {tcP lcP scP : Finset D → ℕ} {ncP : Finset D → Finset D → ℕ}
    (hS : NSpec M.dual (minLen M.dual ℓ₀) split I W Hb testS leafS splitS nodeS G InP Res
      tcP lcP scP ncP) (hHb : 0 < Hb) {A B : ℕ}
    (hl : ∀ P : Finset D, P.card ≤ 1000000 → tcP P + lcP P ≤ A * (cNegMach C).leaf P.card + B)
    (hn : ∀ P₀ P₁ : Finset D, SplitF M.dual (P₀ ∪ P₁) P₀ P₁ →
      tcP (P₀ ∪ P₁) + scP (P₀ ∪ P₁) + ncP P₀ P₁ ≤ A * (cNegMach C).node (P₀ ∪ P₁).card
        (bdry M.dual P₀ P₁).card P₀.card (verts M.dual P₀).card P₁.card
        (verts M.dual P₁).card + B)
    {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : G c) (r0 : c.nreg 3000 = 0)
    (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h)
    (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e)
    (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hin : InP (Fintype.card D) (reps M.dual) (Hb + 5) e c) :
    ∃ c' t o, Exec I W (driver testS leafS splitS nodeS) c c' t ∧
      t ≤ (A + B + 80) * (cMach C C₀).negsssp (Fintype.card D) + B + 22 ∧
      PotOut (M.dual.graph ℓ₀) o ∧ Res (reps M.dual) o (Hb + 5) e c' ∧ G c' ∧
      c'.output = c.output := by
  obtain ⟨c', t, o, ex, ht, hp, hr, g, -, -, ho⟩ :=
    drive_dec hS hHb (Fintype.card D) (reps M.dual) c hc hg r0 r1 r2 r3 m0 m1 m2 he hh hin
  have hf : (decM split (Fintype.card D) (reps M.dual)).FDec M.dual :=
    decM_fDec hsplit _ _ (card_le_univ _) subset_rfl
  have hcost := dcost_le_negCost' (N := M.dual) (tcP := tcP) (lcP := lcP) (scP := scP)
    (ncP := ncP) hl hn (fun m hm => by show 1 ≤ 96 * m ^ 2; nlinarith)
    (fun m hm => by show 1 ≤ 1000 * m; omega) _ hf
  have hfd := fdecCost_le (cNegMach_bounds C) (piece_decM split _ _) hf
  have hk : (A + B + 80) * negCost M.dual (cNegMach C) (decM split (Fintype.card D)
      (reps M.dual)) ≤ (A + B + 80) * (cMach C C₀).negsssp (Fintype.card D) :=
    Nat.mul_le_mul_left _ (by show _ ≤ 10920 * negK C * _ * lg _ ^ 2 + 1000001 * negK C * _
                              omega)
  exact ⟨c', t, o, ex, by omega, potOut_graph_of_reps hneg hp, hr, g, ho⟩

end Driver

/-! ### `SplitF` at one piece -/

section Local

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- **`SplitF` from the order and the cut of one piece**: `splitM N ord cut P` for an order
listing the darts of `P` (at `P` only) and the cut function `cutC` changed at one component `K`
to a cut `A₀` meeting `CutOK` meets `SplitF`. -/
theorem splitF_local (hM : N.IsPlane) (hrot : N.RotTrans) (hface : N.FaceTrans)
    {P : Finset D} (hPr : P ⊆ reps N) (hs : 1000000 < P.card) {ord : Finset D → List D}
    (hL : ∀ d ∈ P, d ∈ ord P) {K A₀ : Finset D} (hA : CutOK N K A₀) :
    SplitF N P (splitM N ord (Function.update (cutC N) K A₀) P).1
      (splitM N ord (Function.update (cutC N) K A₀) P).2 := by
  classical
  set ord' : Finset D → List D := fun Q => if Q = P then ord P else Finset.univ.toList
  have hO : OrdOK ord' := fun Q d hd => by
    by_cases hQ : Q = P
    · subst hQ; simp only [ord', ite_true]; exact hL d hd
    · simp only [ord', hQ, ite_false]; exact Finset.mem_toList.2 (Finset.mem_univ d)
  have hC : CutsOK N (Function.update (cutC N) K A₀) := fun K' hK' h0 hc => by
    by_cases hK : K' = K
    · subst hK; rw [Function.update_self]; exact hA
    · rw [Function.update_of_ne hK]; exact cutsOK_cutC hM hrot hface K' hK' h0 hc
  have e : splitM N ord (Function.update (cutC N) K A₀) P =
      splitM N ord' (Function.update (cutC N) K A₀) P := by
    unfold splitM; simp only [ord', ite_true]
  rw [e]
  exact splitM_splitF hO hC hPr hs

end Local

end NegSSSP

end PlanarFlow
