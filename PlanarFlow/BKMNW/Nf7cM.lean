module

public import PlanarFlow.BKMNW.Nf7cL

/-!
# After the stage loop: clearing the image and the final step, meaning

* `neg_some`: the final negative-length call of `fixPath` has an outcome (`EffInvB.final` gives
  a feasible potential, so no negative closed walk);
* `img_zero`: the resident image (`SLx.Img`) is zero outside its two blocks;
* **`fixFin_exec`**: from the state the stage loop leaves (`SLx.Stt (X.st k)`, `SLx.Img`, the
  fixed arrays, the frame), `clrP ; finP` writes **`fixPath (pmap hP) X.c X.f₀ X.P X.mssp X.fr
  (negLay gid I x hP)`** into the flow array (`FLHas`), the memory `≤ Wz` zero again.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep
  WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Gen

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **A negative-length call with a feasible potential has an outcome.** -/
theorem neg_some {negSSSP : (D → ℤ) → Option (F → ℤ)} (hneg : NegSSSPSpec M negSSSP)
    {c s : D → ℤ} (h : ∃ Φ : F → ℤ, IsPseudo M c (s + M.cob Φ)) :
    ∃ χ, negSSSP (c - s) = some χ := by
  obtain ⟨Φ, hΦ⟩ := h
  rcases e : negSSSP (c - s) with _ | χ
  · have := hneg (c - s)
    rw [e] at this
    obtain ⟨n, cw, hw, hneg'⟩ := this
    have hp : (M.dualGraph (c - s)).IsPot Φ := fun a => by
      have := hΦ.le_cap a
      simp only [Pi.add_apply, cob] at this
      show Φ (M.face (M.rev a)) ≤ Φ (M.face a) + (c - s) a
      simp only [Pi.sub_apply]; linarith
    have := (M.dualGraph (c - s)).walkLen_nonneg hp hw
    omega
  · exact ⟨χ, rfl⟩

end Gen

/-- **The resident image is zero outside its two blocks.** -/
theorem img_zero {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} {X : SLx M} {W : ℕ} (hG : X.Good W)
    {nm : ℕ → ℕ} (hI : X.Img nm) {a : ℕ} (ha : a ≤ X.WN) (h1 : ¬ a < X.lb + 2 * X.P.k)
    (h2 : ¬ (X.Wf + 1 ≤ a ∧ a < X.Wf + 1 + (X.lb + 2 * X.P.k))) :
    nm a = 0 ∧ nm (X.SH + a) = 0 := by
  obtain ⟨pm, r, Lz, hB, hI⟩ := hI
  have hL := MsCall.frPrm_lay hB
  have esb := SLx.prm_sb hG pm r Lz
  have eW := SLx.prm_W hG pm r Lz
  have e : (FrFix.frCfgN (X.prm pm r Lz) X.L).nmem a =
      if a < (X.prm pm r Lz).sb then FrFix.frNM (X.prm pm r Lz) a
      else if (X.prm pm r Lz).W + 1 ≤ a ∧ a < (X.prm pm r Lz).W + 1 + (X.prm pm r Lz).sb then
        FrFix.frRS (X.prm pm r Lz) X.L (a - ((X.prm pm r Lz).W + 1)) else 0 :=
    FrFix.frCfgN_nmem hL a
  rw [esb, eW] at e
  rw [if_neg h1, if_neg h2] at e
  exact ⟨(hI a ha).1.trans e, (hI a ha).2.trans e⟩

end BKMNW

end PlanarFlow
