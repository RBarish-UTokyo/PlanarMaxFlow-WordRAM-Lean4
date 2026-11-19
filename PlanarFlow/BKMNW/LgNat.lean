module

public import PlanarFlow.BKMNW.NegInPlace

/-!
# The logged run of a program without reals, from a configuration with any reals

`lg_lift` (`PlanarFlow/NegSSSP/Enc/StoreLog.lean`) needs the outer configuration to agree with the
reference start on the reals too. For a program without real instructions (`Klein.natOnly`) the
reals play no role: **`lg_liftNat`** runs the logged program from any `d` agreeing with the
reference start `c` on the natural registers of `U` and the natural memory up to `Ws` only; the
reals of `d` are kept. (This is the reals step of `negFix_lgRun`, for any program: the in-place
pattern of `negCall` for other natural-word subroutines.)
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt NegSSSP

/-- **The logged run of a program without reals, any reals outside.** -/
theorem lg_liftNat {P P' : Input} {Ws W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P Ws s c c' k) {U : ℕ → Bool} {LP ONE : ℕ} (hs : s.regsOK U = true)
    (hn : s.noInp = true) (hr : s.noRand = true) (hnat : Klein.natOnly s = true)
    (hLP : U LP = false) (hONE : U ONE = false) (hne : LP ≠ ONE) (hWs : Ws ≤ W) (d : Config)
    (hA : ∀ r, U r = true → d.nreg r = c.nreg r) (hm : ∀ a ≤ Ws, d.nmem a = c.nmem a)
    (hd : WordsBounded W d) (h1 : d.nreg ONE = 1) (hp : Ws < d.nreg LP)
    (hpW : d.nreg LP + k ≤ W) :
    ∃ d' k' j, Exec P' W (lgS LP ONE s) d d' k' ∧ k' ≤ 3 * k ∧ j ≤ k ∧
      (∀ r, U r = true → d'.nreg r = c'.nreg r) ∧ (∀ a ≤ Ws, d'.nmem a = c'.nmem a) ∧
      LgKeep U Ws LP (d.nreg LP) j d d' ∧ d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧
      ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  set d₀ := setR d c.rreg c.rmem with hd₀
  have hA₀ : Agree U Ws c d₀ := ⟨hA, fun _ _ => rfl, hm, fun _ _ => rfl⟩
  obtain ⟨d₀', k', j, ex, hk, hj, hA', hK, L, o1, o2⟩ :=
    lg_lift (P' := P') (W := W) h hs hn hr hLP hONE hne hWs d₀ hA₀ (wb_setR hd _ _) h1 hp hpW
  have ex' := Exec.mbReals ex (mbNatS_of_natOnly _ (lgS_natOnly _ hnat)) d.rreg d.rmem
  rw [hd₀, setR_setR, setR_self] at ex'
  exact ⟨setR d₀' d.rreg d.rmem, k', j, ex', hk, hj, hA'.nreg, hA'.nmem,
    ⟨hK.lp, hK.nreg, fun _ _ => rfl, hK.nmem, fun _ _ => rfl, hK.logle, hK.dirty⟩, rfl, rfl,
    L, o1, o2⟩

end MfDrv

end BKMNW

end PlanarFlow
