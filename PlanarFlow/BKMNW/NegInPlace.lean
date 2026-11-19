module

public import PlanarFlow.BKMNW.MachNeg
public import PlanarFlow.BKMNW.NegFixOK
public import PlanarFlow.BKMNW.MbRun

/-!
# The machine's negative-length shortest paths run in place, logged

`negFix` (`PlanarFlow/NegSSSP/DrvFix.lean`) runs from the root configuration
`rootCfgP g M ℓ P` (`P = repsN M.dual g.gd`): registers `< 3200` zero but `3001 = 1`,
`3002 = rtHb`, `3003 = rtH`, the memory `rootMemP` (the root frame at `rtHb + 5`, zero elsewhere),
reals zero, word bound `rtW`. This file runs it **inside a larger configuration** whose memory up
to `rtW` is the root image and whose memory above `rtW` (and registers `≥ 3200`) hold anything
(the max-flow frames): the run is logged (`lgS`, `PlanarFlow/NegSSSP/Enc/StoreLog.lean`) so that
the cells it wrote can be cleared afterwards in time linear in the run.

* `mbNatS_of_natOnly`; **`res_shift`** (`Res` read from a copy of the frame at another base);
  `rtH_le_rtW`; **`rootMemP_out`** (the root image is zero outside `[rtHb + 2, rtH)`).
* **`negFix_lgRun`**: from any `d` agreeing with the root configuration on the registers `< 3200`
  and on the memory up to `rtW` (reals arbitrary), with `r7331 = 1` and the log pointer `r7330`
  above `rtW`, the logged program `lgS 7330 7331 negFix` runs (any input) within
  `3 · negT C C₀ n` steps (`negT` the bound of `negMach_run`), the final configuration holds
  `negMach g M I ℓ` in the root frame's outcome region (`NegEnc`), and the frame is `LgKeep`: at
  most `negT` log entries, each `≤ rtW`; every cell `≤ rtW` outside the log unchanged; the
  registers `≥ 3200` but `7330`, the memory above `rtW` outside the log, the reals and the output
  kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP
  NegSSSP.Driver NegSSSP.Frame CombMap

/-- A statement without reals has no real instruction (`mbNatS`). -/
theorem mbNatS_of_natOnly : ∀ s : Stmt, Klein.natOnly s = true → mbNatS s = true
  | .skip, _ => rfl
  | .instr i, h => by cases i <;> simp_all [Klein.natOnly, mbNatS, mbNatI, Instr.isReal]
  | .seq s t, h => by
    simp only [Klein.natOnly, mbNatS, Bool.and_eq_true] at h ⊢
    exact ⟨mbNatS_of_natOnly s h.1, mbNatS_of_natOnly t h.2⟩
  | .ifLtN _ _ s t, h => by
    simp only [Klein.natOnly, mbNatS, Bool.and_eq_true] at h ⊢
    exact ⟨mbNatS_of_natOnly s h.1, mbNatS_of_natOnly t h.2⟩
  | .ifLtR .., h => by simp [Klein.natOnly] at h
  | .whileLtN _ _ s, h => by
    simp only [Klein.natOnly, mbNatS] at h ⊢
    exact mbNatS_of_natOnly s h
  | .whileLtR .., h => by simp [Klein.natOnly] at h

universe w

section Res

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **`Res` read from a copy of the frame at another base.** -/
theorem res_shift (g : GIds D V) (N : CombMap D V F) {L : ℕ} {P : Finset D}
    {o : Option (V → ℤ)} {d e d₂ : ℕ} {c c₂ : Config} (h : Res g N L P o d e c)
    (hm : ∀ i < Frame.fsz P.card (ck N P), c₂.nmem (d₂ + i) = c.nmem (d + i)) :
    Res g N L P o d₂ (d₂ + Frame.fsz P.card (ck N P)) c₂ := by
  obtain ⟨-, h⟩ := h
  refine ⟨rfl, ?_⟩
  have key : ∀ a b, a = d₂ + (b - d) → d ≤ b → b < d + Frame.fsz P.card (ck N P) →
      c₂.nmem a = c.nmem b := fun a b h1 h2 h3 => by
    rw [h1, hm _ (by omega)]; congr 1; omega
  unfold Frame.fin at *
  unfold Frame.fsz at key
  rcases o with _ | f
  · rw [key _ (d + (4 + 5 * ck N P + P.card)) (by omega) (by omega) (by omega)]; exact h
  · obtain ⟨h0, w, ι, hw, h1, h2, h3⟩ := h
    have e0 : c₂.nmem (d₂ + (4 + 5 * ck N P + P.card)) = 0 := by
      rw [key _ (d + (4 + 5 * ck N P + P.card)) (by omega) (by omega) (by omega)]; exact h0
    have e1 : c₂.nmem (d₂ + (4 + 5 * ck N P + P.card) + 1) = w := by
      rw [key _ (d + (4 + 5 * ck N P + P.card) + 1) (by omega) (by omega) (by omega)]; exact h1
    refine ⟨e0, w, ι, hw, e1, fun v hv => ?_, h3⟩
    obtain ⟨a1, a2, a3, a4⟩ := h2 v hv
    refine ⟨a1, ?_, ?_, a4⟩
    · rw [key _ (d + (4 + 5 * ck N P + P.card) + 2 + v) (by omega) (by omega) (by omega)]
      exact a2
    · rw [key _ (d + (4 + 5 * ck N P + P.card) + 2 + 2 * P.card + v) (by omega) (by omega)
        (by omega)]
      exact a3

end Res

section Root

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

theorem rtH_le_rtW {n L G m k : ℕ} (hm : m ≤ n) (hk : k ≤ n) : rtH n L G m k ≤ rtW n L G := by
  have h1 : rtH n L G m k ≤ rtH n L G n n := by unfold rtH Frame.fsz; omega
  have h2 : rtH n L G n n ≤ rtW n L G := by unfold rtW; omega
  omega

theorem card_le_n (P : Finset D) : P.card ≤ Fintype.card D := Finset.card_le_univ P

theorem ck_le_n (N : CombMap D F V) (P : Finset D) : ck N P ≤ Fintype.card D :=
  Finset.card_le_univ _

/-- **The root image is zero outside `[rtHb + 2, rtH)`.** -/
theorem rootMemP_out (g : GIds D F) (M : CombMap D V F) (ℓ : D → ℤ) (P : Finset D) {a : ℕ}
    (ha : a < rtHb (Fintype.card D) (rtL M ℓ) g.G + 2 ∨
      rtH (Fintype.card D) (rtL M ℓ) g.G P.card (ck M.dual P) ≤ a) :
    rootMemP g M ℓ P a = 0 := by
  unfold rtH Frame.fsz at ha
  simp only [rootMemP]
  set Hb := rtHb (Fintype.card D) (rtL M ℓ) g.G
  set k := ck M.dual P
  set m := P.card
  repeat (rw [blk_out]; swap; omega)
  rw [blk_out]; omega

/-- The bound of `negMach_run`. -/
def negT (C C₀ n : ℕ) : ℕ :=
  (10 ^ 12 + 1 + fsKC + 80) * (cMach C C₀).negsssp n + fsKC + 22 + (12 * n + 4610)

/-- **The logged run of `negFix` in place** (see the module docstring). -/
theorem negFix_lgRun (C C₀ : ℕ) (hC : 200000 ≤ C) (g : GIds D F) {M : CombMap D V F}
    {ℓ : D → ℤ} (hpre : NegPre M ℓ) (I P' : Input) {W : ℕ} (d : Config)
    (hd : WordsBounded W d)
    (hA : ∀ r, r < nfR → d.nreg r = (rootCfgP g M ℓ (repsN M.dual g.gd)).nreg r)
    (hm : ∀ a ≤ rtW (Fintype.card D) (rtL M ℓ) g.G,
      d.nmem a = rootMemP g M ℓ (repsN M.dual g.gd) a)
    (h1 : d.nreg 7331 = 1) (hp : rtW (Fintype.card D) (rtL M ℓ) g.G < d.nreg 7330)
    (hpW : d.nreg 7330 + negT C C₀ (Fintype.card D) ≤ W)
    (hWs : rtW (Fintype.card D) (rtL M ℓ) g.G ≤ W) :
    ∃ d' k j, Exec P' W (lgS 7330 7331 negFix) d d' k ∧ k ≤ 3 * negT C C₀ (Fintype.card D) ∧
      j ≤ negT C C₀ (Fintype.card D) ∧ NegEnc g M ℓ (negMach g M I ℓ) d' ∧
      LgKeep nfU (rtW (Fintype.card D) (rtL M ℓ) g.G) 7330 (d.nreg 7330) j d d' ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨⟨c', t, hr, ht, ho⟩, hall⟩ := negMach_run C C₀ hC g hpre I
  have henc := hall c' t hr
  set Ws := rtW (Fintype.card D) (rtL M ℓ) g.G with hWs'
  set d₀ := setR d (fun _ => 0) (fun _ => 0) with hd₀
  have hA₀ : Agree nfU Ws (rootCfgP g M ℓ (repsN M.dual g.gd)) d₀ :=
    ⟨fun r hr => hA r (by simpa [nfU] using hr), fun _ _ => rfl, fun a ha => hm a ha,
      fun _ _ => rfl⟩
  obtain ⟨d₀', k, j, ex, hk, hj, hA', hK, L, o1, o2⟩ :=
    lg_lift (P' := P') (W := W) hr negFix_regsOK negFix_noInp negFix_noRand
      (show nfU 7330 = false by decide) (show nfU 7331 = false by decide) (by decide) hWs d₀ hA₀
      (wb_setR hd _ _) h1 hp (show d.nreg 7330 + t ≤ W by unfold negT at hpW; omega)
  have ex' := Exec.mbReals ex (mbNatS_of_natOnly _ (lgS_natOnly _ negFix_natOnly)) d.rreg d.rmem
  rw [hd₀, setR_setR, setR_self] at ex'
  refine ⟨setR d₀' d.rreg d.rmem, k, j, ex', by unfold negT; omega, by unfold negT; omega, ?_,
    ⟨hK.lp, hK.nreg, fun _ _ => rfl, hK.nmem, fun _ _ => rfl, hK.logle, hK.dirty⟩, rfl, rfl, ?_⟩
  · unfold NegEnc at henc ⊢
    have hk' := ck_le_n M.dual (repsN M.dual g.gd)
    have hm' := card_le_n (repsN M.dual g.gd)
    have hle := rtH_le_rtW (L := rtL M ℓ) (G := g.G) hm' hk'
    have := res_shift g M.dual (d₂ := rtHb (Fintype.card D) (rtL M ℓ) g.G + 5)
      (c₂ := setR d₀' d.rreg d.rmem) henc (fun i hi => by
        rw [setR_nmem, hA'.nmem _ (by unfold rtH at hle; omega)])
    exact this
  · rw [setR_output, o2]
    have : L = [] := by
      have h0 : (rootCfgP g M ℓ (repsN M.dual g.gd)).output = [] := rfl
      rw [h0, ho] at o1; simpa using o1.symm
    rw [this, List.append_nil]; rfl

end Root

end MfDrv

end BKMNW

end PlanarFlow
