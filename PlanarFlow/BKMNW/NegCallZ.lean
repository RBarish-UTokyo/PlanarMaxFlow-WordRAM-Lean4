module

public import PlanarFlow.BKMNW.NegCall

/-!
# A repeatable in-place call of `negFix`: from zero memory back to zero memory

`negCall` (`NegCall.lean`) needs the memory up to `Wz` to be the root image `rootMemP`. Here the
root image is **written** from a copy of the root frame's input part held above `Wz` (an `InP`
frame at a base `A`: header `n, m, k, L`, the dart identifiers, `α`, `σ`, the identifiers of the
ends and the offset lengths of the piece), so that the call goes from **memory up to `Wz` zero**
to **memory up to `Wz` zero**, the invariant of a driver calling the subroutine repeatedly with
its own data above `Wz`.

* **`rootCfgP_inP`**: the root configuration holds the input part of its frame (`InP`) for every
  piece `P` (as `rootCfg_props` for `reps`); **`rootMemP_out'`**: the root image is zero outside
  `Hb + 2` and `[Hb + 5, Hb + 5 + fin m k)`.
* `ncImgA` (`r7320 = Hb`, `r7321 = h`, `r7325 = A`: `mem[Hb + 2] := h`; the arguments of `cpArr`
  `4910 = fin m k = 4 + 5k + m` read from the frame at `A`, `4911 = A`, `4912 = Hb + 5`; scratch
  `7336 … 7339`), **`ncImg`** `= ncImgA ; cpArr`; **`ncImg_exec`**.
* **`negCallZ`** `= ncImg ; negCall`; **`negCallZ_exec`**: from memory up to `Wz` zero and an `InP`
  frame of the call at `A` (above `Wz`, below the copy area `Ob`), within
  **`9 · negT C C₀ n + 12 · fsz m k + 7 · fin m k + 3291`** steps the memory up to `Wz` is zero
  again, the copy at `Ob` holds `negMach g M I ℓ` (`Res`), the memory above `Wz` outside the copy
  area and the log area is kept (so is the frame at `A`), the registers `3000 … 3012` and every
  register outside `ncScr` kept, reals and output kept.

What remains for the max-flow driver is a program computing the `InP` frame of a call (the
identifiers, the face labels of the ends in the dual, the kept darts `repsN` and the offset
lengths `minLen`) from the max-flow frame.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP
  NegSSSP.Driver NegSSSP.Frame CombMap

universe w

section Root

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The root configuration holds the input part of its frame**, for every piece `P`. -/
theorem rootCfgP_inP (g : GIds D F) (M : CombMap D V F) (ℓ : D → ℤ) (P : Finset D) :
    InP g M.dual (minLen M.dual ℓ) (rtL M ℓ) (Fintype.card D) P
      (rtHb (Fintype.card D) (rtL M ℓ) g.G + 5)
      (rtH (Fintype.card D) (rtL M ℓ) g.G P.card (ck M.dual P)) (rootCfgP g M ℓ P) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun h hh => ?_, fun h hh => ?_, fun h hh => ?_, fun h hh => ?_,
    fun h hh => ?_, fun h hh => ?_⟩
  all_goals simp only [rootCfgP, rootMemP]
  all_goals simp (disch := omega) only [blk_out, blk_in, Nat.add_sub_cancel_left]

/-- **The root image is zero outside `Hb + 2` and the input part of the frame.** -/
theorem rootMemP_out' (g : GIds D F) (M : CombMap D V F) (ℓ : D → ℤ) (P : Finset D) {a : ℕ}
    (ha : a < rtHb (Fintype.card D) (rtL M ℓ) g.G + 2 ∨
      a = rtHb (Fintype.card D) (rtL M ℓ) g.G + 3 ∨ a = rtHb (Fintype.card D) (rtL M ℓ) g.G + 4 ∨
      rtHb (Fintype.card D) (rtL M ℓ) g.G + 5 + Frame.fin P.card (ck M.dual P) ≤ a) :
    rootMemP g M ℓ P a = 0 := by
  unfold Frame.fin at ha
  simp only [rootMemP]
  set Hb := rtHb (Fintype.card D) (rtL M ℓ) g.G
  set k := ck M.dual P
  set m := P.card
  repeat (rw [blk_out]; swap; omega)
  rw [blk_out]; omega

theorem rootMemP_hb2 (g : GIds D F) (M : CombMap D V F) (ℓ : D → ℤ) (P : Finset D) :
    rootMemP g M ℓ P (rtHb (Fintype.card D) (rtL M ℓ) g.G + 2) =
      rtH (Fintype.card D) (rtL M ℓ) g.G P.card (ck M.dual P) := by
  simp only [rootMemP]
  rw [blk_in (by omega) (by omega)]
  rfl

end Root

/-! ### Writing the root image -/

/-- `mem[Hb + 2] := h`; the arguments of the copy of the input part of the frame at `A`:
`4910 = 4 + 5k + m` (`m = mem[A + 1]`, `k = mem[A + 2]`), `4911 = A`, `4912 = Hb + 5`. -/
def ncImgA : Stmt := block [.constN 7336 1, .addN 7337 7325 7336, .loadN 7338 7337,
  .constN 7336 2, .addN 7337 7325 7336, .loadN 7339 7337,
  .constN 7336 5, .mulN 4910 7339 7336, .addN 4910 4910 7338, .constN 7336 4,
  .addN 4910 4910 7336, .copyN 4911 7325, .constN 7336 5, .addN 4912 7320 7336,
  .constN 7336 2, .addN 7337 7320 7336, .storeN 7337 7321]

/-- **Write the root image** from the input part of the frame at `A`. -/
def ncImg : Stmt := .seq ncImgA cpArr

/-- **A repeatable in-place call of `negFix`.** -/
def negCallZ : Stmt := .seq ncImg negCall

section Blocks

variable {P : Input} {W : ℕ}

theorem ncImgA_exec (c : Config) (hc : WordsBounded W c) {Hb h A m k : ℕ}
    (r20 : c.nreg 7320 = Hb) (r21 : c.nreg 7321 = h) (r25 : c.nreg 7325 = A)
    (hm : c.nmem (A + 1) = m) (hk : c.nmem (A + 2) = k) (hW1 : Hb + 5 ≤ W) (hW2 : A + 2 ≤ W)
    (hW3 : 4 + 5 * k + m ≤ W) :
    ∃ c' t, Exec P W ncImgA c c' t ∧ t = 17 ∧ c'.nmem = upd c.nmem (Hb + 2) h ∧
      c'.nreg 4910 = 4 + 5 * k + m ∧ c'.nreg 4911 = A ∧ c'.nreg 4912 = Hb + 5 ∧
      (∀ r, (r < 4910 ∨ 4912 < r) → (r < 7336 ∨ 7339 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold ncImgA
  exec_block
  all_goals try ((try config_simp); (try simp only [r20, r21, r25, hm, hk]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r20, r21, r25, hm, hk])
  all_goals try omega
  simp only [upd_apply]; split_ifs <;> omega

end Blocks

section Call

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **A repeatable in-place call of the machine's negative-length shortest paths** (see the
module docstring). -/
theorem negCallZ_exec (C C₀ : ℕ) (hC : 200000 ≤ C) (g : GIds D F) {M : CombMap D V F}
    {ℓ : D → ℤ} (hpre : NegPre M ℓ) (I P' : Input) {W Wz A Ob p : ℕ} (d : Config)
    (hd : WordsBounded W d)
    (r20 : d.nreg 7320 = rtHb (Fintype.card D) (rtL M ℓ) g.G)
    (r21 : d.nreg 7321 = rtH (Fintype.card D) (rtL M ℓ) g.G (repsN M.dual g.gd).card
      (ck M.dual (repsN M.dual g.gd)))
    (r22 : d.nreg 7322 = Ob) (r24 : d.nreg 7324 = p) (r25 : d.nreg 7325 = A)
    (hz : ∀ a ≤ Wz, d.nmem a = 0)
    (hin : InP g M.dual (minLen M.dual ℓ) (rtL M ℓ) (Fintype.card D) (repsN M.dual g.gd) A
      (A + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd))) d)
    (hWz : rtW (Fintype.card D) (rtL M ℓ) g.G ≤ Wz) (hA : Wz < A)
    (hAO : A + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) ≤ Ob)
    (hOp : Ob + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) ≤ p)
    (hpW : p + negT C C₀ (Fintype.card D) ≤ W) :
    ∃ d' t, Exec P' W negCallZ d d' t ∧
      t ≤ 9 * negT C C₀ (Fintype.card D) +
        12 * Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) +
        7 * Frame.fin (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) + 3291 ∧
      (∀ a ≤ Wz, d'.nmem a = 0) ∧
      Res g M.dual (rtL M ℓ) (repsN M.dual g.gd) (negMach g M I ℓ) Ob
        (Ob + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd))) d' ∧
      (∀ a, Wz < a →
        (a < Ob ∨ Ob + Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) ≤ a) →
        (a < p ∨ p + negT C C₀ (Fintype.card D) ≤ a) → d'.nmem a = d.nmem a) ∧
      (∀ r, 3000 ≤ r → r ≤ 3012 → d'.nreg r = d.nreg r) ∧
      (∀ r, ¬ ncScr r → d'.nreg r = d.nreg r) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  have hhF : rtH (Fintype.card D) (rtL M ℓ) g.G (repsN M.dual g.gd).card
      (ck M.dual (repsN M.dual g.gd)) = rtHb (Fintype.card D) (rtL M ℓ) g.G + 5 +
      Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) := rfl
  have hhW : rtH (Fintype.card D) (rtL M ℓ) g.G (repsN M.dual g.gd).card
      (ck M.dual (repsN M.dual g.gd)) ≤ rtW (Fintype.card D) (rtL M ℓ) g.G :=
    rtH_le_rtW (card_le_n _) (ck_le_n M.dual _)
  have hT : 4610 ≤ negT C C₀ (Fintype.card D) := by unfold negT; omega
  have hfin : Frame.fin (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) =
      4 + 5 * ck M.dual (repsN M.dual g.gd) + (repsN M.dual g.gd).card := rfl
  have hfsz : Frame.fsz (repsN M.dual g.gd).card (ck M.dual (repsN M.dual g.gd)) =
      6 + 5 * ck M.dual (repsN M.dual g.gd) + 5 * (repsN M.dual g.gd).card := rfl
  -- the root image
  obtain ⟨c₁, t₁, e₁, ht₁, am, a10, a11, a12, akeep, ar, arm, ao⟩ :=
    ncImgA_exec (P := P') d hd r20 r21 r25 hin.rm hin.rk (by omega) (by omega) (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, bcp, bkeep, bregs, br, brm, bo⟩ :=
    cpArr_exec (P := P') c₁ e₁.wb_right a10 a11 a12
      ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  have hcont := InP.content hin (rootCfgP_inP g M ℓ (repsN M.dual g.gd))
  have hm2 : ∀ a ≤ Wz, c₂.nmem a = rootMemP g M ℓ (repsN M.dual g.gd) a := by
    intro a ha
    by_cases h1 : rtHb (Fintype.card D) (rtL M ℓ) g.G + 5 ≤ a ∧
        a < rtHb (Fintype.card D) (rtL M ℓ) g.G + 5 +
          (4 + 5 * ck M.dual (repsN M.dual g.gd) + (repsN M.dual g.gd).card)
    · have := bcp (a - (rtHb (Fintype.card D) (rtL M ℓ) g.G + 5)) (by omega)
      rw [show rtHb (Fintype.card D) (rtL M ℓ) g.G + 5 +
        (a - (rtHb (Fintype.card D) (rtL M ℓ) g.G + 5)) = a by omega] at this
      rw [this, am, upd_other _ _ _ (by omega), hcont _ (by rw [hfin]; omega)]
      rw [show rtHb (Fintype.card D) (rtL M ℓ) g.G + 5 +
        (a - (rtHb (Fintype.card D) (rtL M ℓ) g.G + 5)) = a by omega]
      rfl
    · rw [bkeep a (by omega), am, upd_apply]
      split_ifs with h2
      · rw [h2, rootMemP_hb2]
      · rw [hz a ha, rootMemP_out' g M ℓ _ (by rw [hfin]; omega)]
  have k2 : ∀ r, (r < 4910 ∨ 4916 < r) → (r < 7336 ∨ 7339 < r) → c₂.nreg r = d.nreg r :=
    fun r h1 h2 => by rw [bregs r (by omega), akeep r (by omega) h2]
  -- the call
  obtain ⟨d', t, ex, ht, hz', hres, habove, hdrv, hkeep, hr, hrm, ho⟩ :=
    negCall_exec C C₀ hC g hpre I P' c₂ e₂.wb_right (by rw [k2 _ (by omega) (by omega), r20])
      (by rw [k2 _ (by omega) (by omega), r21]) (by rw [k2 _ (by omega) (by omega), r22])
      (by rw [k2 _ (by omega) (by omega), r24]) hm2 hWz (by omega) hOp hpW
  refine ⟨d', _, (e₁.seq e₂).seq ex, ?_, hz', hres, fun a ha ho hp => ?_, fun r h1 h2 => ?_,
    fun r hr' => ?_, ?_, ?_, ?_⟩
  · rw [hfin] at ⊢; omega
  · rw [habove a ha ho hp, bkeep a (by omega), am, upd_other _ _ _ (by omega)]
  · rw [hdrv r h1 h2, k2 r (by omega) (by omega)]
  · rw [hkeep r hr', k2 r (by unfold ncScr at hr'; omega) (by unfold ncScr at hr'; omega)]
  · rw [hr, br, ar]
  · rw [hrm, brm, arm]
  · rw [ho, bo, ao]

end Call

end MfDrv

end BKMNW

end PlanarFlow
