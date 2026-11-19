module

public import PlanarFlow.NegSSSP.DrvFixA
public import PlanarFlow.NegSSSP.FixWN

/-!
# The whole negative-length recursion as one fixed program

**`negFix`** `= fxSet ; drvT`: one statement, independent of the instance.

* **`fxSet`** (the setup): from the root frame at `Hb + 5` (`Hb` in `r3002`) it reads `n = #D`
  and the length bound `L`, computes `log₂ (3n)` by halving and `spWs n` (the blocks `prepLog`,
  `prepB0` of the split's preparation), puts **`Gt = spWs n + 1`** into `r3100`, and evaluates the
  polynomial expression `WNbE` (`FixWN.lean`) in the variables `n`, `L`, `spWs n` by the
  compiled straight-line program `PE.comp` (`FixPoly.lean`), leaving **`WN = WNb n L`** in
  `r3101`. It writes registers only (`2966 … 2978`, `3100 …`), within `12 n + 4610` steps, under
  the word bound `fxWB n L ≤ W` (`fxWB n L = PE.evalU …`: the polynomial `WNb` with every
  constant and every variable — `n`, `L`, `spWs n` — increased by one) and
  `spWs n + 205 ≤ W`.
* **`drvT`** (`DrvFixA.lean`): the recursion's program `driver testS (leafS Gt) splitS0
  (nodeS Gt (Fs WN Gt))` with `Gt`, `WN` read from `r3100`, `r3101`.

**`Driver.drive_negsssp_fixed`**: `Driver.drive_negsssp_machine` for the fixed program `negFix`,
within **`(10¹² + 1 + fsKC + 80) · (cMach C C₀).negsssp (#D) + fsKC + 22 + 12 · #D + 4610`**
steps (`O(n log² n)`), with the same polynomial word-size hypotheses and the two of the setup.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt PlanarFlow.NegSSSP.Driver
  PlanarFlow.NegSSSP.Frame

variable {P : Input} {W : ℕ}

/-! ### The setup -/

/-- `r2966 = 1`, `r2967 = 2`, `r2969 = n`, `r2970 = 3n`, `r2971 = 0`, `r3102 = n`,
`r3103 = L` (the frame at `r3002 + 5`). -/
def fxA : Stmt := block [.constN 2966 1, .constN 2967 2, .constN 2975 5, .addN 2975 3002 2975,
  .loadN 2969 2975, .addN 2970 2969 2969, .addN 2970 2970 2969, .constN 2971 0,
  .constN 2976 3, .addN 2975 2975 2976, .loadN 3103 2975, .copyN 3102 2969]

/-- `r3104 = spWs n`, `r3100 = Gt = spWs n + 1`. -/
def fxB : Stmt := block [.copyN 3104 2973, .copyN 3100 2978]

/-- `r3101 = WN`. -/
def fxC : Stmt := block [.copyN 3101 3105]

/-- **The setup of the fixed recursion.** -/
def fxSet : Stmt :=
  .seq fxA (.seq prepLog (.seq prepB0 (.seq fxB (.seq (PE.comp 3102 PE.WNbE 3105) fxC))))

/-- **The whole negative-length recursion as one fixed program.** -/
def negFix : Stmt := .seq fxSet drvT

/-- The values of the variables of `WNbE`. -/
def fxρ (n L : ℕ) (i : ℕ) : ℕ := [n, L, spWs n].getD i 0

/-- **The word bound of the setup's polynomial evaluation.** -/
def fxWB (n L : ℕ) : ℕ := PE.evalU (fxρ n L) PE.WNbE

theorem fxA_exec (c : Config) (hc : WordsBounded W c) {Hb n L : ℕ} (r02 : c.nreg 3002 = Hb)
    (hn : c.nmem (Hb + 5) = n) (hL : c.nmem (Hb + 8) = L) (w1 : Hb + 8 ≤ W) (w2 : 3 * n ≤ W) :
    ∃ c' t, Exec P W fxA c c' t ∧ t = 12 ∧ c'.nreg 2966 = 1 ∧ c'.nreg 2967 = 2 ∧
      c'.nreg 2969 = n ∧ c'.nreg 2970 = n + n + n ∧ c'.nreg 2971 = 0 ∧ c'.nreg 3102 = n ∧
      c'.nreg 3103 = L ∧ (∀ r, (r < 2966 ∨ (2976 < r ∧ r < 3102) ∨ 3103 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hnW : n ≤ W := by omega
  unfold fxA
  exec_block
  all_goals try ((try config_simp); (try simp only [r02, hn, hL]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r02, hn, hL])
  simp only [upd_apply]; split_ifs <;> omega

theorem fxB_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W fxB c c' t ∧ t = 2 ∧ c'.nreg 3104 = c.nreg 2973 ∧
      c'.nreg 3100 = c.nreg 2978 ∧ (∀ r, r ≠ 3100 → r ≠ 3104 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fxB
  exec_block
  refine ⟨rfl, ?_, ?_, fun r h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem fxC_exec (c : Config) (hc : WordsBounded W c) :
    ∃ c' t, Exec P W fxC c c' t ∧ t = 1 ∧ c'.nreg 3101 = c.nreg 3105 ∧
      (∀ r, r ≠ 3101 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fxC
  exec_block
  refine ⟨rfl, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  all_goals config_simp
  simp only [upd_apply]; split_ifs <;> omega

theorem WNbE_cost : PE.cost PE.WNbE = 4577 := by decide +kernel

/-- **The setup**: `Gt = spWs n + 1` in `r3100`, `WN = WNb n L` in `r3101`, registers only. -/
theorem fxSet_exec (c : Config) (hc : WordsBounded W c) {Hb n L : ℕ} (r02 : c.nreg 3002 = Hb)
    (hn : c.nmem (Hb + 5) = n) (hL : c.nmem (Hb + 8) = L) (w1 : Hb + 8 ≤ W)
    (w2 : spWs n + 205 ≤ W) (w3 : fxWB n L ≤ W) :
    ∃ c' t, Exec P W fxSet c c' t ∧ t ≤ 12 * n + 4610 ∧ c'.nreg 3100 = spWs n + 1 ∧
      c'.nreg 3101 = WNb n L ∧ (∀ r, 2978 < r → r < 3100 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hsp : 66 * n + 35 ≤ spWs n := by unfold spWs; omega
  obtain ⟨c₁, t₁, e₁, ht₁, a66, a67, a69, a70, a71, a02, a03, ak, am, ar, arm, ao⟩ :=
    fxA_exec (P := P) c hc r02 hn hL w1 (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b71, bk, bm, br, brm, bo⟩ :=
    prepLog_exec (P := P) c₁ e₁.wb_right a66 a67 a70 a71 (by omega)
  have b71' : c₂.nreg 2971 = Nat.log 2 (3 * n) := by
    rw [b71, show n + n + n = 3 * n by omega]
  obtain ⟨c₃, t₃, e₃, ht₃, -, d73, -, d78, dk, dm, dr, drm, do'⟩ :=
    prepB0_exec (P := P) (k := n) c₂ e₂.wb_right (by rw [bk _ (by omega) (by omega)]; exact a66)
      (by rw [bk _ (by omega) (by omega)]; exact a67)
      (by rw [bk _ (by omega) (by omega)]; exact a69) b71' w2
  obtain ⟨c₄, t₄, e₄, ht₄, f04, f00, fk, fm, fr, frm, fo⟩ := fxB_exec (P := P) c₃ e₃.wb_right
  -- the variables of `WNbE`
  have v0 : c₄.nreg 3102 = n := by
    rw [fk _ (by omega) (by omega), dk _ (Or.inr ⟨by omega, by omega⟩),
      bk _ (by omega) (by omega)]; exact a02
  have v1 : c₄.nreg 3103 = L := by
    rw [fk _ (by omega) (by omega), dk _ (Or.inr ⟨by omega, by omega⟩),
      bk _ (by omega) (by omega)]; exact a03
  have v2 : c₄.nreg 3104 = spWs n := by rw [f04, d73]
  have hρ : ∀ i < 3, fxρ n L i = c₄.nreg (3102 + i) := by
    intro i hi
    interval_cases i
    · exact v0.symm
    · exact v1.symm
    · exact v2.symm
  have hvl := PE.varsLt_of_vl PE.WNbE_vl
  have hcg := PE.eval_congr hρ hvl
  obtain ⟨c₅, e₅, g05, gk, gm, gr, grm, go⟩ :=
    PE.comp_exec (P := P) 3102 3 PE.WNbE 3105 hvl le_rfl c₄ e₄.wb_right
      (by rw [← hcg.2]; exact w3)
  obtain ⟨c₆, t₆, e₆, ht₆, h01, hk, hm, hr, hrm, ho⟩ := fxC_exec (P := P) c₅ e₅.wb_right
  have hWN : c₆.nreg 3101 = WNb n L := by
    rw [h01, g05, ← hcg.1]
    exact PE.eval_WNbE (fxρ n L) rfl
  refine ⟨c₆, _, Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆)))), ?_,
    ?_, hWN, fun r h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [WNbE_cost]; omega
  · rw [hk _ (by omega), gk _ (by omega), f00, d78]
  · rw [hk _ (by omega), gk _ (by omega), fk _ (by omega) (by omega),
      dk _ (Or.inr ⟨by omega, by omega⟩), bk _ (by omega) (by omega), ak _ (Or.inr (Or.inl
        ⟨by omega, by omega⟩))]
  · rw [hm, gm, fm, dm, bm, am]
  · rw [hr, gr, fr, dr, br, ar]
  · rw [hrm, grm, frm, drm, brm, arm]
  · rw [ho, go, fo, do', bo, ao]

/-! ### The whole recursion as one fixed program -/

namespace Driver

open Finset BKMNW

universe w

variable {I : Input}

set_option maxHeartbeats 4000000 in
/-- **The whole negative-length recursion as one fixed program** (see the module docstring):
`drive_negsssp_machine` for `negFix = fxSet ; drvT`, with `Gt = spWs (#D) + 1` and
`WN = WNb (#D) L` computed by the setup. -/
theorem drive_negsssp_fixed (C C₀ : ℕ) (hC : 200000 ≤ C) {D V F : Type w} [Fintype D]
    [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    {M : CombMap D V F} (g : GIds D F) (hM : M.dual.IsPlane) (hrot : M.dual.RotTrans)
    (hface : M.dual.FaceTrans)
    {ℓ₀ : D → ℤ} (hneg : ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ₀ d)
    {L Hb : ℕ} (hGH : spWs (Fintype.card D) + 1 + g.G ≤ Hb)
    (hHb2 : 2 * spWs (Fintype.card D) + 2 ≤ Hb) (hWNH : WNb (Fintype.card D) L < Hb)
    (hℓ : ∀ x, |minLen M.dual ℓ₀ x| ≤ L) (hsumL : ∑ x, |minLen M.dual ℓ₀ x| ≤ L)
    (hWL : 8 * Fintype.card D * Fintype.card D * (L + 1) + 3 * L + 2 ≤ W)
    (hWL7 : 7 * L + 2 ≤ W) (hW6 : 1000000 ≤ W)
    (hW4 : 4 * WNb (Fintype.card D) L + 3 * L + 2 ≤ W)
    (hWs : spWs (Fintype.card D) + 205 ≤ W) (hWfx : fxWB (Fintype.card D) L ≤ W)
    {e h : ℕ} (c : Config) (hc : WordsBounded W c) (hg : GZ0 Hb c)
    (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1) (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h)
    (m0 : c.nmem Hb = 0) (m1 : c.nmem (Hb + 1) = 0)
    (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hroom : h + (Fintype.card D + 1) *
      roomB (Fintype.card D) (66 * Fintype.card D + 31 + fsRF (Fintype.card D)) ≤ W)
    (hin : InPR g M.dual (minLen M.dual ℓ₀) L (Fintype.card D) (reps M.dual) (Hb + 5) e c) :
    ∃ c' t o, Exec I W negFix c c' t ∧
      t ≤ (10 ^ 12 + 1 + fsKC + 80) * (cMach C C₀).negsssp (Fintype.card D) + fsKC + 22 +
        (12 * Fintype.card D + 4610) ∧
      PotOut (M.dual.graph ℓ₀) o ∧ Res g M.dual L (reps M.dual) o (Hb + 5) e c' ∧
      GZ0 Hb c' ∧ c'.output = c.output := by
  classical
  -- the word bound of the frame's addresses
  have h9 : 9 ≤ roomB (Fintype.card D) (66 * Fintype.card D + 31 + fsRF (Fintype.card D)) := by
    unfold roomB; omega
  have h9' : roomB (Fintype.card D) (66 * Fintype.card D + 31 + fsRF (Fintype.card D)) ≤
      (Fintype.card D + 1) *
        roomB (Fintype.card D) (66 * Fintype.card D + 31 + fsRF (Fintype.card D)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hn5 : c.nmem (Hb + 5) = Fintype.card D := hin.2.rn
  have hL8 : c.nmem (Hb + 5 + 3) = L := hin.2.rL
  obtain ⟨c₁, t₁, e₁, ht₁, s00, s01, sk, sm, sr, srm, so⟩ :=
    fxSet_exec (P := I) c hc r2 hn5 hL8 (by omega) hWs hWfx
  have hg₁ : GZ0 Hb c₁ := by
    refine ⟨fun r => ?_, fun a ha => ?_, fun a ha => ?_⟩
    · rw [sr]; exact hg.1 r
    · rw [srm]; exact hg.2.1 a ha
    · rw [sm]; exact hg.2.2 a ha
  have hin₁ : InPR g M.dual (minLen M.dual ℓ₀) L (Fintype.card D) (reps M.dual) (Hb + 5) e c₁ :=
    inPR_stab hin fun a _ _ => ⟨by rw [sm], by rw [srm]⟩
  obtain ⟨c', t, o, ex, ht, hpot, hres, hgz, hout⟩ :=
    drive_negsssp_machine (I := I) C C₀ hC g hM hrot hface hneg (Gt := spWs (Fintype.card D) + 1)
      (by omega) hGH hHb2 hWNH hℓ hsumL hWL hWL7 hW6 hW4 c₁ e₁.wb_right hg₁
      (by rw [sk _ (by omega) (by omega)]; exact r0)
      (by rw [sk _ (by omega) (by omega)]; exact r1)
      (by rw [sk _ (by omega) (by omega)]; exact r2)
      (by rw [sk _ (by omega) (by omega)]; exact r3)
      (by rw [sm]; exact m0) (by rw [sm]; exact m1) (by rw [sm]; exact m2) he hh hroom hin₁
  obtain ⟨ex', -⟩ := drvT_exec ex s00 s01
  exact ⟨c', t₁ + t, o, Exec.seq e₁ ex', by omega, hpot, hres, hgz, by rw [hout, so]⟩

end Driver

end NegSSSP

end PlanarFlow
