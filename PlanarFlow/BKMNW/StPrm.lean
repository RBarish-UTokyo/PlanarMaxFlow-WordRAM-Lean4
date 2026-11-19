module

public import PlanarFlow.BKMNW.StFix
public import PlanarFlow.NegSSSP.Enc.HoistPrmFe

/-!
# The parameters of the fixed s-t flow program in closed form

`StFix.ssV B nD n j` (`j < 39`) is the `j`-th instance-dependent constant of the s-t flow program
`STFlow.pstProg B nD n` (`hsAt` at a path). Here they are given in closed form: every one is
linear, `ssV B nD n j = a n + b nD + c B + d` (`ssF`, the coefficients `ssCo`), proved
symbolically for all `B nD n` by unfolding the program along the path (`hs_eval`, a tactic that
unfolds the head of the statement under `hsAt` until it reaches a constant) and `ring`:

* `ssCo`, `ssF`, **`ssV_eq`**: `ssV B nD n j = ssF B nD n j` for `j < 39`;
* `sPrmL` (the 45 parameters of `sNFM` as linear forms in the primary registers `8000 … 8007`:
  `n`, `nD`, `B`, `pstM H`, `H`, `β`, `ib`, `len`), **`sPrm`** `= hpProg 1000 8010 sPrmL`,
  `sPrm_val`, **`sPrm_exec`**: within `hpCost sPrmL` steps, `r1000 + j = sVM B nD n H β ib len j`
  for `j < 45` (the hypothesis `hv` of `STFlow.st_sNFM`).
-/

@[expose] public section

namespace PlanarFlow

namespace BKMNW

namespace StFix

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt NegSSSP

open Lean Elab Tactic Meta in
/-- Unfold the head constant of the statement under the first `hsAt` (looking through `block`
and the left argument of `++`). -/
elab "hs_unf" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some e := t.find? (fun e => e.isAppOfArity ``PlanarFlow.NegSSSP.hsAt 2)
    | throwError "hs_unf: no hsAt"
  let mut x := e.getArg! 0
  let mut found : Option Name := none
  for _ in List.range 40 do
    match x.getAppFn with
    | .const c _ =>
      if c == ``WordRAM.Machine.Stmt.block then x := x.getArg! 0
      else if c == ``HAppend.hAppend then x := x.getArg! 4
      else if (← getEnv).isConstructor c then throwError "hs_unf: constructor"
      else
        found := some c
        break
    | _ => throwError "hs_unf: not a constant"
  match found with
  | some c => evalTactic (← `(tactic| unfold $(mkIdent c):ident))
  | none => throwError "hs_unf: nothing found"

/-- Evaluate `hsAt` of a program along a path. -/
macro "hs_eval" : tactic => `(tactic| repeat (first
  | (simp only [NegSSSP.hsAt, WordRAM.Machine.Stmt.block_cons, List.cons_append,
      List.nil_append, List.append_assoc])
  | hs_unf))

/-- Close a linear identity between layout constants. -/
macro "hs_fin" : tactic => `(tactic| (
  (try simp only [Klein.iHD, Klein.iIV, Klein.iIT, Klein.iIF, Klein.iIC, Klein.iGB, Klein.iXT,
    Klein.iRV, Klein.iNF, Klein.iNE, Klein.iNG, Klein.iNT, Klein.iNH, Klein.iIS, Klein.iLN,
    Klein.iED, Klein.aWT, Klein.aPH, Klein.aTP, Klein.aVL, Klein.aH0, Klein.aTH, STFlow.aCP,
    STFlow.aAK, STFlow.aRS, STFlow.aOT])
  (try ring_nf)
  (try omega)))

/-- The coefficients `(a, b, c, d)` of the parameters (`a n + b nD + c B + d`). -/
def ssCo : List (ℕ × ℕ × ℕ × ℕ) := [(1, 0, 0, 0), (0, 0, 1, 0), (0, 0, 1, 1), (0, 0, 1, 2), (0, 0, 1, 3), (0, 0, 1, 4), (0, 0, 1, 5), (0, 0, 1, 6), (0, 0, 1, 7), (0, 0, 1, 8), (0, 0, 1, 9), (0, 0, 1, 10), (0, 0, 1, 11), (0, 0, 1, 12), (0, 0, 1, 13), (0, 0, 1, 14), (0, 0, 1, 15), (7, 9, 0, 2), (3, 9, 0, 2), (7, 9, 0, 3), (4, 9, 0, 2), (0, 3, 0, 0), (0, 1, 0, 0), (0, 4, 0, 0), (0, 5, 0, 0), (0, 2, 0, 0), (0, 3, 0, 2), (7, 9, 0, 4), (5, 9, 0, 2), (7, 9, 0, 5), (6, 9, 0, 2), (1, 8, 0, 0), (1, 8, 0, 1), (0, 3, 0, 1), (0, 8, 0, 0), (0, 3, 0, 3), (0, 5, 0, 3), (0, 4, 0, 3), (0, 6, 0, 3)]

/-- **The parameters of the s-t flow program in closed form.** -/
def ssF (B nD n : ℕ) (j : ℕ) : ℕ :=
  (ssCo.getD j (0, 0, 0, 0)).1 * n + (ssCo.getD j (0, 0, 0, 0)).2.1 * nD +
    (ssCo.getD j (0, 0, 0, 0)).2.2.1 * B + (ssCo.getD j (0, 0, 0, 0)).2.2.2

/-- **The closed forms are the constants of the program.** -/
theorem ssV_eq (B nD n : ℕ) {j : ℕ} (hj : j < 39) : ssV B nD n j = ssF B nD n j := by
  simp only [ssF]
  interval_cases j <;>
    simp only [ssV, ssPaths, ssCo, List.getD_cons_succ, List.getD_cons_zero]
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin
  · hs_eval
    hs_fin

/-! ### The parameters on the machine -/

/-- **The 45 parameters of `sNFM` as linear forms** in the primary registers `8000 … 8007`
(`n`, `nD`, `B`, `M = pstM H`, `H`, `β`, `ib`, `len`). -/
def sPrmL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8000)], 0),
    ([(1, hpM.v 8002)], 0),
    ([(1, hpM.v 8002), (1, hpM.one)], 0),
    ([(1, hpM.v 8002), (2, hpM.one)], 0),
    ([(1, hpM.v 8002), (3, hpM.one)], 0),
    ([(1, hpM.v 8002), (4, hpM.one)], 0),
    ([(1, hpM.v 8002), (5, hpM.one)], 0),
    ([(1, hpM.v 8002), (6, hpM.one)], 0),
    ([(1, hpM.v 8002), (7, hpM.one)], 0),
    ([(1, hpM.v 8002), (8, hpM.one)], 0),
    ([(1, hpM.v 8002), (9, hpM.one)], 0),
    ([(1, hpM.v 8002), (10, hpM.one)], 0),
    ([(1, hpM.v 8002), (11, hpM.one)], 0),
    ([(1, hpM.v 8002), (12, hpM.one)], 0),
    ([(1, hpM.v 8002), (13, hpM.one)], 0),
    ([(1, hpM.v 8002), (14, hpM.one)], 0),
    ([(1, hpM.v 8002), (15, hpM.one)], 0),
    ([(7, hpM.v 8000), (9, hpM.v 8001), (2, hpM.one)], 0),
    ([(3, hpM.v 8000), (9, hpM.v 8001), (2, hpM.one)], 0),
    ([(7, hpM.v 8000), (9, hpM.v 8001), (3, hpM.one)], 0),
    ([(4, hpM.v 8000), (9, hpM.v 8001), (2, hpM.one)], 0),
    ([(3, hpM.v 8001)], 0),
    ([(1, hpM.v 8001)], 0),
    ([(4, hpM.v 8001)], 0),
    ([(5, hpM.v 8001)], 0),
    ([(2, hpM.v 8001)], 0),
    ([(3, hpM.v 8001), (2, hpM.one)], 0),
    ([(7, hpM.v 8000), (9, hpM.v 8001), (4, hpM.one)], 0),
    ([(5, hpM.v 8000), (9, hpM.v 8001), (2, hpM.one)], 0),
    ([(7, hpM.v 8000), (9, hpM.v 8001), (5, hpM.one)], 0),
    ([(6, hpM.v 8000), (9, hpM.v 8001), (2, hpM.one)], 0),
    ([(1, hpM.v 8000), (8, hpM.v 8001)], 0),
    ([(1, hpM.v 8000), (8, hpM.v 8001), (1, hpM.one)], 0),
    ([(3, hpM.v 8001), (1, hpM.one)], 0),
    ([(8, hpM.v 8001)], 0),
    ([(3, hpM.v 8001), (3, hpM.one)], 0),
    ([(5, hpM.v 8001), (3, hpM.one)], 0),
    ([(4, hpM.v 8001), (3, hpM.one)], 0),
    ([(6, hpM.v 8001), (3, hpM.one)], 0),
    ([(1, hpM.v 8003)], 1),
    ([(1, hpM.v 8003)], 0),
    ([(1, hpM.v 8004)], 0),
    ([(1, hpM.v 8005)], 0),
    ([(1, hpM.v 8006)], 0),
    ([(1, hpM.v 8007)], 0)]

theorem sPrmL_length : sPrmL.length = 45 := rfl

theorem sPrm_shape : hpShape 8000 8008 15 1 sPrmL = true := by decide

/-- **The parameter program of the s-t flow** (into `r1000 … r1044`, scratch `r8010`,
`r8011`). -/
def sPrm : Stmt := hpProg 1000 8010 sPrmL

theorem sPrm_natOnly : Klein.natOnly sPrm = true := by kernel_rfl

/-- The primary values. -/
structure SPrim (f : ℕ → ℕ) (B nD n H β ib len : ℕ) : Prop where
  r0 : f 8000 = n
  r1 : f 8001 = nD
  r2 : f 8002 = B
  r3 : f 8003 = STFlow.pstM H
  r4 : f 8004 = H
  r5 : f 8005 = β
  r6 : f 8006 = ib
  r7 : f 8007 = len

theorem sPrm_val {f : ℕ → ℕ} {B nD n H β ib len : ℕ} (h : SPrim f B nD n H β ib len) {j : ℕ}
    (hj : j < 45) : hpSum f (sPrmL.getD j ([], 0)).1 - (sPrmL.getD j ([], 0)).2 =
      sVM B nD n H β ib len j := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := h
  by_cases h39 : j < 39
  · have e : sVM B nD n H β ib len j = ssF B nD n j := by
      simp only [sVM, sVN, show j < 43 by omega, h39, ↓reduceIte]; exact ssV_eq B nD n h39
    rw [e]
    interval_cases j <;>
      simp only [sPrmL, ssF, ssCo, hpSum, hpM.ev, List.getD_cons_succ, List.getD_cons_zero,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r0, r1, r2] <;> omega
  · interval_cases j <;>
      simp only [sPrmL, sVM, sVN, hpSum, hpM.ev, List.getD_cons_succ, List.getD_cons_zero,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r3, r4, r5, r6, r7] <;>
      simp

/-- **The parameters of `sNFM` on the machine**: from the primary registers, `sPrm` writes
`r1000 + j = sVM B nD n H β ib len j` for every `j < 45` within `hpCost sPrmL` steps. -/
theorem sPrm_exec {I : Input} {W : ℕ} {B nD n H β ib len : ℕ} (c : Config)
    (hc : WordsBounded W c) (hP : SPrim c.nreg B nD n H β ib len)
    (hW : 7 * n + 9 * nD + B + STFlow.pstM H + H + β + ib + len + 16 ≤ W) :
    ∃ c', Exec I W sPrm c c' (hpCost sPrmL) ∧
      (∀ j < 45, c'.nreg (1000 + j) = sVM B nD n H β ib len j) ∧
      (∀ r, (r < 1000 ∨ 1045 ≤ r) → r ≠ 8010 → r ≠ 8011 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 1000 8010 sPrmL :=
    hpShape_ok sPrm_shape (by omega) (by omega) (by simp [sPrmL_length]) (by omega)
      (by simp [sPrmL_length])
  obtain ⟨c', e, v, f, m, r, rm, o⟩ := hpProg_exec (I := I) sPrmL 1000 hok c hc (fun e he => by
    obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hP
    simp only [sPrmL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r0, r1,
        r2, r3, r4, r5, r6, r7] <;> omega)
  refine ⟨c', e, fun j hj => ?_, fun r h1 h2 h3 => f r (by rw [sPrmL_length]; omega) h2 h3, m,
    r, rm, o⟩
  rw [v j (by rw [sPrmL_length]; exact hj)]
  exact sPrm_val hP hj

end StFix

end BKMNW

end PlanarFlow
