module

public import PlanarFlow.BKMNW.StPrm
public import PlanarFlow.BKMNW.KleinFix

/-!
# The parameters of the fixed Klein program in closed form (`knVM`)

`KleinFix.kmV B nD n k t j` (`j < 43`) is the `j`-th instance-dependent constant of Klein's masked
program `Klein.kleinProgM B nD n k t` (`hsAt` at a path). Every one is linear:
`kmV B nD n k t j = a t + b k + c n + d nD + e B + f` (`kmF`, coefficients `kmCo`, read off the
marker instance of `KleinFix.kmTbl`), proved symbolically for all `B nD n k t` by unfolding the
program along the path (`hs_eval`) and `ring`:

* `kmCo`, `kmF`, **`kmV_eq`**;
* `kPrmL` (the 48 parameters `knVM B nD n k t Hc β len` of `KleinFix.kNFM` as linear forms in the
  primary registers `7300 … 7307` = `B`, `nD`, `n`, `k`, `t`, `Hc`, `β`, `len`), **`kPrm`**
  `= hpProg 1000 7310 kPrmL`, **`kPrm_exec`**: within `hpCost kPrmL` steps,
  `r1000 + j = knVM B nD n k t Hc β len j` for `j < 48` (the hypothesis `hv` of
  `KleinFix.kNFM_exec`); registers outside `1000 … 1047`, `7310`, `7311` kept.
-/

@[expose] public section

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt NegSSSP KleinFix

/-- Close a linear identity between Klein's layout constants. -/
macro "km_fin" : tactic => `(tactic| (
  (try simp only [Klein.iHD, Klein.iIV, Klein.iIT, Klein.iIF, Klein.iIC, Klein.iGB, Klein.iXT,
    Klein.iRV, Klein.iNF, Klein.iNE, Klein.iNG, Klein.iNT, Klein.iNH, Klein.iIS, Klein.iLN,
    Klein.iED, Klein.aWT, Klein.aPH, Klein.aTP, Klein.aVL, Klein.aH0, Klein.aTH, Klein.aOUT,
    Klein.aRB, Klein.aMK, Klein.aRBM, Klein.iOB, Klein.iOE, Klein.iOL, Klein.aTL])
  (try ring_nf)
  (try omega)))

/-- The coefficients `(a, b, c, d, e, f)` of the parameters (`a t + b k + c n + d nD + e B + f`). -/
def kmCo : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [(0, 0, 1, 0, 0, 0), (0, 0, 0, 0, 1, 0), (0, 0, 0, 0, 1, 1), (0, 0, 0, 0, 1, 2), (0, 0, 0, 0, 1, 3), (0, 0, 0, 0, 1, 4), (0, 0, 0, 0, 1, 5), (0, 0, 0, 0, 1, 6), (0, 0, 0, 0, 1, 7), (0, 0, 0, 0, 1, 8), (0, 0, 0, 0, 1, 9), (0, 0, 0, 0, 1, 10), (0, 0, 0, 0, 1, 11), (0, 0, 0, 0, 1, 12), (0, 0, 0, 0, 1, 13), (0, 0, 0, 0, 1, 14), (0, 0, 0, 0, 1, 15), (0, 1, 7, 9, 0, 0), (0, 1, 3, 9, 0, 0), (0, 1, 7, 9, 0, 1), (0, 1, 4, 9, 0, 0), (0, 0, 0, 3, 0, 0), (0, 0, 0, 1, 0, 0), (0, 0, 0, 4, 0, 0), (0, 0, 0, 5, 0, 0), (0, 0, 0, 2, 0, 0), (0, 0, 0, 3, 0, 2), (0, 1, 7, 9, 0, 2), (0, 1, 5, 9, 0, 0), (0, 1, 7, 9, 0, 3), (0, 1, 6, 9, 0, 0), (0, 1, 0, 0, 0, 0), (0, 0, 1, 8, 0, 0), (1, 0, 0, 0, 0, 0), (0, 0, 0, 3, 0, 3), (0, 1, 1, 0, 0, 0), (0, 1, 7, 9, 0, 4), (1, 1, 7, 9, 0, 4), (0, 0, 0, 3, 0, 1), (0, 0, 0, 8, 0, 0), (0, 1, 1, 8, 0, 0), (0, 1, 2, 8, 0, 0), (0, 1, 3, 8, 0, 0)]

/-- **The parameters of Klein's masked program in closed form.** -/
def kmF (B nD n k t : ℕ) (j : ℕ) : ℕ :=
  (kmCo.getD j (0, 0, 0, 0, 0, 0)).1 * t + (kmCo.getD j (0, 0, 0, 0, 0, 0)).2.1 * k +
    (kmCo.getD j (0, 0, 0, 0, 0, 0)).2.2.1 * n + (kmCo.getD j (0, 0, 0, 0, 0, 0)).2.2.2.1 * nD +
    (kmCo.getD j (0, 0, 0, 0, 0, 0)).2.2.2.2.1 * B + (kmCo.getD j (0, 0, 0, 0, 0, 0)).2.2.2.2.2

set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
/-- **The closed forms are the constants of the program.** -/
theorem kmV_eq (B nD n k t : ℕ) {j : ℕ} (hj : j < 43) : kmV B nD n k t j = kmF B nD n k t j := by
  simp only [kmF]
  interval_cases j <;>
    simp only [kmV, kmPaths, kmCo, List.getD_cons_succ, List.getD_cons_zero] <;>
    hs_eval <;> km_fin

/-! ### The parameters on the machine -/

/-- **The 48 parameters of `kNFM` as linear forms** in the primary registers `7300 … 7307`
(`B`, `nD`, `n`, `k`, `t`, `Hc`, `β`, `len`). -/
def kPrmL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 7302)], 0),
    ([(1, hpM.v 7300)], 0),
    ([(1, hpM.v 7300), (1, hpM.one)], 0),
    ([(1, hpM.v 7300), (2, hpM.one)], 0),
    ([(1, hpM.v 7300), (3, hpM.one)], 0),
    ([(1, hpM.v 7300), (4, hpM.one)], 0),
    ([(1, hpM.v 7300), (5, hpM.one)], 0),
    ([(1, hpM.v 7300), (6, hpM.one)], 0),
    ([(1, hpM.v 7300), (7, hpM.one)], 0),
    ([(1, hpM.v 7300), (8, hpM.one)], 0),
    ([(1, hpM.v 7300), (9, hpM.one)], 0),
    ([(1, hpM.v 7300), (10, hpM.one)], 0),
    ([(1, hpM.v 7300), (11, hpM.one)], 0),
    ([(1, hpM.v 7300), (12, hpM.one)], 0),
    ([(1, hpM.v 7300), (13, hpM.one)], 0),
    ([(1, hpM.v 7300), (14, hpM.one)], 0),
    ([(1, hpM.v 7300), (15, hpM.one)], 0),
    ([(1, hpM.v 7303), (7, hpM.v 7302), (9, hpM.v 7301)], 0),
    ([(1, hpM.v 7303), (3, hpM.v 7302), (9, hpM.v 7301)], 0),
    ([(1, hpM.v 7303), (7, hpM.v 7302), (9, hpM.v 7301), (1, hpM.one)], 0),
    ([(1, hpM.v 7303), (4, hpM.v 7302), (9, hpM.v 7301)], 0),
    ([(3, hpM.v 7301)], 0),
    ([(1, hpM.v 7301)], 0),
    ([(4, hpM.v 7301)], 0),
    ([(5, hpM.v 7301)], 0),
    ([(2, hpM.v 7301)], 0),
    ([(3, hpM.v 7301), (2, hpM.one)], 0),
    ([(1, hpM.v 7303), (7, hpM.v 7302), (9, hpM.v 7301), (2, hpM.one)], 0),
    ([(1, hpM.v 7303), (5, hpM.v 7302), (9, hpM.v 7301)], 0),
    ([(1, hpM.v 7303), (7, hpM.v 7302), (9, hpM.v 7301), (3, hpM.one)], 0),
    ([(1, hpM.v 7303), (6, hpM.v 7302), (9, hpM.v 7301)], 0),
    ([(1, hpM.v 7303)], 0),
    ([(1, hpM.v 7302), (8, hpM.v 7301)], 0),
    ([(1, hpM.v 7304)], 0),
    ([(3, hpM.v 7301), (3, hpM.one)], 0),
    ([(1, hpM.v 7303), (1, hpM.v 7302)], 0),
    ([(1, hpM.v 7303), (7, hpM.v 7302), (9, hpM.v 7301), (4, hpM.one)], 0),
    ([(1, hpM.v 7304), (1, hpM.v 7303), (7, hpM.v 7302), (9, hpM.v 7301), (4, hpM.one)], 0),
    ([(3, hpM.v 7301), (1, hpM.one)], 0),
    ([(8, hpM.v 7301)], 0),
    ([(1, hpM.v 7303), (1, hpM.v 7302), (8, hpM.v 7301)], 0),
    ([(1, hpM.v 7303), (2, hpM.v 7302), (8, hpM.v 7301)], 0),
    ([(1, hpM.v 7303), (3, hpM.v 7302), (8, hpM.v 7301)], 0),
    ([(2, hpM.v 7305), (1, hpM.one)], 0),
    ([(1, hpM.v 7305)], 0),
    ([(1, hpM.v 7300), (16, hpM.v 7302), (17, hpM.one)], 0),
    ([(1, hpM.v 7306)], 0),
    ([(1, hpM.v 7307)], 0)]

theorem kPrmL_length : kPrmL.length = 48 := rfl

theorem kPrm_shape : hpShape 7300 7308 17 0 kPrmL = true := by decide

/-- **The parameter program of Klein's MSSP** (into `r1000 … r1047`, scratch `r7310`, `r7311`). -/
def kPrm : Stmt := hpProg 1000 7310 kPrmL

theorem kPrm_natOnly : Klein.natOnly kPrm = true := by kernel_rfl

/-- The primary values. -/
structure KPrim (f : ℕ → ℕ) (B nD n k t Hc β len : ℕ) : Prop where
  r0 : f 7300 = B
  r1 : f 7301 = nD
  r2 : f 7302 = n
  r3 : f 7303 = k
  r4 : f 7304 = t
  r5 : f 7305 = Hc
  r6 : f 7306 = β
  r7 : f 7307 = len

theorem kPrm_val {f : ℕ → ℕ} {B nD n k t Hc β len : ℕ} (h : KPrim f B nD n k t Hc β len) {j : ℕ}
    (hj : j < 48) : hpSum f (kPrmL.getD j ([], 0)).1 - (kPrmL.getD j ([], 0)).2 =
      knVM B nD n k t Hc β len j := by
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := h
  by_cases h43 : j < 43
  · have e : knVM B nD n k t Hc β len j = kmF B nD n k t j := by
      simp only [knVM, knV, show j < 46 by omega, h43, ↓reduceIte]; exact kmV_eq B nD n k t h43
    rw [e]
    interval_cases j <;>
      simp only [kPrmL, kmF, kmCo, hpSum, hpM.ev, List.getD_cons_succ, List.getD_cons_zero,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r0, r1, r2, r3, r4] <;> omega
  · interval_cases j <;>
      simp only [kPrmL, knVM, knV, hpSum, hpM.ev, List.getD_cons_succ, List.getD_cons_zero,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r0, r2, r5, r6, r7] <;>
      simp <;> omega

/-- **The parameters of `kNFM` on the machine**: from the primary registers, `kPrm` writes
`r1000 + j = knVM B nD n k t Hc β len j` for every `j < 48` within `hpCost kPrmL` steps. -/
theorem kPrm_exec {I : Input} {W : ℕ} {B nD n k t Hc β len : ℕ} (c : Config)
    (hc : WordsBounded W c) (hP : KPrim c.nreg B nD n k t Hc β len)
    (hW : t + k + 16 * n + 9 * nD + B + 2 * Hc + β + len + 20 ≤ W) :
    ∃ c', Exec I W kPrm c c' (hpCost kPrmL) ∧
      (∀ j < 48, c'.nreg (1000 + j) = knVM B nD n k t Hc β len j) ∧
      (∀ r, (r < 1000 ∨ 1048 ≤ r) → r ≠ 7310 → r ≠ 7311 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 1000 7310 kPrmL :=
    hpShape_ok kPrm_shape (by omega) (by omega) (by simp [kPrmL_length]) (by omega)
      (by simp [kPrmL_length])
  obtain ⟨c', e, v, f, m, r, rm, o⟩ := hpProg_exec (I := I) kPrmL 1000 hok c hc (fun e he => by
    obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := hP
    simp only [kPrmL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r0, r1,
        r2, r3, r4, r5, r6, r7] <;> omega)
  refine ⟨c', e, fun j hj => ?_, fun r h1 h2 h3 => f r (by rw [kPrmL_length]; omega) h2 h3, m,
    r, rm, o⟩
  rw [v j (by rw [kPrmL_length]; exact hj)]
  exact kPrm_val hP hj

end MsEnc

end BKMNW

end PlanarFlow
