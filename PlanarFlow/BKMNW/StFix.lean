module

public import PlanarFlow.STFlow.PstNat
public import PlanarFlow.BKMNW.KleinFix

/-!
# The natural s-t flow program as one fixed program, input in memory, logged run

`STFlow.pstflowW_exec_nat` runs `constsS 201 M H β ; toNat 201 M (pstProg B nD n)` (`M = pstM H`),
whose text depends on the instance (the layout constants of `pstProg`, the constants of the
simulation, and the residue `M - 1` of the real constant `-1` of `pstProg`). Constant hoisting
(`PlanarFlow/NegSSSP/Enc/HoistGen.lean`, as `KleinFix.lean`):

* `resC`, `trIC`, `toNatC` (the residues of the real constants `0`, `1`, `-1` written as `0`, `1`,
  `M - 1`), **`toNatC_eq`** (`toNatC R M s = toNat R M s` for `2 ≤ M`);
* markers `ssB`, `ssND`, `ssN` (`10⁹ + 7`, `10¹² + 39`, `10¹⁵ + 37`), `ssM` (`10³⁰ + 1`), `ssTbl`
  (the 39 instance-dependent constants of `pstProg`), `ssPaths`, `ssV` (`hsAt`), **`ssT`**
  `= hsHoist 1000 ssTbl (pstProg markers)`, **`ssT_eq`**;
* **`sNT`** `= hsHoist 1000 [(ssM - 1, 39)] (toNatC 201 ssM ssT)`, `sVN` (43 parameters: `ssV`,
  `M - 1`, `M`, `H`, `β`), **`sNF`** `= (r402 := r1040; r403 := r1041; r404 := r1042) ; sNT`,
  **`sNF_un`** (`hsUn 1000 (sVN …) sNF = constsS 201 (pstM H) H β ; toNat 201 (pstM H) (pstProg …)`
  for `1 ≤ H`), `sNF_exec`;
* **`sNFM`** (input in memory: base `r1043`, size `r1044`, scratch `r999`), `sVM`, `sNFM_noInp`,
  `sNFM_natOnly`, `sNFM_noRand`, `sNFM_regsOK` (`< 1045`), **`sNFM_exec`** (every run of the
  natural s-t flow program is realized by `sNFM` with the input words in memory, within three
  times the steps), **`sNFM_lgRun`** (the logged in-place run).
-/

@[expose] public section

namespace PlanarFlow

namespace BKMNW

namespace StFix

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt NegSSSP

/-! ### Residues of the small real constants -/

/-- The residue of a real constant, the constants `0`, `1`, `-1` written out. -/
def resC (M : ℕ) (z : ℤ) : ℕ :=
  if z = 0 then 0 else if z = 1 then 1 else if z = -1 then M - 1 else (z % (M : ℤ)).toNat

theorem resC_eq {M : ℕ} (hM : 2 ≤ M) (z : ℤ) : resC M z = (z % (M : ℤ)).toNat := by
  unfold resC
  split_ifs with h0 h1 h2
  · subst h0; simp
  · subst h1
    rw [Int.emod_eq_of_lt (by norm_num) (by omega)]; rfl
  · subst h2
    have h : (-1 : ℤ) = ((M : ℤ) - 1) + M * (-1) := by ring
    rw [h, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
    omega
  · rfl

/-- `trI` with `resC`. -/
def trIC (R M : ℕ) : Instr → Stmt
  | .constR r z => .instr (.constN (R + r) (resC M z))
  | i => ModNat.trI R M i

theorem trIC_eq {R M : ℕ} (hM : 2 ≤ M) (i : Instr) : trIC R M i = ModNat.trI R M i := by
  cases i <;> simp [trIC, ModNat.trI, resC_eq hM]

/-- `toNat` with `trIC`. -/
def toNatC (R M : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .instr i => trIC R M i
  | .seq s t => .seq (toNatC R M s) (toNatC R M t)
  | .ifLtN a b t e => .ifLtN a b (toNatC R M t) (toNatC R M e)
  | .ifLtR a b t e => .seq (ModNat.cmpS R a b)
      (.ifLtN (2 * R + 1) (2 * R + 3) (toNatC R M t) (toNatC R M e))
  | .whileLtN a b body => .whileLtN a b (toNatC R M body)
  | .whileLtR a b body => .seq (ModNat.cmpS R a b)
      (.whileLtN (2 * R + 1) (2 * R + 3) (.seq (toNatC R M body) (ModNat.cmpS R a b)))

theorem toNatC_eq {R M : ℕ} (hM : 2 ≤ M) : ∀ s : Stmt, toNatC R M s = ModNat.toNat R M s
  | .skip => rfl
  | .instr i => trIC_eq hM i
  | .seq s t => by simp only [toNatC, ModNat.toNat, toNatC_eq hM s, toNatC_eq hM t]
  | .ifLtN a b t e => by simp only [toNatC, ModNat.toNat, toNatC_eq hM t, toNatC_eq hM e]
  | .ifLtR a b t e => by simp only [toNatC, ModNat.toNat, toNatC_eq hM t, toNatC_eq hM e]
  | .whileLtN a b body => by simp only [toNatC, ModNat.toNat, toNatC_eq hM body]
  | .whileLtR a b body => by simp only [toNatC, ModNat.toNat, toNatC_eq hM body]

/-! ### The hoisting -/

def ssB : ℕ := 1000000007
def ssND : ℕ := 1000000000039
def ssN : ℕ := 1000000000000037
def ssM : ℕ := 1000000000000000000000000000001

/-- The instance-dependent constants of the marker program and their parameter numbers. -/
def ssTbl : List (ℕ × ℕ) := [(1000000000000037, 0), (1000000007, 1), (1000000008, 2), (1000000009, 3), (1000000010, 4), (1000000011, 5), (1000000012, 6), (1000000013, 7), (1000000014, 8), (1000000015, 9), (1000000016, 10), (1000000017, 11), (1000000018, 12), (1000000019, 13), (1000000020, 14), (1000000021, 15), (1000000022, 16), (7009000000000612, 17), (3009000000000464, 18), (7009000000000613, 19), (4009000000000501, 20), (3000000000117, 21), (1000000000039, 22), (4000000000156, 23), (5000000000195, 24), (2000000000078, 25), (3000000000119, 26), (7009000000000614, 27), (5009000000000538, 28), (7009000000000615, 29), (6009000000000575, 30), (1008000000000349, 31), (1008000000000350, 32), (3000000000118, 33), (8000000000312, 34), (3000000000120, 35), (5000000000198, 36), (4000000000159, 37), (6000000000237, 38)]

/-- A path to an occurrence of each instance-dependent constant. -/
def ssPaths : List (List Bool) :=
  [[false],
    [true, false, true, false, false, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, true, false, false, false, true, true, false],
    [true, true, false, false, true, false, false, false, false],
    [true, true, false, false, true, true, false, true, false],
    [true, true, false, false, true, true, true, false, false, false, false],
    [true, true, false, false, true, true, true, false, false, false, true, true, true, false],
    [true, true, false, false, true, true, true, false, false, false, true, true, true, true, true, true, true, true, true, false],
    [true, true, false, false, true, true, true, true, true, false, false, true, true, true, true, true, true, true, true, true, false],
    [true, true, false, true, false, true, false, true, true, true, false],
    [true, true, false, true, true, false, true, false, true, true, true, true, true, true, true, true, true, true, false],
    [true, true, false, true, true, true, false, false],
    [true, true, false, true, true, true, false, true, true, true, false],
    [true, true, false, true, true, true, true, false, false, false, false],
    [true, true, false, true, true, true, true, true, false, true, false],
    [true, true, false, true, true, true, true, true, true, false, false, false, false],
    [true, true, true, false, false],
    [true, true, true, false, true, true, true, true, true, false],
    [true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, true, true, true, false, false, true, false, false, true, true, false],
    [true, true, true, true, true, false, true, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, true, true, true, true, true, true, false, true, false, true, true, false],
    [true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, false],
    [true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false]]

/-- The parameters of the instance: the constant at the `j`-th path. -/
def ssV (B nD n : ℕ) (j : ℕ) : ℕ := hsAt (STFlow.pstProg B nD n) (ssPaths.getD j [])

/-- The s-t flow program with its layout constants hoisted. -/
def ssT : Stmt := hsHoist 1000 ssTbl (STFlow.pstProg ssB ssND ssN)

theorem ssT_eq (B nD n : ℕ) : hsUn 1000 (ssV B nD n) ssT = STFlow.pstProg B nD n := by
  kernel_rfl

/-- On natural words, the residue `M - 1` hoisted too. -/
def sNT : Stmt := hsHoist 1000 [(ssM - 1, 39)] (toNatC 201 ssM ssT)

/-- The parameters of the natural program. -/
def sVN (B nD n H β : ℕ) (j : ℕ) : ℕ :=
  if j < 39 then ssV B nD n j else if j = 39 then STFlow.pstM H - 1
  else if j = 40 then STFlow.pstM H else if j = 41 then H else β

theorem sNT_eq (B nD n H β : ℕ) :
    hsUn 1000 (sVN B nD n H β) sNT = toNatC 201 (STFlow.pstM H) (STFlow.pstProg B nD n) := by
  kernel_rfl

/-- **The natural s-t flow program as one fixed program.** -/
def sNF : Stmt := .seq (block [.copyN 402 1040, .copyN 403 1041, .copyN 404 1042]) sNT

theorem sNF_ok : hsOK 1000 43 sNF = true := by decide +kernel

theorem sNF_head (B nD n H β : ℕ) :
    hsUn 1000 (sVN B nD n H β) (block [.copyN 402 1040, .copyN 403 1041, .copyN 404 1042]) =
      ModNat.constsS 201 (STFlow.pstM H) H β := by
  kernel_rfl

theorem sNF_un (B nD n H β : ℕ) (hH : 1 ≤ H) :
    hsUn 1000 (sVN B nD n H β) sNF = .seq (ModNat.constsS 201 (STFlow.pstM H) H β)
      (ModNat.toNat 201 (STFlow.pstM H) (STFlow.pstProg B nD n)) := by
  show Stmt.seq _ _ = _
  rw [sNF_head, sNT_eq, toNatC_eq (by unfold STFlow.pstM; omega)]

/-- **Every run of the natural s-t flow program is a run of `sNF`** from a configuration holding
the parameters `sVN` at `1000 … 1042`. -/
theorem sNF_exec {P : Input} {W : ℕ} {B nD n H β : ℕ} {c c' : Config} {s : ℕ}
    (h : Exec P W (.seq (ModNat.constsS 201 (STFlow.pstM H) H β)
      (ModNat.toNat 201 (STFlow.pstM H) (STFlow.pstProg B nD n))) c c' s) (hH : 1 ≤ H)
    (hv : ∀ j < 43, c.nreg (1000 + j) = sVN B nD n H β j) :
    Exec P W sNF c c' s ∧ ∀ a, 1000 ≤ a → c'.nreg a = c.nreg a := by
  rw [← sNF_un B nD n H β hH] at h
  exact hs_exec h sNF_ok hv

/-! ### The input read from memory -/

def ssIB : ℕ := 1000000000000000000000000000000007
def ssIL : ℕ := 1000000000000000000000000000000000009

/-- **The natural s-t flow program, input in memory, as one fixed program** (input base `r1043`,
input size `r1044`, scratch `r999`). -/
def sNFM : Stmt := hsHoist 1000 [(ssIB, 43), (ssIL, 44)] (Stmt.toMem 999 ssIB ssIL sNF)

/-- The parameters of `sNFM`. -/
def sVM (B nD n H β ib len : ℕ) (j : ℕ) : ℕ :=
  if j < 43 then sVN B nD n H β j else if j = 43 then ib else len

theorem sNFM_eq (v : ℕ → ℕ) :
    hsUn 1000 v sNFM = Stmt.toMem 999 (v 43) (v 44) (hsUn 1000 v sNF) := by
  kernel_rfl

theorem sNF_unM (B nD n H β ib len : ℕ) :
    hsUn 1000 (sVM B nD n H β ib len) sNF = hsUn 1000 (sVN B nD n H β) sNF := by
  kernel_rfl

theorem sNFM_ok : hsOK 1000 45 sNFM = true := by decide +kernel

theorem sNFM_natOnly : Klein.natOnly sNFM = true := by decide +kernel

theorem sNFM_noInp : sNFM.noInp = true := by decide +kernel

theorem sNFM_noRand : sNFM.noRand = true := by decide +kernel

theorem sNFM_regsOK : sNFM.regsOK (fun r => decide (r < 1045)) = true := by decide +kernel

theorem sNF_regs (v : ℕ → ℕ) : (hsUn 1000 v sNF).regsOK (fun r => decide (r < 406)) = true := by
  kernel_rfl

theorem sNF_noRandU (v : ℕ → ℕ) : (hsUn 1000 v sNF).noRand = true := by
  kernel_rfl

theorem sNFM_un (B nD n H β ib len : ℕ) (hH : 1 ≤ H) :
    hsUn 1000 (sVM B nD n H β ib len) sNFM =
      Stmt.toMem 999 ib len (.seq (ModNat.constsS 201 (STFlow.pstM H) H β)
        (ModNat.toNat 201 (STFlow.pstM H) (STFlow.pstProg B nD n))) := by
  rw [sNFM_eq, sNF_unM, sNF_un B nD n H β hH]
  rfl

/-- **Every run of the natural s-t flow program is realized by the fixed `sNFM` with its input in
memory** (`Exec.embed`, `hs_exec`), within three times the steps. -/
theorem sNFM_exec {P P' : Input} {W W' : ℕ} {B nD n H β ib : ℕ} {c c' : Config} {s : ℕ}
    (h : Exec P W (.seq (ModNat.constsS 201 (STFlow.pstM H) H β)
      (ModNat.toNat 201 (STFlow.pstM H) (STFlow.pstProg B nD n))) c c' s) (hH : 1 ≤ H)
    (hW : W ≤ W') (d : Config) (hA : Agree (fun r => decide (r < 406)) W c d)
    (hd : WordsBounded W' d) (hI : InData P W ib P.data.length W' d)
    (hv : ∀ j < 45, d.nreg (1000 + j) = sVM B nD n H β ib P.data.length j) :
    ∃ d' s', Exec P' W' sNFM d d' s' ∧ s' ≤ 3 * s ∧
      Agree (fun r => decide (r < 406)) W c' d' ∧
      (∀ r, 406 ≤ r → r ≠ 999 → d'.nreg r = d.nreg r) ∧
      (∀ r, 406 ≤ r → d'.rreg r = d.rreg r) ∧
      (∀ a, W < a → d'.nmem a = d.nmem a) ∧ (∀ a, W < a → d'.rmem a = d.rmem a) ∧
      ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  have hs : (Stmt.seq (ModNat.constsS 201 (STFlow.pstM H) H β)
      (ModNat.toNat 201 (STFlow.pstM H) (STFlow.pstProg B nD n))).regsOK
        (fun r => decide (r < 406)) = true := by
    rw [← sNF_un B nD n H β hH]; exact sNF_regs _
  have hr : (Stmt.seq (ModNat.constsS 201 (STFlow.pstM H) H β)
      (ModNat.toNat 201 (STFlow.pstM H) (STFlow.pstProg B nD n))).noRand = true := by
    rw [← sNF_un B nD n H β hH]; exact sNF_noRandU _
  obtain ⟨d', s', e, -, hs3, -, hA', hK, L, o1, o2⟩ :=
    Exec.embed (P' := P') (tmp := 999) (β := ib) (len := P.data.length) h hs hW (Or.inl hr) d hA
      hd (Or.inr ⟨hI, by decide⟩)
  rw [← sNFM_un B nD n H β ib P.data.length hH] at e
  obtain ⟨e', -⟩ := hs_exec e sNFM_ok hv
  refine ⟨d', s', e', hs3, hA', fun r h1 h2 => ?_, fun r h1 => hK.rreg r (by simp; omega),
    hK.nmem, hK.rmem, L, o1, o2⟩
  exact hK.nreg r (by simp; omega) (fun e => absurd e h2)

/-- **The logged in-place run of the fixed natural s-t flow program** (`lg_liftNat`). -/
theorem sNFM_lgRun {P P' : Input} {Ws W : ℕ} {d d' : Config} {s : ℕ}
    (h : Exec P Ws sNFM d d' s) {LP ONE : ℕ} (hLP : 1045 ≤ LP) (hONE : 1045 ≤ ONE)
    (hne : LP ≠ ONE) (hWs : Ws ≤ W) (e : Config) (hA : ∀ r < 1045, e.nreg r = d.nreg r)
    (hm : ∀ a ≤ Ws, e.nmem a = d.nmem a) (he : WordsBounded W e) (h1 : e.nreg ONE = 1)
    (hp : Ws < e.nreg LP) (hpW : e.nreg LP + s ≤ W) :
    ∃ e' s' j, Exec P' W (NegSSSP.lgS LP ONE sNFM) e e' s' ∧ s' ≤ 3 * s ∧ j ≤ s ∧
      (∀ r < 1045, e'.nreg r = d'.nreg r) ∧ (∀ a ≤ Ws, e'.nmem a = d'.nmem a) ∧
      NegSSSP.LgKeep (fun r => decide (r < 1045)) Ws LP (e.nreg LP) j e e' ∧
      e'.rreg = e.rreg ∧ e'.rmem = e.rmem ∧
      ∃ L, d'.output = d.output ++ L ∧ e'.output = e.output ++ L := by
  obtain ⟨e', s', j, ex, hk, hj, hA', hm', hK, hr, hrm, L, o1, o2⟩ :=
    MfDrv.lg_liftNat (P' := P') h sNFM_regsOK sNFM_noInp sNFM_noRand sNFM_natOnly
      (by simp; omega) (by simp; omega) hne hWs e (fun r hr => hA r (by simpa using hr)) hm he h1
      hp hpW
  exact ⟨e', s', j, ex, hk, hj, fun r hr => hA' r (by simpa using hr), hm', hK, hr, hrm, L, o1, o2⟩

end StFix

end BKMNW

end PlanarFlow
