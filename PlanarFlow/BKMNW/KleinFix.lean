module

public import PlanarFlow.Klein.ExecNat
public import PlanarFlow.NegSSSP.Enc.HoistGen
public import PlanarFlow.BKMNW.LgNat

/-!
# Klein's masked MSSP as one fixed program (constant hoisting)

Constant hoisting (`PlanarFlow/NegSSSP/Enc/HoistGen.lean`) applied to `Klein.kleinProgM B nD n k t`
at the marker instance `kmB … kmT` (`10⁹ + 7`, `10¹² + 39`, `10¹⁵ + 37`, `10¹⁸ + 3`, `10²¹ + 117`;
every instance-dependent constant is then `> 10⁹`, every fixed one `≤ 52`):

* `kmTbl`: the 43 instance-dependent constants of the marker program and their parameter numbers;
  `kmPaths`: a path to an occurrence of each; **`kmV B nD n k t j`** = the constant of
  `kleinProgM B nD n k t` at the `j`-th path (`hsAt`);
* **`kmFixT`** `= hsHoist 1000 kmTbl (kleinProgM kmB kmND kmN kmK kmT)`: one statement;
* **`kmFixT_eq`** (kernel-checked): `hsUn 1000 (kmV B nD n k t) kmFixT = kleinProgM B nD n k t`
  for **all** `B nD n k t`;
* on natural words: `knT = toNat 201 2 kmFixT`, **`kNF`** (the simulation constants `M`, `H`, `β`
  from `r1043 … r1045`, then `knT`), parameters `knV` (`46`), **`kNF_un`**
  (`hsUn 1000 (knV …) kNF = kleinProgMN B nD n k t Hc` for `1 ≤ Hc`; the real constants `0`, `1` of
  Klein's program make the modulus irrelevant, `hs_toNat`), **`kNF_exec`**;
* the input read from memory: **`kNFM`** (`Stmt.toMem 999 β len kNF` with `β`, `len` hoisted to
  `r1046`, `r1047`), `knVM` (`48` parameters), `kNFM_natOnly`, **`kNFM_noInp`**, `kNFM_noRand`,
  `kNFM_regsOK` (registers `< 1048`), **`kNFM_un`**, **`kNFM_exec`** (every run of `kleinProgMN`
  on an input `P` is realized by `kNFM` from a configuration holding the input words in memory,
  `InData`, within three times the steps, `Exec.embed` + `hs_exec`), **`kNFM_lgRun`** (the logged
  in-place run, `lg_liftNat`).

All the equations are checked by the kernel on the whole program (about `7 · 10⁶` statement
nodes, shared), in seconds.
-/

@[expose] public section

namespace PlanarFlow

namespace BKMNW

namespace KleinFix

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt NegSSSP

/-- The markers. -/
def kmB : ℕ := 1000000007
def kmND : ℕ := 1000000000039
def kmN : ℕ := 1000000000000037
def kmK : ℕ := 1000000000000000003
def kmT : ℕ := 1000000000000000000117

/-- The instance-dependent constants of the marker program and their parameter numbers. -/
def kmTbl : List (ℕ × ℕ) := [(1000000000000037, 0), (1000000007, 1), (1000000008, 2), (1000000009, 3), (1000000010, 4), (1000000011, 5), (1000000012, 6), (1000000013, 7), (1000000014, 8), (1000000015, 9), (1000000016, 10), (1000000017, 11), (1000000018, 12), (1000000019, 13), (1000000020, 14), (1000000021, 15), (1000000022, 16), (1007009000000000613, 17), (1003009000000000465, 18), (1007009000000000614, 19), (1004009000000000502, 20), (3000000000117, 21), (1000000000039, 22), (4000000000156, 23), (5000000000195, 24), (2000000000078, 25), (3000000000119, 26), (1007009000000000615, 27), (1005009000000000539, 28), (1007009000000000616, 29), (1006009000000000576, 30), (1000000000000000003, 31), (1008000000000349, 32), (1000000000000000000117, 33), (3000000000120, 34), (1001000000000000040, 35), (1007009000000000617, 36), (1001007009000000000734, 37), (3000000000118, 38), (8000000000312, 39), (1001008000000000352, 40), (1002008000000000389, 41), (1003008000000000426, 42)]

/-- A path to an occurrence of each instance-dependent constant. -/
def kmPaths : List (List Bool) :=
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
    [true, true, true, false, true, false],
    [true, true, true, false, true, true, false],
    [true, true, true, true, false, false, true, true, true, true, false],
    [true, true, true, true, false, false, true, true, true, true, true, true, false],
    [true, true, true, true, false, false, true, true, true, true, true, true, true, true, false],
    [true, true, true, true, false, true, false, false, false, false, false, false],
    [true, true, true, true, false, true, false, false, false, false, true, true, true, false],
    [true, true, true, true, false, true, true, false, false],
    [true, true, true, true, false, true, true, true, false, false, true, true, false, false, false, true, true, false],
    [true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true, false],
    [true, true, true, true, false, true, true, true, true, false, true, false, true, true, true, true, true, true, true, true, true, false],
    [true, true, true, true, false, true, true, true, true, false, true, true, false, false, false, false]]

/-- **The parameters of the instance**: the constant at the `j`-th path. -/
def kmV (B nD n k t : ℕ) (j : ℕ) : ℕ := hsAt (Klein.kleinProgM B nD n k t) (kmPaths.getD j [])

/-- **Klein's masked program with its constants hoisted.** -/
def kmFixT : Stmt := hsHoist 1000 kmTbl (Klein.kleinProgM kmB kmND kmN kmK kmT)

/-- **The hoisted program with the parameters put back is the instance program.** -/
theorem kmFixT_eq (B nD n k t : ℕ) :
    hsUn 1000 (kmV B nD n k t) kmFixT = Klein.kleinProgM B nD n k t := by
  kernel_rfl

/-! ### On natural words -/

/-- The hoisted program on natural words (the modulus `2` of its real constants `0`, `1`). -/
def knT : Stmt := ModNat.toNat 201 2 kmFixT

/-- The parameters of the natural program: those of `kleinProgM`, then the constants of the
simulation `M = 2 Hc + 1`, `Hc`, `β = B + 16 (n + 1) + 1` (`kleinProgMN`). -/
def knV (B nD n k t Hc : ℕ) (j : ℕ) : ℕ :=
  if j < 43 then kmV B nD n k t j else if j = 43 then 2 * Hc + 1 else if j = 44 then Hc
  else B + 16 * (n + 1) + 1

/-- **Klein's masked MSSP on natural words as one fixed program**: the constants of the
simulation from `r1043 … r1045`, then `knT`. -/
def kNF : Stmt := .seq (block [.copyN 402 1043, .copyN 403 1044, .copyN 404 1045]) knT

theorem knFixT_eq (B nD n k t Hc : ℕ) :
    hsUn 1000 (knV B nD n k t Hc) kmFixT = Klein.kleinProgM B nD n k t := by
  kernel_rfl

theorem knT_eq (v : ℕ → ℕ) : hsUn 1000 v knT = ModNat.toNat 201 2 (hsUn 1000 v kmFixT) := by
  kernel_rfl

theorem kmFixT_cr (v : ℕ → ℕ) : hsCR 2 (hsUn 1000 v kmFixT) = true := by
  kernel_rfl

theorem kNF_ok : hsOK 1000 46 kNF = true := by decide +kernel

theorem kNF_natOnly : Klein.natOnly kNF = true := by decide +kernel

theorem kNF_noRand : kNF.noRand = true := by decide +kernel

theorem kNF_head (B nD n k t Hc : ℕ) :
    hsUn 1000 (knV B nD n k t Hc) (block [.copyN 402 1043, .copyN 403 1044, .copyN 404 1045]) =
      ModNat.constsS 201 (2 * Hc + 1) Hc (B + 16 * (n + 1) + 1) := by
  kernel_rfl

/-- **The fixed program with the parameters put back is `kleinProgMN`.** -/
theorem kNF_un (B nD n k t Hc : ℕ) (hHc : 1 ≤ Hc) :
    hsUn 1000 (knV B nD n k t Hc) kNF = Klein.kleinProgMN B nD n k t Hc := by
  have h1 : hsUn 1000 (knV B nD n k t Hc) knT =
      ModNat.toNat 201 (2 * Hc + 1) (Klein.kleinProgM B nD n k t) := by
    rw [knT_eq, knFixT_eq]
    have hcr := kmFixT_cr (knV B nD n k t Hc)
    rw [knFixT_eq] at hcr
    exact hs_toNat _ hcr (by omega) (by omega)
  show Stmt.seq _ _ = _
  rw [kNF_head, h1]
  rfl

/-- **Every run of `kleinProgMN` is a run of the fixed `kNF`** from a configuration holding the
parameters `knV` at `1000 … 1045` (same configurations, same steps); it keeps the registers
`≥ 1000`. -/
theorem kNF_exec {P : Input} {W : ℕ} {B nD n k t Hc : ℕ} {c c' : Config} {s : ℕ}
    (h : Exec P W (Klein.kleinProgMN B nD n k t Hc) c c' s) (hHc : 1 ≤ Hc)
    (hv : ∀ j < 46, c.nreg (1000 + j) = knV B nD n k t Hc j) :
    Exec P W kNF c c' s ∧ ∀ a, 1000 ≤ a → c'.nreg a = c.nreg a := by
  rw [← kNF_un B nD n k t Hc hHc] at h
  exact hs_exec h kNF_ok hv

/-! ### The input read from memory -/

/-- The markers of the input base and the input size. -/
def kmIB : ℕ := 1000000000000000000000007
def kmIL : ℕ := 1000000000000000000000000009

/-- **Klein's masked MSSP on natural words, input in memory, as one fixed program**: `kNF` with
every `readIn r a` read from the memory at the base `r1046` (`tmp = r999`) and `inputSize` from
`r1047`. -/
def kNFM : Stmt := hsHoist 1000 [(kmIB, 46), (kmIL, 47)] (Stmt.toMem 999 kmIB kmIL kNF)

/-- The parameters of `kNFM`: those of `kNF`, the input base `β`, the input size `len`. -/
def knVM (B nD n k t Hc β len : ℕ) (j : ℕ) : ℕ :=
  if j < 46 then knV B nD n k t Hc j else if j = 46 then β else len

theorem kNFM_eq (v : ℕ → ℕ) :
    hsUn 1000 v kNFM = Stmt.toMem 999 (v 46) (v 47) (hsUn 1000 v kNF) := by
  kernel_rfl

theorem kNF_unM (B nD n k t Hc β len : ℕ) :
    hsUn 1000 (knVM B nD n k t Hc β len) kNF = hsUn 1000 (knV B nD n k t Hc) kNF := by
  kernel_rfl

theorem kNFM_ok : hsOK 1000 48 kNFM = true := by decide +kernel

theorem kNFM_natOnly : Klein.natOnly kNFM = true := by decide +kernel

theorem kNFM_noInp : kNFM.noInp = true := by decide +kernel

theorem kNFM_noRand : kNFM.noRand = true := by decide +kernel

theorem kNFM_regsOK : kNFM.regsOK (fun r => decide (r < 1048)) = true := by decide +kernel

theorem kNF_regs (v : ℕ → ℕ) : (hsUn 1000 v kNF).regsOK (fun r => decide (r < 406)) = true := by
  kernel_rfl

theorem kNF_noRandU (v : ℕ → ℕ) : (hsUn 1000 v kNF).noRand = true := by
  kernel_rfl

/-- **The fixed program with the parameters put back is `kleinProgMN` with its input in
memory.** -/
theorem kNFM_un (B nD n k t Hc β len : ℕ) (hHc : 1 ≤ Hc) :
    hsUn 1000 (knVM B nD n k t Hc β len) kNFM =
      Stmt.toMem 999 β len (Klein.kleinProgMN B nD n k t Hc) := by
  rw [kNFM_eq, kNF_unM, kNF_un B nD n k t Hc hHc]
  rfl

/-- **Every run of `kleinProgMN` is realized by the fixed program `kNFM` with its input in
memory** (`Exec.embed`, `hs_exec`): from any `d` agreeing with the start on the registers `< 406`
and the memory `≤ W`, holding the input words at `β` (`InData`) and the parameters `knVM` at
`1000 … 1047`, within at most three times the steps, to a configuration agreeing with the end;
the registers `≥ 406` but `999` and the memory above `W` kept, the registers `≥ 1000` kept. -/
theorem kNFM_exec {P P' : Input} {W W' : ℕ} {B nD n k t Hc β : ℕ} {c c' : Config} {s : ℕ}
    (h : Exec P W (Klein.kleinProgMN B nD n k t Hc) c c' s) (hHc : 1 ≤ Hc) (hW : W ≤ W')
    (d : Config) (hA : Agree (fun r => decide (r < 406)) W c d) (hd : WordsBounded W' d)
    (hI : InData P W β P.data.length W' d)
    (hv : ∀ j < 48, d.nreg (1000 + j) = knVM B nD n k t Hc β P.data.length j) :
    ∃ d' s', Exec P' W' kNFM d d' s' ∧ s' ≤ 3 * s ∧
      Agree (fun r => decide (r < 406)) W c' d' ∧
      (∀ r, 406 ≤ r → r ≠ 999 → d'.nreg r = d.nreg r) ∧
      (∀ r, 406 ≤ r → d'.rreg r = d.rreg r) ∧
      (∀ a, W < a → d'.nmem a = d.nmem a) ∧ (∀ a, W < a → d'.rmem a = d.rmem a) ∧
      ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  have hs : (Klein.kleinProgMN B nD n k t Hc).regsOK (fun r => decide (r < 406)) = true := by
    rw [← kNF_un B nD n k t Hc hHc]; exact kNF_regs _
  have hr : (Klein.kleinProgMN B nD n k t Hc).noRand = true := by
    rw [← kNF_un B nD n k t Hc hHc]; exact kNF_noRandU _
  obtain ⟨d', s', e, -, hs3, -, hA', hK, L, o1, o2⟩ :=
    Exec.embed (P' := P') (tmp := 999) (β := β) (len := P.data.length) h hs hW (Or.inl hr) d hA hd
      (Or.inr ⟨hI, by decide⟩)
  rw [← kNFM_un B nD n k t Hc β P.data.length hHc] at e
  obtain ⟨e', -⟩ := hs_exec e kNFM_ok hv
  refine ⟨d', s', e', hs3, hA', fun r h1 h2 => ?_, fun r h1 => hK.rreg r (by simp; omega),
    hK.nmem, hK.rmem, L, o1, o2⟩
  exact hK.nreg r (by simp; omega) (fun e => absurd e h2)

/-- **The logged in-place run of the fixed natural MSSP** (`lg_liftNat`): `lgS LP ONE kNFM`
(`LP, ONE ≥ 1048`) from any `e` agreeing with the start of a run of `kNFM` on the registers
`< 1048` and the memory `≤ Ws`, within three times the steps: the same registers `< 1048` and
memory `≤ Ws` as the end of that run, the log of the stores above `Ws` (`LgKeep`, for `lgClr`),
reals kept. -/
theorem kNFM_lgRun {P P' : Input} {Ws W : ℕ} {d d' : Config} {s : ℕ}
    (h : Exec P Ws kNFM d d' s) {LP ONE : ℕ} (hLP : 1048 ≤ LP) (hONE : 1048 ≤ ONE)
    (hne : LP ≠ ONE) (hWs : Ws ≤ W) (e : Config) (hA : ∀ r < 1048, e.nreg r = d.nreg r)
    (hm : ∀ a ≤ Ws, e.nmem a = d.nmem a) (he : WordsBounded W e) (h1 : e.nreg ONE = 1)
    (hp : Ws < e.nreg LP) (hpW : e.nreg LP + s ≤ W) :
    ∃ e' s' j, Exec P' W (NegSSSP.lgS LP ONE kNFM) e e' s' ∧ s' ≤ 3 * s ∧ j ≤ s ∧
      (∀ r < 1048, e'.nreg r = d'.nreg r) ∧ (∀ a ≤ Ws, e'.nmem a = d'.nmem a) ∧
      NegSSSP.LgKeep (fun r => decide (r < 1048)) Ws LP (e.nreg LP) j e e' ∧
      e'.rreg = e.rreg ∧ e'.rmem = e.rmem ∧
      ∃ L, d'.output = d.output ++ L ∧ e'.output = e.output ++ L := by
  obtain ⟨e', s', j, ex, hk, hj, hA', hm', hK, hr, hrm, L, o1, o2⟩ :=
    MfDrv.lg_liftNat (P' := P') h kNFM_regsOK kNFM_noInp kNFM_noRand kNFM_natOnly
      (by simp; omega) (by simp; omega) hne hWs e (fun r hr => hA r (by simpa using hr)) hm he h1
      hp hpW
  exact ⟨e', s', j, ex, hk, hj, fun r hr => hA' r (by simpa using hr), hm', hK, hr, hrm, L, o1, o2⟩

end KleinFix

end BKMNW

end PlanarFlow
