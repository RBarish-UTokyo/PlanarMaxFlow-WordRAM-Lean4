module

public import PlanarFlow.BKMNW.StIsoM
public import PlanarFlow.NegSSSP.KEncCotAsm

/-!
# The initial trees of the s-t flow in its input (`Klein.KInit`) on the machine

The input of the s-t flow program (`STFlow.st_sNFM`) holds the depth orders of the initial dual
tree `T₀` (a tree of the faces of the piece map, from the parent words of Dijkstra's run,
`STFlow.stTree_of_par`) and of a cotree `C₀` of it rooted at the source `tail d₁`
(`Klein.KInit (pmap hP).dual σ ιF ιV n 2 (toDD T₀) C₀ vs ts fs cs P`). With the compact node
numbers of `cmProg` (`ιF = 1 + τv`, `ιV = ofF + τf`), the existing programs write them:

* `kiS1` (the registers of `toProg` for `T₀`: the parents at `PRb + 1 + τv y`, the faces of the
  darts from `NT`, the root `τv (face d₀) = NT[σ d₀] - 1`; the root's parent word set to `0`),
  `toProg` (`NegSSSP.toProg_orders` on `Q.dual`, `Q = M.dual`): `IV`, `IT`, `HD[0]`, `HD[1]`;
* `kiS2a`, `kiS2b` (the registers of `cotProg`, the root `τf (tail d₁) = NF[σ d₁] - ofF`),
  `cotProg` (`NegSSSP.cotProg_exec` on `Q`): **a cotree `C₀` of `toDD T₀` rooted at `tail d₁`**,
  `IF`, `IC`, `HD[2]`, `HD[3]`;
* **`kiProg`**, **`kiProg_exec`**: within `kiCost nD n nF nV` steps, the words of the orders at
  `IVb = ib + iIV nD n 2` …; **`kInit_of`**: any input whose words are the memory at `ib` meets
  `Klein.KInit Q σ (1 + τv) (ofF + τf) n 2 (toDD T₀) C₀ vs ts fs cs`.

Registers: natural `7980 … 7991` (inputs `nD`, `NTb`, `NFb`, `RVb`, `IVb`, `n`, `ofF`, `nF`,
`nV`, `PRb`, `Z`, `Gb`), `7992 … 7999` (scratch), and those of `toProg`, `cotProg`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

/-! ### The programs -/

/-- The registers of `toProg` for the tree `T₀` (scratch `Sb = Z`). -/
def kiS1 : Stmt := block [
  .constN 7992 1, .copyN 1600 7987, .addN 7993 7991 7992, .loadN 7993 7993,
  .addN 7993 7981 7993, .loadN 7993 7993, .subN 1601 7993 7992, .addN 1602 7989 7992,
  .copyN 1603 7981, .copyN 1604 7992, .copyN 1605 7990, .addN 1606 1605 7987,
  .addN 1607 1606 7987, .addN 1608 1607 7987, .addN 1608 1608 7992, .addN 1609 1608 7987,
  .addN 1610 1609 7987, .addN 1611 1610 7987, .addN 1612 1611 7987, .copyN 1613 7984,
  .addN 1614 7984 7985, .addN 1615 1614 7985, .addN 1615 1615 7985, .addN 1615 1615 7985,
  .addN 1615 1615 7992, .addN 1615 1615 7992, .addN 1615 1615 7992, .addN 1615 1615 7992,
  .addN 7994 1602 1601, .constN 7995 0, .storeN 7994 7995]

/-- The registers `1700 …`, `1500 …` of `cotProg` (scratch `Z₂ = Z + 8 nF + 1`). -/
def kiS2a : Stmt := block [
  .copyN 1700 7980, .addN 7996 1615 7992, .loadN 1701 7996, .copyN 1702 1614,
  .copyN 1703 7983, .copyN 1704 7982, .copyN 1705 7986, .addN 1706 1612 7987,
  .copyN 1500 7980, .copyN 1501 7988, .addN 1502 1706 7980, .copyN 1504 1706,
  .addN 1505 1502 7980, .addN 1505 1505 7980, .addN 1506 1505 7988, .addN 1506 1506 7992,
  .addN 1507 1506 7988, .addN 1508 1507 7988, .addN 1509 1508 7988]

/-- The registers `1400 …`, `1600 …` of `cotProg`. -/
def kiS2b : Stmt := block [
  .copyN 1400 7988, .loadN 7997 7991, .addN 7997 7982 7997, .loadN 7997 7997,
  .subN 1401 7997 7986, .copyN 1402 1507, .copyN 1403 1508, .copyN 1404 1509,
  .addN 1405 1502 7980, .addN 1406 1509 7980, .addN 1407 1406 7988, .addN 1408 1407 7988,
  .copyN 1600 7988, .copyN 1601 1401, .copyN 1602 1408, .copyN 1603 7982, .copyN 1604 7986,
  .addN 1605 1408 7988, .addN 1606 1605 7988, .addN 1607 1606 7988, .addN 1608 1607 7988,
  .addN 1608 1608 7992, .addN 1609 1608 7988, .addN 1610 1609 7988, .addN 1611 1610 7988,
  .addN 1612 1611 7988, .addN 1613 1702 7985, .addN 1614 1613 7985, .addN 1615 1614 7985,
  .addN 1615 1615 7992, .addN 1615 1615 7992]

/-- The two lengths of the orders of `T₀` copied from `IVb + 4n + 4` to `IVb + 4n` (`cotProg`
may change the words between its outputs). -/
def kiCp : Stmt := block [
  .addN 7998 7984 7985, .addN 7998 7998 7985, .addN 7998 7998 7985, .addN 7998 7998 7985,
  .addN 7999 7998 7992, .addN 7999 7999 7992, .addN 7999 7999 7992, .addN 7999 7999 7992,
  .loadN 7997 7999, .storeN 7998 7997, .addN 7999 7999 7992, .addN 7998 7998 7992,
  .loadN 7997 7999, .storeN 7998 7997]

/-- **The initial trees in the input.** -/
def kiProg : Stmt := .seq kiS1 (.seq toProg (.seq kiS2a (.seq kiS2b (.seq cotProg kiCp))))

theorem kiProg_natOnly : Klein.natOnly kiProg = true := by kernel_rfl

variable {P : Input} {W : ℕ}

/-! ### The registers -/

theorem kiS1_exec {NTb IVb n nF PRb Z Gb : ℕ} (c : Config) (hc : WordsBounded W c)
    (h81 : c.nreg 7981 = NTb) (h84 : c.nreg 7984 = IVb) (h85 : c.nreg 7985 = n)
    (h87 : c.nreg 7987 = nF) (h89 : c.nreg 7989 = PRb) (h90 : c.nreg 7990 = Z)
    (h91 : c.nreg 7991 = Gb) (wG : Gb + 1 ≤ W) (wT : NTb + c.nmem (Gb + 1) ≤ W)
    (wP : PRb + 1 + (c.nmem (NTb + c.nmem (Gb + 1)) - 1) ≤ W) (wZ : Z + 7 * nF + 1 ≤ W)
    (wI : IVb + 4 * n + 4 ≤ W) :
    ∃ c' t, Exec P W kiS1 c c' t ∧ t = 31 ∧
      (ToRegs nF (c.nmem (NTb + c.nmem (Gb + 1)) - 1) Z (PRb + 1) NTb IVb (IVb + n)
          (IVb + 4 * n + 4) 1 c' ∧ c'.nreg 7992 = 1 ∧
        c'.nmem = upd c.nmem (PRb + 1 + (c.nmem (NTb + c.nmem (Gb + 1)) - 1)) 0 ∧
        (∀ r, r < 1600 ∨ (1615 < r ∧ r < 7992) ∨ 7995 < r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold kiS1
  exec_block
  all_goals try ((try config_simp); (try simp only [h81, h84, h85, h87, h89, h90, h91]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
    fun r hr => ?_, rfl, rfl, rfl⟩ <;> config_simp <;>
    (try simp only [h81, h84, h85, h87, h89, h90, h91]) <;> (try omega)
  repeat (rw [upd_other _ _ _ (by omega)])

theorem kiS2a_exec {nD NFb RVb ofF nF nV Z ITb HDb : ℕ} (c : Config) (hc : WordsBounded W c)
    (h80 : c.nreg 7980 = nD) (h82 : c.nreg 7982 = NFb) (h83 : c.nreg 7983 = RVb)
    (h86 : c.nreg 7986 = ofF) (h87 : c.nreg 7987 = nF) (h88 : c.nreg 7988 = nV)
    (h92 : c.nreg 7992 = 1) (h12 : c.nreg 1612 = Z + 7 * nF + 1) (h14 : c.nreg 1614 = ITb)
    (h15 : c.nreg 1615 = HDb) (wH : HDb + 1 ≤ W)
    (wZ : Z + 8 * nF + 1 + 3 * nD + 4 * nV + 1 ≤ W) :
    ∃ c' t, Exec P W kiS2a c c' t ∧ t = 19 ∧
      (c'.nreg 1700 = nD ∧ c'.nreg 1701 = c.nmem (HDb + 1) ∧ c'.nreg 1702 = ITb ∧
        c'.nreg 1703 = RVb ∧ c'.nreg 1704 = NFb ∧ c'.nreg 1705 = ofF ∧
        c'.nreg 1706 = Z + 8 * nF + 1 ∧ c'.nreg 1500 = nD ∧ c'.nreg 1501 = nV ∧
        c'.nreg 1502 = Z + 8 * nF + 1 + nD ∧ c'.nreg 1504 = Z + 8 * nF + 1 ∧
        c'.nreg 1505 = Z + 8 * nF + 1 + 3 * nD ∧
        c'.nreg 1506 = Z + 8 * nF + 1 + 3 * nD + nV + 1 ∧
        c'.nreg 1507 = Z + 8 * nF + 1 + 3 * nD + 2 * nV + 1 ∧
        c'.nreg 1508 = Z + 8 * nF + 1 + 3 * nD + 3 * nV + 1 ∧
        c'.nreg 1509 = Z + 8 * nF + 1 + 3 * nD + 4 * nV + 1 ∧
        (∀ r, r < 1500 ∨ (1509 < r ∧ r < 1700) ∨ (1706 < r ∧ r < 7996) ∨ 7996 < r →
          c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold kiS2a
  exec_block
  all_goals try ((try config_simp); (try simp only [h80, h87, h88, h92, h12, h15]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_,
    rfl, rfl, rfl, rfl⟩ <;> config_simp <;>
    (try simp only [h80, h82, h83, h86, h87, h88, h92, h12, h14, h15]) <;> (try omega)
  repeat (rw [upd_other _ _ _ (by omega)])

theorem kiS2b_exec {nD NFb n ofF nV Gb Z₂ IVb : ℕ} (c : Config) (hc : WordsBounded W c)
    (h80 : c.nreg 7980 = nD) (h82 : c.nreg 7982 = NFb) (h85 : c.nreg 7985 = n)
    (h86 : c.nreg 7986 = ofF) (h88 : c.nreg 7988 = nV) (h91 : c.nreg 7991 = Gb)
    (h92 : c.nreg 7992 = 1) (h02 : c.nreg 1502 = Z₂ + nD)
    (h07 : c.nreg 1507 = Z₂ + 3 * nD + 2 * nV + 1) (h08 : c.nreg 1508 = Z₂ + 3 * nD + 3 * nV + 1)
    (h09 : c.nreg 1509 = Z₂ + 3 * nD + 4 * nV + 1) (h702 : c.nreg 1702 = IVb + n)
    (wG : NFb + c.nmem Gb ≤ W) (wZ : Z₂ + 4 * nD + 15 * nV + 2 ≤ W) (wI : IVb + 4 * n + 2 ≤ W) :
    ∃ c' t, Exec P W kiS2b c c' t ∧ t = 31 ∧
      (c'.nreg 1400 = nV ∧ c'.nreg 1401 = c.nmem (NFb + c.nmem Gb) - ofF ∧
        c'.nreg 1402 = Z₂ + 3 * nD + 2 * nV + 1 ∧ c'.nreg 1403 = Z₂ + 3 * nD + 3 * nV + 1 ∧
        c'.nreg 1404 = Z₂ + 3 * nD + 4 * nV + 1 ∧ c'.nreg 1405 = Z₂ + 2 * nD ∧
        c'.nreg 1406 = Z₂ + 4 * nD + 4 * nV + 1 ∧ c'.nreg 1407 = Z₂ + 4 * nD + 5 * nV + 1 ∧
        c'.nreg 1408 = Z₂ + 4 * nD + 6 * nV + 1 ∧
        ToRegs nV (c.nmem (NFb + c.nmem Gb) - ofF) (Z₂ + 4 * nD + 7 * nV + 1)
          (Z₂ + 4 * nD + 6 * nV + 1) NFb (IVb + 2 * n) (IVb + 3 * n) (IVb + 4 * n + 2) ofF c' ∧
        (∀ r, r < 1400 ∨ (1408 < r ∧ r < 1600) ∨ (1615 < r ∧ r < 7997) ∨ 7997 < r →
          c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold kiS2b
  exec_block
  all_goals try ((try config_simp); (try simp only [h80, h85, h88, h92, h02, h07, h08, h09, h702,
                   h82, h91]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun r hr => ?_,
    rfl, rfl, rfl, rfl⟩ <;> config_simp <;>
    (try simp only [h80, h82, h85, h86, h88, h91, h92, h02, h07, h08, h09, h702]) <;> (try omega)
  repeat (rw [upd_other _ _ _ (by omega)])

theorem kiCp_exec {IVb n : ℕ} (c : Config) (hc : WordsBounded W c) (h84 : c.nreg 7984 = IVb)
    (h85 : c.nreg 7985 = n) (h92 : c.nreg 7992 = 1) (wI : IVb + 4 * n + 5 ≤ W) :
    ∃ c' t, Exec P W kiCp c c' t ∧ t = 14 ∧
      (c'.nmem = upd (upd c.nmem (IVb + 4 * n) (c.nmem (IVb + 4 * n + 4))) (IVb + 4 * n + 1)
          (c.nmem (IVb + 4 * n + 5)) ∧
        (∀ r, r < 7997 ∨ 7999 < r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold kiCp
  exec_block
  all_goals try ((try config_simp); (try simp only [h84, h85, h92]); omega)
  refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl⟩ <;> config_simp <;>
    (try simp only [h84, h85, h92])
  · have e1 : IVb + n + n + n + n = IVb + 4 * n := by ring
    have e2 : IVb + n + n + n + n + 1 + 1 + 1 + 1 = IVb + 4 * n + 4 := by ring
    have e3 : IVb + n + n + n + n + 1 + 1 + 1 + 1 + 1 = IVb + 4 * n + 5 := by ring
    have e4 : IVb + n + n + n + n + 1 = IVb + 4 * n + 1 := by ring
    rw [e3, e2, e4, e1, upd_other _ _ _ (show IVb + 4 * n + 5 ≠ IVb + 4 * n by omega)]
  · repeat (rw [upd_other _ _ _ (by omega)])


/-! ### The whole program -/

/-- The cost bound of `kiProg`. -/
def kiCost (nD nF nV : ℕ) : ℕ := 65 * nD + 122 * nF + 178 * nV + 254

section Map

open STFlow

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- **The initial trees of the s-t flow and their orders on the machine** (see the module
docstring): on a plane map with the compact node words `NT[σ d] = 1 + τv (face d)`,
`NF[σ d] = ofF + τf (tail d)`, the reverses, the parent words `PAR[1 + τv x] = σ (T₀.par x)`
of a dual tree `T₀` rooted at `face d₀` (at `PRb`) and the terminal darts `σ d₁`, `σ d₀` at
`Gb`, `Gb + 1`, `kiProg` ends within `kiCost nD nF nV` steps with the orders of `toDD T₀`
(`IV`, `IT`, `HD[0]`, `HD[1]`) and of **a cotree `C₀` of `T₀` rooted at `tail d₁`** (`IF`, `IC`,
`HD[2]`, `HD[3]`) at `IVb`, `IVb + n`, `IVb + 2n`, `IVb + 3n`, `IVb + 4n`. -/
theorem kiProg_exec [Nonempty D] (hM : M.IsPlane) {nD n nF nV : ℕ} (σ : D ≃ Fin nD)
    (τv : F ≃ Fin nF) (τf : V ≃ Fin nV) {T₀ : DTree M} (d₀ d₁ : D)
    (hroot : T₀.root = M.face d₀) {NTb NFb RVb IVb ofF PRb Z Gb : ℕ} (c : Config)
    (hc : WordsBounded W c)
    (h80 : c.nreg 7980 = nD) (h81 : c.nreg 7981 = NTb) (h82 : c.nreg 7982 = NFb)
    (h83 : c.nreg 7983 = RVb) (h84 : c.nreg 7984 = IVb) (h85 : c.nreg 7985 = n)
    (h86 : c.nreg 7986 = ofF) (h87 : c.nreg 7987 = nF) (h88 : c.nreg 7988 = nV)
    (h89 : c.nreg 7989 = PRb) (h90 : c.nreg 7990 = Z) (h91 : c.nreg 7991 = Gb)
    (hNT : ∀ d, c.nmem (NTb + σ d) = 1 + τv (M.face d))
    (hNF : ∀ d, c.nmem (NFb + σ d) = ofF + τf (M.tail d))
    (hRV : ∀ d, c.nmem (RVb + σ d) = σ (M.rev d))
    (hPAR : ∀ x, x ≠ T₀.root → c.nmem (PRb + 1 + τv x) = σ (T₀.par x))
    (hG0 : c.nmem Gb = σ d₁) (hG1 : c.nmem (Gb + 1) = σ d₀)
    (lT : NTb + nD ≤ IVb) (lN : NFb + nD ≤ IVb) (lR : RVb + nD ≤ IVb) (lG : Gb + 2 ≤ IVb)
    (lP : IVb + 4 * n + 6 ≤ PRb + 1) (lZ : PRb + 1 + nF ≤ Z) (hnF : nF ≤ n) (hnV : nV ≤ n)
    (wZ : Z + 8 * nF + 4 * nD + 15 * nV + 3 ≤ W) (wo : ofF + nV ≤ W) :
    ∃ c' t, Exec P W kiProg c c' t ∧ t ≤ kiCost nD nF nV ∧
      ∃ (ts : List F) (C₀ : DTree M.dual) (cs : List V), C₀.root = M.tail d₁ ∧
        (∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) ∧
        Klein.Orders (toDD T₀) ((List.finRange nF).map τv.symm) ts ∧
        Klein.Orders C₀ ((List.finRange nV).map τf.symm) cs ∧
        (∀ i (h : i < ((List.finRange nF).map τv.symm).length),
          c'.nmem (IVb + i) = 1 + τv ((List.finRange nF).map τv.symm)[i]) ∧
        (∀ i (h : i < ts.length), c'.nmem (IVb + n + i) = σ (T₀.par ts[i])) ∧
        (∀ i (h : i < ((List.finRange nV).map τf.symm).length),
          c'.nmem (IVb + 2 * n + i) = ofF + τf ((List.finRange nV).map τf.symm)[i]) ∧
        (∀ i (h : i < cs.length), c'.nmem (IVb + 3 * n + i) = σ (C₀.par cs[i])) ∧
        c'.nmem (IVb + 4 * n) = ((List.finRange nF).map τv.symm).length ∧
        c'.nmem (IVb + 4 * n + 1) = ts.length ∧
        c'.nmem (IVb + 4 * n + 2) = ((List.finRange nV).map τf.symm).length ∧
        c'.nmem (IVb + 4 * n + 3) = cs.length ∧
        (∀ a, a < IVb ∨ IVb + 4 * n + 6 ≤ a → a < PRb + 1 ∨ PRb + 1 + nF ≤ a →
          a < Z ∨ Z + 8 * nF + 4 * nD + 15 * nV + 3 ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r < 1400 ∨ (1422 < r ∧ r < 1500) ∨ (1520 < r ∧ r < 1600) ∨
          (1634 < r ∧ r < 1700) ∨ (1719 < r ∧ r < 7992) ∨ 7999 < r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hD : 0 < nD := Fin.pos (σ (Classical.arbitrary D))
  have hFp : 0 < nF := Fin.pos (τv (M.face (Classical.arbitrary D)))
  have hroot' : c.nmem (NTb + c.nmem (Gb + 1)) - 1 = τv T₀.root := by
    rw [hG1, hNT, hroot]; omega
  have hd0 := (σ d₀).2
  have hd1 := (σ d₁).2
  -- 1. the registers of the orders of `T₀`
  obtain ⟨c₁, t₁, e₁, ht₁, hR₁, r92, m₁, n₁, rr₁, rm₁, o₁⟩ := kiS1_exec (P := P) c hc h81 h84 h85
    h87 h89 h90 h91 (by omega) (by rw [hG1]; omega)
    (by rw [hroot']; have := (τv T₀.root).2; omega) (by omega) (by omega)
  rw [hroot'] at hR₁ m₁
  have hL₁ : ToLay nF nD (τv (toDD T₀).root) Z (PRb + 1) NTb IVb (IVb + n) (IVb + 4 * n + 4) 1
      W :=
    ⟨hFp, (τv _).2, Or.inr lZ, Or.inr (by omega), Or.inl (by omega), Or.inl (by omega),
      by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hPD₁ : ∀ y, y ≠ (toDD T₀).root → c₁.nmem (PRb + 1 + τv y) = σ ((toDD T₀).par y) :=
    fun y hy => by
      have hne : (τv y : ℕ) ≠ τv T₀.root := fun h => hy (τv.injective (Fin.ext h))
      rw [m₁, upd_other _ _ _ (by omega)]; exact hPAR y hy
  have hPDr₁ : c₁.nmem (PRb + 1 + τv (toDD T₀).root) < nD := by rw [m₁]; simp; exact hD
  have hA₁ : ∀ d, c₁.nmem (NTb + σ d) = 1 + τv ((M.dual.dual).face d) := fun d => by
    have := (σ d).2; have := (τv T₀.root).2
    rw [m₁, upd_other _ _ _ (by omega)]; exact hNT d
  -- 2. the orders of `T₀`
  obtain ⟨c₂, t₂, e₂, ht₂, ts, hOT, hIV, hIT, hH0, hH1, m₂, n₂, rr₂, rm₂, o₂⟩ :=
    toProg_orders (P := P) (M := M.dual.dual) (toDD T₀) σ τv hL₁ c₁ e₁.wb_right hR₁ hPD₁ hPDr₁
      hA₁
  have hts : ts.length ≤ nF := by
    rw [orders_ylen_eq hOT]; have := Fintype.card_fin nF ▸ Fintype.card_congr τv; omega
  have q₂ : ∀ r, r < 1500 ∨ (1520 < r ∧ r < 1620) ∨ 1634 < r → c₂.nreg r = c₁.nreg r := n₂
  have q₁ : ∀ r, 7980 ≤ r → r ≤ 7991 → c₁.nreg r = c.nreg r := fun r h1 h2 => n₁ r (by omega)
  -- 3. the registers `1700 …`, `1500 …` of the cotree
  obtain ⟨c₃, t₃, e₃, ht₃, a00, a01, a02, a03, a04, a05, a06, s00, s01, s02, s04, s05, s06, s07,
    s08, s09, n₃, m₃, rr₃, rm₃, o₃⟩ := kiS2a_exec (P := P) (nD := nD) (NFb := NFb) (RVb := RVb)
      (ofF := ofF) (nF := nF) (nV := nV) (Z := Z) (ITb := IVb + n)
      (HDb := IVb + 4 * n + 4) c₂ e₂.wb_right
      (by rw [q₂ _ (by omega), q₁ _ (by omega) (by omega)]; exact h80)
      (by rw [q₂ _ (by omega), q₁ _ (by omega) (by omega)]; exact h82)
      (by rw [q₂ _ (by omega), q₁ _ (by omega) (by omega)]; exact h83)
      (by rw [q₂ _ (by omega), q₁ _ (by omega) (by omega)]; exact h86)
      (by rw [q₂ _ (by omega), q₁ _ (by omega) (by omega)]; exact h87)
      (by rw [q₂ _ (by omega), q₁ _ (by omega) (by omega)]; exact h88)
      (by rw [q₂ _ (by omega)]; exact r92) (by rw [q₂ _ (by omega)]; exact hR₁.r12)
      (by rw [q₂ _ (by omega)]; exact hR₁.r14) (by rw [q₂ _ (by omega)]; exact hR₁.r15)
      (by omega) (by omega)
  -- 4. the registers `1400 …`, `1600 …` of the cotree
  have hGm : c₃.nmem Gb = σ d₁ := by
    rw [m₃, m₂ _ (Or.inl (by omega)) (Or.inl (by omega)), m₁, upd_other _ _ _ (by omega)]
    exact hG0
  have hNFm : ∀ d, c₃.nmem (NFb + σ d) = ofF + τf (M.tail d) := fun d => by
    have := (σ d).2
    rw [m₃, m₂ _ (Or.inl (by omega)) (Or.inl (by omega)), m₁, upd_other _ _ _ (by omega)]
    exact hNF d
  have q₃ : ∀ r, 7980 ≤ r → r ≤ 7992 → c₃.nreg r = c₁.nreg r := fun r h1 h2 => by
    rw [n₃ r (by omega), q₂ r (by omega)]
  obtain ⟨c₄, t₄, e₄, ht₄, b00, b01, b02, b03, b04, b05, b06, b07, b08, hR₄, n₄, m₄, rr₄, rm₄,
    o₄⟩ := kiS2b_exec (P := P) (nD := nD) (NFb := NFb) (n := n) (ofF := ofF) (nV := nV)
      (Gb := Gb) (Z₂ := Z + 8 * nF + 1) (IVb := IVb) c₃ e₃.wb_right
      (by rw [q₃ _ (by omega) (by omega), q₁ _ (by omega) (by omega)]; exact h80)
      (by rw [q₃ _ (by omega) (by omega), q₁ _ (by omega) (by omega)]; exact h82)
      (by rw [q₃ _ (by omega) (by omega), q₁ _ (by omega) (by omega)]; exact h85)
      (by rw [q₃ _ (by omega) (by omega), q₁ _ (by omega) (by omega)]; exact h86)
      (by rw [q₃ _ (by omega) (by omega), q₁ _ (by omega) (by omega)]; exact h88)
      (by rw [q₃ _ (by omega) (by omega), q₁ _ (by omega) (by omega)]; exact h91)
      (by rw [q₃ _ (by omega) (by omega)]; exact r92) (by rw [s02])
      (s07.trans (by ring)) (s08.trans (by ring)) (s09.trans (by ring)) (by rw [a02])
      (by rw [hGm]; omega) (by omega) (by omega)
  rw [hGm, hNFm] at b01 hR₄
  have e01 : ofF + (τf (M.tail d₁) : ℕ) - ofF = τf ((M.dual).face d₁) := by
    show _ = (τf (M.tail d₁) : ℕ); omega
  rw [e01] at b01 hR₄
  have q₄ : ∀ r, 1700 ≤ r → r ≤ 1706 → c₄.nreg r = c₃.nreg r := fun r h1 h2 => n₄ r (by omega)
  have q₄' : ∀ r, 1500 ≤ r → r ≤ 1509 → c₄.nreg r = c₃.nreg r := fun r h1 h2 => n₄ r (by omega)
  -- 5. the cotree
  have hIT₄ : ∀ j (h : j < ts.length), c₄.nmem (IVb + n + j) = σ ((toDD T₀).par ts[j]) :=
    fun j h => by rw [m₄, m₃]; exact hIT j h
  have hRV₄ : ∀ d, c₄.nmem (RVb + σ d) = σ ((M.dual).rev d) := fun d => by
    have := (σ d).2; have := (τv T₀.root).2
    rw [m₄, m₃, m₂ _ (Or.inl (by omega)) (Or.inl (by omega)), m₁, upd_other _ _ _ (by omega)]
    exact hRV d
  have hNF₄ : ∀ d, c₄.nmem (NFb + σ d) = ofF + τf ((M.dual).face d) := fun d => by
    rw [m₄]; exact hNFm d
  obtain ⟨c₅, t₅, e₅, ht₅, C₀, cs, hCr, hoff, hOC, hIF, hIC, hH2, hH3, m₅, n₅, rr₅, rm₅, o₅⟩ :=
    cotProg_exec (P := P) (M := M.dual) hM.dual (toDD T₀) σ τf (M.tail d₁) hOT.ymem c₄
      e₄.wb_right
      (by rw [q₄ _ (by omega) (by omega)]; exact a00)
      (by rw [q₄ _ (by omega) (by omega), a01]; exact hH1)
      (by rw [q₄ _ (by omega) (by omega)]; exact a02)
      (by rw [q₄ _ (by omega) (by omega)]; exact a03)
      (by rw [q₄ _ (by omega) (by omega)]; exact a04)
      (by rw [q₄ _ (by omega) (by omega)]; exact a05)
      (by rw [q₄ _ (by omega) (by omega)]; exact a06)
      (by rw [q₄' _ (by omega) (by omega)]; exact s00)
      (by rw [q₄' _ (by omega) (by omega)]; exact s01)
      (by rw [q₄' _ (by omega) (by omega)]; exact s02)
      (by rw [q₄' _ (by omega) (by omega)]; exact s04)
      (by rw [q₄' _ (by omega) (by omega)]; exact s05)
      (by rw [q₄' _ (by omega) (by omega), s06])
      (by rw [q₄' _ (by omega) (by omega), s07])
      (by rw [q₄' _ (by omega) (by omega), s08])
      (by rw [q₄' _ (by omega) (by omega), s09])
      b00 b01 b02 b03 b04 b05 b06 b07 b08 hR₄ hIT₄ hRV₄ hNF₄ (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  -- 6. the two lengths of the orders of `T₀`
  have q₅ : ∀ r, 7980 ≤ r → r ≤ 7992 → c₅.nreg r = c₁.nreg r := fun r h1 h2 => by
    rw [n₅ _ (by omega), n₄ _ (by omega), n₃ _ (by omega), q₂ _ (by omega)]
  have r84 : c₅.nreg 7984 = IVb := by
    rw [q₅ _ (by omega) (by omega), q₁ _ (by omega) (by omega)]; exact h84
  have r85 : c₅.nreg 7985 = n := by
    rw [q₅ _ (by omega) (by omega), q₁ _ (by omega) (by omega)]; exact h85
  have r92' : c₅.nreg 7992 = 1 := by rw [q₅ _ (by omega) (by omega)]; exact r92
  obtain ⟨c₆, t₆, e₆, ht₆, m₆, n₆, rr₆, rm₆, o₆⟩ := kiCp_exec (P := P) (IVb := IVb) (n := n) c₅
    e₅.wb_right r84 r85 r92' (by omega)
  have mT : ∀ a, a < IVb + 2 * n ∨ IVb + 4 * n + 4 ≤ a → a < Z → c₅.nmem a = c₂.nmem a :=
    fun a h1 h2 => by rw [m₅ a (Or.inl (by omega)) (by omega), m₄, m₃]
  have m6 : ∀ a, a ≠ IVb + 4 * n → a ≠ IVb + 4 * n + 1 → c₆.nmem a = c₅.nmem a :=
    fun a h1 h2 => by rw [m₆, upd_other _ _ _ h2, upd_other _ _ _ h1]
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ (Exec.seq e₄ (Exec.seq e₅ e₆)))), ?_, ts, C₀, cs,
    hCr, hoff, hOT, hOC, fun i h => ?_, fun i h => ?_, fun i h => ?_, fun i h => ?_, ?_, ?_, ?_,
    ?_, fun a h1 h2 h3 => ?_, fun r hr => ?_, by rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁], by rw [o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · unfold kiCost; unfold toCost at ht₂; unfold cotCost at ht₅; omega
  · have : i < nF := by simpa using h
    rw [m6 _ (by omega) (by omega), mT _ (by omega) (by omega)]; exact hIV i h
  · rw [m6 _ (by omega) (by omega), mT _ (by omega) (by omega)]; exact hIT i h
  · have : i < nV := by simpa using h
    rw [m6 _ (by omega) (by omega)]; exact hIF i h
  · have : i < nV := by
      have h1 := hOC.ylen; have h2 := Fintype.card_fin nV ▸ Fintype.card_congr τf; omega
    rw [m6 _ (by omega) (by omega)]; exact hIC i h
  · rw [m₆, upd_other _ _ _ (by omega), upd_same, mT _ (by omega) (by omega)]; exact hH0
  · rw [m₆, upd_same, mT _ (by omega) (by omega)]; exact hH1
  · rw [m6 _ (by omega) (by omega)]; exact hH2
  · rw [m6 _ (by omega) (by omega), show IVb + 4 * n + 3 = IVb + 4 * n + 2 + 1 by ring]
    exact hH3
  · have := (τv T₀.root).2
    rw [m6 a (by omega) (by omega), m₅ a (by omega) (by omega), m₄, m₃,
      m₂ a (by omega) (by omega), m₁, upd_other _ _ _ (by omega)]
  · rw [n₆ r (by omega), n₅ r (by omega), n₄ r (by omega), n₃ r (by omega), q₂ r (by omega),
      n₁ r (by omega)]

/-- **`Klein.KInit` from the words of `kiProg`** at `IVb = ib + iIV nD n 2`, for any input whose
words are the memory at `ib`. -/
theorem kInit_of {nD n nF nV : ℕ} (σ : D ≃ Fin nD) (τv : F ≃ Fin nF) (τf : V ≃ Fin nV)
    {T₀ : DTree M} {C₀ : DTree M.dual} {ts : List F} {cs : List V}
    (hOT : Klein.Orders (toDD T₀) ((List.finRange nF).map τv.symm) ts)
    (hOC : Klein.Orders C₀ ((List.finRange nV).map τf.symm) cs) {ofF ib : ℕ} {mem : ℕ → ℕ}
    (hIV : ∀ i (h : i < ((List.finRange nF).map τv.symm).length),
      mem (ib + Klein.iIV nD n 2 + i) = 1 + τv ((List.finRange nF).map τv.symm)[i])
    (hIT : ∀ i (h : i < ts.length), mem (ib + Klein.iIV nD n 2 + n + i) = σ (T₀.par ts[i]))
    (hIF : ∀ i (h : i < ((List.finRange nV).map τf.symm).length),
      mem (ib + Klein.iIV nD n 2 + 2 * n + i) = ofF + τf ((List.finRange nV).map τf.symm)[i])
    (hIC : ∀ i (h : i < cs.length), mem (ib + Klein.iIV nD n 2 + 3 * n + i) = σ (C₀.par cs[i]))
    (hH0 : mem (ib + Klein.iIV nD n 2 + 4 * n) = ((List.finRange nF).map τv.symm).length)
    (hH1 : mem (ib + Klein.iIV nD n 2 + 4 * n + 1) = ts.length)
    (hH2 : mem (ib + Klein.iIV nD n 2 + 4 * n + 2) = ((List.finRange nV).map τf.symm).length)
    (hH3 : mem (ib + Klein.iIV nD n 2 + 4 * n + 3) = cs.length)
    (P : Input) (hP : ∀ j, j < Klein.iHD nD n 2 + 4 → P.data.getD j 0 = mem (ib + j))
    (hnF : nF ≤ n) (hnV : nV ≤ n) :
    Klein.KInit M.dual σ (fun x => 1 + (τv x : ℕ)) (fun v => ofF + (τf v : ℕ)) n 2 (toDD T₀) C₀
      ((List.finRange nF).map τv.symm) ts ((List.finRange nV).map τf.symm) cs P := by
  have hts : ts.length ≤ nF := by
    have h1 := hOT.ylen; have h2 := Fintype.card_fin nF ▸ Fintype.card_congr τv; omega
  have hcs : cs.length ≤ nV := by
    have h1 := hOC.ylen; have h2 := Fintype.card_fin nV ▸ Fintype.card_congr τf; omega
  refine ⟨hOT, hOC, fun i h => ?_, fun i h => ?_, fun i h => ?_, fun i h => ?_, ?_, ?_, ?_, ?_⟩
  · have : i < nF := by simpa using h
    rw [hP _ (by simp only [Klein.iHD, Klein.iIT, Klein.iIF, Klein.iIC, Klein.iIV]; omega), ← add_assoc]; exact hIV i h
  · rw [hP _ (by simp only [Klein.iHD, Klein.iIT, Klein.iIF, Klein.iIC, Klein.iIV]; omega)]
    unfold Klein.iIT; rw [← add_assoc, ← add_assoc]; exact hIT i h
  · have : i < nV := by simpa using h
    rw [hP _ (by simp only [Klein.iHD, Klein.iIT, Klein.iIF, Klein.iIC, Klein.iIV]; omega)]
    unfold Klein.iIF; rw [← add_assoc, ← add_assoc]; exact hIF i h
  · rw [hP _ (by simp only [Klein.iHD, Klein.iIT, Klein.iIF, Klein.iIC, Klein.iIV]; omega)]
    unfold Klein.iIC; rw [← add_assoc, ← add_assoc]; exact hIC i h
  · rw [hP _ (by unfold Klein.iHD; omega)]; unfold Klein.iHD; rw [← add_assoc]; exact hH0
  · rw [hP _ (by unfold Klein.iHD; omega)]; unfold Klein.iHD
    rw [show ib + (Klein.iIV nD n 2 + 4 * n + 1) = ib + Klein.iIV nD n 2 + 4 * n + 1 by ring]
    exact hH1
  · rw [hP _ (by unfold Klein.iHD; omega)]; unfold Klein.iHD
    rw [show ib + (Klein.iIV nD n 2 + 4 * n + 2) = ib + Klein.iIV nD n 2 + 4 * n + 2 by ring]
    exact hH2
  · rw [hP _ (by unfold Klein.iHD; omega)]; unfold Klein.iHD
    rw [show ib + (Klein.iIV nD n 2 + 4 * n + 3) = ib + Klein.iIV nD n 2 + 4 * n + 3 by ring]
    exact hH3

end Map

end StEnc

end BKMNW

end PlanarFlow
