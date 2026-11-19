module

public import PlanarFlow.BKMNW.StCallM
public import PlanarFlow.NegSSSP.LinGlue

/-!
# The real start of the s-t flow on natural words: capacities, restriction, lengths, constants

`STFlow.st_sNFM` (`StCallM.lean`) runs the fixed natural s-t flow program from a configuration
holding, as residues modulo `Mo = 2 H + 1`, the real start of `STFlow.pcore_exec`: `capR c X Y`
(`CP`), the restriction `rsIn` (`RS`), the lengths `N capR + ε` (`WT`, `PH`), `kTh`, `kH0`. All of
them are natural numbers at most `H`, so their residues are themselves. Here a program on
**natural words only** computes them, by dart index `i < nD`, from the capacities `C[i]`, the flags
`XT[i]`, `YT[i]` (tail in `X`, in `Y`), the reverses `RV[i]` and the shifted isolating weights
`WW[i] = B₀ + w` (as `NegSSSP.iwProg_treeW` writes them), and also computes `H` and `Mo`:

* `SrD` (the data), `srIns`, `srCr`, `srRs`, `srEp`, `srS`, `srE`, `srSC`, `srLex`, `srN`, `srKZ`,
  `srTh`, `srH0`, `srH`, `srMo`, `srWl` (the values, as natural numbers);
* `srProg = srInit ; srA ; srC1 ; srB ; srC2 ; srD` (`srProg_natOnly`);
* **`srProg_exec`**: within `60 nD + 100` steps, `WT[i] = PH[i] = srWl i`, `CP[i] = srCr i`,
  `RS[i] = srRs i` at `Ob + i`, `Ob + nD + i`, `Ob + 3 nD + 3 + i`, `Ob + 4 nD + 3 + i`, `kTh`,
  `kH0` at `Ob + 3 nD + 1`, `+ 2`, and `H`, `Mo` in `r7833`, `r7834`; memory outside
  `[Ob, Ob + 5 nD + 3)` kept.

Registers: natural `7800 … 7810` (inputs `nD`, `Cb`, `Xb`, `Yb`, `RVb`, `Wb`, `B₀`, `nF`, `nV`,
`n`, `Ob`), `7811 … 7843` (scratch and results). No real register or real memory is touched.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

variable {P : Input} {W : ℕ}

/-! ### The values -/

/-- The data of the program: sizes and the arrays by dart index. -/
structure SrD where
  nD : ℕ
  n : ℕ
  nF : ℕ
  nV : ℕ
  B0 : ℕ
  C : ℕ → ℕ
  XT : ℕ → ℕ
  YT : ℕ → ℕ
  RV : ℕ → ℕ
  WW : ℕ → ℕ

namespace SrD

variable (p : SrD)

/-- `L₀ = (4 nF + 5) nV` (`STFlow.isoL`). -/
def L0 : ℕ := (4 * p.nF + 5) * p.nV

/-- The dart `i` is inside `X` or inside `Y`. -/
def ins (i : ℕ) : Prop := (0 < p.XT i ∧ 0 < p.XT (p.RV i)) ∨ (0 < p.YT i ∧ 0 < p.YT (p.RV i))

instance (i : ℕ) : Decidable (p.ins i) := by unfold ins; infer_instance

/-- The total capacity. -/
def S : ℕ := ∑ i ∈ range p.nD, p.C i

/-- The contracted capacity `capR`. -/
def cr (i : ℕ) : ℕ := if p.ins i then p.S + 1 else if 0 < p.YT i then 0 else p.C i

/-- The restriction. -/
def rs (i : ℕ) : ℕ := if p.ins i then 0 else 1

/-- The perturbation `isoL + w`. -/
def ep (i : ℕ) : ℕ := p.L0 + p.WW i - p.B0

def E : ℕ := ∑ i ∈ range p.nD, p.ep i
def SC : ℕ := ∑ i ∈ range p.nD, p.cr i
def lex : ℕ := (p.nF + 1) * p.E
def N : ℕ := 2 * p.lex + 1
def kZ : ℕ := p.N * p.SC + 2 * p.lex
def kTh : ℕ := p.kZ + 1
def kH0 : ℕ := p.kTh + (p.nD + 2) * p.kZ
/-- `H = pstH n nD nF nV kH0`. -/
def H : ℕ := 2 * STFlow.pstVb p.n p.nD p.nF p.nV p.kH0
def Mo : ℕ := 2 * p.H + 1
/-- The length `N capR + ε`. -/
def wl (i : ℕ) : ℕ := p.N * p.cr i + p.ep i

end SrD

/-! ### The program -/

/-- `r7811 = 1`, `r7812 = 0`, the counter and the sums `0`, `L₀` in `r7816`. -/
def srInit : Stmt :=
  block [.constN 7811 1, .constN 7812 0, .constN 7813 0, .constN 7814 0, .constN 7815 0,
    .constN 7817 4, .mulN 7817 7817 7807, .constN 7818 5, .addN 7817 7817 7818,
    .mulN 7816 7817 7808]

/-- The dart `i = r7813`: `S += C[i]`, `E += L₀ + WW[i] - B₀`. -/
def srABody : Stmt :=
  block [.addN 7817 7801 7813, .loadN 7817 7817, .addN 7814 7814 7817,
    .addN 7817 7805 7813, .loadN 7817 7817, .addN 7817 7817 7816, .subN 7817 7817 7806,
    .addN 7815 7815 7817, .addN 7813 7813 7811]

def srA : Stmt := .whileLtN 7813 7800 srABody

/-- `lex = (nF + 1) E` (`r7822`), `N = 2 lex + 1` (`r7820`), `SC = 0`, the counter, the bases
`Ob + 3 nD + 3` (`r7841`), `Ob + 4 nD + 3` (`r7842`), `Ob + nD` (`r7843`). -/
def srC1 : Stmt :=
  block [.addN 7818 7807 7811, .mulN 7822 7818 7815, .addN 7820 7822 7822, .addN 7820 7820 7811,
    .constN 7821 0, .constN 7813 0, .constN 7818 3, .mulN 7818 7818 7800, .addN 7818 7818 7810,
    .constN 7819 3, .addN 7841 7818 7819, .addN 7842 7841 7800, .addN 7843 7810 7800]

/-- Load `x₁ = XT[i]` (`r7823`), `x₂ = XT[RV[i]]` (`r7825`), `y₁ = YT[i]` (`r7826`),
`y₂ = YT[RV[i]]` (`r7827`), `C[i]` (`r7828`), the flag `r7830 := 0`. -/
def srBLd : Stmt :=
  block [.addN 7823 7802 7813, .loadN 7823 7823, .addN 7824 7804 7813, .loadN 7824 7824,
    .addN 7825 7802 7824, .loadN 7825 7825, .addN 7826 7803 7813, .loadN 7826 7826,
    .addN 7827 7803 7824, .loadN 7827 7827, .addN 7828 7801 7813, .loadN 7828 7828,
    .constN 7830 0]

/-- `f := 1` if `0 < a` and `0 < b` (`r7812 = 0`). -/
def srPair (a b f : ℕ) : Stmt :=
  .ifLtN 7812 a (.ifLtN 7812 b (block [.constN f 1]) .skip) .skip

/-- The capacity (`r7829`) and the restriction (`r7831`) from the flag `r7830`. -/
def srSel : Stmt :=
  .ifLtN 7812 7830 (block [.addN 7829 7814 7811, .constN 7831 0])
    (.seq (block [.constN 7831 1]) (.ifLtN 7812 7826 (block [.constN 7829 0])
      (block [.copyN 7829 7828])))

/-- Store `CP[i]`, `RS[i]`, `SC += cr`, `i += 1`. -/
def srBSt : Stmt :=
  block [.addN 7832 7841 7813, .storeN 7832 7829, .addN 7832 7842 7813, .storeN 7832 7831,
    .addN 7821 7821 7829, .addN 7813 7813 7811]

def srBBody : Stmt :=
  .seq srBLd (.seq (srPair 7823 7825 7830) (.seq (srPair 7826 7827 7830) (.seq srSel srBSt)))

def srB : Stmt := .whileLtN 7813 7800 srBBody

/-- `kZ` (`r7830`), `kTh` (`r7831`), `kH0` (`r7832`), stored at `Ob + 3 nD + 1`, `+ 2`. -/
def srC2a : Stmt :=
  block [.mulN 7830 7820 7821, .addN 7830 7830 7822, .addN 7830 7830 7822,
    .addN 7831 7830 7811, .constN 7835 2, .addN 7835 7800 7835, .mulN 7835 7835 7830,
    .addN 7832 7831 7835, .constN 7836 3, .mulN 7836 7836 7800, .addN 7836 7836 7810,
    .addN 7836 7836 7811, .storeN 7836 7831, .addN 7836 7836 7811, .storeN 7836 7832]

/-- `pstVb n nD nF nV kH0` (`r7837`), `H` (`r7833`), `Mo` (`r7834`), the counter `0`. -/
def srC2b : Stmt :=
  block [.addN 7837 7807 7808, .constN 7838 4, .mulN 7837 7838 7837, .mulN 7837 7837 7832,
    .mulN 7837 7809 7837,
    .constN 7838 2, .mulN 7838 7838 7809, .mulN 7838 7838 7832, .addN 7838 7838 7809,
    .constN 7839 4, .mulN 7839 7839 7832, .addN 7838 7838 7839, .constN 7839 2,
    .addN 7839 7800 7839, .mulN 7838 7839 7838, .addN 7837 7837 7838,
    .constN 7838 8, .mulN 7838 7838 7807, .mulN 7838 7838 7832, .mulN 7838 7809 7838,
    .addN 7837 7837 7838, .addN 7837 7837 7809, .addN 7837 7837 7832, .addN 7837 7837 7811,
    .addN 7833 7837 7837, .addN 7834 7833 7833, .addN 7834 7834 7811, .constN 7813 0]

/-- The dart `i = r7813`: `WT[i] = PH[i] := N · CP[i] + L₀ + WW[i] - B₀`. -/
def srDBody : Stmt :=
  block [.addN 7823 7841 7813, .loadN 7823 7823, .mulN 7823 7820 7823,
    .addN 7824 7805 7813, .loadN 7824 7824, .addN 7824 7824 7816, .subN 7824 7824 7806,
    .addN 7823 7823 7824, .addN 7825 7810 7813, .storeN 7825 7823,
    .addN 7825 7843 7813, .storeN 7825 7823, .addN 7813 7813 7811]

def srD : Stmt := .whileLtN 7813 7800 srDBody

/-- **The real start of the s-t flow on natural words.** -/
def srProg : Stmt :=
  .seq srInit (.seq srA (.seq srC1 (.seq srB (.seq srC2a (.seq srC2b srD)))))

/-- **`srProg` has no real instruction and no real test** (checked by the kernel). -/
theorem srProg_natOnly : Klein.natOnly srProg = true := by kernel_rfl


/-! ### The data in memory -/

/-- The layout: the input arrays below `W` and apart from the output `[Ob, Ob + 5 nD + 3)`. -/
structure SrLay (nD Cb Xb Yb RVb Wb Ob W : ℕ) : Prop where
  wC : Cb + nD ≤ W
  wX : Xb + nD ≤ W
  wY : Yb + nD ≤ W
  wR : RVb + nD ≤ W
  wW : Wb + nD ≤ W
  wO : Ob + 5 * nD + 3 ≤ W
  dC : Cb + nD ≤ Ob ∨ Ob + 5 * nD + 3 ≤ Cb
  dX : Xb + nD ≤ Ob ∨ Ob + 5 * nD + 3 ≤ Xb
  dY : Yb + nD ≤ Ob ∨ Ob + 5 * nD + 3 ≤ Yb
  dR : RVb + nD ≤ Ob ∨ Ob + 5 * nD + 3 ≤ RVb
  dW : Wb + nD ≤ Ob ∨ Ob + 5 * nD + 3 ≤ Wb

/-- The inputs of `srProg` in the registers and the memory. -/
structure SrIn (p : SrD) (Cb Xb Yb RVb Wb Ob : ℕ) (c : Config) : Prop where
  r00 : c.nreg 7800 = p.nD
  r01 : c.nreg 7801 = Cb
  r02 : c.nreg 7802 = Xb
  r03 : c.nreg 7803 = Yb
  r04 : c.nreg 7804 = RVb
  r05 : c.nreg 7805 = Wb
  r06 : c.nreg 7806 = p.B0
  r07 : c.nreg 7807 = p.nF
  r08 : c.nreg 7808 = p.nV
  r09 : c.nreg 7809 = p.n
  r10 : c.nreg 7810 = Ob
  mC : ∀ i < p.nD, c.nmem (Cb + i) = p.C i
  mX : ∀ i < p.nD, c.nmem (Xb + i) = p.XT i
  mY : ∀ i < p.nD, c.nmem (Yb + i) = p.YT i
  mR : ∀ i < p.nD, c.nmem (RVb + i) = p.RV i
  mW : ∀ i < p.nD, c.nmem (Wb + i) = p.WW i

variable {p : SrD} {Cb Xb Yb RVb Wb Ob : ℕ}

/-- Close the conjuncts of a postcondition: equalities, bounds and register frames. -/
macro "sr_fin" : tactic =>
  `(tactic| (and_intros <;> first | rfl | trivial | omega | (intros; trivial) |
    (intros; simp only [upd_apply]; split_ifs <;> first | omega | rfl) | skip))

theorem SrIn.frame {c c' : Config} (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W)
    (h : SrIn p Cb Xb Yb RVb Wb Ob c) (hn : ∀ r, r ≤ 7810 → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < Ob ∨ Ob + 5 * p.nD + 3 ≤ a → c'.nmem a = c.nmem a) :
    SrIn p Cb Xb Yb RVb Wb Ob c' := by
  have := hL.dC; have := hL.dX; have := hL.dY; have := hL.dR; have := hL.dW
  exact ⟨(hn _ (by omega)).trans h.r00, (hn _ (by omega)).trans h.r01,
    (hn _ (by omega)).trans h.r02, (hn _ (by omega)).trans h.r03,
    (hn _ (by omega)).trans h.r04, (hn _ (by omega)).trans h.r05,
    (hn _ (by omega)).trans h.r06, (hn _ (by omega)).trans h.r07,
    (hn _ (by omega)).trans h.r08, (hn _ (by omega)).trans h.r09,
    (hn _ (by omega)).trans h.r10,
    fun i hi => (hm _ (by omega)).trans (h.mC i hi), fun i hi => (hm _ (by omega)).trans (h.mX i hi),
    fun i hi => (hm _ (by omega)).trans (h.mY i hi), fun i hi => (hm _ (by omega)).trans (h.mR i hi),
    fun i hi => (hm _ (by omega)).trans (h.mW i hi)⟩

/-! ### The first phases -/

theorem srInit_exec (h45 : 4 * p.nF + 5 ≤ W) (hL0 : p.L0 ≤ W) (c : Config)
    (hc : WordsBounded W c) (h07 : c.nreg 7807 = p.nF) (h08 : c.nreg 7808 = p.nV) :
    ∃ c' t, Exec P W srInit c c' t ∧ t ≤ 10 ∧
      (c'.nreg 7811 = 1 ∧ c'.nreg 7812 = 0 ∧ c'.nreg 7813 = 0 ∧ c'.nreg 7814 = 0 ∧
        c'.nreg 7815 = 0 ∧ c'.nreg 7816 = p.L0 ∧
        (∀ r, r < 7811 ∨ 7819 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold SrD.L0 at hL0
  unfold srInit
  exec_block
  all_goals try ((try config_simp); (try simp only [h07, h08]); omega)
  config_simp
  simp only [h07, h08]
  refine ⟨le_rfl, rfl, fun r hr => ?_⟩
  simp only [upd_apply]
  split_ifs <;> first | omega | rfl


lemma psum_le (f : ℕ → ℕ) {k n : ℕ} (h : k ≤ n) : ∑ i ∈ range k, f i ≤ ∑ i ∈ range n, f i :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

theorem srA_exec (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W) (hS : p.S ≤ W) (hE : p.E ≤ W)
    (hLW : ∀ i < p.nD, p.L0 + p.WW i ≤ W) (c : Config) (hc : WordsBounded W c)
    (hI : SrIn p Cb Xb Yb RVb Wb Ob c) (h11 : c.nreg 7811 = 1) (h13 : c.nreg 7813 = 0)
    (h14 : c.nreg 7814 = 0) (h15 : c.nreg 7815 = 0) (h16 : c.nreg 7816 = p.L0) :
    ∃ c' t, Exec P W srA c c' t ∧ t ≤ 11 * p.nD + 2 ∧
      (c'.nreg 7814 = p.S ∧ c'.nreg 7815 = p.E ∧
        (∀ r, r ≤ 7812 ∨ r = 7816 ∨ 7818 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wC; have := hL.wW
  let J : ℕ → Config → Prop := fun i c' =>
    c'.nreg 7814 = ∑ j ∈ range i, p.C j ∧ c'.nreg 7815 = ∑ j ∈ range i, p.ep j ∧
      (∀ r, r ≤ 7812 ∨ r = 7816 ∨ 7818 ≤ r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 7813) (bR := 7800) (body := srABody) J (K := 9)
    (n := p.nD) c hc h13 hI.r00 ⟨by simp [h14], by simp [h15], fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
    (fun i c₁ hi hw ha hb ⟨g14, g15, gn, gnm, gr, grm, go⟩ => by
      have e01 : c₁.nreg 7801 = Cb := (gn 7801 (by omega)).trans hI.r01
      have e05 : c₁.nreg 7805 = Wb := (gn 7805 (by omega)).trans hI.r05
      have e06 : c₁.nreg 7806 = p.B0 := (gn 7806 (by omega)).trans hI.r06
      have e11 : c₁.nreg 7811 = 1 := (gn 7811 (by omega)).trans h11
      have e16 : c₁.nreg 7816 = p.L0 := (gn 7816 (by omega)).trans h16
      have xc : c₁.nmem (Cb + i) = p.C i := by rw [gnm]; exact hI.mC i hi
      have xw : c₁.nmem (Wb + i) = p.WW i := by rw [gnm]; exact hI.mW i hi
      have b1 : ∑ j ∈ range (i + 1), p.C j ≤ W := (psum_le p.C (by omega)).trans hS
      have b2 : ∑ j ∈ range (i + 1), p.ep j ≤ W := (psum_le p.ep (by omega)).trans hE
      rw [Finset.sum_range_succ] at b1 b2
      have b3 := hLW i hi
      have b2' : ∑ j ∈ range i, p.ep j + (p.WW i + p.L0 - p.B0) ≤ W := by
        have : p.ep i = p.WW i + p.L0 - p.B0 := by simp only [SrD.ep]; omega
        omega
      unfold srABody
      exec_block
      all_goals try
        ((try config_simp); (try simp only [e01, e05, e06, e11, e16, ha, xc, xw, g14, g15]); omega)
      dsimp only [J]
      config_simp
      simp only [e01, e05, e06, e11, e16, ha, xc, xw, g14, g15]
      refine ⟨le_rfl, trivial, hb, (Finset.sum_range_succ _ _).symm, ?_, fun r hr => ?_, gnm, gr,
        grm, go⟩
      · rw [Finset.sum_range_succ]; simp only [SrD.ep]; omega
      · simp only [upd_apply]
        split_ifs <;> first | omega | exact gn r hr)) ?_
  intro c₂ k₂ hk₂ _ ⟨_, g14, g15, gn, gnm, gr, grm, go⟩
  exact ⟨by omega, g14, g15, gn, gnm, gr, grm, go⟩


theorem srC1_exec (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W) (hlex : p.N ≤ W) (hF : p.nF + 1 ≤ W)
    (c : Config) (hc : WordsBounded W c) (hI : SrIn p Cb Xb Yb RVb Wb Ob c)
    (h11 : c.nreg 7811 = 1) (h15 : c.nreg 7815 = p.E) :
    ∃ c' t, Exec P W srC1 c c' t ∧ t ≤ 13 ∧
      (c'.nreg 7822 = p.lex ∧ c'.nreg 7820 = p.N ∧ c'.nreg 7821 = 0 ∧ c'.nreg 7813 = 0 ∧
        c'.nreg 7841 = Ob + 3 * p.nD + 3 ∧ c'.nreg 7842 = Ob + 4 * p.nD + 3 ∧
        c'.nreg 7843 = Ob + p.nD ∧
        (∀ r, r ≤ 7812 ∨ (7814 ≤ r ∧ r ≤ 7817) ∨ (7823 ≤ r ∧ r ≤ 7840) ∨ 7844 ≤ r →
          c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO
  have h00 := hI.r00; have h07 := hI.r07; have h10 := hI.r10
  have hN : p.N = 2 * ((p.nF + 1) * p.E) + 1 := rfl
  unfold srC1
  exec_block
  all_goals try ((try config_simp); (try simp only [h00, h07, h10, h11, h15]); omega)
  config_simp
  simp only [h00, h07, h10, h11, h15]
  rw [hN]
  sr_fin

theorem srBLd_exec (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W) (c : Config) (hc : WordsBounded W c)
    (hI : SrIn p Cb Xb Yb RVb Wb Ob c) {i : ℕ} (hi : i < p.nD) (h13 : c.nreg 7813 = i)
    (hRV : p.RV i < p.nD) :
    ∃ c' t, Exec P W srBLd c c' t ∧ t ≤ 13 ∧
      (c'.nreg 7823 = p.XT i ∧ c'.nreg 7825 = p.XT (p.RV i) ∧ c'.nreg 7826 = p.YT i ∧
        c'.nreg 7827 = p.YT (p.RV i) ∧ c'.nreg 7828 = p.C i ∧ c'.nreg 7830 = 0 ∧
        (∀ r, r < 7823 ∨ 7831 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wC; have := hL.wX; have := hL.wY; have := hL.wR
  have h01 := hI.r01; have h02 := hI.r02; have h03 := hI.r03; have h04 := hI.r04
  have xr := hI.mR i hi
  have x1 := hI.mX i hi; have x2 := hI.mX _ hRV; have y1 := hI.mY i hi; have y2 := hI.mY _ hRV
  have xc := hI.mC i hi
  unfold srBLd
  exec_block
  all_goals try ((try config_simp); (try simp only [h01, h02, h03, h04, h13, xr]); omega)
  config_simp
  simp only [h01, h02, h03, h04, h13, xr, x1, x2, y1, y2, xc]
  sr_fin

theorem srPair_exec {a b f : ℕ} (hf : f ≠ 7812) (h1W : 1 ≤ W) (c : Config) (hc : WordsBounded W c)
    (h12 : c.nreg 7812 = 0) :
    ∃ c' t, Exec P W (srPair a b f) c c' t ∧ t ≤ 4 ∧
      (c'.nreg f = (if 0 < c.nreg a ∧ 0 < c.nreg b then 1 else c.nreg f) ∧
        (∀ r, r ≠ f → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold srPair
  by_cases ha : 0 < c.nreg a
  · refine spec_ifLtN_true (by rw [h12]; exact ha) ?_
    by_cases hb : 0 < c.nreg b
    · refine spec_ifLtN_true (by rw [h12]; exact hb) ?_
      exec_block
      · omega
      config_simp
      simp only [ha, hb, and_self, ↓reduceIte]
      sr_fin
    · refine spec_ifLtN_false (by rw [h12]; exact hb) ?_
      refine spec_skip hc ?_
      simp only [ha, hb, and_false, ↓reduceIte]
      sr_fin
  · refine spec_ifLtN_false (by rw [h12]; exact ha) ?_
    refine spec_skip hc ?_
    simp only [ha, false_and, ↓reduceIte]
    sr_fin

theorem srSel_exec (hS : p.S + 1 ≤ W) (c : Config) (hc : WordsBounded W c)
    (h11 : c.nreg 7811 = 1) (h12 : c.nreg 7812 = 0) (h14 : c.nreg 7814 = p.S) :
    ∃ c' t, Exec P W srSel c c' t ∧ t ≤ 6 ∧
      (c'.nreg 7829 = (if 0 < c.nreg 7830 then p.S + 1 else if 0 < c.nreg 7826 then 0
          else c.nreg 7828) ∧
        c'.nreg 7831 = (if 0 < c.nreg 7830 then 0 else 1) ∧
        (∀ r, r ≠ 7829 → r ≠ 7831 → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  unfold srSel
  by_cases hf : 0 < c.nreg 7830
  · refine spec_ifLtN_true (by rw [h12]; exact hf) ?_
    exec_block
    all_goals try ((try config_simp); (try simp only [h11, h14]); omega)
    config_simp
    simp only [hf, ↓reduceIte, h11, h14]
    sr_fin
  · refine spec_ifLtN_false (by rw [h12]; exact hf) ?_
    refine spec_seq ?_
    exec_block
    all_goals try omega
    by_cases hy : 0 < c.nreg 7826
    · refine spec_ifLtN_true (by config_simp; rw [h12]; exact hy) ?_
      exec_block
      all_goals try omega
      config_simp
      simp only [hf, hy, ↓reduceIte]
      sr_fin
    · refine spec_ifLtN_false (by config_simp; rw [h12]; exact hy) ?_
      exec_block
      config_simp
      simp only [hf, hy, ↓reduceIte]
      sr_fin

theorem srBSt_exec (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W) (c : Config) (hc : WordsBounded W c)
    {i : ℕ} (hi : i < p.nD) (h13 : c.nreg 7813 = i) (h11 : c.nreg 7811 = 1)
    (h41 : c.nreg 7841 = Ob + 3 * p.nD + 3) (h42 : c.nreg 7842 = Ob + 4 * p.nD + 3)
    (hsum : c.nreg 7821 + c.nreg 7829 ≤ W) :
    ∃ c' t, Exec P W srBSt c c' t ∧ t ≤ 6 ∧
      (c'.nmem = upd (upd c.nmem (Ob + 3 * p.nD + 3 + i) (c.nreg 7829))
          (Ob + 4 * p.nD + 3 + i) (c.nreg 7831) ∧
        c'.nreg 7821 = c.nreg 7821 + c.nreg 7829 ∧ c'.nreg 7813 = i + 1 ∧
        (∀ r, r ≠ 7832 → r ≠ 7821 → r ≠ 7813 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO
  unfold srBSt
  exec_block
  all_goals try ((try config_simp); (try simp only [h11, h13, h41, h42]); omega)
  config_simp
  simp only [h11, h13, h41, h42]
  sr_fin


lemma flag_ins (i : ℕ) :
    (0 < (if 0 < p.YT i ∧ 0 < p.YT (p.RV i) then 1 else
      if 0 < p.XT i ∧ 0 < p.XT (p.RV i) then 1 else 0) ↔ p.ins i) := by
  unfold SrD.ins
  split_ifs <;> simp_all

theorem srBBody_exec (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W) (hS : p.S + 1 ≤ W) (c : Config)
    (hc : WordsBounded W c) (hI : SrIn p Cb Xb Yb RVb Wb Ob c) {i : ℕ} (hi : i < p.nD)
    (hRV : p.RV i < p.nD) (h11 : c.nreg 7811 = 1) (h12 : c.nreg 7812 = 0)
    (h13 : c.nreg 7813 = i) (h14 : c.nreg 7814 = p.S)
    (h41 : c.nreg 7841 = Ob + 3 * p.nD + 3) (h42 : c.nreg 7842 = Ob + 4 * p.nD + 3)
    (hsum : c.nreg 7821 + p.cr i ≤ W) :
    ∃ c' t, Exec P W srBBody c c' t ∧ t ≤ 33 ∧
      (c'.nmem = upd (upd c.nmem (Ob + 3 * p.nD + 3 + i) (p.cr i)) (Ob + 4 * p.nD + 3 + i)
          (p.rs i) ∧
        c'.nreg 7821 = c.nreg 7821 + p.cr i ∧ c'.nreg 7813 = i + 1 ∧
        (∀ r, (r < 7823 ∨ 7833 ≤ r) → r ≠ 7821 → r ≠ 7813 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have h1W : 1 ≤ W := by omega
  unfold srBBody
  refine spec_seq ?_
  refine spec_use (srBLd_exec (P := P) hL c hc hI hi h13 hRV) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a23, a25, a26, a27, a28, a30, an, anm, ar, arm, ao⟩
  refine spec_seq ?_
  refine spec_use (srPair_exec (P := P) (a := 7823) (b := 7825) (f := 7830) (by omega) h1W c₁ hw₁
    (by rw [an _ (by omega), h12])) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨b30, bn, bnm, br, brm, bo⟩
  refine spec_seq ?_
  refine spec_use (srPair_exec (P := P) (a := 7826) (b := 7827) (f := 7830) (by omega) h1W c₂ hw₂
    (by rw [bn _ (by omega), an _ (by omega), h12])) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨d30, dn, dnm, dr, drm, d_o⟩
  refine spec_seq ?_
  refine spec_use (srSel_exec (P := P) hS c₃ hw₃
    (by rw [dn _ (by omega), bn _ (by omega), an _ (by omega), h11])
    (by rw [dn _ (by omega), bn _ (by omega), an _ (by omega), h12])
    (by rw [dn _ (by omega), bn _ (by omega), an _ (by omega), h14])) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨e29, e31, en, enm, er, erm, eo⟩
  have v26 : c₃.nreg 7826 = p.YT i := by rw [dn _ (by omega), bn _ (by omega), a26]
  have v28 : c₃.nreg 7828 = p.C i := by rw [dn _ (by omega), bn _ (by omega), a28]
  have v30 : c₃.nreg 7830 = (if 0 < p.YT i ∧ 0 < p.YT (p.RV i) then 1 else
      if 0 < p.XT i ∧ 0 < p.XT (p.RV i) then 1 else 0) := by
    rw [d30, bn _ (by omega), bn _ (by omega), b30, a23, a25, a26, a27, a30]
  have hcr : c₄.nreg 7829 = p.cr i := by
    rw [e29, v30, v26, v28]
    unfold SrD.cr
    by_cases hin : p.ins i
    · simp only [(flag_ins i).2 hin, ↓reduceIte, hin]
    · have : ¬ 0 < (if 0 < p.YT i ∧ 0 < p.YT (p.RV i) then 1 else
          if 0 < p.XT i ∧ 0 < p.XT (p.RV i) then 1 else 0) := fun h => hin ((flag_ins i).1 h)
      simp only [this, ↓reduceIte, hin]
  have hrs : c₄.nreg 7831 = p.rs i := by
    rw [e31, v30]
    unfold SrD.rs
    by_cases hin : p.ins i
    · simp only [(flag_ins i).2 hin, ↓reduceIte, hin]
    · have : ¬ 0 < (if 0 < p.YT i ∧ 0 < p.YT (p.RV i) then 1 else
          if 0 < p.XT i ∧ 0 < p.XT (p.RV i) then 1 else 0) := fun h => hin ((flag_ins i).1 h)
      simp only [this, ↓reduceIte, hin]
  have k21 : c₄.nreg 7821 = c.nreg 7821 := by
    rw [en _ (by omega) (by omega), dn _ (by omega), bn _ (by omega), an _ (by omega)]
  refine spec_use (srBSt_exec (P := P) hL c₄ hw₄ hi
    (by rw [en _ (by omega) (by omega), dn _ (by omega), bn _ (by omega), an _ (by omega), h13])
    (by rw [en _ (by omega) (by omega), dn _ (by omega), bn _ (by omega), an _ (by omega), h11])
    (by rw [en _ (by omega) (by omega), dn _ (by omega), bn _ (by omega), an _ (by omega), h41])
    (by rw [en _ (by omega) (by omega), dn _ (by omega), bn _ (by omega), an _ (by omega), h42])
    (by rw [k21, hcr]; exact hsum)) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨f1, f21, f13, fn, fr, frm, fo⟩
  refine ⟨by omega, ?_, by rw [f21, k21, hcr], f13, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · rw [f1, hcr, hrs, enm, dnm, bnm, anm]
  · rw [fn r (by omega) h2 h3, en r (by omega) (by omega), dn r (by omega), bn r (by omega),
      an r (by omega)]
  · rw [fr, er, dr, br, ar]
  · rw [frm, erm, drm, brm, arm]
  · rw [fo, eo, d_o, bo, ao]


theorem srB_exec (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W) (hS : p.S + 1 ≤ W) (hSC : p.SC ≤ W)
    (hRV : ∀ i < p.nD, p.RV i < p.nD) (c : Config) (hc : WordsBounded W c)
    (hI : SrIn p Cb Xb Yb RVb Wb Ob c) (h11 : c.nreg 7811 = 1) (h12 : c.nreg 7812 = 0)
    (h13 : c.nreg 7813 = 0) (h14 : c.nreg 7814 = p.S) (h21 : c.nreg 7821 = 0)
    (h41 : c.nreg 7841 = Ob + 3 * p.nD + 3) (h42 : c.nreg 7842 = Ob + 4 * p.nD + 3) :
    ∃ c' t, Exec P W srB c c' t ∧ t ≤ 35 * p.nD + 2 ∧
      ((∀ j < p.nD, c'.nmem (Ob + 3 * p.nD + 3 + j) = p.cr j ∧
          c'.nmem (Ob + 4 * p.nD + 3 + j) = p.rs j) ∧
        (∀ a, a < Ob + 3 * p.nD + 3 ∨ Ob + 5 * p.nD + 3 ≤ a → c'.nmem a = c.nmem a) ∧
        c'.nreg 7821 = p.SC ∧
        (∀ r, (r < 7823 ∨ 7833 ≤ r) → r ≠ 7821 → r ≠ 7813 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ j < i, c'.nmem (Ob + 3 * p.nD + 3 + j) = p.cr j ∧
        c'.nmem (Ob + 4 * p.nD + 3 + j) = p.rs j) ∧
      (∀ a, a < Ob + 3 * p.nD + 3 ∨ Ob + 3 * p.nD + 3 + i ≤ a ∧ a < Ob + 4 * p.nD + 3 ∨
        Ob + 4 * p.nD + 3 + i ≤ a → c'.nmem a = c.nmem a) ∧
      c'.nreg 7821 = ∑ j ∈ range i, p.cr j ∧
      (∀ r, (r < 7823 ∨ 7833 ≤ r) → r ≠ 7821 → r ≠ 7813 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 7813) (bR := 7800) (body := srBBody) J (K := 33)
    (n := p.nD) c hc h13 hI.r00 ⟨fun j hj => absurd hj (by omega), fun _ _ => rfl,
      by simp [h21], fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ hi hw ha hb ⟨g, gnm, g21, gn, gr, grm, go⟩ => by
      have hI₁ : SrIn p Cb Xb Yb RVb Wb Ob c₁ :=
        hI.frame hL (fun r hr => gn r (by omega) (by omega) (by omega))
          (fun a ha' => gnm a (by omega))
      have b1 : ∑ j ∈ range (i + 1), p.cr j ≤ W := (psum_le p.cr (by omega)).trans hSC
      rw [Finset.sum_range_succ] at b1
      refine spec_use (srBBody_exec (P := P) hL hS c₁ hw hI₁ hi (hRV i hi)
        ((gn _ (by omega) (by omega) (by omega)).trans h11)
        ((gn _ (by omega) (by omega) (by omega)).trans h12) ha
        ((gn _ (by omega) (by omega) (by omega)).trans h14)
        ((gn _ (by omega) (by omega) (by omega)).trans h41)
        ((gn _ (by omega) (by omega) (by omega)).trans h42) (by rw [g21]; exact b1)) ?_
      intro c₂ k₂ hk₂ hw₂ ⟨f1, f21, f13, fn, fr, frm, fo⟩
      refine ⟨hk₂, f13, by rw [fn _ (by omega) (by omega) (by omega)]; exact hb, fun j hj => ?_,
        fun a ha' => ?_, by rw [f21, g21, Finset.sum_range_succ], fun r h1 h2 h3 => ?_,
        fr.trans gr, frm.trans grm, fo.trans go⟩
      · rw [f1]
        by_cases hji : j = i
        · subst hji
          simp only [upd_apply, show Ob + 3 * p.nD + 3 + j ≠ Ob + 4 * p.nD + 3 + j by omega,
            ↓reduceIte, and_self]
        · simp only [upd_apply, show Ob + 3 * p.nD + 3 + j ≠ Ob + 4 * p.nD + 3 + i by omega,
            show Ob + 3 * p.nD + 3 + j ≠ Ob + 3 * p.nD + 3 + i by omega,
            show Ob + 4 * p.nD + 3 + j ≠ Ob + 4 * p.nD + 3 + i by omega,
            show Ob + 4 * p.nD + 3 + j ≠ Ob + 3 * p.nD + 3 + i by omega, ↓reduceIte]
          exact g j (by omega)
      · rw [f1]
        simp only [upd_apply]
        split_ifs
        · omega
        · omega
        · exact gnm a (by omega)
      · rw [fn r h1 h2 h3]; exact gn r h1 h2 h3)) ?_
  intro c₂ k₂ hk₂ _ ⟨_, g, gnm, g21, gn, gr, grm, go⟩
  exact ⟨by omega, g, fun a ha => gnm a (by omega), g21, gn, gr, grm, go⟩


theorem srC2a_exec (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W) (hK : p.kH0 ≤ W) (c : Config)
    (hc : WordsBounded W c) (h00 : c.nreg 7800 = p.nD) (h10 : c.nreg 7810 = Ob)
    (h11 : c.nreg 7811 = 1) (h20 : c.nreg 7820 = p.N) (h21 : c.nreg 7821 = p.SC)
    (h22 : c.nreg 7822 = p.lex) :
    ∃ c' t, Exec P W srC2a c c' t ∧ t ≤ 15 ∧
      (c'.nreg 7830 = p.kZ ∧ c'.nreg 7831 = p.kTh ∧ c'.nreg 7832 = p.kH0 ∧
        c'.nmem = upd (upd c.nmem (Ob + 3 * p.nD + 1) p.kTh) (Ob + 3 * p.nD + 2) p.kH0 ∧
        (∀ r, r < 7830 ∨ 7837 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO
  have eZ : p.kZ = p.N * p.SC + 2 * p.lex := rfl
  have eT : p.kTh = p.kZ + 1 := rfl
  have eH : p.kH0 = p.kTh + (p.nD + 2) * p.kZ := rfl
  have hZ : p.N * p.SC + p.lex + p.lex = p.kZ := by omega
  unfold srC2a
  exec_block
  all_goals try ((try config_simp); (try simp only [h00, h10, h11, h20, h21, h22, hZ]); omega)
  config_simp
  simp only [h00, h10, h11, h20, h21, h22, hZ]
  rw [← eT, ← eH]
  sr_fin
  all_goals (funext a; simp only [upd_apply]; split_ifs <;> first | omega | rfl)

/-- The intermediate values of `pstVb` are at most `pstVb`. -/
theorem vb_bounds {n cD cF cV K : ℕ} (hn : 1 ≤ n) (hK : 1 ≤ K) (hFV : cF + cV ≤ n) :
    cF + cV ≤ STFlow.pstVb n cD cF cV K ∧ 4 * (cF + cV) ≤ STFlow.pstVb n cD cF cV K ∧ 4 * (cF + cV) * K ≤ STFlow.pstVb n cD cF cV K ∧
      n * (4 * (cF + cV) * K) ≤ STFlow.pstVb n cD cF cV K ∧ 2 * n ≤ STFlow.pstVb n cD cF cV K ∧ 2 * n * K ≤ STFlow.pstVb n cD cF cV K ∧ 2 * n * K + n ≤ STFlow.pstVb n cD cF cV K ∧
      4 * K ≤ STFlow.pstVb n cD cF cV K ∧ 2 * n * K + n + 4 * K ≤ STFlow.pstVb n cD cF cV K ∧ cD + 2 ≤ STFlow.pstVb n cD cF cV K ∧
      (cD + 2) * (2 * n * K + n + 4 * K) ≤ STFlow.pstVb n cD cF cV K ∧
      n * (4 * (cF + cV) * K) + (cD + 2) * (2 * n * K + n + 4 * K) ≤ STFlow.pstVb n cD cF cV K ∧
      8 * cF ≤ STFlow.pstVb n cD cF cV K ∧ 8 * cF * K ≤ STFlow.pstVb n cD cF cV K ∧ n * (8 * cF * K) ≤ STFlow.pstVb n cD cF cV K ∧
      n * (4 * (cF + cV) * K) + (cD + 2) * (2 * n * K + n + 4 * K) + n * (8 * cF * K) ≤ STFlow.pstVb n cD cF cV K ∧
      n * (4 * (cF + cV) * K) + (cD + 2) * (2 * n * K + n + 4 * K) + n * (8 * cF * K) + n
        ≤ STFlow.pstVb n cD cF cV K ∧
      n * (4 * (cF + cV) * K) + (cD + 2) * (2 * n * K + n + 4 * K) + n * (8 * cF * K) + n + K
        ≤ STFlow.pstVb n cD cF cV K ∧ 8 ≤ STFlow.pstVb n cD cF cV K := by
  have eV : STFlow.pstVb n cD cF cV K = n * (4 * (cF + cV) * K) + (cD + 2) * (2 * n * K + n + 4 * K) +
      n * (8 * cF * K) + n + K + 1 := rfl
  have m1 : 4 * (cF + cV) ≤ 4 * (cF + cV) * K := Nat.le_mul_of_pos_right _ hK
  have m2 : 4 * (cF + cV) * K ≤ n * (4 * (cF + cV) * K) := Nat.le_mul_of_pos_left _ hn
  have m3 : 2 * n ≤ 2 * n * K := Nat.le_mul_of_pos_right _ hK
  have m4 : 2 * n * K + n + 4 * K ≤ (cD + 2) * (2 * n * K + n + 4 * K) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have m5 : cD + 2 ≤ (cD + 2) * (2 * n * K + n + 4 * K) := Nat.le_mul_of_pos_right _ (by omega)
  have m6 : 8 * cF ≤ 8 * cF * K := Nat.le_mul_of_pos_right _ hK
  have m7 : 8 * cF * K ≤ n * (8 * cF * K) := Nat.le_mul_of_pos_left _ hn
  have m8 : 2 * ((2 * n * K + n + 4 * K)) ≤ (cD + 2) * (2 * n * K + n + 4 * K) :=
    Nat.mul_le_mul_right _ (by omega)
  rw [eV]
  generalize n * (4 * (cF + cV) * K) = A at *
  generalize (cD + 2) * (2 * n * K + n + 4 * K) = B at *
  generalize n * (8 * cF * K) = C at *
  generalize 4 * (cF + cV) * K = a at *
  generalize 8 * cF * K = b at *
  generalize 2 * n * K = d at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

set_option maxHeartbeats 2000000 in
theorem srC2b_exec (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W) (hMo : p.Mo ≤ W) (hn : 1 ≤ p.n)
    (hFV : p.nF + p.nV ≤ p.n) (c : Config) (hc : WordsBounded W c) (h00 : c.nreg 7800 = p.nD)
    (h07 : c.nreg 7807 = p.nF) (h08 : c.nreg 7808 = p.nV) (h09 : c.nreg 7809 = p.n)
    (h11 : c.nreg 7811 = 1) (h32 : c.nreg 7832 = p.kH0) :
    ∃ c' t, Exec P W srC2b c c' t ∧ t ≤ 28 ∧
      (c'.nreg 7833 = p.H ∧ c'.nreg 7834 = p.Mo ∧ c'.nreg 7813 = 0 ∧
        (∀ r, r < 7833 ∧ r ≠ 7813 ∨ 7840 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have hK : 1 ≤ p.kH0 := by unfold SrD.kH0 SrD.kTh; omega
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19⟩ :=
    vb_bounds (cD := p.nD) hn hK hFV
  have eH : p.H = 2 * STFlow.pstVb p.n p.nD p.nF p.nV p.kH0 := rfl
  have eM : p.Mo = 2 * p.H + 1 := rfl
  have eV : STFlow.pstVb p.n p.nD p.nF p.nV p.kH0 = p.n * (4 * (p.nF + p.nV) * p.kH0) +
      (p.nD + 2) * (2 * p.n * p.kH0 + p.n + 4 * p.kH0) + p.n * (8 * p.nF * p.kH0) + p.n +
      p.kH0 + 1 := rfl
  generalize STFlow.pstVb p.n p.nD p.nF p.nV p.kH0 = Vb at *
  unfold srC2b
  exec_block
  all_goals try ((try config_simp); (try simp only [h00, h07, h08, h09, h11, h32]); omega)
  all_goals try ((try config_simp); (try simp only [h00, h07, h08, h09, h11, h32,
    show 2 + p.nD = p.nD + 2 by omega]); omega)
  config_simp
  simp only [h00, h07, h08, h09, h11, h32, show 2 + p.nD = p.nD + 2 by omega]
  sr_fin


theorem srD_exec (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W) (hwl : ∀ i < p.nD, p.wl i ≤ W)
    (hLW : ∀ i < p.nD, p.L0 + p.WW i ≤ W) (c : Config) (hc : WordsBounded W c)
    (hI : SrIn p Cb Xb Yb RVb Wb Ob c) (h11 : c.nreg 7811 = 1) (h13 : c.nreg 7813 = 0)
    (h16 : c.nreg 7816 = p.L0) (h20 : c.nreg 7820 = p.N)
    (h41 : c.nreg 7841 = Ob + 3 * p.nD + 3) (h43 : c.nreg 7843 = Ob + p.nD)
    (hcp : ∀ j < p.nD, c.nmem (Ob + 3 * p.nD + 3 + j) = p.cr j) :
    ∃ c' t, Exec P W srD c c' t ∧ t ≤ 15 * p.nD + 2 ∧
      ((∀ j < p.nD, c'.nmem (Ob + j) = p.wl j ∧ c'.nmem (Ob + p.nD + j) = p.wl j) ∧
        (∀ a, a < Ob ∨ Ob + 2 * p.nD ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, (r < 7823 ∨ 7826 ≤ r) → r ≠ 7813 → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO; have := hL.wW; have := hL.dW
  have h05 := hI.r05; have h06 := hI.r06; have h10 := hI.r10
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ j < i, c'.nmem (Ob + j) = p.wl j ∧ c'.nmem (Ob + p.nD + j) = p.wl j) ∧
      (∀ a, a < Ob ∨ Ob + i ≤ a ∧ a < Ob + p.nD ∨ Ob + p.nD + i ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 7823 ∨ 7826 ≤ r) → r ≠ 7813 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  refine spec_use (forLoop_exec (P := P) (a := 7813) (bR := 7800) (body := srDBody) J (K := 13)
    (n := p.nD) c hc h13 hI.r00 ⟨fun j hj => absurd hj (by omega), fun _ _ => rfl,
      fun _ _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c₁ hi hw ha hb ⟨g, gnm, gn, gr, grm, go⟩ => by
      have e05 : c₁.nreg 7805 = Wb := (gn _ (by omega) (by omega)).trans h05
      have e06 : c₁.nreg 7806 = p.B0 := (gn _ (by omega) (by omega)).trans h06
      have e10 : c₁.nreg 7810 = Ob := (gn _ (by omega) (by omega)).trans h10
      have e11 : c₁.nreg 7811 = 1 := (gn _ (by omega) (by omega)).trans h11
      have e16 : c₁.nreg 7816 = p.L0 := (gn _ (by omega) (by omega)).trans h16
      have e20 : c₁.nreg 7820 = p.N := (gn _ (by omega) (by omega)).trans h20
      have e41 : c₁.nreg 7841 = Ob + 3 * p.nD + 3 := (gn _ (by omega) (by omega)).trans h41
      have e43 : c₁.nreg 7843 = Ob + p.nD := (gn _ (by omega) (by omega)).trans h43
      have xc : c₁.nmem (Ob + 3 * p.nD + 3 + i) = p.cr i := by
        rw [gnm _ (by omega)]; exact hcp i hi
      have xw : c₁.nmem (Wb + i) = p.WW i := by
        rw [gnm _ (by omega)]; exact hI.mW i hi
      have b1 := hwl i hi
      have b2 := hLW i hi
      have ewl : p.N * p.cr i + (p.WW i + p.L0 - p.B0) = p.wl i := by
        unfold SrD.wl SrD.ep; omega
      unfold SrD.wl SrD.ep at b1
      unfold srDBody
      exec_block
      all_goals try
        ((try config_simp); (try simp only [e05, e06, e10, e11, e16, e20, e41, e43, ha, xc, xw]); omega)
      config_simp
      simp only [e05, e06, e10, e11, e16, e20, e41, e43, ha, xc, xw, ewl]
      refine ⟨le_rfl, trivial, hb, fun j hj => ?_, fun a ha' => ?_, fun r h1 h2 => ?_, gr, grm,
        go⟩
      · simp only [upd_apply]
        by_cases hji : j = i
        · subst hji
          refine ⟨?_, ?_⟩ <;> split_ifs <;> first | omega | rfl
        · have hj' : j < i := by omega
          obtain ⟨g1, g2⟩ := g j hj'
          refine ⟨?_, ?_⟩ <;> split_ifs <;> first | omega | assumption
      · simp only [upd_apply]
        split_ifs <;> first | omega | exact gnm a (by omega)
      · simp only [upd_apply]
        split_ifs <;> first | omega | exact gn r h1 h2)) ?_
  intro c₂ k₂ hk₂ _ ⟨_, g, gnm, gn, gr, grm, go⟩
  exact ⟨by omega, g, fun a ha => gnm a (by omega), gn, gr, grm, go⟩


set_option maxHeartbeats 1000000 in
/-- **The real start of the s-t flow on natural words** (index level): `srProg` writes
`WT = PH = wl`, `CP = cr`, `RS = rs`, `kTh`, `kH0` at `Ob` and leaves `H`, `Mo` in `r7833`,
`r7834`, within `61 nD + 72` steps. -/
theorem srProg_exec (hL : SrLay p.nD Cb Xb Yb RVb Wb Ob W) (hRV : ∀ i < p.nD, p.RV i < p.nD)
    (h45 : 4 * p.nF + 5 ≤ W) (hL0 : p.L0 ≤ W) (hS : p.S + 1 ≤ W) (hE : p.E ≤ W)
    (hLW : ∀ i < p.nD, p.L0 + p.WW i ≤ W) (hN : p.N ≤ W) (hF : p.nF + 1 ≤ W) (hSC : p.SC ≤ W)
    (hK : p.kH0 ≤ W) (hMo : p.Mo ≤ W) (hn : 1 ≤ p.n) (hFV : p.nF + p.nV ≤ p.n)
    (hwl : ∀ i < p.nD, p.wl i ≤ W) (c : Config) (hc : WordsBounded W c)
    (hI : SrIn p Cb Xb Yb RVb Wb Ob c) :
    ∃ c' t, Exec P W srProg c c' t ∧ t ≤ 61 * p.nD + 72 ∧
      ((∀ j < p.nD, c'.nmem (Ob + j) = p.wl j ∧ c'.nmem (Ob + p.nD + j) = p.wl j ∧
          c'.nmem (Ob + 3 * p.nD + 3 + j) = p.cr j ∧ c'.nmem (Ob + 4 * p.nD + 3 + j) = p.rs j) ∧
        c'.nmem (Ob + 3 * p.nD + 1) = p.kTh ∧ c'.nmem (Ob + 3 * p.nD + 2) = p.kH0 ∧
        c'.nreg 7833 = p.H ∧ c'.nreg 7834 = p.Mo ∧
        (∀ a, a < Ob ∨ Ob + 5 * p.nD + 3 ≤ a → c'.nmem a = c.nmem a) ∧
        (∀ r, r ≤ 7810 ∨ 7844 ≤ r → c'.nreg r = c.nreg r) ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output) := by
  have := hL.wO
  unfold srProg
  refine spec_seq ?_
  refine spec_use (srInit_exec (P := P) h45 hL0 c hc hI.r07 hI.r08) ?_
  intro c₁ k₁ hk₁ hw₁ ⟨a11, a12, a13, a14, a15, a16, an, anm, ar, arm, ao⟩
  have hI₁ : SrIn p Cb Xb Yb RVb Wb Ob c₁ :=
    hI.frame hL (fun r hr => an r (by omega)) (fun a _ => by rw [anm])
  refine spec_seq ?_
  refine spec_use (srA_exec (P := P) hL (by omega) hE hLW c₁ hw₁ hI₁ a11 a13 a14 a15 a16) ?_
  intro c₂ k₂ hk₂ hw₂ ⟨b14, b15, bn, bnm, br, brm, bo⟩
  have hI₂ : SrIn p Cb Xb Yb RVb Wb Ob c₂ :=
    hI₁.frame hL (fun r hr => bn r (by omega)) (fun a _ => by rw [bnm])
  refine spec_seq ?_
  refine spec_use (srC1_exec (P := P) hL hN hF c₂ hw₂ hI₂ ((bn _ (by omega)).trans a11) b15) ?_
  intro c₃ k₃ hk₃ hw₃ ⟨d22, d20, d21, d13, d41, d42, d43, dn, dnm, dr, drm, d_o⟩
  have hI₃ : SrIn p Cb Xb Yb RVb Wb Ob c₃ :=
    hI₂.frame hL (fun r hr => dn r (by omega)) (fun a _ => by rw [dnm])
  have e11 : c₃.nreg 7811 = 1 := by rw [dn _ (by omega), bn _ (by omega), a11]
  have e12 : c₃.nreg 7812 = 0 := by rw [dn _ (by omega), bn _ (by omega), a12]
  have e14 : c₃.nreg 7814 = p.S := by rw [dn _ (by omega), b14]
  refine spec_seq ?_
  refine spec_use (srB_exec (P := P) hL hS hSC hRV c₃ hw₃ hI₃ e11 e12 d13 e14 d21 d41 d42) ?_
  intro c₄ k₄ hk₄ hw₄ ⟨f1, fnm, f21, fn, fr, frm, fo⟩
  have hI₄ : SrIn p Cb Xb Yb RVb Wb Ob c₄ :=
    hI₃.frame hL (fun r hr => fn r (by omega) (by omega) (by omega)) (fun a ha => fnm a (by omega))
  refine spec_seq ?_
  refine spec_use (srC2a_exec (P := P) hL hK c₄ hw₄ hI₄.r00 hI₄.r10
    (by rw [fn _ (by omega) (by omega) (by omega), e11])
    (by rw [fn _ (by omega) (by omega) (by omega), d20]) f21
    (by rw [fn _ (by omega) (by omega) (by omega), d22])) ?_
  intro c₅ k₅ hk₅ hw₅ ⟨g30, g31, g32, gnm, gn, gr, grm, go⟩
  have hI₅ : SrIn p Cb Xb Yb RVb Wb Ob c₅ :=
    hI₄.frame hL (fun r hr => gn r (by omega)) (fun a ha => by
      rw [gnm]; simp only [upd_apply]; split_ifs <;> first | omega | rfl)
  refine spec_seq ?_
  refine spec_use (srC2b_exec (P := P) hL hMo hn hFV c₅ hw₅ hI₅.r00 hI₅.r07 hI₅.r08 hI₅.r09
    (by rw [gn _ (by omega), fn _ (by omega) (by omega) (by omega), e11]) g32) ?_
  intro c₆ k₆ hk₆ hw₆ ⟨h33, h34, h13, hn6, hnm6, hr6, hrm6, ho6⟩
  have hI₆ : SrIn p Cb Xb Yb RVb Wb Ob c₆ :=
    hI₅.frame hL (fun r hr => hn6 r (by omega)) (fun a _ => by rw [hnm6])
  have k6 : ∀ r, 7811 ≤ r → r ≤ 7822 → r ≠ 7813 → r ≠ 7821 → c₆.nreg r = c₃.nreg r := by
    intro r h1 h2 h3 h4
    rw [hn6 r (by omega), gn r (by omega), fn r (by omega) h4 h3]
  have k6' : ∀ r, 7841 ≤ r → r ≤ 7843 → c₆.nreg r = c₃.nreg r := by
    intro r h1 h2
    rw [hn6 r (by omega), gn r (by omega), fn r (by omega) (by omega) (by omega)]
  refine spec_use (srD_exec (P := P) hL hwl hLW c₆ hw₆ hI₆ (by rw [k6 _ le_rfl (by omega)
    (by omega) (by omega), e11]) h13
    (by rw [k6 _ (by omega) (by omega) (by omega) (by omega), dn _ (by omega), bn _ (by omega),
      a16])
    (by rw [k6 _ (by omega) (by omega) (by omega) (by omega), d20])
    (by rw [k6' _ le_rfl (by omega), d41]) (by rw [k6' _ (by omega) le_rfl, d43])
    (fun j hj => by
      rw [hnm6, gnm]; simp only [upd_apply]
      split_ifs <;> first | omega | exact (f1 j hj).1)) ?_
  intro c₇ k₇ hk₇ hw₇ ⟨i1, inm, inn, ir, irm, io⟩
  have m7 : ∀ a, Ob + 2 * p.nD ≤ a → c₇.nmem a = c₅.nmem a := fun a ha => by
    rw [inm a (by omega), hnm6]
  refine ⟨by omega, fun j hj => ⟨(i1 j hj).1, (i1 j hj).2, ?_, ?_⟩, ?_, ?_, ?_, ?_,
    fun a ha => ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · rw [m7 _ (by omega), gnm]; simp only [upd_apply]
    split_ifs <;> first | omega | exact (f1 j hj).1
  · rw [m7 _ (by omega), gnm]; simp only [upd_apply]
    split_ifs <;> first | omega | exact (f1 j hj).2
  · rw [m7 _ (by omega), gnm]; simp only [upd_apply]
    split_ifs <;> first | omega | rfl
  · rw [m7 _ (by omega), gnm]; simp [upd_apply]
  · rw [inn _ (by omega) (by omega), h33]
  · rw [inn _ (by omega) (by omega), h34]
  · rw [inm a (by omega), hnm6, gnm]; simp only [upd_apply]
    split_ifs
    · omega
    · omega
    · rw [fnm a (by omega), dnm, bnm, anm]
  · rw [inn r (by omega) (by omega), hn6 r (by omega), gn r (by omega),
      fn r (by omega) (by omega) (by omega), dn r (by omega), bn r (by omega), an r (by omega)]
  · rw [ir, hr6, gr, fr, dr, br, ar]
  · rw [irm, hrm6, grm, frm, drm, brm, arm]
  · rw [io, ho6, go, fo, d_o, bo, ao]

end StEnc

end BKMNW

end PlanarFlow
