module

public import PlanarFlow.BKMNW.StCallP
public import PlanarFlow.BKMNW.StWords
public import PlanarFlow.BKMNW.StMapG
public import PlanarFlow.BKMNW.StRankM
public import PlanarFlow.BKMNW.StIsoM
public import PlanarFlow.BKMNW.StPrm

/-!
# The s-t flow call as one program: the programs, the layout, the map stage

**`stCall`** `= stPro ; stA ; stB ; stC ; stD` is one in-place call of the natural-word s-t flow
program from the frame arrays of a map numbered by `en` (the reverses `RV`, the rotation indices
`RT`, the capacities `C`, the flags `XT`, `YT` of the tails in `X`, `Y`):

* `stPro = hpProg 9160 9190 stLayL`: the layout of one call (`StL`: `n = 4m + 1`,
  `len = 37m + 13`, `W₀ = 101m + 45`, `β₀ = W₀ + 1`, the scratch addresses `Sb + …`);
* `stA = cpL ; smP ; cpL ; cmProg ; cpL ; gbProg ; cpL` (the map in Klein's encoding with compact
  node numbers and the terminal darts, in the scratch at `IMb = Sb + 3m`);
* `stB = cpL ; ivProg ; cpL ; srProg ; cpL ; mzFill` (the isolating weight, the residues at
  `β₀` in the low memory);
* `stC = stSC1 ; stdP ; cpL ; kiProg` (the initial dual tree and Klein's `KInit`);
* `stD = stD1 ; stD2 ; stD3`: `stD1 = cpL ; clpProg ; mbZeroRegs ; cpL ; sPrm ; cpL` (the clamped
  copy of the image to `ib`, the registers `< 1000` zeroed, the parameters), `stD2 = lgS 9150 9151
  sNFM` (the logged run), `stD3 = cpL ; rdbProg ; cpL ; lgClr ; cpL ; mzFill ; cpL ; mzFill` (the
  read-back, the clearing).

Registers: inputs `9100 … 9110` (`m`, `RVb`, `RTb`, `Cb`, `Xb`, `Yb`, `Sb`, `ib`, `Ob`, `Z`, `p`),
layout `9160 … 9182`, saved values `9145`, `9146`, `9183`, `9184`, loops `9120 … 9140`, log
`9150`, `9151`.

Here: `cpL` (a list of register copies, `cpL_exec`), the programs, `stPro_exec`, and the map
stage **`stA_exec`**.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace StCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP StEnc

variable {P : Input} {W : ℕ}

/-! ### Register copies -/

/-- A list of register copies `(dst, src)`. -/
def cpL : List (ℕ × ℕ) → Stmt
  | [] => .skip
  | p :: l => .seq (.instr (.copyN p.1 p.2)) (cpL l)

/-- **Register copies**: when no source is a destination and the destinations are distinct,
every destination holds its source's start value. -/
theorem cpL_exec : ∀ (l : List (ℕ × ℕ)) (hsd : ∀ p ∈ l, ∀ q ∈ l, p.2 ≠ q.1)
    (hnd : (l.map Prod.fst).Nodup) (c : Config) (hc : WordsBounded W c),
    ∃ c', Exec P W (cpL l) c c' l.length ∧ (∀ p ∈ l, c'.nreg p.1 = c.nreg p.2) ∧
      (∀ r, r ∉ l.map Prod.fst → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  | [], _, _, c, hc => ⟨c, .skip hc, fun p hp => by simp at hp, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | p :: l, hsd, hnd, c, hc => by
    have e₁ := Machine.Exec.copyN (P := P) hc p.1 p.2
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨c', e', v', f', m', r', rm', o'⟩ := cpL_exec l
      (fun a ha b hb => hsd a (by simp [ha]) b (by simp [hb])) hnd.2 _ e₁.wb_right
    refine ⟨c', (Exec.seq e₁ e').cast (by simp; omega), fun q hq => ?_, fun r hr => ?_, ?_, ?_,
      ?_, ?_⟩
    · simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · rw [f' q.1 hnd.1]; simp [upd_same]
      · rw [v' q hq]
        simp only [Config.nreg_mk]
        rw [upd_other _ _ _ (hsd q (by simp [hq]) p (by simp))]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [f' r hr.2]; simp only [Config.nreg_mk]; rw [upd_other _ _ _ hr.1]
    · rw [m']
    · rw [r']
    · rw [rm']
    · rw [o']

theorem cpL_natOnly : ∀ l : List (ℕ × ℕ), Klein.natOnly (cpL l) = true
  | [] => rfl
  | p :: l => by
    simp only [cpL, Klein.natOnly, cpL_natOnly l, Bool.and_true]
    rfl

/-! ### The layout of one call -/

/-- The layout of one call as linear forms in `m = r9100` and `Sb = r9106`. -/
def stLayL : List (List (ℕ × hpM) × ℕ) :=
  [([(4, hpM.v 9100), (1, hpM.one)], 0),
    ([(37, hpM.v 9100), (13, hpM.one)], 0),
    ([(101, hpM.v 9100), (45, hpM.one)], 0),
    ([(101, hpM.v 9100), (46, hpM.one)], 0),
    ([(1, hpM.v 9106), (3, hpM.v 9100)], 0),
    ([(1, hpM.v 9106), (4, hpM.v 9100)], 0),
    ([(1, hpM.v 9106), (7, hpM.v 9100)], 0),
    ([(1, hpM.v 9106), (8, hpM.v 9100)], 0),
    ([(1, hpM.v 9106), (15, hpM.v 9100), (1, hpM.one)], 0),
    ([(1, hpM.v 9106), (15, hpM.v 9100), (2, hpM.one)], 0),
    ([(1, hpM.v 9106), (24, hpM.v 9100), (5, hpM.one)], 0),
    ([(1, hpM.v 9106), (40, hpM.v 9100), (15, hpM.one)], 0),
    ([(1, hpM.v 9106), (41, hpM.v 9100), (15, hpM.one)], 0),
    ([(1, hpM.v 9106), (63, hpM.v 9100), (21, hpM.one)], 0),
    ([(1, hpM.v 9106), (64, hpM.v 9100), (21, hpM.one)], 0),
    ([(1, hpM.v 9106), (101, hpM.v 9100), (31, hpM.one)], 0),
    ([(1, hpM.v 9106), (105, hpM.v 9100), (33, hpM.one)], 0),
    ([(2, hpM.v 9100), (1, hpM.one)], 0),
    ([(103, hpM.v 9100), (46, hpM.one)], 0),
    ([(1, hpM.v 9100), (1, hpM.one)], 0),
    ([(107, hpM.v 9100), (49, hpM.one)], 0),
    ([(5, hpM.v 9100), (3, hpM.one)], 0),
    ([(1, hpM.one)], 0)]

theorem stLayL_length : stLayL.length = 23 := rfl

theorem stLay_shape : hpShape 9100 9107 107 0 stLayL = true := by decide

/-- **The layout program.** -/
def stPro : Stmt := hpProg 9160 9190 stLayL

/-- The size of the scratch of one call (above `Sb`). -/
def stSz (m : ℕ) : ℕ := 132 * m + 36

/-- **The layout of one call** in the registers `9160 … 9182`. -/
structure StL (f : ℕ → ℕ) (m Sb : ℕ) : Prop where
  n : f 9160 = 4 * m + 1
  len : f 9161 = 37 * m + 13
  w0 : f 9162 = 101 * m + 45
  b0 : f 9163 = 101 * m + 46
  im : f 9164 = Sb + 3 * m
  nf : f 9165 = Sb + 4 * m
  nt : f 9166 = Sb + 7 * m
  nh : f 9167 = Sb + 8 * m
  gb : f 9168 = Sb + 15 * m + 1
  gp : f 9169 = Sb + 15 * m + 2
  iv : f 9170 = Sb + 24 * m + 5
  rb : f 9171 = Sb + 40 * m + 15
  zi : f 9172 = Sb + 41 * m + 15
  wb : f 9173 = Sb + 63 * m + 21
  ab : f 9174 = Sb + 64 * m + 21
  pr : f 9175 = Sb + 101 * m + 31
  zk : f 9176 = Sb + 105 * m + 33
  of : f 9177 = 2 * m + 1
  gap : f 9178 = 103 * m + 46
  gl : f 9179 = m + 1
  ob : f 9180 = 107 * m + 49
  rl : f 9181 = 5 * m + 3
  one : f 9182 = 1

/-- The layout survives any change of registers outside `9160 … 9182`. -/
theorem StL.frame {f g : ℕ → ℕ} {m Sb : ℕ} (h : StL f m Sb)
    (hk : ∀ r, 9160 ≤ r → r ≤ 9182 → g r = f r) : StL g m Sb := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21, a22⟩ := h
  exact ⟨(hk _ (by omega) (by omega)).trans a0, (hk _ (by omega) (by omega)).trans a1,
    (hk _ (by omega) (by omega)).trans a2, (hk _ (by omega) (by omega)).trans a3,
    (hk _ (by omega) (by omega)).trans a4, (hk _ (by omega) (by omega)).trans a5,
    (hk _ (by omega) (by omega)).trans a6, (hk _ (by omega) (by omega)).trans a7,
    (hk _ (by omega) (by omega)).trans a8, (hk _ (by omega) (by omega)).trans a9,
    (hk _ (by omega) (by omega)).trans a10, (hk _ (by omega) (by omega)).trans a11,
    (hk _ (by omega) (by omega)).trans a12, (hk _ (by omega) (by omega)).trans a13,
    (hk _ (by omega) (by omega)).trans a14, (hk _ (by omega) (by omega)).trans a15,
    (hk _ (by omega) (by omega)).trans a16, (hk _ (by omega) (by omega)).trans a17,
    (hk _ (by omega) (by omega)).trans a18, (hk _ (by omega) (by omega)).trans a19,
    (hk _ (by omega) (by omega)).trans a20, (hk _ (by omega) (by omega)).trans a21,
    (hk _ (by omega) (by omega)).trans a22⟩

theorem stLay_val {f : ℕ → ℕ} {m Sb : ℕ} (h0 : f 9100 = m) (h6 : f 9106 = Sb) {g : ℕ → ℕ}
    (hv : ∀ j < 23, g (9160 + j) = hpSum f (stLayL.getD j ([], 0)).1 - (stLayL.getD j ([], 0)).2) :
    StL g m Sb := by
  have e : ∀ j < 23, ∀ v, hpSum f (stLayL.getD j ([], 0)).1 - (stLayL.getD j ([], 0)).2 = v →
      g (9160 + j) = v := fun j hj v hv' => (hv j hj).trans hv'
  refine ⟨e 0 (by omega) _ ?_, e 1 (by omega) _ ?_, e 2 (by omega) _ ?_, e 3 (by omega) _ ?_,
    e 4 (by omega) _ ?_, e 5 (by omega) _ ?_, e 6 (by omega) _ ?_, e 7 (by omega) _ ?_,
    e 8 (by omega) _ ?_, e 9 (by omega) _ ?_, e 10 (by omega) _ ?_, e 11 (by omega) _ ?_,
    e 12 (by omega) _ ?_, e 13 (by omega) _ ?_, e 14 (by omega) _ ?_, e 15 (by omega) _ ?_,
    e 16 (by omega) _ ?_, e 17 (by omega) _ ?_, e 18 (by omega) _ ?_, e 19 (by omega) _ ?_,
    e 20 (by omega) _ ?_, e 21 (by omega) _ ?_, e 22 (by omega) _ ?_⟩ <;>
  simp only [stLayL, hpSum, hpM.ev, List.getD_cons_succ, List.getD_cons_zero, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, h0, h6] <;> omega

/-- **The layout of one call.** -/
theorem stPro_exec (c : Config) (hc : WordsBounded W c) {m Sb : ℕ} (h0 : c.nreg 9100 = m)
    (h6 : c.nreg 9106 = Sb) (hW : Sb + 132 * m + 36 ≤ W) (hW' : 107 * m + 107 ≤ W) :
    ∃ c', Exec P W stPro c c' (hpCost stLayL) ∧ StL c'.nreg m Sb ∧
      (∀ r, (r < 9160 ∨ 9183 ≤ r) → r ≠ 9190 → r ≠ 9191 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 9160 9190 stLayL :=
    hpShape_ok stLay_shape (by omega) (by omega) (by simp [stLayL_length])
      (by omega) (by simp [stLayL_length])
  obtain ⟨c', e, v, f, m', r, rm, o⟩ := hpProg_exec (I := P) stLayL 9160 hok c hc (fun e he => by
    simp only [stLayL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0,
        h6] <;> omega)
  exact ⟨c', e, stLay_val h0 h6 (fun j hj => v j (by rw [stLayL_length]; exact hj)),
    fun r h1 h2 h3 => f r (by rw [stLayL_length]; omega) h2 h3, m', r, rm, o⟩

/-! ### The programs -/

def stSA1 : List (ℕ × ℕ) := [(7700, 9100), (7701, 9101), (7702, 9102), (7703, 9106), (7704, 9164)]
def stSA2 : List (ℕ × ℕ) :=
  [(7950, 9100), (7951, 9166), (7952, 9167), (7953, 9165), (7954, 9100), (7955, 9171)]
def stSA3 : List (ℕ × ℕ) := [(7850, 9100), (7851, 9104), (7852, 9105), (7853, 9168)]
def stSA4 : List (ℕ × ℕ) := [(9183, 7957), (9184, 7959)]

/-- **The map stage**: Klein's encoding of the dual with compact numbers, the terminal darts. -/
def stA : Stmt :=
  .seq (cpL stSA1) (.seq smP (.seq (cpL stSA2) (.seq cmProg (.seq (cpL stSA3)
    (.seq gbProg (cpL stSA4))))))

def stSB1 : List (ℕ × ℕ) :=
  [(7960, 9100), (7961, 9165), (7962, 9164), (7963, 9177), (7964, 9184), (7965, 9169),
    (7966, 9172), (7967, 9173), (7968, 9100)]
def stSB2 : List (ℕ × ℕ) :=
  [(7800, 9100), (7801, 9103), (7802, 9104), (7803, 9105), (7804, 9164), (7805, 9173),
    (7806, 9100), (7807, 9183), (7808, 9184), (7809, 9160), (7810, 9163)]
def stSB3 : List (ℕ × ℕ) := [(9145, 7833), (9146, 7834), (5030, 9179), (5031, 9178)]

/-- **The weight stage**: the isolating weight, the residues at `β₀`, the gap zeroed. -/
def stB : Stmt :=
  .seq (cpL stSB1) (.seq ivProg (.seq (cpL stSB2) (.seq srProg (.seq (cpL stSB3) mzFill))))

/-- The registers of Dijkstra's run (`Inf = Mo² + 1`, the root `NT[G[1]]`). -/
def stSC1 : Stmt := block [.copyN 7860 9100, .copyN 7861 9160, .copyN 7862 9166,
  .copyN 7863 9167, .copyN 7864 9163, .copyN 7865 9174, .mulN 7870 9146 9146,
  .addN 7870 7870 9182, .loadN 7871 9169, .addN 7871 9166 7871, .loadN 7871 7871]
def stSC2 : List (ℕ × ℕ) :=
  [(7980, 9100), (7981, 9166), (7982, 9165), (7983, 9164), (7984, 9170), (7985, 9160),
    (7986, 9177), (7987, 9183), (7988, 9184), (7989, 9175), (7990, 9176), (7991, 9168)]

/-- **The tree stage**: Dijkstra's distances and tight parents, Klein's `KInit`. -/
def stC : Stmt := .seq stSC1 (.seq stdP (.seq (cpL stSC2) kiProg))

def stSD1 : List (ℕ × ℕ) := [(9120, 9161), (9121, 9164), (9122, 9107), (9123, 9162)]
def stSD2 : List (ℕ × ℕ) :=
  [(8000, 9160), (8001, 9100), (8002, 9161), (8003, 9146), (8004, 9145), (8005, 9163),
    (8006, 9107), (8007, 9161)]
def stSD3 : List (ℕ × ℕ) := [(9150, 9110), (9151, 9182)]
def stSD4 : List (ℕ × ℕ) :=
  [(9130, 9100), (9131, 9180), (9132, 9108), (9133, 9109), (9134, 9145), (9135, 9146)]
def stSD5 : List (ℕ × ℕ) := [(2924, 9110), (2925, 9150), (2926, 9182)]
def stSD6 : List (ℕ × ℕ) := [(5030, 9181), (5031, 9163)]
def stSD7 : List (ℕ × ℕ) := [(5030, 9161), (5031, 9107)]

/-- The clamped image at `ib`, the registers `< 1000` zeroed, the parameters, the log registers. -/
def stD1 : Stmt :=
  .seq (cpL stSD1) <| .seq clpProg <| .seq (mbZeroRegs (List.range 1000)) <|
  .seq (cpL stSD2) <| .seq StFix.sPrm (cpL stSD3)

/-- The logged run of the fixed natural s-t flow program. -/
def stD2 : Stmt := lgS 9150 9151 StFix.sNFM

/-- The read-back and the clearing. -/
def stD3 : Stmt :=
  .seq (cpL stSD4) <| .seq rdbProg <| .seq (cpL stSD5) <| .seq lgClr <| .seq (cpL stSD6) <|
  .seq mzFill <| .seq (cpL stSD7) mzFill

/-- **The run stage**: the clamped image at `ib`, the parameters, the logged run, the read-back,
the clearing. -/
def stD : Stmt := .seq stD1 (.seq stD2 stD3)

/-- **One in-place call of the s-t flow program.** -/
def stCall : Stmt := .seq stPro (.seq stA (.seq stB (.seq stC stD)))

/-- The registers the encoders may write. -/
def EncScr (r : ℕ) : Prop :=
  r < 2600 ∨ (4900 ≤ r ∧ r < 4920) ∨ (5030 ≤ r ∧ r < 5036) ∨ (6210 ≤ r ∧ r < 6218) ∨
    (7350 ≤ r ∧ r < 7410) ∨ (7700 ≤ r ∧ r < 8012)

/-- **The scratch registers of `stCall`.** -/
def StScr (r : ℕ) : Prop := EncScr r ∨ (2900 ≤ r ∧ r < 2930) ∨ (9100 ≤ r ∧ r < 9200)

end StCall

end BKMNW

end PlanarFlow
