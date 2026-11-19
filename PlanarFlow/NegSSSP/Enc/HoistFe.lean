module

public import PlanarFlow.NegSSSP.Enc.NodeOne
public import PlanarFlow.NegSSSP.Enc.HoistGen

/-!
# The encoder of a one-face instance as one fixed program

Constant hoisting (`HoistGen.lean`) applied to the encoder `feProgDk p` (`FeFinalDk.lean`), run
with its registers renamed by `nbSwap` (as in `node_exec_natNNL_Dk1`):

* `hfM`: the marker instance (six distinct primes near `10⁹`; every instance-dependent constant
  of `feProgDk hfM` is then `> 10⁹`, every fixed one is `≤ 4800`), `hfTbl`: the 110 values
  of `feProgDk hfM` that depend on the instance, with their parameter numbers.
* `feVL p`: **the 110 parameters of the instance `p`** (sizes and layout bases of `FeP`:
  `p.nD`, `p.k`, …, `p.β + 4 p.N`, …, `p.Kw + 1`, `p.Kw`), `feV p j` its `j`-th entry.
* `feFixT PB = rnS nbSwap (hsHoist PB hfTbl (feProgDk hfM))`: **one statement, independent of
  the instance**, reading its 110 constants from the registers `PB + j`.
* **`feFixT_eq0`**, **`feFixT_eq1`** (kernel-checked, for `PB = 10000` and `PB = 10200`):
  `hsUn PB (feV p) (feFixT PB) = rnS nbSwap (feProgDk p)` for **every** `p : FeP`;
  `feFixT_ok0`, `feFixT_ok1`: the register condition `hsOK PB 110` (all other registers `< 3748`).
* **`feFix_exec`**: every run of `rnS nbSwap (feProgDk p)` from a configuration holding
  `feVL p` at `PB` is a run of `feFixT PB`, same configurations, same number of steps; it keeps
  the registers `≥ PB`.
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt

/-- The marker instance of the encoder. -/
def hfM : FeP := ⟨1000000007, 1000000009, 1000000021, 1000000033, 1000000087, 1000000093⟩

/-- The instance-dependent constants of `feProgDk hfM` and their parameter numbers. -/
def hfTbl : List (ℕ × ℕ) :=
  [(1000000007, 0), (1000000009, 1), (1000000021, 2), (1000000033, 3),
    (7000000131, 4), (1000000874000009481, 5), (1000000087, 6), (2000000094, 7),
    (3000000101, 8), (4000000108, 9), (5000000115, 10), (6000000122, 11),
    (9000000079, 12), (1000000883000009560, 13), (3000000039, 14), (43000000447, 15),
    (1000000892000009639, 16), (1000000895000009679, 17), (1000000898000009718, 18), (1000000901000009757, 19),
    (1000000904000009796, 20), (52000000526, 21), (1000000913000009875, 22), (1000000916000009914, 23),
    (1000000919000009953, 24), (1000000920000009976, 25), (1000000920000009974, 26), (16000000210, 27),
    (12000000118, 28), (1000000928000010096, 29), (3000000051, 30), (1000000937000010175, 31),
    (1000000955000010333, 32), (1000000958000010385, 33), (1000000961000010436, 34), (1000000964000010487, 35),
    (1000000967000010538, 36), (1000000946000010254, 37), (1000000976000010617, 38), (1000000979000010668, 39),
    (1000000982000010719, 40), (1000000985000010770, 41), (1000000988000010821, 42), (1000000991000010872, 43),
    (1000000994000010924, 44), (1000000997000010975, 45), (1000001000000011026, 46), (1000001003000011077, 47),
    (1000001006000011128, 48), (1000000922000009992, 49), (1000000925000010043, 50), (1000000928000010094, 51),
    (17000000217, 52), (15000000169, 53), (3000000050, 54), (1000001018000011258, 55),
    (1000001009000011179, 56), (61000000605, 57), (1000001192000013339, 58), (1000001195000013379, 59),
    (110000001110, 60), (140000001448, 61), (170000001786, 62), (1000000023, 63),
    (1000001042000011506, 64), (1000001045000011545, 65), (1000001033000011427, 66), (1000001048000011585, 67),
    (1000001057000011664, 68), (300000003230, 69), (299000003221, 70), (1000001084000011904, 71),
    (1000001087000011943, 72), (3000000318000003628, 73), (1000001090000011982, 74), (1000001093000012021, 75),
    (1000001096000012061, 76), (1000001099000012100, 77), (1000001102000012139, 78), (1000001105000012178, 79),
    (1000001108000012217, 80), (179000001865, 81), (209000002203, 82), (299000003217, 83),
    (3000000038, 84), (1000001111000012256, 85), (1000001120000012335, 86), (1000001138000012493, 87),
    (1000001141000012545, 88), (1000001144000012596, 89), (1000001147000012647, 90), (1000001150000012698, 91),
    (1000001129000012414, 92), (1000001159000012777, 93), (1000001162000012828, 94), (1000001165000012879, 95),
    (1000001168000012930, 96), (1000001171000012981, 97), (1000001174000013032, 98), (1000001177000013084, 99),
    (1000001180000013135, 100), (1000001183000013186, 101), (1000001186000013237, 102), (1000001189000013288, 103),
    (239000002541, 104), (269000002879, 105), (299000003219, 106), (299000003218, 107),
    (1000000867000009350, 108), (1000000867000009349, 109)]

/-- **The 110 parameters of the encoder of the instance `p`**, in the order of `hfTbl`. -/
def feVL (p : FeP) : List ℕ :=
  [p.nD,
    p.k,
    p.nV,
    p.nF,
    p.β,
    p.SL,
    p.I0,
    p.I0 + p.nD,
    p.I0 + 2 * p.nD,
    p.I0 + 3 * p.nD,
    p.I0 + 4 * p.nD,
    p.I0 + 5 * p.nD,
    p.N,
    p.ONE,
    p.A,
    p.β + 4 * p.N,
    p.ZV,
    p.ZV + p.A + 1,
    p.ZV + 2 * p.A + 1,
    p.ZV + 3 * p.A + 1,
    p.ZV + 4 * p.A + 1,
    p.β + 5 * p.N,
    p.ZV + 4 * p.A + 1 + p.N,
    p.ZV + 5 * p.A + 1 + p.N,
    p.ZV + 6 * p.A + 1 + p.N,
    p.PA + p.nV + 2,
    p.PA + p.nV,
    p.β + p.N,
    p.A + p.N,
    p.ZC,
    p.FN,
    p.ZC + p.N,
    p.ZC + 3 * p.N,
    p.ZC + 3 * p.N + p.FN + 1,
    p.ZC + 3 * p.N + 2 * p.FN + 1,
    p.ZC + 3 * p.N + 3 * p.FN + 1,
    p.ZC + 3 * p.N + 4 * p.FN + 1,
    p.ZC + 2 * p.N,
    p.ZC + 4 * p.N + 4 * p.FN + 1,
    p.ZC + 4 * p.N + 5 * p.FN + 1,
    p.ZC + 4 * p.N + 6 * p.FN + 1,
    p.ZC + 4 * p.N + 7 * p.FN + 1,
    p.ZC + 4 * p.N + 7 * p.FN + 1 + p.FN,
    p.ZC + 4 * p.N + 7 * p.FN + 1 + 2 * p.FN,
    p.ZC + 4 * p.N + 7 * p.FN + 1 + 3 * p.FN + 1,
    p.ZC + 4 * p.N + 7 * p.FN + 1 + 4 * p.FN + 1,
    p.ZC + 4 * p.N + 7 * p.FN + 1 + 5 * p.FN + 1,
    p.ZC + 4 * p.N + 7 * p.FN + 1 + 6 * p.FN + 1,
    p.ZC + 4 * p.N + 7 * p.FN + 1 + 7 * p.FN + 1,
    p.O1,
    p.O1 + p.FN,
    p.O1 + 2 * p.FN,
    p.β + p.N + p.nD,
    p.A + p.N + p.FN,
    p.FN - 1,
    p.ZI,
    p.WW,
    p.β + 6 * p.N,
    p.OS,
    p.OS + p.A + 1,
    p.β + Klein.iOB p.N p.NN p.k,
    p.β + Klein.iOE p.N p.NN p.k,
    p.β + Klein.iOL p.N p.NN p.k,
    p.nV + 2,
    p.MK,
    p.MK + p.A,
    p.RD,
    p.ISO,
    p.RK,
    p.β + Klein.iXT p.N p.NN p.k + p.k,
    p.β + Klein.iXT p.N p.NN p.k,
    p.DB,
    p.ZS,
    p.Inf,
    p.ZS + p.A,
    p.ZS + 2 * p.A,
    p.ZS + 3 * p.A + 1,
    p.ZS + 4 * p.A + 1,
    p.ZS + 5 * p.A + 1,
    p.ZS + 6 * p.A + 1,
    p.ZS + 7 * p.A + 1,
    p.β + Klein.iIV p.N p.NN p.k,
    p.β + Klein.iIT p.N p.NN p.k,
    p.β + Klein.iHD p.N p.NN p.k,
    p.A - 1,
    p.ZT,
    p.ZT + p.N,
    p.ZT + 3 * p.N,
    p.ZT + 3 * p.N + p.FN + 1,
    p.ZT + 3 * p.N + 2 * p.FN + 1,
    p.ZT + 3 * p.N + 3 * p.FN + 1,
    p.ZT + 3 * p.N + 4 * p.FN + 1,
    p.ZT + 2 * p.N,
    p.ZT + 4 * p.N + 4 * p.FN + 1,
    p.ZT + 4 * p.N + 5 * p.FN + 1,
    p.ZT + 4 * p.N + 6 * p.FN + 1,
    p.ZT + 4 * p.N + 7 * p.FN + 1,
    p.ZT + 4 * p.N + 7 * p.FN + 1 + p.FN,
    p.ZT + 4 * p.N + 7 * p.FN + 1 + 2 * p.FN,
    p.ZT + 4 * p.N + 7 * p.FN + 1 + 3 * p.FN + 1,
    p.ZT + 4 * p.N + 7 * p.FN + 1 + 4 * p.FN + 1,
    p.ZT + 4 * p.N + 7 * p.FN + 1 + 5 * p.FN + 1,
    p.ZT + 4 * p.N + 7 * p.FN + 1 + 6 * p.FN + 1,
    p.ZT + 4 * p.N + 7 * p.FN + 1 + 7 * p.FN + 1,
    p.β + Klein.iIF p.N p.NN p.k,
    p.β + Klein.iIC p.N p.NN p.k,
    p.β + Klein.iHD p.N p.NN p.k + 2,
    p.β + Klein.iHD p.N p.NN p.k + 1,
    p.Kw + 1,
    p.Kw]

/-- The `j`-th parameter. -/
def feV (p : FeP) (j : ℕ) : ℕ := (feVL p).getD j 0

theorem feVL_length (p : FeP) : (feVL p).length = 110 := rfl

/-- **The encoder as one fixed statement** reading its constants from `PB + j`, `j < 110`. -/
def feFixT (PB : ℕ) : Stmt := rnS nbSwap (hsHoist PB hfTbl (feProgDk hfM))

set_option maxRecDepth 100000 in
/-- **The fixed encoder is the encoder of every instance** (`PB = 10000`, kernel-checked). -/
theorem feFixT_eq0 (p : FeP) : hsUn 10000 (feV p) (feFixT 10000) = rnS nbSwap (feProgDk p) := by
  kernel_rfl

set_option maxRecDepth 100000 in
/-- **The fixed encoder is the encoder of every instance** (`PB = 10200`, kernel-checked). -/
theorem feFixT_eq1 (p : FeP) : hsUn 10200 (feV p) (feFixT 10200) = rnS nbSwap (feProgDk p) := by
  kernel_rfl

set_option maxRecDepth 100000 in
theorem feFixT_ok0 : hsOK 10000 110 (feFixT 10000) = true := by kernel_rfl

set_option maxRecDepth 100000 in
theorem feFixT_ok1 : hsOK 10200 110 (feFixT 10200) = true := by kernel_rfl

/-- **The fixed encoder runs as the encoder of the instance** whose parameters it holds. -/
theorem feFix_exec {I : Input} {W PB : ℕ} (hPB : PB = 10000 ∨ PB = 10200) {p : FeP}
    {c c' : Config} {t : ℕ} (h : Exec I W (rnS nbSwap (feProgDk p)) c c' t)
    (hv : ∀ j < 110, c.nreg (PB + j) = feV p j) :
    Exec I W (feFixT PB) c c' t ∧ ∀ a, PB ≤ a → c'.nreg a = c.nreg a := by
  rcases hPB with rfl | rfl
  · exact hs_exec' (feFixT_eq0 p) h feFixT_ok0 hv
  · exact hs_exec' (feFixT_eq1 p) h feFixT_ok1 hv

end NegSSSP

end PlanarFlow
