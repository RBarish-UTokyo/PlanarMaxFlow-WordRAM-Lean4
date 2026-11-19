module

public import PlanarFlow.BKMNW.MsValB
public import PlanarFlow.BKMNW.MsPrm

/-!
# The MSSP encoder: the layout of the scratch and the register set-ups

The scratch of an MSSP call starts at `p` (`r8009`); with `m = r8000` darts and `q = r8006`
queries, its regions (`aS … aLg`) are fixed linear forms in `p`, `m`, `q`:

| region | base | size |
|---|---|---|
| `fcProg` (`FL`, `LF`, `TA`, `TR`, `CD`, `CS`, `CN`) | `p` | `10 m` |
| `cutProg` scratch (`RE` at `+3m`, `RK` at `+4m`) | `p + 10 m` | `6 m` |
| cut outputs, `smP` scratch | `p + 16 m` | `25 m` |
| **Klein's image** `IM` | `p + 41 m` | `200 m + 20` |
| `cmProg` scratch | `p + 241 m + 20` | `5 m` |
| `GG` (two words `σ g₀`) | `p + 246 m + 20` | `2` |
| `ivProg` scratch | `p + 246 m + 22` | `60 m + 30` |
| `WM`, `CL`, `LD`, `DU` | `p + 306 m + 52` … | `5 m` each |
| Dijkstra from `g₀`, from `g₁` | `p + 326 m + 52`, `p + 532 m + 64` | `206 m + 12` each |
| `kiProg` scratch | `p + 738 m + 76` | `81 m + 18` |
| `osProg` scratch | `p + 819 m + 94` | `41 m + 6` |
| `SL`, `TI`, the log | `p + 860 m + 100`, `+ q`, `+ 2q` | |

* `msLayL`, **`msLay = hpProg 8280 8262 msLayL`** (the 17 bases into `r8280 … r8296`),
  `msLay_exec`;
* `fcL`, **`fcSet = hpProg 8150 8262 fcL`** (the registers `8150 … 8155` of `fcProg`),
  `fcSet_exec`; `ckL`, **`ckSet = hpProg 8250 8262 ckL`** (the registers `8250 … 8259` of
  `cutKin`), `ckSet_exec`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace MsEnc

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

variable {P : Input} {W : ℕ}

/-! ### The bases -/

def aZ (m p : ℕ) : ℕ := p + 10 * m
def aIM (m p : ℕ) : ℕ := p + 41 * m
def aX (m p : ℕ) : ℕ := p + 241 * m + 20
def aGG (m p : ℕ) : ℕ := p + 246 * m + 20
def aZi (m p : ℕ) : ℕ := p + 246 * m + 22
def aWM (m p : ℕ) : ℕ := p + 306 * m + 52
def aCL (m p : ℕ) : ℕ := p + 311 * m + 52
def aLD (m p : ℕ) : ℕ := p + 316 * m + 52
def aDU (m p : ℕ) : ℕ := p + 321 * m + 52
def aA0 (m p : ℕ) : ℕ := p + 326 * m + 52
def aA1 (m p : ℕ) : ℕ := p + 532 * m + 64
def aZk (m p : ℕ) : ℕ := p + 738 * m + 76
def aOs (m p : ℕ) : ℕ := p + 819 * m + 94
def aSL (m p : ℕ) : ℕ := p + 860 * m + 100
def aTI (m p q : ℕ) : ℕ := p + 860 * m + 100 + q
def aLg (m p q : ℕ) : ℕ := p + 860 * m + 100 + 2 * q

/-- The values of the 17 layout registers. -/
def msLayV (m p q : ℕ) : List ℕ :=
  [p, aZ m p, aIM m p, aX m p, aGG m p, aZi m p, aWM m p, aCL m p, aLD m p, aDU m p, aA0 m p,
    aA1 m p, aZk m p, aOs m p, aSL m p, aTI m p q, aLg m p q]

/-- **The layout as linear forms** in `r8000 = m`, `r8006 = q`, `r8009 = p`. -/
def msLayL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8009)], 0),
    ([(1, hpM.v 8009), (10, hpM.v 8000)], 0),
    ([(1, hpM.v 8009), (41, hpM.v 8000)], 0),
    ([(1, hpM.v 8009), (241, hpM.v 8000), (20, hpM.one)], 0),
    ([(1, hpM.v 8009), (246, hpM.v 8000), (20, hpM.one)], 0),
    ([(1, hpM.v 8009), (246, hpM.v 8000), (22, hpM.one)], 0),
    ([(1, hpM.v 8009), (306, hpM.v 8000), (52, hpM.one)], 0),
    ([(1, hpM.v 8009), (311, hpM.v 8000), (52, hpM.one)], 0),
    ([(1, hpM.v 8009), (316, hpM.v 8000), (52, hpM.one)], 0),
    ([(1, hpM.v 8009), (321, hpM.v 8000), (52, hpM.one)], 0),
    ([(1, hpM.v 8009), (326, hpM.v 8000), (52, hpM.one)], 0),
    ([(1, hpM.v 8009), (532, hpM.v 8000), (64, hpM.one)], 0),
    ([(1, hpM.v 8009), (738, hpM.v 8000), (76, hpM.one)], 0),
    ([(1, hpM.v 8009), (819, hpM.v 8000), (94, hpM.one)], 0),
    ([(1, hpM.v 8009), (860, hpM.v 8000), (100, hpM.one)], 0),
    ([(1, hpM.v 8009), (860, hpM.v 8000), (100, hpM.one), (1, hpM.v 8006)], 0),
    ([(1, hpM.v 8009), (860, hpM.v 8000), (100, hpM.one), (2, hpM.v 8006)], 0)]

theorem msLayL_length : msLayL.length = 17 := rfl

theorem msLay_shape : hpShape 8000 8010 860 0 msLayL = true := by decide

/-- **The layout program.** -/
def msLay : Stmt := hpProg 8280 8262 msLayL

theorem msLay_exec (c : Config) (hc : WordsBounded W c) {m p q : ℕ} (r0 : c.nreg 8000 = m)
    (r6 : c.nreg 8006 = q) (r9 : c.nreg 8009 = p) (hW : p + 860 * m + 100 + 2 * q ≤ W)
    (h860 : 860 ≤ W) :
    ∃ c', Exec P W msLay c c' (hpCost msLayL) ∧
      (∀ j < 17, c'.nreg (8280 + j) = (msLayV m p q).getD j 0) ∧
      (∀ r, (r < 8280 ∨ 8297 ≤ r) → r ≠ 8262 → r ≠ 8263 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8280 8262 msLayL :=
    hpShape_ok msLay_shape (by omega) (by omega) (by simp [msLayL_length]) (by omega)
      (by simp [msLayL_length])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) msLayL 8280 hok c hc (fun e he => by
    simp only [msLayL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r0,
        r6, r9] <;> omega)
  refine ⟨c', e, fun j hj => ?_, fun r h1 h2 h3 => f r (by rw [msLayL_length]; omega) h2 h3, mm,
    r, rm, o⟩
  rw [v j (by rw [msLayL_length]; exact hj)]
  interval_cases j <;>
    simp only [msLayL, msLayV, hpSum, hpM.ev, List.getD_cons_succ, List.getD_cons_zero,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r0, r6, r9, aZ, aIM, aX, aGG,
      aZi, aWM, aCL, aLD, aDU, aA0, aA1, aZk, aOs, aSL, aTI, aLg] <;> omega

/-! ### The registers of `fcProg` and `cutKin` -/

/-- `r8150 … r8155 := m, RVb, RTb, k, Pb, p`. -/
def fcL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8000)], 0), ([(1, hpM.v 8001)], 0), ([(1, hpM.v 8002)], 0),
    ([(1, hpM.v 8003)], 0), ([(1, hpM.v 8004)], 0), ([(1, hpM.v 8009)], 0)]

theorem fcL_shape : hpShape 8000 8010 1 0 fcL = true := by decide

def fcSet : Stmt := hpProg 8150 8262 fcL

theorem fcSet_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb k Pb p : ℕ}
    (r0 : c.nreg 8000 = m) (r1 : c.nreg 8001 = RVb) (r2 : c.nreg 8002 = RTb)
    (r3 : c.nreg 8003 = k) (r4 : c.nreg 8004 = Pb) (r9 : c.nreg 8009 = p) (hW : 1 ≤ W) :
    ∃ c', Exec P W fcSet c c' (hpCost fcL) ∧
      c'.nreg 8150 = m ∧ c'.nreg 8151 = RVb ∧ c'.nreg 8152 = RTb ∧ c'.nreg 8153 = k ∧
      c'.nreg 8154 = Pb ∧ c'.nreg 8155 = p ∧
      (∀ r, (r < 8150 ∨ 8156 ≤ r) → r ≠ 8262 → r ≠ 8263 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8150 8262 fcL :=
    hpShape_ok fcL_shape (by omega) (by omega) (by simp [fcL]) (by omega) (by simp [fcL])
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) fcL 8150 hok c hc (fun e he => by
    simp only [fcL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] <;>
      simp only [Nat.one_mul, Nat.add_zero] <;> exact hc.1 _)
  have g : ∀ j < 6, c'.nreg (8150 + j) = hpSum c.nreg (fcL.getD j ([], 0)).1 - (fcL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [fcL]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => f x (by simp [fcL]; omega) h2 h3, mm,
    r, rm, o⟩
  · have := g 0 (by omega); simp [fcL, hpSum, hpM.ev] at this; rw [this, r0]
  · have := g 1 (by omega); simp [fcL, hpSum, hpM.ev] at this; rw [this, r1]
  · have := g 2 (by omega); simp [fcL, hpSum, hpM.ev] at this; rw [this, r2]
  · have := g 3 (by omega); simp [fcL, hpSum, hpM.ev] at this; rw [this, r3]
  · have := g 4 (by omega); simp [fcL, hpSum, hpM.ev] at this; rw [this, r4]
  · have := g 5 (by omega); simp [fcL, hpSum, hpM.ev] at this; rw [this, r9]

/-- `r8250 … r8259 := m, RVb, RTb, p + 2m, p + 5m, p + 10m, p + 16m, p + 21m, p + 26m, p + 41m`. -/
def ckL : List (List (ℕ × hpM) × ℕ) :=
  [([(1, hpM.v 8000)], 0), ([(1, hpM.v 8001)], 0), ([(1, hpM.v 8002)], 0),
    ([(1, hpM.v 8009), (2, hpM.v 8000)], 0), ([(1, hpM.v 8009), (5, hpM.v 8000)], 0),
    ([(1, hpM.v 8009), (10, hpM.v 8000)], 0), ([(1, hpM.v 8009), (16, hpM.v 8000)], 0),
    ([(1, hpM.v 8009), (21, hpM.v 8000)], 0), ([(1, hpM.v 8009), (26, hpM.v 8000)], 0),
    ([(1, hpM.v 8009), (41, hpM.v 8000)], 0)]

theorem ckL_shape : hpShape 8000 8010 41 0 ckL = true := by decide

def ckSet : Stmt := hpProg 8250 8262 ckL

theorem ckSet_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb p : ℕ}
    (r0 : c.nreg 8000 = m) (r1 : c.nreg 8001 = RVb) (r2 : c.nreg 8002 = RTb)
    (r9 : c.nreg 8009 = p) (hW : p + 41 * m + 41 ≤ W) :
    ∃ c', Exec P W ckSet c c' (hpCost ckL) ∧
      c'.nreg 8250 = m ∧ c'.nreg 8251 = RVb ∧ c'.nreg 8252 = RTb ∧
      c'.nreg 8253 = p + 2 * m ∧ c'.nreg 8254 = p + 5 * m ∧ c'.nreg 8255 = p + 10 * m ∧
      c'.nreg 8256 = p + 16 * m ∧ c'.nreg 8257 = p + 21 * m ∧ c'.nreg 8258 = p + 26 * m ∧
      c'.nreg 8259 = p + 41 * m ∧
      (∀ r, (r < 8250 ∨ 8260 ≤ r) → r ≠ 8262 → r ≠ 8263 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hok : hpProgOK W 8250 8262 ckL :=
    hpShape_ok ckL_shape (by omega) (by omega) (by simp [ckL]) (by omega) (by simp [ckL])
  have h1 := hc.1 8001
  have h2 := hc.1 8002
  obtain ⟨c', e, v, f, mm, r, rm, o⟩ := hpProg_exec (I := P) ckL 8250 hok c hc (fun e he => by
    simp only [ckL, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with h | h | h | h | h | h | h | h | h | h <;> subst h <;>
      simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, r0,
        r1, r2, r9] <;> omega)
  have g : ∀ j < 10, c'.nreg (8250 + j) = hpSum c.nreg (ckL.getD j ([], 0)).1 - (ckL.getD j ([], 0)).2 :=
    fun j hj => v j (by simp [ckL]; omega)
  refine ⟨c', e, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun x h1 h2 h3 => f x (by simp [ckL]; omega) h2 h3, mm, r, rm, o⟩
  · have := g 0 (by omega); simp [ckL, hpSum, hpM.ev] at this; rw [this, r0]
  · have := g 1 (by omega); simp [ckL, hpSum, hpM.ev] at this; rw [this, r1]
  · have := g 2 (by omega); simp [ckL, hpSum, hpM.ev] at this; rw [this, r2]
  · have := g 3 (by omega); simp [ckL, hpSum, hpM.ev] at this; rw [this, r0, r9]; try ring
  · have := g 4 (by omega); simp [ckL, hpSum, hpM.ev] at this; rw [this, r0, r9]; try ring
  · have := g 5 (by omega); simp [ckL, hpSum, hpM.ev] at this; rw [this, r0, r9]; try ring
  · have := g 6 (by omega); simp [ckL, hpSum, hpM.ev] at this; rw [this, r0, r9]; try ring
  · have := g 7 (by omega); simp [ckL, hpSum, hpM.ev] at this; rw [this, r0, r9]; try ring
  · have := g 8 (by omega); simp [ckL, hpSum, hpM.ev] at this; rw [this, r0, r9]; try ring
  · have := g 9 (by omega); simp [ckL, hpSum, hpM.ev] at this; rw [this, r0, r9]; try ring

end MsEnc

end BKMNW

end PlanarFlow
