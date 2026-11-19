module

public import PlanarFlow.BKMNW.Nf9aA
public import PlanarFlow.BKMNW.Nf7fB
public import PlanarFlow.BKMNW.MsEncJ
public import PlanarFlow.BKMNW.MsCostS
public import PlanarFlow.BKMNW.CsScale

/-!
# The envelopes of `fixP7` and of the MSSP encoder as expressions

The polynomial pieces of the zero area `wzF7 MsEnc.wzm` and of the room `rOF7 C C₀ MsEnc.Rm`
(`Nf7fB`) are mirrored on `PE` (suffix `P`, verbatim copies, as `NegSSSP.FixWN` does for `WNb`);
the logarithms (`fLv`, `fP2`, `lg`, `Nat.log 2`), `spWs`, `WNb`, `fxWB` enter as variables.

* **`eval_wzmP`** (`MsEnc.wzm`), **`eval_shwMP`** (`shwM`), **`eval_rtWP`** (`rtW`),
  **`eval_wzF7P`**: `wzF7 MsEnc.wzm m Z = eval ρ (wzF7P …)` for
  `ρ = [m, Z, a, b, S, WN, FX, l1, l2]` with `a = fLv (2m)`, `b = fP2 (2m)`, `S = spWs m`,
  `WN = WNb m L`, `FX = fxWB m L`, `l1 = lg m`, `l2 = lg (2m)`, `L = rtLM m Z`;
* **`RmS_Rm_le`** (`RmS MsEnc.Rm m ≤ (m + 1)(2m + 1)(864 m + 101 + 3 KCf m m)`), **`eval_KCfP`**,
  **`eval_negTP`** (`negT 3200000 C₀`), **`rOF7_le_eval`**: `rOF7 3200000 C₀ MsEnc.Rm m Z ≤
  eval ρ (rOF7P …)` for `ρ = [m, Z, lg (2m), log₂ (20m + 1), lg m, spWs m, fxWB m L]`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace P9

open Finset NegSSSP NegSSSP.PE NegSSSP.Frame MsEnc

/-! ### The MSSP encoder's zero area `MsEnc.wzm` -/

def msThP (w nV : PE) : PE := 2 * nV * w + w + 1
def msKP (w nV : PE) : PE := 6 * nV * w + 2 * w + 1
def msLP (w nV : PE) : PE := 4 * nV * w + w + 1
def msH0P (w nV k : PE) : PE := msThP w nV + (k + 1) * ((nV + 1) * msKP w nV)
def msZP (w nV nF k : PE) : PE :=
  2 * nV * w + 2 * nF * (msH0P w nV k + msLP w nV + 2 * nV * w)
def msHIP (w nV nF k : PE) : PE :=
  30 * (msH0P w nV k + msLP w nV + w + 2 * nV * w + msZP w nV nF k) + 12 * msKP w nV +
    8 * (msLP w nV + w)
def N1MP (m : PE) : PE := isoN1P (2 * m) (5 * m) (2 * m + 1)
def wMP (m L : PE) : PE := 5 * m * (N1MP m * (L + 1))
def HMP (m L : PE) : PE := msHIP (wMP m L) (2 * m) (2 * m + 1) m
def dBP (w nD k t : PE) : PE := w + 40 * nD + 2 * k + 2 * t + t * t + 20
def kleinWNP (B n Hc : PE) : PE :=
  2 * (B + 16 * (n + 1)) + 1 + (2 * Hc + 1) * (2 * Hc + 1) + (2 * Hc + 1)
def KMeP (m L : PE) : PE := kleinWNP (dBP (wMP m L) (5 * m) m m) (20 * m + 1) (HMP m L)
def wzmP (m L : PE) : PE :=
  100 * (KMeP m L + 1) + 4 * (5 * m + 2) * (N1MP m * (L + 1)) + 100 * (m + 1) * (m + 1)

theorem eval_wzmP (ρ : ℕ → ℕ) (m L : PE) :
    eval ρ (wzmP m L) = MsEnc.wzm (eval ρ m) (eval ρ L) := rfl

/-! ### The envelopes of `fixP7` (`Nf7fB`) -/

def fpBP (AS m k : PE) : PE := (k + 2) * (2 * (AS + m * (4 * AS + 1))) + 12 * AS + 4
def fpMP (m Z : PE) : PE := fpBP (m * Z) m m
def KMfP (m Z : PE) : PE := 16 * fpMP m Z
def LMP (m Z : PE) : PE := 8 * fpMP m Z
def rtLMP (m Z : PE) : PE := m * KMfP m Z
def moOfP (b L : PE) : PE := 2 * (6 * ((b + 2) * L)) + 1
def lySbP (b k : PE) : PE := b * b + b + b + 1 + 2 * k + 2 * k
def fWP (b wb lv p2 : PE) : PE :=
  wb + (b + b + b) + b * lv * 16 + b * 16 + 16 +
    (wb + (b + b + b) + b * lv * 16 + b * lv * 16 + b * lv * 16 + p2 * 16) +
    8 * (b * lv) * lv + 4 * b + 16
def wfOfP (b k lv p2 : PE) : PE := fWP b (lySbP b k + b + b) lv p2
def shOfP (b k L lv p2 : PE) : PE :=
  (wfOfP b k lv p2 + 1) + (wfOfP b k lv p2 + 1) + moOfP b L * moOfP b L + moOfP b L
def shwMP (m Z lv p2 : PE) : PE :=
  shOfP (2 * m) m (LMP m Z) lv p2 + (2 * wfOfP (2 * m) m lv p2 + 1 +
    moOfP (2 * m) (LMP m Z) * moOfP (2 * m) (LMP m Z) + moOfP (2 * m) (LMP m Z))
def tszP (m : PE) : PE := 2 * ((m + 1) * (m + 1))

theorem eval_rtLMP (ρ : ℕ → ℕ) (m Z : PE) :
    eval ρ (rtLMP m Z) = rtLM (eval ρ m) (eval ρ Z) := rfl

theorem eval_shwMP (ρ : ℕ → ℕ) (m Z lv p2 : PE) (h1 : eval ρ lv = MsCall.fLv (2 * eval ρ m))
    (h2 : eval ρ p2 = MsCall.fP2 (2 * eval ρ m)) :
    eval ρ (shwMP m Z lv p2) = shwM (eval ρ m) (eval ρ Z) := by
  unfold shwM shOf wfOf MsCall.fW
  rw [← h1, ← h2]
  rfl

/-! ### The root word bound `rtW` -/

def spWsP (n l : PE) : PE := 204 * n + (l + 2) * (3 * n) + 7 + 66 * n + 35
def fszP (m k : PE) : PE := 6 + 5 * k + 5 * m
def rtHbP (G S WN : PE) : PE := 3 * S + G + WN + 4
def rtHP (G m k S WN : PE) : PE := rtHbP G S WN + 5 + fszP m k
def rSfP (m k S : PE) : PE := 10 + 2 * fszP m k + S + 205
def roomBP (nD RN S : PE) : PE := 37 * nD + 9 + rSfP nD nD S + RN
def fsRoomBP (m k w b S lgm lgb : PE) : PE :=
  200 * k + S + (2 * (12 * (32886 * 2372500000)) + 3000000) * (m * lgm) +
    4 * (7900 * ((b + 1) * (b + 1) * lgb)) + 300 * (b * b) + 1000 * b + 8528 + 50000 +
    5 * (m + w) + 8 * (w + 1) + 1
def fsRFP (n S lgn lg2n : PE) : PE :=
  10 + (6 + 5 * n + 5 * n) + (6 + 5 * n + 5 * n) + fsRoomBP n n (2 * n) (2 * n) S lgn lg2n
def rtWP (n L G S WN FX lgn lg2n : PE) : PE :=
  rtHP G n n S WN + (n + 1) * roomBP n (66 * n + 31 + fsRFP n S lgn lg2n) S +
    8 * n * n * (L + 1) + 7 * L + 4 * WN + S + FX + G + 1000210

theorem eval_spWsP (ρ : ℕ → ℕ) (n l : PE) (h : eval ρ l = Nat.log 2 (3 * eval ρ n)) :
    eval ρ (spWsP n l) = spWs (eval ρ n) := by
  unfold spWs
  rw [spB0_eq, ← h]
  rfl

lemma fsRoomB_eq (m k w b : ℕ) : fsRoomB m k w b =
    200 * k + spWs k + (2 * (12 * (32886 * 2372500000)) + 3000000) * (m * lg m) +
    4 * (7900 * ((b + 1) * (b + 1) * lg b)) + 300 * (b * b) + 1000 * b + 8528 + 50000 +
    5 * (m + w) + 8 * (w + 1) + 1 := by
  have h := fsKC_eq
  unfold fsKC at h
  norm_num at h
  unfold fsRoomB
  rw [sq]
  omega

theorem eval_rtWP (ρ : ℕ → ℕ) (n L S WN FX lgn lg2n : PE)
    (hS : eval ρ S = spWs (eval ρ n)) (hW : eval ρ WN = WNb (eval ρ n) (eval ρ L))
    (hF : eval ρ FX = fxWB (eval ρ n) (eval ρ L)) (h5 : eval ρ lgn = lg (eval ρ n))
    (h6 : eval ρ lg2n = lg (2 * eval ρ n)) :
    eval ρ (rtWP n L n S WN FX lgn lg2n) = rtW (eval ρ n) (eval ρ L) (eval ρ n) := by
  unfold rtW rtH rtHb roomB rSf fsRF
  rw [fsRoomB_eq, ← hS, ← hW, ← hF, ← h5, ← h6]
  rfl

/-! ### The zero area `wzF7 MsEnc.wzm` -/

def wzF7P (m Z lv p2 S WN FX lgm lg2m : PE) : PE :=
  wzmP m (2 * Z) + shwMP m Z lv p2 + (9 * m + 1 + tszP m) +
    rtWP m (rtLMP m Z) m S WN FX lgm lg2m

/-- **The value of `wzF7P`**, the variables `a … l2` given by equations (kept abstract so that the
kernel compares them syntactically; a concrete list makes the kernel unfold `WNb`). -/
theorem eval_wzF7P {m Z a b S WN FX l1 l2 : ℕ} (ha : a = MsCall.fLv (2 * m))
    (hb : b = MsCall.fP2 (2 * m)) (hS : S = spWs m) (hW : WN = WNb m (rtLM m Z))
    (hF : FX = fxWB m (rtLM m Z)) (h1 : l1 = lg m) (h2 : l2 = lg (2 * m)) :
    wzF7 MsEnc.wzm m Z = eval (lv [m, Z, a, b, S, WN, FX, l1, l2])
      (wzF7P (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) := by
  have e1 := eval_wzmP (lv [m, Z, a, b, S, WN, FX, l1, l2]) (var 0) (2 * var 1)
  have e2 := eval_shwMP (lv [m, Z, a, b, S, WN, FX, l1, l2]) (var 0) (var 1) (var 2) (var 3)
    ha hb
  have e3 := eval_rtWP (lv [m, Z, a, b, S, WN, FX, l1, l2]) (var 0) (rtLMP (var 0) (var 1))
    (var 4) (var 5) (var 6) (var 7) (var 8) hS hW hF h1 h2
  have e4 : eval (lv [m, Z, a, b, S, WN, FX, l1, l2]) (wzF7P (var 0) (var 1) (var 2) (var 3)
      (var 4) (var 5) (var 6) (var 7) (var 8)) =
      eval (lv [m, Z, a, b, S, WN, FX, l1, l2]) (wzmP (var 0) (2 * var 1)) +
      eval (lv [m, Z, a, b, S, WN, FX, l1, l2]) (shwMP (var 0) (var 1) (var 2) (var 3)) +
      (9 * m + 1 + 2 * ((m + 1) * (m + 1))) +
      eval (lv [m, Z, a, b, S, WN, FX, l1, l2]) (rtWP (var 0) (rtLMP (var 0) (var 1)) (var 0)
        (var 4) (var 5) (var 6) (var 7) (var 8)) := rfl
  rw [e4, e1, e2, e3]
  rfl

/-! ### The room `rOF7 3200000 C₀ MsEnc.Rm` -/

def lyTP (b k : PE) : PE := 4 * k + 4 * b + 2
def lyOmP (S1 b k : PE) : PE := S1 + lyTP b k
def lyAP (S1 b k : PE) : PE := lyOmP S1 b k + b * b
def lySP (S1 b k : PE) : PE := lyAP S1 b k + lySbP b k + lySbP b k
def lyObP (S1 b k : PE) : PE := lySP S1 b k + lyTP b k
def lyPP (S1 b k : PE) : PE := lyObP S1 b k + b + b
def lgTP (b k lgb : PE) : PE := 4 * (6300 * (b * (lgb * lgb) + 2 * k * lgb)) + 3
def opCostEP (l : PE) : PE := 311600 * l + 42220
def kleinOpsMP (nV nF nD nS k f t : PE) : PE :=
  6 * (nV + nF) + 2 * nD + f * t + 64 * nS + 31 * k
def kleinExtMP (nV nF nD nS k f t : PE) : PE :=
  60 * (nV + nF) + 20 * nD + 60 + 14 * (f * t) + 190 * k + 60 * nS
def kStepsP (nV nF nD nS n k f t l : PE) : PE :=
  4 * (140 * (n + 1) + 21 + kleinOpsMP nV nF nD nS k f t * opCostEP l +
    kleinExtMP nV nF nD nS k f t) + 3
def KCfP (m k l : PE) : PE :=
  kStepsP (2 * m) (2 * m + 1) (5 * m) (5 * m) (20 * m + 1) m (2 * k) (2 * k) l
def RmSP (m l : PE) : PE :=
  (m + 1) * ((2 * m + 1) * (860 * m + 100 + 2 * (2 * m) + 3 * KCfP m m l + 1))
/-- `negK 3200000`. -/
def nkP : PE := cst (32886 * 2372500000 + 3200000)
def negTP (n lgn : PE) : PE :=
  (cst (10 ^ 12) + 1 + 1000230256 + 80) *
      (10920 * nkP * n * (lgn * lgn) + 1000001 * nkP * n) + 1000230256 + 22 + (12 * n + 4610)
def valMP (m Z S FX : PE) : PE :=
  4 * (m * Z) + 20 * KMfP m Z + 2 * LMP m Z + 2 * moOfP (2 * m) (LMP m Z) + 3 * rtLMP m Z + S +
    FX + 3 * Z + m + 300
def rOF7P (m Z lg2m l lgm S FX : PE) : PE :=
  100 + 100 * m + lyPP 0 (2 * m) m + lgTP (2 * m) m lg2m + RmSP m l + negTP m lgm +
    valMP m Z S FX

theorem eval_KCfP (ρ : ℕ → ℕ) (m l : PE) (h : eval ρ l = Nat.log 2 (20 * eval ρ m + 1)) :
    eval ρ (KCfP m m l) = KCf (eval ρ m) (eval ρ m) := by
  unfold KCf MsCall.kSteps Klein.kleinOpsM Klein.kleinExtM DynTree.opCostE
  rw [← h]
  rfl

/-- **The scratch summed over `k ≤ m`, `b ≤ 2m`.** -/
theorem RmS_Rm_le (m : ℕ) : RmS MsEnc.Rm m ≤
    (m + 1) * ((2 * m + 1) * (860 * m + 100 + 2 * (2 * m) + 3 * KCf m m + 1)) := by
  unfold RmS
  have h : ∀ k ∈ range (m + 1), ∀ b ∈ range (2 * m + 1),
      MsEnc.Rm m k b ≤ 860 * m + 100 + 2 * (2 * m) + 3 * KCf m m + 1 := by
    intro k hk b hb
    have hk' := mem_range.1 hk
    have hb' := mem_range.1 hb
    have hK : KCf m k ≤ KCf m m := kSteps_le_KCf le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
      (by omega) (by omega)
    unfold MsEnc.Rm
    omega
  calc ∑ k ∈ range (m + 1), ∑ b ∈ range (2 * m + 1), MsEnc.Rm m k b
      ≤ ∑ _k ∈ range (m + 1), ∑ _b ∈ range (2 * m + 1),
          (860 * m + 100 + 2 * (2 * m) + 3 * KCf m m + 1) :=
        sum_le_sum fun k hk => sum_le_sum fun b hb => h k hk b hb
    _ = _ := by simp only [sum_const, card_range, smul_eq_mul]

theorem eval_negTP (ρ : ℕ → ℕ) (n lgn : PE) (h : eval ρ lgn = lg (eval ρ n)) (C₀ : ℕ) :
    eval ρ (negTP n lgn) = MfDrv.negT 3200000 C₀ (eval ρ n) := by
  have e : MfDrv.negT 3200000 C₀ (eval ρ n) = (10 ^ 12 + 1 + fsKC + 80) *
      (10920 * NegSSSP.negK 3200000 * eval ρ n * lg (eval ρ n) ^ 2 +
        1000001 * NegSSSP.negK 3200000 * eval ρ n) + fsKC + 22 + (12 * eval ρ n + 4610) := rfl
  rw [e, fsKC_eq, sq, ← h]
  rfl

/-- The values of the variables of `rOF7P`. -/
def rOρ (m Z : ℕ) : List ℕ :=
  [m, Z, lg (2 * m), Nat.log 2 (20 * m + 1), lg m, spWs m, fxWB m (rtLM m Z)]

theorem rOF7_le_eval (C₀ m Z : ℕ) :
    rOF7 3200000 C₀ MsEnc.Rm m Z ≤ eval (lv (rOρ m Z)) (rOF7P (var 0) (var 1) (var 2) (var 3)
      (var 4) (var 5) (var 6)) := by
  have h1 := RmS_Rm_le m
  have h2 := eval_KCfP (lv (rOρ m Z)) (var 0) (var 3) rfl
  have h3 := eval_negTP (lv (rOρ m Z)) (var 0) (var 4) rfl C₀
  have h4 : lgT (2 * m) m = eval (lv (rOρ m Z)) (lgTP (2 * var 0) (var 0) (var 2)) := by
    unfold lgT
    rw [sq]
    rfl
  have e1 : eval (lv (rOρ m Z)) (rOF7P (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) =
      100 + 100 * m + lyP 0 (2 * m) m + eval (lv (rOρ m Z)) (lgTP (2 * var 0) (var 0) (var 2)) +
      (m + 1) * ((2 * m + 1) * (860 * m + 100 + 2 * (2 * m) +
        3 * eval (lv (rOρ m Z)) (KCfP (var 0) (var 0) (var 3)) + 1)) +
      eval (lv (rOρ m Z)) (negTP (var 0) (var 4)) + valM m Z := rfl
  have e2 : rOF7 3200000 C₀ MsEnc.Rm m Z = 100 + 100 * m + lyP 0 (2 * m) m + lgT (2 * m) m +
      RmS MsEnc.Rm m + MfDrv.negT 3200000 C₀ m + valM m Z := rfl
  rw [e1, e2, ← h4, h2, h3]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left h1 _) _) _

end P9

end BKMNW

end PlanarFlow
