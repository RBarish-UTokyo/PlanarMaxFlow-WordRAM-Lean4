module

public import PlanarFlow.NegSSSP.FixPoly
public import PlanarFlow.NegSSSP.NdFullWN

/-!
# The node's word bound `WNb n L` as a polynomial expression

`WNb n L` (`NdFullWN.lean`) is a polynomial with natural coefficients in `n`, `L` and
`spWs n` (through `fbI0B`). Its pieces are mirrored verbatim on `PE` (suffix `P`), and
**`WNbE`** `= WNbP (var 0) (var 1) (var 2)` is the expression with the variables `n`, `L`,
`S = spWs n`; **`eval_WNbE`**: `PE.eval ρ WNbE = WNb (ρ 0) (ρ 1)` when `ρ 2 = spWs (ρ 0)`.
`WNbE_vl` (its variables are `< 3`) and `WNbE_cost` (its compiled program has `wnK`
instructions) are checked by the kernel.
-/

@[expose] public section

namespace PlanarFlow

namespace NegSSSP

namespace PE

/-! ### The pieces of `WNb` on expressions (verbatim copies) -/

def isoN3P (n m : PE) : PE := n * m + 1
def isoN2P (n m B : PE) : PE := isoN3P n m * (2 * B * n + 1)
def isoN1P (n m B : PE) : PE := isoN2P n m B * (n + 1)
def feIsoBP (nV nD nF W₀ : PE) : PE :=
  isoN1P nV nD nF * W₀ + isoN2P nV nD nF + isoN3P nV nD * (2 * nF) + nD
def kcnHcP (nV nF Wv k : PE) : PE := 4800 * (k + 1) * (nV + 1) * (nV + 1) * (nF + 1) * (Wv + 1)
def aOUTP (nD : PE) : PE := 3 * nD + 3
def kBLP (nD n k t L : PE) : PE :=
  9 * nD + 7 * n + k + 4 + 2 * t + aOUTP nD + k * t + n + 2 * nD + L
def fbZvP (B₀ k m w b nD₀ nV₀ nF₀ k₀ nD₁ nV₁ nF₁ k₁ : PE) : PE :=
  B₀ + 66 * k + 4 * m + 18 * w + 8 * (b * b) + 14 * b + 28 * (nD₀ + 8 * k₀) +
    49 * (2 * (nD₀ + 8 * k₀) + 2 * (nV₀ + 2 * k₀) + 2 * (nF₀ + 2 * k₀)) + 6 * k₀ +
    3 * (k₀ * k₀) + 28 * (nD₁ + 8 * k₁) +
    49 * (2 * (nD₁ + 8 * k₁) + 2 * (nV₁ + 2 * k₁) + 2 * (nF₁ + 2 * k₁)) + 6 * k₁ +
    3 * (k₁ * k₁) + 320
def bfWPP (b : PE) : PE := 8 * (b * b) + 14 * b + 12
def bfΔP (b L : PE) : PE := 2 * b * L * (2 * b + 1)
def bfXmP (b L : PE) : PE := 2 * bfΔP b L * (b + 1)
def bfBP (b L : PE) : PE := bfXmP b L + b * b * L + 2 * b + 1 + bfWPP b
def partBP (b w B : PE) : PE := (w + 3) * ((2 * b + 3) * ((b + 1) * B))
def dijBP (b w B : PE) : PE := partBP b w (partBP b w ((4 * b + 2) * B))
def restBP (b w B : PE) : PE := dijBP b w (bfBP b B)
def nodeHNP (m b w B : PE) : PE := 2 * B + 512 * restBP b w ((3 * m + 2) * B)
def fbLmBP (n L : PE) : PE := feIsoBP (5 * n) (11 * n) (5 * n) (1 + 3 * L * n)
def fbKcBP (n L : PE) : PE := kcnHcP (5 * n) (5 * n) (11 * n * fbLmBP n L) n
def fbKwBP (n : PE) : PE := kBLP (11 * n) (2 * (21 * n)) n n 0 + 16 * (2 * (21 * n) + 1)
def fbI0BP (n S : PE) : PE :=
  fbZvP S n n (2 * n) (2 * n) (3 * n) (3 * n) (3 * n) n (3 * n) (3 * n) (3 * n) n +
    22 * (n + 2 * n + 1) + 16 * (2 * n + 2 * n * (2 * n) + n + n) + 2 * (2 * n)
def fbEcP (n : PE) : PE := 37 + 85 * (3 * n) + 944 * n + 69 * (3 * n) + 81 * (3 * n) + n * n
def fbE1BP (n S : PE) : PE := fbEcP n + (fbEcP n + fbI0BP n S)
def fbWpBP (n L S : PE) : PE :=
  fbE1BP n S + fbLmBP n L + fbLmBP n L + (5 * n * fbLmBP n L + 1) + (5 * n * fbLmBP n L + 1) +
    (2 * fbKcBP n L + 1) + (2 * fbKcBP n L + 1)
def fbHBP (n L : PE) : PE := nodeHNP n (2 * n) (2 * n) (L + 1)
def fbMBP (n L : PE) : PE := 2 * fbHBP n L + 1
def fbN1BP (n : PE) : PE := isoN1P (5 * n) (11 * n) (5 * n)
def WNbP (n L S : PE) : PE :=
  (2 * fbWpBP n L S + 1 + fbMBP n L * fbMBP n L + fbMBP n L) +
    (2 * fbWpBP n L S + 2 + (2 * fbKwBP n + 1) + (2 * fbKcBP n L + 1) * (2 * fbKcBP n L + 1) +
      (2 * fbKcBP n L + 1)) +
    (2 * fbKcBP n L + 1 + 2 * fbMBP n L) + fbN1BP n + (1 + 3 * L * n) +
    (3 * (fbE1BP n S + fbE1BP n S + fbWpBP n L S + fbMBP n L + fbHBP n L + fbN1BP n +
      fbN1BP n + (1 + 3 * L * n) + (1 + 3 * L * n) + fbI0BP n S + fbI0BP n S) + 3) +
      2 * L + 9600

/-- **`WNb` as an expression** in the variables `0 = n`, `1 = L`, `2 = spWs n`. -/
def WNbE : PE := WNbP (var 0) (var 1) (var 2)

/-! ### The values -/

section
variable (ρ : ℕ → ℕ)

theorem eval_lmB (n L : PE) : eval ρ (fbLmBP n L) = fbLmB (eval ρ n) (eval ρ L) := rfl
theorem eval_kcB (n L : PE) : eval ρ (fbKcBP n L) = fbKcB (eval ρ n) (eval ρ L) := rfl
theorem eval_kwB (n : PE) : eval ρ (fbKwBP n) = fbKwB (eval ρ n) := rfl
theorem eval_i0B (n S : PE) (h : eval ρ S = Frame.spWs (eval ρ n)) :
    eval ρ (fbI0BP n S) = fbI0B (eval ρ n) := by
  unfold fbI0B; rw [← h]; rfl
theorem eval_e1B (n S : PE) (h : eval ρ S = Frame.spWs (eval ρ n)) :
    eval ρ (fbE1BP n S) = fbE1B (eval ρ n) := by
  unfold fbE1B; rw [← eval_i0B ρ n S h]; rfl
theorem eval_wpB (n L S : PE) (h : eval ρ S = Frame.spWs (eval ρ n)) :
    eval ρ (fbWpBP n L S) = fbWpB (eval ρ n) (eval ρ L) := by
  unfold fbWpB; rw [← eval_e1B ρ n S h]; rfl

theorem eval_hB (n L : PE) : eval ρ (fbHBP n L) = fbHB (eval ρ n) (eval ρ L) := rfl
theorem eval_mB (n L : PE) : eval ρ (fbMBP n L) = fbMB (eval ρ n) (eval ρ L) := rfl
theorem eval_n1B (n : PE) : eval ρ (fbN1BP n) = fbN1B (eval ρ n) := rfl
theorem eval_add' (a b : PE) : eval ρ (a + b) = eval ρ a + eval ρ b := rfl
theorem eval_mul' (a b : PE) : eval ρ (a * b) = eval ρ a * eval ρ b := rfl
theorem eval_ofNat' (k : ℕ) : eval ρ (no_index (OfNat.ofNat k : PE)) = (OfNat.ofNat k : ℕ) := rfl
theorem eval_var' (i : ℕ) : eval ρ (var i) = ρ i := rfl

/-- **The value of `WNbE`.** -/
theorem eval_WNbE (h : ρ 2 = Frame.spWs (ρ 0)) : eval ρ WNbE = WNb (ρ 0) (ρ 1) := by
  have hS : eval ρ (var 2) = Frame.spWs (eval ρ (var 0)) := h
  have h1 := eval_wpB ρ _ (var 1) _ hS
  have h2 := eval_e1B ρ _ _ hS
  have h3 := eval_i0B ρ _ _ hS
  simp only [eval_var'] at h1 h2 h3
  simp only [WNbE, WNbP, WNb, eval_add', eval_mul', eval_ofNat', h1, h2, h3, eval_kcB, eval_kwB,
    eval_hB, eval_mB, eval_n1B, eval_var']

end

theorem WNbE_vl : vl 3 WNbE = true := by decide +kernel

end PE

end NegSSSP

end PlanarFlow
