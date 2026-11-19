module

public import PlanarFlow.NegSSSP.NdFullPn

/-!
# The full branch: the node's low layout and its arrays

`fbLL` (a chain) computes the node's layout from the sizes of the two instances (left by the
side arrays in `2240 … 2247`), `m`, `w`, `b`, `k`, `B₀`: `Z` (above the split's work area and
every lower bound of `node_exec_fixedD`: `loB m w`, `bfWP b`, `2 Kwᵢ + 1`, `NNᵢ + kᵢ²`),
`M₀ = m + w + 1`, `Y = Z + 22 M₀`, `S = w + b² + k₀ + k₁`, `Pb₀ = Y + 16 S`, `Pb₁ = Pb₀ + w`,
`I0₀ = Pb₀ + 2 w`, `END₀ = I0₁`, `END₁`. **`fbC1`** copies into it the node's arrays: the tail
and head numbers (`Z`, `Z + M₀`), the sides (`Z + 2 M₀`, from the split's side array), the plain
arrays of the two instances (`I0₀`, `I0₁ = END₀`), the positions re-indexed by `J`
(`Pb₀`, `Pb₁`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

/-- The low layout of the node (scratch `2296`, `2297`). -/
def fbLL : List PcStep :=
  [(2300, [(1, .v 2242), (1, .one)], 0), (2301, [(1, .v 2246), (1, .one)], 0),
    (2302, [(1, .v 2240), (8, .v 2243)], 0), (2303, [(1, .v 2241), (2, .v 2243)], 0),
    (2304, [(1, .v 2300), (2, .v 2243)], 0),
    (2305, [(2, .v 2302), (2, .v 2303), (2, .v 2304)], 0),
    (2306, [(1, .v 2244), (8, .v 2247)], 0), (2307, [(1, .v 2245), (2, .v 2247)], 0),
    (2308, [(1, .v 2301), (2, .v 2247)], 0),
    (2309, [(2, .v 2306), (2, .v 2307), (2, .v 2308)], 0),
    (2310, [(1, .vv 2243 2243)], 0), (2311, [(1, .vv 2247 2247)], 0),
    (2312, [(1, .vv 2496 2496)], 0),
    (2313, [(1, .v 2972), (66, .v 2475), (4, .v 2474), (18, .v 2464), (8, .v 2312),
      (14, .v 2496), (28, .v 2302), (49, .v 2305), (6, .v 2243), (3, .v 2310), (28, .v 2306),
      (49, .v 2309), (6, .v 2247), (3, .v 2311), (320, .one)], 0),
    (2314, [(1, .v 2474), (1, .v 2464), (1, .one)], 0),
    (2315, [(1, .v 2313), (22, .v 2314)], 0),
    (2316, [(1, .v 2464), (1, .v 2312), (1, .v 2243), (1, .v 2247)], 0),
    (2317, [(1, .v 2315), (16, .v 2316)], 0), (2318, [(1, .v 2317), (1, .v 2464)], 0),
    (2319, [(1, .v 2317), (2, .v 2464)], 0),
    (2320, [(37, .one), (85, .v 2240), (944, .v 2243), (69, .v 2241), (81, .v 2300),
      (1, .v 2319), (1, .v 2310)], 0),
    (2321, [(37, .one), (85, .v 2244), (944, .v 2247), (69, .v 2245), (81, .v 2301),
      (1, .v 2320), (1, .v 2311)], 0),
    (2322, [(5, .v 2240), (1, .v 2243)], 0), (2323, [(5, .v 2244), (1, .v 2247)], 0),
    (2324, [(1, .v 2313), (1, .v 2314)], 0), (2325, [(1, .v 2313), (2, .v 2314)], 0),
    (2326, [(1, .v 2972), (41, .v 2475), (4, .one)], 0),
    (2327, [(1, .v 3003), (20, .v 2475), (2, .v 961), (2, .v 962)], 0),
    (2328, [(1, .v 3003), (80, .v 2475), (2, .v 961), (2, .v 962)], 0),
    (2100, [(16, .v 2475)], 0), (2101, [(1, .v 3003), (140, .v 2475)], 0),
    (2329, [(1, .v 3003), (140, .v 2475)], 0)]

set_option maxRecDepth 100000 in
theorem fbLL_wf : pcWF 2296 9600 fbLL = true := by kernel_rfl

/-- The value of `Z`. -/
def fbZv (B₀ k m w b nD₀ nV₀ nF₀ k₀ nD₁ nV₁ nF₁ k₁ : ℕ) : ℕ :=
  B₀ + 66 * k + 4 * m + 18 * w + 8 * (b * b) + 14 * b + 28 * (nD₀ + 8 * k₀) +
    49 * (2 * (nD₀ + 8 * k₀) + 2 * (nV₀ + 2 * k₀) + 2 * (nF₀ + 2 * k₀)) + 6 * k₀ +
    3 * (k₀ * k₀) + 28 * (nD₁ + 8 * k₁) +
    49 * (2 * (nD₁ + 8 * k₁) + 2 * (nV₁ + 2 * k₁) + 2 * (nF₁ + 2 * k₁)) + 6 * k₁ +
    3 * (k₁ * k₁) + 320

set_option maxHeartbeats 2000000 in
theorem fbLL_eqs {g : ℕ → ℕ} (h : PcSol fbLL g) :
    g 2300 = g 2242 + 1 ∧ g 2301 = g 2246 + 1 ∧
    g 2313 = fbZv (g 2972) (g 2475) (g 2474) (g 2464) (g 2496) (g 2240) (g 2241) (g 2242 + 1)
      (g 2243) (g 2244) (g 2245) (g 2246 + 1) (g 2247) ∧
    g 2314 = g 2474 + g 2464 + 1 ∧ g 2315 = g 2313 + 22 * g 2314 ∧
    g 2316 = g 2464 + g 2496 * g 2496 + g 2243 + g 2247 ∧
    g 2317 = g 2315 + 16 * g 2316 ∧ g 2318 = g 2317 + g 2464 ∧
    g 2319 = g 2317 + 2 * g 2464 ∧
    g 2320 = 37 + 85 * g 2240 + 944 * g 2243 + 69 * g 2241 + 81 * (g 2242 + 1) + g 2319 +
      g 2243 * g 2243 ∧
    g 2321 = 37 + 85 * g 2244 + 944 * g 2247 + 69 * g 2245 + 81 * (g 2246 + 1) + g 2320 +
      g 2247 * g 2247 ∧
    g 2322 = 5 * g 2240 + g 2243 ∧ g 2323 = 5 * g 2244 + g 2247 ∧
    g 2324 = g 2313 + g 2314 ∧ g 2325 = g 2313 + 2 * g 2314 ∧
    g 2326 = g 2972 + 41 * g 2475 + 4 ∧
    g 2327 = g 3003 + 20 * g 2475 + 2 * g 961 + 2 * g 962 ∧
    g 2328 = g 3003 + 80 * g 2475 + 2 * g 961 + 2 * g 962 ∧
    g 2100 = 16 * g 2475 ∧ g 2101 = g 3003 + 140 * g 2475 ∧
    g 2329 = g 3003 + 140 * g 2475 := by
  simp only [PcSol, fbLL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.sub_zero, one_mul, add_zero] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := h
  have hZ : g 2313 = fbZv (g 2972) (g 2475) (g 2474) (g 2464) (g 2496) (g 2240) (g 2241)
      (g 2242 + 1) (g 2243) (g 2244) (g 2245) (g 2246 + 1) (g 2247) := by
    rw [h13, h12, h5, h2, h3, h4, h0, h9, h6, h7, h8, h1, h10, h11]; unfold fbZv; ring
  refine ⟨by omega, by omega, hZ, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega⟩

theorem fbLL_notDst {r : ℕ} (h : r < 2100 ∨ (2101 < r ∧ r < 2300) ∨ 2329 < r) :
    r ∉ pcDsts fbLL := by
  simp only [pcDsts, fbLL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false]
  omega

/-- `Z` from the two instances' parameters. -/
def fbZ (B₀ k m w b : ℕ) (p₀ p₁ : FeP) : ℕ :=
  fbZv B₀ k m w b p₀.nD p₀.nV p₀.nF p₀.k p₁.nD p₁.nV p₁.nF p₁.k

/-- `S`. -/
def fbS (w b : ℕ) (p₀ p₁ : FeP) : ℕ := w + b * b + p₀.k + p₁.k

/-- `Y`. -/
def fbY (B₀ k m w b : ℕ) (p₀ p₁ : FeP) : ℕ := fbZ B₀ k m w b p₀ p₁ + 22 * (m + w + 1)

set_option maxHeartbeats 8000000 in
theorem fbLL_bound {g : ℕ → ℕ} (h : PcSol fbLL g) {W : ℕ} {p₀ p₁ : FeP}
    (e0 : g 2240 = p₀.nD) (e1 : g 2241 = p₀.nV) (e2 : g 2242 + 1 = p₀.nF) (e3 : g 2243 = p₀.k)
    (f0 : g 2244 = p₁.nD) (f1 : g 2245 = p₁.nV) (f2 : g 2246 + 1 = p₁.nF) (f3 : g 2247 = p₁.k)
    (hI0₀ : p₀.I0 = fbY (g 2972) (g 2475) (g 2474) (g 2464) (g 2496) p₀ p₁ +
      16 * fbS (g 2464) (g 2496) p₀ p₁ + 2 * g 2464) (hI0₁ : p₁.I0 = p₀.END)
    (hE : p₁.END ≤ W) (hR : g 3003 + 160 * g 2475 ≤ W) (hVF : g 961 + g 962 ≤ 2 * g 2475) :
    ∀ s ∈ fbLL, hpSum g s.2.1 ≤ W := by
  have E := fbLL_eqs h
  obtain ⟨E0, E1, EZ, E14, E15, E16, E17, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27,
    E28, E100, E101, E29⟩ := E
  have h0 := pn_end p₀
  have h1 := pn_end p₁
  have hZ : g 2313 = fbZ (g 2972) (g 2475) (g 2474) (g 2464) (g 2496) p₀ p₁ := by
    rw [EZ]; unfold fbZ; rw [← e0, ← e1, ← e2, ← e3, ← f0, ← f1, ← f2, ← f3]
  have hY : g 2315 = fbY (g 2972) (g 2475) (g 2474) (g 2464) (g 2496) p₀ p₁ := by
    rw [E15, hZ, E14]; rfl
  have hS : g 2316 = fbS (g 2464) (g 2496) p₀ p₁ := by rw [E16, e3, f3]; unfold fbS; ring
  have hI : g 2319 = p₀.I0 := by rw [E19, E17, hY, hS, hI0₀]
  have hE0 : g 2320 = p₀.END := by rw [E20, hI, h0, e0, e1, ← e2, e3]
  have hE1 : g 2321 = p₁.END := by rw [E21, hE0, h1, hI0₁, f0, f1, ← f2, f3]
  clear hZ hY hS hI hE0 EZ h0 h1 hI0₀ hI0₁
  have R := h
  simp only [PcSol, fbLL, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.sub_zero, one_mul, add_zero] at R
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩ := R
  have hW1 : g 2321 ≤ W := by rw [hE1]; exact hE
  clear hE1 hE e0 e1 e2 e3 f0 f1 f2 f3
  intro s hs
  simp only [fbLL, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
  · simp only [hpSum, hpM.ev, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      one_mul, add_zero, mul_one]
    omega

/-- **The node's low arrays.** -/
def fbC1 : Stmt :=
  .seq (pcProg 2296 fbLL) <| .seq idProg <| .seq (gaS 2474 3003 2203 2313) <|
  .seq (gaS 2474 2214 2203 2324) <| .seq (gaS 2474 2326 2203 2325) <|
  .seq (gaS 2322 2223 2329 2319) <| .seq (gaS 2323 2233 2329 2320) <|
  .seq (gaS 2464 2327 2267 2317) (gaS 2464 2328 2267 2318)

theorem fbLL_cost : pcCost fbLL = 468 := by kernel_rfl

/-- The cost of `fbC1`. -/
def fbC1Cost (k : ℕ) : ℕ := 468 + (80 * k + 4) + 3 * (9 * k + 8) + 2 * (9 * (16 * k) + 8) +
  2 * (9 * (2 * k) + 8)

/-- The layout facts of `fbC1`. -/
theorem fbC1_lay {B₀ k m w b h : ℕ} {p₀ p₁ : FeP}
    (hI0₀ : p₀.I0 = fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + 2 * w) (hI0₁ : p₁.I0 = p₀.END)
    (hEh : p₁.END ≤ h) :
    B₀ + 66 * k + 320 ≤ fbZ B₀ k m w b p₀ p₁ ∧
    fbZ B₀ k m w b p₀ p₁ + 22 * (m + w + 1) = fbY B₀ k m w b p₀ p₁ ∧
    p₀.I0 + 5 * p₀.nD + p₀.k ≤ p₀.END ∧ p₁.I0 + 5 * p₁.nD + p₁.k ≤ p₁.END ∧
    p₀.END ≤ p₁.I0 ∧ p₁.END ≤ h ∧ fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + 2 * w = p₀.I0 := by
  have h0 := pn_end p₀
  have h1 := pn_end p₁
  have hk0 : p₀.k ≤ p₀.k * p₀.k ∨ p₀.k = 0 := by
    rcases Nat.eq_zero_or_pos p₀.k with h | h
    · right; exact h
    · left; exact Nat.le_mul_of_pos_left _ h
  refine ⟨by unfold fbZ fbZv; omega, rfl, by omega, by omega, by omega, hEh, hI0₀.symm⟩

end NegSSSP

end PlanarFlow
