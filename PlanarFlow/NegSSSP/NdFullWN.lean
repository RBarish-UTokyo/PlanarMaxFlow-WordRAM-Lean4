module

public import PlanarFlow.NegSSSP.NdFullP3

/-!
# The full branch: a closed bound `WNb n L` on the node's word bound

The node of the full branch runs with a word bound `WN` that must dominate nine terms (`hWN` of
`fs_node`) and the parameter sum `hnB` (`hBN`), all depending on the two instances' parameters
`p₀`, `p₁`, the sizes `m w b`, and the weight bounds `srcW`. Every one of them is a polynomial
with natural coefficients in these quantities (monotone), and each quantity is bounded in terms
of `n` (the number of darts of the whole map) and `L` (the length bound): `nDᵢ ≤ 3n`, `kᵢ ≤ n`,
`nVᵢ, nFᵢ ≤ 3n`, `m, k ≤ n`, `w, b ≤ 2n`, `B₀ ≤ spWs n`, `srcWᵢ ≤ 1 + 3Ln`.

* monotonicity lemmas (`feIsoB_mono4`, `kcnHc_mono4`, `kBL_mono`, `fbZv_mono`, `nodeHN_mono`,
  `isoN1_mono3`);
* **`WNb n L`** (closed, polynomial in `n` and `L`) and its pieces `fbLmB`, `fbKcB`, `fbKwB`,
  `fbI0B`, `fbE1B`, `fbWpB`, `fbMB`, `fbHB`, `fbN1B`;
* **`fs_WN_le`**: under the bounds above, the nine terms of `hWN`, the sum `hnB`, `pnW`,
  `2·nodeHN + 1 + 2L + 2`, `isoN1` of both instances, `END₁` are all `≤ WNb n L`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset

/-! ### Monotonicity -/

theorem isoN1_mono3 {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    MSSP.isoN1 a b c ≤ MSSP.isoN1 a' b' c' := by
  unfold MSSP.isoN1 MSSP.isoN2 MSSP.isoN3; gcongr

theorem feIsoB_mono4 {a b c d a' b' c' d' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hd : d ≤ d') : feIsoB a b c d ≤ feIsoB a' b' c' d' := by
  unfold feIsoB MSSP.isoN1 MSSP.isoN2 MSSP.isoN3; gcongr

theorem kcnHc_mono4 {a b c d a' b' c' d' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hd : d ≤ d') : kcnHc a b c d ≤ kcnHc a' b' c' d' := by
  unfold kcnHc; gcongr

theorem kBL_mono {a b c d e a' b' c' d' e' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hd : d ≤ d') (he : e ≤ e') : Klein.kBL a b c d e ≤ Klein.kBL a' b' c' d' e' := by
  unfold Klein.kBL Klein.aOUT; gcongr

theorem nodeHN_mono {a b c d a' b' c' d' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hd : d ≤ d') : nodeHN a b c d ≤ nodeHN a' b' c' d' := by
  unfold nodeHN restB dijB partB bfB Monge.bfXm Monge.bfΔ bfWP; gcongr

theorem fbZv_mono {a b c d e f g h i j k l o a' b' c' d' e' f' g' h' i' j' k' l' o' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') (hd : d ≤ d') (he : e ≤ e') (hf : f ≤ f')
    (hg : g ≤ g') (hh : h ≤ h') (hi : i ≤ i') (hj : j ≤ j') (hk : k ≤ k') (hl : l ≤ l')
    (ho : o ≤ o') : fbZv a b c d e f g h i j k l o ≤ fbZv a' b' c' d' e' f' g' h' i' j' k' l' o' := by
  unfold fbZv; gcongr

/-! ### The closed bound -/

/-- The bound of `Lmax`. -/
def fbLmB (n L : ℕ) : ℕ := feIsoB (5 * n) (11 * n) (5 * n) (1 + 3 * L * n)

/-- The bound of `kcnHc A FN (N · Lmax) k`. -/
def fbKcB (n L : ℕ) : ℕ := kcnHc (5 * n) (5 * n) (11 * n * fbLmB n L) n

/-- The bound of `Kw`. -/
def fbKwB (n : ℕ) : ℕ := Klein.kBL (11 * n) (2 * (21 * n)) n n 0 + 16 * (2 * (21 * n) + 1)

/-- The bound of `I0₀` (and of `Pb₀`, `Pb₁`). -/
def fbI0B (n : ℕ) : ℕ :=
  fbZv (Frame.spWs n) n n (2 * n) (2 * n) (3 * n) (3 * n) (3 * n) n (3 * n) (3 * n) (3 * n) n +
    22 * (n + 2 * n + 1) + 16 * (2 * n + 2 * n * (2 * n) + n + n) + 2 * (2 * n)

/-- The growth of `END` over `I0` (`pn_end`). -/
def fbEc (n : ℕ) : ℕ := 37 + 85 * (3 * n) + 944 * n + 69 * (3 * n) + 81 * (3 * n) + n * n

/-- The bound of `END₁`. -/
def fbE1B (n : ℕ) : ℕ := fbEc n + (fbEc n + fbI0B n)

/-- The bound of `W' = pnW p₀ p₁`. -/
def fbWpB (n L : ℕ) : ℕ :=
  fbE1B n + fbLmB n L + fbLmB n L + (5 * n * fbLmB n L + 1) + (5 * n * fbLmB n L + 1) +
    (2 * fbKcB n L + 1) + (2 * fbKcB n L + 1)

/-- The bound of `H = nodeHN m b w (L + 1)`. -/
def fbHB (n L : ℕ) : ℕ := nodeHN n (2 * n) (2 * n) (L + 1)

/-- The bound of `M`. -/
def fbMB (n L : ℕ) : ℕ := 2 * fbHB n L + 1

/-- The bound of `srcN1`. -/
def fbN1B (n : ℕ) : ℕ := MSSP.isoN1 (5 * n) (11 * n) (5 * n)

/-- **The closed word bound of the full branch's node.** -/
def WNb (n L : ℕ) : ℕ :=
  (2 * fbWpB n L + 1 + fbMB n L * fbMB n L + fbMB n L) +
    (2 * fbWpB n L + 2 + (2 * fbKwB n + 1) + (2 * fbKcB n L + 1) * (2 * fbKcB n L + 1) +
      (2 * fbKcB n L + 1)) +
    (2 * fbKcB n L + 1 + 2 * fbMB n L) + fbN1B n + (1 + 3 * L * n) +
    (3 * (fbE1B n + fbE1B n + fbWpB n L + fbMB n L + fbHB n L + fbN1B n + fbN1B n +
      (1 + 3 * L * n) + (1 + 3 * L * n) + fbI0B n + fbI0B n) + 3) + 2 * L + 9600

/-! ### The terms are bounded -/

/-- The parameters of one instance are within the envelope. -/
structure FbEnv (p : FeP) (n L W₀ : ℕ) : Prop where
  nD : p.nD ≤ 3 * n
  k : p.k ≤ n
  nV : p.nV ≤ 3 * n
  nF : p.nF ≤ 3 * n
  Lm : p.Lmax = feIsoB p.A p.N p.FN W₀
  W₀ : W₀ ≤ 1 + 3 * L * n

theorem FbEnv.A_le {p : FeP} {n L W₀ : ℕ} (h : FbEnv p n L W₀) : p.A ≤ 5 * n := by
  have := h.nV; have := h.k; unfold FeP.A; omega

theorem FbEnv.N_le {p : FeP} {n L W₀ : ℕ} (h : FbEnv p n L W₀) : p.N ≤ 11 * n := by
  have := h.nD; have := h.k; unfold FeP.N; omega

theorem FbEnv.FN_le {p : FeP} {n L W₀ : ℕ} (h : FbEnv p n L W₀) : p.FN ≤ 5 * n := by
  have := h.nF; have := h.k; unfold FeP.FN; omega

theorem FbEnv.Lm_le {p : FeP} {n L W₀ : ℕ} (h : FbEnv p n L W₀) : p.Lmax ≤ fbLmB n L := by
  rw [h.Lm]; exact feIsoB_mono4 h.A_le h.N_le h.FN_le h.W₀

theorem FbEnv.Kc_le {p : FeP} {n L W₀ : ℕ} (h : FbEnv p n L W₀) :
    kcnHc p.A p.FN (p.N * p.Lmax) p.k ≤ fbKcB n L :=
  kcnHc_mono4 h.A_le h.FN_le (Nat.mul_le_mul h.N_le h.Lm_le) h.k

theorem FbEnv.Kw_le {p : FeP} {n L W₀ : ℕ} (h : FbEnv p n L W₀) : p.Kw ≤ fbKwB n := by
  have hNN : p.NN ≤ 2 * (21 * n) := by
    have := h.A_le; have := h.N_le; have := h.FN_le; unfold FeP.NN FeP.AE; omega
  unfold FeP.Kw FeP.Bw fbKwB
  have := kBL_mono (c := p.k) (d := p.k) (e := 0) (c' := n) (d' := n) (e' := 0) h.N_le hNN h.k h.k
    le_rfl
  omega

theorem FbEnv.Inf_le {p : FeP} {n L W₀ : ℕ} (h : FbEnv p n L W₀) :
    p.Inf ≤ 5 * n * fbLmB n L + 1 := by
  unfold FeP.Inf; have := Nat.mul_le_mul h.A_le h.Lm_le; omega

theorem FbEnv.N1_le {p : FeP} {n L W₀ : ℕ} (h : FbEnv p n L W₀) :
    MSSP.isoN1 p.A p.N p.FN ≤ fbN1B n :=
  isoN1_mono3 h.A_le h.N_le h.FN_le

theorem FbEnv.end_le {p : FeP} {n L W₀ : ℕ} (h : FbEnv p n L W₀) : p.END ≤ fbEc n + p.I0 := by
  rw [pn_end]; unfold fbEc
  have := Nat.mul_le_mul h.k h.k; have := h.nD; have := h.k; have := h.nV; have := h.nF; omega

/-- **The closed bound** (see the module docstring). -/
theorem fs_WN_le {p₀ p₁ : FeP} {n L W₀ W₁ m w b k B₀ : ℕ} (e₀ : FbEnv p₀ n L W₀)
    (e₁ : FbEnv p₁ n L W₁) (hm : m ≤ n) (hw : w ≤ 2 * n) (hb : b ≤ 2 * n) (hk : k ≤ n)
    (hB₀ : B₀ ≤ Frame.spWs n)
    (hI0₀ : p₀.I0 = fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + 2 * w)
    (hI0₁ : p₁.I0 = p₀.END) :
    let W' := pnW p₀ p₁
    let H := nodeHN m b w (L + 1)
    let M := 2 * H + 1
    let Pb₀ := fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁
    (2 * W' + 1 + M * M + M ≤ WNb n L ∧
      2 * W' + 2 + (2 * p₀.Kw + 1) +
          (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) *
            (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) +
          (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) ≤ WNb n L ∧
      2 * W' + 2 + (2 * p₁.Kw + 1) +
          (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1) *
            (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1) +
          (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1) ≤ WNb n L ∧
      2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1 + 2 * M ≤ WNb n L ∧
      2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1 + 2 * M ≤ WNb n L ∧
      MSSP.isoN1 p₀.A p₀.N p₀.FN ≤ WNb n L ∧ MSSP.isoN1 p₁.A p₁.N p₁.FN ≤ WNb n L ∧
      W₀ ≤ WNb n L ∧ W₁ ≤ WNb n L) ∧
    hnB p₀ p₁ Pb₀ (Pb₀ + w) W' M H (MSSP.isoN1 p₀.A p₀.N p₀.FN)
      (MSSP.isoN1 p₁.A p₁.N p₁.FN) W₀ W₁ ≤ WNb n L ∧
    W' ≤ WNb n L ∧ M + 2 * L + 2 ≤ WNb n L ∧ p₁.END ≤ W' ∧ Pb₀ + 2 * w ≤ p₀.I0 ∧
    p₀.I0 ≤ p₀.END ∧ p₀.END ≤ p₁.END := by
  intro W' H M Pb₀
  -- the bounds of the parts
  have hPb : Pb₀ + 2 * w ≤ fbI0B n := by
    have hS : fbS w b p₀ p₁ ≤ 2 * n + 2 * n * (2 * n) + n + n := by
      unfold fbS; have := Nat.mul_le_mul hb hb; have := e₀.k; have := e₁.k; omega
    have hZ : fbZ B₀ k m w b p₀ p₁ ≤
        fbZv (Frame.spWs n) n n (2 * n) (2 * n) (3 * n) (3 * n) (3 * n) n (3 * n) (3 * n)
          (3 * n) n :=
      fbZv_mono hB₀ hk hm hw hb e₀.nD e₀.nV e₀.nF e₀.k e₁.nD e₁.nV e₁.nF e₁.k
    show fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + 2 * w ≤ fbI0B n
    unfold fbY fbI0B
    generalize fbZ B₀ k m w b p₀ p₁ = z at hZ
    generalize fbS w b p₀ p₁ = s at hS
    generalize fbZv (Frame.spWs n) n n (2 * n) (2 * n) (3 * n) (3 * n) (3 * n) n (3 * n) (3 * n)
      (3 * n) n = zb at hZ ⊢
    generalize 2 * n * (2 * n) = q at hS ⊢
    omega
  have hI0 : p₀.I0 ≤ fbI0B n := by rw [hI0₀]; exact hPb
  have hE0 := e₀.end_le
  have hE1 := e₁.end_le
  have hEnd0 : p₀.I0 ≤ p₀.END := by rw [pn_end p₀]; omega
  have hEnd1 : p₁.I0 ≤ p₁.END := by rw [pn_end p₁]; omega
  have hE1B : p₁.END ≤ fbE1B n := by unfold fbE1B; omega
  have hWp : W' ≤ fbWpB n L := by
    have a1 := e₀.Lm_le; have a2 := e₁.Lm_le; have a3 := e₀.Inf_le; have a4 := e₁.Inf_le
    have a5 := e₀.Kc_le; have a6 := e₁.Kc_le
    show pnW p₀ p₁ ≤ _
    unfold pnW fbWpB
    generalize kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k = x₀ at a5 ⊢
    generalize kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k = x₁ at a6 ⊢
    generalize 5 * n * fbLmB n L = y at a3 a4 ⊢
    omega
  have hH : H ≤ fbHB n L := nodeHN_mono hm hb hw le_rfl
  have hM : M ≤ fbMB n L := by show 2 * H + 1 ≤ 2 * fbHB n L + 1; omega
  have hMM : M * M ≤ fbMB n L * fbMB n L := Nat.mul_le_mul hM hM
  have hK0 := e₀.Kc_le
  have hK1 := e₁.Kc_le
  have hKK0 : (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) *
      (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) ≤
      (2 * fbKcB n L + 1) * (2 * fbKcB n L + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hKK1 : (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1) *
      (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1) ≤
      (2 * fbKcB n L + 1) * (2 * fbKcB n L + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hKw0 := e₀.Kw_le
  have hKw1 := e₁.Kw_le
  have hN0 := e₀.N1_le
  have hN1 := e₁.N1_le
  have hW0 := e₀.W₀
  have hW1 := e₁.W₀
  have hE0B : p₀.END ≤ fbE1B n := by omega
  have hWP' : p₁.END ≤ W' := by show p₁.END ≤ pnW p₀ p₁; unfold pnW; omega
  unfold WNb
  generalize fbWpB n L = a at hWp ⊢
  generalize fbMB n L = b at hM hMM ⊢
  generalize fbKcB n L = c at hK0 hK1 hKK0 hKK1 ⊢
  generalize fbKwB n = d at hKw0 hKw1 ⊢
  generalize fbN1B n = e at hN0 hN1 ⊢
  generalize fbHB n L = f at hH ⊢
  generalize fbE1B n = g at hE1B hE0B ⊢
  generalize fbI0B n = i at hPb hI0 ⊢
  generalize 3 * L * n = j at hW0 hW1 ⊢
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega⟩, ?_, by omega, by omega, hWP', by omega, hEnd0, by omega⟩
  unfold hnB
  omega

end NegSSSP

end PlanarFlow
