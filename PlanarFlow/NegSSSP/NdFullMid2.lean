module

public import PlanarFlow.NegSSSP.NdFullWN

/-!
# The full branch: `fbJ ; fbK ; fbC1 ; mdProg ; fbC2` from the end of `fbA`

**`fs_mid`**: from the end of `fbA` (the hypotheses of `fs_p3a` and the inputs of `fbC2_exec'`
on that configuration), the run of `fbJ ; fbK ; fbC1 ; mdProg ; fbC2`: every register and
every memory fact that `fs_node` reads, stated against the configuration `c` at the end of
`fbA` (so the semantic conversion — `SideOut` to `FdArr`/`FdPos` — is done separately).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  PlanarSeparator.MillerProg

universe u v w

variable {P : Input} {W : ℕ}

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- The middle of the full branch. -/
def fbMid : Stmt := .seq (.seq fbJ (.seq fbK (.seq fbC1 mdProg))) fbC2

/-- The cost of `fbMid`. -/
def fsMidCost (k w : ℕ) (p₀ p₁ : FeP) : ℕ := fsP3aCost k w + fbC2Cost k p₀ p₁

/-- `pwS` of a copied plain array. -/
theorem pw_shift {mem mem' : ℕ → ℕ} {a b n k' : ℕ}
    (h : ∀ j < 5 * n + k', mem' (a + j) = mem (b + j)) :
    pwS mem' (a + 3 * n) (a + 4 * n) n = pwS mem (b + 3 * n) (b + 4 * n) n := by
  unfold pwS
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  have e1 := h (3 * n + j) (by omega)
  have e2 := h (4 * n + j) (by omega)
  rw [← Nat.add_assoc, ← Nat.add_assoc] at e1 e2
  rw [e1, e2]

set_option maxHeartbeats 16000000 in
/-- **The middle of the full branch** (see the module docstring). -/
theorem fs_mid {K Pc : Finset D} {m k m' w nV nF h d B₀ L b : ℕ} {en : ℕ → D}
    {α σ : ℕ → ℕ} (he : PEnc N Pc m k en α σ) (hKP : K ⊆ Pc) {ν : V → ℕ} {ι : ℕ → V}
    (hι : ∀ x ∈ verts N Pc, ι (ν x) = x) (hνw : ∀ x ∈ verts N Pc, ν x < w)
    (cn : SDart (rcl N K) ≃ Fin m') (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) (ψ : V → SVert (kσ N K) (rcl N K))
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {ℓ : D → ℤ} {δ₀ δ₁ : V → ℤ}
    {p₀ p₁ : FeP} (c : Config) (hc : WordsBounded W c)
    (r03 : c.nreg 3003 = h) (r04 : c.nreg 3004 = d) (r75 : c.nreg 2475 = k)
    (r74 : c.nreg 2474 = m)
    (r64 : c.nreg 2464 = w) (r960 : c.nreg 960 = m') (r961 : c.nreg 961 = nV)
    (r962 : c.nreg 962 = nF) (r96 : c.nreg 2496 = b) (r72 : c.nreg 2972 = B₀)
    (R : FbRegs c h d k B₀ m' L)
    (e0 : c.nreg 2240 = p₀.nD) (e1 : c.nreg 2241 = p₀.nV) (e2 : c.nreg 2242 + 1 = p₀.nF)
    (e3 : c.nreg 2243 = p₀.k) (f0 : c.nreg 2244 = p₁.nD) (f1 : c.nreg 2245 = p₁.nV)
    (f2 : c.nreg 2246 + 1 = p₁.nF) (f3 : c.nreg 2247 = p₁.k)
    (hid : ∀ i < 2 * k, c.nmem (h + 10 * k + i) = i)
    (hT : ∀ i < m, c.nmem (h + i) = ν (N.tail (en i)))
    (hH : ∀ i < m, c.nmem (h + k + i) = ν (N.head (en i)))
    (hE : Enc (kmap N K) cn vn fn c.nmem (B₀ + 28 * k + 3) (B₀ + 28 * k + 3 + m')
      (B₀ + 28 * k + 3 + 2 * m') (B₀ + 28 * k + 3 + 3 * m') (B₀ + 28 * k + 3 + 4 * m'))
    (hXm : ∀ i < k, ∀ hm : en i ∈ rcl N K, c.nmem (B₀ + 25 * k + 3 + i) = cn ⟨en i, hm⟩)
    (hFm : ∀ x < m, (c.nmem (B₀ + 33 * k + 3 + x) ≠ 0 ↔ en x ∈ K))
    (hlow : ∀ a < 2 * (B₀ + 66 * k + 35) + 2, c.nmem a ≤ B₀ + 66 * k + 35)
    (hm1 : c.nmem (d + 1) = m) (hk2 : c.nmem (d + 2) = k)
    (hln : ∀ i < m, c.nmem (d + 4 + 5 * k + i) = (ℓ (en i) + L).toNat)
    (hℓ : ∀ i < m, |ℓ (en i)| ≤ L)
    (hG₀ : ∀ v < w, (c.nmem (h + 4 * k + v) : ℤ) = δ₀ (ι v) + (L + 1) ∧ |δ₀ (ι v)| ≤ L + 1)
    (hG₁ : ∀ v < w, (c.nmem (h + 6 * k + v) : ℤ) = δ₁ (ι v) + (L + 1) ∧ |δ₁ (ι v)| ≤ L + 1)
    (hB0 : B₀ = Frame.spB0 k)
    (hmk : m ≤ k) (hw : w ≤ 2 * k) (hm' : m' ≤ k) (hVF : nV + nF ≤ 2 * k) (hk0 : 0 < k)
    (hb1 : 1 ≤ b)
    (hI0₀ : p₀.I0 = fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + 2 * w)
    (hI0₁ : p₁.I0 = p₀.END)
    (hl₀ : 5 * p₀.nD + p₀.k ≤ 16 * k) (hl₁ : 5 * p₁.nD + p₁.k ≤ 16 * k)
    (hL₀ : p₀.Lmax = feIsoB p₀.A p₀.N p₀.FN
      (1 + pwS c.nmem (h + 50 * k + 3 * p₀.nD) (h + 50 * k + 4 * p₀.nD) p₀.nD))
    (hL₁ : p₁.Lmax = feIsoB p₁.A p₁.N p₁.FN
      (1 + pwS c.nmem (h + 110 * k + 3 * p₁.nD) (h + 110 * k + 4 * p₁.nD) p₁.nD))
    (hEW : p₁.END ≤ pnW p₀ p₁) (hW1 : pnW p₀ p₁ ≤ W) (hW2 : 2 * nodeHN m b w (L + 1) + 1 ≤ W)
    (hW3 : MSSP.isoN1 p₀.A p₀.N p₀.FN ≤ W) (hW4 : MSSP.isoN1 p₁.A p₁.N p₁.FN ≤ W)
    (hWs : Frame.spWs k + 205 ≤ W) (hdW : 2 * pnW p₀ p₁ + 2 ≤ d)
    (hdh : d + 4 + 5 * k + m ≤ h)
    (hMW : 2 * nodeHN m b w (L + 1) + 1 + 2 * L + 2 ≤ W)
    (hBh : 2 * (B₀ + 66 * k + 35) + 2 ≤ h) (hW : h + 160 * k + (B₀ + 66 * k + 35) ≤ W)
    (h9600 : 9600 ≤ W) :
    ∃ c' t, Exec P W fbMid c c' t ∧ t ≤ fsMidCost k w p₀ p₁ ∧
      c'.nreg 1022 = pnW p₀ p₁ ∧ c'.nreg 1023 = 2 * nodeHN m b w (L + 1) + 1 ∧
      c'.nreg 1024 = nodeHN m b w (L + 1) ∧
      c'.nreg 2313 = fbZ B₀ k m w b p₀ p₁ ∧ c'.nreg 2314 = m + w + 1 ∧
      c'.nreg 2315 = fbY B₀ k m w b p₀ p₁ ∧ c'.nreg 2316 = fbS w b p₀ p₁ ∧
      c'.nreg 2321 = p₁.END ∧ c'.nreg 2300 = p₀.nF ∧ c'.nreg 2301 = p₁.nF ∧
      (∀ r, (r < 1000 ∨ (1170 ≤ r ∧ r < 2100) ∨ (2119 < r ∧ r < 2260) ∨
        (2269 < r ∧ r < 2296) ∨ (2335 < r ∧ r < 2776) ∨ (2788 < r ∧ r < 2840) ∨
        (2850 < r ∧ r < 2966) ∨ 2978 < r) → c'.nreg r = c.nreg r) ∧
      (∀ a ≤ Frame.spWs k, c'.nmem a = 0) ∧
      (∀ i < m, c'.nmem (fbZ B₀ k m w b p₀ p₁ + i) = c.nmem (h + i)) ∧
      (∀ i < m, c'.nmem (fbZ B₀ k m w b p₀ p₁ + (m + w + 1) + i) = c.nmem (h + k + i)) ∧
      (∀ i < m, c'.nmem (fbZ B₀ k m w b p₀ p₁ + 2 * (m + w + 1) + i) =
        c.nmem (B₀ + 41 * k + 4 + i)) ∧
      (∀ j < 5 * p₀.nD + p₀.k, c'.nmem (p₀.I0 + j) = c.nmem (h + 50 * k + j)) ∧
      (∀ j < 5 * p₁.nD + p₁.k, c'.nmem (p₁.I0 + j) = c.nmem (h + 110 * k + j)) ∧
      (∀ x ∈ verts N K, c'.nmem (fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + ν x) =
        c.nmem (h + 20 * k + 2 * nV + 2 * nF + vn (ψ x)) % k) ∧
      (∀ x ∈ verts N K, c'.nmem (fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + w + ν x) =
        c.nmem (h + 80 * k + 2 * nV + 2 * nF + vn (ψ x)) % k) ∧
      (∀ i < 2 * w, c'.nmem (fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + i) < k) ∧
      (∀ i < m, (c'.nmem (pnW p₀ p₁ + 1 + (fbZ B₀ k m w b p₀ p₁ + 3 * (m + w + 1) + i)) : ℤ) =
        ℓ (en i) % ((2 * nodeHN m b w (L + 1) + 1 : ℕ) : ℤ)) ∧
      (∀ v < w, (c'.nmem (pnW p₀ p₁ + 1 + (fbZ B₀ k m w b p₀ p₁ + 4 * (m + w + 1) + v)) : ℤ) =
        δ₀ (ι v) % ((2 * nodeHN m b w (L + 1) + 1 : ℕ) : ℤ)) ∧
      (∀ v < w, (c'.nmem (pnW p₀ p₁ + 1 + (fbZ B₀ k m w b p₀ p₁ + 5 * (m + w + 1) + v)) : ℤ) =
        δ₁ (ι v) % ((2 * nodeHN m b w (L + 1) + 1 : ℕ) : ℤ)) ∧
      (∀ a, Frame.spWs k < a →
        (a < fbZ B₀ k m w b p₀ p₁ ∨ fbZ B₀ k m w b p₀ p₁ + m ≤ a) →
        (a < fbZ B₀ k m w b p₀ p₁ + (m + w + 1) ∨ fbZ B₀ k m w b p₀ p₁ + (m + w + 1) + m ≤ a) →
        (a < fbZ B₀ k m w b p₀ p₁ + 2 * (m + w + 1) ∨
          fbZ B₀ k m w b p₀ p₁ + 2 * (m + w + 1) + m ≤ a) →
        (a < p₀.I0 ∨ p₀.I0 + (5 * p₀.nD + p₀.k) ≤ a) →
        (a < p₁.I0 ∨ p₁.I0 + (5 * p₁.nD + p₁.k) ≤ a) →
        (a < fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ ∨
          fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + 2 * w ≤ a) →
        (a < pnW p₀ p₁ + 1 + (fbZ B₀ k m w b p₀ p₁ + 3 * (m + w + 1)) ∨
          pnW p₀ p₁ + 1 + (fbZ B₀ k m w b p₀ p₁ + 3 * (m + w + 1)) + m ≤ a) →
        (a < pnW p₀ p₁ + 1 + (fbZ B₀ k m w b p₀ p₁ + 4 * (m + w + 1)) ∨
          pnW p₀ p₁ + 1 + (fbZ B₀ k m w b p₀ p₁ + 4 * (m + w + 1)) + w ≤ a) →
        (a < pnW p₀ p₁ + 1 + (fbZ B₀ k m w b p₀ p₁ + 5 * (m + w + 1)) ∨
          pnW p₀ p₁ + 1 + (fbZ B₀ k m w b p₀ p₁ + 5 * (m + w + 1)) + w ≤ a) →
        (a < h + 130 * k ∨ h + 156 * k ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hEh : p₁.END ≤ h := by clear * - hEW hdW hdh; omega
  obtain ⟨c₄, t₄, e₄, ht₄, z13, z14, z15, z16, z19, z20, z21, z00, z01, A1, A2, A3, A4, A5, A6,
    A7, AP, Lg, N₄, rr₄, rm₄, o₄⟩ := fs_p3a (P := P) he hKP hι hνw cn vn fn ψ hψ c hc r03 r75
      r74 r64 r960 r961 r962 r96 r72 R e0 e1 e2 e3 f0 f1 f2 f3 hid hT hH hE hXm hFm hlow hmk hw
      hm' hVF hk0 hI0₀ hI0₁ hEh hl₀ hl₁ hBh hW h9600
  set Z := fbZ B₀ k m w b p₀ p₁ with hZ
  set Y := fbY B₀ k m w b p₀ p₁ with hY
  set S := fbS w b p₀ p₁ with hS
  have hYZ : Z + 22 * (m + w + 1) = Y := rfl
  have q1 : p₀.I0 + (5 * p₀.nD + p₀.k) ≤ p₀.END := by rw [pn_end p₀]; omega
  have q2 : p₁.I0 + (5 * p₁.nD + p₁.k) ≤ p₁.END := by rw [pn_end p₁]; omega
  have hZs : Frame.spWs k < Z := by
    have := (fbZ_bounds B₀ k m w b p₀ p₁).2.2.2.2.2.2
    unfold Frame.spWs; omega
  -- the frame of the first part, for the high cells
  have Fh : ∀ a, p₁.END ≤ a → (a < h + 130 * k ∨ h + 156 * k ≤ a) → c₄.nmem a = c.nmem a :=
    fun a h1 h2 => Lg a (Or.inr (by clear * - h1 hI0₀ hI0₁ q1 q2 hYZ; omega))
      (Or.inr (by clear * - h1 hI0₀ hI0₁ q1 q2 hYZ; omega))
      (Or.inr (by clear * - h1 hI0₀ hI0₁ q1 q2 hYZ; omega))
      (Or.inr (by clear * - h1 hI0₀ hI0₁ q1 q2; omega))
      (Or.inr (by clear * - h1 q2; omega))
      (Or.inr (by clear * - h1 hI0₀ hI0₁ q1 q2; omega)) h2
  have hpw₀ := pw_shift (k' := p₀.k) A4
  have hpw₁ := pw_shift (k' := p₁.k) A5
  have hdE : p₁.END ≤ d := by clear * - hEW hdW; omega
  -- `fbC2`
  obtain ⟨c₆, t₆, e₆, ht₆, Zs, HP, R1, R2, R3, Lw2, Lg2, N₆, rr₆, rm₆, o₆⟩ :=
    fbC2_exec' (P := P) (en := en) (ι := ι) (ℓ := ℓ) (δ₀ := δ₀) (δ₁ := δ₁) (p₀ := p₀) (p₁ := p₁)
      (m := m) (k := k) (w := w) (b := b) (L := L) (h := h) (d := d) (Z := Z) (M₀ := m + w + 1)
      (Y := Y) (S := S) c₄ e₄.wb_right
      (by rw [N₄ _ (by decide)]; exact r03) (by rw [N₄ _ (by decide)]; exact r04)
      (by rw [N₄ _ (by decide)]; exact r74) (by rw [N₄ _ (by decide)]; exact r75)
      (by rw [N₄ _ (by decide)]; exact r64) (by rw [N₄ _ (by decide)]; exact r96)
      (by rw [N₄ _ (by decide)]; exact R.rra) (by rw [N₄ _ (by decide)]; exact R.rL)
      (by rw [N₄ _ (by decide)]; exact R.rL1) (by rw [N₄ _ (by decide)]; exact e0)
      (by rw [N₄ _ (by decide)]; exact e1) z00 (by rw [N₄ _ (by decide)]; exact e3)
      (by rw [N₄ _ (by decide)]; exact f0) (by rw [N₄ _ (by decide)]; exact f1) z01
      (by rw [N₄ _ (by decide)]; exact f3) z13 z14 z15 z16
      (by rw [Fh _ (by clear * - hdE; omega) (Or.inl (by clear * - hdh; omega))]; exact hm1)
      (by rw [Fh _ (by clear * - hdE; omega) (Or.inl (by clear * - hdh; omega))]; exact hk2)
      (fun i hi => by
        rw [Fh _ (by clear * - hEh; omega) (Or.inl (by clear * - hi; omega))]; exact hid i hi)
      (fun i hi => by
        rw [Fh _ (by clear * - hdE; omega) (Or.inl (by clear * - hi hdh; omega))]
        exact hln i hi) hℓ
      (fun v hv => by
        rw [Fh _ (by clear * - hEh; omega) (Or.inl (by clear * - hv hw; omega))]; exact hG₀ v hv)
      (fun v hv => by
        rw [Fh _ (by clear * - hEh; omega) (Or.inl (by clear * - hv hw; omega))]; exact hG₁ v hv)
      rfl (by clear * - hYZ; omega) hI0₀ hI0₁ hZs (by rw [hpw₀]; exact hL₀)
      (by rw [hpw₁]; exact hL₁) hb1 hW1 hW2 hW3 hW4 h9600 hWs hdW hdh hmk hw
      (by clear * - hW; omega) hMW
  rw [hpw₀, hpw₁] at HP
  have v1022 : c₆.nreg 1022 = pnW p₀ p₁ := by
    have := HP.c2; rwa [show (10550 + 2 = 10552) from rfl, pnπ_hi 22 (by decide)] at this
  have v1023 : c₆.nreg 1023 = 2 * nodeHN m b w (L + 1) + 1 := by
    have := HP.c3; rwa [show (10550 + 3 = 10553) from rfl, pnπ_hi 23 (by decide)] at this
  have v1024 : c₆.nreg 1024 = nodeHN m b w (L + 1) := by
    have := HP.c4; rwa [show (10550 + 4 = 10554) from rfl, pnπ_hi 24 (by decide)] at this
  -- the memory of `c₆` against `c₄`, then `c`
  have K6 : ∀ a, Frame.spWs k < a →
      (a < pnW p₀ p₁ + 1 + (Z + 3 * (m + w + 1)) ∨
        pnW p₀ p₁ + 1 + (Z + 3 * (m + w + 1)) + m ≤ a) →
      (a < pnW p₀ p₁ + 1 + (Z + 4 * (m + w + 1)) ∨
        pnW p₀ p₁ + 1 + (Z + 4 * (m + w + 1)) + w ≤ a) →
      (a < pnW p₀ p₁ + 1 + (Z + 5 * (m + w + 1)) ∨
        pnW p₀ p₁ + 1 + (Z + 5 * (m + w + 1)) + w ≤ a) → c₆.nmem a = c₄.nmem a := Lg2
  have hlowW : Z + 6 * (m + w + 1) ≤ pnW p₀ p₁ := by
    clear * - hEW hI0₀ hI0₁ q1 q2 hYZ; omega
  have Kl : ∀ a, Frame.spWs k < a → a < pnW p₀ p₁ + 1 → c₆.nmem a = c₄.nmem a := fun a h1 h2 =>
    K6 a h1 (Or.inl (by clear * - h2; omega)) (Or.inl (by clear * - h2; omega))
      (Or.inl (by clear * - h2; omega))
  have N6 : ∀ r, (r < 1000 ∨ (1170 ≤ r ∧ r < 2296) ∨ (2297 < r ∧ r < 2330) ∨
      (2335 < r ∧ r < 2840) ∨ (2850 < r ∧ r < 2966) ∨ 2978 < r) → c₆.nreg r = c₄.nreg r := N₆
  have hI0W : p₀.I0 ≤ pnW p₀ p₁ := by clear * - hEW q1 q2 hI0₁; omega
  refine ⟨c₆, t₄ + t₆, .seq e₄ e₆, ?_, v1022, v1023, v1024, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun r hr => ?_, Zs, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_,
    fun j hj => ?_, fun x hx => ?_, fun x hx => ?_, fun i hi => ?_, R1, R2, R3,
    fun a h0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 => ?_, by rw [rr₆, rr₄], by rw [rm₆, rm₄],
    by rw [o₆, o₄]⟩
  · unfold fsMidCost; clear * - ht₄ ht₆; omega
  · rw [N6 _ (by decide)]; exact z13
  · rw [N6 _ (by decide)]; exact z14
  · rw [N6 _ (by decide)]; exact z15
  · rw [N6 _ (by decide)]; exact z16
  · rw [N6 _ (by decide)]; exact z21
  · rw [N6 _ (by decide)]; exact z00
  · rw [N6 _ (by decide)]; exact z01
  · rw [N6 r (by clear * - hr; omega), N₄ r (by clear * - hr; omega)]
  · rw [Kl _ (by clear * - hZs; omega) (by clear * - hi hlowW; omega)]; exact A1 i hi
  · rw [Kl _ (by clear * - hZs; omega) (by clear * - hi hlowW; omega)]; exact A2 i hi
  · rw [Kl _ (by clear * - hZs; omega) (by clear * - hi hlowW; omega)]; exact A3 i hi
  · rw [Kl _ (by clear * - hZs hYZ hI0₀; omega) (by clear * - hj q1 q2 hI0₁ hEW; omega)]
    exact A4 j hj
  · rw [Kl _ (by clear * - hZs hYZ hI0₀ hI0₁ q1; omega) (by clear * - hj q2 hEW; omega)]
    exact A5 j hj
  · have hxw : ν x < w := hνw x (verts_mono hKP hx)
    rw [Kl _ (by clear * - hZs hYZ; omega) (by clear * - hxw hI0₀ hI0W; omega)]; exact A6 x hx
  · have hxw : ν x < w := hνw x (verts_mono hKP hx)
    rw [Kl _ (by clear * - hZs hYZ; omega) (by clear * - hxw hI0₀ hI0W; omega)]; exact A7 x hx
  · rw [Kl _ (by clear * - hZs hYZ; omega) (by clear * - hi hI0₀ hI0W; omega)]; exact AP i hi
  · rw [K6 a h0 k7 k8 k9, Lg a k1 k2 k3 k4 k5 k6 k10]

end NegSSSP

end PlanarFlow
