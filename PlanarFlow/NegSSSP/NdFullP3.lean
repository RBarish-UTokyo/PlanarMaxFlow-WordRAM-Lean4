module

public import PlanarFlow.NegSSSP.NdFullMd
public import PlanarFlow.NegSSSP.NdFullFin

/-!
# The full branch: `fbJ ; fbK ; fbC1 ; mdProg` from the end of `fbA`

**`fs_p3a`**: from a configuration `c` meeting the hypotheses of `fbJ_exec` (the end of `fbA`
in the full branch, see `fs_p2`) and the size registers of two instance parameters `p₀`, `p₁`
(any `Lmax`; `I0₀ = Y + 16S + 2w`, `I0₁ = END₀`), the run of `fbJ ; fbK ; fbC1 ; mdProg`:
the node's low arrays (tails, heads, side flags at `Z + j M₀`), the two plain arrays, the
positions of the vertices of `K` gathered and reduced modulo `k`, every position word `< k`,
the exact memory frame, the layout registers.
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

/-- The cost of `fbJ ; fbK ; fbC1 ; mdProg`. -/
def fsP3aCost (k w : ℕ) : ℕ := fbJCost k + (3 + (fbC1Cost k + (14 * w + 8)))

set_option maxHeartbeats 8000000 in
/-- **`fbJ ; fbK ; fbC1 ; mdProg`** (see the module docstring). -/
theorem fs_p3a {K Pc : Finset D} {m k m' w nV nF h d B₀ L b : ℕ} {en : ℕ → D}
    {α σ : ℕ → ℕ} (he : PEnc N Pc m k en α σ) (hKP : K ⊆ Pc) {ν : V → ℕ} {ι : ℕ → V}
    (hι : ∀ x ∈ verts N Pc, ι (ν x) = x) (hνw : ∀ x ∈ verts N Pc, ν x < w)
    (cn : SDart (rcl N K) ≃ Fin m') (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) (ψ : V → SVert (kσ N K) (rcl N K))
    (hψ : ∀ x : SDart (rcl N K), ψ (N.tail x.1) = (kmap N K).vert x)
    {p₀ p₁ : FeP} (c : Config) (hc : WordsBounded W c)
    (r03 : c.nreg 3003 = h) (r75 : c.nreg 2475 = k) (r74 : c.nreg 2474 = m)
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
    (hmk : m ≤ k) (hw : w ≤ 2 * k) (hm' : m' ≤ k) (hVF : nV + nF ≤ 2 * k) (hk0 : 0 < k)
    (hI0₀ : p₀.I0 = fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + 2 * w)
    (hI0₁ : p₁.I0 = p₀.END) (hEh : p₁.END ≤ h)
    (hl₀ : 5 * p₀.nD + p₀.k ≤ 16 * k) (hl₁ : 5 * p₁.nD + p₁.k ≤ 16 * k)
    (hBh : 2 * (B₀ + 66 * k + 35) + 2 ≤ h) (hW : h + 160 * k + (B₀ + 66 * k + 35) ≤ W)
    (h9600 : 9600 ≤ W) :
    ∃ c' t, Exec P W (.seq fbJ (.seq fbK (.seq fbC1 mdProg))) c c' t ∧ t ≤ fsP3aCost k w ∧
      c'.nreg 2313 = fbZ B₀ k m w b p₀ p₁ ∧ c'.nreg 2314 = m + w + 1 ∧
      c'.nreg 2315 = fbY B₀ k m w b p₀ p₁ ∧ c'.nreg 2316 = fbS w b p₀ p₁ ∧
      c'.nreg 2319 = p₀.I0 ∧ c'.nreg 2320 = p₀.END ∧ c'.nreg 2321 = p₁.END ∧
      c'.nreg 2300 = p₀.nF ∧ c'.nreg 2301 = p₁.nF ∧
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
      (∀ a, (a < fbZ B₀ k m w b p₀ p₁ ∨ fbZ B₀ k m w b p₀ p₁ + m ≤ a) →
        (a < fbZ B₀ k m w b p₀ p₁ + (m + w + 1) ∨ fbZ B₀ k m w b p₀ p₁ + (m + w + 1) + m ≤ a) →
        (a < fbZ B₀ k m w b p₀ p₁ + 2 * (m + w + 1) ∨
          fbZ B₀ k m w b p₀ p₁ + 2 * (m + w + 1) + m ≤ a) →
        (a < p₀.I0 ∨ p₀.I0 + (5 * p₀.nD + p₀.k) ≤ a) →
        (a < p₁.I0 ∨ p₁.I0 + (5 * p₁.nD + p₁.k) ≤ a) →
        (a < fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ ∨
          fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + 2 * w ≤ a) →
        (a < h + 130 * k ∨ h + 156 * k ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2100 ∨ (2119 < r ∧ r < 2260) ∨ (2269 < r ∧ r < 2296) ∨
        (2329 < r ∧ r < 2776) ∨ 2788 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- `fbJ`
  obtain ⟨c₁, t₁, e₁, ht₁, J1, J2, m₁, n₁, rr₁, rm₁, o₁⟩ :=
    fbJ_exec (P := P) he hKP hι hνw cn vn fn ψ hψ c hc r03 r75 r74 r64 r960 R hid hT hH hE hXm
      hFm hlow hmk hw hm' hBh (by clear * - hW; omega) h9600
  have N₁ : ∀ r, (r < 2100 ∨ (2119 < r ∧ r < 2260) ∨ (2269 < r ∧ r < 2296) ∨
      (2329 < r ∧ r < 2776) ∨ 2788 < r) → c₁.nreg r = c.nreg r := fun r hr =>
    n₁ r (by clear * - hr; omega)
  -- `fbK`
  obtain ⟨c₂, t₂, e₂, ht₂, k67, n₂, m₂, rr₂, rm₂, o₂⟩ := fbK_exec (P := P) (h := h) (k := k) c₁ e₁.wb_right
    (by rw [N₁ _ (by decide)]; exact r03) (by rw [N₁ _ (by decide)]; exact r75)
    (by clear * - hW; omega) (by clear * - h9600; omega)
  have N₂ : ∀ r, (r < 2100 ∨ (2119 < r ∧ r < 2260) ∨ (2269 < r ∧ r < 2296) ∨
      (2329 < r ∧ r < 2776) ∨ 2788 < r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [n₂ r (by clear * - hr; omega) (by clear * - hr; omega) (by clear * - hr; omega), N₁ r hr]
  have M₂ : ∀ a, (a < h + 130 * k ∨ h + 140 * k ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m₂, m₁ a ha]
  -- `fbC1`
  obtain ⟨c₃, t₃, e₃, ht₃, z13, z14, z15, z16, z19, z20, z21, z00, z01, A1, A2, A3, A4, A5, A6,
    A7, Lw, Lg, n₃, rr₃, rm₃, o₃⟩ := fbC1_exec' (P := P) (p₀ := p₀) (p₁ := p₁) (m := m) (k := k)
      (w := w) (b := b) (B₀ := B₀) (h := h) (nV := nV) (nF := nF) c₂ e₂.wb_right
      (by rw [N₂ _ (by decide)]; exact e0) (by rw [N₂ _ (by decide)]; exact e1)
      (by rw [N₂ _ (by decide)]; exact e2) (by rw [N₂ _ (by decide)]; exact e3)
      (by rw [N₂ _ (by decide)]; exact f0) (by rw [N₂ _ (by decide)]; exact f1)
      (by rw [N₂ _ (by decide)]; exact f2) (by rw [N₂ _ (by decide)]; exact f3)
      (by rw [N₂ _ (by decide)]; exact r74) (by rw [N₂ _ (by decide)]; exact r75)
      (by rw [N₂ _ (by decide)]; exact r64) (by rw [N₂ _ (by decide)]; exact r96)
      (by rw [N₂ _ (by decide)]; exact r72) (by rw [N₂ _ (by decide)]; exact r03)
      (by rw [N₂ _ (by decide)]; exact r961) (by rw [N₂ _ (by decide)]; exact r962)
      (by rw [N₂ _ (by decide)]; exact R.rra) (by rw [N₂ _ (by decide)]; exact R.rHh)
      (by rw [N₂ _ (by decide)]; exact R.rI00) (by rw [N₂ _ (by decide)]; exact R.rI01) k67
      (fun i hi => by rw [M₂ _ (Or.inl (by clear * - hi; omega))]; exact hid i hi)
      (fun j hj => by rw [m₂]; exact J2 j hj) hI0₀ hI0₁ hEh hmk hw hVF hl₀ hl₁ hW h9600
  set Y := fbY B₀ k m w b p₀ p₁ with hY
  set S := fbS w b p₀ p₁ with hS
  -- `mdProg`
  obtain ⟨c₄, t₄, e₄, ht₄, D1, D2, n₄, rr₄, rm₄, o₄⟩ := mdProg_exec (P := P) (w := w) (Y := Y)
    (S := S) (k := k) c₃ e₃.wb_right
    (by rw [n₃ _ (by decide), N₂ _ (by decide)]; exact r64) z15 z16
    (by rw [n₃ _ (by decide), N₂ _ (by decide)]; exact r75)
    (by
      have q1 : p₀.I0 ≤ p₀.END := by rw [pn_end p₀]; omega
      have q2 : p₁.I0 ≤ p₁.END := by rw [pn_end p₁]; omega
      clear * - hI0₀ hI0₁ hEh hW q1 q2; omega)
    (by clear * - h9600; omega)
  have hYS : fbZ B₀ k m w b p₀ p₁ + 22 * (m + w + 1) = Y := rfl
  have N₄ : ∀ r, (r < 2100 ∨ (2119 < r ∧ r < 2260) ∨ (2269 < r ∧ r < 2296) ∨
      (2329 < r ∧ r < 2776) ∨ 2788 < r) → c₄.nreg r = c.nreg r := fun r hr => by
    rw [n₄ r (by clear * - hr; omega), n₃ r (by clear * - hr; omega), N₂ r hr]
  have P₄ : ∀ a, (a < Y + 16 * S ∨ Y + 16 * S + 2 * w ≤ a) → c₄.nmem a = c₃.nmem a := D2
  refine ⟨c₄, t₁ + (t₂ + (t₃ + t₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), ?_,
    by rw [n₄ _ (by decide)]; exact z13, by rw [n₄ _ (by decide)]; exact z14,
    by rw [n₄ _ (by decide)]; exact z15, by rw [n₄ _ (by decide)]; exact z16,
    by rw [n₄ _ (by decide)]; exact z19, by rw [n₄ _ (by decide)]; exact z20,
    by rw [n₄ _ (by decide)]; exact z21, by rw [n₄ _ (by decide)]; exact z00,
    by rw [n₄ _ (by decide)]; exact z01, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun j hj => ?_, fun j hj => ?_, fun x hx => ?_, fun x hx => ?_,
    fun i hi => by rw [D1 i hi]; exact Nat.mod_lt _ hk0,
    fun a k1 k2 k3 k4 k5 k6 k7 => ?_, N₄, by rw [rr₄, rr₃, rr₂, rr₁], by rw [rm₄, rm₃, rm₂, rm₁],
    by rw [o₄, o₃, o₂, o₁]⟩
  · unfold fsP3aCost; clear * - ht₁ ht₂ ht₃ ht₄; omega
  · rw [P₄ _ (Or.inl (by clear * - hi hYS; omega)), A1 i hi,
      M₂ _ (Or.inl (by clear * - hi hmk hk0; omega))]
  · rw [P₄ _ (Or.inl (by clear * - hi hYS; omega)), A2 i hi,
      M₂ _ (Or.inl (by clear * - hi hmk hk0; omega))]
  · rw [P₄ _ (Or.inl (by clear * - hi hYS; omega)), A3 i hi,
      M₂ _ (Or.inl (by clear * - hi hmk hk0 hBh; omega))]
  · have q1 : p₀.I0 ≤ p₀.END := by rw [pn_end p₀]; omega
    rw [P₄ _ (Or.inr (by clear * - hI0₀ q1; omega)), A4 j hj,
      M₂ _ (Or.inl (by clear * - hj hl₀; omega))]
  · have q1 : p₀.I0 ≤ p₀.END := by rw [pn_end p₀]; omega
    rw [P₄ _ (Or.inr (by clear * - hI0₀ hI0₁ q1; omega)), A5 j hj,
      M₂ _ (Or.inl (by clear * - hj hl₁; omega))]
  · have hxw : ν x < w := hνw x (verts_mono hKP hx)
    have hv : (vn (ψ x) : ℕ) < nV := (vn (ψ x)).2
    have hJx : c₂.nmem (h + 138 * k + ν x) = vn (ψ x) := by rw [m₂]; exact J1 x hx
    rw [D1 (ν x) (by clear * - hxw; omega), A6 (ν x) hxw (by rw [hJx]; clear * - hv hVF; omega),
      hJx, M₂ _ (Or.inl (by clear * - hv hVF; omega))]
  · have hxw : ν x < w := hνw x (verts_mono hKP hx)
    have hv : (vn (ψ x) : ℕ) < nV := (vn (ψ x)).2
    have hJx : c₂.nmem (h + 138 * k + ν x) = vn (ψ x) := by rw [m₂]; exact J1 x hx
    have e := D1 (w + ν x) (by clear * - hxw; omega)
    rw [← Nat.add_assoc] at e
    rw [e, A7 (ν x) hxw (by rw [hJx]; clear * - hv hVF; omega),
      hJx, M₂ _ (Or.inl (by clear * - hv hVF; omega))]
  · rw [P₄ a k6, Lg a k1 k2 k3 k4 k5 k6 (by clear * - k7; omega),
      M₂ a (by clear * - k7; omega)]

end NegSSSP

end PlanarFlow
