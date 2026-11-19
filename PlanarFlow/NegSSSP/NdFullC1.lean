module

public import PlanarFlow.NegSSSP.NdFullC

/-!
# The full branch: the node's low arrays on the machine

**`fbC1_exec`**: `fbC1` from the layout registers: the tail and head numbers at `Z`,
`Z + M₀`, the side array at `Z + 2 M₀`, the plain arrays of the two instances at `I0₀`,
`I0₁ = END₀`, the positions re-indexed through `J` at `Pb₀ = Y + 16 S`, `Pb₁ = Pb₀ + w`;
memory kept outside `[Z, END₁)` and `[h + 140k, h + 156k)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

variable {P : Input} {W : ℕ}

theorem lt_off {a b i n : ℕ} (hi : i < n) (h : a + n ≤ b) : a + i < b := by omega

theorem le_off {a b i : ℕ} (h : b ≤ a) : b ≤ a + i := by omega

/-- **A copy through an identity array.** -/
theorem gaCopy_exec {a b c d n INb Jb Ob : ℕ} (ha : a < 2105 ∨ 2108 < a)
    (hb : b < 2105 ∨ 2108 < b) (hc : c < 2105 ∨ 2108 < c) (hd : d < 2105 ∨ 2108 < d)
    (c₀ : Config) (hw : WordsBounded W c₀) (ra : c₀.nreg a = n) (rb : c₀.nreg b = INb)
    (rc : c₀.nreg c = Jb) (rd : c₀.nreg d = Ob) (hid : ∀ i < n, c₀.nmem (Jb + i) = i)
    (h1 : 1 ≤ W) (wO : Ob + n ≤ W) (wJ : Jb + n ≤ W) (wI : INb + n ≤ W)
    (dJ : Ob + n ≤ Jb ∨ Jb + n ≤ Ob) (dI : Ob + n ≤ INb ∨ INb + n ≤ Ob) :
    ∃ c' t, Exec P W (gaS a b c d) c₀ c' t ∧ t ≤ 9 * n + 8 ∧
      (∀ i < n, c'.nmem (Ob + i) = c₀.nmem (INb + i)) ∧
      (∀ x, (x < Ob ∨ Ob + n ≤ x) → c'.nmem x = c₀.nmem x) ∧
      (∀ r, (r < 2105 ∨ 2113 < r) → c'.nreg r = c₀.nreg r) ∧
      c'.rreg = c₀.rreg ∧ c'.rmem = c₀.rmem ∧ c'.output = c₀.output := by
  obtain ⟨c', t, e, ht, v, m, f, rr, rm, o⟩ := gaS_exec (P := P) (W := W) ha hb hc hd c₀ hw ra rb
    rc rd h1 wO wJ dJ (fun i hi => by rw [hid i hi]; omega)
  exact ⟨c', t, e, ht, fun i hi => by rw [v i hi, hid i hi], m, f, rr, rm, o⟩

/-- The layout facts of `fbC1_exec`. -/
theorem fbC1_L {Z Y S m k w h W Ws B₀ I0₀ I0₁ E₁ len₀ len₁ nV nF : ℕ}
    (hZ : B₀ + 66 * k + 320 ≤ Z) (hY : Z + 22 * (m + w + 1) = Y)
    (hI : Y + 16 * S + 2 * w = I0₀) (hE0 : I0₀ + len₀ ≤ I0₁) (hE1 : I0₁ + len₁ ≤ E₁)
    (hEh : E₁ ≤ h) (hmk : m ≤ k) (hw : w ≤ 2 * k) (hVF : nV + nF ≤ 2 * k)
    (hl₀ : len₀ ≤ 16 * k) (hl₁ : len₁ ≤ 16 * k) (hW : h + 160 * k + Ws ≤ W) :
    (Z + m ≤ W ∧ h + 10 * k + m ≤ W ∧ h + m ≤ W ∧ Z + m ≤ h + 10 * k ∧ Z + m ≤ h) ∧
    (Z + (m + w + 1) + m ≤ W ∧ h + k + m ≤ W ∧ Z + (m + w + 1) + m ≤ h + 10 * k ∧
      Z + (m + w + 1) + m ≤ h + k) ∧
    (Z + 2 * (m + w + 1) + m ≤ W ∧ B₀ + 41 * k + 4 + m ≤ W ∧
      Z + 2 * (m + w + 1) + m ≤ h + 10 * k ∧ B₀ + 41 * k + 4 + m ≤ Z + 2 * (m + w + 1)) ∧
    (I0₀ + len₀ ≤ W ∧ h + 140 * k + len₀ ≤ W ∧ h + 50 * k + len₀ ≤ W ∧
      I0₀ + len₀ ≤ h + 140 * k ∧ I0₀ + len₀ ≤ h + 50 * k) ∧
    (I0₁ + len₁ ≤ W ∧ h + 140 * k + len₁ ≤ W ∧ h + 110 * k + len₁ ≤ W ∧
      I0₁ + len₁ ≤ h + 140 * k ∧ I0₁ + len₁ ≤ h + 110 * k) ∧
    (h + 140 * k + 16 * k ≤ W ∧ 1 ≤ W) ∧
    (Y + 16 * S + w ≤ W ∧ h + 138 * k + w ≤ W ∧ Y + 16 * S + w ≤ h + 138 * k ∧
      h + 20 * k + 2 * nV + 2 * nF + Ws ≤ W ∧ Y + 16 * S + w ≤ h + 20 * k + 2 * nV + 2 * nF) ∧
    (Y + 16 * S + w + w ≤ W ∧ Y + 16 * S + w + w ≤ h + 138 * k ∧
      h + 80 * k + 2 * nV + 2 * nF + Ws ≤ W ∧
      Y + 16 * S + w + w ≤ h + 80 * k + 2 * nV + 2 * nF) ∧
    (Z + m ≤ Z + (m + w + 1) ∧ Z + (m + w + 1) + m ≤ Z + 2 * (m + w + 1) ∧
      Z + 2 * (m + w + 1) + m ≤ Y + 16 * S ∧ Y + 16 * S + w + w = I0₀ ∧
      h + 140 * k + 16 * k ≤ h + 156 * k) ∧
    (Z + (m + w + 1) + m ≤ h ∧ Z + 2 * (m + w + 1) + m ≤ h ∧ I0₀ + len₀ ≤ h ∧
      I0₁ + len₁ ≤ h ∧ Y + 16 * S + w + w ≤ h ∧ Y + 16 * S + w + w ≤ I0₁ ∧ I0₁ + len₁ ≤ E₁ ∧
      B₀ + 41 * k + 4 + m ≤ Z) := by
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega⟩, ⟨by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩⟩

set_option maxHeartbeats 8000000 in
/-- **The node's low arrays on the machine** (see the module docstring). -/
theorem fbC1_exec {p₀ p₁ : FeP} {m k w b B₀ h nV nF : ℕ} (c : Config) (hc : WordsBounded W c)
    (e0 : c.nreg 2240 = p₀.nD) (e1 : c.nreg 2241 = p₀.nV) (e2 : c.nreg 2242 + 1 = p₀.nF)
    (e3 : c.nreg 2243 = p₀.k) (f0 : c.nreg 2244 = p₁.nD) (f1 : c.nreg 2245 = p₁.nV)
    (f2 : c.nreg 2246 + 1 = p₁.nF) (f3 : c.nreg 2247 = p₁.k)
    (r74 : c.nreg 2474 = m) (r75 : c.nreg 2475 = k) (r64 : c.nreg 2464 = w)
    (r96 : c.nreg 2496 = b) (r72 : c.nreg 2972 = B₀) (r03 : c.nreg 3003 = h)
    (r961 : c.nreg 961 = nV) (r962 : c.nreg 962 = nF) (r2203 : c.nreg 2203 = h + 10 * k)
    (r2214 : c.nreg 2214 = h + k) (r2223 : c.nreg 2223 = h + 50 * k)
    (r2233 : c.nreg 2233 = h + 110 * k) (r2267 : c.nreg 2267 = h + 138 * k)
    (hid : ∀ i < 2 * k, c.nmem (h + 10 * k + i) = i)
    (hJ : ∀ j < w, c.nmem (h + 138 * k + j) ≤ B₀ + 66 * k + 35)
    (hI0₀ : p₀.I0 = fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + 2 * w)
    (hI0₁ : p₁.I0 = p₀.END) (hEh : p₁.END ≤ h)
    (hmk : m ≤ k) (hw : w ≤ 2 * k) (hVF : nV + nF ≤ 2 * k)
    (hl₀ : 5 * p₀.nD + p₀.k ≤ 16 * k) (hl₁ : 5 * p₁.nD + p₁.k ≤ 16 * k)
    (hW : h + 160 * k + (B₀ + 66 * k + 35) ≤ W) (h9600 : 9600 ≤ W) :
    ∃ c' t, Exec P W fbC1 c c' t ∧ t ≤ fbC1Cost k ∧
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
      (∀ v < w, c.nmem (h + 138 * k + v) < 2 * k →
        c'.nmem (fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + v) =
        c.nmem (h + 20 * k + 2 * nV + 2 * nF + c.nmem (h + 138 * k + v))) ∧
      (∀ v < w, c.nmem (h + 138 * k + v) < 2 * k →
        c'.nmem (fbY B₀ k m w b p₀ p₁ + 16 * fbS w b p₀ p₁ + w + v) =
        c.nmem (h + 80 * k + 2 * nV + 2 * nF + c.nmem (h + 138 * k + v))) ∧
      (∀ a, (a < fbZ B₀ k m w b p₀ p₁ ∨ p₁.END ≤ a) → (a < h + 140 * k ∨ h + 156 * k ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2100 ∨ (2119 < r ∧ r < 2296) ∨ 2329 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨y1, y2, y3, y4, y5, y6, y7⟩ := fbC1_lay (B₀ := B₀) (k := k) (m := m) (w := w) (b := b)
    (h := h) hI0₀ hI0₁ hEh
  set Z := fbZ B₀ k m w b p₀ p₁ with hZdef
  set Y := fbY B₀ k m w b p₀ p₁ with hYdef
  set S := fbS w b p₀ p₁ with hSdef
  -- the layout chain
  have hgs : ∀ g : ℕ → ℕ, (∀ r, r ∉ pcDsts fbLL → r ≠ 2296 → r ≠ 2296 + 1 → g r = c.nreg r) →
      ∀ r, (r < 2100 ∨ (2101 < r ∧ r < 2296) ∨ 2329 < r) → g r = c.nreg r :=
    fun g hg r hr => hg r (fbLL_notDst (by omega)) (by omega) (by omega)
  obtain ⟨c₁, e₁, s₁, f₁, m₁, rr₁, rm₁, o₁⟩ := pcProg_exec (I := P) (W := W) fbLL fbLL_wf h9600
    c hc (fun g hg hs => by
      have k' := hgs g hg
      exact fbLL_bound hs ((k' 2240 (by omega)).trans e0) ((k' 2241 (by omega)).trans e1)
        (by rw [k' 2242 (by omega)]; exact e2) ((k' 2243 (by omega)).trans e3)
        ((k' 2244 (by omega)).trans f0) ((k' 2245 (by omega)).trans f1)
        (by rw [k' 2246 (by omega)]; exact f2) ((k' 2247 (by omega)).trans f3)
        (by rw [k' 2972 (by omega), k' 2475 (by omega), k' 2474 (by omega), k' 2464 (by omega),
          k' 2496 (by omega), r72, r75, r74, r64, r96]; exact hI0₀) hI0₁ (by omega)
        (by rw [k' 3003 (by omega), k' 2475 (by omega), r03, r75]; omega)
        (by rw [k' 961 (by omega), k' 962 (by omega), k' 2475 (by omega), r961, r962, r75]
            exact hVF))
  have K₁ := hgs c₁.nreg f₁
  obtain ⟨E0, E1, EZ, E14, E15, E16, E17, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27,
    E28, E100, E101, E29⟩ := fbLL_eqs s₁
  have i40 : c₁.nreg 2240 = p₀.nD := (K₁ 2240 (by omega)).trans e0
  have i41 : c₁.nreg 2241 = p₀.nV := (K₁ 2241 (by omega)).trans e1
  have i42 : c₁.nreg 2242 + 1 = p₀.nF := by rw [K₁ 2242 (by omega)]; exact e2
  have i43 : c₁.nreg 2243 = p₀.k := (K₁ 2243 (by omega)).trans e3
  have i44 : c₁.nreg 2244 = p₁.nD := (K₁ 2244 (by omega)).trans f0
  have i45 : c₁.nreg 2245 = p₁.nV := (K₁ 2245 (by omega)).trans f1
  have i46 : c₁.nreg 2246 + 1 = p₁.nF := by rw [K₁ 2246 (by omega)]; exact f2
  have i47 : c₁.nreg 2247 = p₁.k := (K₁ 2247 (by omega)).trans f3
  have i74 : c₁.nreg 2474 = m := (K₁ 2474 (by omega)).trans r74
  have i75 : c₁.nreg 2475 = k := (K₁ 2475 (by omega)).trans r75
  have i64 : c₁.nreg 2464 = w := (K₁ 2464 (by omega)).trans r64
  have i96 : c₁.nreg 2496 = b := (K₁ 2496 (by omega)).trans r96
  have i72 : c₁.nreg 2972 = B₀ := (K₁ 2972 (by omega)).trans r72
  have i03 : c₁.nreg 3003 = h := (K₁ 3003 (by omega)).trans r03
  have i961 : c₁.nreg 961 = nV := (K₁ 961 (by omega)).trans r961
  have i962 : c₁.nreg 962 = nF := (K₁ 962 (by omega)).trans r962
  have q13 : c₁.nreg 2313 = Z := by
    rw [EZ, i40, i41, i42, i43, i44, i45, i46, i47, i74, i75, i64, i96, i72]; rfl
  have q14 : c₁.nreg 2314 = m + w + 1 := by rw [E14, i74, i64]
  have q15 : c₁.nreg 2315 = Y := by rw [E15, q13, q14]; rfl
  have q16 : c₁.nreg 2316 = S := by rw [E16, i64, i96, i43, i47]; rfl
  have q17 : c₁.nreg 2317 = Y + 16 * S := by rw [E17, q15, q16]
  have q18 : c₁.nreg 2318 = Y + 16 * S + w := by rw [E18, q17, i64]
  have q19 : c₁.nreg 2319 = p₀.I0 := by rw [E19, q17, i64, y7]
  have q20 : c₁.nreg 2320 = p₀.END := by
    rw [E20, i40, i41, i42, i43, q19, pn_end p₀]
  have q21 : c₁.nreg 2321 = p₁.END := by
    rw [E21, i44, i45, i46, i47, q20, pn_end p₁, hI0₁]
  have q00 : c₁.nreg 2300 = p₀.nF := by rw [E0, i42]
  have q01 : c₁.nreg 2301 = p₁.nF := by rw [E1, i46]
  have q22 : c₁.nreg 2322 = 5 * p₀.nD + p₀.k := by rw [E22, i40, i43]
  have q23 : c₁.nreg 2323 = 5 * p₁.nD + p₁.k := by rw [E23, i44, i47]
  have q24 : c₁.nreg 2324 = Z + (m + w + 1) := by rw [E24, q13, q14]
  have q25 : c₁.nreg 2325 = Z + 2 * (m + w + 1) := by rw [E25, q13, q14]
  have q26 : c₁.nreg 2326 = B₀ + 41 * k + 4 := by rw [E26, i72, i75]
  have q27 : c₁.nreg 2327 = h + 20 * k + 2 * nV + 2 * nF := by rw [E27, i03, i75, i961, i962]
  have q28 : c₁.nreg 2328 = h + 80 * k + 2 * nV + 2 * nF := by rw [E28, i03, i75, i961, i962]
  have q100 : c₁.nreg 2100 = 16 * k := by rw [E100, i75]
  have q101 : c₁.nreg 2101 = h + 140 * k := by rw [E101, i03, i75]
  have q29 : c₁.nreg 2329 = h + 140 * k := by rw [E29, i03, i75]
  have hm₁ : c₁.nmem = c.nmem := m₁
  clear E0 E1 EZ E14 E15 E16 E17 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28 E100 E101 E29
  have hlen₀ : p₀.I0 + (5 * p₀.nD + p₀.k) ≤ p₁.I0 := by rw [hI0₁]; omega
  have hlen₁ : p₁.I0 + (5 * p₁.nD + p₁.k) ≤ p₁.END := by omega
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, ⟨b1, b2, b3, b4⟩, ⟨d1, d2, d3, d4⟩, ⟨x1, x2, x3, x4, x5⟩,
    ⟨z1, z2, z3, z4, z5⟩, ⟨w1, w2⟩, ⟨u1, u2, u3, u4, u5⟩, ⟨v1, v2, v3, v4⟩,
    ⟨o1, o2, o3, o4, o5⟩, ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩⟩ := fbC1_L (Z := Z) (Y := Y) (S := S) (Ws := B₀ + 66 * k + 35)
    (nV := nV) (nF := nF) y1 y2 y7 hlen₀ hlen₁ hEh hmk hw hVF hl₀ hl₁ hW
  have hVF' : 2 * nV + 2 * nF ≤ 4 * k := by omega
  clear y1 y2 y3 y4 y5 y6 hVF hW
  -- the second identity array
  obtain ⟨c₂, t₂, e₂, ht₂, i₂, m₂, f₂, rr₂, rm₂, o₂⟩ := idProg_exec (P := P) (n := 16 * k)
    (Ob := h + 140 * k) c₁ e₁.wb_right q100 q101 w1 w2
  have N₂ : ∀ r, 2104 < r → c₂.nreg r = c₁.nreg r := fun r hr => f₂ r (Or.inr hr)
  have L₂ : ∀ a, (a < h + 140 * k ∨ h + 156 * k ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [m₂ a (by rcases ha with ha | ha; exact Or.inl ha; exact Or.inr (le_trans o5 ha)), hm₁]
  have ID₂ : ∀ i < m, c₂.nmem (h + 10 * k + i) = i := fun i hi => by
    rw [L₂ _ (Or.inl (by clear * - hi hmk; omega))]; exact hid i (by clear * - hi hmk; omega)
  have hn : ∀ r, 2113 < r → (r < 2105 ∨ 2113 < r) := fun r hr => Or.inr hr
  -- the tails
  obtain ⟨c₃, t₃, e₃, ht₃, v₃, m₃, f₃, rr₃, rm₃, o₃⟩ := gaCopy_exec (P := P) (W := W)
    (a := 2474) (b := 3003) (c := 2203) (d := 2313) (n := m) (INb := h) (Jb := h + 10 * k)
    (Ob := Z) (by decide) (by decide) (by decide) (by decide) c₂ e₂.wb_right
    (by rw [N₂ _ (by decide), i74]) (by rw [N₂ _ (by decide), i03])
    (by rw [N₂ _ (by decide), K₁ _ (by decide), r2203]) (by rw [N₂ _ (by decide), q13])
    ID₂ w2 a1 a2 a3 (Or.inl a4) (Or.inl a5)
  have N₃ : ∀ r, 2113 < r → c₃.nreg r = c₁.nreg r := fun r hr => by
    rw [f₃ r (hn r hr), N₂ r (by clear * - hr; omega)]
  have ID₃ : ∀ i < m, c₃.nmem (h + 10 * k + i) = i := fun i hi => by
    rw [m₃ (h + 10 * k + i) (Or.inr (le_trans a4 (Nat.le_add_right _ _)))]; exact ID₂ i hi
  -- the heads
  obtain ⟨c₄, t₄, e₄, ht₄, v₄, m₄, f₄, rr₄, rm₄, o₄⟩ := gaCopy_exec (P := P) (W := W)
    (a := 2474) (b := 2214) (c := 2203) (d := 2324) (n := m) (INb := h + k) (Jb := h + 10 * k)
    (Ob := Z + (m + w + 1)) (by decide) (by decide) (by decide) (by decide) c₃ e₃.wb_right
    (by rw [N₃ _ (by decide), i74]) (by rw [N₃ _ (by decide), K₁ _ (by decide), r2214])
    (by rw [N₃ _ (by decide), K₁ _ (by decide), r2203]) (by rw [N₃ _ (by decide), q24])
    ID₃ w2 b1 a2 b2 (Or.inl b3) (Or.inl b4)
  have N₄ : ∀ r, 2113 < r → c₄.nreg r = c₁.nreg r := fun r hr => by
    rw [f₄ r (hn r hr), N₃ r hr]
  have ID₄ : ∀ i < m, c₄.nmem (h + 10 * k + i) = i := fun i hi => by
    rw [m₄ (h + 10 * k + i) (Or.inr (le_trans b3 (Nat.le_add_right _ _)))]; exact ID₃ i hi
  -- the sides
  obtain ⟨c₅, t₅, e₅, ht₅, v₅, m₅, f₅, rr₅, rm₅, o₅⟩ := gaCopy_exec (P := P) (W := W)
    (a := 2474) (b := 2326) (c := 2203) (d := 2325) (n := m) (INb := B₀ + 41 * k + 4)
    (Jb := h + 10 * k) (Ob := Z + 2 * (m + w + 1)) (by decide) (by decide) (by decide)
    (by decide) c₄ e₄.wb_right (by rw [N₄ _ (by decide), i74]) (by rw [N₄ _ (by decide), q26])
    (by rw [N₄ _ (by decide), K₁ _ (by decide), r2203]) (by rw [N₄ _ (by decide), q25])
    ID₄ w2 d1 a2 d2 (Or.inl d3) (Or.inr d4)
  have N₅ : ∀ r, 2113 < r → c₅.nreg r = c₁.nreg r := fun r hr => by
    rw [f₅ r (hn r hr), N₄ r hr]
  have I2₅ : ∀ j < 16 * k, c₅.nmem (h + 140 * k + j) = j := fun j hj => by
    rw [m₅ (h + 140 * k + j) (Or.inr (by clear * - d3; omega)),
      m₄ (h + 140 * k + j) (Or.inr (by clear * - b3; omega)),
      m₃ (h + 140 * k + j) (Or.inr (by clear * - a4; omega))]
    exact i₂ j hj
  -- `R`: the room above `h` is kept by the low writes
  have R₅ : ∀ a, h ≤ a → (a < h + 140 * k ∨ h + 156 * k ≤ a) → c₅.nmem a = c.nmem a :=
    fun a h1 h2 => by
      rw [m₅ a (Or.inr (by clear * - g2 h1; omega)), m₄ a (Or.inr (by clear * - g1 h1; omega)),
        m₃ a (Or.inr (by clear * - a5 h1; omega)), L₂ a h2]
  -- the plain arrays
  obtain ⟨c₆, t₆, e₆, ht₆, v₆, m₆, f₆, rr₆, rm₆, o₆⟩ := gaCopy_exec (P := P) (W := W)
    (a := 2322) (b := 2223) (c := 2329) (d := 2319) (n := 5 * p₀.nD + p₀.k)
    (INb := h + 50 * k) (Jb := h + 140 * k) (Ob := p₀.I0) (by decide) (by decide) (by decide)
    (by decide) c₅ e₅.wb_right (by rw [N₅ _ (by decide), q22])
    (by rw [N₅ _ (by decide), K₁ _ (by decide), r2223]) (by rw [N₅ _ (by decide), q29])
    (by rw [N₅ _ (by decide), q19]) (fun i hi => I2₅ i (by clear * - hi hl₀; omega))
    w2 x1 x2 x3 (Or.inl x4) (Or.inl x5)
  have N₆ : ∀ r, 2113 < r → c₆.nreg r = c₁.nreg r := fun r hr => by
    rw [f₆ r (hn r hr), N₅ r hr]
  have I2₆ : ∀ j < 16 * k, c₆.nmem (h + 140 * k + j) = j := fun j hj => by
    rw [m₆ (h + 140 * k + j) (Or.inr (by clear * - x4; omega))]; exact I2₅ j hj
  have R₆ : ∀ a, h ≤ a → (a < h + 140 * k ∨ h + 156 * k ≤ a) → c₆.nmem a = c.nmem a :=
    fun a h1 h2 => by rw [m₆ a (Or.inr (by clear * - g3 h1; omega)), R₅ a h1 h2]
  obtain ⟨c₇, t₇, e₇, ht₇, v₇, m₇, f₇, rr₇, rm₇, o₇⟩ := gaCopy_exec (P := P) (W := W)
    (a := 2323) (b := 2233) (c := 2329) (d := 2320) (n := 5 * p₁.nD + p₁.k)
    (INb := h + 110 * k) (Jb := h + 140 * k) (Ob := p₁.I0) (by decide) (by decide) (by decide)
    (by decide) c₆ e₆.wb_right (by rw [N₆ _ (by decide), q23])
    (by rw [N₆ _ (by decide), K₁ _ (by decide), r2233]) (by rw [N₆ _ (by decide), q29])
    (by rw [N₆ _ (by decide), q20, hI0₁]) (fun i hi => I2₆ i (by clear * - hi hl₁; omega))
    w2 z1 z2 z3 (Or.inl z4) (Or.inl z5)
  have N₇ : ∀ r, 2113 < r → c₇.nreg r = c₁.nreg r := fun r hr => by
    rw [f₇ r (hn r hr), N₆ r hr]
  have R₇ : ∀ a, h ≤ a → (a < h + 140 * k ∨ h + 156 * k ≤ a) → c₇.nmem a = c.nmem a :=
    fun a h1 h2 => by rw [m₇ a (Or.inr (by clear * - g4 h1; omega)), R₆ a h1 h2]
  -- the positions
  obtain ⟨c₈, t₈, e₈, ht₈, v₈, m₈, f₈, rr₈, rm₈, o₈⟩ := gaS_exec (P := P) (W := W)
    (a := 2464) (b := 2327) (c := 2267) (d := 2317) (n := w)
    (INb := h + 20 * k + 2 * nV + 2 * nF) (Jb := h + 138 * k) (Ob := Y + 16 * S) (by decide)
    (by decide) (by decide) (by decide) c₇ e₇.wb_right (by rw [N₇ _ (by decide), i64])
    (by rw [N₇ _ (by decide), q27]) (by rw [N₇ _ (by decide), K₁ _ (by decide), r2267])
    (by rw [N₇ _ (by decide), q17]) w2 u1 u2 (Or.inl u3)
    (fun v hv => by
      rw [R₇ _ (by clear * -; omega) (Or.inl (by clear * - hv hw; omega))]
      have := hJ v hv
      exact ⟨by clear * - this u4; omega, Or.inr (by clear * - u5; omega)⟩)
  have N₈ : ∀ r, 2113 < r → c₈.nreg r = c₁.nreg r := fun r hr => by
    rw [f₈ r (hn r hr), N₇ r hr]
  have R₈ : ∀ a, h ≤ a → (a < h + 140 * k ∨ h + 156 * k ≤ a) → c₈.nmem a = c.nmem a :=
    fun a h1 h2 => by rw [m₈ a (Or.inr (by clear * - g5 h1; omega)), R₇ a h1 h2]
  obtain ⟨c₉, t₉, e₉, ht₉, v₉, m₉, f₉, rr₉, rm₉, o₉⟩ := gaS_exec (P := P) (W := W)
    (a := 2464) (b := 2328) (c := 2267) (d := 2318) (n := w)
    (INb := h + 80 * k + 2 * nV + 2 * nF) (Jb := h + 138 * k) (Ob := Y + 16 * S + w) (by decide)
    (by decide) (by decide) (by decide) c₈ e₈.wb_right (by rw [N₈ _ (by decide), i64])
    (by rw [N₈ _ (by decide), q28]) (by rw [N₈ _ (by decide), K₁ _ (by decide), r2267])
    (by rw [N₈ _ (by decide), q18]) w2 v1 u2 (Or.inl v2)
    (fun v hv => by
      rw [R₈ _ (by clear * -; omega) (Or.inl (by clear * - hv hw; omega))]
      have := hJ v hv
      exact ⟨by clear * - this v3; omega, Or.inr (by clear * - v4; omega)⟩)
  have N₉ : ∀ r, 2113 < r → c₉.nreg r = c₁.nreg r := fun r hr => by
    rw [f₉ r (hn r hr), N₈ r hr]
  have Lw : ∀ a, (a < Z ∨ p₁.END ≤ a) → (a < h + 140 * k ∨ h + 156 * k ≤ a) →
      c₉.nmem a = c.nmem a := fun a h1 h2 => by
    have k1 : a < Y + 16 * S + w ∨ Y + 16 * S + w + w ≤ a := by
      clear * - h1 o1 o2 o3 g6 g7 hlen₁; omega
    have k2 : a < Y + 16 * S ∨ Y + 16 * S + w ≤ a := by
      clear * - h1 o1 o2 o3 g6 g7 hlen₁; omega
    have k3 : a < p₁.I0 ∨ p₁.I0 + (5 * p₁.nD + p₁.k) ≤ a := by
      clear * - h1 o1 o2 o3 g6 g7 hlen₁; omega
    have k4 : a < p₀.I0 ∨ p₀.I0 + (5 * p₀.nD + p₀.k) ≤ a := by
      clear * - h1 o1 o2 o3 o4 g6 g7 hlen₀ hlen₁; omega
    have k5 : a < Z + 2 * (m + w + 1) ∨ Z + 2 * (m + w + 1) + m ≤ a := by
      clear * - h1 o1 o2 o3 g6 g7 hlen₁; omega
    have k6 : a < Z + (m + w + 1) ∨ Z + (m + w + 1) + m ≤ a := by
      clear * - h1 o1 o2 o3 g6 g7 hlen₁; omega
    have k7 : a < Z ∨ Z + m ≤ a := by clear * - h1 o1 o2 o3 g6 g7 hlen₁; omega
    rw [m₉ a k1, m₈ a k2, m₇ a k3, m₆ a k4, m₅ a k5, m₄ a k6, m₃ a k7, L₂ a h2]
  refine ⟨c₉, pcCost fbLL + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + (t₈ + t₉))))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈ e₉))))))), ?_,
    by rw [N₉ _ (by decide), q13], by rw [N₉ _ (by decide), q14],
    by rw [N₉ _ (by decide), q15], by rw [N₉ _ (by decide), q16],
    by rw [N₉ _ (by decide), q19], by rw [N₉ _ (by decide), q20],
    by rw [N₉ _ (by decide), q21], by rw [N₉ _ (by decide), q00],
    by rw [N₉ _ (by decide), q01], fun i hi => ?_, fun i hi => ?_, fun i hi => ?_,
    fun j hj => ?_, fun j hj => ?_, fun v hv hJv => ?_, fun v hv hJv => ?_, Lw,
    fun r hr => ?_, by rw [rr₉, rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₉, rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₉, o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [fbLL_cost]; unfold fbC1Cost
    clear * - ht₂ ht₃ ht₄ ht₅ ht₆ ht₇ ht₈ ht₉ hmk hw hl₀ hl₁; omega
  · rw [m₉ _ (Or.inl (by clear * - hi o1 o2 o3; omega)),
      m₈ _ (Or.inl (by clear * - hi o1 o2 o3; omega)),
      m₇ _ (Or.inl (by clear * - hi o1 o2 o3 g6; omega)),
      m₆ _ (Or.inl (by clear * - hi o1 o2 o3 o4; omega)),
      m₅ _ (Or.inl (by clear * - hi o1 o2; omega)), m₄ _ (Or.inl (by clear * - hi o1; omega)),
      v₃ i hi, L₂ _ (Or.inl (by clear * - hi hmk; omega))]
  · rw [m₉ _ (Or.inl (by clear * - hi o1 o2 o3; omega)),
      m₈ _ (Or.inl (by clear * - hi o1 o2 o3; omega)),
      m₇ _ (Or.inl (by clear * - hi o1 o2 o3 g6; omega)),
      m₆ _ (Or.inl (by clear * - hi o1 o2 o3 o4; omega)),
      m₅ _ (Or.inl (by clear * - hi o2; omega)), v₄ i hi,
      m₃ _ (Or.inr (by clear * - a5; omega)), L₂ _ (Or.inl (by clear * - hi hmk; omega))]
  · rw [m₉ _ (Or.inl (by clear * - hi o1 o2 o3; omega)),
      m₈ _ (Or.inl (by clear * - hi o1 o2 o3; omega)),
      m₇ _ (Or.inl (by clear * - hi o1 o2 o3 g6; omega)),
      m₆ _ (Or.inl (by clear * - hi o1 o2 o3 o4; omega)), v₅ i hi,
      m₄ _ (Or.inl (by clear * - hi g8; omega)), m₃ _ (Or.inl (by clear * - hi g8; omega)),
      L₂ _ (Or.inl (by clear * - hi g8 a5; omega))]
  · rw [m₉ _ (Or.inr (by clear * - o4; omega)), m₈ _ (Or.inr (by clear * - o4; omega)),
      m₇ _ (Or.inl (by clear * - hj hlen₀; omega)), v₆ j hj,
      R₅ _ (by clear * -; omega) (Or.inl (by clear * - hj hl₀; omega))]
  · rw [m₉ _ (Or.inr (by clear * - g6; omega)), m₈ _ (Or.inr (by clear * - g6; omega)), v₇ j hj,
      R₆ _ (by clear * -; omega) (Or.inl (by clear * - hj hl₁; omega))]
  · rw [m₉ _ (Or.inl (by clear * - hv; omega)), v₈ v hv,
      R₇ (h + 138 * k + v) (by clear * -; omega) (Or.inl (by clear * - hv hw; omega)),
      R₇ _ (by clear * -; omega) (Or.inl (by clear * - hJv hVF'; omega))]
  · rw [v₉ v hv, R₈ (h + 138 * k + v) (by clear * -; omega) (Or.inl (by clear * - hv hw; omega)),
      R₈ _ (by clear * -; omega) (Or.inl (by clear * - hJv hVF'; omega))]
  · by_cases h1 : 2113 < r
    · rw [N₉ r h1, K₁ r (by clear * - hr; omega)]
    · rw [f₉ r (Or.inl (by clear * - hr h1; omega)), f₈ r (Or.inl (by clear * - hr h1; omega)),
        f₇ r (Or.inl (by clear * - hr h1; omega)), f₆ r (Or.inl (by clear * - hr h1; omega)),
        f₅ r (Or.inl (by clear * - hr h1; omega)), f₄ r (Or.inl (by clear * - hr h1; omega)),
        f₃ r (Or.inl (by clear * - hr h1; omega)), f₂ r (Or.inl (by clear * - hr h1; omega)),
        K₁ r (by clear * - hr h1; omega)]

end NegSSSP

end PlanarFlow
