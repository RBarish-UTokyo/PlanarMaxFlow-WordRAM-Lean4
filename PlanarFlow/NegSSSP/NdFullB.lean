module

public import PlanarFlow.NegSSSP.NdFullPre

/-!
# The full branch: the side arrays of both sides

**`fbA = fbPre ; fbSide (side Z) ; fbSide (side Zᶜ)`** and **`fbA_exec`**: from the data the
split leaves (the plain encoding of the piece map of the large component `K`, the marks of the
side `Z`, the index array and the flags), the frame's lengths, the node's tail/head numbers at
`h`, `h + k` and the gathered children's values at `h + 4k`, `h + 6k`: the side arrays of both
sides (`SideOut` with `T₀ = h + 20k`, `I0 = h + 50k`, sizes in `2240 … 2243`, and
`T₀ = h + 80k`, `I0 = h + 110k`, sizes in `2244 … 2247`); memory below `h + 10k` and from
`h + 126k` kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Function Equiv Orbit CombMap Relation PlanarSeparator PlanarSeparator.Map
  PlanarSeparator.StDart BKMNW WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  Monge.CmpAbs PlanarSeparator.MillerProg

universe u v w

variable {P : Input} {W : ℕ}

/-- **The side arrays of both sides.** -/
def fbA : Stmt :=
  .seq fbPre (.seq (fbSide 2209 2220 2221 2222 2219 2223 2240)
    (fbSide 2210 2230 2231 2232 2224 2233 2244))

theorem fbSL_ok : cpOK (fbSL 2209 2220 2221 2222 2219 2223) = true ∧
    cpSrc (fbSL 2209 2220 2221 2222 2219 2223) = true ∧
    cpOK (fbSL 2210 2230 2231 2232 2224 2233) = true ∧
    cpSrc (fbSL 2210 2230 2231 2232 2224 2233) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The layout facts of `fbA_exec`. -/
theorem fbA_lay {h k m m' w nV nF B₀ d Ck : ℕ} (hmk : m ≤ k) (hw : w ≤ 2 * k) (hm' : m' ≤ k)
    (hVF : nV + nF ≤ 2 * k) (hCk : Ck ≤ k) (hdh : d + 4 + 5 * k + m ≤ h)
    (hB : B₀ + 66 * k + 35 < d) :
    (B₀ + 28 * k + 3 + 5 * m' ≤ h + 18 * k ∧ B₀ + 22 * m' + m' ≤ h + 18 * k ∧
      h + 17 * k + m' ≤ h + 18 * k ∧ B₀ + 25 * k + 3 + k ≤ h + 18 * k ∧
      B₀ + 33 * k + 3 + m ≤ h + 18 * k) ∧
    (B₀ + 28 * k + 3 + 5 * m' ≤ h + 78 * k ∧ B₀ + 22 * m' + m' ≤ h + 78 * k ∧
      h + 17 * k + m' ≤ h + 78 * k ∧ B₀ + 25 * k + 3 + k ≤ h + 78 * k ∧
      B₀ + 33 * k + 3 + m ≤ h + 78 * k) ∧
    h + 12 * k + m ≤ h + 18 * k ∧ h + k + m ≤ h + 18 * k ∧
    h + 12 * k + m ≤ h + 78 * k ∧ h + k + m ≤ h + 78 * k ∧
    h + 18 * k + 48 * k ≤ h + 78 * k ∧
    h + 20 * k + 2 * (nV + nF) + nV ≤ h + 78 * k ∧ h + 18 * k ≤ h + 20 * k := by
  refine ⟨⟨by omega, by omega, by omega, by omega, by omega⟩,
    ⟨by omega, by omega, by omega, by omega, by omega⟩, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega⟩

section Sides

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}
variable {K : Finset D} {C : (kst N K).SCycle} {Z : Finset (kst N K).Face}

set_option maxHeartbeats 8000000 in
/-- **The side arrays of both sides** (see the module docstring). -/
theorem fbA_exec (hrot : N.RotTrans) (hKr : K ⊆ reps N) {ψ : V → SVert (kσ N K) (rcl N K)}
    (hbd₀ : ∀ δ, ((kst N K).face δ ∈ Z ↔ (kst N K).face ((kst N K).α δ) ∈ Z) ↔ ¬ C.Mem δ)
    (hbd₁ : ∀ δ, ((kst N K).face δ ∈ Zᶜ ↔ (kst N K).face ((kst N K).α δ) ∈ Zᶜ) ↔ ¬ C.Mem δ)
    {Bs : Finset V} (hBs : ∀ b ∈ Bs, Sum.inl (ψ b) ∈ C.verts)
    {Pc : Finset D} {m k : ℕ} {en : ℕ → D} {α σ : ℕ → ℕ} (he : PEnc N Pc m k en α σ)
    (hKP : K ⊆ Pc) (ℓ : D → ℤ) (δ₀ δ₁ : V → ℤ) {w : ℕ} (ν : V → ℕ) (ι : ℕ → V)
    {m' nV nF : ℕ} (cn : SDart (rcl N K) ≃ Fin m') (vn : SVert (kσ N K) (rcl N K) ≃ Fin nV)
    (fn : (kmap N K).Face ≃ Fin nF) {L h d B₀ : ℕ}
    (c : Config) (hc : WordsBounded W c)
    (r03 : c.nreg 3003 = h) (r04 : c.nreg 3004 = d) (r75 : c.nreg 2475 = k)
    (r74 : c.nreg 2474 = m) (r64 : c.nreg 2464 = w) (r72 : c.nreg 2972 = B₀)
    (r960 : c.nreg 960 = m') (r961 : c.nreg 961 = nV) (r962 : c.nreg 962 = nF)
    (hL : c.nmem (d + 3) = L)
    (hln : ∀ i < m, c.nmem (d + 4 + 5 * k + i) = (ℓ (en i) + L).toNat)
    (hℓ : ∀ i < m, |ℓ (en i)| ≤ L)
    (hTn : ∀ i < m, c.nmem (h + i) = ν (N.tail (en i)) ∧ ν (N.tail (en i)) < w ∧
      ι (ν (N.tail (en i))) = N.tail (en i))
    (hHn : ∀ i < m, c.nmem (h + k + i) = ν (N.head (en i)) ∧ ν (N.head (en i)) < w ∧
      ι (ν (N.head (en i))) = N.head (en i))
    (hG₀ : ∀ v < w, (c.nmem (h + 4 * k + v) : ℤ) = δ₀ (ι v) + (L + 1) ∧ |δ₀ (ι v)| ≤ L + 1)
    (hG₁ : ∀ v < w, (c.nmem (h + 6 * k + v) : ℤ) = δ₁ (ι v) + (L + 1) ∧ |δ₁ (ι v)| ≤ L + 1)
    (hE : Enc (kmap N K) cn vn fn c.nmem (B₀ + 28 * k + 3) (B₀ + 28 * k + 3 + m')
      (B₀ + 28 * k + 3 + 2 * m') (B₀ + 28 * k + 3 + 3 * m') (B₀ + 28 * k + 3 + 4 * m'))
    (hz₀ : ∀ x, ((kst N K).face (old x) ∈ Z ↔ c.nmem (B₀ + 22 * m' + cn x) = 1))
    (hz₁ : ∀ x, ((kst N K).face (old x) ∈ Zᶜ ↔ c.nmem (B₀ + 22 * m' + cn x) = 0))
    (hXm : ∀ i < k, ∀ hm : en i ∈ rcl N K, c.nmem (B₀ + 25 * k + 3 + i) = cn ⟨en i, hm⟩)
    (hFm : ∀ x < m, (c.nmem (B₀ + 33 * k + 3 + x) ≠ 0 ↔ en x ∈ K))
    (hred₀ : ∀ x ∈ side N K Z, 0 ≤ redLen N ℓ δ₀ x ∧ redLen N ℓ δ₀ x < (3 * L + 1 : ℕ))
    (hred₁ : ∀ x ∈ side N K Zᶜ, 0 ≤ redLen N ℓ δ₁ x ∧ redLen N ℓ δ₁ x < (3 * L + 1 : ℕ))
    (hCk : C.k ≤ k) (hmk : m ≤ k) (hw : w ≤ 2 * k) (hm' : m' ≤ k) (hVF : nV + nF ≤ 2 * k)
    (hdh : d + 4 + 5 * k + m ≤ h) (hB : B₀ + 66 * k + 35 < d) (hW : h + 150 * k ≤ W)
    (hk1 : 1 ≤ k) (hLW : 3 * (3 * L + 1) + 2 * L + 2 ≤ W) (h9600 : 9600 ≤ W) :
    ∃ c' t, Exec P W fbA c c' t ∧
      t ≤ fbPreCost k + 2 * (33 * m + 405 * m' + 13 * (nV + nF) + 22 * C.k + 155) ∧
      FbRegs c' h d k B₀ m' L ∧
      SideOut K C Z hbd₀ Bs ψ vn nF ℓ δ₀ (h + 20 * k) (h + 50 * k) 2240 c' ∧
      SideOut K C Zᶜ hbd₁ Bs ψ vn nF ℓ δ₁ (h + 80 * k) (h + 110 * k) 2244 c' ∧
      (∀ i < 2 * k, c'.nmem (h + 10 * k + i) = i) ∧
      (∀ a, (a < h + 10 * k ∨ h + 126 * k ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 10 → (r < 300 ∨ 318 < r) → (r < 800 ∨ 840 < r) → (r < 2100 ∨
        (2248 ≤ r ∧ r < 2550) ∨ (2593 < r ∧ r < 2750) ∨ 2850 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨ok0, sr0, ok1, sr1⟩ := fbSL_ok
  obtain ⟨⟨l1, l2, l3, l4, l5⟩, ⟨l6, l7, l8, l9, l10⟩, l11, l12, l13, l14, l15, l16, l17⟩ :=
    fbA_lay (nV := nV) (nF := nF) hmk hw hm' hVF hCk hdh hB
  -- the inputs
  obtain ⟨c₁, t₁, e₁, ht₁, R₁, I₁, RL₁, D0₁, D1₁, K₁, M₁, F₁, rr₁, rm₁, o₁⟩ :=
    fbPre_exec (P := P) he hKP cn ℓ δ₀ δ₁ ι c hc r03 r04 r75 r74 r64 r72 r960 hL hln hℓ hG₀ hG₁
      hXm hFm hmk hw hm' hdh hB (by omega) hLW h9600
  have L₁ : ∀ a, a < h + 10 * k → c₁.nmem a = c.nmem a := fun a ha => M₁ a (Or.inl ha)
  have k₁ : ∀ r, r < 2100 → c₁.nreg r = c.nreg r := fun r hr => F₁ r (Or.inl hr)
  have k₁' : ∀ r, 2850 < r → c₁.nreg r = c.nreg r := fun r hr => F₁ r (by omega)
  have hTn₁ : ∀ i < m, c₁.nmem (h + i) = ν (N.tail (en i)) := fun i hi => by
    rw [L₁ _ (by omega)]; exact (hTn i hi).1
  have hHn₁ : ∀ i < m, c₁.nmem (h + k + i) = ν (N.head (en i)) := fun i hi => by
    rw [L₁ _ (by omega)]; exact (hHn i hi).1
  have hMs : 0 < 3 * L + 1 := by omega
  -- side `Z`
  obtain ⟨c₂, t₂, e₂, ht₂, S₂, hn₂, M₂, F₂, rr₂, rm₂, o₂⟩ :=
    fbSide_exec (P := P) (W := W) (C := C) (Z := Z) (o := 2240) hrot hKr hbd₀ hBs he hKP ℓ δ₀
      cn vn fn ok0 sr0 (Or.inr ⟨by omega, by omega⟩) (Y := B₀ + 28 * k + 3)
      (bz := B₀ + 22 * m') (sv := 1) (bK := h + 17 * k) (Xb := B₀ + 25 * k + 3)
      (Fb := B₀ + 33 * k + 3) (Lb := h + 12 * k) (h := h) (Db := h + 13 * k) (M := 3 * L + 1)
      (Sb := h + 18 * k) c₁ e₁.wb_right
      (enc_congr hE fun i hi => ⟨L₁ _ (by omega), L₁ _ (by omega), L₁ _ (by omega),
        L₁ _ (by omega), L₁ _ (by omega)⟩)
      (fun x => by rw [L₁ _ (by have := (cn x).2; omega)]; exact hz₀ x) K₁
      (fun i hi hm => by rw [L₁ _ (by omega)]; exact hXm i hi hm)
      (fun x hx => by rw [L₁ _ (by omega)]; exact hFm x hx) RL₁
      (fun i hi => by
        rw [hTn₁ i hi, D0₁ _ (hTn i hi).2.1, (hTn i hi).2.2])
      (fun i hi => by
        rw [hHn₁ i hi, D0₁ _ (hHn i hi).2.1, (hHn i hi).2.2]) hred₀ hCk hMs
      (by rw [F₁ _ (by omega), r74]) R₁.rRL (by rw [k₁' _ (by omega), r03]) R₁.rHh R₁.rD0
      R₁.rMs R₁.rS0 (by rw [k₁ _ (by omega), r960]) (by rw [R₁.rbL0]; ring) R₁.rFb R₁.rXb R₁.rY
      (by rw [R₁.rT00]; ring) R₁.rbz R₁.rone R₁.rbK (by rw [F₁ _ (by omega), r75])
      (by rw [R₁.rI00]; ring) (by rw [k₁ _ (by omega), r961])
      (by rw [k₁ _ (by omega), r962]) hmk hm' hVF ⟨l1, l2, l3, l4, l5⟩ l11 l12
      (fun i hi => by rw [hTn₁ i hi]; have := (hTn i hi).2.1; omega)
      (fun i hi => by rw [hHn₁ i hi]; have := (hHn i hi).2.1; omega)
      (by omega) (by omega) (by omega)
  have L₂ : ∀ a, a < h + 18 * k → c₂.nmem a = c₁.nmem a := fun a ha => M₂ a (Or.inl ha)
  have G₂ : ∀ r, 2200 ≤ r → r < 2240 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    F₂ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have R₂ : FbRegs c₂ h d k B₀ m' L := R₁.of G₂
  have k₂ : ∀ r, r ≠ 10 → (r < 300 ∨ 318 < r) → (r < 800 ∨ 840 < r) → (r < 2100 ∨
      (2248 ≤ r ∧ r < 2550) ∨ (2593 < r ∧ r < 2750) ∨ 2850 < r) →
      c₂.nreg r = c.nreg r := fun r h1 h2 h3 h4 => by
    rw [F₂ r h1 h2 h3 (by omega) (by omega) (by omega), F₁ r (by omega)]
  -- side `Zᶜ`
  obtain ⟨c₃, t₃, e₃, ht₃, S₃, hn₃, M₃, F₃, rr₃, rm₃, o₃⟩ :=
    fbSide_exec (P := P) (W := W) (C := C) (Z := Zᶜ) (o := 2244) hrot hKr hbd₁ hBs he hKP ℓ δ₁
      cn vn fn ok1 sr1 (Or.inr ⟨by omega, by omega⟩) (Y := B₀ + 28 * k + 3)
      (bz := B₀ + 22 * m') (sv := 0) (bK := h + 17 * k) (Xb := B₀ + 25 * k + 3)
      (Fb := B₀ + 33 * k + 3) (Lb := h + 12 * k) (h := h) (Db := h + 15 * k) (M := 3 * L + 1)
      (Sb := h + 78 * k) c₂ e₂.wb_right
      (enc_congr hE fun i hi => ⟨by rw [L₂ _ (by omega), L₁ _ (by omega)],
        by rw [L₂ _ (by omega), L₁ _ (by omega)], by rw [L₂ _ (by omega), L₁ _ (by omega)],
        by rw [L₂ _ (by omega), L₁ _ (by omega)], by rw [L₂ _ (by omega), L₁ _ (by omega)]⟩)
      (fun x => by
        rw [L₂ _ (by have := (cn x).2; omega), L₁ _ (by have := (cn x).2; omega)]
        exact hz₁ x)
      (fun x => by rw [L₂ _ (by have := (cn x).2; omega)]; exact K₁ x)
      (fun i hi hm => by rw [L₂ _ (by omega), L₁ _ (by omega)]; exact hXm i hi hm)
      (fun x hx => by rw [L₂ _ (by omega), L₁ _ (by omega)]; exact hFm x hx)
      (fun i hi => by rw [L₂ _ (by omega)]; exact RL₁ i hi)
      (fun i hi => by
        rw [L₂ (h + i) (by omega), hTn₁ i hi, L₂ _ (by have := (hTn i hi).2.1; omega),
          D1₁ _ (hTn i hi).2.1, (hTn i hi).2.2])
      (fun i hi => by
        rw [L₂ (h + k + i) (by omega), hHn₁ i hi, L₂ _ (by have := (hHn i hi).2.1; omega),
          D1₁ _ (hHn i hi).2.1, (hHn i hi).2.2]) hred₁ hCk hMs
      (by rw [k₂ _ (by omega) (by omega) (by omega) (by omega), r74]) R₂.rRL
      (by rw [k₂ _ (by omega) (by omega) (by omega) (by omega), r03]) R₂.rHh R₂.rD1
      R₂.rMs R₂.rS1 (by rw [F₂ _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), k₁ _ (by omega), r960]) (by rw [R₂.rbL1]; ring) R₂.rFb R₂.rXb R₂.rY
      (by rw [R₂.rT01]; ring) R₂.rbz R₂.rzero R₂.rbK
      (by rw [k₂ _ (by omega) (by omega) (by omega) (by omega), r75]) (by rw [R₂.rI01]; ring)
      (by rw [F₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        k₁ _ (by omega), r961])
      (by rw [F₂ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        k₁ _ (by omega), r962]) hmk hm' hVF ⟨l6, l7, l8, l9, l10⟩ l13 l14
      (fun i hi => by
        rw [L₂ (h + i) (by omega), hTn₁ i hi]; have := (hTn i hi).2.1; omega)
      (fun i hi => by
        rw [L₂ (h + k + i) (by omega), hHn₁ i hi]; have := (hHn i hi).2.1; omega)
      (by omega) (by omega) (by omega)
  have e0 : h + 18 * k + 2 * k = h + 20 * k := by ring
  have e0' : h + 18 * k + 32 * k = h + 50 * k := by ring
  rw [e0, e0'] at S₂
  have S₂' : SideOut K C Z hbd₀ Bs ψ vn nF ℓ δ₀ (h + 20 * k) (h + 50 * k) 2240 c₃ :=
    S₂.congr (fun a h1 h2 => M₃ a (Or.inl (by omega)))
      (fun a h1 h2 => M₃ a (Or.inl (by omega)))
      (fun j hj => F₃ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega,
    R₂.of fun r h1 h2 => F₃ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
    S₂', ?_, fun i hi => ?_, fun a ha => ?_, fun r h1 h2 h3 h4 => ?_, by rw [rr₃, rr₂, rr₁],
    by rw [rm₃, rm₂, rm₁], by rw [o₃, o₂, o₁]⟩
  · have e : h + 78 * k + 2 * k = h + 80 * k := by ring
    have e' : h + 78 * k + 32 * k = h + 110 * k := by ring
    rw [e, e'] at S₃
    exact S₃
  · rw [M₃ _ (Or.inl (by omega)), L₂ _ (by omega)]; exact I₁ i hi
  · rcases ha with ha | ha
    · rw [M₃ _ (Or.inl (by omega)), L₂ _ (by omega), L₁ _ ha]
    · rw [M₃ _ (Or.inr (by omega)), M₂ _ (Or.inr (by omega)), M₁ _ (Or.inr (by omega))]
  · rw [F₃ r h1 h2 h3 (by omega) (by omega) (by omega), k₂ r h1 h2 h3 h4]

end Sides

end NegSSSP

end PlanarFlow
