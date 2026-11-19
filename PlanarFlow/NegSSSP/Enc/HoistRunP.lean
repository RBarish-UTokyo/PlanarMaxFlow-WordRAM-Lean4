module

public import PlanarFlow.NegSSSP.Enc.HoistPrmN

/-!
# The node of the recursion as one fixed program, with its parameters computed on the machine

`nodeFullP = hpProg 10000 10600 (hfPrmL 10530) ; hpProg 10200 10600 (hfPrmL 10540) ;
hpProg 10400 10600 hnPrmL ; nodeFullT`: **one statement** (independent of the instance).

**`node_exec_fixedP`**: under the hypotheses of `node_exec_natNNL_Dk1`, `M ≥ 2`,
`1382 ≤ WN`, the 21 **primary values** in the registers `10530 … 10558` of the start `d₀`
(`HnPrim`: the six constants `nD k nV nF I0 Lmax` of each encoder, `Pb₀ Pb₁ W' M`,
`H = nodeHN m b w B`, `N₁ᵢ = srcN1 …` and `Wcᵢ = (srcW …).toNat` of the two instances) and the
word bound `hnB … ≤ WN` of the parameters, the fixed statement runs from `d₀` within
`2 hpCost (hfPrmL 0) + hpCost hnPrmL + t₁ + t'` steps (`t₁ ≤ feCostDk p₀ + feCostDk p₁ + 8`,
`t'` the bound of `node_exec_natNNL_Dk1` `+ 2`), with the outcome of `node_exec_natNNL_Dk1`.
All 340 parameters of the fixed encoders and node are computed by the machine (straight-line
`constN`/`copyN`/`mulN`/`addN`/`subN`), the bounds `Hcᵢ` copied from the encoders.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge
  Monge.FR CmpAbs ModNat

/-- **The node of the recursion as one fixed statement, parameters included.** -/
def nodeFullP : Stmt :=
  .seq (hpProg 10000 10600 (hfPrmL 10530)) <| .seq (hpProg 10200 10600 (hfPrmL 10540)) <|
    .seq (hpProg 10400 10600 hnPrmL) nodeFullT

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
open Classical in
/-- **The node of the recursion as one run of one fixed program, parameters computed on the
machine** (see the module docstring). -/
theorem node_exec_fixedP (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {P P₀ P₁ : Finset D} (hS : SplitF N P P₀ P₁) (hB : (bdry N P₀ P₁).Nonempty) (ℓ : D → ℤ)
    (δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    (fd₀ : FaceData N P₀ (bdry N P₀ P₁)) (hq₀ : fd₀.q ≤ 18 * P.card)
    (hk₀ : fd₀.k ^ 2 ≤ 1200 * P.card)
    (fd₁ : FaceData N P₁ (bdry N P₀ P₁)) (hq₁ : fd₁.q ≤ 18 * P.card)
    (hk₁ : fd₁.k ^ 2 ≤ 1200 * P.card)
    -- the plain numberings and the constants of the two encoders
    (σ₀ : fd₀.DQ ≃ Fin (Fintype.card fd₀.DQ)) (νv₀ : fd₀.VQ ≃ Fin (Fintype.card fd₀.VQ))
    (τ₀ : fd₀.FQ ≃ Fin (Fintype.card fd₀.FQ))
    (σ₁ : fd₁.DQ ≃ Fin (Fintype.card fd₁.DQ)) (νv₁ : fd₁.VQ ≃ Fin (Fintype.card fd₁.VQ))
    (τ₁ : fd₁.FQ ≃ Fin (Fintype.card fd₁.FQ)) (p₀ p₁ : FeP)
    (hpD₀ : p₀.nD = Fintype.card fd₀.DQ) (hpk₀ : p₀.k = fd₀.k)
    (hpV₀ : p₀.nV = Fintype.card fd₀.VQ) (hpF₀ : p₀.nF = Fintype.card fd₀.FQ)
    (hpD₁ : p₁.nD = Fintype.card fd₁.DQ) (hpk₁ : p₁.k = fd₁.k)
    (hpV₁ : p₁.nV = Fintype.card fd₁.VQ) (hpF₁ : p₁.nF = Fintype.card fd₁.FQ)
    {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (hN : NodeEnc N P₀ P₁ m w e ν ι)
    (hb : b = (bdry N P₀ P₁).card)
    (Pb₀ Pb₁ Z M₀ Y S W' B M WN : ℕ) (I : Input) (c : Config)
    (hM₀ : M₀ = m + w + 1) (hZ : loB m w ≤ Z) (hbZ : bfWP b < Z)
    (hK₀ : 2 * p₀.Kw + 1 < Z) (hK₁ : 2 * p₁.Kw + 1 < Z)
    (hkk₀ : p₀.NN + fd₀.k * fd₀.k ≤ Z) (hkk₁ : p₁.NN + fd₁.k * fd₁.k ≤ Z)
    (hY : Z + 22 * M₀ ≤ Y)
    (hSz : w ≤ S ∧ b * b ≤ S ∧ fd₀.k ≤ S ∧ fd₁.k ≤ S)
    -- the layout: the node's data, the positions, then the two encoders
    (hIn : Y + 16 * S ≤ Pb₀ ∧ Y + 16 * S ≤ Pb₁ ∧ Pb₀ + w ≤ p₀.I0 ∧ Pb₁ + w ≤ p₀.I0 ∧
      p₀.END ≤ p₁.I0 ∧ p₁.END ≤ W')
    -- the word bounds of the encoders
    (hLm₀ : feIsoB p₀.A p₀.N p₀.FN
      (srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat ≤ p₀.Lmax)
    (hLW₀ : p₀.Lmax ≤ W') (hIW₀ : p₀.Inf + p₀.Lmax ≤ W')
    (hH₀ : 2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1 ≤ W')
    (hLm₁ : feIsoB p₁.A p₁.N p₁.FN
      (srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat ≤ p₁.Lmax)
    (hLW₁ : p₁.Lmax ≤ W') (hIW₁ : p₁.Inf + p₁.Lmax ≤ W')
    (hH₁ : 2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1 ≤ W')
    -- the word bounds of the node
    (hWN : 2 * W' + 1 + M * M + M ≤ WN ∧
      2 * W' + 2 + (2 * p₀.Kw + 1) +
          (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) *
            (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) +
          (2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1) ≤ WN ∧
      2 * W' + 2 + (2 * p₁.Kw + 1) +
          (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1) *
            (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1) +
          (2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1) ≤ WN ∧
      2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1 + 2 * M ≤ WN ∧
      2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1 + 2 * M ≤ WN ∧
      Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k ≤ WN ∧ Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k ≤ WN ∧
      (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat ≤ WN ∧
      (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat ≤ WN)
    (hM : 2 * nodeHN m b w B < M)
    (hc : WordsBounded W' c) (hctx : NCtx m w b Z M₀ c) (hx : XCtx Y S c)
    (hTm : ∀ d < m, c.nmem (Z + 0 * M₀ + d) = encT N e ν d)
    (hHm : ∀ d < m, c.nmem (Z + 1 * M₀ + d) = encH N e ν d)
    (hSm : ∀ d < m, c.nmem (Z + 2 * M₀ + d) = encS P₀ e d)
    (hLm : ∀ d < m, c.rmem (Z + 3 * M₀ + d) = ℓ (e d))
    (hD₀ : ∀ v < w, c.rmem (Z + 4 * M₀ + v) = δ₀ (ι v))
    (hD₁ : ∀ v < w, c.rmem (Z + 5 * M₀ + v) = δ₁ (ι v))
    (hz : ∀ a < Z, c.nmem a = 0)
    (hpos₀ : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₀ + ν x) < fd₀.k ∧
      fd₀.Q.tail (fd₀.g (c.nmem (Pb₀ + ν x))) = fd₀.j x)
    (hpos₁ : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₁ + ν x) < fd₁.k ∧
      fd₁.Q.tail (fd₁.g (c.nmem (Pb₁ + ν x))) = fd₁.j x)
    -- the plain arrays of the two maps
    (hQRV₀ : ∀ d, c.nmem (p₀.I0 + σ₀ d) = σ₀ (fd₀.Q.rev d))
    (hQNT₀ : ∀ d, c.nmem (p₀.I0 + p₀.nD + σ₀ d) = νv₀ (fd₀.Q.tail d))
    (hQNF₀ : ∀ d, c.nmem (p₀.I0 + 2 * p₀.nD + σ₀ d) = τ₀ (fd₀.Q.face d))
    (hQIS₀ : ∀ d, c.nmem (p₀.I0 + 3 * p₀.nD + σ₀ d) = if d ∈ fd₀.P'.image fd₀.e then 1 else 0)
    (hQLN₀ : ∀ d, c.nmem (p₀.I0 + 4 * p₀.nD + σ₀ d) =
      (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀) d).toNat)
    (hQG₀ : ∀ i < fd₀.k, c.nmem (p₀.I0 + 5 * p₀.nD + i) = σ₀ (fd₀.g i))
    (hQRV₁ : ∀ d, c.nmem (p₁.I0 + σ₁ d) = σ₁ (fd₁.Q.rev d))
    (hQNT₁ : ∀ d, c.nmem (p₁.I0 + p₁.nD + σ₁ d) = νv₁ (fd₁.Q.tail d))
    (hQNF₁ : ∀ d, c.nmem (p₁.I0 + 2 * p₁.nD + σ₁ d) = τ₁ (fd₁.Q.face d))
    (hQIS₁ : ∀ d, c.nmem (p₁.I0 + 3 * p₁.nD + σ₁ d) = if d ∈ fd₁.P'.image fd₁.e then 1 else 0)
    (hQLN₁ : ∀ d, c.nmem (p₁.I0 + 4 * p₁.nD + σ₁ d) =
      (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁) d).toNat)
    (hQG₁ : ∀ i < fd₁.k, c.nmem (p₁.I0 + 5 * p₁.nD + i) = σ₁ (fd₁.g i))
    (hI : NInv W' B c) (hZi : IntAll c)
    (d₀ : Config) (hS₀ : Sim 1000 W' M (W' + 1) c d₀) (hd₀ : WordsBounded WN d₀)
    (hR0 : ∀ r, 2600 ≤ r → r < 3748 → d₀.nreg r ≤ W') 
    -- the primary values of the parameter program and its word bounds
    (hM2 : 2 ≤ M) (h1382 : 1382 ≤ WN)
    (hPrim : HnPrim d₀.nreg p₀ p₁ Pb₀ Pb₁ W' M (nodeHN m b w B)
      (Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k) (Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k)
      (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat
      (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat)
    (hBN : hnB p₀ p₁ Pb₀ Pb₁ W' M (nodeHN m b w B)
      (Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k) (Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k)
      (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat
      (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat ≤ WN) :
    ∃ (Hc₀ Hc₁ : ℕ), 4800 ≤ Hc₀ ∧ Hc₀ ≤ kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k ∧
      4800 ≤ Hc₁ ∧ Hc₁ ≤ kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k ∧
      ∃ d' t₁ t', ∃ o : Option (V → ℤ),
        Exec I WN nodeFullP d₀ d' (hpCost (hfPrmL 0) + hpCost (hfPrmL 0) + hpCost hnPrmL + (t₁ + t')) ∧
        t₁ ≤ feCostDk p₀ + feCostDk p₁ + 8 ∧
        t' ≤ 4 * (8 + (61 * m + 12)) + 3 +
          (partNCost P.card fd₀.k b p₀.Kw p₀.N + partNCost P.card fd₁.k b p₁.Kw p₁.N + 14) +
          4 * (bfCostP b + 4 * bfWP b + 22 * (b * b) + 2 * (cNegMach C).dij (w + 1) (m + w) +
            232 * m + 450 * w + 92 * b + 2917) + 2 ∧
        PotOut ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).join
          (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁))) o ∧
        (∀ bf : DDG V → DDG V → Option (V → ℤ),
          bf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) =
            o →
          (step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = none ∧ d'.nreg 990 ≠ 0) ∨
          (∃ f, step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = some f ∧ d'.nreg 990 = 0 ∧
            ∀ x ∈ verts N (P₀ ∪ P₁),
              (f x : ℝ) = sgnD (nodeHN m b w B) M (d'.nmem (W' + 1 + (Z + 20 * M₀ + ν x))))) ∧
        d'.output = c.output := by
  classical
  obtain ⟨hIn₁, hIn₂, hIn₃, hIn₄, hIn₅, hIn₆⟩ := hIn
  have hW1 : W' ≤ WN := by clear * - hWN; omega
  have o₀ := nbFeP_ord p₀
  have o₁ := nbFeP_ord p₁
  have hEI₀ : p₀.END + p₀.Inf ≤ WN := by
    have : p₀.END ≤ p₁.END := by
      obtain ⟨x1, x2, x3, x4⟩ := o₁; clear * - x1 x2 x3 x4 hIn₅; omega
    clear * - this hIn₆ hIW₀ hWN; omega
  have hEI₁ : p₁.END + p₁.Inf ≤ WN := by clear * - hIn₆ hIW₁ hWN; omega
  have h942 : 942 ≤ WN := by clear * - h1382; omega
  obtain ⟨a0, a1, a2, a3, a4, a5, b0, b1, b2, b3, b4, b5, c0, c1, c2, c3, c4, c5, c6, c7, c8⟩ :=
    hPrim
  -- 1. the parameters of the two encoders, then of the node
  obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁'⟩ := hfPrm_exec (I := I) 10000 10530 (Or.inl ⟨rfl, rfl⟩)
    p₀ d₀ hd₀ hEI₀ h942 a0 a1 a2 a3 a4 a5
  have k₁ : ∀ r, 10110 ≤ r → r ≠ 10600 → r ≠ 10601 → c₁.nreg r = d₀.nreg r := fun r h h' h'' =>
    f₁ r (Or.inr h) h' h''
  obtain ⟨c₂, e₂, v₂, f₂, m₂, r₂, rm₂, o₂⟩ := hfPrm_exec (I := I) 10200 10540 (Or.inr ⟨rfl, rfl⟩)
    p₁ c₁ e₁.wb_right hEI₁ h942 ((k₁ _ (by omega) (by omega) (by omega)).trans b0)
    ((k₁ _ (by omega) (by omega) (by omega)).trans b1)
    ((k₁ _ (by omega) (by omega) (by omega)).trans b2)
    ((k₁ _ (by omega) (by omega) (by omega)).trans b3)
    ((k₁ _ (by omega) (by omega) (by omega)).trans b4)
    ((k₁ _ (by omega) (by omega) (by omega)).trans b5)
  have k₂ : ∀ r, 10310 ≤ r → r ≠ 10600 → r ≠ 10601 → c₂.nreg r = d₀.nreg r := fun r h h' h'' =>
    (f₂ r (Or.inr h) h' h'').trans (k₁ r (by omega) h' h'')
  have hP₂ : HnPrim c₂.nreg p₀ p₁ Pb₀ Pb₁ W' M (nodeHN m b w B)
      (Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k) (Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k)
      (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat
      (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat :=
    ⟨(k₂ _ (by omega) (by omega) (by omega)).trans a0, (k₂ _ (by omega) (by omega) (by omega)).trans a1,
      (k₂ _ (by omega) (by omega) (by omega)).trans a2, (k₂ _ (by omega) (by omega) (by omega)).trans a3,
      (k₂ _ (by omega) (by omega) (by omega)).trans a4, (k₂ _ (by omega) (by omega) (by omega)).trans a5,
      (k₂ _ (by omega) (by omega) (by omega)).trans b0, (k₂ _ (by omega) (by omega) (by omega)).trans b1,
      (k₂ _ (by omega) (by omega) (by omega)).trans b2, (k₂ _ (by omega) (by omega) (by omega)).trans b3,
      (k₂ _ (by omega) (by omega) (by omega)).trans b4, (k₂ _ (by omega) (by omega) (by omega)).trans b5,
      (k₂ _ (by omega) (by omega) (by omega)).trans c0, (k₂ _ (by omega) (by omega) (by omega)).trans c1,
      (k₂ _ (by omega) (by omega) (by omega)).trans c2, (k₂ _ (by omega) (by omega) (by omega)).trans c3,
      (k₂ _ (by omega) (by omega) (by omega)).trans c4, (k₂ _ (by omega) (by omega) (by omega)).trans c5,
      (k₂ _ (by omega) (by omega) (by omega)).trans c6, (k₂ _ (by omega) (by omega) (by omega)).trans c7,
      (k₂ _ (by omega) (by omega) (by omega)).trans c8⟩
  obtain ⟨c₃, e₃, v₃, f₃, m₃, r₃, rm₃, o₃⟩ := hnPrm_exec (I := I) c₂ e₂.wb_right hP₂ hBN h1382
  -- 2. the configuration of the fixed node
  have low : ∀ r, r < 10000 → c₃.nreg r = d₀.nreg r := fun r hr => by
    rw [f₃ r (Or.inl (by omega)) (by omega) (by omega), f₂ r (Or.inl (by omega)) (by omega)
      (by omega), f₁ r (Or.inl hr) (by omega) (by omega)]
  have mem3 : c₃.nmem = d₀.nmem := by rw [m₃, m₂, m₁]
  have hS₃ : Sim 1000 W' M (W' + 1) c c₃ :=
    ⟨fun r hr => by rw [low r (by omega)]; exact hS₀.nreg r hr,
      fun r hr => by rw [low _ (by omega)]; exact hS₀.rreg r hr,
      fun a ha => by rw [mem3]; exact hS₀.nmem a ha,
      fun a ha => by rw [mem3]; exact hS₀.rmem a ha,
      by rw [o₃, o₂, o₁']; exact hS₀.output⟩
  have hR₃ : ∀ r, 2600 ≤ r → r < 3748 → c₃.nreg r ≤ W' := fun r h h' => by
    rw [low r (by omega)]; exact hR0 r h h'
  have hP₀ : ∀ j < 110, c₃.nreg (10000 + j) = feV p₀ j := fun j hj => by
    rw [f₃ _ (Or.inl (by omega)) (by omega) (by omega), f₂ _ (Or.inl (by omega)) (by omega)
      (by omega)]
    exact v₁ j hj
  have hP₁ : ∀ j < 110, c₃.nreg (10200 + j) = feV p₁ j := fun j hj => by
    rw [f₃ _ (Or.inl (by omega)) (by omega) (by omega)]
    exact v₂ j hj
  obtain ⟨cD₀, -, -⟩ := fe_cards (k := fd₀.k) (D := fd₀.DQ) (V := fd₀.VQ) (F := fd₀.FQ) p₀ hpD₀
    hpk₀ hpV₀ hpF₀
  obtain ⟨cD₁, -, -⟩ := fe_cards (k := fd₁.k) (D := fd₁.DQ) (V := fd₁.VQ) (F := fd₁.FQ) p₁ hpD₁
    hpk₁ hpV₁ hpF₁
  have hR₀K : kpnOf fd₀ (redLen N ℓ δ₀) p₀.NN p₀.Bw (fePk p₀ fun _ => 0) p₀.β p₀.RK Pb₀ 0
      (2 * W' + 2) (W' + 1) M = hnRec p₀ Pb₀ (Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k)
        (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat W' M := by
    unfold kpnOf hnRec
    rw [fePk_len, cD₀, hpk₀]
  have hR₁K : kpnOf fd₁ (redLen N ℓ δ₁) p₁.NN p₁.Bw (fePk p₁ fun _ => 0) p₁.β p₁.RK Pb₁ 0
      (2 * W' + 2) (W' + 1) M = hnRec p₁ Pb₁ (Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k)
        (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat W' M := by
    unfold kpnOf hnRec
    rw [fePk_len, cD₁, hpk₁]
  have hPN : ∀ j < 115, j ≠ 11 → j ≠ 12 → j ≠ 66 → j ≠ 67 → c₃.nreg (10400 + j) =
      hnV (kpnOf fd₀ (redLen N ℓ δ₀) p₀.NN p₀.Bw (fePk p₀ fun _ => 0) p₀.β p₀.RK Pb₀ 0
          (2 * W' + 2) (W' + 1) M)
        (kpnOf fd₁ (redLen N ℓ δ₁) p₁.NN p₁.Bw (fePk p₁ fun _ => 0) p₁.β p₁.RK Pb₁ 0
          (2 * W' + 2) (W' + 1) M) M (nodeHN m b w B) (W' + 1) j := fun j hj _ _ _ _ => by
    rw [hR₀K, hR₁K]; exact v₃ j hj
  have hIn : Y + 16 * S ≤ Pb₀ ∧ Y + 16 * S ≤ Pb₁ ∧ Pb₀ + w ≤ p₀.I0 ∧ Pb₁ + w ≤ p₀.I0 ∧
      p₀.END ≤ p₁.I0 ∧ p₁.END ≤ W' := ⟨hIn₁, hIn₂, hIn₃, hIn₄, hIn₅, hIn₆⟩
  -- 3. the fixed node
  obtain ⟨Hc₀, Hc₁, g1, g2, g3, g4, d', t₁, t', o, ex, ht₁, ht', hpot, hstep, hout⟩ :=
    node_exec_fixed C hfr hmssp hS hB ℓ δ₀ δ₁ hδ₀ hδ₁ fd₀ hq₀ hk₀ fd₁ hq₁ hk₁ σ₀ νv₀ τ₀ σ₁ νv₁ τ₁ p₀ p₁ hpD₀ hpk₀ hpV₀ hpF₀ hpD₁ hpk₁ hpV₁ hpF₁ hN hb Pb₀ Pb₁ Z M₀ Y S W' B M WN I c hM₀ hZ hbZ hK₀ hK₁ hkk₀ hkk₁ hY hSz hIn hLm₀ hLW₀ hIW₀ hH₀ hLm₁ hLW₁ hIW₁ hH₁ hWN hM hc hctx hx hTm hHm hSm hLm hD₀ hD₁ hz hpos₀ hpos₁ hQRV₀ hQNT₀ hQNF₀ hQIS₀ hQLN₀ hQG₀ hQRV₁ hQNT₁ hQNF₁ hQIS₁ hQLN₁ hQG₁ hI hZi c₃ hS₃ e₃.wb_right hR₃ hM2 hP₀ hP₁ hPN
  refine ⟨Hc₀, Hc₁, g1, g2, g3, g4, d', t₁, t', o,
    (Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ ex))).cast (by omega), ht₁, ht', hpot, hstep,
    hout⟩

end NegSSSP

end PlanarFlow
