module

public import PlanarFlow.NegSSSP.Enc.HoistRunP
public import PlanarFlow.NegSSSP.Enc.PrmNode

/-!
# The node of the recursion as one fixed program, from the node's sizes only

`nodeFullP2 = pnProg ; nodeFullP`: **one statement**. `pnProg` (`PrmNode.lean`) computes the 21
primary values that `node_exec_fixedP` assumed in its registers (`HnPrim`) from **14 sizes** in
the registers `10610 … 10623` (`PnIn`: `nD k nV nF` of the maps of the two one-face instances,
`m w b B`, `Y S`) and from the plain arrays of the two instances (the weight bounds
`Wcᵢ = (srcW …).toNat` by a loop over `IS`, `LN`).

**`node_exec_fixedP'`**: the statement of `node_exec_fixedP` where the layout, the bounds of the
encoders, `W'` and `M` are no longer free but **defined** (and computed by the program):
`Pb₀ = Y + 16 S`, `Pb₁ = Pb₀ + w`, `p₀.I0 = Pb₀ + 2 w`, `p₁.I0 = p₀.END`,
`pᵢ.Lmax = feIsoB Aᵢ Nᵢ FNᵢ Wcᵢ`, `W' = pnW p₀ p₁`, `M = 2 nodeHN m b w B + 1`; the hypotheses
`hIn`, `hLm`, `hLW`, `hIW`, `hH`, `hM`, `hM2`, `h1382`, `hPrim` of `node_exec_fixedP` are gone
(derived), the 14 sizes `PnIn` and `9600 ≤ WN` are new. Extra cost: `t₀ ≤ pnCost p₀.nD p₁.nD =
9 (p₀.nD + p₁.nD) + 701` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge
  Monge.FR CmpAbs ModNat

/-- **The node of the recursion as one fixed statement, from its sizes.** -/
def nodeFullP2 : Stmt := .seq pnProg nodeFullP

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
open Classical in
/-- **The node of the recursion as one run of one fixed program, from the node's sizes** (see the
module docstring). -/
theorem node_exec_fixedP' (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
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
    (hPb₀ : Pb₀ = Y + 16 * S) (hPb₁ : Pb₁ = Y + 16 * S + w)
    (hI0₀ : p₀.I0 = Y + 16 * S + 2 * w) (hI0₁ : p₁.I0 = p₀.END)
    -- the word bounds of the encoders
    (hL₀ : p₀.Lmax = feIsoB p₀.A p₀.N p₀.FN
      (srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat)
    (hL₁ : p₁.Lmax = feIsoB p₁.A p₁.N p₁.FN
      (srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat)
    (hW' : W' = pnW p₀ p₁)
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
    (hMd : M = 2 * nodeHN m b w B + 1)
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
    (h9600 : 9600 ≤ WN) (hin : PnIn d₀.nreg p₀ p₁ m w b B Y S)
    (hBN : hnB p₀ p₁ Pb₀ Pb₁ W' M (nodeHN m b w B)
      (Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k) (Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k)
      (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat
      (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat ≤ WN) :
    ∃ (Hc₀ Hc₁ : ℕ), 4800 ≤ Hc₀ ∧ Hc₀ ≤ kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k ∧
      4800 ≤ Hc₁ ∧ Hc₁ ≤ kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k ∧
      ∃ d' t₀ t₁ t', ∃ o : Option (V → ℤ),
        Exec I WN nodeFullP2 d₀ d'
          (t₀ + (hpCost (hfPrmL 0) + hpCost (hfPrmL 0) + hpCost hnPrmL + (t₁ + t'))) ∧
        t₀ ≤ pnCost p₀.nD p₁.nD ∧
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
  have hb1 : 1 ≤ b := by rw [hb]; exact Finset.card_pos.2 hB
  obtain ⟨cD₀, cV₀, cF₀⟩ := fe_cards (k := fd₀.k) (D := fd₀.DQ) (V := fd₀.VQ) (F := fd₀.FQ) p₀
    hpD₀ hpk₀ hpV₀ hpF₀
  obtain ⟨cD₁, cV₁, cF₁⟩ := fe_cards (k := fd₁.k) (D := fd₁.DQ) (V := fd₁.VQ) (F := fd₁.FQ) p₁
    hpD₁ hpk₁ hpV₁ hpF₁
  have hN1₀ : Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k = MSSP.isoN1 p₀.A p₀.N p₀.FN := by
    unfold Klein.srcN1; rw [cD₀, cV₀, cF₀]
  have hN1₁ : Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k = MSSP.isoN1 p₁.A p₁.N p₁.FN := by
    unfold Klein.srcN1; rw [cD₁, cV₁, cF₁]
  have E₀ := pn_end p₀
  have E₁ := pn_end p₁
  have hEW : p₁.END ≤ W' := by rw [hW']; unfold pnW; omega
  -- the weight bounds: the loops read the plain arrays (kept by the simulation)
  have hWc₀ : 1 + pwS d₀.nmem (p₀.I0 + 3 * p₀.nD) (p₀.I0 + 4 * p₀.nD) p₀.nD =
      (srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat := by
    have hlt : ∀ d, (σ₀ d : ℕ) < p₀.nD := fun d => by
      have := (σ₀ d).isLt; omega
    have h := pw_srcW σ₀ (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))
      (faceLen_nonneg _ _ _) d₀.nmem (p₀.I0 + 3 * p₀.nD) (p₀.I0 + 4 * p₀.nD)
      (fun d => by
        rw [hS₀.nmem _ (by have := hlt d; omega)]; exact hQIS₀ d)
      (fun d => by
        rw [hS₀.nmem _ (by have := hlt d; omega)]; exact hQLN₀ d)
    rwa [← hpD₀] at h
  have hWc₁ : 1 + pwS d₀.nmem (p₁.I0 + 3 * p₁.nD) (p₁.I0 + 4 * p₁.nD) p₁.nD =
      (srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat := by
    have hlt : ∀ d, (σ₁ d : ℕ) < p₁.nD := fun d => by
      have := (σ₁ d).isLt; omega
    have h := pw_srcW σ₁ (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))
      (faceLen_nonneg _ _ _) d₀.nmem (p₁.I0 + 3 * p₁.nD) (p₁.I0 + 4 * p₁.nD)
      (fun d => by
        rw [hS₀.nmem _ (by have := hlt d; omega)]; exact hQIS₁ d)
      (fun d => by
        rw [hS₀.nmem _ (by have := hlt d; omega)]; exact hQLN₁ d)
    rwa [← hpD₁] at h
  have hW1 : pnW p₀ p₁ ≤ WN := by rw [← hW']; clear * - hWN; omega
  have hW2 : 2 * nodeHN m b w B + 1 ≤ WN := by
    rw [← hMd]; clear * - hWN; omega
  have hW3 : MSSP.isoN1 p₀.A p₀.N p₀.FN ≤ WN := by rw [← hN1₀]; exact hWN.2.2.2.2.2.1
  have hW4 : MSSP.isoN1 p₁.A p₁.N p₁.FN ≤ WN := by rw [← hN1₁]; exact hWN.2.2.2.2.2.2.1
  -- 1. the primary values
  obtain ⟨d₁, t₀, ex₀, ht₀, hP, hf, hm, hr, hrm, ho⟩ := pnProg_exec (P := I) d₀ hd₀ hin hI0₀
    hI0₁ (by rw [hWc₀]; exact hL₀) (by rw [hWc₁]; exact hL₁) hb1 hW1 hW2 hW3 hW4 h9600
  rw [hWc₀, hWc₁, ← hN1₀, ← hN1₁, ← hW', ← hMd, ← hPb₁, ← hPb₀] at hP
  have hS₁ : Sim 1000 W' M (W' + 1) c d₁ :=
    ⟨fun r hr' => by rw [hf r (Or.inl (by omega))]; exact hS₀.nreg r hr',
      fun r hr' => by rw [hf _ (Or.inl (by omega))]; exact hS₀.rreg r hr',
      fun a ha => by rw [hm]; exact hS₀.nmem a ha,
      fun a ha => by rw [hm]; exact hS₀.rmem a ha,
      by rw [ho]; exact hS₀.output⟩
  have hR₁ : ∀ r, 2600 ≤ r → r < 3748 → d₁.nreg r ≤ W' := fun r h h' => by
    rw [hf r (Or.inl (by omega))]; exact hR0 r h h'
  have hIn : Y + 16 * S ≤ Pb₀ ∧ Y + 16 * S ≤ Pb₁ ∧ Pb₀ + w ≤ p₀.I0 ∧ Pb₁ + w ≤ p₀.I0 ∧
      p₀.END ≤ p₁.I0 ∧ p₁.END ≤ W' := by
    refine ⟨by omega, by omega, by omega, by omega, by omega, hEW⟩
  have hLm₀ : feIsoB p₀.A p₀.N p₀.FN
      (srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat ≤ p₀.Lmax :=
    hL₀.ge
  have hLm₁ : feIsoB p₁.A p₁.N p₁.FN
      (srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat ≤ p₁.Lmax :=
    hL₁.ge
  have hB' : p₀.Lmax ≤ W' ∧ p₀.Inf + p₀.Lmax ≤ W' ∧
      2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1 ≤ W' ∧ p₁.Lmax ≤ W' ∧
      p₁.Inf + p₁.Lmax ≤ W' ∧ 2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1 ≤ W' := by
    rw [hW']; unfold pnW; omega
  have hM : 2 * nodeHN m b w B < M := by omega
  have hH1 : 1 ≤ nodeHN m b w B := by
    have h1 := (le_restB (w := w) (B := (3 * m + 2) * B) hb1).2
    have h2 : 1 ≤ bfB b ((3 * m + 2) * B) := by unfold bfB; omega
    unfold nodeHN; omega
  -- 2. the fixed node
  obtain ⟨Hc₀, Hc₁, g1, g2, g3, g4, d', t₁, t', o, ex, ht₁, ht', hpot, hstep, hout⟩ :=
    node_exec_fixedP C hfr hmssp hS hB ℓ δ₀ δ₁ hδ₀ hδ₁ fd₀ hq₀ hk₀ fd₁ hq₁ hk₁ σ₀ νv₀ τ₀ σ₁ νv₁
      τ₁ p₀ p₁ hpD₀ hpk₀ hpV₀ hpF₀ hpD₁ hpk₁ hpV₁ hpF₁ hN hb Pb₀ Pb₁ Z M₀ Y S W' B M WN I c
      hM₀ hZ hbZ hK₀ hK₁ hkk₀ hkk₁ hY hSz hIn hLm₀ hB'.1 hB'.2.1 hB'.2.2.1 hLm₁ hB'.2.2.2.1
      hB'.2.2.2.2.1 hB'.2.2.2.2.2 hWN hM hc hctx hx hTm hHm hSm hLm hD₀ hD₁ hz hpos₀ hpos₁
      hQRV₀ hQNT₀ hQNF₀ hQIS₀ hQLN₀ hQG₀ hQRV₁ hQNT₁ hQNF₁ hQIS₁ hQLN₁ hQG₁ hI hZi d₁ hS₁
      ex₀.wb_right hR₁ (by omega) (by omega) hP hBN
  exact ⟨Hc₀, Hc₁, g1, g2, g3, g4, d', t₀, t₁, t', o, Exec.seq ex₀ ex, ht₀, ht₁, ht', hpot,
    hstep, hout⟩

end NegSSSP

end PlanarFlow
