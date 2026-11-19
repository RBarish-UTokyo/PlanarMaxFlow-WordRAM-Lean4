module

public import PlanarFlow.NegSSSP.Enc.NodeBFA
public import PlanarFlow.NegSSSP.NL.NodeNatNRun

/-!
# The node of the recursion from the plain encodings of its two one-face instances

**`node_exec_natNNL_BF`**: in the node's configuration `c` (the one of `node_exec_natNNL`: the
node's data in `[Z, Y + 16 S)`, its reals, `NCtx`, `XCtx`, `NInv`, `IntAll`), with the **plain
arrays** of the maps `fd₀.Q`, `fd₁.Q` (`RV`, `NT`, `NF`, `IS`, `LN` of the reduced lengths
`redLen N ℓ δᵢ`, by numberings `σᵢ` of their darts, and the darts of the face) at `p₀.I0`,
`p₁.I0` above the positions `Pb₀`, `Pb₁`:

1. the two composed encoders `feProg p₀ ; feProg p₁` run on `c` within
   `feCost p₀ + feCost p₁` steps (`nbFe2_exec`), changing only the natural memory in
   `[p₀.β, p₀.END) ∪ [p₁.β, p₁.END)` and natural registers `≥ 1400`, so the node's context is
   kept (`NCtx` reads `800 … 825`, `XCtx` `930 … 945`; the reals are untouched, whence `NInv`,
   `IntAll`);
2. from the natural image `natOf 1000 W' M (W' + 1) c₁` of the configuration `c₁` they leave,
   `nodeProgNN` runs as in `node_exec_natNNL`, with Klein's slots at `pᵢ.β`, the residues at
   `pᵢ.RK`, the encodings `fePk pᵢ c₁.nmem` and some `Hcᵢ ≤ kcnHc pᵢ.A pᵢ.FN (pᵢ.N · pᵢ.Lmax)
   pᵢ.k`: same outcome (`NegSSSP.step`), same step bound (with `Kwᵢ = pᵢ.Kw`, `#D'ᵢ = pᵢ.N`).

So none of the hypotheses `FEncNatNL`, `fdHI ≤ Hc`, `KSlotN` of `node_exec_natNNL` remains; the
plain arrays are inputs. **Cost**: `feCost pᵢ` is quadratic at a node
(`nbFeCost_node_le`: `≤ 186624 m² + 416324 m + 1184` for `fd.q ≤ 18 m`, `fd.k² ≤ 1200 m`),
because the distances of the first root are computed by **Bellman–Ford** (`O(#V' · #D')`), hence
`BF` in the name.

The encoders run on `c` itself (natural instructions only, `feProg_natOnly`); `nodeProgNN` runs on
the natural image of the result, as `node_exec_natNNL` does. (The encoders cannot run on
`natOf … c` directly: they use natural registers `1400 … 2459`, and `natOf` keeps the residues
of the real registers in `1000 … 1999`.)
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge
  Monge.FR CmpAbs ModNat

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

theorem nb_ninv {W B : ℕ} {c c' : Config} (h : NInv W B c) (hr : c'.rreg = c.rreg)
    (hm : c'.rmem = c.rmem) : NInv W B c' := by
  simpa only [NInv, MemB, hr, hm] using h

theorem nb_intAll {c c' : Config} (h : IntAll c) (hr : c'.rreg = c.rreg)
    (hm : c'.rmem = c.rmem) : IntAll c' := by
  simpa only [IntAll, hr, hm] using h

theorem nb_wn {W' K H H' M WN : ℕ} (hH : H ≤ H')
    (h1 : 2 * W' + 2 + (2 * K + 1) + (2 * H' + 1) * (2 * H' + 1) + (2 * H' + 1) ≤ WN)
    (h2 : 2 * H' + 1 + 2 * M ≤ WN) :
    2 * W' + 2 + (2 * K + 1) + (2 * H + 1) * (2 * H + 1) + (2 * H + 1) ≤ WN ∧
      2 * H + 1 + 2 * M ≤ WN := by
  have := Nat.mul_le_mul (show 2 * H + 1 ≤ 2 * H' + 1 by omega)
    (show 2 * H + 1 ≤ 2 * H' + 1 by omega)
  generalize (2 * H + 1) * (2 * H + 1) = X at this ⊢
  generalize (2 * H' + 1) * (2 * H' + 1) = Y at this h1
  omega

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
open Classical in
/-- **The node of the recursion from the plain encodings of its one-face instances**, the
distances of the encoders by Bellman–Ford (see the module docstring). -/
theorem node_exec_natNNL_BF (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
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
    (hI : NInv W' B c) (hZi : IntAll c) :
    ∃ c₁ t₁, Exec I W' (.seq (feProg p₀) (feProg p₁)) c c₁ t₁ ∧ t₁ ≤ feCost p₀ + feCost p₁ ∧
      (∀ a, a < p₀.β ∨ p₀.END ≤ a → a < p₁.β ∨ p₁.END ≤ a → c₁.nmem a = c.nmem a) ∧
      (∀ r < 1400, c₁.nreg r = c.nreg r) ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧
      ∃ Hc₀ Hc₁ : ℕ, Hc₀ ≤ kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k ∧
        Hc₁ ≤ kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k ∧
      ∃ d' t', ∃ o : Option (V → ℤ),
        Exec I WN (nodeProgNN
          (kpnOf fd₀ (redLen N ℓ δ₀) p₀.NN p₀.Bw (fePk p₀ c₁.nmem) p₀.β p₀.RK Pb₀ Hc₀
            (2 * W' + 2) (W' + 1) M)
          (kpnOf fd₁ (redLen N ℓ δ₁) p₁.NN p₁.Bw (fePk p₁ c₁.nmem) p₁.β p₁.RK Pb₁ Hc₁
            (2 * W' + 2) (W' + 1) M) M
          (nodeHN m b w B) (W' + 1)) (natOf 1000 W' M (W' + 1) c₁) d' t' ∧
        t' ≤ 4 * (8 + (61 * m + 12)) + 3 +
          (partNCost P.card fd₀.k b p₀.Kw p₀.N + partNCost P.card fd₁.k b p₁.Kw p₁.N + 14) +
          4 * (bfCostP b + 4 * bfWP b + 22 * (b * b) + 2 * (cNegMach C).dij (w + 1) (m + w) +
            232 * m + 450 * w + 92 * b + 2917) ∧
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
  obtain ⟨hIn₁, hIn₂, hIn₃, hIn₄, hIn₅, hIn₆⟩ := hIn
  obtain ⟨hWN₁, hWN₂, hWN₃, hWN₄, hWN₅, hWN₆, hWN₇, hWN₈, hWN₉⟩ := hWN
  obtain ⟨o₀1, o₀2, o₀3, o₀4⟩ := nbFeP_ord p₀
  obtain ⟨o₁1, o₁2, o₁3, o₁4⟩ := nbFeP_ord p₁
  obtain ⟨cD₀, -, -⟩ := fe_cards (k := fd₀.k) (D := fd₀.DQ) (V := fd₀.VQ) (F := fd₀.FQ) p₀ hpD₀
    hpk₀ hpV₀ hpF₀
  obtain ⟨cD₁, -, -⟩ := fe_cards (k := fd₁.k) (D := fd₁.DQ) (V := fd₁.VQ) (F := fd₁.FQ) p₁ hpD₁
    hpk₁ hpV₁ hpF₁
  -- 1. the two encoders
  obtain ⟨c₁, t₁, e₁, ht₁, ⟨w₀, Hc₀, hv₀, hHI₀, hHle₀, hKS₀⟩, ⟨w₁, Hc₁, hv₁, hHI₁, hHle₁, hKS₁⟩,
      hm₁, hr₁, hrr₁, hrm₁, ho₁⟩ :=
    nbFe2_exec (P := I) (W := W') fd₀ fd₁ (redLen N ℓ δ₀) (redLen N ℓ δ₁) σ₀ νv₀ τ₀ σ₁ νv₁ τ₁
      p₀ p₁ hpD₀ hpk₀ hpV₀ hpF₀ hpD₁ hpk₁ hpV₁ hpF₁ hIn₅ hIn₆ hLm₀ hLW₀ hIW₀ hH₀ hLm₁ hLW₁ hIW₁
      hH₁ c hc hQRV₀ hQNT₀ hQNF₀ hQIS₀ hQLN₀ hQG₀ hQRV₁ hQNT₁ hQNF₁ hQIS₁ hQLN₁ hQG₁
  have hlow : ∀ a, a < p₀.I0 → c₁.nmem a = c.nmem a := fun a ha =>
    hm₁ a (Or.inl (by clear * - ha o₀1; omega))
      (Or.inl (by clear * - ha o₀1 o₀4 o₁1 hIn₅; omega))
  have hYI : Y ≤ p₀.I0 := by clear * - hIn₁ hIn₃; omega
  have hm₀ : 0 < M₀ := by clear * - hM₀; omega
  have hslot : ∀ j < 6, ∀ d < M₀, c₁.nmem (Z + j * M₀ + d) = c.nmem (Z + j * M₀ + d) :=
    fun j hj d hd => hlow _ (by
      have h1 : j * M₀ ≤ 5 * M₀ := Nat.mul_le_mul_right _ (by clear * - hj; omega)
      clear * - h1 hd hY hYI; omega)
  have hmM : m < M₀ := by clear * - hM₀; omega
  have hwM : w < M₀ := by clear * - hM₀; omega
  -- 2. the node from the configuration the encoders leave
  have hwn₀ := nb_wn (K := p₀.Kw) hHle₀ hWN₂ hWN₄
  have hwn₁ := nb_wn (K := p₁.Kw) hHle₁ hWN₃ hWN₅
  obtain ⟨d', t', o, ex, ht', hpot, hstep, hout⟩ :=
    node_exec_natNNL C hfr hmssp hS hB ℓ δ₀ δ₁ hδ₀ hδ₁ fd₀ hq₀ hk₀ fd₁ hq₁ hk₁
      (n₀ := p₀.NN) (Bw₀ := p₀.Bw) (σ₀ := srcNum σ₀) (wt₀ := w₀) (Pk₀ := fePk p₀ c₁.nmem) hv₀
      (Hc₀ := Hc₀) hHI₀
      (n₁ := p₁.NN) (Bw₁ := p₁.Bw) (σ₁ := srcNum σ₁) (wt₁ := w₁) (Pk₁ := fePk p₁ c₁.nmem) hv₁
      (Hc₁ := Hc₁) hHI₁ hN hb Pb₀ Pb₁ p₀.β p₁.β p₀.RK p₁.RK Z M₀ Y S W' B M WN I c₁ hM₀ hZ hbZ
      hK₀ hK₁ hkk₀ hkk₁ hY hSz
      ⟨hIn₁, hIn₂, by clear * - hIn₁ hIn₃ o₀1; omega, by clear * - hIn₁ hIn₃ o₀1 o₀4 o₁1 hIn₅; omega,
        by clear * - hIn₁ hIn₃ o₀1 o₀2; omega,
        by clear * - hIn₁ hIn₃ o₀1 o₀4 o₁1 o₁2 hIn₅; omega⟩
      ⟨by clear * - hIn₁ hIn₃ o₀1 o₀4 o₁1 o₁4 hIn₅ hIn₆; omega,
        by clear * - hIn₃ o₀1 o₀4 o₁1 o₁4 hIn₅ hIn₆; omega,
        by clear * - hIn₄ o₀1 o₀4 o₁1 o₁4 hIn₅ hIn₆; omega,
        by rw [cD₀]; clear * - o₀3 o₁1 o₁4 hIn₅ hIn₆; omega,
        by rw [cD₁]; clear * - o₁3 hIn₆; omega,
        by have := p₀.kw_eq.2; clear * - this o₀4 o₁1 o₁4 hIn₅ hIn₆; omega,
        by have := p₁.kw_eq.2; clear * - this o₁4 hIn₆; omega⟩
      ⟨hWN₁, hwn₀.1, hwn₁.1, hwn₀.2, hwn₁.2, hWN₆, hWN₇, hWN₈, hWN₉⟩ hM e₁.wb_right
      (hctx.of fun r h1 h2 => hr₁ r (by clear * - h2; omega))
      (hx.of fun r h1 h2 => hr₁ r (by clear * - h2; omega))
      (fun d hd => by rw [hslot 0 (by norm_num) d (by clear * - hd hmM; omega)]; exact hTm d hd)
      (fun d hd => by rw [hslot 1 (by norm_num) d (by clear * - hd hmM; omega)]; exact hHm d hd)
      (fun d hd => by rw [hslot 2 (by norm_num) d (by clear * - hd hmM; omega)]; exact hSm d hd)
      (fun d hd => by rw [hrm₁]; exact hLm d hd)
      (fun v hv => by rw [hrm₁]; exact hD₀ v hv)
      (fun v hv => by rw [hrm₁]; exact hD₁ v hv)
      (fun a ha => by rw [hlow a (by clear * - ha hY hYI; omega)]; exact hz a ha)
      (fun x hx => by
        have := hN.lt _ (bdry_sub_verts hx)
        rw [hlow _ (by clear * - this hIn₃; omega)]; exact hpos₀ x hx)
      (fun x hx => by
        have := hN.lt _ (bdry_sub_verts hx)
        rw [hlow _ (by clear * - this hIn₄; omega)]; exact hpos₁ x hx)
      hKS₀ hKS₁ (nb_ninv hI hrr₁ hrm₁) (nb_intAll hZi hrr₁ hrm₁)
  refine ⟨c₁, t₁, e₁, ht₁, hm₁, hr₁, hrr₁, hrm₁, Hc₀, Hc₁, hHle₀, hHle₁, d', t', o, ex, ?_, hpot,
    hstep, hout.trans ho₁⟩
  rw [cD₀, cD₁] at ht'
  exact ht'

end NegSSSP

end PlanarFlow
