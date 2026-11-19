module

public import PlanarFlow.NegSSSP.Enc.HoistRunA

/-!
# The node of the recursion as one fixed program

**`node_exec_fixed`**: under the hypotheses of `node_exec_natNNL_Dk1` (the node of the recursion
from the plain arrays of its two one-face instances, on natural words), plus the parameters of the
fixed program in the registers `≥ 10000` of the start `d₀` (`feVL pᵢ` at `10000`, `10200`; the
node's parameters `hnVL …` at `10400` **except** the four entries `2 Hcᵢ + 1`, `Hcᵢ`, which the
program itself copies from the encoders' register `3325` = renamed `2125`), and `M ≥ 2`:
**one run of the fixed statement `nodeFullT`** (independent of the instance) from `d₀`, within
`t₁ + t'` steps, `t₁ ≤ feCostDk p₀ + feCostDk p₁ + 8`, `t'` the bound of `node_exec_natNNL_Dk1`
`+ 2`, with the outcome of `NegSSSP.step` read back as in `node_exec_natNNL_Dk1`; the bounds
satisfy `4800 ≤ Hcᵢ ≤ kcnHc …`.

The proof is that of `node_exec_natNNL_Dk1`, with the two encoders run separately
(`fhFin_exec`, which exports `Hc` in `2125`), each renamed, lifted (`Exec.lift_trunc`,
`Exec.lift`) and replaced by the fixed encoder (`feFix_exec`), the saves `hfSave`, and the node
replaced by `nodeFixT` (`nodeFix_exec`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge
  Monge.FR CmpAbs ModNat

theorem hnV_11 (p₀ p₁ : KPN) (M H βN : ℕ) : hnV p₀ p₁ M H βN 11 = 2 * p₀.Hc + 1 := by
  kernel_rfl
theorem hnV_12 (p₀ p₁ : KPN) (M H βN : ℕ) : hnV p₀ p₁ M H βN 12 = p₀.Hc := by kernel_rfl
theorem hnV_66 (p₀ p₁ : KPN) (M H βN : ℕ) : hnV p₀ p₁ M H βN 66 = 2 * p₁.Hc + 1 := by
  kernel_rfl
theorem hnV_67 (p₀ p₁ : KPN) (M H βN : ℕ) : hnV p₀ p₁ M H βN 67 = p₁.Hc := by kernel_rfl

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
open Classical in
/-- **The node of the recursion as one run of one fixed program** (see the module docstring). -/
theorem node_exec_fixed (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
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
    -- the parameters of the fixed program (all but the bounds `Hcᵢ`, computed by the encoders)
    (hM2 : 2 ≤ M)
    (hP₀ : ∀ j < 110, d₀.nreg (10000 + j) = feV p₀ j)
    (hP₁ : ∀ j < 110, d₀.nreg (10200 + j) = feV p₁ j)
    (hPN : ∀ j < 115, j ≠ 11 → j ≠ 12 → j ≠ 66 → j ≠ 67 → d₀.nreg (10400 + j) =
      hnV (kpnOf fd₀ (redLen N ℓ δ₀) p₀.NN p₀.Bw (fePk p₀ fun _ => 0) p₀.β p₀.RK Pb₀ 0
          (2 * W' + 2) (W' + 1) M)
        (kpnOf fd₁ (redLen N ℓ δ₁) p₁.NN p₁.Bw (fePk p₁ fun _ => 0) p₁.β p₁.RK Pb₁ 0
          (2 * W' + 2) (W' + 1) M) M (nodeHN m b w B) (W' + 1) j) :
    ∃ (Hc₀ Hc₁ : ℕ), 4800 ≤ Hc₀ ∧ Hc₀ ≤ kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k ∧
      4800 ≤ Hc₁ ∧ Hc₁ ≤ kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k ∧
      ∃ d' t₁ t', ∃ o : Option (V → ℤ),
        Exec I WN nodeFullT d₀ d' (t₁ + t') ∧
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
  obtain ⟨hWN₁, hWN₂, hWN₃, hWN₄, hWN₅, hWN₆, hWN₇, hWN₈, hWN₉⟩ := hWN
  obtain ⟨o₀1, o₀2, o₀3, o₀4⟩ := nbFeP_ord p₀
  obtain ⟨o₁1, o₁2, o₁3, o₁4⟩ := nbFeP_ord p₁
  obtain ⟨cD₀, -, -⟩ := fe_cards (k := fd₀.k) (D := fd₀.DQ) (V := fd₀.VQ) (F := fd₀.FQ) p₀ hpD₀
    hpk₀ hpV₀ hpF₀
  obtain ⟨cD₁, -, -⟩ := fe_cards (k := fd₁.k) (D := fd₁.DQ) (V := fd₁.VQ) (F := fd₁.FQ) p₁ hpD₁
    hpk₁ hpV₁ hpF₁
  have hβ₀ : p₀.β = p₀.I0 + 5 * p₀.nD + p₀.k := rfl
  have hβ₁ : p₁.β = p₁.I0 + 5 * p₁.nD + p₁.k := rfl
  have hWW : W' ≤ WN := by clear * - hWN₁; omega
  have hEW₀ : p₀.β < W' := by clear * - o₀4 o₁1 o₁4 hIn₅ hIn₆; omega
  -- 1. the start of the encoders: the truncation of `d₀`, registers renamed
  have htw : WordsBounded W' (trunc nbU W' d₀) :=
    wordsBounded_trunc (fun r hr => by
        simp only [nbU, decide_eq_true_eq] at hr; exact hR0 r hr.1 hr.2)
      (fun a ha => by rw [hS₀.nmem a ha]; exact hc.2 a)
  set y₀ := rnC nbSwap.symm (trunc nbU W' d₀) with hy₀
  have hy₀w : WordsBounded W' y₀ := rn_wb htw
  have hy₀m : ∀ a ≤ W', y₀.nmem a = c.nmem a := fun a ha => by
    show (if a ≤ W' then d₀.nmem a else 0) = _
    rw [ite_eq_left_of_eq_true _ _ (eq_true ha)]; exact hS₀.nmem a ha
  have hσ₀ : ∀ d : fd₀.DQ, (σ₀ d : ℕ) < p₀.nD := fun d => by rw [hpD₀]; exact (σ₀ d).2
  have hσ₁ : ∀ d : fd₁.DQ, (σ₁ d : ℕ) < p₁.nD := fun d => by rw [hpD₁]; exact (σ₁ d).2
  have a₀ : ∀ x, x < p₀.β → x ≤ W' := fun x hx => by clear * - hx hEW₀; omega
  have a₁ : ∀ x, x < p₁.β → x ≤ W' := fun x hx => by clear * - hx o₁4 hIn₆; omega
  -- 2. the two encoders on the truncation, each exporting its bound `Hc`
  have g0RV : ∀ d, y₀.nmem (p₀.I0 + σ₀ d) = σ₀ (fd₀.Q.rev d) :=
    fun d => by
      rw [hy₀m _ (a₀ _ (by have := hσ₀ d; clear * - this hβ₀; omega))]; exact hQRV₀ d
  have g0NT : ∀ d, y₀.nmem (p₀.I0 + p₀.nD + σ₀ d) = νv₀ (fd₀.Q.tail d) :=
    fun d => by
      rw [hy₀m _ (a₀ _ (by have := hσ₀ d; clear * - this hβ₀; omega))]; exact hQNT₀ d
  have g0NF : ∀ d, y₀.nmem (p₀.I0 + 2 * p₀.nD + σ₀ d) = τ₀ (fd₀.Q.face d) :=
    fun d => by
      rw [hy₀m _ (a₀ _ (by have := hσ₀ d; clear * - this hβ₀; omega))]; exact hQNF₀ d
  have g0IS : ∀ d, y₀.nmem (p₀.I0 + 3 * p₀.nD + σ₀ d) = if d ∈ fd₀.P'.image fd₀.e then 1 else 0 :=
    fun d => by
      rw [hy₀m _ (a₀ _ (by have := hσ₀ d; clear * - this hβ₀; omega))]; exact hQIS₀ d
  have g0LN : ∀ d, y₀.nmem (p₀.I0 + 4 * p₀.nD + σ₀ d) =
      (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀) d).toNat :=
    fun d => by
      rw [hy₀m _ (a₀ _ (by have := hσ₀ d; clear * - this hβ₀; omega))]; exact hQLN₀ d
  have g0G : ∀ i < fd₀.k, y₀.nmem (p₀.I0 + 5 * p₀.nD + i) = σ₀ (fd₀.g i) :=
    fun i hi => by
      rw [hy₀m _ (a₀ _ (by rw [← hpk₀] at hi; clear * - hi hβ₀; omega))]; exact hQG₀ i hi
  have g1RV : ∀ d, y₀.nmem (p₁.I0 + σ₁ d) = σ₁ (fd₁.Q.rev d) :=
    fun d => by
      rw [hy₀m _ (a₁ _ (by have := hσ₁ d; clear * - this hβ₁; omega))]; exact hQRV₁ d
  have g1NT : ∀ d, y₀.nmem (p₁.I0 + p₁.nD + σ₁ d) = νv₁ (fd₁.Q.tail d) :=
    fun d => by
      rw [hy₀m _ (a₁ _ (by have := hσ₁ d; clear * - this hβ₁; omega))]; exact hQNT₁ d
  have g1NF : ∀ d, y₀.nmem (p₁.I0 + 2 * p₁.nD + σ₁ d) = τ₁ (fd₁.Q.face d) :=
    fun d => by
      rw [hy₀m _ (a₁ _ (by have := hσ₁ d; clear * - this hβ₁; omega))]; exact hQNF₁ d
  have g1IS : ∀ d, y₀.nmem (p₁.I0 + 3 * p₁.nD + σ₁ d) = if d ∈ fd₁.P'.image fd₁.e then 1 else 0 :=
    fun d => by
      rw [hy₀m _ (a₁ _ (by have := hσ₁ d; clear * - this hβ₁; omega))]; exact hQIS₁ d
  have g1LN : ∀ d, y₀.nmem (p₁.I0 + 4 * p₁.nD + σ₁ d) =
      (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁) d).toNat :=
    fun d => by
      rw [hy₀m _ (a₁ _ (by have := hσ₁ d; clear * - this hβ₁; omega))]; exact hQLN₁ d
  have g1G : ∀ i < fd₁.k, y₀.nmem (p₁.I0 + 5 * p₁.nD + i) = σ₁ (fd₁.g i) :=
    fun i hi => by
      rw [hy₀m _ (a₁ _ (by rw [← hpk₁] at hi; clear * - hi hβ₁; omega))]; exact hQG₁ i hi
  obtain ⟨ya, ta, ea, hta, w₀, Hc₀, hv₀a, hHI₀, hHle₀, hK₀a, hma, -, -, hoa, h25a, h48a⟩ :=
    fhFin_exec (P := I) (W := W') fd₀ (redLen N ℓ δ₀) σ₀ νv₀ τ₀ p₀ hpD₀ hpk₀ hpV₀ hpF₀
      (by clear * - o₀4 o₁1 o₁4 hIn₅ hIn₆; omega) hLm₀ hLW₀ hIW₀ hH₀ y₀ hy₀w g0RV g0NT g0NF g0IS
      g0LN g0G
  have hk0 : ∀ a, p₁.I0 ≤ a → ya.nmem a = y₀.nmem a := fun a ha =>
    hma a (Or.inr (by clear * - ha hIn₅; omega))
  obtain ⟨y₁, tb, eb, htb, w₁, Hc₁, hv₁, hHI₁, hHle₁, hKS₁, hmb, -, -, hob, h25b, h48b⟩ :=
    fhFin_exec (P := I) (W := W') fd₁ (redLen N ℓ δ₁) σ₁ νv₁ τ₁ p₁ hpD₁ hpk₁ hpV₁ hpF₁ hIn₆ hLm₁ hLW₁
      hIW₁ hH₁ ya ea.wb_right
      (fun d => by rw [hk0 _ (Nat.le_add_right _ _)]; exact g1RV d)
      (fun d => by rw [hk0 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))]; exact g1NT d)
      (fun d => by rw [hk0 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))]; exact g1NF d)
      (fun d => by rw [hk0 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))]; exact g1IS d)
      (fun d => by rw [hk0 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))]; exact g1LN d)
      (fun i hi => by rw [hk0 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))]; exact g1G i hi)
  have hk1 : ∀ a, a < p₁.β → y₁.nmem a = ya.nmem a := fun a ha => hmb a (Or.inl ha)
  have hKwlt : p₀.β + p₀.Kw < p₁.β := by clear * - o₀4 o₁1 hIn₅; omega
  have hPk₀ : fePk p₀ y₁.nmem = fePk p₀ ya.nmem :=
    nb_fePk_congr p₀ fun i hi => hk1 _ (by clear * - hi hKwlt; omega)
  have hv₀ : FEncNatNL fd₀ (redLen N ℓ δ₀) p₀.NN p₀.Bw (srcNum σ₀) w₀ (fePk p₀ y₁.nmem) := by
    rw [hPk₀]; exact hv₀a
  have hm₁ : ∀ a, (a < p₀.β ∨ p₀.END ≤ a) → (a < p₁.β ∨ p₁.END ≤ a) → y₁.nmem a = y₀.nmem a :=
    fun a h0 h1 => by rw [hmb a h1, hma a h0]
  -- 3. renamed, lifted to `d₀`, the fixed encoders, the bounds saved in the parameters
  obtain ⟨hU1, hU2, hU3⟩ := hf_enc_ok p₀
  obtain ⟨hV1, hV2, hV3⟩ := hf_enc_ok p₁
  have eRa := rn_exec nbSwap ea
  rw [hy₀, nb_rnC_back] at eRa
  obtain ⟨da, eLa, hAga, hKpa, hoLa⟩ := Exec.lift_trunc (P' := I) eRa hU1 hU2 hU3 hWW hd₀
  obtain ⟨fa, -⟩ := feFix_exec (Or.inl rfl) eLa hP₀
  have hda25 : da.nreg 3325 = Hc₀ := by
    rw [hAga.nreg 3325 (by decide), rnC_nreg', hf_swap2125, h25a]
  obtain ⟨db, esa, hsa1, hsa2, hsa3, hsam, hsar, hsarm, hsao⟩ :=
    hfSave_exec (I := I) (dst := 10411) (src := 3325) da eLa.wb_right
      (by rw [hda25]; clear * - hHle₀ hH₀ hWW; omega) (by norm_num) (by norm_num) (by norm_num)
  have hAgb : Agree nbU W' (rnC nbSwap ya) db :=
    ⟨fun r hr => by
        simp only [nbU, decide_eq_true_eq] at hr
        rw [hsa3 r (by omega) (by omega) (by omega)]
        exact hAga.nreg r (by simp only [nbU, decide_eq_true_eq]; exact hr),
      fun r hr => by rw [hsar]; exact hAga.rreg r hr,
      fun a ha => by rw [hsam]; exact hAga.nmem a ha,
      fun a ha => by rw [hsarm]; exact hAga.rmem a ha⟩
  have eRb := rn_exec nbSwap eb
  obtain ⟨dc, eLb, hAgc, hKpc, L, hL1, hL2⟩ :=
    Exec.lift (P' := I) eRb hV1 hV2 hV3 hWW hAgb esa.wb_right
  have hL : L = [] := by
    simp only [rnC_output, hob] at hL1
    simpa using hL1
  have hP₁b : ∀ j < 110, db.nreg (10200 + j) = feV p₁ j := fun j hj => by
    rw [hsa3 _ (by omega) (by omega) (by omega),
      hKpa.nreg _ (by simp only [nbU]; exact decide_eq_false (by omega))]
    exact hP₁ j hj
  obtain ⟨fb, -⟩ := feFix_exec (Or.inr rfl) eLb hP₁b
  have hdc25 : dc.nreg 3325 = Hc₁ := by
    rw [hAgc.nreg 3325 (by decide), rnC_nreg', hf_swap2125, h25b]
  obtain ⟨dd, esb, hsb1, hsb2, hsb3, hsbm, hsbr, hsbrm, hsbo⟩ :=
    hfSave_exec (I := I) (dst := 10466) (src := 3325) dc eLb.wb_right
      (by rw [hdc25]; clear * - hHle₁ hH₁ hWW; omega) (by norm_num) (by norm_num) (by norm_num)
  have hlowR : ∀ r, (r < 2600 ∨ 3748 ≤ r) → r ≠ 10411 → r ≠ 10412 → r ≠ 10466 → r ≠ 10467 →
      r ≠ 10520 → dd.nreg r = d₀.nreg r := fun r h1 h2 h3 h4 h5 h6 => by
    have hn : nbU r = false := by simp only [nbU]; exact decide_eq_false (by omega)
    rw [hsb3 r h4 h5 h6, hKpc.nreg r hn, hsa3 r h2 h3 h6, hKpa.nreg r hn]
  -- 4. the configuration the node starts from
  obtain ⟨c₁, hc₁r, hc₁m, hc₁rr, hc₁rm, hc₁o⟩ : ∃ c₁ : Config, c₁.nreg = c.nreg ∧
      c₁.nmem = y₁.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output :=
    ⟨{ c with nmem := y₁.nmem }, rfl, rfl, rfl, rfl, rfl⟩
  have hc₁ : WordsBounded W' c₁ :=
    ⟨fun r => by rw [hc₁r]; exact hc.1 r, fun a => by rw [hc₁m]; exact eb.wb_right.2 a⟩
  have hlow : ∀ a, a < p₀.I0 → c₁.nmem a = c.nmem a := fun a ha => by
    rw [hc₁m, hm₁ a (Or.inl (by clear * - ha o₀1; omega))
      (Or.inl (by clear * - ha o₀1 o₀4 o₁1 hIn₅; omega))]
    exact hy₀m a (by clear * - ha o₀1 hEW₀; omega)
  have hSim : Sim 1000 W' M (W' + 1) c₁ dd := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_⟩
    · rw [hlowR r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hc₁r]
      exact hS₀.nreg r hr
    · rw [hlowR (1000 + r) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        hc₁rr]
      exact hS₀.rreg r hr
    · rw [hsbm, hAgc.nmem a ha, hc₁m]; rfl
    · rw [hsbm, hKpc.nmem _ (by omega), hsam, hKpa.nmem _ (by omega), hc₁rm]
      exact hS₀.rmem a ha
    · rw [hsbo, hL2, hL, List.append_nil, hsao, hoLa, hc₁o]
      show ya.output = c.output
      rw [hoa]; exact hS₀.output
  have hYI : Y ≤ p₀.I0 := by clear * - hIn₁ hIn₃; omega
  have hm₀ : 0 < M₀ := by clear * - hM₀; omega
  have hslot : ∀ j < 6, ∀ d < M₀, c₁.nmem (Z + j * M₀ + d) = c.nmem (Z + j * M₀ + d) :=
    fun j hj d hd => hlow _ (by
      have h1 : j * M₀ ≤ 5 * M₀ := Nat.mul_le_mul_right _ (by clear * - hj; omega)
      clear * - h1 hd hY hYI; omega)
  have hmM : m < M₀ := by clear * - hM₀; omega
  -- 5. the node
  have hwn₀ := nb_wn (K := p₀.Kw) hHle₀ hWN₂ hWN₄
  have hwn₁ := nb_wn (K := p₁.Kw) hHle₁ hWN₃ hWN₅
  obtain ⟨d', t', o, ex, ht', hpot, hstep, hout⟩ :=
    node_exec_natNNL_sim C hfr hmssp hS hB ℓ δ₀ δ₁ hδ₀ hδ₁ fd₀ hq₀ hk₀ fd₁ hq₁ hk₁
      (n₀ := p₀.NN) (Bw₀ := p₀.Bw) (σ₀ := srcNum σ₀) (wt₀ := w₀) (Pk₀ := fePk p₀ y₁.nmem) hv₀
      (Hc₀ := Hc₀) hHI₀
      (n₁ := p₁.NN) (Bw₁ := p₁.Bw) (σ₁ := srcNum σ₁) (wt₁ := w₁) (Pk₁ := fePk p₁ y₁.nmem) hv₁
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
      ⟨hWN₁, hwn₀.1, hwn₁.1, hwn₀.2, hwn₁.2, hWN₆, hWN₇, hWN₈, hWN₉⟩ hM hc₁
      (hctx.of fun r _ _ => by rw [hc₁r]) (hx.of fun r _ _ => by rw [hc₁r])
      (fun d hd => by rw [hslot 0 (by norm_num) d (by clear * - hd hmM; omega)]; exact hTm d hd)
      (fun d hd => by rw [hslot 1 (by norm_num) d (by clear * - hd hmM; omega)]; exact hHm d hd)
      (fun d hd => by rw [hslot 2 (by norm_num) d (by clear * - hd hmM; omega)]; exact hSm d hd)
      (fun d hd => by rw [hc₁rm]; exact hLm d hd) (fun v hv => by rw [hc₁rm]; exact hD₀ v hv)
      (fun v hv => by rw [hc₁rm]; exact hD₁ v hv)
      (fun a ha => by rw [hlow a (by clear * - ha hY hYI; omega)]; exact hz a ha)
      (fun x hx => by
        have := hN.lt _ (bdry_sub_verts hx)
        rw [hlow _ (by clear * - this hIn₃; omega)]; exact hpos₀ x hx)
      (fun x hx => by
        have := hN.lt _ (bdry_sub_verts hx)
        rw [hlow _ (by clear * - this hIn₄; omega)]; exact hpos₁ x hx)
      ⟨fun i hi => by
          rw [hc₁m, hPk₀, hk1 _ (by have := p₀.kw_eq.2; clear * - hi hKwlt this; omega)]
          exact hK₀a.dat i hi,
        fun a ha => by
          have ha' := ha; rw [cD₀] at ha'
          rw [hc₁m, hk1 _ (by clear * - ha' o₀3 o₁1 hIn₅; omega)]
          exact hK₀a.res a ha⟩
      ⟨fun i hi => by rw [hc₁m]; exact hKS₁.dat i hi, fun a ha => by rw [hc₁m]; exact hKS₁.res a ha⟩
      (nb_ninv hI hc₁rr hc₁rm) (nb_intAll hZi hc₁rr hc₁rm) dd hSim esb.wb_right
  -- 6. the fixed node
  have hvN : ∀ j < 115, dd.nreg (10400 + j) =
      hnV (kpnOf fd₀ (redLen N ℓ δ₀) p₀.NN p₀.Bw (fePk p₀ y₁.nmem) p₀.β p₀.RK Pb₀ Hc₀
          (2 * W' + 2) (W' + 1) M)
        (kpnOf fd₁ (redLen N ℓ δ₁) p₁.NN p₁.Bw (fePk p₁ y₁.nmem) p₁.β p₁.RK Pb₁ Hc₁
          (2 * W' + 2) (W' + 1) M) M (nodeHN m b w B) (W' + 1) j := by
    intro j hj
    by_cases j11 : j = 11
    · subst j11
      rw [hnV_11]
      show dd.nreg 10411 = 2 * Hc₀ + 1
      rw [hsb3 _ (by norm_num) (by norm_num) (by norm_num),
        hKpc.nreg _ (by decide), hsa2, hda25]
    by_cases j12 : j = 12
    · subst j12
      rw [hnV_12]
      show dd.nreg 10412 = Hc₀
      rw [hsb3 _ (by norm_num) (by norm_num) (by norm_num),
        hKpc.nreg _ (by decide), hsa1, hda25]
    by_cases j66 : j = 66
    · subst j66
      rw [hnV_66]
      show dd.nreg 10466 = 2 * Hc₁ + 1
      rw [hsb2, hdc25]
    by_cases j67 : j = 67
    · subst j67
      rw [hnV_67]
      show dd.nreg 10467 = Hc₁
      rw [hsb1, hdc25]
    rw [hlowR (10400 + j) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      hPN j hj j11 j12 j66 j67,
      kpnOf_len fd₀ (redLen N ℓ δ₀) p₀.NN p₀.Bw (Pk := fePk p₀ y₁.nmem)
        (Pk' := fePk p₀ fun _ => 0) (by rw [fePk_len, fePk_len]) p₀.β p₀.RK Pb₀ Hc₀
        (2 * W' + 2) (W' + 1) M,
      kpnOf_len fd₁ (redLen N ℓ δ₁) p₁.NN p₁.Bw (Pk := fePk p₁ y₁.nmem)
        (Pk' := fePk p₁ fun _ => 0) (by rw [fePk_len, fePk_len]) p₁.β p₁.RK Pb₁ Hc₁
        (2 * W' + 2) (W' + 1) M]
    exact (hnV_upd _ _ Hc₀ Hc₁ _ _ _ j hj j11 j12 j66 j67).symm
  obtain ⟨tN, fN, htN, -⟩ := nodeFix_exec (by show 1 ≤ Hc₀; omega) (by show 1 ≤ Hc₁; omega)
    hM2 ex hvN
  refine ⟨Hc₀, Hc₁, h48a, hHle₀, h48b, hHle₁, d', ta + tb + 8, tN, o,
    (Exec.seq fa (Exec.seq esa (Exec.seq fb (Exec.seq esb fN)))).cast (by omega),
    by clear * - hta htb; omega, ?_, hpot, hstep, hout.trans hc₁o⟩
  rw [cD₀, cD₁] at ht'
  exact htN.trans (Nat.add_le_add_right ht' 2)

end NegSSSP

end PlanarFlow
