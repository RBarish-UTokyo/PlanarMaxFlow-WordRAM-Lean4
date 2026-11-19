module

public import PlanarFlow.NegSSSP.Enc.NodeDkA
public import PlanarFlow.NegSSSP.Enc.NodeSim
public import PlanarFlow.NegSSSP.Enc.RenReg

/-!
# The node of the recursion from the plain encodings, as one natural run

`node_exec_natNNL_Dk` runs the encoders on the node's (real) configuration `c` and the node from
`natOf … c₁`. Here everything is **one run of one natural-word program** from any natural
configuration `d₀` simulating `c` (`Sim 1000 W' M (W' + 1) c d₀`, e.g. `natOf … c`):

`rnS nbSwap (feProgDk p₀) ; rnS nbSwap (feProgDk p₁) ; nodeProgNN …`

* `nbSwap`: the involution of `ℕ` exchanging the registers `[1400, 2548)` (those of the
  encoders, `nbDk_regsOK`) with `[2600, 3748)`, so that the renamed encoders (`rnS`, `rn_exec`)
  leave the residues of the real registers (`1000 … 1999`) and the node's registers (`< 1000`)
  alone;
* the encoders run on the truncation of `d₀` to their registers and the memory `≤ W'`
  (so all their words are `≤ W'`), lifted to `d₀` (`Exec.lift_trunc`);
* the node runs from the configuration they leave, which simulates `c` with the memory of the
  encoders (`node_exec_natNNL_sim`).

**`node_exec_natNNL_Dk1`**: same hypotheses as `node_exec_natNNL_Dk`, plus `d₀`, `Sim`, words of
`d₀` `≤ WN`, and the registers `2600 … 3747` of `d₀` `≤ W'` (zero in `natOf … c`); within
`t₁ + t'` steps, `t₁ ≤ feCostDk p₀ + feCostDk p₁` (`O(m log m)` at a node), `t'` the bound of
`node_exec_natNNL`.
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

/-- The registers of the encoders `[1400, 2548)` exchanged with `[2600, 3748)`. -/
def nbSwapF (r : ℕ) : ℕ :=
  if 1400 ≤ r ∧ r < 2548 then r + 1200 else if 2600 ≤ r ∧ r < 3748 then r - 1200 else r

theorem nbSwapF_inv : Function.Involutive nbSwapF := by
  intro r; unfold nbSwapF; split_ifs <;> omega

/-- The involution `nbSwapF` as a permutation. -/
def nbSwap : Equiv.Perm ℕ := Function.Involutive.toPerm _ nbSwapF_inv

/-- The registers of the renamed encoders. -/
def nbU (r : ℕ) : Bool := decide (2600 ≤ r ∧ r < 3748)

/-- **The encoders name only the registers `[1400, 2548)`** (checked by the kernel). -/
theorem nbDk_regsOK (p : FeP) :
    (feProgDk p).regsOK (fun r => decide (1400 ≤ r ∧ r < 2548)) = true := by kernel_rfl

/-- **The renamed encoders name only `[2600, 3748)`, read no input, use no randomness.** -/
theorem nbDk2_ok (p₀ p₁ : FeP) :
    (rnS nbSwap (.seq (feProgDk p₀) (feProgDk p₁))).regsOK nbU = true ∧
      (rnS nbSwap (.seq (feProgDk p₀) (feProgDk p₁))).noInp = true ∧
      (rnS nbSwap (.seq (feProgDk p₀) (feProgDk p₁))).noRand = true := by
  refine ⟨?_, ?_, ?_⟩ <;> kernel_rfl

theorem nb_rnC_back (π : Equiv.Perm ℕ) (c : Config) : rnC π (rnC π.symm c) = c := by
  have := rnC_symm π.symm c
  rwa [Equiv.symm_symm] at this

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
open Classical in
/-- **The node of the recursion from the plain encodings of its one-face instances, as one
natural run** (see the module docstring). -/
theorem node_exec_natNNL_Dk1 (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
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
    (hR0 : ∀ r, 2600 ≤ r → r < 3748 → d₀.nreg r ≤ W') :
    ∃ (Hc₀ Hc₁ : ℕ) (Pk₀ Pk₁ : Input), Hc₀ ≤ kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k ∧
      Hc₁ ≤ kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k ∧
      ∃ d' t₁ t', ∃ o : Option (V → ℤ),
        Exec I WN (.seq (.seq (rnS nbSwap (feProgDk p₀)) (rnS nbSwap (feProgDk p₁)))
          (nodeProgNN
            (kpnOf fd₀ (redLen N ℓ δ₀) p₀.NN p₀.Bw Pk₀ p₀.β p₀.RK Pb₀ Hc₀ (2 * W' + 2) (W' + 1) M)
            (kpnOf fd₁ (redLen N ℓ δ₁) p₁.NN p₁.Bw Pk₁ p₁.β p₁.RK Pb₁ Hc₁ (2 * W' + 2) (W' + 1) M) M
            (nodeHN m b w B) (W' + 1))) d₀ d' (t₁ + t') ∧
        t₁ ≤ feCostDk p₀ + feCostDk p₁ ∧
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
  -- 2. the two encoders
  obtain ⟨y₁, t₁, e₁, ht₁, ⟨w₀, Hc₀, hv₀, hHI₀, hHle₀, hKS₀⟩, ⟨w₁, Hc₁, hv₁, hHI₁, hHle₁, hKS₁⟩,
      hm₁, -, hrr₁, hrm₁, ho₁⟩ :=
    nbFe2Dk_exec (P := I) (W := W') fd₀ fd₁ (redLen N ℓ δ₀) (redLen N ℓ δ₁) σ₀ νv₀ τ₀ σ₁ νv₁ τ₁
      p₀ p₁ hpD₀ hpk₀ hpV₀ hpF₀ hpD₁ hpk₁ hpV₁ hpF₁ hIn₅ hIn₆ hLm₀ hLW₀ hIW₀ hH₀ hLm₁ hLW₁ hIW₁
      hH₁ y₀ hy₀w
      (fun d => by
        rw [hy₀m _ (a₀ _ (by have := hσ₀ d; clear * - this hβ₀; omega))]; exact hQRV₀ d)
      (fun d => by
        rw [hy₀m _ (a₀ _ (by have := hσ₀ d; clear * - this hβ₀; omega))]; exact hQNT₀ d)
      (fun d => by
        rw [hy₀m _ (a₀ _ (by have := hσ₀ d; clear * - this hβ₀; omega))]; exact hQNF₀ d)
      (fun d => by
        rw [hy₀m _ (a₀ _ (by have := hσ₀ d; clear * - this hβ₀; omega))]; exact hQIS₀ d)
      (fun d => by
        rw [hy₀m _ (a₀ _ (by have := hσ₀ d; clear * - this hβ₀; omega))]; exact hQLN₀ d)
      (fun i hi => by
        rw [hy₀m _ (a₀ _ (by rw [← hpk₀] at hi; clear * - hi hβ₀; omega))]; exact hQG₀ i hi)
      (fun d => by
        rw [hy₀m _ (a₁ _ (by have := hσ₁ d; clear * - this hβ₁; omega))]; exact hQRV₁ d)
      (fun d => by
        rw [hy₀m _ (a₁ _ (by have := hσ₁ d; clear * - this hβ₁; omega))]; exact hQNT₁ d)
      (fun d => by
        rw [hy₀m _ (a₁ _ (by have := hσ₁ d; clear * - this hβ₁; omega))]; exact hQNF₁ d)
      (fun d => by
        rw [hy₀m _ (a₁ _ (by have := hσ₁ d; clear * - this hβ₁; omega))]; exact hQIS₁ d)
      (fun d => by
        rw [hy₀m _ (a₁ _ (by have := hσ₁ d; clear * - this hβ₁; omega))]; exact hQLN₁ d)
      (fun i hi => by
        rw [hy₀m _ (a₁ _ (by rw [← hpk₁] at hi; clear * - hi hβ₁; omega))]; exact hQG₁ i hi)
  -- 3. renamed and lifted to `d₀`
  have eR := rn_exec nbSwap e₁
  rw [hy₀, nb_rnC_back] at eR
  obtain ⟨hU1, hU2, hU3⟩ := nbDk2_ok p₀ p₁
  obtain ⟨d₁, eL, hAg, hKp, hoL⟩ := Exec.lift_trunc (P' := I) eR hU1 hU2 hU3 hWW hd₀
  -- 4. the configuration the node starts from
  obtain ⟨c₁, hc₁r, hc₁m, hc₁rr, hc₁rm, hc₁o⟩ : ∃ c₁ : Config, c₁.nreg = c.nreg ∧
      c₁.nmem = y₁.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output :=
    ⟨{ c with nmem := y₁.nmem }, rfl, rfl, rfl, rfl, rfl⟩
  have hc₁ : WordsBounded W' c₁ :=
    ⟨fun r => by rw [hc₁r]; exact hc.1 r, fun a => by rw [hc₁m]; exact e₁.wb_right.2 a⟩
  have hlow : ∀ a, a < p₀.I0 → c₁.nmem a = c.nmem a := fun a ha => by
    rw [hc₁m, hm₁ a (Or.inl (by clear * - ha o₀1; omega))
      (Or.inl (by clear * - ha o₀1 o₀4 o₁1 hIn₅; omega))]
    exact hy₀m a (by clear * - ha o₀1 hEW₀; omega)
  have hSim : Sim 1000 W' M (W' + 1) c₁ d₁ := by
    refine ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_⟩
    · rw [hKp.nreg r (by simp only [nbU]; exact decide_eq_false (by omega)), hc₁r]
      exact hS₀.nreg r hr
    · rw [hKp.nreg _ (by simp only [nbU]; exact decide_eq_false (by omega)), hc₁rr]
      exact hS₀.rreg r hr
    · rw [hAg.nmem a ha, hc₁m]; rfl
    · rw [hKp.nmem _ (by omega), hc₁rm]; exact hS₀.rmem a ha
    · rw [hoL, hc₁o]; show y₁.output = c.output
      rw [ho₁]; exact hS₀.output
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
      ⟨fun i hi => by rw [hc₁m]; exact hKS₀.dat i hi, fun a ha => by rw [hc₁m]; exact hKS₀.res a ha⟩
      ⟨fun i hi => by rw [hc₁m]; exact hKS₁.dat i hi, fun a ha => by rw [hc₁m]; exact hKS₁.res a ha⟩
      (nb_ninv hI hc₁rr hc₁rm) (nb_intAll hZi hc₁rr hc₁rm) d₁ hSim eL.wb_right
  refine ⟨Hc₀, Hc₁, fePk p₀ y₁.nmem, fePk p₁ y₁.nmem, hHle₀, hHle₁, d', t₁, t', o,
    Exec.seq eL ex, ht₁, ?_, hpot, hstep, hout.trans hc₁o⟩
  rw [cD₀, cD₁] at ht'
  exact ht'

end NegSSSP

end PlanarFlow
