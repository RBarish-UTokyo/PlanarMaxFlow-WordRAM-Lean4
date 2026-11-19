module

public import PlanarFlow.NegSSSP.Enc.FeFinalDk
public import PlanarFlow.NegSSSP.Enc.NodeBF

/-!
# The two encoders of a node, one after the other (distances by Dijkstra)

As `NodeBFA.lean`, for the encoder `feProgDk` (phase D by Dijkstra in memory):

* **`nbFeProgDk_keeps`**: `feProgDk p` writes only natural registers `≥ 1400` (kernel-checked).
* **`nbFe2Dk_exec`**: `feProgDk p₀ ; feProgDk p₁` within `feCostDk p₀ + feCostDk p₁` steps, both
  encodings at the end, memory changed only in `[p₀.β, p₀.END) ∪ [p₁.β, p₁.END)`.
* `nbFeCostDk_le`; **`nbFeCostDk_node_le`**: at a one-face instance of a node (`fd.q ≤ 18 m`,
  `fd.k² ≤ 1200 m`), **`feCostDk p ≤ (3114 m + 13) (⌊log₂ m⌋ + 8) + 444800 m + 1384`**:
  `O(m log m)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge.CmpAbs

/-- **The composed encoder writes only natural registers `≥ 1400`** (for every `p`). -/
theorem nbFeProgDk_keeps (p : FeP) : nbKeepsBelow 1400 (feProgDk p) = true := by kernel_rfl

/-- The cost bound of the encoder with its linear terms collected. -/
theorem nbFeCostDk_le (p : FeP) :
    feCostDk p ≤ (23 * p.A + 13 * p.N + 13) * Heap.lg (2 * p.A) +
      1100 * (p.N + p.A + p.FN + p.nD + p.k) + 8 * p.Kw + 1200 := by
  unfold feCostDk feMidCost feEndCostDk dkpCost feBCost osCost cotCost toCost
  have e : (23 * p.A + 13 * p.N + 13) * Heap.lg (2 * p.A) =
      p.A * (23 * Heap.lg (2 * p.A)) + 13 * Heap.lg (2 * p.A) * p.N + 13 * Heap.lg (2 * p.A) := by
    ring
  have e2 : p.A * (23 * Heap.lg (2 * p.A) + 21) = p.A * (23 * Heap.lg (2 * p.A)) + 21 * p.A := by
    ring
  have e3 : (13 * Heap.lg (2 * p.A) + 20) * p.N = 13 * Heap.lg (2 * p.A) * p.N + 20 * p.N := by
    ring
  rw [e, e2, e3]
  generalize p.A * (23 * Heap.lg (2 * p.A)) = X
  generalize 13 * Heap.lg (2 * p.A) * p.N = Y
  omega

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- `lg (2 A) ≤ ⌊log₂ m⌋ + 8` for `1 ≤ A ≤ 54 m`. -/
theorem nb_lg_le {A m : ℕ} (hA : 1 ≤ A) (hm : A ≤ 54 * m) :
    Heap.lg (2 * A) ≤ Nat.log 2 m + 8 := by
  have hm1 : 1 ≤ m := by omega
  have h1 : Heap.lg (2 * A) ≤ Heap.lg (128 * m) := Heap.lg_mono (by omega)
  have h2 : Heap.lg (128 * m) = Heap.lg m + 7 := by
    have : 128 * m = 2 * (2 * (2 * (2 * (2 * (2 * (2 * m)))))) := by ring
    rw [this, Heap.lg_two_mul (by omega), Heap.lg_two_mul (by omega), Heap.lg_two_mul (by omega),
      Heap.lg_two_mul (by omega), Heap.lg_two_mul (by omega), Heap.lg_two_mul (by omega),
      Heap.lg_two_mul (by omega)]
  have h3 := Heap.lg_eq_log hm1
  omega

/-- **The cost of the encoder at a one-face instance of a node** (`fd.q ≤ 18 m`,
`fd.k² ≤ 1200 m`): **`O(m log m)`** (Dijkstra). -/
theorem nbFeCostDk_node_le {X : Finset D} {B : Finset V} (fd : FaceData N X B) (m : ℕ)
    (hq : fd.q ≤ 18 * m) (hk2 : fd.k ^ 2 ≤ 1200 * m) (p : FeP)
    (hD : p.nD = Fintype.card fd.DQ) (hk : p.k = fd.k) (hV : p.nV = Fintype.card fd.VQ)
    (hF : p.nF = Fintype.card fd.FQ) :
    feCostDk p ≤ (3114 * m + 13) * (Nat.log 2 m + 8) + 444800 * m + 1384 := by
  have hc := fd.inst.card
  have hkV : fd.k ≤ Fintype.card fd.VQ := by
    have hinj : Function.Injective fun i : Fin fd.k => fd.Q.tail (fd.g i) := fun i j h =>
      Fin.ext (fd.inst.cycle.inj _ i.2 _ j.2 h)
    simpa using Fintype.card_le_of_injective _ hinj
  have h2k := fd.inst.cycle.two_le
  have hE := p.eqs
  obtain ⟨hBw, hKw⟩ := p.kw_eq
  have hkk : p.k * p.k ≤ 1200 * m := by rw [hk, ← pow_two]; exact hk2
  have hlin : p.N + p.A + p.FN + p.nD + p.k ≤ 288 * m ∧ p.A ≤ 54 * m ∧ p.N ≤ 144 * m ∧
      p.AE ≤ 234 * m ∧ 1 ≤ p.A := by
    obtain ⟨e1, e2, e3, e4, -⟩ := hE
    rw [← hk] at hkV h2k
    clear * - e1 e2 e3 e4 hc hq hkV hD hV hF h2k
    omega
  have hKw' : p.Kw ≤ 16000 * m + 23 := by
    obtain ⟨e1, e2, e3, e4, e5, -⟩ := hE
    rw [hKw, hBw]
    clear * - e1 e2 e3 e4 e5 hlin hkk
    omega
  have hL := nb_lg_le hlin.2.2.2.2 hlin.2.1
  have hprod : (23 * p.A + 13 * p.N + 13) * Heap.lg (2 * p.A) ≤
      (3114 * m + 13) * (Nat.log 2 m + 8) :=
    Nat.mul_le_mul (by have := hlin.2.1; have := hlin.2.2.1; omega) hL
  have := nbFeCostDk_le p
  generalize (23 * p.A + 13 * p.N + 13) * Heap.lg (2 * p.A) = X at hprod this
  generalize (3114 * m + 13) * (Nat.log 2 m + 8) = Y at hprod ⊢
  clear * - this hprod hKw' hlin
  omega

section Two

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The two encoders of a node, one after the other, distances by Dijkstra.** -/
theorem nbFe2Dk_exec {X₀ X₁ : Finset D} {B₀ B₁ : Finset V} (fd₀ : FaceData N X₀ B₀)
    (fd₁ : FaceData N X₁ B₁) (ℓ₀ ℓ₁ : D → ℤ)
    (σ₀ : fd₀.DQ ≃ Fin (Fintype.card fd₀.DQ)) (νv₀ : fd₀.VQ ≃ Fin (Fintype.card fd₀.VQ))
    (τ₀ : fd₀.FQ ≃ Fin (Fintype.card fd₀.FQ))
    (σ₁ : fd₁.DQ ≃ Fin (Fintype.card fd₁.DQ)) (νv₁ : fd₁.VQ ≃ Fin (Fintype.card fd₁.VQ))
    (τ₁ : fd₁.FQ ≃ Fin (Fintype.card fd₁.FQ)) (p₀ p₁ : FeP)
    (hD₀ : p₀.nD = Fintype.card fd₀.DQ) (hk₀ : p₀.k = fd₀.k) (hV₀ : p₀.nV = Fintype.card fd₀.VQ)
    (hF₀ : p₀.nF = Fintype.card fd₀.FQ)
    (hD₁ : p₁.nD = Fintype.card fd₁.DQ) (hk₁ : p₁.k = fd₁.k) (hV₁ : p₁.nV = Fintype.card fd₁.VQ)
    (hF₁ : p₁.nF = Fintype.card fd₁.FQ)
    (hE₀₁ : p₀.END ≤ p₁.I0) (hW : p₁.END ≤ W)
    (hLm₀ : feIsoB p₀.A p₀.N p₀.FN (srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e ℓ₀)).toNat ≤
      p₀.Lmax)
    (hLW₀ : p₀.Lmax ≤ W) (hIW₀ : p₀.Inf + p₀.Lmax ≤ W)
    (hH₀ : 2 * kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k + 1 ≤ W)
    (hLm₁ : feIsoB p₁.A p₁.N p₁.FN (srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e ℓ₁)).toNat ≤
      p₁.Lmax)
    (hLW₁ : p₁.Lmax ≤ W) (hIW₁ : p₁.Inf + p₁.Lmax ≤ W)
    (hH₁ : 2 * kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k + 1 ≤ W)
    (c : Config) (hc : WordsBounded W c)
    (hQRV₀ : ∀ d, c.nmem (p₀.I0 + σ₀ d) = σ₀ (fd₀.Q.rev d))
    (hQNT₀ : ∀ d, c.nmem (p₀.I0 + p₀.nD + σ₀ d) = νv₀ (fd₀.Q.tail d))
    (hQNF₀ : ∀ d, c.nmem (p₀.I0 + 2 * p₀.nD + σ₀ d) = τ₀ (fd₀.Q.face d))
    (hQIS₀ : ∀ d, c.nmem (p₀.I0 + 3 * p₀.nD + σ₀ d) = if d ∈ fd₀.P'.image fd₀.e then 1 else 0)
    (hQLN₀ : ∀ d, c.nmem (p₀.I0 + 4 * p₀.nD + σ₀ d) = (faceLen fd₀.P' fd₀.e ℓ₀ d).toNat)
    (hQG₀ : ∀ i < fd₀.k, c.nmem (p₀.I0 + 5 * p₀.nD + i) = σ₀ (fd₀.g i))
    (hQRV₁ : ∀ d, c.nmem (p₁.I0 + σ₁ d) = σ₁ (fd₁.Q.rev d))
    (hQNT₁ : ∀ d, c.nmem (p₁.I0 + p₁.nD + σ₁ d) = νv₁ (fd₁.Q.tail d))
    (hQNF₁ : ∀ d, c.nmem (p₁.I0 + 2 * p₁.nD + σ₁ d) = τ₁ (fd₁.Q.face d))
    (hQIS₁ : ∀ d, c.nmem (p₁.I0 + 3 * p₁.nD + σ₁ d) = if d ∈ fd₁.P'.image fd₁.e then 1 else 0)
    (hQLN₁ : ∀ d, c.nmem (p₁.I0 + 4 * p₁.nD + σ₁ d) = (faceLen fd₁.P' fd₁.e ℓ₁ d).toNat)
    (hQG₁ : ∀ i < fd₁.k, c.nmem (p₁.I0 + 5 * p₁.nD + i) = σ₁ (fd₁.g i)) :
    ∃ c' t, Exec P W (.seq (feProgDk p₀) (feProgDk p₁)) c c' t ∧ t ≤ feCostDk p₀ + feCostDk p₁ ∧
      (∃ (w : SrcD fd₀.DQ fd₀.k → ℤ) (Hc : ℕ),
        FEncNatNL fd₀ ℓ₀ p₀.NN p₀.Bw (srcNum σ₀) w (fePk p₀ c'.nmem) ∧
        fdHI fd₀ ℓ₀ (srcNum σ₀) w ≤ (Hc : ℝ) ∧ Hc ≤ kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k ∧
        KSlotN (srcMap fd₀.inst.cycle) fd₀.k (srcG fd₀.inst.cycle)
          (srcPiece fd₀.k (fd₀.P'.image fd₀.e))
          (srcIso (V := fd₀.VQ) (F := fd₀.FQ) fd₀.k (fd₀.P'.image fd₀.e)
            (faceLen fd₀.P' fd₀.e ℓ₀) w (srcNum σ₀)) (srcNum σ₀) p₀.Bw p₀.NN p₀.β p₀.RK
          (2 * Hc + 1) (fePk p₀ c'.nmem) c') ∧
      (∃ (w : SrcD fd₁.DQ fd₁.k → ℤ) (Hc : ℕ),
        FEncNatNL fd₁ ℓ₁ p₁.NN p₁.Bw (srcNum σ₁) w (fePk p₁ c'.nmem) ∧
        fdHI fd₁ ℓ₁ (srcNum σ₁) w ≤ (Hc : ℝ) ∧ Hc ≤ kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k ∧
        KSlotN (srcMap fd₁.inst.cycle) fd₁.k (srcG fd₁.inst.cycle)
          (srcPiece fd₁.k (fd₁.P'.image fd₁.e))
          (srcIso (V := fd₁.VQ) (F := fd₁.FQ) fd₁.k (fd₁.P'.image fd₁.e)
            (faceLen fd₁.P' fd₁.e ℓ₁) w (srcNum σ₁)) (srcNum σ₁) p₁.Bw p₁.NN p₁.β p₁.RK
          (2 * Hc + 1) (fePk p₁ c'.nmem) c') ∧
      (∀ a, a < p₀.β ∨ p₀.END ≤ a → a < p₁.β ∨ p₁.END ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r < 1400, c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨o₀1, o₀2, o₀3, o₀4⟩ := nbFeP_ord p₀
  obtain ⟨o₁1, o₁2, o₁3, o₁4⟩ := nbFeP_ord p₁
  obtain ⟨cD₀, -, -⟩ := fe_cards (k := fd₀.k) (D := fd₀.DQ) (V := fd₀.VQ) (F := fd₀.FQ) p₀ hD₀
    hk₀ hV₀ hF₀
  obtain ⟨cD₁, -, -⟩ := fe_cards (k := fd₁.k) (D := fd₁.DQ) (V := fd₁.VQ) (F := fd₁.FQ) p₁ hD₁
    hk₁ hV₁ hF₁
  -- the first encoder
  obtain ⟨c₀, t₀, e₀, ht₀, w₀, Hc₀, hv₀, hHI₀, hHle₀, hK₀, hm₀, hr₀, hrm₀, ho₀⟩ :=
    fencNatNL_Dk_exec (P := P) (W := W) fd₀ ℓ₀ σ₀ νv₀ τ₀ p₀ hD₀ hk₀ hV₀ hF₀
      (by clear * - o₀4 o₁1 o₁4 hE₀₁ hW; omega) hLm₀ hLW₀ hIW₀ hH₀ c hc hQRV₀ hQNT₀ hQNF₀ hQIS₀ hQLN₀
      hQG₀
  have hk0 : ∀ a, p₁.I0 ≤ a → c₀.nmem a = c.nmem a := fun a ha =>
    hm₀ a (Or.inr (by clear * - ha hE₀₁; omega))
  -- the second encoder
  obtain ⟨c₁, t₁, e₁, ht₁, w₁, Hc₁, hv₁, hHI₁, hHle₁, hK₁, hm₁, hr₁, hrm₁, ho₁⟩ :=
    fencNatNL_Dk_exec (P := P) (W := W) fd₁ ℓ₁ σ₁ νv₁ τ₁ p₁ hD₁ hk₁ hV₁ hF₁ hW hLm₁ hLW₁ hIW₁
      hH₁ c₀ e₀.wb_right
      (fun d => by rw [hk0 _ (Nat.le_add_right _ _)]; exact hQRV₁ d)
      (fun d => by rw [hk0 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))]; exact hQNT₁ d)
      (fun d => by rw [hk0 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))]; exact hQNF₁ d)
      (fun d => by rw [hk0 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))]; exact hQIS₁ d)
      (fun d => by rw [hk0 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))]; exact hQLN₁ d)
      (fun i hi => by rw [hk0 _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))]; exact hQG₁ i hi)
  -- the slot of the first encoder survives the second
  have hk1 : ∀ a, a < p₁.β → c₁.nmem a = c₀.nmem a := fun a ha => hm₁ a (Or.inl ha)
  have hKwlt : p₀.β + p₀.Kw < p₁.β := by clear * - o₀4 o₁1 hE₀₁; omega
  have hPk₀ : fePk p₀ c₁.nmem = fePk p₀ c₀.nmem :=
    nb_fePk_congr p₀ fun i hi => hk1 _ (by clear * - hi hKwlt; omega)
  have e01 := Exec.seq e₀ e₁
  refine ⟨c₁, t₀ + t₁, e01, Nat.add_le_add ht₀ ht₁, ⟨w₀, Hc₀, by rw [hPk₀]; exact hv₀, hHI₀, hHle₀,
    ⟨fun i hi => ?_, fun a ha => ?_⟩⟩, ⟨w₁, Hc₁, hv₁, hHI₁, hHle₁, hK₁⟩,
    fun a h0 h1 => ?_, nb_exec_keep e01 (by
      simp only [nbKeepsBelow, Stmt.allI, Bool.and_eq_true]
      exact ⟨nbFeProgDk_keeps p₀, nbFeProgDk_keeps p₁⟩), by rw [hr₁, hr₀], by rw [hrm₁, hrm₀],
    by rw [ho₁, ho₀]⟩
  · rw [hPk₀, hk1 _ (by have := p₀.kw_eq.2; clear * - hi hKwlt this; omega)]
    exact hK₀.dat i hi
  · rw [cD₀] at ha
    rw [hk1 _ (by clear * - ha o₀3 o₁1 hE₀₁; omega)]
    exact hK₀.res a (by rw [cD₀]; exact ha)
  · rw [hm₁ a h1, hm₀ a h0]

end Two

end NegSSSP

end PlanarFlow
