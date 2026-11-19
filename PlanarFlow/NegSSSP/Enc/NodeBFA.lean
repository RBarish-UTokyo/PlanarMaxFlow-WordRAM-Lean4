module

public import PlanarFlow.NegSSSP.Enc.FeFinal
public import PlanarFlow.Monge.CmpPlug

/-!
# The two encoders of a node, one after the other (distances by Bellman–Ford)

The node of the negative-length recursion (`node_exec_natNNL`) takes, for each of its two
one-face instances `fd₀`, `fd₁`, Klein's encoding in its natural memory (`FEncNatNL`, `KSlotN`).
Here the two composed encoders `feProg p₀`, `feProg p₁` (`fencNatNL_BF_exec`) are run one after
the other, the regions of the second (`[p₁.I0, p₁.END)`) above those of the first:

* `nbKeepsBelow lo s`: no instruction of `s` writes a natural register below `lo`
  (decidable); `nb_exec_keep`: such a statement keeps those registers;
  **`nbFeProg_keeps`**: `feProg p` writes only natural registers `≥ 1400` (kernel-checked, for
  every `p`), so it keeps every register the node reads (`800 … 999`) and its whole natural
  register file below `1000`.
* **`nbFe2_exec`**: the run of `feProg p₀ ; feProg p₁` within `feCost p₀ + feCost p₁` steps:
  both encodings at the end (in the final memory), the natural memory changed only in
  `[p₀.β, p₀.END) ∪ [p₁.β, p₁.END)`, the natural registers `< 1400`, the reals and the output
  kept.
* `nbFeCost_le`, **`nbFeCost_node_le`**: the cost of one encoder; at a one-face instance of a
  node (`fd.q ≤ 18 m`, `fd.k² ≤ 1200 m`), **`feCost p ≤ 186624 m² + 416324 m + 1184`**:
  quadratic, because the distances of the first root are computed by **Bellman–Ford**
  (`O(#V' · #D')`), not by a heap Dijkstra.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge.CmpAbs

/-- No instruction of `s` writes a natural register below `lo`. -/
def nbKeepsBelow (lo : ℕ) (s : Stmt) : Bool :=
  s.allI fun i => match i.wN with
    | some r => decide (lo ≤ r)
    | none => true

theorem nb_allI_mono {f g : Instr → Bool} (h : ∀ i, f i = true → g i = true) :
    ∀ s : Stmt, s.allI f = true → s.allI g = true := by
  intro s
  induction s with
  | skip => intro _; rfl
  | instr i => exact h i
  | seq s t ih₁ ih₂ =>
    simp only [Stmt.allI, Bool.and_eq_true]; exact fun hs => ⟨ih₁ hs.1, ih₂ hs.2⟩
  | ifLtN _ _ s t ih₁ ih₂ =>
    simp only [Stmt.allI, Bool.and_eq_true]; exact fun hs => ⟨ih₁ hs.1, ih₂ hs.2⟩
  | ifLtR _ _ s t ih₁ ih₂ =>
    simp only [Stmt.allI, Bool.and_eq_true]; exact fun hs => ⟨ih₁ hs.1, ih₂ hs.2⟩
  | whileLtN _ _ b ih => exact ih
  | whileLtR _ _ b ih => exact ih

theorem nb_keepsN {lo r : ℕ} {s : Stmt} (h : nbKeepsBelow lo s = true) (hr : r < lo) :
    keepsN r s = true := by
  refine nb_allI_mono (fun i hi => ?_) s h
  simp only [decide_eq_true_eq]
  intro he
  rw [he] at hi
  simp only [decide_eq_true_eq] at hi
  omega

/-- **A statement writing no natural register below `lo` keeps them.** -/
theorem nb_exec_keep {P : Input} {W lo : ℕ} {s : Stmt} {c d : Config} {k : ℕ}
    (e : Exec P W s c d k) (h : nbKeepsBelow lo s = true) : ∀ r < lo, d.nreg r = c.nreg r :=
  fun _ hr => e.nreg_keep (nb_keepsN h hr)

/-- **The composed encoder writes only natural registers `≥ 1400`** (for every `p`). -/
theorem nbFeProg_keeps (p : FeP) : nbKeepsBelow 1400 (feProg p) = true := by kernel_rfl

/-- `fePk` depends only on the slot. -/
theorem nb_fePk_congr (p : FeP) {m m' : ℕ → ℕ} (h : ∀ i ≤ p.Kw, m' (p.β + i) = m (p.β + i)) :
    fePk p m' = fePk p m := by
  unfold fePk
  congr 1
  exact List.ofFn_inj.2 (funext fun i => h i (by have := i.2; omega))

/-- The order of the regions used here (for `omega` in small contexts). -/
theorem nbFeP_ord (p : FeP) :
    p.I0 ≤ p.β ∧ p.β + p.Kw < p.RK ∧ p.RK + 3 * p.N + 3 ≤ p.END ∧ p.β + p.Kw < p.END := by
  simp only [FeP.β, FeP.RK, FeP.END, FeP.ISO, FeP.MK, FeP.RD, FeP.ZI, FeP.WW, FeP.ZC, FeP.O1,
    FeP.ZV, FeP.ONE, FeP.SL, FeP.DB, FeP.ZS, FeP.ZT, FeP.OS]
  omega

/-- The cost bound of the encoder with its linear terms collected. -/
theorem nbFeCost_le (p : FeP) :
    feCost p ≤ p.A * (24 * p.N + 6) + 1000 * (p.N + p.A + p.FN + p.nD + p.k) + 8 * p.Kw + 1000 := by
  unfold feCost feMidCost feEndCost feBCost osCost cotCost toCost
  omega

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

/-- **The cost of the encoder at a one-face instance of a node** (`fd.q ≤ 18 m`,
`fd.k² ≤ 1200 m`, as for `kw_existsNL_le`): **quadratic in `m`** (Bellman–Ford). -/
theorem nbFeCost_node_le {X : Finset D} {B : Finset V} (fd : FaceData N X B) (m : ℕ)
    (hq : fd.q ≤ 18 * m) (hk2 : fd.k ^ 2 ≤ 1200 * m) (p : FeP)
    (hD : p.nD = Fintype.card fd.DQ) (hk : p.k = fd.k) (hV : p.nV = Fintype.card fd.VQ)
    (hF : p.nF = Fintype.card fd.FQ) :
    feCost p ≤ 186624 * m ^ 2 + 416324 * m + 1184 := by
  have hc := fd.inst.card
  have hkV : fd.k ≤ Fintype.card fd.VQ := by
    have hinj : Function.Injective fun i : Fin fd.k => fd.Q.tail (fd.g i) := fun i j h =>
      Fin.ext (fd.inst.cycle.inj _ i.2 _ j.2 h)
    simpa using Fintype.card_le_of_injective _ hinj
  have hE := p.eqs
  obtain ⟨hBw, hKw⟩ := p.kw_eq
  have hkk : p.k * p.k ≤ 1200 * m := by rw [hk, ← pow_two]; exact hk2
  have hlin : p.N + p.A + p.FN + p.nD + p.k ≤ 288 * m ∧ p.A ≤ 54 * m ∧ p.N ≤ 144 * m ∧
      p.AE ≤ 234 * m := by
    obtain ⟨e1, e2, e3, e4, -⟩ := hE
    rw [← hk] at hkV
    clear * - e1 e2 e3 e4 hc hq hkV hD hV hF
    omega
  have hKw' : p.Kw ≤ 16000 * m + 23 := by
    obtain ⟨e1, e2, e3, e4, e5, -⟩ := hE
    rw [hKw, hBw]
    clear * - e1 e2 e3 e4 e5 hlin hkk
    omega
  have hprod : p.A * (24 * p.N + 6) ≤ 186624 * m ^ 2 + 324 * m := by
    calc p.A * (24 * p.N + 6) ≤ (54 * m) * (24 * (144 * m) + 6) :=
          Nat.mul_le_mul hlin.2.1 (by have := hlin.2.2.1; omega)
      _ = 186624 * m ^ 2 + 324 * m := by ring
  have := nbFeCost_le p
  generalize p.A * (24 * p.N + 6) = X at hprod this
  generalize m ^ 2 = Y at hprod ⊢
  clear * - this hprod hKw' hlin
  omega

section Two

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 4000000 in
open Classical in
/-- **The two encoders of a node, one after the other** (see the module docstring). -/
theorem nbFe2_exec {X₀ X₁ : Finset D} {B₀ B₁ : Finset V} (fd₀ : FaceData N X₀ B₀)
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
    ∃ c' t, Exec P W (.seq (feProg p₀) (feProg p₁)) c c' t ∧ t ≤ feCost p₀ + feCost p₁ ∧
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
    fencNatNL_BF_exec (P := P) (W := W) fd₀ ℓ₀ σ₀ νv₀ τ₀ p₀ hD₀ hk₀ hV₀ hF₀
      (by clear * - o₀4 o₁1 o₁4 hE₀₁ hW; omega) hLm₀ hLW₀ hIW₀ hH₀ c hc hQRV₀ hQNT₀ hQNF₀ hQIS₀ hQLN₀
      hQG₀
  have hk0 : ∀ a, p₁.I0 ≤ a → c₀.nmem a = c.nmem a := fun a ha =>
    hm₀ a (Or.inr (by clear * - ha hE₀₁; omega))
  -- the second encoder
  obtain ⟨c₁, t₁, e₁, ht₁, w₁, Hc₁, hv₁, hHI₁, hHle₁, hK₁, hm₁, hr₁, hrm₁, ho₁⟩ :=
    fencNatNL_BF_exec (P := P) (W := W) fd₁ ℓ₁ σ₁ νv₁ τ₁ p₁ hD₁ hk₁ hV₁ hF₁ hW hLm₁ hLW₁ hIW₁
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
      exact ⟨nbFeProg_keeps p₀, nbFeProg_keeps p₁⟩), by rw [hr₁, hr₀], by rw [hrm₁, hrm₀],
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
