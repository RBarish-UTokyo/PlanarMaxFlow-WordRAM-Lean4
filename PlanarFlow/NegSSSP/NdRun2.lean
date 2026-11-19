module

public import PlanarFlow.NegSSSP.NdFullR

/-!
# The fixed node inside the driver, with the word bound of its memory

**`nd_run'`**: `nd_run` (a copy of its proof) with one more conclusion: every word of the
node's memory up to `WN` is at most `WN` at the end (the node runs with the word bound `WN`, and
the configuration of the driver agrees with it there). The outcome read back by `sgnD` is then
within `WN` of `0`, which the renormalization of the outcome needs.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge
  WordRAM.Machine.ModNat

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
open Classical in
/-- **The fixed node inside the driver**, `nd_run` with the words of the node's memory
bounded by `WN` at the end. -/
theorem nd_run' (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {P P₀ P₁ : Finset D} (hS : SplitF N P P₀ P₁) (hB : (bdry N P₀ P₁).Nonempty) (ℓ : D → ℤ)
    (δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    (fd₀ : FaceData N P₀ (bdry N P₀ P₁)) (hq₀ : fd₀.q ≤ 18 * P.card)
    (hk₀ : fd₀.k ^ 2 ≤ 1200 * P.card)
    (fd₁ : FaceData N P₁ (bdry N P₀ P₁)) (hq₁ : fd₁.q ≤ 18 * P.card)
    (hk₁ : fd₁.k ^ 2 ≤ 1200 * P.card)
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
    (Pb₀ Pb₁ Z M₀ Y S W' B M WN : ℕ) (I : Input) {W : ℕ}
    (hM₀ : M₀ = m + w + 1) (hZ : loB m w ≤ Z) (hbZ : bfWP b < Z)
    (hK₀ : 2 * p₀.Kw + 1 < Z) (hK₁ : 2 * p₁.Kw + 1 < Z)
    (hkk₀ : p₀.NN + fd₀.k * fd₀.k ≤ Z) (hkk₁ : p₁.NN + fd₁.k * fd₁.k ≤ Z)
    (hY : Z + 22 * M₀ ≤ Y)
    (hSz : w ≤ S ∧ b * b ≤ S ∧ fd₀.k ≤ S ∧ fd₁.k ≤ S)
    (hPb₀ : Pb₀ = Y + 16 * S) (hPb₁ : Pb₁ = Y + 16 * S + w)
    (hI0₀ : p₀.I0 = Y + 16 * S + 2 * w) (hI0₁ : p₁.I0 = p₀.END)
    (hL₀ : p₀.Lmax = feIsoB p₀.A p₀.N p₀.FN
      (srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat)
    (hL₁ : p₁.Lmax = feIsoB p₁.A p₁.N p₁.FN
      (srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat)
    (hW' : W' = pnW p₀ p₁)
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
    (d : Config) (hd : WordsBounded W d) (hWNW : WN ≤ W)
    -- the word bound of the node's part of `d`
    (hdr : ∀ r < 2920, d.nreg r ≤ WN) (hdm : ∀ a ≤ WN, d.nmem a ≤ WN)
    -- the natural part of the node's configuration
    (hr1 : ∀ r < 1000, d.nreg r ≤ W') (hmW : ∀ a ≤ W', d.nmem a ≤ W')
    (hctx : NCtx m w b Z M₀ d) (hx : XCtx Y S d)
    (hTm : ∀ i < m, d.nmem (Z + 0 * M₀ + i) = encT N e ν i)
    (hHm : ∀ i < m, d.nmem (Z + 1 * M₀ + i) = encH N e ν i)
    (hSm : ∀ i < m, d.nmem (Z + 2 * M₀ + i) = encS P₀ e i)
    (hz : ∀ a < Z, d.nmem a = 0)
    (hrz : ∀ r < 1000, d.nreg (1000 + r) = 0)
    (hres : ∀ a ≤ W', d.nmem (W' + 1 + a) < M ∧
      (d.nmem (W' + 1 + a) ≤ B ∨ M ≤ d.nmem (W' + 1 + a) + B))
    (hLm : ∀ i < m, (d.nmem (W' + 1 + (Z + 3 * M₀ + i)) : ℤ) = ℓ (e i) % M ∧ |ℓ (e i)| ≤ B)
    (hD₀ : ∀ v < w, (d.nmem (W' + 1 + (Z + 4 * M₀ + v)) : ℤ) = δ₀ (ι v) % M ∧ |δ₀ (ι v)| ≤ B)
    (hD₁ : ∀ v < w, (d.nmem (W' + 1 + (Z + 5 * M₀ + v)) : ℤ) = δ₁ (ι v) % M ∧ |δ₁ (ι v)| ≤ B)
    (hpos₀ : ∀ x ∈ bdry N P₀ P₁, d.nmem (Pb₀ + ν x) < fd₀.k ∧
      fd₀.Q.tail (fd₀.g (d.nmem (Pb₀ + ν x))) = fd₀.j x)
    (hpos₁ : ∀ x ∈ bdry N P₀ P₁, d.nmem (Pb₁ + ν x) < fd₁.k ∧
      fd₁.Q.tail (fd₁.g (d.nmem (Pb₁ + ν x))) = fd₁.j x)
    (hQRV₀ : ∀ x, d.nmem (p₀.I0 + σ₀ x) = σ₀ (fd₀.Q.rev x))
    (hQNT₀ : ∀ x, d.nmem (p₀.I0 + p₀.nD + σ₀ x) = νv₀ (fd₀.Q.tail x))
    (hQNF₀ : ∀ x, d.nmem (p₀.I0 + 2 * p₀.nD + σ₀ x) = τ₀ (fd₀.Q.face x))
    (hQIS₀ : ∀ x, d.nmem (p₀.I0 + 3 * p₀.nD + σ₀ x) = if x ∈ fd₀.P'.image fd₀.e then 1 else 0)
    (hQLN₀ : ∀ x, d.nmem (p₀.I0 + 4 * p₀.nD + σ₀ x) =
      (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀) x).toNat)
    (hQG₀ : ∀ i < fd₀.k, d.nmem (p₀.I0 + 5 * p₀.nD + i) = σ₀ (fd₀.g i))
    (hQRV₁ : ∀ x, d.nmem (p₁.I0 + σ₁ x) = σ₁ (fd₁.Q.rev x))
    (hQNT₁ : ∀ x, d.nmem (p₁.I0 + p₁.nD + σ₁ x) = νv₁ (fd₁.Q.tail x))
    (hQNF₁ : ∀ x, d.nmem (p₁.I0 + 2 * p₁.nD + σ₁ x) = τ₁ (fd₁.Q.face x))
    (hQIS₁ : ∀ x, d.nmem (p₁.I0 + 3 * p₁.nD + σ₁ x) = if x ∈ fd₁.P'.image fd₁.e then 1 else 0)
    (hQLN₁ : ∀ x, d.nmem (p₁.I0 + 4 * p₁.nD + σ₁ x) =
      (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁) x).toNat)
    (hQG₁ : ∀ i < fd₁.k, d.nmem (p₁.I0 + 5 * p₁.nD + i) = σ₁ (fd₁.g i))
    (hR0 : ∀ r, 2004 ≤ r → r < 2920 → (r < 2657 ∨ 2671 ≤ r) → d.nreg r ≤ W')
    (h9600 : 9600 ≤ WN) (hin : PnInR d.nreg p₀ p₁ m w b B Y S)
    (hBN : hnB p₀ p₁ Pb₀ Pb₁ W' M (nodeHN m b w B)
      (Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k) (Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k)
      (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat
      (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat ≤ WN)
    -- the log
    (h26 : d.nreg 2926 = 1) (h25 : WN < d.nreg 2925)
    (h25W : d.nreg 2925 + ndRunCost C P.card m w b fd₀.k fd₁.k p₀ p₁ ≤ W) :
    ∃ d' k' j, Exec I W (lgS 2925 2926 nodeFullR) d d' k' ∧
      k' ≤ 3 * ndRunCost C P.card m w b fd₀.k fd₁.k p₀ p₁ ∧
      j ≤ ndRunCost C P.card m w b fd₀.k fd₁.k p₀ p₁ ∧
      LgKeep (fun r => decide (r < 2920)) WN 2925 (d.nreg 2925) j d d' ∧
      d'.output = d.output ∧ (∀ a ≤ WN, d'.nmem a ≤ WN) ∧
      ((PotOut (pg N (P₀ ∪ P₁) ℓ) none ∧ d'.nreg 990 ≠ 0) ∨
        (∃ f, (pg N (P₀ ∪ P₁) ℓ).IsPot f ∧ d'.nreg 990 = 0 ∧
          ∀ x ∈ verts N (P₀ ∪ P₁),
            (f x : ℝ) = sgnD (nodeHN m b w B) M (d'.nmem (W' + 1 + (Z + 20 * M₀ + ν x))))) := by
  classical
  set U : ℕ → Bool := fun r => decide (r < 2920) with hU
  set d₀ := trunc U WN d with hd₀def
  -- the layout below `W'`
  have hE₀ := pn_end p₀
  have hE₁ := pn_end p₁
  have hWE : p₁.END ≤ W' := by rw [hW']; unfold pnW; omega
  have hw2 := hN.w2
  have h2W : 2 * W' + 1 ≤ WN := by have := hWN.1; omega
  have tm : ∀ a ≤ WN, d₀.nmem a = d.nmem a := fun a ha => trunc_nmem d ha
  have tr : ∀ r < 2920, d₀.nreg r = d.nreg r := fun r hr => trunc_nreg d hr
  have tr0 : ∀ r, 2920 ≤ r → d₀.nreg r = 0 := fun r hr => trunc_nreg0 d hr
  have hwb₀ : WordsBounded WN d₀ := wordsBounded_trunc (fun r hr => by
    simp only [hU, decide_eq_true_eq] at hr; exact hdr r hr) hdm
  have hσ₀ : ∀ x, (σ₀ x : ℕ) < p₀.nD := fun x => by rw [hpD₀]; exact (σ₀ x).2
  have hσ₁ : ∀ x, (σ₁ x : ℕ) < p₁.nD := fun x => by rw [hpD₁]; exact (σ₁ x).2
  have hk₀' : fd₀.k = p₀.k := hpk₀.symm
  have hk₁' : fd₁.k = p₁.k := hpk₁.symm
  have hνw : ∀ x ∈ bdry N P₀ P₁, ν x < w := fun x hx => hN.lt x (bdry_sub_verts hx)
  obtain ⟨c', t₀, t₁, t', o, Hc₀, Hc₁, -, -, -, -, ex, ht₀, ht₁, ht', hpo, hst, -, ho'⟩ :
      ∃ (c' : Config) (t₀ t₁ t' : ℕ) (o : Option (V → ℤ)) (Hc₀ Hc₁ : ℕ), 4800 ≤ Hc₀ ∧
        Hc₀ ≤ kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k ∧
        4800 ≤ Hc₁ ∧ Hc₁ ≤ kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k ∧
        Exec I WN nodeFullR d₀ c'
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
          (step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = none ∧ c'.nreg 990 ≠ 0) ∨
          (∃ f, step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = some f ∧ c'.nreg 990 = 0 ∧
            ∀ x ∈ verts N (P₀ ∪ P₁),
              (f x : ℝ) = sgnD (nodeHN m b w B) M (c'.nmem (W' + 1 + (Z + 20 * M₀ + ν x))))) ∧
        (∀ r, 2920 ≤ r → c'.nreg r = d₀.nreg r) ∧ c'.output = d₀.output := by
    obtain ⟨Hc₀, Hc₁, a1, a2, a3, a4, c', t₀, t₁, t', o, ex, ht₀, ht₁, ht', hpo, hst, hr, ho⟩ :=
      node_exec_fixedD C hfr hmssp hS hB ℓ δ₀ δ₁ hδ₀ hδ₁ fd₀ hq₀ hk₀ fd₁ hq₁ hk₁ σ₀ νv₀ τ₀ σ₁
        νv₁ τ₁ p₀ p₁ hpD₀ hpk₀ hpV₀ hpF₀ hpD₁ hpk₁ hpV₁ hpF₁ hN hb Pb₀ Pb₁ Z M₀ Y S W' B M WN
        I hM₀ hZ hbZ hK₀ hK₁ hkk₀ hkk₁ hY hSz hPb₀ hPb₁ hI0₀ hI0₁ hL₀ hL₁ hW' hWN hMd d₀ hwb₀
        (fun r hr => by rw [tr r (by omega)]; exact hr1 r hr)
        (fun a ha => by rw [tm a (by omega)]; exact hmW a ha)
        (hctx.of fun r h1 h2 => tr r (by omega)) (hx.of fun r h1 h2 => tr r (by omega))
        (fun i hi => by rw [tm _ (by omega)]; exact hTm i hi)
        (fun i hi => by rw [tm _ (by omega)]; exact hHm i hi)
        (fun i hi => by rw [tm _ (by omega)]; exact hSm i hi)
        (fun a ha => by rw [tm a (by omega)]; exact hz a ha)
        (fun r hr => by rw [tr _ (by omega)]; exact hrz r hr)
        (fun a ha => by rw [tm _ (by omega)]; exact hres a ha)
        (fun i hi => by rw [tm _ (by omega)]; exact hLm i hi)
        (fun v hv => by rw [tm _ (by omega)]; exact hD₀ v hv)
        (fun v hv => by rw [tm _ (by omega)]; exact hD₁ v hv)
        (fun x hx => by have := hνw x hx; rw [tm _ (by omega)]; exact hpos₀ x hx)
        (fun x hx => by have := hνw x hx; rw [tm _ (by omega)]; exact hpos₁ x hx)
        (fun x => by have := hσ₀ x; rw [tm _ (by omega)]; exact hQRV₀ x)
        (fun x => by have := hσ₀ x; rw [tm _ (by omega)]; exact hQNT₀ x)
        (fun x => by have := hσ₀ x; rw [tm _ (by omega)]; exact hQNF₀ x)
        (fun x => by have := hσ₀ x; rw [tm _ (by omega)]; exact hQIS₀ x)
        (fun x => by have := hσ₀ x; rw [tm _ (by omega)]; exact hQLN₀ x)
        (fun i hi => by rw [tm _ (by rw [hk₀'] at hi; omega)]; exact hQG₀ i hi)
        (fun x => by have := hσ₁ x; rw [tm _ (by omega)]; exact hQRV₁ x)
        (fun x => by have := hσ₁ x; rw [tm _ (by omega)]; exact hQNT₁ x)
        (fun x => by have := hσ₁ x; rw [tm _ (by omega)]; exact hQNF₁ x)
        (fun x => by have := hσ₁ x; rw [tm _ (by omega)]; exact hQIS₁ x)
        (fun x => by have := hσ₁ x; rw [tm _ (by omega)]; exact hQLN₁ x)
        (fun i hi => by rw [tm _ (by rw [hk₁'] at hi; omega)]; exact hQG₁ i hi)
        (fun r h1 h2 => by
          by_cases h : r < 2920
          · rw [tr r h]; exact hR0 r h1 h h2
          · rw [tr0 r (by omega)]; exact Nat.zero_le _)
        h9600
        ⟨(tr _ (by omega)).trans hin.a0, (tr _ (by omega)).trans hin.a1,
          (tr _ (by omega)).trans hin.a2, (tr _ (by omega)).trans hin.a3,
          (tr _ (by omega)).trans hin.b0, (tr _ (by omega)).trans hin.b1,
          (tr _ (by omega)).trans hin.b2, (tr _ (by omega)).trans hin.b3,
          (tr _ (by omega)).trans hin.m, (tr _ (by omega)).trans hin.w,
          (tr _ (by omega)).trans hin.b, (tr _ (by omega)).trans hin.B,
          (tr _ (by omega)).trans hin.Y, (tr _ (by omega)).trans hin.S⟩ hBN
    exact ⟨c', t₀, t₁, t', o, Hc₀, Hc₁, a1, a2, a3, a4, ex, ht₀, ht₁, ht', hpo, hst, hr, ho⟩
  have hT : t₀ + (hpCost (hfPrmL 0) + hpCost (hfPrmL 0) + hpCost hnPrmL + (t₁ + t')) ≤
      ndRunCost C P.card m w b fd₀.k fd₁.k p₀ p₁ := by
    unfold ndRunCost; omega
  obtain ⟨d', k', j, ex', hk', hj, hA, hK, hout⟩ :=
    lg_lift_trunc (P' := I) (W := W) (d := d) (LP := 2925) (ONE := 2926) ex nodeFullR_ok.1
      nodeFullR_ok.2.1 nodeFullR_ok.2.2 (by simp [hU]) (by simp [hU]) (by omega) hWNW hd h26 h25
      (by omega)
  have h990 : d'.nreg 990 = c'.nreg 990 := hA.nreg 990 (by simp [hU])
  have hmem : ∀ x ∈ verts N (P₀ ∪ P₁),
      d'.nmem (W' + 1 + (Z + 20 * M₀ + ν x)) = c'.nmem (W' + 1 + (Z + 20 * M₀ + ν x)) :=
    fun x hx => by
      have := hN.lt x hx
      exact hA.nmem _ (by omega)
  have hwN : ∀ a ≤ WN, d'.nmem a ≤ WN := fun a ha => by
    rw [hA.nmem a ha]; exact ex.wb_right.2 a
  refine ⟨d', k', j, ex', by omega, by omega, hK, by rw [hout, ho']; rfl, hwN, ?_⟩
  rcases nd_full_pot (Q := c'.nreg 990 ≠ 0)
      (R := fun f => c'.nreg 990 = 0 ∧ ∀ x ∈ verts N (P₀ ∪ P₁),
        (f x : ℝ) = sgnD (nodeHN m b w B) M (c'.nmem (W' + 1 + (Z + 20 * M₀ + ν x))))
      hfr hmssp hδ₀ hδ₁ hpo hst with ⟨h1, h2⟩ | ⟨f, h1, h2, h3⟩
  · exact Or.inl ⟨h1, by rw [h990]; exact h2⟩
  · exact Or.inr ⟨f, h1, by rw [h990]; exact h2, fun x hx => by rw [hmem x hx]; exact h3 x hx⟩

end NegSSSP

end PlanarFlow
