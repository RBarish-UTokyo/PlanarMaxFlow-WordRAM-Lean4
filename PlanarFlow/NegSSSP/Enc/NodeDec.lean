module

public import PlanarFlow.NegSSSP.Enc.NodeRen

/-!
# The fixed node from a natural configuration alone

`node_exec_fixedR` runs the fixed node `nodeFullR` from a natural configuration `d₀` simulating a
real configuration `c` of the node (`Sim 1000 W' M (W' + 1) c d₀`), with the node's data stated on
`c`. A node step on the machine has only natural configurations: the real configuration is read
back from `d₀` (`decodeN`, the integers `sgnD H M v` of the residues, `H = nodeHN m b w B`).

* `zeroC`, `nodeC` (the configuration read back), `sgnD_abs_le` (a residue `v < M` with `v ≤ B`
  or `M ≤ v + B` reads back within `B`, `M = 2 H + 1`, `B ≤ H`).
* **`node_exec_fixedD`**: the statement of `node_exec_fixedR` with every hypothesis on `c` replaced
  by one on `d₀`: the natural registers below `1000` and the memory up to `W'` bounded by `W'`,
  `NCtx`, `XCtx`, the arrays `encT`, `encH`, `encS`, the zeros below `Z`, the positions and the
  plain arrays on `d₀.nmem`; the registers `1000 … 1999` zero; every residue `d₀.nmem (W' + 1 + a)`
  (`a ≤ W'`) below `M` and within `B` of `0` modulo `M`; the residues of the lengths `ℓ (e d)` and
  of the potentials `δᵢ (ι v)` at `W' + 1 + (Z + j M₀ + ·)` with `|·| ≤ B`. Conclusion: that of
  `node_exec_fixedR` with `d'.output = d₀.output`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge
  WordRAM.Machine.ModNat

/-- The configuration with all words zero (program counter and output of `d`). -/
def zeroC (d : Config) : Config where
  pc := d.pc
  nreg _ := 0
  rreg _ := 0
  nmem _ := 0
  rmem _ := 0
  output := d.output

theorem zeroC_wb (W : ℕ) (d : Config) : WordsBounded W (zeroC d) :=
  ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

theorem zeroC_int (d : Config) : IntAll (zeroC d) :=
  ⟨fun _ => ⟨0, by simp [zeroC]⟩, fun _ => ⟨0, by simp [zeroC]⟩⟩

/-- **A residue near `0` reads back within `B`.** -/
theorem sgnD_abs_le {H M B v : ℕ} (hM : M = 2 * H + 1) (hBH : B ≤ H) (hv : v < M)
    (hb : v ≤ B ∨ M ≤ v + B) : |sgnD H M v| ≤ (B : ℝ) := by
  unfold sgnD
  split_ifs with h
  · have : v ≤ B := by omega
    rw [abs_of_nonneg (by positivity)]; exact_mod_cast this
  · have h1 : M ≤ v + B := by omega
    have h2 : ((v : ℝ) - M) ≤ 0 := by
      have : (v : ℝ) < M := by exact_mod_cast hv
      linarith
    rw [abs_of_nonpos h2]
    have : (M : ℝ) ≤ v + B := by exact_mod_cast h1
    linarith

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
open Classical in
/-- **The fixed node from a natural configuration alone** (see the module docstring). -/
theorem node_exec_fixedD (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
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
    (Pb₀ Pb₁ Z M₀ Y S W' B M WN : ℕ) (I : Input)
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
    (d₀ : Config) (hd₀ : WordsBounded WN d₀)
    -- the natural part of the node's configuration
    (hr1 : ∀ r < 1000, d₀.nreg r ≤ W') (hmW : ∀ a ≤ W', d₀.nmem a ≤ W')
    (hctx : NCtx m w b Z M₀ d₀) (hx : XCtx Y S d₀)
    (hTm : ∀ d < m, d₀.nmem (Z + 0 * M₀ + d) = encT N e ν d)
    (hHm : ∀ d < m, d₀.nmem (Z + 1 * M₀ + d) = encH N e ν d)
    (hSm : ∀ d < m, d₀.nmem (Z + 2 * M₀ + d) = encS P₀ e d)
    (hz : ∀ a < Z, d₀.nmem a = 0)
    -- the residues: the real registers zero, the real memory read back within `B`
    (hrz : ∀ r < 1000, d₀.nreg (1000 + r) = 0)
    (hres : ∀ a ≤ W', d₀.nmem (W' + 1 + a) < M ∧
      (d₀.nmem (W' + 1 + a) ≤ B ∨ M ≤ d₀.nmem (W' + 1 + a) + B))
    (hLm : ∀ d < m, (d₀.nmem (W' + 1 + (Z + 3 * M₀ + d)) : ℤ) = ℓ (e d) % M ∧ |ℓ (e d)| ≤ B)
    (hD₀ : ∀ v < w, (d₀.nmem (W' + 1 + (Z + 4 * M₀ + v)) : ℤ) = δ₀ (ι v) % M ∧ |δ₀ (ι v)| ≤ B)
    (hD₁ : ∀ v < w, (d₀.nmem (W' + 1 + (Z + 5 * M₀ + v)) : ℤ) = δ₁ (ι v) % M ∧ |δ₁ (ι v)| ≤ B)
    (hpos₀ : ∀ x ∈ bdry N P₀ P₁, d₀.nmem (Pb₀ + ν x) < fd₀.k ∧
      fd₀.Q.tail (fd₀.g (d₀.nmem (Pb₀ + ν x))) = fd₀.j x)
    (hpos₁ : ∀ x ∈ bdry N P₀ P₁, d₀.nmem (Pb₁ + ν x) < fd₁.k ∧
      fd₁.Q.tail (fd₁.g (d₀.nmem (Pb₁ + ν x))) = fd₁.j x)
    -- the plain arrays of the two maps
    (hQRV₀ : ∀ d, d₀.nmem (p₀.I0 + σ₀ d) = σ₀ (fd₀.Q.rev d))
    (hQNT₀ : ∀ d, d₀.nmem (p₀.I0 + p₀.nD + σ₀ d) = νv₀ (fd₀.Q.tail d))
    (hQNF₀ : ∀ d, d₀.nmem (p₀.I0 + 2 * p₀.nD + σ₀ d) = τ₀ (fd₀.Q.face d))
    (hQIS₀ : ∀ d, d₀.nmem (p₀.I0 + 3 * p₀.nD + σ₀ d) = if d ∈ fd₀.P'.image fd₀.e then 1 else 0)
    (hQLN₀ : ∀ d, d₀.nmem (p₀.I0 + 4 * p₀.nD + σ₀ d) =
      (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀) d).toNat)
    (hQG₀ : ∀ i < fd₀.k, d₀.nmem (p₀.I0 + 5 * p₀.nD + i) = σ₀ (fd₀.g i))
    (hQRV₁ : ∀ d, d₀.nmem (p₁.I0 + σ₁ d) = σ₁ (fd₁.Q.rev d))
    (hQNT₁ : ∀ d, d₀.nmem (p₁.I0 + p₁.nD + σ₁ d) = νv₁ (fd₁.Q.tail d))
    (hQNF₁ : ∀ d, d₀.nmem (p₁.I0 + 2 * p₁.nD + σ₁ d) = τ₁ (fd₁.Q.face d))
    (hQIS₁ : ∀ d, d₀.nmem (p₁.I0 + 3 * p₁.nD + σ₁ d) = if d ∈ fd₁.P'.image fd₁.e then 1 else 0)
    (hQLN₁ : ∀ d, d₀.nmem (p₁.I0 + 4 * p₁.nD + σ₁ d) =
      (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁) d).toNat)
    (hQG₁ : ∀ i < fd₁.k, d₀.nmem (p₁.I0 + 5 * p₁.nD + i) = σ₁ (fd₁.g i))
    (hR0 : ∀ r, 2004 ≤ r → (r < 2657 ∨ 2671 ≤ r) → d₀.nreg r ≤ W') 
    -- the primary values of the parameter program and its word bounds
    (h9600 : 9600 ≤ WN) (hin : PnInR d₀.nreg p₀ p₁ m w b B Y S)
    (hBN : hnB p₀ p₁ Pb₀ Pb₁ W' M (nodeHN m b w B)
      (Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k) (Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k)
      (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat
      (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat ≤ WN) :
    ∃ (Hc₀ Hc₁ : ℕ), 4800 ≤ Hc₀ ∧ Hc₀ ≤ kcnHc p₀.A p₀.FN (p₀.N * p₀.Lmax) p₀.k ∧
      4800 ≤ Hc₁ ∧ Hc₁ ≤ kcnHc p₁.A p₁.FN (p₁.N * p₁.Lmax) p₁.k ∧
      ∃ d' t₀ t₁ t', ∃ o : Option (V → ℤ),
        Exec I WN nodeFullR d₀ d'
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
        (∀ r, 2920 ≤ r → d'.nreg r = d₀.nreg r) ∧ d'.output = d₀.output := by
  classical
  set H := nodeHN m b w B with hH
  set c : Config := decodeN 1000 W' M H (W' + 1) (zeroC d₀) d₀ with hcdef
  have hBH : B ≤ H := by rw [hH]; unfold nodeHN; omega
  have hM2 : 2 * H < M := by rw [hMd]; omega
  have hM0 : 0 < M := by omega
  have cN : ∀ a ≤ W', c.nmem a = d₀.nmem a := fun a ha => by simp [hcdef, decodeN, ha]
  have cR : ∀ a ≤ W', c.rmem a = sgnD H M (d₀.nmem (W' + 1 + a)) := fun a ha => by
    simp [hcdef, decodeN, ha]
  have cG : ∀ r < 1000, c.nreg r = d₀.nreg r := fun r hr => by simp [hcdef, decodeN, hr]
  -- the layout below `W'`
  have hE₀ := pn_end p₀
  have hE₁ := pn_end p₁
  have hWE : p₁.END ≤ W' := by rw [hW']; unfold pnW; omega
  have hI0W : Y + 16 * S + 2 * w ≤ W' := by omega
  have hZW : Z + 22 * M₀ ≤ W' := by omega
  have hEW₀ : p₀.I0 + 5 * p₀.nD + p₀.k ≤ W' := by omega
  have hEW₁ : p₁.I0 + 5 * p₁.nD + p₁.k ≤ W' := by omega
  have hσ₀ : ∀ d, (σ₀ d : ℕ) < p₀.nD := fun d => by rw [hpD₀]; exact (σ₀ d).2
  have hσ₁ : ∀ d, (σ₁ d : ℕ) < p₁.nD := fun d => by rw [hpD₁]; exact (σ₁ d).2
  have hνb : ∀ x ∈ bdry N P₀ P₁, ν x < w := fun x hx => by
    obtain ⟨d, hd, h⟩ := mem_verts.1 (mem_inter.1 hx).1
    exact hN.lt x (mem_verts.2 ⟨d, mem_union_left _ hd, h⟩)
  have hres' : ∀ (z : ℤ) (a : ℕ), a ≤ W' → (d₀.nmem (W' + 1 + a) : ℤ) = z % M → |z| ≤ B →
      c.rmem a = z := fun z a ha h1 h2 => by
    rw [cR a ha]
    refine sgnD_eq ⟨z, rfl, h1⟩ ?_ hM2
    rw [← Int.cast_abs]
    have : (B : ℤ) ≤ H := by exact_mod_cast hBH
    exact_mod_cast (show |z| ≤ (H : ℤ) by omega)
  have hS₀ : Sim 1000 W' M (W' + 1) c d₀ :=
    sim_decodeN (fun r hr => by rw [hrz r hr]; exact hM0) (fun a ha => (hres a ha).1)
  have hI : NInv W' B c := ⟨fun a ha => by
      rw [cR a ha]; exact sgnD_abs_le hMd hBH (hres a ha).1 (hres a ha).2,
    fun r h1 h2 => by
      simp only [hcdef, decodeN, show r < 1000 by omega, ↓reduceIte, hrz r (by omega)]
      simp [sgnD]⟩
  exact node_exec_fixedR C hfr hmssp hS hB ℓ δ₀ δ₁ hδ₀ hδ₁ fd₀ hq₀ hk₀ fd₁ hq₁ hk₁ σ₀ νv₀ τ₀ σ₁
    νv₁ τ₁ p₀ p₁ hpD₀ hpk₀ hpV₀ hpF₀ hpD₁ hpk₁ hpV₁ hpF₁ hN hb Pb₀ Pb₁ Z M₀ Y S W' B M WN I c
    hM₀ hZ hbZ hK₀ hK₁ hkk₀ hkk₁ hY hSz hPb₀ hPb₁ hI0₀ hI0₁ hL₀ hL₁ hW' hWN hMd
    (wb_decodeN (zeroC_wb W' d₀) hr1 hmW)
    (NCtx.of hctx fun r h1 h2 => cG r (by omega)) (XCtx.of hx fun r h1 h2 => cG r (by omega))
    (fun d hd => by rw [cN _ (by omega)]; exact hTm d hd)
    (fun d hd => by rw [cN _ (by omega)]; exact hHm d hd)
    (fun d hd => by rw [cN _ (by omega)]; exact hSm d hd)
    (fun d hd => hres' _ _ (by omega) (hLm d hd).1 (hLm d hd).2)
    (fun v hv => hres' _ _ (by omega) (hD₀ v hv).1 (hD₀ v hv).2)
    (fun v hv => hres' _ _ (by omega) (hD₁ v hv).1 (hD₁ v hv).2)
    (fun a ha => by rw [cN _ (by omega)]; exact hz a ha)
    (fun x hx => by have := hνb x hx; rw [cN _ (by omega)]; exact hpos₀ x hx)
    (fun x hx => by have := hνb x hx; rw [cN _ (by omega)]; exact hpos₁ x hx)
    (fun d => by have := hσ₀ d; rw [cN _ (by omega)]; exact hQRV₀ d)
    (fun d => by have := hσ₀ d; rw [cN _ (by omega)]; exact hQNT₀ d)
    (fun d => by have := hσ₀ d; rw [cN _ (by omega)]; exact hQNF₀ d)
    (fun d => by have := hσ₀ d; rw [cN _ (by omega)]; exact hQIS₀ d)
    (fun d => by have := hσ₀ d; rw [cN _ (by omega)]; exact hQLN₀ d)
    (fun i hi => by rw [cN _ (by rw [hpk₀] at hEW₀; omega)]; exact hQG₀ i hi)
    (fun d => by have := hσ₁ d; rw [cN _ (by omega)]; exact hQRV₁ d)
    (fun d => by have := hσ₁ d; rw [cN _ (by omega)]; exact hQNT₁ d)
    (fun d => by have := hσ₁ d; rw [cN _ (by omega)]; exact hQNF₁ d)
    (fun d => by have := hσ₁ d; rw [cN _ (by omega)]; exact hQIS₁ d)
    (fun d => by have := hσ₁ d; rw [cN _ (by omega)]; exact hQLN₁ d)
    (fun i hi => by rw [cN _ (by rw [hpk₁] at hEW₁; omega)]; exact hQG₁ i hi)
    hI (intAll_decodeN (zeroC_int d₀)) d₀ hS₀ hd₀ hR0 h9600 hin hBN

end NegSSSP

end PlanarFlow
