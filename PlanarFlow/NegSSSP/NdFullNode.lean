module

public import PlanarFlow.NegSSSP.NdFullOut

/-!
# The full branch: the node from its prepared data

**`fbTail WN`** `= fbR ; lgS 2925 2926 nodeFullR ; fbOut WN`: from a configuration `c` holding
the node's data (every memory hypothesis of `nd_run'` stated on `c`, the registers as `fbC2`
leaves them), **`fs_node`**: the registers set up (`fbR_exec`), the node run with its stores
logged (`nd_run'`), and the outcome (`fbNo_exec` / `fbYes_exec`): a `PotOut` outcome `o` of the
piece `P₀ ∪ P₁` in the frame (`Res`), every cell up to `WN` zero again (if it was zero outside
the node's arrays `[Z, END₁)` and residues `[R, R + 3M₀)`), the memory between `WN` and the
frame and between the frame and the heap top kept, registers `≥ 3000`, reals, output kept.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open Finset Klein WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge
  WordRAM.Machine.ModNat

variable {W : ℕ}

/-- **The node and its outcome.** -/
def fbTail (WN : ℕ) : Stmt := .seq fbR (.seq (lgS 2925 2926 nodeFullR) (fbOut WN))

/-- The registers after `fbR` are bounded (the hypotheses `hr1`, `hR0`, `hdr` of `nd_run`). -/
theorem fbR_regs_le {d : Config} {m w b Z M₀ Y S B W' WN : ℕ} {p₀ p₁ : FeP}
    (hctx : NCtx m w b Z M₀ d) (hx : XCtx Y S d) (hin : PnInR d.nreg p₀ p₁ m w b B Y S)
    (hz : ∀ r < 2920, (r < 800 ∨ (825 < r ∧ r < 930) ∨ (945 < r ∧ r < 2657) ∨ 2670 < r) →
      d.nreg r = 0)
    (hm : m ≤ W') (hw : w ≤ W') (hb : b ≤ W') (hZ : Z + 21 * M₀ ≤ W') (hlo : loB m w ≤ W')
    (hY : Y + 15 * S ≤ W') (hs : p₀.nD ≤ WN ∧ p₀.k ≤ WN ∧ p₀.nV ≤ WN ∧ p₀.nF ≤ WN ∧
      p₁.nD ≤ WN ∧ p₁.k ≤ WN ∧ p₁.nV ≤ WN ∧ p₁.nF ≤ WN) (hBN : B ≤ WN) (hWN : W' ≤ WN) :
    (∀ r < 1000, d.nreg r ≤ W') ∧
    (∀ r, 2004 ≤ r → r < 2920 → (r < 2657 ∨ 2671 ≤ r) → d.nreg r ≤ W') ∧
    (∀ r < 2920, d.nreg r ≤ WN) := by
  have h1 : ∀ r < 1000, d.nreg r ≤ W' := by
    intro r hr
    by_cases a : 800 ≤ r ∧ r ≤ 825
    · by_cases a1 : r = 800
      · subst a1; rw [hctx.r800]; exact hm
      by_cases a2 : r = 801
      · subst a2; rw [hctx.r801]; exact hw
      by_cases a3 : r = 802
      · subst a3; rw [hctx.r802]; exact hb
      by_cases a4 : r = 825
      · subst a4; rw [hctx.r825]; exact hlo
      obtain ⟨j, rfl⟩ : ∃ j, r = 803 + j := ⟨r - 803, by omega⟩
      rw [hctx.slot j (by omega)]
      have : j * M₀ ≤ 21 * M₀ := Nat.mul_le_mul_right _ (by omega)
      omega
    by_cases b' : 930 ≤ r ∧ r ≤ 945
    · obtain ⟨j, rfl⟩ : ∃ j, r = 930 + j := ⟨r - 930, by omega⟩
      rw [hx.reg j (by omega)]
      have : j * S ≤ 15 * S := Nat.mul_le_mul_right _ (by omega)
      omega
    rw [hz r (by omega) (by omega)]; exact Nat.zero_le _
  refine ⟨h1, fun r h2 h3 h4 => by rw [hz r h3 (by omega)]; exact Nat.zero_le _, fun r hr => ?_⟩
  by_cases a : r < 1000
  · exact (h1 r a).trans hWN
  by_cases b' : 2657 ≤ r ∧ r ≤ 2670
  · obtain ⟨a0, a1, a2, a3, b0, b1, b2, b3, em, ew, eb, eB, eY, eS⟩ := hin
    obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := hs
    have hj : r = 2657 ∨ r = 2658 ∨ r = 2659 ∨ r = 2660 ∨ r = 2661 ∨ r = 2662 ∨ r = 2663 ∨
        r = 2664 ∨ r = 2665 ∨ r = 2666 ∨ r = 2667 ∨ r = 2668 ∨ r = 2669 ∨ r = 2670 := by omega
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl
    · rw [a0]; exact s1
    · rw [a1]; exact s2
    · rw [a2]; exact s3
    · rw [a3]; exact s4
    · rw [b0]; exact s5
    · rw [b1]; exact s6
    · rw [b2]; exact s7
    · rw [b3]; exact s8
    · rw [em]; omega
    · rw [ew]; omega
    · rw [eb]; omega
    · rw [eB]; exact hBN
    · rw [eY]; omega
    · rw [eS]; omega
  rw [hz r hr (by omega)]; exact Nat.zero_le _

set_option maxRecDepth 100000 in
theorem nodeFullR_natOnly : Klein.natOnly nodeFullR = true := by kernel_rfl

/-- The cost of `fbTail`. -/
def fsNodeCost (R E Z M₀ m w : ℕ) : ℕ := fbRCost + (3 * R + (2 + fbYesCost R (E - Z) (3 * M₀) m w))

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] [Fintype F] [DecidableEq F] {N : CombMap D V F}

theorem fs_arith {p₀ p₁ : FeP} {W' WN M Z M₀ Y S w m b B : ℕ}
    (hW' : W' = pnW p₀ p₁) (hWN1 : 2 * W' + 1 + M * M + M ≤ WN)
    (hMd : M = 2 * nodeHN m b w B + 1) (hY : Z + 22 * M₀ ≤ Y)
    (hI0₀ : p₀.I0 = Y + 16 * S + 2 * w) (hI0₁ : p₁.I0 = p₀.END) (hZ : loB m w ≤ Z)
    (hbb : b * b ≤ S) (hM₀ : M₀ = m + w + 1) :
    p₁.END ≤ W' ∧ B ≤ nodeHN m b w B ∧ 2 * W' + 1 + M ≤ WN ∧ Z + 22 * M₀ ≤ W' ∧
    Y + 16 * S + 2 * w ≤ W' ∧ 4 * m + 18 * w + 175 ≤ Z ∧ b ≤ S ∧ m + w + 1 ≤ M₀ ∧
    p₀.nD ≤ W' ∧ p₀.k ≤ W' ∧ p₀.nV ≤ W' ∧ p₀.nF ≤ W' ∧ p₁.nD ≤ W' ∧ p₁.k ≤ W' ∧
    p₁.nV ≤ W' ∧ p₁.nF ≤ W' := by
  have hE₀ := pn_end p₀
  have hE₁ := pn_end p₁
  have hWE : p₁.END ≤ W' := by rw [hW']; unfold pnW; omega
  have hMM : M ≤ M * M + M := Nat.le_add_left _ _
  have hBH : B ≤ nodeHN m b w B := by unfold nodeHN; omega
  have hbS : b ≤ S := (Nat.le_mul_self b).trans hbb
  unfold loB at hZ
  refine ⟨hWE, hBH, by omega, by omega, by omega, hZ, hbS, by omega, ?_⟩
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
open Classical in
/-- **The registers and the node** (the first half of `fs_node`). -/
theorem fs_run (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {P₀ P₁ : Finset D} (hS : SplitF N (P₀ ∪ P₁) P₀ P₁) (hB : (bdry N P₀ P₁).Nonempty) (ℓ : D → ℤ)
    (δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    (fd₀ : FaceData N P₀ (bdry N P₀ P₁)) (hq₀ : fd₀.q ≤ 18 * (P₀ ∪ P₁).card)
    (hk₀ : fd₀.k ^ 2 ≤ 1200 * (P₀ ∪ P₁).card)
    (fd₁ : FaceData N P₁ (bdry N P₀ P₁)) (hq₁ : fd₁.q ≤ 18 * (P₀ ∪ P₁).card)
    (hk₁ : fd₁.k ^ 2 ≤ 1200 * (P₀ ∪ P₁).card)
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
    {g : Frame.GIds D V} {L n k h df de : ℕ}
    (c : Config) (hc : WordsBounded W c) (hWNW : WN ≤ W)
    (hinP : Frame.InP g N ℓ L n (P₀ ∪ P₁) df de c)
    (hm : m = (P₀ ∪ P₁).card) (hk : k = Frame.ck N (P₀ ∪ P₁))
    (r1022 : c.nreg 1022 = W') (r2313 : c.nreg 2313 = Z) (r2314 : c.nreg 2314 = M₀)
    (r1024 : c.nreg 1024 = nodeHN m b w B) (r1023 : c.nreg 1023 = M)
    (r2321 : c.nreg 2321 = p₁.END)
    (r2464 : c.nreg 2464 = w) (r2474 : c.nreg 2474 = m) (r2475 : c.nreg 2475 = k)
    (r2496 : c.nreg 2496 = b) (r2205 : c.nreg 2205 = B) (r2315 : c.nreg 2315 = Y)
    (r2316 : c.nreg 2316 = S)
    (e40 : c.nreg 2240 = p₀.nD) (e43 : c.nreg 2243 = p₀.k) (e41 : c.nreg 2241 = p₀.nV)
    (e00 : c.nreg 2300 = p₀.nF) (f44 : c.nreg 2244 = p₁.nD) (f47 : c.nreg 2247 = p₁.k)
    (f45 : c.nreg 2245 = p₁.nV) (f01 : c.nreg 2301 = p₁.nF) (r3003 : c.nreg 3003 = h)
    (r3004 : c.nreg 3004 = df)
    (hdm : ∀ a ≤ WN, c.nmem a ≤ WN)
    -- the node's data on `c`
    (hmW : ∀ a ≤ W', c.nmem a ≤ W') (h9600 : 9600 ≤ WN)
    (hTm : ∀ i < m, c.nmem (Z + 0 * M₀ + i) = encT N e ν i)
    (hHm : ∀ i < m, c.nmem (Z + 1 * M₀ + i) = encH N e ν i)
    (hSm : ∀ i < m, c.nmem (Z + 2 * M₀ + i) = encS P₀ e i)
    (hz : ∀ a < Z, c.nmem a = 0)
    (hres : ∀ a ≤ W', c.nmem (W' + 1 + a) < M ∧
      (c.nmem (W' + 1 + a) ≤ B ∨ M ≤ c.nmem (W' + 1 + a) + B))
    (hLm : ∀ i < m, (c.nmem (W' + 1 + (Z + 3 * M₀ + i)) : ℤ) = ℓ (e i) % M ∧ |ℓ (e i)| ≤ B)
    (hD₀ : ∀ v < w, (c.nmem (W' + 1 + (Z + 4 * M₀ + v)) : ℤ) = δ₀ (ι v) % M ∧ |δ₀ (ι v)| ≤ B)
    (hD₁ : ∀ v < w, (c.nmem (W' + 1 + (Z + 5 * M₀ + v)) : ℤ) = δ₁ (ι v) % M ∧ |δ₁ (ι v)| ≤ B)
    (hpos₀ : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₀ + ν x) < fd₀.k ∧
      fd₀.Q.tail (fd₀.g (c.nmem (Pb₀ + ν x))) = fd₀.j x)
    (hpos₁ : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₁ + ν x) < fd₁.k ∧
      fd₁.Q.tail (fd₁.g (c.nmem (Pb₁ + ν x))) = fd₁.j x)
    (hQRV₀ : ∀ x, c.nmem (p₀.I0 + σ₀ x) = σ₀ (fd₀.Q.rev x))
    (hQNT₀ : ∀ x, c.nmem (p₀.I0 + p₀.nD + σ₀ x) = νv₀ (fd₀.Q.tail x))
    (hQNF₀ : ∀ x, c.nmem (p₀.I0 + 2 * p₀.nD + σ₀ x) = τ₀ (fd₀.Q.face x))
    (hQIS₀ : ∀ x, c.nmem (p₀.I0 + 3 * p₀.nD + σ₀ x) = if x ∈ fd₀.P'.image fd₀.e then 1 else 0)
    (hQLN₀ : ∀ x, c.nmem (p₀.I0 + 4 * p₀.nD + σ₀ x) =
      (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀) x).toNat)
    (hQG₀ : ∀ i < fd₀.k, c.nmem (p₀.I0 + 5 * p₀.nD + i) = σ₀ (fd₀.g i))
    (hQRV₁ : ∀ x, c.nmem (p₁.I0 + σ₁ x) = σ₁ (fd₁.Q.rev x))
    (hQNT₁ : ∀ x, c.nmem (p₁.I0 + p₁.nD + σ₁ x) = νv₁ (fd₁.Q.tail x))
    (hQNF₁ : ∀ x, c.nmem (p₁.I0 + 2 * p₁.nD + σ₁ x) = τ₁ (fd₁.Q.face x))
    (hQIS₁ : ∀ x, c.nmem (p₁.I0 + 3 * p₁.nD + σ₁ x) = if x ∈ fd₁.P'.image fd₁.e then 1 else 0)
    (hQLN₁ : ∀ x, c.nmem (p₁.I0 + 4 * p₁.nD + σ₁ x) =
      (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁) x).toNat)
    (hQG₁ : ∀ i < fd₁.k, c.nmem (p₁.I0 + 5 * p₁.nD + i) = σ₁ (fd₁.g i))
    (hBN : hnB p₀ p₁ Pb₀ Pb₁ W' M (nodeHN m b w B)
      (Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k) (Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k)
      (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat
      (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat ≤ WN)
    -- the layout
    (hWdf : WN < df) (hdeh : de ≤ h)
    (hRW : h + 200 * k + ndRunCost C (P₀ ∪ P₁).card m w b fd₀.k fd₁.k p₀ p₁ ≤ W)
    (hW96 : 9600 ≤ W) :
    ∃ d' t j, Exec I W (.seq fbR (lgS 2925 2926 nodeFullR)) c d' t ∧
      t ≤ fbRCost + 3 * ndRunCost C (P₀ ∪ P₁).card m w b fd₀.k fd₁.k p₀ p₁ ∧
      j ≤ ndRunCost C (P₀ ∪ P₁).card m w b fd₀.k fd₁.k p₀ p₁ ∧
      d'.nreg 2924 = h + 200 * k ∧ d'.nreg 2925 = h + 200 * k + j ∧ d'.nreg 2926 = 1 ∧
      d'.nreg 2954 = p₁.END - Z ∧ d'.nreg 2931 = Z ∧ d'.nreg 2953 = 3 * M₀ ∧
      d'.nreg 2952 = W' + Z + 3 * M₀ + 1 ∧ d'.nreg 2937 = m ∧ d'.nreg 2938 = k ∧
      d'.nreg 2936 = w ∧ d'.nreg 2951 = W' + Z + 20 * M₀ + 1 ∧ d'.nreg 2957 = h + 8 * k ∧
      d'.nreg 2934 = M ∧ d'.nreg 2933 = nodeHN m b w B ∧ d'.nreg 2956 = 0 ∧
      (∀ r, 3000 ≤ r → d'.nreg r = c.nreg r) ∧
      (∀ i < j, d'.nmem (h + 200 * k + i) ≤ WN) ∧
      (∀ a ≤ WN, (∀ i < j, d'.nmem (h + 200 * k + i) ≠ a) → d'.nmem a = c.nmem a) ∧
      (∀ a, WN < a → a < h + 200 * k → d'.nmem a = c.nmem a) ∧
      (∀ a ≤ WN, d'.nmem a ≤ WN) ∧
      d'.rreg = c.rreg ∧ d'.rmem = c.rmem ∧ d'.output = c.output ∧
      ((PotOut (pg N (P₀ ∪ P₁) ℓ) none ∧ d'.nreg 990 ≠ 0) ∨
        (∃ f, (pg N (P₀ ∪ P₁) ℓ).IsPot f ∧ d'.nreg 990 = 0 ∧
          ∀ x ∈ verts N (P₀ ∪ P₁),
            (f x : ℝ) = sgnD (nodeHN m b w B) M (d'.nmem (W' + 1 + (Z + 20 * M₀ + ν x))))) := by
  classical
  obtain ⟨A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16⟩ :=
    fs_arith (B := B) hW' hWN.1 hMd hY hI0₀ hI0₁ hZ hSz.2.1 hM₀
  have hen := hinP.en
  unfold Frame.fsz at hen
  have hmk : m ≤ k := by rw [hm, hk]; exact Frame.ck_ge _
  have b1 : h + 200 * k ≤ W := by clear * - hRW; omega
  have b2 : W' + Z + 20 * M₀ + 1 ≤ W := by clear * - A3 A4 hWNW; omega
  have b3 : Z + 21 * M₀ ≤ W := by clear * - A3 A4 hWNW; omega
  have b4 : 4 * m + 18 * w + 175 ≤ W := by clear * - A3 A4 A6 hWNW; omega
  have b5 : Y + 15 * S ≤ W := by clear * - A3 A5 hWNW; omega
  have b6 : WN < h + 200 * k := by clear * - hWdf hdeh hen; omega
  -- the registers
  obtain ⟨d, t₁, e₁, ht₁, s30, s31, s32, s33, s34, s35, s36, s37, s38, s24, s25, s26, s51, s52,
    s53, s54, s56, s57, hctx, hx, hinR, hz0, hkR, hm₁, hr₁, hrm₁, ho₁⟩ :=
    fbR_exec (P := I) c hc r1022 r2313 r2314 r1024 r1023 r2321 r2464 r2474 r2475 r2496 r2205
      r2315 r2316 e40 e43 e41 e00 f44 f47 f45 f01 r3003 hW96 b1 b2 b3 b4 b5
  have hm₁' : ∀ a, d.nmem a = c.nmem a := fun a => by rw [hm₁]
  obtain ⟨hr1, hR0, hdr⟩ := fbR_regs_le (W' := W') (WN := WN) hctx hx hinR hz0 (by clear * - A8 A4; omega)
    (by clear * - A8 A4; omega) (by clear * - A7 A5; omega) (by clear * - A4; omega)
    (by unfold loB; clear * - A6 A4; omega) (by clear * - A5; omega)
    ⟨by clear * - A9 A3; omega, by clear * - A10 A3; omega, by clear * - A11 A3; omega,
      by clear * - A12 A3; omega, by clear * - A13 A3; omega, by clear * - A14 A3; omega,
      by clear * - A15 A3; omega, by clear * - A16 A3; omega⟩
    (by clear * - A2 A3 hMd; omega) (by clear * - A3; omega)
  have hrz : ∀ r < 1000, d.nreg (1000 + r) = 0 := fun r hr => hz0 (1000 + r) (by omega) (by omega)
  -- the node
  obtain ⟨d', k', j, ex', hk', hj, hK, hout', hwN, hres'⟩ := nd_run' C hfr hmssp hS hB ℓ δ₀ δ₁
    hδ₀ hδ₁ fd₀ hq₀ hk₀ fd₁ hq₁ hk₁ σ₀ νv₀ τ₀ σ₁ νv₁ τ₁ p₀ p₁ hpD₀ hpk₀ hpV₀ hpF₀ hpD₁ hpk₁ hpV₁
    hpF₁ hN hb Pb₀ Pb₁ Z M₀ Y S W' B M WN I hM₀ hZ hbZ hK₀ hK₁ hkk₀ hkk₁ hY hSz hPb₀ hPb₁ hI0₀
    hI0₁ hL₀ hL₁ hW' hWN hMd d e₁.wb_right hWNW hdr (fun a ha => by rw [hm₁']; exact hdm a ha)
    hr1 (fun a ha => by rw [hm₁']; exact hmW a ha) hctx hx
    (fun i hi => by rw [hm₁']; exact hTm i hi) (fun i hi => by rw [hm₁']; exact hHm i hi)
    (fun i hi => by rw [hm₁']; exact hSm i hi) (fun a ha => by rw [hm₁']; exact hz a ha)
    hrz (fun a ha => by rw [hm₁']; exact hres a ha)
    (fun i hi => by rw [hm₁']; exact hLm i hi) (fun v hv => by rw [hm₁']; exact hD₀ v hv)
    (fun v hv => by rw [hm₁']; exact hD₁ v hv) (fun x hx => by rw [hm₁']; exact hpos₀ x hx)
    (fun x hx => by rw [hm₁']; exact hpos₁ x hx)
    (fun x => by rw [hm₁']; exact hQRV₀ x) (fun x => by rw [hm₁']; exact hQNT₀ x)
    (fun x => by rw [hm₁']; exact hQNF₀ x) (fun x => by rw [hm₁']; exact hQIS₀ x)
    (fun x => by rw [hm₁']; exact hQLN₀ x) (fun i hi => by rw [hm₁']; exact hQG₀ i hi)
    (fun x => by rw [hm₁']; exact hQRV₁ x) (fun x => by rw [hm₁']; exact hQNT₁ x)
    (fun x => by rw [hm₁']; exact hQNF₁ x) (fun x => by rw [hm₁']; exact hQIS₁ x)
    (fun x => by rw [hm₁']; exact hQLN₁ x) (fun i hi => by rw [hm₁']; exact hQG₁ i hi)
    hR0 h9600 hinR hBN s26 (by rw [s25]; exact b6) (by rw [s25]; exact hRW)
  rw [s25] at hK
  have KR : ∀ r, 2920 ≤ r → r ≠ 2925 → d'.nreg r = d.nreg r := fun r h1 h2 =>
    hK.nreg r (by simp only [decide_eq_false_iff_not]; omega) h2
  obtain ⟨hrr', hrm'⟩ := Frame.exec_reals_keep (lgS_natOnly _ nodeFullR_natOnly) ex'
  exact ⟨d', t₁ + k', j, .seq e₁ ex', by clear * - ht₁ hk'; omega, hj,
    by rw [KR _ (by omega) (by omega), s24], hK.lp, by rw [KR _ (by omega) (by omega), s26],
    by rw [KR _ (by omega) (by omega), s54], by rw [KR _ (by omega) (by omega), s31],
    by rw [KR _ (by omega) (by omega), s53], by rw [KR _ (by omega) (by omega), s52],
    by rw [KR _ (by omega) (by omega), s37], by rw [KR _ (by omega) (by omega), s38],
    by rw [KR _ (by omega) (by omega), s36], by rw [KR _ (by omega) (by omega), s51],
    by rw [KR _ (by omega) (by omega), s57], by rw [KR _ (by omega) (by omega), s34],
    by rw [KR _ (by omega) (by omega), s33], by rw [KR _ (by omega) (by omega), s56],
    fun r hr => by rw [KR r (by omega) (by omega), hkR r (by omega)], hK.logle,
    fun a ha hn => by rw [hK.dirty a ha hn, hm₁'],
    fun a h1 h2 => by rw [hK.nmem a h1 (Or.inl h2), hm₁'], hwN, by rw [hrr', hr₁],
    by rw [hrm', hrm₁], by rw [hout', ho₁], hres'⟩

set_option maxHeartbeats 8000000 in
/-- **The outcome after the node** (the second half of `fs_node`): from the configuration
`d'` after the node (`fs_run`), `fbOut WN` ends with a `PotOut` outcome of the piece in the
frame, the logged cells and the node's arrays zero, every other cell up to `WN` and between
`WN` and the frame, and between the frame and the heap top, kept. -/
theorem fs_out {ℓ : D → ℤ} {L n : ℕ} {Q : Finset D} {g : Frame.GIds D V}
    {df de h k m w WN W' Z M₀ M H E j R : ℕ} {ν : V → ℕ} {ι : ℕ → V} (I : Input)
    (d' : Config) (hd : WordsBounded W d') (hinP : Frame.InP g N ℓ L n Q df de d')
    (r24 : d'.nreg 2924 = h + 200 * k) (r25 : d'.nreg 2925 = h + 200 * k + j)
    (r26 : d'.nreg 2926 = 1) (r54 : d'.nreg 2954 = E - Z) (r31 : d'.nreg 2931 = Z)
    (r53 : d'.nreg 2953 = 3 * M₀) (r52 : d'.nreg 2952 = W' + Z + 3 * M₀ + 1)
    (r37 : d'.nreg 2937 = m) (r38 : d'.nreg 2938 = k) (r36 : d'.nreg 2936 = w)
    (r51 : d'.nreg 2951 = W' + Z + 20 * M₀ + 1) (r57 : d'.nreg 2957 = h + 8 * k)
    (r34 : d'.nreg 2934 = M) (r33 : d'.nreg 2933 = H) (r56 : d'.nreg 2956 = 0)
    (r03 : d'.nreg 3003 = h) (r04 : d'.nreg 3004 = df)
    (hlog : ∀ i < j, d'.nmem (h + 200 * k + i) ≤ WN) (hwN : ∀ a ≤ WN, d'.nmem a ≤ WN)
    (hres' : (PotOut (pg N Q ℓ) none ∧ d'.nreg 990 ≠ 0) ∨
      (∃ f, (pg N Q ℓ).IsPot f ∧ d'.nreg 990 = 0 ∧
        ∀ x ∈ verts N Q, (f x : ℝ) = sgnD H M (d'.nmem (W' + 1 + (Z + 20 * M₀ + ν x)))))
    (hm : m = Q.card) (hk : k = Frame.ck N Q)
    (hν : ∀ x ∈ verts N Q, ν x < w ∧ ι (ν x) = x)
    (hι : ∀ v < w, ι v ∈ verts N Q ∧ ν (ι v) = v) (hw2 : w ≤ 2 * m)
    (hT : ∀ a < m, d'.nmem (h + a) = ν (N.tail (Frame.cδ g N Q a)))
    (hH : ∀ a < m, d'.nmem (h + k + a) = ν (N.head (Frame.cδ g N Q a)))
    (hI : ∀ v < w, d'.nmem (h + 2 * k + v) = g.gv (ι v))
    (hM : M = 2 * H + 1) (hHW : H ≤ WN)
    (hℓL : ∀ x ∈ Q, |ℓ x| ≤ L) (hsL : ∑ x ∈ Q, |ℓ x| ≤ L)
    (hWdf : WN < df) (hdeh : de ≤ h) (hEZ : Z ≤ E) (hEW : E ≤ WN)
    (hRW : W' + Z + 21 * M₀ + 1 ≤ WN) (hM₀ : w ≤ M₀) (hjR : j ≤ R)
    (hroom : h + 10 * k + 5 * (m + w) + 8 * (w + 1) + 1 ≤ W)
    (hW4 : 4 * WN + 3 * L + 2 ≤ W) (h10 : 10 ≤ W) :
    ∃ c' t o, Exec I W (fbOut WN) d' c' t ∧ t ≤ 2 + fbYesCost R (E - Z) (3 * M₀) m w ∧
      PotOut (pg N Q ℓ) o ∧ Frame.Res g N L Q o df de c' ∧
      (∀ a ≤ WN, ((∃ i < j, d'.nmem (h + 200 * k + i) = a) ∨ (Z ≤ a ∧ a < E) ∨
        (W' + Z + 3 * M₀ + 1 ≤ a ∧ a < W' + Z + 3 * M₀ + 1 + 3 * M₀)) → c'.nmem a = 0) ∧
      (∀ a ≤ WN, (∀ i < j, d'.nmem (h + 200 * k + i) ≠ a) → (a < Z ∨ E ≤ a) →
        (a < W' + Z + 3 * M₀ + 1 ∨ W' + Z + 3 * M₀ + 1 + 3 * M₀ ≤ a) → c'.nmem a = d'.nmem a) ∧
      (∀ a, WN < a → a < df → c'.nmem a = d'.nmem a) ∧
      (∀ a, de ≤ a → a < h → c'.nmem a = d'.nmem a) ∧
      (∀ r, 3000 ≤ r → c'.nreg r = d'.nreg r) ∧ c'.rreg = d'.rreg ∧ c'.rmem = d'.rmem ∧
      c'.output = d'.output := by
  have hen := hinP.en
  unfold Frame.fsz at hen
  have hmk : m ≤ k := by rw [hm, hk]; exact Frame.ck_ge _
  have hpW : WN < h + 200 * k := by clear * - hWdf hdeh hen; omega
  have hcl : fbClrCost j (E - Z) (3 * M₀) ≤ fbClrCost R (E - Z) (3 * M₀) := by
    unfold fbClrCost; omega
  by_cases hf : d'.nreg 2956 < d'.nreg 990
  · -- no feasible potential
    have hnone : PotOut (pg N Q ℓ) none := by
      rcases hres' with ⟨h1, -⟩ | ⟨f, -, h2, -⟩
      · exact h1
      · rw [h2] at hf; omega
    obtain ⟨c₃, t₃, e₃, ht₃, f1, z₃, y₃, x₃, k₃, n₃, rr₃, rm₃, o₃⟩ := fbNo_exec (P := I) d' hd
      r24 r25 r26 hlog hpW r54 r31 r53 r52 hEZ (by omega) (by omega) (by omega) r37 r38 r04
      (by omega)
    have hfl : df + 5 * k + m + 4 = df + Frame.fin Q.card (Frame.ck N Q) := by
      unfold Frame.fin; rw [← hm, ← hk]; omega
    refine ⟨c₃, t₃ + 1, none, .ifLtN_true hf e₃, ?_, hnone,
      ⟨hen.symm ▸ (by unfold Frame.fsz; omega), ?_⟩, fun a ha h => ?_,
      fun a ha h1 h2 h3 => k₃ a (by omega) h1 h2 h3,
      fun a h1 h2 => k₃ a (by omega) (fun i hi => by have := hlog i hi; omega) (by omega)
        (by omega),
      fun a h1 h2 => k₃ a (by omega) (fun i hi => by have := hlog i hi; omega) (by omega)
        (by omega),
      fun r hr => n₃ r (by omega), rr₃, rm₃, o₃⟩
    · unfold fbYesCost; omega
    · show c₃.nmem (df + Frame.fin Q.card (Frame.ck N Q)) ≠ 0
      rw [← hfl, f1]; omega
    · have hne : a ≠ df + 5 * k + m + 4 := by omega
      rcases h with h | h | h
      · exact z₃ a hne h
      · exact y₃ a hne h.1 h.2
      · exact x₃ a hne h.1 h.2
  · -- a feasible potential
    have h990 : d'.nreg 990 = 0 := by rw [r56] at hf; omega
    obtain ⟨f, hpf, -, hfv⟩ : ∃ f, (pg N Q ℓ).IsPot f ∧ d'.nreg 990 = 0 ∧
        ∀ x ∈ verts N Q, (f x : ℝ) = sgnD H M (d'.nmem (W' + 1 + (Z + 20 * M₀ + ν x))) := by
      rcases hres' with ⟨-, h2⟩ | h
      · exact absurd h990 h2
      · exact h
    obtain ⟨c₃, t₃, g', e₃, ht₃, hpo, hres3, z₃, y₃, x₃, k₃, k₃', n₃, rr₃, rm₃, o₃⟩ :=
      fbYes_exec (P := I) (g := g) (ν := ν) (ι := ι) d' hd hinP hpf r24 r25 r26 hlog hpW r54
        r31 r53 r52 hEZ r36 r51 r57 r34 r33 r38 r03 r04 hν hι (by rw [← hm]; exact hw2)
        (fun a ha => hT a (by rw [hm]; exact ha)) (fun a ha => hH a (by rw [hm]; exact ha)) hI
        (fun v hv => by
          have hx := (hι v hv).1
          have e1 : W' + Z + 20 * M₀ + 1 + v = W' + 1 + (Z + 20 * M₀ + ν (ι v)) := by
            rw [(hι v hv).2]; omega
          rw [e1]
          exact ⟨hfv _ hx, hwN _ (by have := (hν _ hx).1; omega)⟩)
        hM hHW hℓL hsL (by rw [← hm]; exact hmk) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hdeh (by rw [← hm]; omega) hW4 h10
    refine ⟨c₃, t₃ + 2, some g', .ifLtN_false hf e₃, ?_, hpo, hres3, fun a ha h => ?_,
      fun a ha h1 h2 h3 => k₃ a (by omega) h1 h2 h3,
      fun a h1 h2 => k₃ a (by omega) (fun i hi => by have := hlog i hi; omega) (by omega)
        (by omega),
      fun a h1 h2 => k₃' a (by omega) h2, n₃, rr₃, rm₃, o₃⟩
    · rw [← hm] at ht₃; unfold fbYesCost at ht₃ ⊢; omega
    · rcases h with h | h | h
      · exact z₃ a (by omega) h
      · exact y₃ a (by omega) h.1 h.2
      · exact x₃ a (by omega) h.1 h.2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
open Classical in
/-- **The node from its prepared data** (see the module docstring). -/
theorem fs_node (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {P₀ P₁ : Finset D} (hS : SplitF N (P₀ ∪ P₁) P₀ P₁) (hB : (bdry N P₀ P₁).Nonempty) (ℓ : D → ℤ)
    (δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    (fd₀ : FaceData N P₀ (bdry N P₀ P₁)) (hq₀ : fd₀.q ≤ 18 * (P₀ ∪ P₁).card)
    (hk₀ : fd₀.k ^ 2 ≤ 1200 * (P₀ ∪ P₁).card)
    (fd₁ : FaceData N P₁ (bdry N P₀ P₁)) (hq₁ : fd₁.q ≤ 18 * (P₀ ∪ P₁).card)
    (hk₁ : fd₁.k ^ 2 ≤ 1200 * (P₀ ∪ P₁).card)
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
    {g : Frame.GIds D V} {L n k h df de : ℕ}
    (c : Config) (hc : WordsBounded W c) (hWNW : WN ≤ W)
    (hinP : Frame.InP g N ℓ L n (P₀ ∪ P₁) df de c)
    (hm : m = (P₀ ∪ P₁).card) (hk : k = Frame.ck N (P₀ ∪ P₁))
    (r1022 : c.nreg 1022 = W') (r2313 : c.nreg 2313 = Z) (r2314 : c.nreg 2314 = M₀)
    (r1024 : c.nreg 1024 = nodeHN m b w B) (r1023 : c.nreg 1023 = M)
    (r2321 : c.nreg 2321 = p₁.END)
    (r2464 : c.nreg 2464 = w) (r2474 : c.nreg 2474 = m) (r2475 : c.nreg 2475 = k)
    (r2496 : c.nreg 2496 = b) (r2205 : c.nreg 2205 = B) (r2315 : c.nreg 2315 = Y)
    (r2316 : c.nreg 2316 = S)
    (e40 : c.nreg 2240 = p₀.nD) (e43 : c.nreg 2243 = p₀.k) (e41 : c.nreg 2241 = p₀.nV)
    (e00 : c.nreg 2300 = p₀.nF) (f44 : c.nreg 2244 = p₁.nD) (f47 : c.nreg 2247 = p₁.k)
    (f45 : c.nreg 2245 = p₁.nV) (f01 : c.nreg 2301 = p₁.nF) (r3003 : c.nreg 3003 = h)
    (r3004 : c.nreg 3004 = df)
    (hdm : ∀ a ≤ WN, c.nmem a ≤ WN)
    -- the node's data on `c`
    (hmW : ∀ a ≤ W', c.nmem a ≤ W') (h9600 : 9600 ≤ WN)
    (hTm : ∀ i < m, c.nmem (Z + 0 * M₀ + i) = encT N e ν i)
    (hHm : ∀ i < m, c.nmem (Z + 1 * M₀ + i) = encH N e ν i)
    (hSm : ∀ i < m, c.nmem (Z + 2 * M₀ + i) = encS P₀ e i)
    (hz : ∀ a < Z, c.nmem a = 0)
    (hres : ∀ a ≤ W', c.nmem (W' + 1 + a) < M ∧
      (c.nmem (W' + 1 + a) ≤ B ∨ M ≤ c.nmem (W' + 1 + a) + B))
    (hLm : ∀ i < m, (c.nmem (W' + 1 + (Z + 3 * M₀ + i)) : ℤ) = ℓ (e i) % M ∧ |ℓ (e i)| ≤ B)
    (hD₀ : ∀ v < w, (c.nmem (W' + 1 + (Z + 4 * M₀ + v)) : ℤ) = δ₀ (ι v) % M ∧ |δ₀ (ι v)| ≤ B)
    (hD₁ : ∀ v < w, (c.nmem (W' + 1 + (Z + 5 * M₀ + v)) : ℤ) = δ₁ (ι v) % M ∧ |δ₁ (ι v)| ≤ B)
    (hpos₀ : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₀ + ν x) < fd₀.k ∧
      fd₀.Q.tail (fd₀.g (c.nmem (Pb₀ + ν x))) = fd₀.j x)
    (hpos₁ : ∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₁ + ν x) < fd₁.k ∧
      fd₁.Q.tail (fd₁.g (c.nmem (Pb₁ + ν x))) = fd₁.j x)
    (hQRV₀ : ∀ x, c.nmem (p₀.I0 + σ₀ x) = σ₀ (fd₀.Q.rev x))
    (hQNT₀ : ∀ x, c.nmem (p₀.I0 + p₀.nD + σ₀ x) = νv₀ (fd₀.Q.tail x))
    (hQNF₀ : ∀ x, c.nmem (p₀.I0 + 2 * p₀.nD + σ₀ x) = τ₀ (fd₀.Q.face x))
    (hQIS₀ : ∀ x, c.nmem (p₀.I0 + 3 * p₀.nD + σ₀ x) = if x ∈ fd₀.P'.image fd₀.e then 1 else 0)
    (hQLN₀ : ∀ x, c.nmem (p₀.I0 + 4 * p₀.nD + σ₀ x) =
      (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀) x).toNat)
    (hQG₀ : ∀ i < fd₀.k, c.nmem (p₀.I0 + 5 * p₀.nD + i) = σ₀ (fd₀.g i))
    (hQRV₁ : ∀ x, c.nmem (p₁.I0 + σ₁ x) = σ₁ (fd₁.Q.rev x))
    (hQNT₁ : ∀ x, c.nmem (p₁.I0 + p₁.nD + σ₁ x) = νv₁ (fd₁.Q.tail x))
    (hQNF₁ : ∀ x, c.nmem (p₁.I0 + 2 * p₁.nD + σ₁ x) = τ₁ (fd₁.Q.face x))
    (hQIS₁ : ∀ x, c.nmem (p₁.I0 + 3 * p₁.nD + σ₁ x) = if x ∈ fd₁.P'.image fd₁.e then 1 else 0)
    (hQLN₁ : ∀ x, c.nmem (p₁.I0 + 4 * p₁.nD + σ₁ x) =
      (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁) x).toNat)
    (hQG₁ : ∀ i < fd₁.k, c.nmem (p₁.I0 + 5 * p₁.nD + i) = σ₁ (fd₁.g i))
    (hBN : hnB p₀ p₁ Pb₀ Pb₁ W' M (nodeHN m b w B)
      (Klein.srcN1 fd₀.VQ fd₀.FQ fd₀.DQ fd₀.k) (Klein.srcN1 fd₁.VQ fd₁.FQ fd₁.DQ fd₁.k)
      (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))).toNat
      (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))).toNat ≤ WN)
    -- the outcome
    (hT : ∀ a < m, c.nmem (h + a) = ν (N.tail (Frame.cδ g N (P₀ ∪ P₁) a)))
    (hH : ∀ a < m, c.nmem (h + k + a) = ν (N.head (Frame.cδ g N (P₀ ∪ P₁) a)))
    (hI : ∀ v < w, c.nmem (h + 2 * k + v) = g.gv (ι v))
    (hι : ∀ v < w, ι v ∈ verts N (P₀ ∪ P₁) ∧ ν (ι v) = v)
    (hℓL : ∀ x ∈ P₀ ∪ P₁, |ℓ x| ≤ L) (hsL : ∑ x ∈ P₀ ∪ P₁, |ℓ x| ≤ L)
    -- the layout
    (hzc : ∀ a ≤ WN, (a < Z ∨ p₁.END ≤ a) →
      (a < W' + Z + 3 * M₀ + 1 ∨ W' + Z + 6 * M₀ + 1 ≤ a) → c.nmem a = 0)
    (hWdf : WN < df) (hdeh : de ≤ h)
    (hRW : h + 200 * k + ndRunCost C (P₀ ∪ P₁).card m w b fd₀.k fd₁.k p₀ p₁ ≤ W)
    (hroom : h + 10 * k + 5 * (m + w) + 8 * (w + 1) + 1 ≤ W)
    (hW4 : 4 * WN + 3 * L + 2 ≤ W) (hW96 : 9600 ≤ W) :
    ∃ c' t o, Exec I W (fbTail WN) c c' t ∧
      t ≤ fsNodeCost (ndRunCost C (P₀ ∪ P₁).card m w b fd₀.k fd₁.k p₀ p₁) p₁.END Z M₀ m w ∧
      PotOut (pg N (P₀ ∪ P₁) ℓ) o ∧ Frame.Res g N L (P₀ ∪ P₁) o df de c' ∧
      (∀ a ≤ WN, c'.nmem a = 0) ∧ (∀ a, WN < a → a < df → c'.nmem a = c.nmem a) ∧
      (∀ a, de ≤ a → a < h → c'.nmem a = c.nmem a) ∧
      (∀ r, 3000 ≤ r → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  classical
  obtain ⟨A1, A2, A3, A4, A5, A6, A7, A8, -⟩ :=
    fs_arith (B := B) hW' hWN.1 hMd hY hI0₀ hI0₁ hZ hSz.2.1 hM₀
  have hen := hinP.en
  unfold Frame.fsz at hen
  obtain ⟨d', t₁, j, e₁, ht₁, hj, s24, s25, s26, s54, s31, s53, s52, s37, s38, s36, s51, s57,
    s34, s33, s56, R3, hlog, hdirty, hkeep, hwN, hrr, hrm, ho, hres'⟩ :=
    fs_run C hfr hmssp hS hB ℓ δ₀ δ₁ hδ₀ hδ₁ fd₀ hq₀ hk₀ fd₁ hq₁ hk₁ σ₀ νv₀ τ₀ σ₁ νv₁ τ₁ p₀ p₁
      hpD₀ hpk₀ hpV₀ hpF₀ hpD₁ hpk₁ hpV₁ hpF₁ hN hb Pb₀ Pb₁ Z M₀ Y S W' B M WN I hM₀ hZ hbZ hK₀
      hK₁ hkk₀ hkk₁ hY hSz hPb₀ hPb₁ hI0₀ hI0₁ hL₀ hL₁ hW' hWN hMd c hc hWNW hinP hm hk r1022
      r2313 r2314 r1024 r1023 r2321 r2464 r2474 r2475 r2496 r2205 r2315 r2316 e40 e43 e41 e00
      f44 f47 f45 f01 r3003 r3004 hdm hmW h9600 hTm hHm hSm hz hres hLm hD₀ hD₁ hpos₀ hpos₁
      hQRV₀ hQNT₀ hQNF₀ hQIS₀ hQLN₀ hQG₀ hQRV₁ hQNT₁ hQNF₁ hQIS₁ hQLN₁ hQG₁ hBN hWdf hdeh hRW
      hW96
  have hmk : m ≤ k := by rw [hm, hk]; exact Frame.ck_ge _
  have K : ∀ a, WN < a → a < h + 200 * k → d'.nmem a = c.nmem a := hkeep
  have hinP' : Frame.InP g N ℓ L n (P₀ ∪ P₁) df de d' := Frame.inP_stab hinP fun a h1 h2 =>
    ⟨K a (by omega) (by omega), by rw [hrm]⟩
  have hw2 := hN.w2
  obtain ⟨c', t₂, o, e₂, ht₂, hpo, hres, Z1, Z2, Z3, Z4, R4, rr₂, rm₂, o₂⟩ :=
    fs_out (R := ndRunCost C (P₀ ∪ P₁).card m w b fd₀.k fd₁.k p₀ p₁) (E := p₁.END)
      (ν := ν) (ι := ι) I d' e₁.wb_right hinP' s24 s25 s26 s54 s31 s53 s52 s37 s38 s36 s51 s57
      s34 s33 s56 (by rw [R3 _ (by omega), r3003]) (by rw [R3 _ (by omega), r3004]) hlog hwN
      hres' hm hk (fun x hx => ⟨hN.lt x hx, hN.inv x hx⟩) hι hw2
      (fun a ha => by rw [K _ (by omega) (by omega)]; exact hT a ha)
      (fun a ha => by rw [K _ (by omega) (by omega)]; exact hH a ha)
      (fun v hv => by rw [K _ (by omega) (by omega)]; exact hI v hv) hMd
      (by clear * - A2 A3 hMd; omega) hℓL hsL hWdf hdeh (by
        have e0 := pn_end p₀; have e1 := pn_end p₁; clear * - hY A4 A5 hI0₀ hI0₁ A1 e0 e1; omega)
      (by clear * - A1 A3; omega) (by clear * - A3 A4; omega)
      (by clear * - A8; omega) hj (by clear * - hroom; omega) hW4 (by omega)
  have E : Exec I W (fbTail WN) c c' (t₁ + t₂) := by
    cases e₁ with
    | seq e₁ e₂' => exact (Exec.seq e₁ (Exec.seq e₂' e₂)).cast (by omega)
  refine ⟨c', t₁ + t₂, o, E, ?_, hpo, hres, fun a ha => ?_,
    fun a h1 h2 => by rw [Z3 a h1 h2, K a h1 (by omega)],
    fun a h1 h2 => by rw [Z4 a h1 h2, K a (by omega) (by omega)],
    fun r hr => by rw [R4 r hr, R3 r hr], by rw [rr₂, hrr], by rw [rm₂, hrm], by rw [o₂, ho]⟩
  · unfold fsNodeCost; omega
  · by_cases hl : (∃ i < j, d'.nmem (h + 200 * k + i) = a) ∨ (Z ≤ a ∧ a < p₁.END) ∨
        (W' + Z + 3 * M₀ + 1 ≤ a ∧ a < W' + Z + 3 * M₀ + 1 + 3 * M₀)
    · exact Z1 a ha hl
    · push_neg at hl
      obtain ⟨h1, h2, h3⟩ := hl
      rw [Z2 a ha h1 (by omega) (by omega), hdirty a ha h1]
      exact hzc a ha (by omega) (by omega)

end NegSSSP

end PlanarFlow
