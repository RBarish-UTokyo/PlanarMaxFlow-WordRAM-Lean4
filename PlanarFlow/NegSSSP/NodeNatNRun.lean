module

public import PlanarFlow.NegSSSP.NodeNatN

/-!
# The whole node on natural words: the run

`node_exec_natN`: the node of the negative-length recursion as **one run of a natural-word
program** (`nodeProgNN`, no real instruction), with no hypothesis on Klein's part: from the
natural configuration `natOf 1000 W' M (W' + 1) c` simulating an integer real configuration `c`
holding the node's inputs (as `node_exec`, with the real memory and registers bounded by `B`)
and the encodings of the two one-face instances **for their isolating lengths** in natural slots
(`KSlotN`, residues modulo `2 Hc + 1`), with one modulus `M > 2 nodeHN m b w B`, the program
runs within `4 (8 + 61 m + 12) + 3` (the glue) `+ partNCost₀ + partNCost₁ + 14` (the two parts)
`+ 4 ·` (the bound of `rest_exec`) steps with words at most `WN`, and its outcome is that of
`NegSSSP.step`: `r990 ≠ 0` when `step` fails, otherwise `r990 = 0` and the value `f x` of every
vertex read back from its residue at `W' + 1 + Z + 20 M₀ + ν x` (`sgnD`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge Monge.FR
  CmpAbs ModNat

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
/-- **The whole node on natural words** (see the module docstring). -/
theorem node_exec_natN (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {P P₀ P₁ : Finset D} (hS : SplitF N P P₀ P₁) (hB : (bdry N P₀ P₁).Nonempty) (ℓ : D → ℤ)
    (δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁)
    (fd₀ : FaceData N P₀ (bdry N P₀ P₁)) (hq₀ : fd₀.q ≤ 18 * P.card)
    (hk₀ : fd₀.k ^ 2 ≤ 1200 * P.card)
    (fd₁ : FaceData N P₁ (bdry N P₀ P₁)) (hq₁ : fd₁.q ≤ 18 * P.card)
    (hk₁ : fd₁.k ^ 2 ≤ 1200 * P.card)
    {n₀ Bw₀ : ℕ} {σ₀ : Klein.SrcD fd₀.DQ fd₀.k ≃ Fin (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k))}
    {wt₀ : Klein.SrcD fd₀.DQ fd₀.k → ℤ} {Pk₀ : Input}
    (hv₀ : FEncNat fd₀ (redLen N ℓ δ₀) n₀ Bw₀ σ₀ wt₀ Pk₀) {Hc₀ : ℕ}
    (hH₀ : fdHI fd₀ (redLen N ℓ δ₀) σ₀ wt₀ ≤ Hc₀)
    {n₁ Bw₁ : ℕ} {σ₁ : Klein.SrcD fd₁.DQ fd₁.k ≃ Fin (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k))}
    {wt₁ : Klein.SrcD fd₁.DQ fd₁.k → ℤ} {Pk₁ : Input}
    (hv₁ : FEncNat fd₁ (redLen N ℓ δ₁) n₁ Bw₁ σ₁ wt₁ Pk₁) {Hc₁ : ℕ}
    (hH₁ : fdHI fd₁ (redLen N ℓ δ₁) σ₁ wt₁ ≤ Hc₁)
    {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V} (hN : NodeEnc N P₀ P₁ m w e ν ι)
    (hb : b = (bdry N P₀ P₁).card)
    (Pb₀ Pb₁ β₀ β₁ Rk₀ Rk₁ Z M₀ Y S W' B M WN : ℕ) (I : Input) (c : Config)
    (hM₀ : M₀ = m + w + 1) (hZ : loB m w ≤ Z) (hbZ : bfWP b < Z)
    (hK₀ : 2 * (Bw₀ + 16 * (n₀ + 1)) + 1 < Z) (hK₁ : 2 * (Bw₁ + 16 * (n₁ + 1)) + 1 < Z)
    (hkk₀ : n₀ + fd₀.k * fd₀.k ≤ Z) (hkk₁ : n₁ + fd₁.k * fd₁.k ≤ Z)
    (hY : Z + 22 * M₀ ≤ Y)
    (hSz : w ≤ S ∧ b * b ≤ S ∧ fd₀.k ≤ S ∧ fd₁.k ≤ S)
    (hIn : Y + 16 * S ≤ Pb₀ ∧ Y + 16 * S ≤ Pb₁ ∧ Y + 16 * S ≤ β₀ ∧ Y + 16 * S ≤ β₁ ∧
      Y + 16 * S ≤ Rk₀ ∧ Y + 16 * S ≤ Rk₁)
    (hW : Y + 16 * S ≤ W' ∧ Pb₀ + w ≤ W' ∧ Pb₁ + w ≤ W' ∧
      Rk₀ + (3 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 3) ≤ W' ∧
      Rk₁ + (3 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 3) ≤ W' ∧
      β₀ + (Bw₀ + 16 * (n₀ + 1)) ≤ W' ∧ β₁ + (Bw₁ + 16 * (n₁ + 1)) ≤ W')
    (hWN : 2 * W' + 1 + M * M + M ≤ WN ∧
      2 * W' + 2 + (2 * (Bw₀ + 16 * (n₀ + 1)) + 1) + (2 * Hc₀ + 1) * (2 * Hc₀ + 1) +
        (2 * Hc₀ + 1) ≤ WN ∧
      2 * W' + 2 + (2 * (Bw₁ + 16 * (n₁ + 1)) + 1) + (2 * Hc₁ + 1) * (2 * Hc₁ + 1) +
        (2 * Hc₁ + 1) ≤ WN ∧
      2 * Hc₀ + 1 + 2 * M ≤ WN ∧ 2 * Hc₁ + 1 + 2 * M ≤ WN ∧
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
    (hE₀ : KSlotN (Klein.srcMap fd₀.inst.cycle) fd₀.k (Klein.srcG fd₀.inst.cycle)
      (Klein.srcPiece fd₀.k (fd₀.P'.image fd₀.e))
      (Klein.srcIso (V := fd₀.VQ) (F := fd₀.FQ) fd₀.k (fd₀.P'.image fd₀.e)
        (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀)) wt₀ σ₀) σ₀ Bw₀ n₀ β₀ Rk₀ (2 * Hc₀ + 1) Pk₀ c)
    (hE₁ : KSlotN (Klein.srcMap fd₁.inst.cycle) fd₁.k (Klein.srcG fd₁.inst.cycle)
      (Klein.srcPiece fd₁.k (fd₁.P'.image fd₁.e))
      (Klein.srcIso (V := fd₁.VQ) (F := fd₁.FQ) fd₁.k (fd₁.P'.image fd₁.e)
        (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁)) wt₁ σ₁) σ₁ Bw₁ n₁ β₁ Rk₁ (2 * Hc₁ + 1) Pk₁ c)
    (hI : NInv W' B c) (hZi : IntAll c) :
    ∃ d' t', ∃ o : Option (V → ℤ),
      Exec I WN (nodeProgNN
        (kpnOf fd₀ (redLen N ℓ δ₀) n₀ Bw₀ Pk₀ β₀ Rk₀ Pb₀ Hc₀ (2 * W' + 2) (W' + 1) M)
        (kpnOf fd₁ (redLen N ℓ δ₁) n₁ Bw₁ Pk₁ β₁ Rk₁ Pb₁ Hc₁ (2 * W' + 2) (W' + 1) M) M
        (nodeHN m b w B) (W' + 1)) (natOf 1000 W' M (W' + 1) c) d' t' ∧
      t' ≤ 4 * (8 + (61 * m + 12)) + 3 +
        (partNCost P.card fd₀.k b (Bw₀ + 16 * (n₀ + 1)) (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k)) +
          partNCost P.card fd₁.k b (Bw₁ + 16 * (n₁ + 1)) (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k)) +
          14) +
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
  obtain ⟨hSw, hSb, hSk₀, hSk₁⟩ := hSz
  obtain ⟨hI₁, hI₂, hI₃, hI₄, hI₅, hI₆⟩ := hIn
  obtain ⟨hW₁, hW₂, hW₃, hW₄, hW₅, hW₆, hW₇⟩ := hW
  obtain ⟨hWN₁, hWN₂, hWN₃, hWN₄, hWN₅, hWN₆, hWN₇, hWN₈, hWN₉⟩ := hWN
  set H := nodeHN m b w B with hHd
  set BK := (3 * m + 2) * B with hBK
  have hbw : b ≤ w := hb ▸ card_bdry_le hN
  have hm2 := hN.w2
  have hA : loB m w = 4 * m + 18 * w + 175 := rfl
  have hP₀ : P₀.Nonempty := card_pos.1 hS.2.2.1
  have hP₁ : P₁.Nonempty := card_pos.1 hS.2.2.2.1
  have hb1 : 1 ≤ b := by rw [hb]; exact card_pos.2 hB
  have hnn₀ := redLen_nonneg hδ₀
  have hnn₁ := redLen_nonneg hδ₁
  have hBH : B ≤ H := by rw [hHd]; unfold nodeHN; omega
  have hBKH : BK ≤ restB b w BK ∧ restB b w BK ≤ H := by
    refine ⟨(le_restB (w := w) hb1).1.trans (le_restB (w := w) hb1).2, ?_⟩
    rw [hHd]; unfold nodeHN; rw [← hBK]; omega
  have hM0 : 0 < M := by omega
  have hx' := hx.reg
  -- 0. the natural configuration
  have hS₀ : Sim 1000 W' M (W' + 1) c (natOf 1000 W' M (W' + 1) c) :=
    sim_natOf (by omega) hM0 (fun r _ => hZi.1 r) (fun a _ => hZi.2 a)
  have hd₀ : WordsBounded WN (natOf 1000 W' M (W' + 1) c) :=
    natOf_wb hc (by omega) (by have := Nat.le_mul_self M; omega) hM0
  -- 1. the glue before Klein's part, real, then simulated
  obtain ⟨c₁, k₁, e₁, hq₁k, g10, g200, g201, g202, g206, g207, g208, g209, gn₁, gnm₁, grm₁,
    go₁⟩ := bdSet_exec (I := I) c hc (by pomega)
  have hBL : BdLay m w (Z + 0 * M₀) (Z + 1 * M₀) (Z + 2 * M₀) Y (Y + 2 * S) W' (encT N e ν)
      (encH N e ν) (encS P₀ e) :=
    ⟨enc_ends hN, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega,
      by pomega, by pomega, by pomega, by pomega, by pomega, by pomega, by pomega⟩
  have hBI : BdIn m w (Z + 0 * M₀) (Z + 1 * M₀) (Z + 2 * M₀) Y (Y + 2 * S) (encT N e ν)
      (encH N e ν) (encS P₀ e) c₁ :=
    ⟨g10, by rw [g200, hctx.r800], by rw [g201, hctx.slot 0 (by omega)],
      by rw [g202, hctx.slot 1 (by omega)], by rw [g206, hctx.slot 2 (by omega)],
      by rw [g207, hctx.r801], by rw [g208, hx' 0 (by omega), zero_mul, add_zero],
      by rw [g209, hx' 2 (by omega)], fun d hd => by rw [gnm₁]; exact hTm d hd,
      fun d hd => by rw [gnm₁]; exact hHm d hd, fun d hd => by rw [gnm₁]; exact hSm d hd⟩
  obtain ⟨c₂, k₂, src, e₂, hq₂k, hsrc, hsl, hm₂, hf₂⟩ :=
    bdryProg_node' (I := I) hN hBL c₁ e₁.wb_right hBI
  rw [← hb] at hsrc hsl
  have hR₂ : ∀ r, (800 ≤ r ∧ r < 900) ∨ 919 ≤ r → c₂.nreg r = c.nreg r := fun r hr => by
    rw [hf₂.nreg r (by pomega), gn₁ r (by pomega) (by pomega)]
  have hm₂' : ∀ a, (a < Y ∨ Y + 3 * S ≤ a) → c₂.nmem a = c.nmem a := fun a ha => by
    rw [hm₂ a (by pomega) (by pomega), gnm₁]
  have hrm₂ : c₂.rmem = c.rmem := by rw [hf₂.rmem, grm₁]
  obtain ⟨hC₁, hI₁'⟩ := glue_cmp bdSet_glueOK e₁ hI
  obtain ⟨hC₂, hI₂'⟩ := glue_cmp bdryProg_glueOK e₂ hI₁'
  have hZi₂ : IntAll c₂ := Exec.intAll (Exec.seq e₁ e₂) prefix_noDivR hZi
  obtain ⟨d₂, k₂', ex₂, hk₂', hS₂, hK₂, hfr₂, hfm₂, -, -⟩ :=
    ((ExecCmp.seq hC₁ hC₂).mono_H (show 2 * B ≤ H by rw [hHd]; unfold nodeHN; omega)).toNat_consts
      prefix_regsOK prefix_noDivR (M := M) hM (β := W' + 1) (W' := WN) (by omega) (by omega)
      (by omega) (by omega) hS₀ hd₀
  -- facts on the natural configuration after the glue
  have hd₂ : WordsBounded WN d₂ := ex₂.wb_right
  have hc₂ : WordsBounded W' c₂ := e₂.wb_right
  have hN₂ : ∀ r, ((800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r < 1000)) → d₂.nreg r = c.nreg r :=
    fun r hr => by rw [hS₂.nreg r (by omega), hR₂ r (by omega)]
  have hm₂N : ∀ a ≤ W', (a < Y ∨ Y + 3 * S ≤ a) → d₂.nmem a = c.nmem a := fun a h1 h2 => by
    rw [hS₂.nmem a h1, hm₂' a h2]
  have hx₂ : XCtx Y S d₂ := ⟨fun j hj => by rw [hN₂ _ (by omega)]; exact hx' j hj⟩
  have h802 : d₂.nreg 802 = b := by rw [hN₂ 802 (by omega), hctx.r802]
  have h807 : d₂.nreg 807 = Z + 4 * M₀ := by rw [hN₂ 807 (by omega), hctx.slot 4 (by omega)]
  have h808 : d₂.nreg 808 = Z + 5 * M₀ := by rw [hN₂ 808 (by omega), hctx.slot 5 (by omega)]
  have hsl₂ : ∀ i < b, d₂.nmem (Y + 2 * S + i) = ν (src i) := fun i hi => by
    rw [hS₂.nmem _ (by pomega)]; exact hsl i hi
  have hpos₀' : ∀ x ∈ bdry N P₀ P₁, d₂.nmem (Pb₀ + ν x) < fd₀.k ∧
      fd₀.Q.tail (fd₀.g (d₂.nmem (Pb₀ + ν x))) = fd₀.j x := fun x hx => by
    have := hN.lt _ (bdry_sub_verts hx)
    rw [hm₂N _ (by pomega) (by pomega)]; exact hpos₀ x hx
  have hpos₁' : ∀ x ∈ bdry N P₀ P₁, d₂.nmem (Pb₁ + ν x) < fd₁.k ∧
      fd₁.Q.tail (fd₁.g (d₂.nmem (Pb₁ + ν x))) = fd₁.j x := fun x hx => by
    have := hN.lt _ (bdry_sub_verts hx)
    rw [hm₂N _ (by pomega) (by pomega)]; exact hpos₁ x hx
  have hδ₀' : ∀ v < w, Res M (δ₀ (ι v) : ℝ) (d₂.nmem (W' + 1 + (Z + 4 * M₀) + v)) :=
    fun v hv => by
      have := hS₂.rmem (Z + 4 * M₀ + v) (by pomega)
      rw [hrm₂, hD₀ v hv, ← Nat.add_assoc] at this; exact this
  have hδ₁' : ∀ v < w, Res M (δ₁ (ι v) : ℝ) (d₂.nmem (W' + 1 + (Z + 5 * M₀) + v)) :=
    fun v hv => by
      have := hS₂.rmem (Z + 5 * M₀ + v) (by pomega)
      rw [hrm₂, hD₁ v hv, ← Nat.add_assoc] at this; exact this
  have hE₀' : KSlotN (Klein.srcMap fd₀.inst.cycle) fd₀.k (Klein.srcG fd₀.inst.cycle)
      (Klein.srcPiece fd₀.k (fd₀.P'.image fd₀.e))
      (Klein.srcIso (V := fd₀.VQ) (F := fd₀.FQ) fd₀.k (fd₀.P'.image fd₀.e)
        (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀)) wt₀ σ₀) σ₀ Bw₀ n₀ β₀ Rk₀ (2 * Hc₀ + 1) Pk₀ d₂ :=
    ⟨fun i hi => by rw [hm₂N _ (by pomega) (by pomega)]; exact hE₀.dat i hi,
      fun a ha => by rw [hm₂N _ (by pomega) (by pomega)]; exact hE₀.res a ha⟩
  have hE₁' : KSlotN (Klein.srcMap fd₁.inst.cycle) fd₁.k (Klein.srcG fd₁.inst.cycle)
      (Klein.srcPiece fd₁.k (fd₁.P'.image fd₁.e))
      (Klein.srcIso (V := fd₁.VQ) (F := fd₁.FQ) fd₁.k (fd₁.P'.image fd₁.e)
        (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁)) wt₁ σ₁) σ₁ Bw₁ n₁ β₁ Rk₁ (2 * Hc₁ + 1) Pk₁ d₂ :=
    ⟨fun i hi => by rw [hm₂N _ (by pomega) (by pomega)]; exact hE₁.dat i hi,
      fun a ha => by rw [hm₂N _ (by pomega) (by pomega)]; exact hE₁.res a ha⟩
  have hlow : ∀ a < Z, d₂.nmem a = 0 := fun a ha => by
    rw [hm₂N a (by pomega) (by pomega)]; exact hz a ha
  have hRW₂ : ∀ r < 752, d₂.nreg r ≤ W' := fun r hr => by
    rw [hS₂.nreg r (by omega)]; exact hc₂.1 r
  have hMW₂ : ∀ a ≤ W', d₂.nmem a ≤ W' := fun a ha => by
    rw [hS₂.nmem a ha]; exact hc₂.2 a
  have hKL₀ : ∀ z ≤ 1, KLayN b w fd₀.k (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k)) n₀
      (Bw₀ + 16 * (n₀ + 1)) (Y + 2 * S) Pb₀ (Z + 4 * M₀) (Y + (3 + 5 * z) * S) S β₀ Rk₀
      (2 * W' + 2) (W' + 1) W' :=
    fun z hz => klayN_of hz (by pomega) hSb hSk₀ hK₀ hkk₀ (by pomega) (by pomega) hI₁ hI₃ hI₅ hW₁
      hW₂ hW₄ hW₆ (by pomega) (by pomega)
  have hKL₁ : ∀ z ≤ 1, KLayN b w fd₁.k (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k)) n₁
      (Bw₁ + 16 * (n₁ + 1)) (Y + 2 * S) Pb₁ (Z + 5 * M₀) (Y + (3 + 5 * z) * S) S β₁ Rk₁
      (2 * W' + 2) (W' + 1) W' :=
    fun z hz => klayN_of hz (by pomega) hSb hSk₁ hK₁ hkk₁ (by pomega) (by pomega) hI₂ hI₄ hI₆ hW₁
      hW₃ hW₅ hW₇ (by pomega) (by pomega)
  have hr₀ : KPartRunN N P P₀ P₁ P₀ ℓ δ₀ mssp fd₀ n₀ Bw₀ σ₀ wt₀ Pk₀ Hc₀ :=
    kpartN_exec hnn₀ hmssp fd₀ hq₀ hk₀ hv₀ hH₀
  have hr₁ : KPartRunN N P P₀ P₁ P₁ ℓ δ₁ mssp fd₁ n₁ Bw₁ σ₁ wt₁ Pk₁ Hc₁ :=
    kpartN_exec hnn₁ hmssp fd₁ hq₁ hk₁ hv₁ hH₁
  have e4 : ∀ x, Y + (3 + 5 * 0) * S + S + x = Y + 4 * S + x := fun x => by ring
  have e6 : ∀ x, Y + (3 + 5 * 0) * S + 3 * S + x = Y + 6 * S + x := fun x => by ring
  have e9 : ∀ x, Y + (3 + 5 * 1) * S + S + x = Y + 9 * S + x := fun x => by ring
  have e11 : ∀ x, Y + (3 + 5 * 1) * S + 3 * S + x = Y + 11 * S + x := fun x => by ring
  set p₀ := kpnOf fd₀ (redLen N ℓ δ₀) n₀ Bw₀ Pk₀ β₀ Rk₀ Pb₀ Hc₀ (2 * W' + 2) (W' + 1) M with hp₀
  set p₁ := kpnOf fd₁ (redLen N ℓ δ₁) n₁ Bw₁ Pk₁ β₁ Rk₁ Pb₁ Hc₁ (2 * W' + 2) (W' + 1) M with hp₁
  -- 2. the two parts on natural words
  obtain ⟨d₃, k₃, γ₀, γ₁, e₃, hk₃, hen₀, hO₀, hcr₀, hF₀, hen₁, hO₁, hcr₁, hF₁, hn₃, hm₃, ho₃,
      hz₃, hRW₃, hR96₃, hMW₃⟩ : ∃ d₃ k₃, ∃ γ₀ γ₁ : ℕ → V,
      Exec I WN (if p₀.Kw ≤ p₁.Kw then kPairN 0 807 p₀ 1 808 p₁ else kPairN 1 808 p₁ 0 807 p₀)
        d₂ d₃ k₃ ∧
      k₃ ≤ partNCost P.card fd₀.k b (Bw₀ + 16 * (n₀ + 1)) (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k)) +
          partNCost P.card fd₁.k b (Bw₁ + 16 * (n₁ + 1)) (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k)) +
          14 ∧
      IsEnum b γ₀ (bdry N P₀ P₁) ∧ (∀ x < b, d₃.nmem (Y + 4 * S + x) = ν (γ₀ x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).len (γ₀ i)
        (γ₀ i')) ∧
      (∀ s < b, ∀ t < b,
        d₃.nmem (Y + 6 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) γ₀) s t ∧
          Res M (matOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) γ₀ s t : ℝ)
            (d₃.nmem (W' + 1 + (Y + 6 * S + (s * b + t))))) ∧
      IsEnum b γ₁ (bdry N P₀ P₁) ∧ (∀ x < b, d₃.nmem (Y + 9 * S + x) = ν (γ₁ x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)).len (γ₁ i)
        (γ₁ i')) ∧
      (∀ s < b, ∀ t < b,
        d₃.nmem (Y + 11 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) γ₁) s t ∧
          Res M (matOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) γ₁ s t : ℝ)
            (d₃.nmem (W' + 1 + (Y + 11 * S + (s * b + t))))) ∧
      (∀ r, (752 ≤ r ∧ r < 910) ∨ (919 ≤ r ∧ r < 960) ∨ 967 ≤ r → d₃.nreg r = d₂.nreg r) ∧
      (∀ a, Z ≤ a → a ≤ 2 * W' + 1 → (a < Y + 3 * S ∨ Y + 13 * S ≤ a) →
        (a < W' + 1 + (Y + 6 * S) ∨ W' + 1 + (Y + 6 * S) + b * b ≤ a) →
        (a < W' + 1 + (Y + 11 * S) ∨ W' + 1 + (Y + 11 * S) + b * b ≤ a) →
        d₃.nmem a = d₂.nmem a) ∧
      d₃.output = d₂.output ∧
      (∀ r, r < 408 ∨ (910 ≤ r ∧ r < 919) → d₃.nreg r = 0) ∧ (∀ r < 752, d₃.nreg r ≤ W') ∧
      (∀ r, 960 ≤ r → r < 967 → d₃.nreg r ≤ W') ∧ (∀ a ≤ W', d₃.nmem a ≤ W') := by
    by_cases hKK : Bw₀ + 16 * (n₀ + 1) ≤ Bw₁ + 16 * (n₁ + 1)
    · have hKK' : p₀.Kw ≤ p₁.Kw := hKK
      obtain ⟨d₃, k₃, γ₀, γ₁, e₃, hk₃, hen₀, hO₀, hcr₀, hF₀, hen₁, hO₁, hcr₁, hF₁, hn₃, hm₃,
        ho₃, hz₃, hRW₃, hR96₃, hMW₃⟩ := kpairN_exec hr₀ hr₁ hN hsrc (zf := 0) (zs := 1)
          (δrf := 807) (δrs := 808) (by omega) (by omega) (by omega) (by omega) (by omega)
          Pb₀ β₀ Rk₀ (Z + 4 * M₀) Pb₁ β₁ Rk₁ (Z + 5 * M₀) Y S (2 * W' + 2) (W' + 1) M W' WN I
          d₂ (hKL₀ 0 (by omega)) (hKL₁ 1 (by omega)) hWN₂ hWN₃ hM0 hWN₄ hWN₅ hWN₆ hWN₇ hWN₈ hWN₉
          hKK ⟨by pomega, by pomega, by pomega⟩ (by pomega) hd₂ h802 hx₂ h807 h808 hsl₂ hpos₀'
          hpos₁' hδ₀' hδ₁' hE₀' hE₁' (fun a ha => by rw [hlow a (by pomega)]; exact Nat.zero_le _)
          hRW₂ hMW₂
      refine ⟨d₃, k₃, γ₀, γ₁, by rw [ite_eq_left_of_eq_true _ _ (eq_true hKK')]; exact e₃, hk₃,
        hen₀, fun x hx => by rw [← e4]; exact hO₀ x hx, hcr₀,
        fun s hs t ht => by rw [← e6]; exact hF₀ s hs t ht, hen₁,
        fun x hx => by rw [← e9]; exact hO₁ x hx, hcr₁,
        fun s hs t ht => by rw [← e11]; exact hF₁ s hs t ht, hn₃,
        fun a h1 h2 h3 h4 h5 => hm₃ a (by pomega) h3 (by pomega) (by pomega) (by pomega), ho₃,
        hz₃, hRW₃, hR96₃, hMW₃⟩
    · have hKK' : ¬ p₀.Kw ≤ p₁.Kw := hKK
      obtain ⟨d₃, k₃, γ₁, γ₀, e₃, hk₃, hen₁, hO₁, hcr₁, hF₁, hen₀, hO₀, hcr₀, hF₀, hn₃, hm₃,
        ho₃, hz₃, hRW₃, hR96₃, hMW₃⟩ := kpairN_exec hr₁ hr₀ hN hsrc (zf := 1) (zs := 0)
          (δrf := 808) (δrs := 807) (by omega) (by omega) (by omega) (by omega) (by omega)
          Pb₁ β₁ Rk₁ (Z + 5 * M₀) Pb₀ β₀ Rk₀ (Z + 4 * M₀) Y S (2 * W' + 2) (W' + 1) M W' WN I
          d₂ (hKL₁ 1 (by omega)) (hKL₀ 0 (by omega)) hWN₃ hWN₂ hM0 hWN₅ hWN₄ hWN₇ hWN₆ hWN₉ hWN₈
          (by omega) ⟨by pomega, by pomega, by pomega⟩ (by pomega) hd₂ h802 hx₂ h808 h807 hsl₂
          hpos₁' hpos₀' hδ₁' hδ₀' hE₁' hE₀' (fun a ha => by rw [hlow a (by pomega)]; exact Nat.zero_le _)
          hRW₂ hMW₂
      refine ⟨d₃, k₃, γ₀, γ₁, by rw [ite_eq_right_of_eq_false _ _ (eq_false hKK')]; exact e₃,
        hk₃.trans (le_of_eq (by ring)),
        hen₀, fun x hx => by rw [← e4]; exact hO₀ x hx, hcr₀,
        fun s hs t ht => by rw [← e6]; exact hF₀ s hs t ht, hen₁,
        fun x hx => by rw [← e9]; exact hO₁ x hx, hcr₁,
        fun s hs t ht => by rw [← e11]; exact hF₁ s hs t ht, hn₃,
        fun a h1 h2 h3 h4 h5 => hm₃ a (by pomega) h3 (by pomega) (by pomega) (by pomega), ho₃,
        hz₃, hRW₃, hR96₃, hMW₃⟩
  -- 3. the real configuration read back after the parts
  have hrow : ∀ a ≤ W', (Y + 6 * S ≤ a ∧ a < Y + 6 * S + b * b) ∨
      (Y + 11 * S ≤ a ∧ a < Y + 11 * S + b * b) ∨
      d₃.nmem (W' + 1 + a) = d₂.nmem (W' + 1 + a) := fun a ha => by
    by_cases h0 : Y + 6 * S ≤ a ∧ a < Y + 6 * S + b * b
    · exact Or.inl h0
    by_cases h1 : Y + 11 * S ≤ a ∧ a < Y + 11 * S + b * b
    · exact Or.inr (Or.inl h1)
    exact Or.inr (Or.inr (hm₃ _ (by pomega) (by pomega) (Or.inr (by pomega)) (by pomega)
      (by pomega)))
  have hres3 : ∀ a ≤ W', d₃.nmem (W' + 1 + a) < M := fun a ha => by
    rcases hrow a ha with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · obtain ⟨s', hs', t', ht', he⟩ := rowmaj (show a - (Y + 6 * S) < b * b by omega)
      have := (hF₀ s' hs' t' ht').2.lt hM0
      rwa [← he, show Y + 6 * S + (a - (Y + 6 * S)) = a by omega] at this
    · obtain ⟨s', hs', t', ht', he⟩ := rowmaj (show a - (Y + 11 * S) < b * b by omega)
      have := (hF₁ s' hs' t' ht').2.lt hM0
      rwa [← he, show Y + 11 * S + (a - (Y + 11 * S)) = a by omega] at this
    · rw [h]; exact (hS₂.rmem a ha).lt hM0
  have hregs3 : ∀ r < 1000, d₃.nreg (1000 + r) < M := fun r hr => by
    rw [hn₃ _ (by omega)]; exact (hS₂.rreg r hr).lt hM0
  set c₃ := decodeN 1000 W' M H (W' + 1) c₂ d₃ with hc₃d
  have hS₃ : Sim 1000 W' M (W' + 1) c₃ d₃ := sim_decodeN hregs3 hres3
  have hc₃ : WordsBounded W' c₃ := wb_decodeN hc₂ (fun r hr => by
      by_cases h1 : r < 752
      · exact hRW₃ r h1
      by_cases h2 : r < 910
      · rw [hn₃ r (by omega), hS₂.nreg r (by omega)]; exact hc₂.1 r
      by_cases h3 : r < 919
      · rw [hz₃ r (by omega)]; exact Nat.zero_le _
      by_cases h4 : r < 960
      · rw [hn₃ r (by omega), hS₂.nreg r (by omega)]; exact hc₂.1 r
      by_cases h5 : r < 967
      · exact hR96₃ r (by omega) h5
      · rw [hn₃ r (by omega), hS₂.nreg r (by omega)]; exact hc₂.1 r) hMW₃
  have hZi₃ : IntAll c₃ := intAll_decodeN hZi₂
  have hn₃c : ∀ r, ((800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r < 960)) → c₃.nreg r = c.nreg r :=
    fun r hr => by
      show (if r < 1000 then d₃.nreg r else c₂.nreg r) = c.nreg r
      rw [if_pos (by omega), hn₃ r (by omega), hN₂ r (by omega)]
  have hctx₃ : NCtx m w b Z M₀ c₃ := hctx.of fun r h1 h2 => hn₃c r (by omega)
  have hx₃ : XCtx Y S c₃ := hx.of fun r h1 h2 => hn₃c r (by omega)
  have hnm₃ : ∀ a, Z ≤ a → a < Y → c₃.nmem a = c.nmem a := fun a h1 h2 => by
    show (if a ≤ W' then d₃.nmem a else c₂.nmem a) = c.nmem a
    rw [if_pos (by pomega), hm₃ a h1 (by pomega) (Or.inl (by pomega)) (Or.inl (by pomega))
      (Or.inl (by pomega)), hm₂N a (by pomega) (Or.inl h2)]
  have hrm₃keep : ∀ a ≤ W', ¬ (Y + 6 * S ≤ a ∧ a < Y + 6 * S + b * b) →
      ¬ (Y + 11 * S ≤ a ∧ a < Y + 11 * S + b * b) → c₃.rmem a = c₂.rmem a :=
    fun a ha h1 h2 => by
      show (if a ≤ W' then sgnD H M (d₃.nmem (W' + 1 + a)) else c₂.rmem a) = c₂.rmem a
      rw [if_pos ha]
      rcases hrow a ha with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · rw [h]; exact sgnD_eq (hS₂.rmem a ha) ((hI₂'.1 a ha).trans (by exact_mod_cast hBH)) hM
  have hrmc : ∀ a, Z ≤ a → a < Y → c₃.rmem a = c.rmem a := fun a h1 h2 => by
    rw [hrm₃keep a (by pomega) (by pomega) (by pomega), hrm₂]
  -- the bounds of the matrices
  have hPm₀ : P₀.card ≤ m := by
    rw [hN.enum.card]; exact card_le_card subset_union_left
  have hPm₁ : P₁.card ≤ m := by
    rw [hN.enum.card]; exact card_le_card subset_union_right
  have hℓB : ∀ d ∈ P₀ ∪ P₁, |ℓ d| ≤ B := fun d hd => by
    obtain ⟨i, hi, rfl⟩ := hN.enum.surj d hd
    have := hI.1 (Z + 3 * M₀ + i) (by pomega)
    rw [hLm i hi] at this
    exact_mod_cast this
  have hδB₀ : ∀ x ∈ verts N (P₀ ∪ P₁), |δ₀ x| ≤ B := fun x hx => by
    have := hI.1 (Z + 4 * M₀ + ν x) (by have := hN.lt x hx; pomega)
    rw [hD₀ _ (hN.lt x hx), hN.inv x hx] at this
    exact_mod_cast this
  have hδB₁ : ∀ x ∈ verts N (P₀ ∪ P₁), |δ₁ x| ≤ B := fun x hx => by
    have := hI.1 (Z + 5 * M₀ + ν x) (by have := hN.lt x hx; pomega)
    rw [hD₁ _ (hN.lt x hx), hN.inv x hx] at this
    exact_mod_cast this
  have hvm : ∀ {X : Finset D}, X ⊆ P₀ ∪ P₁ → verts N X ⊆ verts N (P₀ ∪ P₁) := fun hX =>
    union_subset_union (image_subset_image hX) (image_subset_image hX)
  have hBK₀ : ∀ s < b, ∀ t < b,
      |(matOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) γ₀ s t : ℝ)| ≤ (BK : ℝ) :=
    fun s hs t ht => abs_matOf_le hmssp hnn₀ hPm₀ (fun d hd => hℓB d (mem_union_left _ hd))
      (fun x hx => hδB₀ x (hvm subset_union_left hx))
      inter_subset_left γ₀ s t (hen₀.mem s hs) (hen₀.mem t ht)
  have hBK₁ : ∀ s < b, ∀ t < b,
      |(matOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) γ₁ s t : ℝ)| ≤ (BK : ℝ) :=
    fun s hs t ht => abs_matOf_le hmssp hnn₁ hPm₁ (fun d hd => hℓB d (mem_union_right _ hd))
      (fun x hx => hδB₁ x (hvm subset_union_right hx))
      inter_subset_right γ₁ s t (hen₁.mem s hs) (hen₁.mem t ht)
  have hF₀' : ∀ s < b, ∀ t < b,
      c₃.nmem (Y + 6 * S + (s * b + t)) =
          finB (arcOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) γ₀) s t ∧
        c₃.rmem (Y + 6 * S + (s * b + t)) =
          (matOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) γ₀ s t : ℝ) := fun s hs t ht => by
    have := rmLt hs ht
    refine ⟨?_, ?_⟩
    · show (if _ ≤ W' then d₃.nmem _ else c₂.nmem _) = _
      rw [if_pos (by pomega)]; exact (hF₀ s hs t ht).1
    · show (if _ ≤ W' then sgnD H M (d₃.nmem _) else c₂.rmem _) = _
      rw [if_pos (by pomega)]
      have hb' : (BK : ℝ) ≤ H := by exact_mod_cast le_trans hBKH.1 hBKH.2
      exact sgnD_eq (hF₀ s hs t ht).2 ((hBK₀ s hs t ht).trans hb') hM
  have hF₁' : ∀ s < b, ∀ t < b,
      c₃.nmem (Y + 11 * S + (s * b + t)) =
          finB (arcOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) γ₁) s t ∧
        c₃.rmem (Y + 11 * S + (s * b + t)) =
          (matOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) γ₁ s t : ℝ) := fun s hs t ht => by
    have := rmLt hs ht
    refine ⟨?_, ?_⟩
    · show (if _ ≤ W' then d₃.nmem _ else c₂.nmem _) = _
      rw [if_pos (by pomega)]; exact (hF₁ s hs t ht).1
    · show (if _ ≤ W' then sgnD H M (d₃.nmem _) else c₂.rmem _) = _
      rw [if_pos (by pomega)]
      have hb' : (BK : ℝ) ≤ H := by exact_mod_cast le_trans hBKH.1 hBKH.2
      exact sgnD_eq (hF₁ s hs t ht).2 ((hBK₁ s hs t ht).trans hb') hM
  have hO₀' : ∀ x < b, c₃.nmem (Y + 4 * S + x) = ν (γ₀ x) := fun x hx => by
    show (if _ ≤ W' then d₃.nmem _ else c₂.nmem _) = _
    rw [if_pos (by pomega)]; exact hO₀ x hx
  have hO₁' : ∀ x < b, c₃.nmem (Y + 9 * S + x) = ν (γ₁ x) := fun x hx => by
    show (if _ ≤ W' then d₃.nmem _ else c₂.nmem _) = _
    rw [if_pos (by pomega)]; exact hO₁ x hx
  have hI₃ : NInv W' BK c₃ := by
    refine ⟨fun a ha => ?_, fun r h1 h2 => ?_⟩
    · by_cases h0 : Y + 6 * S ≤ a ∧ a < Y + 6 * S + b * b
      · obtain ⟨s', hs', t', ht', he⟩ := rowmaj (show a - (Y + 6 * S) < b * b by omega)
        have := (hF₀' s' hs' t' ht').2
        rw [← he, show Y + 6 * S + (a - (Y + 6 * S)) = a by omega] at this
        rw [this]; exact hBK₀ s' hs' t' ht'
      by_cases h1 : Y + 11 * S ≤ a ∧ a < Y + 11 * S + b * b
      · obtain ⟨s', hs', t', ht', he⟩ := rowmaj (show a - (Y + 11 * S) < b * b by omega)
        have := (hF₁' s' hs' t' ht').2
        rw [← he, show Y + 11 * S + (a - (Y + 11 * S)) = a by omega] at this
        rw [this]; exact hBK₁ s' hs' t' ht'
      rw [hrm₃keep a ha h0 h1]
      exact (hI₂'.1 a ha).trans (by exact_mod_cast (show B ≤ BK by rw [hBK]; nlinarith))
    · show |(if r < 1000 then sgnD H M (d₃.nreg (1000 + r)) else c₂.rreg r)| ≤ _
      rw [if_pos (by omega), hn₃ _ (by omega),
        sgnD_eq (hS₂.rreg r (by omega)) ((hI₂'.2 r h1 h2).trans (by exact_mod_cast hBH)) hM]
      exact (hI₂'.2 r h1 h2).trans (by exact_mod_cast (show B ≤ BK by rw [hBK]; nlinarith))
  -- 4. the end of the node: real, then simulated
  obtain ⟨c₄, k₄, o, e₄, hk₄, hpot, hstep, ho₄⟩ :=
    rest_exec (I := I) C hfr hmssp hN hP₀ hP₁ ℓ δ₀ δ₁ hδ₀ hδ₁ hen₀ hen₁ hcr₀ hcr₁ hM₀ hZ hbZ hY
      hSw hSb hW₁ c₃ hc₃ hctx₃ hx₃
      (fun d hd => by rw [hnm₃ _ (by pomega) (by pomega)]; exact hTm d hd)
      (fun d hd => by rw [hnm₃ _ (by pomega) (by pomega)]; exact hHm d hd)
      (fun d hd => by rw [hnm₃ _ (by pomega) (by pomega)]; exact hSm d hd)
      (fun d hd => by rw [hrmc _ (by pomega) (by pomega)]; exact hLm d hd)
      (fun v hv => by rw [hrmc _ (by pomega) (by pomega)]; exact hD₀ v hv)
      (fun v hv => by rw [hrmc _ (by pomega) (by pomega)]; exact hD₁ v hv) hO₀' hO₁' hF₀' hF₁'
  obtain ⟨hNC, hI₄, -⟩ := rest_cmp (I := I) hfr hN hP₀ hP₁ hb1 ℓ δ₀ δ₁ hδ₀ hδ₁ hen₀ hen₁ hcr₀ hcr₁
    hM₀ hZ hbZ hY hSw hSb hW₁ c₃ hctx₃ hx₃
    (fun d hd => by rw [hnm₃ _ (by pomega) (by pomega)]; exact hTm d hd)
    (fun d hd => by rw [hnm₃ _ (by pomega) (by pomega)]; exact hHm d hd)
    (fun d hd => by rw [hnm₃ _ (by pomega) (by pomega)]; exact hSm d hd)
    (fun d hd => by rw [hrmc _ (by pomega) (by pomega)]; exact hLm d hd)
    (fun v hv => by rw [hrmc _ (by pomega) (by pomega)]; exact hD₀ v hv)
    (fun v hv => by rw [hrmc _ (by pomega) (by pomega)]; exact hD₁ v hv) hO₀' hO₁' hF₀' hF₁'
    hI₃ hZi₃ e₄
  have hK₃ : Consts 1000 M H (W' + 1) d₃ :=
    ⟨by rw [hn₃ _ (by omega)]; exact hK₂.m, by rw [hn₃ _ (by omega)]; exact hK₂.h,
      by rw [hn₃ _ (by omega)]; exact hK₂.b⟩
  have h512 : 512 * restB b w BK ≤ H := by rw [hHd]; unfold nodeHN; rw [← hBK]; omega
  obtain ⟨d₄, k₄', ex₄, hk₄', hS₄, -⟩ :=
    ((hNC.exec e₄).mono_H h512).toNat restProg_regs1000 restProg_noDivR hM (β := W' + 1) (W' := WN) (by omega)
      (by omega) (by omega) (by omega) hS₃ hK₃ e₃.wb_right
  refine ⟨d₄, k₂' + (k₃ + k₄'), o, Exec.seq ex₂ (Exec.seq e₃ ex₄), ?_, hpot,
    fun bf hbf => ?_, ?_⟩
  · have : k₁ = 8 := hq₁k
    pomega
  · rcases hstep bf hbf with ⟨h1, h2⟩ | ⟨f, h1, h2, h3⟩
    · exact Or.inl ⟨h1, by rw [hS₄.nreg 990 (by omega)]; exact h2⟩
    · refine Or.inr ⟨f, h1, by rw [hS₄.nreg 990 (by omega)]; exact h2, fun x hx => ?_⟩
      have hνx := hN.lt x hx
      have ha : Z + 20 * M₀ + ν x ≤ W' := by pomega
      rw [sgnD_eq (hS₄.rmem _ ha) ((hI₄.1 _ ha).trans (by exact_mod_cast hBKH.2)) hM]
      exact (h3 x hx).symm
  · rw [hS₄.output, ho₄]
    show d₃.output = c.output
    rw [ho₃, hS₂.output, hf₂.out, go₁]

end NegSSSP

end PlanarFlow
