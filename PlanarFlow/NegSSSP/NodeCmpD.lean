module

public import PlanarFlow.NegSSSP.NodeCmpC

/-!
# The node run on natural words: the composition, the whole node

`node_exec_cmp`: `node_exec` with, for the same one-face instances and encodings of the two parts
and from the same configurations, **every run of the node compare-bounded**: from a configuration
with `NInv W' B` (real memory `≤ W'` and real registers `500 … 519` bounded by `B`) and integer
reals, with `nodeProg` free of `divR` and Klein's part (`kStmt`, the two `kPairOf`)
compare-bounded by `HK` ending with `NInv W' BK` (`KCmp`, a hypothesis), the node satisfies
`NodeCmp I W' (nodeH b w B HK BK) (nodeBf b w BK)`:

* `nodeBf b w BK = restB b w BK = partB b w (partB b w ((4 b + 2) bfB b BK))`, with
  `partB b w X = (w + 3) (2 b + 3) (b + 1) X` (the chain `B → BK → bfB b BK → (4 b + 2) · →
  (2 b + 3)(b + 1) · → (w + 3) · → (2 b + 3)(b + 1) · → (w + 3) ·`: Klein's part, Bellman–Ford,
  `cProg`, the first part (`pProg`, FR-Dijkstra), the second part);
* `nodeH b w B HK BK = 2 B + HK + 512 nodeBf b w BK`.

The walk is that of `node_exec` (the start of `restProg` is only known there), with `rest_cmp`
for the end of the node.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace NegSSSP

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs BKMNW Monge Monge.FR
  CmpAbs ModNat

/-- Klein's part of the node: the two parts, the one with the smaller work space first. -/
def kStmt (p₀ p₁ : KP) : Stmt :=
  if p₀.Kw ≤ p₁.Kw then kPairOf 0 807 p₀ 1 808 p₁ else kPairOf 1 808 p₁ 0 807 p₀

theorem nodeProg_eq (p₀ p₁ : KP) :
    nodeProg p₀ p₁ = .seq bdSet (.seq bdryProg (.seq (kStmt p₀ p₁) restProg)) := rfl

/-- The bound of the real memory at the end of the node. -/
def nodeBf (b w BK : ℕ) : ℕ := restB b w BK

/-- The bound of the comparisons of the node. -/
def nodeH (b w B HK BK : ℕ) : ℕ := 2 * B + HK + 512 * nodeBf b w BK

theorem nodeBf_le_nodeH (b w B HK BK : ℕ) : nodeBf b w BK ≤ nodeH b w B HK BK := by
  unfold nodeH; omega

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxHeartbeats 8000000 in
/-- **The whole node as one run, compare-bounded** (see the module docstring). -/
theorem node_exec_cmp (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
    {mssp : Finset D → (D → ℤ) → Finset V → V → V → Option ℤ} (hmssp : PieceMSSPSpec N mssp)
    {P P₀ P₁ : Finset D} (hS : SplitF N P P₀ P₁) (hB : (bdry N P₀ P₁).Nonempty) (ℓ : D → ℤ)
    (δ₀ δ₁ : V → ℤ) (hδ₀ : (pg N P₀ ℓ).IsPot δ₀) (hδ₁ : (pg N P₁ ℓ).IsPot δ₁) :
    ∃ (fd₀ : FaceData N P₀ (bdry N P₀ P₁)) (n₀ Bw₀ : ℕ)
      (σ₀ : Klein.SrcD fd₀.DQ fd₀.k ≃ Fin (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k))) (Pk₀ : Input)
      (fd₁ : FaceData N P₁ (bdry N P₀ P₁)) (n₁ Bw₁ : ℕ)
      (σ₁ : Klein.SrcD fd₁.DQ fd₁.k ≃ Fin (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k))) (Pk₁ : Input),
      fd₀.q = 18 * P.card ∧ fd₁.q = 18 * P.card ∧
      ∀ {m w b : ℕ} {e : ℕ → D} {ν : V → ℕ} {ι : ℕ → V}, NodeEnc N P₀ P₁ m w e ν ι →
      b = (bdry N P₀ P₁).card →
      ∀ (L₀ L₁ Pb₀ Pb₁ β₀ β₁ Rk₀ Rk₁ Z M₀ Y S W' : ℕ) (I : Input) (c : Config),
        M₀ = m + w + 1 → loB m w ≤ Z → bfWP b < Z →
        Bw₀ + 16 * (n₀ + 1) < Z → Bw₁ + 16 * (n₁ + 1) < Z →
        n₀ + fd₀.k * fd₀.k ≤ Z → n₁ + fd₁.k * fd₁.k ≤ Z →
        3 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 3 + fd₀.k * fd₀.k ≤ Z →
        3 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 3 + fd₁.k * fd₁.k ≤ Z →
        Z + 22 * M₀ ≤ Y →
        (w ≤ S ∧ b * b ≤ S ∧ fd₀.k ≤ S ∧ fd₁.k ≤ S ∧ 3 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 3 ≤ S ∧
          3 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 3 ≤ S) →
        (Y + 16 * S ≤ Pb₀ ∧ Y + 16 * S ≤ Pb₁ ∧ Y + 16 * S ≤ β₀ ∧ Y + 16 * S ≤ β₁ ∧
          Y + 16 * S ≤ Rk₀ ∧ Y + 16 * S ≤ Rk₁) →
        (Y + 16 * S ≤ W' ∧ Pb₀ + w ≤ W' ∧ Pb₁ + w ≤ W' ∧ Rk₀ + (3 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 3) ≤ W' ∧
          Rk₁ + (3 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 3) ≤ W' ∧ L₀ + 1 ≤ W' ∧ L₁ + 1 ≤ W') →
        ((Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀)) : ℤ) : ℝ) ≤ 2 ^ L₀ →
        ((Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁)) : ℤ) : ℝ) ≤ 2 ^ L₁ →
        WordsBounded W' c → NCtx m w b Z M₀ c → XCtx Y S c →
        (∀ d < m, c.nmem (Z + 0 * M₀ + d) = encT N e ν d) →
        (∀ d < m, c.nmem (Z + 1 * M₀ + d) = encH N e ν d) →
        (∀ d < m, c.nmem (Z + 2 * M₀ + d) = encS P₀ e d) →
        (∀ d < m, c.rmem (Z + 3 * M₀ + d) = ℓ (e d)) →
        (∀ v < w, c.rmem (Z + 4 * M₀ + v) = δ₀ (ι v)) →
        (∀ v < w, c.rmem (Z + 5 * M₀ + v) = δ₁ (ι v)) →
        (∀ a < Z, c.nmem a = 0) →
        (∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₀ + ν x) < fd₀.k ∧
          fd₀.Q.tail (fd₀.g (c.nmem (Pb₀ + ν x))) = fd₀.j x) →
        (∀ x ∈ bdry N P₀ P₁, c.nmem (Pb₁ + ν x) < fd₁.k ∧
          fd₁.Q.tail (fd₁.g (c.nmem (Pb₁ + ν x))) = fd₁.j x) →
        KSlot (Klein.srcMap fd₀.inst.cycle) fd₀.k (Klein.srcG fd₀.inst.cycle)
          (Klein.srcPiece fd₀.k (fd₀.P'.image fd₀.e))
          (MSSP.pert (Klein.srcLen (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))
            (Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀)))))
          σ₀ Bw₀ n₀ β₀ Rk₀ W' Pk₀ c →
        KSlot (Klein.srcMap fd₁.inst.cycle) fd₁.k (Klein.srcG fd₁.inst.cycle)
          (Klein.srcPiece fd₁.k (fd₁.P'.image fd₁.e))
          (MSSP.pert (Klein.srcLen (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))
            (Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁)))))
          σ₁ Bw₁ n₁ β₁ Rk₁ W' Pk₁ c →
        (∃ c' t, ∃ o : Option (V → ℤ),
          Exec I W' (nodeProg ⟨fd₀.k, Fintype.card (Klein.SrcD fd₀.DQ fd₀.k), n₀, Bw₀, Pk₀.data.length, β₀, Rk₀, Pb₀, L₀,
          Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))⟩
            ⟨fd₁.k, Fintype.card (Klein.SrcD fd₁.DQ fd₁.k), n₁, Bw₁, Pk₁.data.length, β₁, Rk₁, Pb₁, L₁,
          Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))⟩) c c' t ∧
          t ≤ 8 + (61 * m + 12) +
          ((3 * (32886 * 2372500000 * P.card * lg P.card) + rdCost b L₀ (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k)) + 19 * fd₀.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 300) +
          (3 * (32886 * 2372500000 * P.card * lg P.card) + rdCost b L₁ (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k)) + 19 * fd₁.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 300) + 14) +
          (bfCostP b + 4 * bfWP b + 22 * (b * b) + 2 * (cNegMach C).dij (w + 1) (m + w) +
            232 * m + 450 * w + 92 * b + 2917) ∧
          PotOut ((childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).join (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁))) o ∧
          (∀ bf : DDG V → DDG V → Option (V → ℤ), bf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) = o →
            (step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = none ∧ c'.nreg 990 ≠ 0) ∨
            (∃ f, step N mssp bf fr P₀ P₁ ℓ δ₀ δ₁ = some f ∧ c'.nreg 990 = 0 ∧
              ∀ x ∈ verts N (P₀ ∪ P₁), c'.rmem (Z + 20 * M₀ + ν x) = f x)) ∧
          c'.output = c.output) ∧
        ∀ B HK BK : ℕ, NInv W' B c → IntAll c →
          (nodeProg
          ⟨fd₀.k, Fintype.card (Klein.SrcD fd₀.DQ fd₀.k), n₀, Bw₀, Pk₀.data.length, β₀, Rk₀, Pb₀, L₀,
            Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))⟩
            ⟨fd₁.k, Fintype.card (Klein.SrcD fd₁.DQ fd₁.k), n₁, Bw₁, Pk₁.data.length, β₁, Rk₁, Pb₁, L₁,
            Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))⟩).noDivR = true →
          KCmp I W' B HK BK (kStmt
          ⟨fd₀.k, Fintype.card (Klein.SrcD fd₀.DQ fd₀.k), n₀, Bw₀, Pk₀.data.length, β₀, Rk₀, Pb₀, L₀,
            Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))⟩
            ⟨fd₁.k, Fintype.card (Klein.SrcD fd₁.DQ fd₁.k), n₁, Bw₁, Pk₁.data.length, β₁, Rk₁, Pb₁, L₁,
            Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))⟩) →
          NodeCmp I W' (nodeH b w B HK BK) (nodeBf b w BK)
          ⟨fd₀.k, Fintype.card (Klein.SrcD fd₀.DQ fd₀.k), n₀, Bw₀, Pk₀.data.length, β₀, Rk₀, Pb₀, L₀,
            Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))⟩
            ⟨fd₁.k, Fintype.card (Klein.SrcD fd₁.DQ fd₁.k), n₁, Bw₁, Pk₁.data.length, β₁, Rk₁, Pb₁, L₁,
            Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))⟩ c := by
  classical
  have hnn₀ := redLen_nonneg hδ₀
  have hnn₁ := redLen_nonneg hδ₁
  obtain ⟨fd₀, n₀, Bw₀, σ₀, Pk₀, hq₀, hr₀⟩ := kpart_exec hS hB (Or.inl rfl) hnn₀ hmssp
  obtain ⟨fd₁, n₁, Bw₁, σ₁, Pk₁, hq₁, hr₁⟩ := kpart_exec hS hB (Or.inr rfl) hnn₁ hmssp
  refine ⟨fd₀, n₀, Bw₀, σ₀, Pk₀, fd₁, n₁, Bw₁, σ₁, Pk₁, hq₀, hq₁, ?_⟩
  intro m w b e ν ι hN hb L₀ L₁ Pb₀ Pb₁ β₀ β₁ Rk₀ Rk₁ Z M₀ Y S W' I c hM₀ hZ hbZ hK₀ hK₁ hk₀
    hk₁ ho₀ ho₁ hY hSz hIn hW hWL₀ hWL₁ hc hctx hx hTm hHm hSm hLm hD₀ hD₁ hz hpos₀ hpos₁ hE₀
    hE₁
  obtain ⟨hSw, hSb, hSk₀, hSk₁, hSn₀, hSn₁⟩ := hSz
  obtain ⟨hI₁, hI₂, hI₃, hI₄, hI₅, hI₆⟩ := hIn
  obtain ⟨hW₁, hW₂, hW₃, hW₄, hW₅, hW₆, hW₇⟩ := hW
  have hbw : b ≤ w := hb ▸ card_bdry_le hN
  have hm2 := hN.w2
  have hA : loB m w = 4 * m + 18 * w + 175 := rfl
  have hP₀ : P₀.Nonempty := card_pos.1 hS.2.2.1
  have hP₁ : P₁.Nonempty := card_pos.1 hS.2.2.2.1
  have hx' := hx.reg
  -- 1. the boundary
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
  have hx₂ : XCtx Y S c₂ := hx.of fun r h1 h2 => hR₂ r (by pomega)
  have h802 : c₂.nreg 802 = b := by rw [hR₂ 802 (by pomega), hctx.r802]
  have h807 : c₂.nreg 807 = Z + 4 * M₀ := by rw [hR₂ 807 (by pomega), hctx.slot 4 (by omega)]
  have h808 : c₂.nreg 808 = Z + 5 * M₀ := by rw [hR₂ 808 (by pomega), hctx.slot 5 (by omega)]
  have hpos₀' : ∀ x ∈ bdry N P₀ P₁, c₂.nmem (Pb₀ + ν x) < fd₀.k ∧
      fd₀.Q.tail (fd₀.g (c₂.nmem (Pb₀ + ν x))) = fd₀.j x := fun x hx => by
    rw [hm₂' _ (by pomega)]; exact hpos₀ x hx
  have hpos₁' : ∀ x ∈ bdry N P₀ P₁, c₂.nmem (Pb₁ + ν x) < fd₁.k ∧
      fd₁.Q.tail (fd₁.g (c₂.nmem (Pb₁ + ν x))) = fd₁.j x := fun x hx => by
    rw [hm₂' _ (by pomega)]; exact hpos₁ x hx
  have hδ₀' : ∀ v < w, c₂.rmem (Z + 4 * M₀ + v) = δ₀ (ι v) := fun v hv => by
    rw [hrm₂]; exact hD₀ v hv
  have hδ₁' : ∀ v < w, c₂.rmem (Z + 5 * M₀ + v) = δ₁ (ι v) := fun v hv => by
    rw [hrm₂]; exact hD₁ v hv
  have hE₀' := hE₀.of (d := c₂) (fun i _ => by rw [hrm₂]) (fun i _ => hm₂' _ (by pomega))
  have hE₁' := hE₁.of (d := c₂) (fun i _ => by rw [hrm₂]) (fun i _ => hm₂' _ (by pomega))
  have hlow : ∀ a < Z, c₂.nmem a = 0 := fun a ha => by rw [hm₂' a (by pomega)]; exact hz a ha
  have hKL₀ : ∀ z ≤ 1, KLay b w fd₀.k (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k)) n₀
      (Bw₀ + 16 * (n₀ + 1)) L₀ (Y + 2 * S) Pb₀ (Z + 4 * M₀) (Y + (3 + 5 * z) * S) S β₀ Rk₀ W' :=
    fun z hz => klay_of hz (by pomega) hSb hSk₀ hSn₀ hK₀ hk₀ ho₀ (by pomega) (by pomega) hI₁ hI₃
      hI₅ hW₁ hW₂ hW₄ hW₆ (by pomega) (by pomega)
  have hKL₁ : ∀ z ≤ 1, KLay b w fd₁.k (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k)) n₁
      (Bw₁ + 16 * (n₁ + 1)) L₁ (Y + 2 * S) Pb₁ (Z + 5 * M₀) (Y + (3 + 5 * z) * S) S β₁ Rk₁ W' :=
    fun z hz => klay_of hz (by pomega) hSb hSk₁ hSn₁ hK₁ hk₁ ho₁ (by pomega) (by pomega) hI₂ hI₄
      hI₆ hW₁ hW₃ hW₅ hW₇ (by pomega) (by pomega)
  have e4 : ∀ x, Y + (3 + 5 * 0) * S + S + x = Y + 4 * S + x := fun x => by ring
  have e6 : ∀ x, Y + (3 + 5 * 0) * S + 3 * S + x = Y + 6 * S + x := fun x => by ring
  have e9 : ∀ x, Y + (3 + 5 * 1) * S + S + x = Y + 9 * S + x := fun x => by ring
  have e11 : ∀ x, Y + (3 + 5 * 1) * S + 3 * S + x = Y + 11 * S + x := fun x => by ring
  set p₀ : KP := ⟨fd₀.k, Fintype.card (Klein.SrcD fd₀.DQ fd₀.k), n₀, Bw₀, Pk₀.data.length, β₀,
    Rk₀, Pb₀, L₀, Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))⟩
    with hp₀
  set p₁ : KP := ⟨fd₁.k, Fintype.card (Klein.SrcD fd₁.DQ fd₁.k), n₁, Bw₁, Pk₁.data.length, β₁,
    Rk₁, Pb₁, L₁, Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))⟩
    with hp₁
  -- 2. the two parts
  obtain ⟨c₃, k₃, γ₀, γ₁, e₃, hk₃, hen₀, hO₀, hcr₀, hF₀, hen₁, hO₁, hcr₁, hF₁, hn₃, hm₃, hr₃,
      ho₃⟩ : ∃ c₃ k₃, ∃ γ₀ γ₁ : ℕ → V,
      Exec I W' (if p₀.Kw ≤ p₁.Kw then kPairOf 0 807 p₀ 1 808 p₁ else kPairOf 1 808 p₁ 0 807 p₀)
        c₂ c₃ k₃ ∧
      k₃ ≤ (3 * (32886 * 2372500000 * P.card * lg P.card) +
            rdCost b L₀ (Fintype.card (Klein.SrcD fd₀.DQ fd₀.k)) + 19 * fd₀.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fd₀.DQ fd₀.k) + 300) +
          (3 * (32886 * 2372500000 * P.card * lg P.card) +
            rdCost b L₁ (Fintype.card (Klein.SrcD fd₁.DQ fd₁.k)) + 19 * fd₁.k + 10 * b +
            33 * Fintype.card (Klein.SrcD fd₁.DQ fd₁.k) + 300) + 14 ∧
      IsEnum b γ₀ (bdry N P₀ P₁) ∧ (∀ x < b, c₃.nmem (Y + 4 * S + x) = ν (γ₀ x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)).len (γ₀ i)
        (γ₀ i')) ∧
      (∀ s < b, ∀ t < b,
        c₃.nmem (Y + 6 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) γ₀) s t ∧
          c₃.rmem (Y + 6 * S + (s * b + t)) =
            (matOf (childDDG N mssp P₀ ℓ δ₀ (bdry N P₀ P₁)) γ₀ s t : ℝ)) ∧
      IsEnum b γ₁ (bdry N P₀ P₁) ∧ (∀ x < b, c₃.nmem (Y + 9 * S + x) = ν (γ₁ x)) ∧
      Monge.CrossingO b (fun i i' => (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)).len (γ₁ i)
        (γ₁ i')) ∧
      (∀ s < b, ∀ t < b,
        c₃.nmem (Y + 11 * S + (s * b + t)) =
            finB (arcOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) γ₁) s t ∧
          c₃.rmem (Y + 11 * S + (s * b + t)) =
            (matOf (childDDG N mssp P₁ ℓ δ₁ (bdry N P₀ P₁)) γ₁ s t : ℝ)) ∧
      (∀ r, (800 ≤ r ∧ r < 900) ∨ (919 ≤ r ∧ r < 960) ∨ 967 ≤ r → c₃.nreg r = c₂.nreg r) ∧
      (∀ a, Z ≤ a → a < Y → c₃.nmem a = c₂.nmem a) ∧
      (∀ a, Z ≤ a → a < Y → c₃.rmem a = c₂.rmem a) ∧
      c₃.output = c₂.output := by
    by_cases hKK : Bw₀ + 16 * (n₀ + 1) ≤ Bw₁ + 16 * (n₁ + 1)
    · have hKK' : p₀.Kw ≤ p₁.Kw := hKK
      obtain ⟨c₃, k₃, γ₀, γ₁, e₃, hk₃, hen₀, hO₀, hcr₀, hF₀, hen₁, hO₁, hcr₁, hF₁, hn₃, hm₃,
        hr₃, ho₃⟩ := kpair_exec hr₀ hr₁ hN hsrc (zf := 0) (zs := 1) (δrf := 807) (δrs := 808)
          (by omega) (by omega) (by omega) (by omega) (by omega) L₀ Pb₀ β₀ Rk₀ (Z + 4 * M₀) L₁
          Pb₁ β₁ Rk₁ (Z + 5 * M₀) Y S W' I c₂ (hKL₀ 0 (by omega)) (hKL₁ 1 (by omega)) hWL₀
          hWL₁ hKK (by pomega) ⟨by pomega, by pomega⟩ ⟨by pomega, by pomega, by pomega⟩
          ⟨by pomega, by pomega⟩ e₂.wb_right h802 hx₂ h807 h808 hsl hpos₀' hpos₁' hδ₀' hδ₁'
          hE₀' hE₁' (fun a ha => by rw [hlow a (by pomega)]; exact Nat.zero_le _)
      refine ⟨c₃, k₃, γ₀, γ₁, by rw [ite_eq_left_of_eq_true _ _ (eq_true hKK')]; exact e₃, hk₃,
        hen₀, fun x hx => by rw [← e4]; exact hO₀ x hx, hcr₀,
        fun s hs t ht => by rw [← e6]; exact hF₀ s hs t ht, hen₁,
        fun x hx => by rw [← e9]; exact hO₁ x hx, hcr₁,
        fun s hs t ht => by rw [← e11]; exact hF₁ s hs t ht, hn₃,
        fun a h1 h2 => hm₃ a (by pomega) (by pomega),
        fun a h1 h2 => hr₃ a (by pomega) (by pomega) (by pomega) (by pomega), ho₃⟩
    · have hKK' : ¬ p₀.Kw ≤ p₁.Kw := hKK
      obtain ⟨c₃, k₃, γ₁, γ₀, e₃, hk₃, hen₁, hO₁, hcr₁, hF₁, hen₀, hO₀, hcr₀, hF₀, hn₃, hm₃,
        hr₃, ho₃⟩ := kpair_exec hr₁ hr₀ hN hsrc (zf := 1) (zs := 0) (δrf := 808) (δrs := 807)
          (by omega) (by omega) (by omega) (by omega) (by omega) L₁ Pb₁ β₁ Rk₁ (Z + 5 * M₀) L₀
          Pb₀ β₀ Rk₀ (Z + 4 * M₀) Y S W' I c₂ (hKL₁ 1 (by omega)) (hKL₀ 0 (by omega)) hWL₁
          hWL₀ (by omega) (by pomega) ⟨by pomega, by pomega⟩ ⟨by pomega, by pomega, by pomega⟩
          ⟨by pomega, by pomega⟩ e₂.wb_right h802 hx₂ h808 h807 hsl hpos₁' hpos₀' hδ₁' hδ₀'
          hE₁' hE₀' (fun a ha => by rw [hlow a (by pomega)]; exact Nat.zero_le _)
      refine ⟨c₃, k₃, γ₀, γ₁, by rw [ite_eq_right_of_eq_false _ _ (eq_false hKK')]; exact e₃,
        hk₃.trans (le_of_eq (by ring)), hen₀, fun x hx => by rw [← e4]; exact hO₀ x hx, hcr₀,
        fun s hs t ht => by rw [← e6]; exact hF₀ s hs t ht, hen₁,
        fun x hx => by rw [← e9]; exact hO₁ x hx, hcr₁,
        fun s hs t ht => by rw [← e11]; exact hF₁ s hs t ht, hn₃,
        fun a h1 h2 => hm₃ a (by pomega) (by pomega),
        fun a h1 h2 => hr₃ a (by pomega) (by pomega) (by pomega) (by pomega), ho₃⟩
  -- 3. `π`, Bellman–Ford, the Dijkstra half
  have hctx₃ : NCtx m w b Z M₀ c₃ :=
    hctx.of fun r h1 h2 => by rw [hn₃ r (by pomega), hR₂ r (by pomega)]
  have hx₃ : XCtx Y S c₃ := hx.of fun r h1 h2 => by rw [hn₃ r (by pomega), hR₂ r (by pomega)]
  have hm₃' : ∀ a, Z ≤ a → a < Y → c₃.nmem a = c.nmem a := fun a h1 h2 => by
    rw [hm₃ a h1 h2, hm₂' a (by pomega)]
  have hr₃' : ∀ a, Z ≤ a → a < Y → c₃.rmem a = c.rmem a := fun a h1 h2 => by
    rw [hr₃ a h1 h2, hrm₂]
  obtain ⟨c₄, k₄, o, e₄, hk₄, hpot, hstep, ho₄⟩ :=
    rest_exec (I := I) C hfr hmssp hN hP₀ hP₁ ℓ δ₀ δ₁ hδ₀ hδ₁ hen₀ hen₁ hcr₀ hcr₁ hM₀ hZ hbZ hY
      hSw hSb hW₁ c₃ e₃.wb_right hctx₃ hx₃
      (fun d hd => by rw [hm₃' _ (by pomega) (by pomega)]; exact hTm d hd)
      (fun d hd => by rw [hm₃' _ (by pomega) (by pomega)]; exact hHm d hd)
      (fun d hd => by rw [hm₃' _ (by pomega) (by pomega)]; exact hSm d hd)
      (fun d hd => by rw [hr₃' _ (by pomega) (by pomega)]; exact hLm d hd)
      (fun v hv => by rw [hr₃' _ (by pomega) (by pomega)]; exact hD₀ v hv)
      (fun v hv => by rw [hr₃' _ (by pomega) (by pomega)]; exact hD₁ v hv) hO₀ hO₁ hF₀ hF₁
  refine ⟨?_, fun B HK BK hI hZi hD hK c' t ex => ?_⟩
  · refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), o, Exec.seq e₁ (Exec.seq e₂ (Exec.seq e₃ e₄)), ?_, hpot,
      hstep, by rw [ho₄, ho₃, hf₂.out, go₁]⟩
    clear hstep hpot e₄ e₃ e₂ e₁
    generalize 32886 * 2372500000 * P.card * lg P.card = X at hk₃ ⊢
    pomega
  -- the actual run
  have hD3 : (kStmt p₀ p₁).noDivR = true := by
    simp only [nodeProg, Stmt.noDivR, Bool.and_eq_true] at hD; exact hD.2.2.1
  have ex' := ex
  unfold nodeProg at ex
  obtain ⟨_, _, _, x₁, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₁ x₁
  obtain ⟨_, _, _, x₂, ex⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₂ x₂
  obtain ⟨_, _, _, x₃, x₄⟩ := seq_parts ex
  obtain ⟨rfl, -⟩ := Exec.det e₃ x₃
  have hb1 : 1 ≤ b := hb ▸ Finset.card_pos.2 hB
  obtain ⟨hB1, hB2⟩ := le_restB (w := w) (B := BK) hb1
  have G₁ := good_glue (H := nodeH b w B HK BK) bdSet_glueOK (by decide +kernel) e₁ hI hZi
    (by unfold nodeH; omega)
  have G₂ := good_glue (H := nodeH b w B HK BK) bdryProg_glueOK (by decide +kernel) e₂ G₁.2.1
    G₁.2.2 (by unfold nodeH; omega)
  have G₃ : NGood I W' (nodeH b w B HK BK) BK (kStmt p₀ p₁) c₂ c₃ := by
    obtain ⟨C, hI'⟩ := hK c₂ c₃ k₃ G₂.2.1 G₂.2.2 e₃
    exact ⟨⟨_, C.mono_H (by unfold nodeH; omega)⟩, hI', Exec.intAll e₃ hD3 G₂.2.2⟩
  have G₄ := rest_cmp (I := I) hfr hN hP₀ hP₁ hb1 ℓ δ₀ δ₁ hδ₀ hδ₁ hen₀ hen₁ hcr₀ hcr₁ hM₀ hZ hbZ hY
      hSw hSb hW₁ c₃ hctx₃ hx₃
      (fun d hd => by rw [hm₃' _ (by pomega) (by pomega)]; exact hTm d hd)
      (fun d hd => by rw [hm₃' _ (by pomega) (by pomega)]; exact hHm d hd)
      (fun d hd => by rw [hm₃' _ (by pomega) (by pomega)]; exact hSm d hd)
      (fun d hd => by rw [hr₃' _ (by pomega) (by pomega)]; exact hLm d hd)
      (fun v hv => by rw [hr₃' _ (by pomega) (by pomega)]; exact hD₀ v hv)
      (fun v hv => by rw [hr₃' _ (by pomega) (by pomega)]; exact hD₁ v hv) hO₀ hO₁ hF₀ hF₁
      G₃.2.1 G₃.2.2 x₄
  have G := G₁.seq (G₂.seq (G₃.seq (G₄.mono (by unfold nodeH nodeBf; omega) le_rfl)))
  exact ⟨G.1.exec ex', G.2.1.1⟩


end NegSSSP

end PlanarFlow
