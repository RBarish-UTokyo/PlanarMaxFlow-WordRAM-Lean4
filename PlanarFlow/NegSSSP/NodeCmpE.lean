module

public import PlanarFlow.NegSSSP.NodeCmpD
public import PlanarFlow.NegSSSP.NodeExec

/-!
# The node run on natural words: the whole node on natural words

`node_exec_nat'`: `node_exec_cmp` and `node_exec_nat` together. For the one-face instances and
encodings of `node_exec`, from a configuration as in `node_exec` with `NInv W' B` and integer
reals, assuming `nodeProg` free of `divR`, its registers `< R`, and Klein's part compare-bounded
(`KCmp … HK BK`), with one modulus `M > 2 nodeH b w B HK BK` and words `WN ≥ 2 W' + 1 + M² + M`:
the run of `node_exec` (the output of `NegSSSP.step` at `Z + 20 M₀ + ν x`) is simulated by
`constsS R M H (W' + 1); ModNat.toNat R M nodeProg` (`H = nodeH b w B HK BK`) from
`natOf R W' M (W' + 1) c` within `4 t + 3` steps, every real cell `≤ W'` of the end read back
from its residue; with the sizes of `node_exec_cost_le` (`m = |P| = m₀ + m₁`, `L₀ = L₁ = ε lg m`),
`t ≤ 1000 · NegCosts.node + 10000` and `t' ≤ 4000 · NegCosts.node + 40003` under `cNegMach C`.
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

universe u v w

variable {D : Type u} {V : Type v} {F : Type w} [Fintype D] [DecidableEq D] [Fintype V]
  [DecidableEq V] {N : CombMap D V F}

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- **The whole node on natural words** (see the module docstring). -/
theorem node_exec_nat' (C : ℕ) {fr : FRFun (Option V)} (hfr : FRSpec fr)
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
        ∀ B HK BK R M WN : ℕ, NInv W' B c → IntAll c →
          let p₀ : KP := ⟨fd₀.k, Fintype.card (Klein.SrcD fd₀.DQ fd₀.k), n₀, Bw₀, Pk₀.data.length, β₀, Rk₀, Pb₀, L₀,
            Klein.srcW (fd₀.P'.image fd₀.e) (faceLen fd₀.P' fd₀.e (redLen N ℓ δ₀))⟩
          let p₁ : KP := ⟨fd₁.k, Fintype.card (Klein.SrcD fd₁.DQ fd₁.k), n₁, Bw₁, Pk₁.data.length, β₁, Rk₁, Pb₁, L₁,
            Klein.srcW (fd₁.P'.image fd₁.e) (faceLen fd₁.P' fd₁.e (redLen N ℓ δ₁))⟩
          (nodeProg p₀ p₁).noDivR = true →
          (nodeProg p₀ p₁).regsOK (fun r => decide (r < R)) = true →
          KCmp I W' B HK BK (kStmt p₀ p₁) →
          2 * nodeH b w B HK BK < M → 2 * W' + 1 + M * M + M ≤ WN →
          ∃ c' t, ∃ o : Option (V → ℤ),
            Exec I W' (nodeProg p₀ p₁) c c' t ∧
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
            c'.output = c.output ∧
            ∃ d' t', Exec I WN (.seq (constsS R M (nodeH b w B HK BK) (W' + 1))
                (ModNat.toNat R M (nodeProg p₀ p₁))) (natOf R W' M (W' + 1) c) d' t' ∧
              t' ≤ 4 * t + 3 ∧ Sim R W' M (W' + 1) c' d' ∧ Consts R M (nodeH b w B HK BK) (W' + 1) d' ∧
              (∀ a ≤ W', c'.rmem a = if d'.nmem (W' + 1 + a) ≤ nodeH b w B HK BK
                then (d'.nmem (W' + 1 + a) : ℝ) else (d'.nmem (W' + 1 + a) : ℝ) - M) ∧
              ∀ m₀ m₁ w₀ w₁ ε : ℕ, m = P.card → P.card = m₀ + m₁ → 1 ≤ m₀ → 1 ≤ m₁ →
                w ≤ 2 * P.card → ε ≤ 10 ^ 12 → L₀ = ε * lg P.card → L₁ = ε * lg P.card →
                t ≤ 1000 * (cNegMach C).node P.card b m₀ w₀ m₁ w₁ + 10000 ∧
                t' ≤ 4000 * (cNegMach C).node P.card b m₀ w₀ m₁ w₁ + 40003 := by
  obtain ⟨fd₀, n₀, Bw₀, σ₀, Pk₀, fd₁, n₁, Bw₁, σ₁, Pk₁, hq₀, hq₁, H⟩ :=
    node_exec_cmp C hfr hmssp hS hB ℓ δ₀ δ₁ hδ₀ hδ₁
  refine ⟨fd₀, n₀, Bw₀, σ₀, Pk₀, fd₁, n₁, Bw₁, σ₁, Pk₁, hq₀, hq₁, ?_⟩
  intro m w b e ν ι hN hb L₀ L₁ Pb₀ Pb₁ β₀ β₁ Rk₀ Rk₁ Z M₀ Y S W' I c hM₀ hZ hbZ hK₀ hK₁ hk₀
    hk₁ ho₀ ho₁ hY hSz hIn hW hWL₀ hWL₁ hc hctx hx hTm hHm hSm hLm hD₀ hD₁ hz hpos₀ hpos₁ hE₀
    hE₁ B HK BK R M WN hI hZi p₀ p₁ hD hR hK hM hWN
  obtain ⟨⟨c', t, o, ex, ht, hpot, hstep, hout⟩, hC⟩ := H hN hb L₀ L₁ Pb₀ Pb₁ β₀ β₁ Rk₀ Rk₁ Z M₀
    Y S W' I c hM₀ hZ hbZ hK₀ hK₁ hk₀ hk₁ ho₀ ho₁ hY hSz hIn hW hWL₀ hWL₁ hc hctx hx hTm hHm hSm
    hLm hD₀ hD₁ hz hpos₀ hpos₁ hE₀ hE₁
  obtain ⟨d', t', e', ht', hS', hK', hrd⟩ := node_exec_nat (hC B HK BK hI hZi hD hK) ex hR hD hZi
    hM (nodeBf_le_nodeH b w B HK BK) hWN
  refine ⟨c', t, o, ex, ht, hpot, hstep, hout, d', t', e', ht', hS', hK', hrd,
    fun m₀ m₁ w₀ w₁ ε hmP hm h₀ h₁ hw hε hL₀ hL₁ => ?_⟩
  subst hmP
  have hbw : b ≤ w := hb ▸ card_bdry_le hN
  obtain ⟨hk₀', hn₀'⟩ := faceData_bounds fd₀ hq₀
  obtain ⟨hk₁', hn₁'⟩ := faceData_bounds fd₁ hq₁
  have hcost := node_exec_cost_le C (w₀ := w₀) (w₁ := w₁) hm h₀ h₁ hw hbw hk₀' hk₁' hn₀' hn₁' hε
    hL₀ hL₁
  have h1 := ht.trans hcost
  clear hcost ht hstep hpot ex e' hrd hS' hK' hC H
  generalize (cNegMach C).node P.card b m₀ w₀ m₁ w₁ = NN at h1 ⊢
  exact ⟨h1, by omega⟩

end NegSSSP

end PlanarFlow
