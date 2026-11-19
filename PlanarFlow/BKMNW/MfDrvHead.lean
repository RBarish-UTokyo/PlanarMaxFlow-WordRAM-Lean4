module

public import PlanarFlow.BKMNW.MfDrv
public import PlanarFlow.BKMNW.SepM

/-!
# The max-flow driver on the decomposition of the headline theorem

`maxflow_plane_cost_decM` (the decomposition `τ` computed with Miller's separator on the machine,
`runLCost ≤ (100000 + 11)² · 448 · (27 · 102256 + 25) · K · n · lg³ n + (100000 + 11)² · 28 · K₀ ·
n · lg n`) and `mfDrive` (the fixed driver program runs the recursion `arunL` on any
decomposition, frame by frame) together:

* **`mfDrive_decM`**: for subprograms meeting `MfSpec` on `lpreMap M` (with the subroutines of
  `planeOracles`), each call within `A ·` (its charge in `arunLCost`) `+ B` steps, the driver runs
  from the root frame of `τ` to the flow `arunL … τ [] (rotPerm _)` of the recursion (whose
  extension `runL`, restricted by `nlRun`, is a maximum flow of `M`) within
  `A · ((100000 + 11)² · 448 · (27 · 102256 + 25) · K · n · lg³ n + (100000 + 11)² · 28 · K₀ · n ·
  lg n) + B · asize τ + 2` steps.

Honest status: the four subprograms (`testS`, `leafS`, `splitS`, `nodeS`), the frame encodings
(`FIn`, `FOut`) and the per-call cost bounds are **parameters** (hypotheses `MfSpec`, `hl`,
`hn`); the number of calls `asize τ` is not bounded here.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit CombMap WordRAM WordRAM.Machine NegSSSP.Driver

universe w

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The max-flow driver on the decomposition of `maxflow_plane_cost_decM`** (see the module
docstring). -/
theorem mfDrive_decM (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    {I : Input} {W Hb : ℕ} {testS leafS splitS nodeS : Stmt} {G : Config → Prop}
    {FIn : MCall (lpreMap M) → ℕ → ℕ → Config → Prop} {FOut : FOutT (lpreMap M)}
    {tcm lcm scm ncm : MCall (lpreMap M) → ℕ} {A B : ℕ}
    (hS : MfSpec (lpreMap M) (planeOracles fun X => frRef X)
      (preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)) (preTerm (nlTerm M S))
      (preTerm (nlTerm M T)) I W Hb testS leafS splitS nodeS G FIn FOut tcm lcm scm ncm)
    (hl : ∀ Q Hs σ, tcm (.leaf Q, Hs, σ) + lcm (.leaf Q, Hs, σ) + 20 ≤
      A * (c.leaf (pdarts (lpreMap M) Q Hs).card + 4 * c.lin (Q.card + Hs.length)) + B)
    (hn : ∀ l r π Hs σ, tcm (.node l r π, Hs, σ) + scm (.node l r π, Hs, σ) +
      ncm (.node l r π, Hs, σ) + 80 ≤ A * nodeCharge (lpreMap M) c l r π Hs σ + B)
    (hHb : 0 < Hb) {eF h : ℕ} (c₀ : Config) (hc₀ : WordsBounded W c₀) (hg : G c₀)
    (r0 : c₀.nreg 3000 = 0) (r1 : c₀.nreg 3001 = 1) (r2 : c₀.nreg 3002 = Hb)
    (r3 : c₀.nreg 3003 = h) (m0 : c₀.nmem Hb = 0) (m1 : c₀.nmem (Hb + 1) = 0)
    (m2 : c₀.nmem (Hb + 2) = eF) (he : Hb + 5 ≤ eF) (hh : eF ≤ h) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    FIn (τ, [], rotPerm (lpreMap M)) (Hb + 5) eF c₀ →
    ∃ c' t, Exec I W (driver testS leafS splitS nodeS) c₀ c' t ∧
      t ≤ A * ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D)) +
        B * asize τ + 2 ∧
      FOut (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X)
          (preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)) (preTerm (nlTerm M S))
          (preTerm (nlTerm M T)) τ [] (rotPerm (lpreMap M))) (Hb + 5) eF c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro pc sc τ hin
  obtain ⟨-, hmax, hcost⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀ hc
  obtain ⟨c', t, ex, ht, -, hout, -⟩ := mfDrive hS hHb τ [] (rotPerm (lpreMap M)) c₀ hc₀ hg
    r0 r1 r2 r3 m0 m1 m2 he hh hin
  have hm := mcost_le c hl hn τ [] (rotPerm (lpreMap M))
  have ha : arunLCost (lpreMap M) c τ [] (rotPerm (lpreMap M)) ≤ runLCost (lpreMap M) c τ := by
    unfold runLCost; omega
  have hA := Nat.mul_le_mul_left A (ha.trans hcost)
  refine ⟨c', t, ex, by omega, hout, hmax⟩

/-- **`mfDrive_decM` with the number of calls bounded**: the decomposition of
`maxflow_plane_cost_decM` covers all the darts of `lpreMap M` and meets `Core`, so it has at most
`2 m + 1` calls (`m = τ.piece.card` the darts of `lpreMap M`): the driver takes at most
`A · ((100000+11)² · 448 · (27 · 102256 + 25) · K · n · lg³ n + (100000+11)² · 28 · K₀ · n · lg n)
+ B · (2 m + 1) + 2` steps. -/
theorem mfDrive_decM' (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _)
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀)
    {I : Input} {W Hb : ℕ} {testS leafS splitS nodeS : Stmt} {G : Config → Prop}
    {FIn : MCall (lpreMap M) → ℕ → ℕ → Config → Prop} {FOut : FOutT (lpreMap M)}
    {tcm lcm scm ncm : MCall (lpreMap M) → ℕ} {A B : ℕ}
    (hS : MfSpec (lpreMap M) (planeOracles fun X => frRef X)
      (preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)) (preTerm (nlTerm M S))
      (preTerm (nlTerm M T)) I W Hb testS leafS splitS nodeS G FIn FOut tcm lcm scm ncm)
    (hl : ∀ Q Hs σ, tcm (.leaf Q, Hs, σ) + lcm (.leaf Q, Hs, σ) + 20 ≤
      A * (c.leaf (pdarts (lpreMap M) Q Hs).card + 4 * c.lin (Q.card + Hs.length)) + B)
    (hn : ∀ l r π Hs σ, tcm (.node l r π, Hs, σ) + scm (.node l r π, Hs, σ) +
      ncm (.node l r π, Hs, σ) + 80 ≤ A * nodeCharge (lpreMap M) c l r π Hs σ + B)
    (hHb : 0 < Hb) {eF h : ℕ} (c₀ : Config) (hc₀ : WordsBounded W c₀) (hg : G c₀)
    (r0 : c₀.nreg 3000 = 0) (r1 : c₀.nreg 3001 = 1) (r2 : c₀.nreg 3002 = Hb)
    (r3 : c₀.nreg 3003 = h) (m0 : c₀.nmem Hb = 0) (m1 : c₀.nmem (Hb + 1) = 0)
    (m2 : c₀.nmem (Hb + 2) = eF) (he : Hb + 5 ≤ eF) (hh : eF ≤ h) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    FIn (τ, [], rotPerm (lpreMap M)) (Hb + 5) eF c₀ →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (driver testS leafS splitS nodeS) c₀ c' t ∧
      t ≤ A * ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D)) +
        B * (2 * τ.piece.card + 1) + 2 ∧
      FOut (τ, [], rotPerm (lpreMap M))
        (arunL (lpreMap M) (planeOracles fun X => frRef X)
          (preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)) (preTerm (nlTerm M S))
          (preTerm (nlTerm M T)) τ [] (rotPerm (lpreMap M))) (Hb + 5) eF c' ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) := by
  intro pc sc τ hin
  obtain ⟨hbal, -, -⟩ := maxflow_plane_cost_decM hM hrot hface hu hST e hsurj d₀ hc
  obtain ⟨c', t, ex, ht, hout, hmax⟩ := mfDrive_decM hM hrot hface hu hST e hsurj d₀ hc hS hl hn
    hHb c₀ hc₀ hg r0 r1 r2 r3 m0 m1 m2 he hh hin
  have hsz := asize_le (ADec.BalA.core hbal.2.2.2.2)
  have := Nat.mul_le_mul_left B hsz
  exact ⟨hbal.1, c', t, ex, ht.trans (Nat.add_le_add_right (Nat.add_le_add_left this _) 2),
    hout, hmax⟩

end MfDrv

end BKMNW

end PlanarFlow
