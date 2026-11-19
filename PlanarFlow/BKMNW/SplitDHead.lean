module

public import PlanarFlow.BKMNW.HeadDecA
public import PlanarFlow.BKMNW.SplitD
public import PlanarFlow.BKMNW.SmallD

/-!
# The headline with the explicit split functions

`maxflow_plane_cost_decA` for `spS = spSD`, `spH = spHD` (the split chain as functions of the
piece and of choice functions, `PlanarFlow.BKMNW.SplitD`), on the preprocessed map `lpreMap M`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

universe w

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap

section Main

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The explicit split functions meet `SplitFns` on `lpreMap M`**, for choice functions meeting
their specifications (pendant vertices `pendQ`). -/
theorem splitFns_lpreD (S T : Finset V) (pc : PcChoice _ _)
    (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    (σf : Finset _ → List (Finset _) → Perm _)
    (hσf : ∀ P Hs, CInv (lpreMap M) (pendQ _) P Hs →
      PMap (lpreMap M) (pdarts (lpreMap M) (core (lpreMap M) (pendQ _) P) Hs) Hs (σf P Hs)) :
    SplitFns (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000
      (CInv (lpreMap M) (pendQ _)) (spSD (lpreMap M) pc sc σf (pendQ _))
      (spHD (lpreMap M) pc sc σf (pendQ _))
      (smC (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000) := by
  obtain ⟨h1, h2, h3⟩ := pendQ_hyps (hrot := nlMap_rotTrans) (nlE_tail (M := M)) (nlTerm M S)
    (nlTerm M T)
  exact splitFns_D (preMap_loopless nlMap_loopless nlE_tail) h1 h2 h3 pc hpc sc hsc σf hσf

/-- **Maximum flow in plane graphs in `O(n log³ n)` on the explicit split functions**:
`maxflow_plane_cost_decA` for `τ = decA (lpreMap M) (spSD …) (spHD …) smC 100000 univ [] true`,
the splits being the explicit chain (Miller's separator, pruning, certificate, classes, two
groups by a scan, runs) for any choice functions meeting their specifications (Miller's separator
of each core piece map, cut-vertex holes, heavy components, anchors, orders, the rotation of each
core piece map); the small pieces are still decomposed by `smC` (chosen). Constants as in
`maxflow_plane_cost`. -/
theorem maxflow_plane_cost_decD (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) (pc : PcChoice _ _)
    (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    (σf : Finset _ → List (Finset _) → Perm _)
    (hσf : ∀ P Hs, CInv (lpreMap M) (pendQ _) P Hs →
      PMap (lpreMap M) (pdarts (lpreMap M) (core (lpreMap M) (pendQ _) P) Hs) Hs (σf P Hs))
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    let τ := decA (lpreMap M) (spSD (lpreMap M) pc sc σf (pendQ _))
      (spHD (lpreMap M) pc sc σf (pendQ _))
      (smC (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000) 100000 univ [] true
    BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap M) c τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) :=
  maxflow_plane_cost_decA hM hrot hface hu hST (splitFns_lpreD S T pc hpc sc hsc σf hσf) hc

/-- **All three subroutines explicit** (`splitFns_D` with the small pieces by `smD` with the
picking function `pc.pick`): `SplitFns … (spSD …) (spHD …) (smD M pc.pick S T)`. -/
theorem splitFns_DD {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} (hloop : ∀ d, M.head d ≠ M.tail d)
    {S T Q : Finset V} (hSTQ : S ∪ T ⊆ Q)
    (hQdeg : ∀ q ∈ Q, ∀ d d', M.tail d = q → M.tail d' = q → d = d')
    (hQ5 : ∀ d, ¬ (M.tail d ∈ Q ∧ M.head d ∈ Q)) (pc : PcChoice D V)
    (hpc : ∀ P Hs, pc.OK M Q P Hs) (sc : List (Finset V) → ℕ → ℕ → ScChoice M)
    (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W) (σf : Finset D → List (Finset V) → Perm D)
    (hσf : ∀ P Hs, CInv M Q P Hs → PMap M (pdarts M (core M Q P) Hs) Hs (σf P Hs)) :
    SplitFns M S T 9 100000 (CInv M Q) (spSD M pc sc σf Q) (spHD M pc sc σf Q)
      (smD M pc.pick S T) := by
  have hF := splitFns_D hloop hSTQ hQdeg hQ5 pc hpc sc hsc σf hσf
  exact ⟨fun P Hs hP hs ht b => smD_spec (by norm_num) (by norm_num) hloop
    (fun t ht => hQdeg t (hSTQ ht)) (hpc ∅ []).pick _ P Hs rfl hP hs ht b, hF.size, hF.hole⟩

/-- `splitFns_DD` on `lpreMap M`. -/
theorem splitFns_lpreDD (S T : Finset V) (pc : PcChoice _ _)
    (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    (σf : Finset _ → List (Finset _) → Perm _)
    (hσf : ∀ P Hs, CInv (lpreMap M) (pendQ _) P Hs →
      PMap (lpreMap M) (pdarts (lpreMap M) (core (lpreMap M) (pendQ _) P) Hs) Hs (σf P Hs)) :
    SplitFns (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 100000
      (CInv (lpreMap M) (pendQ _)) (spSD (lpreMap M) pc sc σf (pendQ _))
      (spHD (lpreMap M) pc sc σf (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T))) := by
  obtain ⟨h1, h2, h3⟩ := pendQ_hyps (hrot := nlMap_rotTrans) (nlE_tail (M := M)) (nlTerm M S)
    (nlTerm M T)
  exact splitFns_DD (preMap_loopless nlMap_loopless nlE_tail) h1 h2 h3 pc hpc sc hsc σf hσf

/-- **Maximum flow in plane graphs in `O(n log³ n)` with all three subroutines explicit**:
`maxflow_plane_cost_decA` for `τ = decA (lpreMap M) (spSD …) (spHD …) (smD … pc.pick …) 100000
univ [] true`, for any choice functions `pc`, `sc`, `σf` meeting their specifications. -/
theorem maxflow_plane_cost_decDD (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T) (pc : PcChoice _ _)
    (hpc : ∀ P Hs, pc.OK (lpreMap M) (pendQ _) P Hs)
    (sc : List (Finset _) → ℕ → ℕ → ScChoice (lpreMap M)) (hsc : ∀ Hs A W, (sc Hs A W).OK Hs A W)
    (σf : Finset _ → List (Finset _) → Perm _)
    (hσf : ∀ P Hs, CInv (lpreMap M) (pendQ _) P Hs →
      PMap (lpreMap M) (pdarts (lpreMap M) (core (lpreMap M) (pendQ _) P) Hs) Hs (σf P Hs))
    {c : SubCosts} {K K₀ : ℕ} (hc : c.Bounds K K₀) :
    let τ := decA (lpreMap M) (spSD (lpreMap M) pc sc σf (pendQ _))
      (spHD (lpreMap M) pc sc σf (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T))) 100000 univ [] true
    BalDecA (lpreMap M) (preTerm (nlTerm M S)) (preTerm (nlTerm M T)) 9 6 100000 τ ∧
      IsMax M u S T (nlRun M u S T τ (planeOracles fun X => frRef X)) ∧
      runLCost (lpreMap M) c τ ≤
        (100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * K * Fintype.card D *
            lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * K₀ * Fintype.card D * lg (Fintype.card D) :=
  maxflow_plane_cost_decA hM hrot hface hu hST (splitFns_lpreDD S T pc hpc sc hsc σf hσf) hc

end Main

end BKMNW

end PlanarFlow
