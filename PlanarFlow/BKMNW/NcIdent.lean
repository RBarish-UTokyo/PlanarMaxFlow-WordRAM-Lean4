module

public import PlanarFlow.BKMNW.NcHole
public import PlanarFlow.BKMNW.NcMath
public import PlanarFlow.BKMNW.NpMach
public import PlanarFlow.BKMNW.NcChs
public import PlanarFlow.BKMNW.NpPushC

/-!
# `c2s` / `s2c` of the machine at a hole: the unfolded form and the word bounds

* **`c2s_machNF`**: the `c2s` of the machine's node subroutines (`machNF gid I chs pch`) at a node
  call is `f + pch β ∅ (fixFrozen e … (f + st) π Del − f)` with `st` the machine's s-t flow on
  `c2sCap`, `β = c2sBeta`, `Del = delSet`, for **any** dart `e v` at each vertex of the piece map
  (`c2sG_eqE`); **`s2c_machNF`**: `s2c U f π H = −(c2s (U ∘ rev) (−f) π H)`.
* The bounds on the words of `c2sP` (all the flows are pseudoflows for capacities `0 ≤ U ≤ Z`):
  `IsPseudo.bound` (`|f| ≤ Z`), `c2sCap_le` (`c2sCap ≤ 2Z`), `STOut.bound` (`|st| ≤ 2Z`),
  **`f1_pseudo`** (`g + st` is a pseudoflow for `U`), and **`c2sParts`**: at a hole with the
  invariant `HoleC2S` and the specifications of the subroutines, `0 ≤ cap ≤ 2Z`, `|st| ≤ 2Z`,
  `|g + st| ≤ Z`, `|fixFrozen …| ≤ Z`, `|c2sG …| ≤ Z`; `HoleS2C.mirror` (the precondition of
  `s2c` is that of `c2s` on `U ∘ rev`, `−g`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open Finset Function Equiv Orbit CombMap MfDrv NsStep

universe w

section Bounds

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- A pseudoflow for capacities at most `Z` is bounded by `Z`. -/
lemma pseudo_bound {U f : D → ℤ} (hf : IsPseudo M U f) {Z : ℤ} (hU : ∀ d, U d ≤ Z) (y : D) :
    -Z ≤ f y ∧ f y ≤ Z := by
  have h1 := hf.le_cap y
  have h2 := hf.le_cap (M.rev y)
  rw [hf.antisymm y] at h2
  have := hU y; have := hU (M.rev y)
  constructor <;> omega

/-- The capacities of the maximum flow of `c2s` are at most `2Z`. -/
lemma c2sCap_le {U f : D → ℤ} (hf : IsPseudo M U f) (hU0 : ∀ d, 0 ≤ U d) {Z : ℤ}
    (hU : ∀ d, U d ≤ Z) (C : Finset V) (y : D) : c2sCap M U f C y ≤ 2 * Z := by
  have := (pseudo_bound hf hU y).1
  have := hU y
  have := hU0 y
  unfold c2sCap; split_ifs <;> omega

/-- A flow of an s-t flow output is bounded by the capacities. -/
lemma stOut_bound {c s : D → ℤ} {X Y : Finset V} (hs : STOut M c X Y s) {K : ℤ}
    (hc : ∀ y, c y ≤ K) (y : D) : -K ≤ s y ∧ s y ≤ K :=
  pseudo_bound hs.pseudo hc y

/-- **The flow after the maximum flow of `c2s` is a pseudoflow.** -/
lemma f1_pseudo {U g s : D → ℤ} (hg : IsPseudo M U g) {C H : Finset V}
    (hs : STOut M (c2sCap M U g C) C H s) : IsPseudo M U (g + s) := by
  refine ⟨fun d => by simp [hg.antisymm d, hs.pseudo.antisymm d]; ring, fun d => ?_⟩
  have h1 := hs.pseudo.le_cap d
  have h2 := hg.le_cap d
  simp only [Pi.add_apply]
  unfold c2sCap at h1
  split_ifs at h1 <;> omega

/-- **The words of `c2s` at a hole.** -/
theorem c2sParts (hM : M.IsPlane) {push : PushFn D V} (hpush : PushSpec M push)
    {U g : D → ℤ} (hU : ∀ d, 0 ≤ U d) {Z : ℤ} (hUZ : ∀ d, U d ≤ Z) {π : SPath M}
    {H : Finset V} (hh : HoleC2S M U g π H) {mssp : List D → (D → ℤ) → F → F → Option ℤ}
    (hmssp : MSSPSpecAt M mssp π) {fr : FRFun F} (hfr : FRSpec fr)
    {neg : (D → ℤ) → Option (F → ℤ)} (hneg : NegSSSPSpec M neg)
    {stflow : (D → ℤ) → Finset V → Finset V → D → ℤ} (hst : STFlowSpec M stflow)
    (e : V → D) (he : ∀ v, M.tail (e v) = v) (y : D) :
    (0 ≤ c2sCap M U g π.verts y ∧ c2sCap M U g π.verts y ≤ 2 * Z) ∧
    (-(2 * Z) ≤ stflow (c2sCap M U g π.verts) π.verts H y ∧
      stflow (c2sCap M U g π.verts) π.verts H y ≤ 2 * Z) ∧
    IsPseudo M U (g + stflow (c2sCap M U g π.verts) π.verts H) ∧
    (-Z ≤ g y ∧ g y ≤ Z) ∧
    (-Z ≤ (g + stflow (c2sCap M U g π.verts) π.verts H) y ∧
      (g + stflow (c2sCap M U g π.verts) π.verts H) y ≤ Z) ∧
    (-Z ≤ fixFrozen M e he mssp fr neg U (g + stflow (c2sCap M U g π.verts) π.verts H) π
        (delSet M U g π.verts) y ∧
      fixFrozen M e he mssp fr neg U (g + stflow (c2sCap M U g π.verts) π.verts H) π
        (delSet M U g π.verts) y ≤ Z) ∧
    (-Z ≤ c2sG M push mssp fr neg stflow U g π H y ∧
      c2sG M push mssp fr neg stflow U g π H y ≤ Z) := by
  obtain ⟨πH, hπH⟩ := hh.path
  have hs : STOut M (c2sCap M U g π.verts) π.verts H
      (stflow (c2sCap M U g π.verts) π.verts H) := by
    have := hst (c2sCap M U g π.verts) π πH (c2sCap_nonneg hh.pseudo π.verts)
      (by rw [hπH]; exact hh.disj)
    rwa [hπH] at this
  have hf₁ := f1_pseudo hh.pseudo hs
  have hcap : ∀ y, c2sCap M U g π.verts y ≤ 2 * Z := c2sCap_le hh.pseudo hU hUZ π.verts
  have hfix := (fixFrozen_spec (e := e) (he := he) hM hU hf₁ hmssp hfr hneg
    (delSet M U g π.verts)).1
  have hc2s := (c2sG_spec hM hpush hU hh.pseudo hh.disj hh.path hh.pre hmssp hfr hneg hst).pseudo
  exact ⟨⟨c2sCap_nonneg hh.pseudo _ y, hcap y⟩, stOut_bound hs hcap y, hf₁,
    pseudo_bound hh.pseudo hUZ y, pseudo_bound hf₁ hUZ y, pseudo_bound hfix hUZ y,
    pseudo_bound hc2s hUZ y⟩

/-- **The precondition of `s2c` is that of `c2s` on the reversed capacities and the opposite
flow.** -/
lemma HoleS2C.mirror {U g : D → ℤ} {π : SPath M} {H : Finset V} (hh : HoleS2C M U g π H) :
    HoleC2S M (fun d => U (M.rev d)) (-g) π H := by
  have hf' : IsPseudo M (fun d => U (M.rev d)) (-g) :=
    ⟨fun d => by simp [hh.pseudo.antisymm d], fun d => by
      have := hh.pseudo.le_cap (M.rev d); rw [hh.pseudo.antisymm d] at this
      simp only [Pi.neg_apply]; omega⟩
  have hre := fwdReach_mirror (U := U) hh.pseudo.antisymm (negSet M g π.verts) π.verts
  refine ⟨hf', hh.disj, hh.path, fun v hv => ?_⟩
  rw [posSet_neg, hre] at hv; rw [div_neg']; have := hh.pre v hv; omega

end Bounds

/-! ### The machine's `c2s` and `s2c` unfolded -/

section Mach

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The `c2s` of the machine's node subroutines** with any dart at each vertex. -/
theorem c2s_machNF (gid : D → ℕ) (I : WordRAM.Input)
    (chs : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → STFlow.StChoice (pmap h))
    (pch : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      PushFn (SDart (pdarts M x.1.piece x.2.1)) (SVert x.2.2 (pdarts M x.1.piece x.2.1)))
    (u : D → ℤ) (S T : Finset V) {l r : ADec M} {π : HSep M} {Hs : List (Finset V)}
    {σ : Perm D} (h : SCond M l r π Hs σ)
    (e : SVert σ (pdarts M (l.piece ∪ r.piece) Hs) → SDart (pdarts M (l.piece ∪ r.piece) Hs))
    (he : ∀ v, (pmap h.1).tail (e v) = v) (U f : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ)
    (πj : SPath (pmap h.1)) (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))) :
    (xCtxN M (machNF gid I chs pch) u S T l r π Hs σ h).O.c2s U f πj H =
      f + @id (SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ)
        (pch (.node l r π, Hs, σ) h.1 (c2sBeta (pmap h.1) U f πj.verts) ∅
        (fixFrozen (pmap h.1) e he (Klein.msspPlaneK (pmap h.1)) (frRef _)
          (negLay gid I (.node l r π, Hs, σ) h.1) U
          (f + @id (SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ)
            ((chs (.node l r π, Hs, σ) h.1).flow (c2sCap (pmap h.1) U f πj.verts) πj.verts H))
          πj (delSet (pmap h.1) U f πj.verts) - f)) :=
  c2sG_eqE e he _ _ _ _ _ U f πj H

/-- **The `s2c` of the machine's node subroutines** is its `c2s` on the reversed capacities and
the opposite flow, negated. -/
theorem s2c_machNF (gid : D → ℕ) (I : WordRAM.Input)
    (chs : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → STFlow.StChoice (pmap h))
    (pch : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) →
      PushFn (SDart (pdarts M x.1.piece x.2.1)) (SVert x.2.2 (pdarts M x.1.piece x.2.1)))
    (u : D → ℤ) (S T : Finset V) {l r : ADec M} {π : HSep M} {Hs : List (Finset V)}
    {σ : Perm D} (h : SCond M l r π Hs σ) (U f : SDart (pdarts M (l.piece ∪ r.piece) Hs) → ℤ)
    (πj : SPath (pmap h.1)) (H : Finset (SVert σ (pdarts M (l.piece ∪ r.piece) Hs))) :
    (xCtxN M (machNF gid I chs pch) u S T l r π Hs σ h).O.s2c U f πj H =
      -((xCtxN M (machNF gid I chs pch) u S T l r π Hs σ h).O.c2s
        (fun d => U ((pmap h.1).rev d)) (-f) πj H) := rfl

end Mach

end NcStep

end BKMNW

end PlanarFlow
