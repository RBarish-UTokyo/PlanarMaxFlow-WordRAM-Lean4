module

public import PlanarFlow.BKMNW.SepPX2
public import PlanarFlow.BKMNW.MfDrvFrame

/-!
# The driver on the extended frame

`mfSpecR_frame` / `mfDriveFrame` (`MfDrvFrame.lean`) restated with the input frames `FInLX`
(the frame with the decomposition record) and the split `splitSX sepP` (`SepSplit.lean`):

* **`mfSpecR_frameX`**: `mtProg`, `mlProg`, `splitSX sepP` (with `SepPSpecX sepP`) and any `nodeS`
  meeting `NodeSpecF` (on the frames `FInL`/`FOutL`; `FInLX → FInL`) meet `MfSpecR` for
  `FIn = FInLX ds Reach`, `FOut = FOutL`, room `rSpX sR`, split steps `scpX sT`;
* **`mfDriveFrameX`**: the fixed program `driver mtProg mlProg (splitSX sepP) nodeS` from a root
  frame holding `FInLX` ends with `FOutL` of the flow `arunL` within `mcost + 2` steps.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {O : PlaneOracles.{w}} {Reach : MCall M → Prop} {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ}
  {S T : Finset V} {Z : ℕ} {I : Input} {W Hb : ℕ} {sepP nodeS : Stmt} {sT : ℕ → ℕ → ℕ}
  {sR : ℕ → ℕ → ℕ → ℕ} {nc rN : MCall M → ℕ} {ds : DSys M}

/-- **The concrete test, leaf solver and extended split, with `sepP` and `nodeS` meeting their
specifications, meet `MfSpecR` on the extended frames.** -/
theorem mfSpecR_frameX (hsep : SepPSpecX M ds Reach gid ν u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) (hZ : 2 * Z ≤ W)
    (hnode : NodeSpecF M O Reach gid u S T Z I W Hb nodeS nc (rSpX M sR) rN) :
    MfSpecR M O u S T I W Hb mtProg mlProg (splitSX sepP) nodeS (fun _ => True)
      (FInLX M ds Reach gid ν u S T Z) (FOutL M gid u S T Z) (fun _ => 3)
      (fun x => 20 * (pdarts M x.1.piece x.2.1).card + 17) (scpX M sT) nc (fun _ => 0)
      (rSpX M sR) rN where
  g_stab _ _ _ _ _ _ := trivial
  in_stab _ _ _ _ _ h hm := h.stab hm
  out_stab _ _ _ _ _ _ h hm := h.stab hm
  test x d e h c hg hc r4 r5 r3 h1 h2 h3 hin :=
    mtProg_spec x d e h c hg hc r4 r5 r3 h1 h2 h3 hin.finL
  leaf Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 _ hin :=
    mlProg_spec O hZ Q Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hin.finL
  split l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin :=
    mfSplit_specX hsep hReach l r π Hs σ d e h c hg hc r4 r5 r3 h1 h2 h3 hrm hin
  node l r π Hs σ d e bl el er c hg hc a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 hrm hin hl hr :=
    hnode l r π Hs σ d e bl el er c hg hc a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 hrm hin.finL hl hr

/-- **The fixed driver program on the extended frames** (see the module docstring). -/
theorem mfDriveFrameX (hsep : SepPSpecX M ds Reach gid ν u S T Z I W sepP sT sR)
    (hReach : ∀ l r π Hs σ, Reach ((.node l r π, Hs, σ) : MCall M) →
      Reach (chL M l r π Hs σ) ∧ Reach (chR M l r π Hs σ)) (hZ : 2 * Z ≤ W)
    (hnode : NodeSpecF M O Reach gid u S T Z I W Hb nodeS nc (rSpX M sR) rN)
    (hHb : 0 < Hb) (τ : ADec M) (Hs : List (Finset V)) (σ : Perm D) {e h : ℕ} (c : Config)
    (hc : WordsBounded W c) (r0 : c.nreg 3000 = 0) (r1 : c.nreg 3001 = 1)
    (r2 : c.nreg 3002 = Hb) (r3 : c.nreg 3003 = h) (m0 : c.nmem Hb = 0)
    (m1 : c.nmem (Hb + 1) = 0) (m2 : c.nmem (Hb + 2) = e) (he : Hb + 5 ≤ e) (hh : e ≤ h)
    (hr : h + roomC M (fun _ => 0) (rSpX M sR) rN τ Hs σ ≤ W)
    (hin : FInLX M ds Reach gid ν u S T Z (τ, Hs, σ) (Hb + 5) e c) :
    ∃ c' t, Exec I W (driver mtProg mlProg (splitSX sepP) nodeS) c c' t ∧
      t ≤ mcost M (fun _ => 3) (fun x => 20 * (pdarts M x.1.piece x.2.1).card + 17) (scpX M sT) nc
        τ Hs σ + 2 ∧
      FOutL M gid u S T Z (τ, Hs, σ) (arunL M O u S T τ Hs σ) (Hb + 5) e c' ∧
      HeapKeep Hb h Hb e c c' ∧ c'.output = c.output := by
  obtain ⟨c', t, ex, ht, -, hout, -, -, hk, ho⟩ :=
    mfDriveR (mfSpecR_frameX hsep hReach hZ hnode) hHb τ Hs σ c hc trivial r0 r1 r2 r3 m0 m1 m2
      he hh hr hin
  exact ⟨c', t, ex, ht, hout, hk, ho⟩

end MfDrv

end BKMNW

end PlanarFlow
