module

public import PlanarFlow.BKMNW.MsRunA

/-!
# The MSSP call, part B: the explicit Klein start and the answers read back

* **`KStart`**: the data an encoder must produce for Klein's run of a call (a cut `C` along the
  path with `SameReach`, an isolating weight `w`, a numbering `σ`, and the Klein data of
  `mssp_explicit` for the isolating lengths `kLen C w σ`), bundled;
* `KStart.run`: the natural run of `kleinProgMN` and its answers (`mssp_explicit`);
* **`kAns_read`**: the value `mrVal` read back from a memory agreeing with the end of that run
  at a flagged slot and a target is the word `msW` of `msspPlaneK` (the answer divided by `N₁`,
  `0` when there is none).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open Finset WordRAM WordRAM.Machine Klein MSSP STFlow DynTree

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

/-- The isolating lengths of a cut for the weight `w` and the numbering `σ`. -/
noncomputable abbrev kLen {ℓ : D → ℤ} {L : List D} (C : Cut M ℓ L (CutD M L) (CutV M L) (CutF M L))
    (w : CutD M L → ℤ) {nD : ℕ} (σ : CutD M L ≃ Fin nD) : CutD M L → ℤ :=
  isoLen (Fintype.card (CutV M L)) (Fintype.card (CutD M L)) (Fintype.card (CutF M L)) w
    (fun d => (σ d : ℕ)) C.len

/-- The scale `N₁` of the isolating lengths of the cut along `L`. -/
noncomputable abbrev kN1 (M : CombMap D V F) (L : List D) : ℕ :=
  isoN1 (Fintype.card (CutV M L)) (Fintype.card (CutD M L)) (Fintype.card (CutF M L))

/-- **The explicit Klein start of an MSSP call**: the hypotheses of `mssp_explicit`. -/
structure KStart (P : SPath M) (ℓ : D → ℤ)
    (C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts))
    (w : CutD M P.darts → ℤ) (nD : ℕ) (σ : CutD M P.darts ≃ Fin nD) (n B t : ℕ)
    (ιv : CutV M P.darts → ℕ) (ιg : CutD M P.darts → ℕ) (ιf : CutF M P.darts → ℕ)
    (ιe : CutD M P.darts → ℕ) (X : ℕ → CutV M P.darts) (fl : ℕ → Bool) (Pin : Input)
    (T : DTree C.map.dual) (C₀ : DTree C.map) (vs ts : List (CutV M P.darts))
    (fs cs : List (CutF M P.darts)) (c₀ : Config) (Hc : ℕ) : Prop where
  hRp : SameReach C.map C.k C.g C.piece (pert C.len)
  hw : IsoW C.map (C.map.face (C.g 0)) w
  hwB : ∀ d, |w d| ≤ Fintype.card (CutF M P.darts)
  hnD : nD = Fintype.card (CutD M P.darts)
  hWa : 9 * nD + 7 * n + C.k + 4 + 2 * t ≤ B
  hB : n + 2 * nD ≤ B
  hOUT : aOUT nD + kRank fl C.k * t ≤ B
  hRB : aRBM n C.k + kRank fl C.k * t ≤ B
  hP : ∀ i, Pin.data.getD i 0 ≤ B + 16 * (n + 1)
  hL : Layout C.map n ιv ιg ιf ιe
  hK : KInput C.map C.piece (kLen C w σ) σ ιv ιg ιf ιe Pin
  hG : KBnd C.k C.g σ n Pin
  hO : KOut C.map C.piece σ ιv n C.k Pin
  hX : KTgt C.map C.k C.g C.piece (kLen C w σ) nD n ιv t X Pin
  hI : KInit C.map σ ιv ιf n C.k T C₀ vs ts fs cs Pin
  hoff : ∀ x, x ≠ C₀.root → ¬ T.InT (C₀.par x)
  hCr : C₀.root = C.map.face (C.g 0)
  hT : Compat T (tripSrc C.map C.k C.g 0) (tripDst C.map C.k C.g 0) (C.g (0 % C.k))
    (tpar (pieceGraph C.map C.piece (kLen C w σ)) (tripSrc C.map C.k C.g 0))
  hc₀ : WordsBounded (B + 16 * (n + 1)) c₀
  hwt : ∀ d, c₀.rmem (aWT + σ d) = tripWt C.map C.k C.g C.piece (kLen C w σ) 0 d
  hph : ∀ d, c₀.rmem (aPH nD + σ d) = tripφ C.piece (kLen C w σ) d
  htl : c₀.rmem (aTL nD) = tripL (CutV M P.darts) C.piece (kLen C w σ)
  hth : c₀.rmem (aTH nD) = tripTh (CutV M P.darts) C.piece (kLen C w σ)
  hh0 : c₀.rmem (aH0 nD) = tripH0 (CutV M P.darts) C.piece (kLen C w σ) C.k
  hmk : ∀ j < C.k, c₀.nmem (aMK n + j) = if fl j then 1 else 0
  hr0 : ∀ r, ∃ z : ℤ, c₀.rreg r = z
  hm0 : ∀ a, ∃ z : ℤ, c₀.rmem a = z
  hHc : kleinHI (CutV M P.darts) (CutF M P.darts) C.piece (kLen C w σ) C.k ≤ Hc

/-- The step bound of Klein's run of a start. -/
def kSteps (nV nF nD nS n k f t : ℕ) : ℕ :=
  4 * (140 * (n + 1) + 21 + kleinOpsM nV nF nD nS k f t * opCostE n +
    kleinExtM nV nF nD nS k f t) + 3

/-- **The run of an explicit start** (`mssp_explicit`). -/
theorem KStart.run (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans) {P : SPath M}
    {ℓ : D → ℤ} (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e)
    {C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts)}
    {w : CutD M P.darts → ℤ} {nD : ℕ} {σ : CutD M P.darts ≃ Fin nD} {n B t : ℕ}
    {ιv : CutV M P.darts → ℕ} {ιg : CutD M P.darts → ℕ} {ιf : CutF M P.darts → ℕ}
    {ιe : CutD M P.darts → ℕ} {X : ℕ → CutV M P.darts} {fl : ℕ → Bool} {Pin : Input}
    {T : DTree C.map.dual} {C₀ : DTree C.map} {vs ts : List (CutV M P.darts)}
    {fs cs : List (CutF M P.darts)} {c₀ : Config} {Hc : ℕ}
    (h : KStart P ℓ C w nD σ n B t ιv ιg ιf ιe X fl Pin T C₀ vs ts fs cs c₀ Hc) :
    ∃ d' steps, Exec Pin (kleinWN B n Hc) (kleinProgMN B nD n C.k t Hc)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) d' steps ∧
      steps ≤ kSteps (Fintype.card (CutV M P.darts)) (Fintype.card (CutF M P.darts)) nD
        C.piece.card n C.k (kRank fl C.k) t ∧
      (∀ j < C.k, fl j = true → C.root j ∈ P.faces → ∀ i < t, ∀ y, X i = C.vx y →
        (kOutN nD n C.k t (B + 16 * (n + 1) + 1) d' (kRank fl j) i).map
          (· / (kN1 M P.darts : ℤ)) = msspPlaneK M P.darts ℓ (C.root j) y) ∧
      d'.output = c₀.output :=
  mssp_explicit hM hrot hface P hnn C h.hRp h.hw h.hwB σ h.hnD h.hWa h.hB h.hOUT h.hRB h.hP
    h.hL h.hK h.hG h.hO h.hX h.hI h.hoff h.hCr h.hT h.hc₀ h.hwt h.hph h.htl h.hth h.hh0 h.hmk
    h.hr0 h.hm0 h.hHc

/-- **The value read back is the word of the answer**: if the memory `mem` agrees with the end
`d'` of Klein's run at the reach bit `aRBM n k + s t + τ` and at the answer word
`β + aOUT nD + s t + τ` of the slot `s = kRank fl j` of a flagged root and a target `τ`, and the
answer divided by `N₁` is `msspPlaneK M P.darts ℓ x y`, then the read-back value is
`(msspPlaneK … x y).getD 0` as a natural word. -/
theorem kAns_read {P : SPath M} {ℓ : D → ℤ} {nD n k t β N1 s τ : ℕ} {d' : Config}
    {mem : ℕ → ℕ} {x y : F}
    (h1 : mem (aRBM n k + (s * t + τ)) = d'.nmem (aRBM n k + s * t + τ))
    (h2 : mem (β + aOUT nD + (s * t + τ)) = d'.nmem (β + (aOUT nD + s * t + τ)))
    (hans : (kOutN nD n k t β d' s τ).map (· / (N1 : ℤ)) = msspPlaneK M P.darts ℓ x y) :
    (if mem (aRBM n k + (s * t + τ)) = 1 then mem (β + aOUT nD + (s * t + τ)) / N1 else 0) =
      ((msspPlaneK M P.darts ℓ x y).getD 0).toNat := by
  rw [← hans, h1, h2]
  unfold kOutN
  split_ifs with hc
  · simp only [Option.map_some, Option.getD_some]
    rw [show ((d'.nmem (β + (aOUT nD + s * t + τ)) : ℤ) / (N1 : ℤ)) =
      ((d'.nmem (β + (aOUT nD + s * t + τ)) / N1 : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast]
  · rfl

end MsCall

end BKMNW

end PlanarFlow
