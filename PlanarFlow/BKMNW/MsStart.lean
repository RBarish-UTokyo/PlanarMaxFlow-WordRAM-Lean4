module

public import PlanarFlow.BKMNW.MsSpec
public import PlanarFlow.Klein.IsoExecNat

/-!
# Klein's MSSP of a call from an explicit start (the target of an encoder)

`cMach_mssp_execNat` / `Klein.msspPlaneK_maskedNat` start the natural run of `kleinProgMN` from an
**existential** input and configuration (a classically chosen cut, the numbering
`Fintype.equivFin`, a classically chosen isolating weight, the trees of `klein_init_exists`). A
machine encoder computes its own. This file restates the run and its answers for **every**
explicit choice, so that an encoder only has to establish the hypotheses below:

* **`kleinM_natRun`**: the natural run of `kleinProgMN` from `natCfg c₀` for explicit Klein data
  (`Layout`, `KInput`, `KBnd`, `KOut`, `KTgt`, `KInit`, the compatible trees, the real memory
  `tripWt`, `tripφ`, `tripL`, `tripTh`, `tripH0`, the flags `MK`), any `Hc ≥ kleinHI`: within
  `4 · 36500000 (N lg N + f t lg N) + 3` steps, the flagged answers read exactly (`kOutN`);
* **`cut_odist_isDist`**: on **any** cut `C` of the dual graph minus the path (`BKMNW.Cut`), the
  distances of the cut from the root `j` to the copies of the faces are the distances of the dual
  graph minus the path from the face `C.root j`;
* **`cut_iso_answer`**: for **any** isolating weight `w` (`MSSP.IsoW`, `|w| ≤ #F'`) and any
  numbering `σ` of the darts of the cut, the answers on the isolating lengths divided by `N₁` are
  **`msspPlaneK M P.darts ℓ (C.root j) y`** at the faces `C.root j` along the path;
* **`mssp_explicit`**: both together: an encoder that writes, for some cut `C`, some isolating
  weight, some numbering and some Klein data meeting the hypotheses of `kleinM_exec`, the start
  `natCfg c₀` and the input words, makes `kleinProgMN` (hence the fixed `KleinFix.kNFM`,
  `kNFM_exec`) output `msspPlaneK` exactly, for every flagged root and every target.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MsCall

open Finset WordRAM WordRAM.Machine Klein MSSP STFlow DynTree

/-! ### The natural run from explicit Klein data -/

section Run

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ : D → ℤ}
  {n B t nD : ℕ} {ιv : V → ℕ} {ιg : D → ℕ} {ιf : F → ℕ} {ιe : D → ℕ} {σ : D ≃ Fin nD}
  {X : ℕ → V} {fl : ℕ → Bool} {P : Input}

/-- **Klein's masked program on natural words from an explicit start**: the hypotheses of
`kleinM_exec` (explicit layout, input words, trees, real memory and flags) and `kleinHI ≤ Hc`
give the natural run of `kleinProgMN` from `natCfg c₀`, with the flagged answers read exactly. -/
theorem kleinM_natRun (hWa : 9 * nD + 7 * n + k + 4 + 2 * t ≤ B) (hB : n + 2 * nD ≤ B)
    (hOUT : aOUT nD + kRank fl k * t ≤ B) (hRB : aRBM n k + kRank fl k * t ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1))
    (H : Hyp M k g S ℓ) (hR : SameReach M k g S ℓ) (hL : Layout M n ιv ιg ιf ιe)
    (hK : KInput M S ℓ σ ιv ιg ιf ιe P) (hG : KBnd k g σ n P) (hO : KOut M S σ ιv n k P)
    (hX : KTgt M k g S ℓ nD n ιv t X P) {T : DTree M.dual} {C : DTree M} {vs ts : List V}
    {fs cs : List F}
    (hI : KInit M σ ιv ιf n k T C vs ts fs cs P) (hoff : ∀ x, x ≠ C.root → ¬ T.InT (C.par x))
    (hCr : C.root = M.face (g 0))
    (hT : Compat T (tripSrc M k g 0) (tripDst M k g 0) (g (0 % k))
      (tpar (pieceGraph M S ℓ) (tripSrc M k g 0)))
    {c₀ : Config} (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀)
    (hwt : ∀ d, c₀.rmem (aWT + σ d) = tripWt M k g S ℓ 0 d)
    (hph : ∀ d, c₀.rmem (aPH nD + σ d) = tripφ S ℓ d) (htl : c₀.rmem (aTL nD) = tripL V S ℓ)
    (hth : c₀.rmem (aTH nD) = tripTh V S ℓ) (hh0 : c₀.rmem (aH0 nD) = tripH0 V S ℓ k)
    (hmk : ∀ j < k, c₀.nmem (aMK n + j) = if fl j then 1 else 0)
    (hr0 : ∀ r, ∃ z : ℤ, c₀.rreg r = z) (hm0 : ∀ a, ∃ z : ℤ, c₀.rmem a = z)
    {Hc : ℕ} (hHc : kleinHI V F S ℓ k ≤ Hc) :
    ∃ d' steps, Exec P (kleinWN B n Hc) (kleinProgMN B nD n k t Hc)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) d' steps ∧
      steps ≤ 4 * (140 * (n + 1) + 21 +
        kleinOpsM (Fintype.card V) (Fintype.card F) nD S.card k (kRank fl k) t * opCostE n +
        kleinExtM (Fintype.card V) (Fintype.card F) nD S.card k (kRank fl k) t) + 3 ∧
      (∀ j < k, fl j = true → ∀ i < t,
        kOutN nD n k t (B + 16 * (n + 1) + 1) d' (kRank fl j) i =
          odist (pieceGraph M S ℓ) (tripSrc M k g j) (X i)) ∧
      d'.output = c₀.output := by
  obtain ⟨c', steps, e, hsteps, -, hd, hout⟩ := kleinM_exec (B := B) (fl := fl) hWa hB hOUT hRB
    hP H hR hL hK hG hO hX hI hoff hCr hT hc₀ hwt hph htl hth hh0 hmk
  have hcmp := kleinProgM_cmpOK (B := B) (fl := fl) hWa hB hOUT hRB hP H hR hL hK hG hO hX hI
    hoff hCr hT hc₀ hwt hph htl hth hh0 hmk hHc
  have hW' : kleinWN B n Hc = 2 * (B + 16 * (n + 1)) + 1 + (2 * Hc + 1) * (2 * Hc + 1) +
      (2 * Hc + 1) := rfl
  obtain ⟨d', k', ex, hk', hS', -, -, -, -, -⟩ := ModNat.ExecCmp.toNat_consts (hcmp.exec e)
    (kleinProgM_regsOK _ _ _ _ _) (kleinProgM_noDivR _ _ _ _ _) (M := 2 * Hc + 1) (by omega)
    (β := B + 16 * (n + 1) + 1) (W' := kleinWN B n Hc) (by omega) (by omega) (by omega)
    (by omega) (d := natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀)
    (sim_natCfg (by omega) (by omega) hr0 (fun a => hm0 a))
    (wb_natCfg hc₀ (by omega) (by omega) (by omega))
  refine ⟨d', k', ex, by omega, fun j hj hfj i hi => ?_, by rw [hS'.output, hout]⟩
  have hq : kRank fl j * t + t ≤ kRank fl k * t := by
    have := Nat.mul_le_mul_right t (kRank_succ_le fl hj hfj)
    rw [Nat.add_mul, one_mul] at this
    exact this
  refine kOutN_of_sim hS' (by unfold aRBM at hRB ⊢; omega)
    (by unfold aOUT at hOUT ⊢; omega) (hd j hj hfj i hi) fun z hz => ?_
  obtain ⟨hz0, hz1⟩ := odist_le_tripW H hz
  have h1 : ((z : ℤ) : ℝ) ≤ Hc := by
    have : ((z : ℤ) : ℝ) ≤ tripW S ℓ := by exact_mod_cast hz1
    linarith [tripW_le_kleinHI (V := V) (F := F) (S := S) (ℓ := ℓ) (k := k)]
  refine ⟨hz0, ?_⟩
  have h2 : z ≤ (Hc : ℤ) := by exact_mod_cast h1
  omega

end Run

/-! ### The answers on any cut -/

section CutAns

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {D' V' F' : Type*} [Fintype D'] [DecidableEq D']
  [Fintype V'] [DecidableEq V'] [Fintype F'] [DecidableEq F'] {ℓ : D → ℤ} {L : List D}

/-- **On any cut, the distances of the cut from a root are the distances of the dual graph
minus `L` from the face of the root.** -/
theorem cut_odist_isDist (C : Cut M ℓ L D' V' F') {j : ℕ} (hj : j < C.k) :
    IsDist ((M.dualGraph ℓ).restrict fun e => e ∉ L) (C.root j)
      (fun y => odist (pieceGraph C.map C.piece C.len) (C.map.tail (C.g j)) (C.vx y)) := by
  classical
  have hD := isDist_odist (G := pieceGraph C.map C.piece C.len)
    (fun a => C.hyp.nonneg a.1 a.2) (C.map.tail (C.g j))
  refine isDist_of_embed (G := (M.dualGraph ℓ).restrict fun e => e ∉ L)
    (G' := pieceGraph C.map C.piece C.len) (arc := C.arc) C.vx_inj
    C.tail_arc C.head_arc C.len_arc ?_ (C.root_ne j hj) ?_ ?_ hD
  · intro b
    rcases C.cover b.1 b.2 with ⟨e, he⟩ | ⟨i, hi, h1, -, -⟩
    · exact Or.inl ⟨e, Subtype.ext he⟩
    · right; intro y; change C.map.tail b.1 ≠ _; rw [h1]; exact C.root_ne i hi y
  · intro b hb
    change C.map.tail b.1 = C.map.tail (C.g j) at hb
    rcases C.cover b.1 b.2 with ⟨e, he⟩ | ⟨i, hi, h1, h2, h3⟩
    · rw [← he, C.tail_arc] at hb
      exact absurd hb.symm (C.root_ne j hj _)
    · have hij : i = j := C.hyp.face.inj i hi j hj (h1.symm.trans hb)
      subst hij
      exact ⟨h2, h3⟩
  · obtain ⟨d, hd, h1⟩ := C.pend j hj
    exact ⟨⟨d, hd⟩, h1⟩

/-- **The answers of the cut on any isolating lengths, divided by `N₁`, are `msspPlaneK`** at
the faces along the path: for any cut `C` along a simple path `P` of a plane map with transitive
rotations and faces, any isolating weight `w` of the cut map (`|w| ≤ #F'`) and any injective
numbering `ι` of its darts below `#D'`. -/
theorem cut_iso_answer (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (P : SPath M) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e)
    (C : Cut M ℓ P.darts D' V' F') {w : D' → ℤ} (hwB : ∀ d, |w d| ≤ Fintype.card F')
    {ι : D' → ℕ} (hιm : ∀ d, ι d < Fintype.card D') {j : ℕ} (hj : j < C.k)
    (hx : C.root j ∈ P.faces) (y : F) :
    (odist (pieceGraph C.map C.piece (isoLen (Fintype.card V') (Fintype.card D')
        (Fintype.card F') w ι C.len)) (C.map.tail (C.g j)) (C.vx y)).map
        (· / (isoN1 (Fintype.card V') (Fintype.card D') (Fintype.card F') : ℤ)) =
      msspPlaneK M P.darts ℓ (C.root j) y := by
  rw [odist_isoLen hwB le_rfl hιm C.hyp.nonneg,
    Klein.msspPlaneK_eq_of_isDist hM hrot hface P ℓ hnn hx (cut_odist_isDist C hj)]

/-- **The MSSP of a call from an explicit start**: for any cut `C` along `P` with `SameReach`
for its perturbed lengths, any isolating weight `w` (`MSSP.IsoW`, `|w| ≤ #F'`), any numbering
`σ` of the darts of the cut, and Klein data for the isolating lengths
`len' = isoLen #V' #D' #F' w σ C.len` meeting the hypotheses of `kleinM_exec`, with
`kleinHI ≤ Hc`, the natural run of `kleinProgMN` from `natCfg c₀` ends with
`(kOutN … (kRank fl j) i).map (· / N₁) = msspPlaneK M P.darts ℓ (C.root j) y` for every
flagged root `j` whose face is along the path and every target `X i = C.vx y`. -/
theorem mssp_explicit (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (P : SPath M) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) (C : Cut M ℓ P.darts D' V' F')
    (hRp : SameReach C.map C.k C.g C.piece (pert C.len))
    {w : D' → ℤ} (hw : IsoW C.map (C.map.face (C.g 0)) w) (hwB : ∀ d, |w d| ≤ Fintype.card F')
    {nD : ℕ} (σ : D' ≃ Fin nD) (hnD : nD = Fintype.card D')
    {n B t : ℕ} {ιv : V' → ℕ} {ιg : D' → ℕ} {ιf : F' → ℕ} {ιe : D' → ℕ}
    {X : ℕ → V'} {fl : ℕ → Bool} {Pin : Input}
    (hWa : 9 * nD + 7 * n + C.k + 4 + 2 * t ≤ B) (hB : n + 2 * nD ≤ B)
    (hOUT : aOUT nD + kRank fl C.k * t ≤ B) (hRB : aRBM n C.k + kRank fl C.k * t ≤ B)
    (hP : ∀ i, Pin.data.getD i 0 ≤ B + 16 * (n + 1))
    (hL : Layout C.map n ιv ιg ιf ιe)
    (hK : KInput C.map C.piece (isoLen (Fintype.card V') (Fintype.card D') (Fintype.card F') w
      (fun d => (σ d : ℕ)) C.len) σ ιv ιg ιf ιe Pin)
    (hG : KBnd C.k C.g σ n Pin) (hO : KOut C.map C.piece σ ιv n C.k Pin)
    (hX : KTgt C.map C.k C.g C.piece (isoLen (Fintype.card V') (Fintype.card D')
      (Fintype.card F') w (fun d => (σ d : ℕ)) C.len) nD n ιv t X Pin)
    {T : DTree C.map.dual} {C₀ : DTree C.map} {vs ts : List V'} {fs cs : List F'}
    (hI : KInit C.map σ ιv ιf n C.k T C₀ vs ts fs cs Pin)
    (hoff : ∀ x, x ≠ C₀.root → ¬ T.InT (C₀.par x)) (hCr : C₀.root = C.map.face (C.g 0))
    (hT : Compat T (tripSrc C.map C.k C.g 0) (tripDst C.map C.k C.g 0) (C.g (0 % C.k))
      (tpar (pieceGraph C.map C.piece (isoLen (Fintype.card V') (Fintype.card D')
        (Fintype.card F') w (fun d => (σ d : ℕ)) C.len)) (tripSrc C.map C.k C.g 0)))
    {c₀ : Config} (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀)
    (hwt : ∀ d, c₀.rmem (aWT + σ d) = tripWt C.map C.k C.g C.piece (isoLen (Fintype.card V')
      (Fintype.card D') (Fintype.card F') w (fun d => (σ d : ℕ)) C.len) 0 d)
    (hph : ∀ d, c₀.rmem (aPH nD + σ d) = tripφ C.piece (isoLen (Fintype.card V')
      (Fintype.card D') (Fintype.card F') w (fun d => (σ d : ℕ)) C.len) d)
    (htl : c₀.rmem (aTL nD) = tripL V' C.piece (isoLen (Fintype.card V') (Fintype.card D')
      (Fintype.card F') w (fun d => (σ d : ℕ)) C.len))
    (hth : c₀.rmem (aTH nD) = tripTh V' C.piece (isoLen (Fintype.card V') (Fintype.card D')
      (Fintype.card F') w (fun d => (σ d : ℕ)) C.len))
    (hh0 : c₀.rmem (aH0 nD) = tripH0 V' C.piece (isoLen (Fintype.card V') (Fintype.card D')
      (Fintype.card F') w (fun d => (σ d : ℕ)) C.len) C.k)
    (hmk : ∀ j < C.k, c₀.nmem (aMK n + j) = if fl j then 1 else 0)
    (hr0 : ∀ r, ∃ z : ℤ, c₀.rreg r = z) (hm0 : ∀ a, ∃ z : ℤ, c₀.rmem a = z)
    {Hc : ℕ} (hHc : kleinHI V' F' C.piece (isoLen (Fintype.card V') (Fintype.card D')
      (Fintype.card F') w (fun d => (σ d : ℕ)) C.len) C.k ≤ Hc) :
    ∃ d' steps, Exec Pin (kleinWN B n Hc) (kleinProgMN B nD n C.k t Hc)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) d' steps ∧
      steps ≤ 4 * (140 * (n + 1) + 21 +
        kleinOpsM (Fintype.card V') (Fintype.card F') nD C.piece.card C.k (kRank fl C.k) t *
          opCostE n +
        kleinExtM (Fintype.card V') (Fintype.card F') nD C.piece.card C.k (kRank fl C.k) t) + 3 ∧
      (∀ j < C.k, fl j = true → C.root j ∈ P.faces → ∀ i < t, ∀ y, X i = C.vx y →
        (kOutN nD n C.k t (B + 16 * (n + 1) + 1) d' (kRank fl j) i).map
          (· / (isoN1 (Fintype.card V') (Fintype.card D') (Fintype.card F') : ℤ)) =
          msspPlaneK M P.darts ℓ (C.root j) y) ∧
      d'.output = c₀.output := by
  subst hnD
  have hι : Function.Injective fun d => (σ d : ℕ) := fun a b h => σ.injective (Fin.ext h)
  have hιm : ∀ d, ((σ d : ℕ)) < Fintype.card D' := fun d => (σ d).isLt
  have H := C.hyp.hypIso hw hwB le_rfl hι hιm
  have hR₀ : SameReach C.map C.k C.g C.piece C.len :=
    sameReach_congr (fun x y => (isPerturb_pert C.map C.piece C.len).reach_iff.symm) hRp
  have hR : SameReach C.map C.k C.g C.piece (isoLen (Fintype.card V') (Fintype.card D')
      (Fintype.card F') w (fun d => (σ d : ℕ)) C.len) :=
    sameReach_congr (fun x y => reach_iso_iff hwB le_rfl hιm C.hyp.nonneg) hR₀
  obtain ⟨d', steps, ex, hs, hans, ho⟩ := kleinM_natRun hWa hB hOUT hRB hP H hR hL hK hG hO hX
    hI hoff hCr hT hc₀ hwt hph htl hth hh0 hmk hr0 hm0 hHc
  refine ⟨d', steps, ex, hs, fun j hj hfj hx i hi y hy => ?_, ho⟩
  have e : tripSrc C.map C.k C.g j = C.map.tail (C.g j) := by
    unfold tripSrc; rw [Nat.mod_eq_of_lt hj]
  rw [hans j hj hfj i hi, e, hy]
  exact cut_iso_answer hM hrot hface P hnn C hwB hιm hj hx y

end CutAns

end MsCall

end BKMNW

end PlanarFlow
