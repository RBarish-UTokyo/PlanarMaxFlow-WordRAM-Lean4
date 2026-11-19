module

public import PlanarFlow.BKMNW.MfMainO
public import PlanarFlow.NegSSSP.Relab

/-!
# The machine subroutines of a call: negative-length shortest paths from the run of `negFix`

The fixed program `negFix` (`PlanarFlow/NegSSSP/`, `cMach_negsssp_exec_gd`) computes, from the
root configuration `rootCfgP g M ℓ (repsN M.dual g.gd)` of a map `M` with identifiers `g`, **some**
outcome `o` with `PotOut (M.dual.graph ℓ) o`, written in the outcome region (`Res`). A feasible
potential is not unique, so the output depends on `g` (the numbering of the frame): the subroutine
is a function of the call (`MOFam`, `PlanarFlow/BKMNW/LocalO.lean`).

* `NegPre` (the preconditions of the machine theorem: plane, transitive rotations and faces, the
  loops of the dual of nonnegative length), `NegRun` (a run of `negFix` from the root
  configuration, word bound `rtW`), `NegEnc` (the outcome region holds `o`, `Res`).
* **`negMach g M I`**: the outcome encoded in the final configuration of the run of `negFix` (an
  outcome `o` with `NegEnc o` at the end of a run and `PotOut o`) when there is one, otherwise the
  reference implementation `negSSSPImpl`. **`negMach_spec`**: it meets `NegSSSPSpec` on every map.
  **`negMach_run`**: under `NegPre`, the run exists within the bound of `cMach_negsssp_exec_gd`
  (`(10¹² + 1 + fsKC + 80) · (cMach C C₀).negsssp n + fsKC + 22 + 12 n + 4610`), and **every** run
  (`Exec.det`) ends with `negMach g M I ℓ` in the outcome region.
* `frSpec_agree`, `msspSpec_agree`: FR-Dijkstra and MSSP compute distances, which are unique: any
  two subroutines meeting `FRSpec` (`MSSPSpec`) agree wherever the specification applies, so a
  machine FR (MSSP) meeting the specification on the calls computes the values of `frRef`
  (Klein's `msspPlaneK`) there; no per-call version is needed for them.
* **`machMO gs I`**: the subroutines of the calls with the machine's negative-length shortest paths
  (identifiers `gs x h` of the piece map of each call), Klein's MSSP, `frRef`, `pstflowW`;
  **`oSpecOn_machMO`**: they meet `OSpecOn` on every set of calls.
* **`mfMain_cMachNM`**: `mfMain_cMachOC` for `machMO gs I`: the hypothesis `OSpecOn` is discharged;
  the six step specifications ask for the outputs of `impl` with `negMach` at each call.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine NegSSSP NegSSSP.Driver NegSSSP.Frame
  CombMap

universe w

section Neg

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]

/-- **The preconditions of the machine's negative-length shortest paths**: a plane map with
transitive rotations and faces, the loops of the dual of nonnegative length. -/
def NegPre (M : CombMap D V F) (ℓ : D → ℤ) : Prop :=
  M.IsPlane ∧ M.RotTrans ∧ M.FaceTrans ∧ ∀ d, M.dual.tail d = M.dual.head d → 0 ≤ ℓ d

/-- A run of `negFix` from the root configuration of the kept darts in the numbering of `g`. -/
def NegRun (g : GIds D F) (M : CombMap D V F) (ℓ : D → ℤ) (I : Input) (c' : Config) (t : ℕ) :
    Prop :=
  Exec I (rtW (Fintype.card D) (rtL M ℓ) g.G) negFix (rootCfgP g M ℓ (repsN M.dual g.gd)) c' t

/-- The outcome region of the root frame holds `o`. -/
def NegEnc (g : GIds D F) (M : CombMap D V F) (ℓ : D → ℤ) (o : Option (F → ℤ)) (c' : Config) :
    Prop :=
  Res g M.dual (rtL M ℓ) (repsN M.dual g.gd) o (rtHb (Fintype.card D) (rtL M ℓ) g.G + 5)
    (rtH (Fintype.card D) (rtL M ℓ) g.G (repsN M.dual g.gd).card
      (ck M.dual (repsN M.dual g.gd))) c'

open Classical in
/-- **The machine's negative-length shortest paths**: the outcome encoded at the end of the run of
`negFix` (with `PotOut`), when there is one; otherwise `negSSSPImpl`. -/
noncomputable def negMach (g : GIds D F) (M : CombMap D V F) (I : Input) (ℓ : D → ℤ) :
    Option (F → ℤ) :=
  if h : ∃ o c' t, NegRun g M ℓ I c' t ∧ NegEnc g M ℓ o c' ∧ PotOut (M.dual.graph ℓ) o then
    h.choose
  else negSSSPImpl (fun X => frRef X) M ℓ

/-- **`negMach` meets the specification of negative-length shortest paths** on every map. -/
theorem negMach_spec (g : GIds D F) (M : CombMap D V F) (I : Input) :
    NegSSSPSpec M (negMach g M I) := by
  intro ℓ
  unfold negMach
  split_ifs with h
  · rw [← dual_graph]
    exact negSSSPOut_of_potOut h.choose_spec.choose_spec.choose_spec.2.2
  · exact negSSSPImpl_spec (fun X => frRef X) (fun X => frRef_spec X) M ℓ

/-- **The machine run of `negSSSP`**: under `NegPre`, `negFix` runs from the root configuration
within the bound of `cMach_negsssp_exec_gd`, and every run ends with `negMach g M I ℓ` in the
outcome region (the semantics is deterministic). -/
theorem negMach_run (C C₀ : ℕ) (hC : 200000 ≤ C) (g : GIds D F) {M : CombMap D V F}
    {ℓ : D → ℤ} (hpre : NegPre M ℓ) (I : Input) :
    (∃ c' t, NegRun g M ℓ I c' t ∧
      t ≤ (10 ^ 12 + 1 + fsKC + 80) * (cMach C C₀).negsssp (Fintype.card D) + fsKC + 22 +
        (12 * Fintype.card D + 4610) ∧ c'.output = []) ∧
    ∀ c' t, NegRun g M ℓ I c' t → NegEnc g M ℓ (negMach g M I ℓ) c' := by
  obtain ⟨hM, hrot, hface, hneg⟩ := hpre
  obtain ⟨c₀, t₀, o₀, ex₀, ht₀, hpot₀, hres₀, hout₀⟩ :=
    cMach_negsssp_exec_gd C C₀ hC g hM.dual (dual_rotTrans hface) (dual_faceTrans hrot) hneg I
  have hex : ∃ o c' t, NegRun g M ℓ I c' t ∧ NegEnc g M ℓ o c' ∧ PotOut (M.dual.graph ℓ) o :=
    ⟨o₀, c₀, t₀, ex₀, hres₀, hpot₀⟩
  refine ⟨⟨c₀, t₀, ex₀, ht₀, hout₀⟩, fun c' t hr => ?_⟩
  have e : negMach g M I ℓ = hex.choose := by unfold negMach; rw [dite_of_pos hex]
  obtain ⟨c₁, t₁, hr₁, he₁, -⟩ := hex.choose_spec
  obtain ⟨rfl, -⟩ := Exec.det hr₁ hr
  rw [e]
  exact he₁

end Neg

/-! ### FR-Dijkstra and MSSP: the values are determined by the specification -/

/-- **Two FR-Dijkstras meeting the specification agree** wherever it applies. -/
theorem frSpec_agree {X : Type*} [Fintype X] [DecidableEq X] {f f' : FRFun X} (hf : FRSpec f)
    (hf' : FRSpec f') {H : DDG X} {E : List (X × X × ℤ)} {r : X} {p : X → ℤ}
    (hp : (DDG.union H E).IsPot p) : f H E r p = f' H E r p :=
  (hf H E r p hp).unique (hf' H E r p hp)

/-- **Two MSSPs meeting the specification agree** wherever it applies. -/
theorem msspSpec_agree {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
    [DecidableEq V'] [Fintype F'] [DecidableEq F'] {M' : CombMap D' V' F'}
    {m m' : List D' → (D' → ℤ) → F' → F' → Option ℤ} (hm : MSSPSpec M' m) (hm' : MSSPSpec M' m')
    (P : SPath M') {ℓ : D' → ℤ} (hℓ : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) {x : F'} (hx : x ∈ P.faces) :
    m P.darts ℓ x = m' P.darts ℓ x :=
  (hm P ℓ hℓ x hx).unique (hm' P ℓ hℓ x hx)

/-! ### The subroutines of the calls -/

section Fam

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- Identifiers for the piece map of every call (darts and faces). -/
abbrev GIdsFam :=
  (x : MCall M) → PieceInv M x.1.piece x.2.1 x.2.2 →
    GIds (SDart (pdarts M x.1.piece x.2.1)) (SFace x.2.2 (pdarts M x.1.piece x.2.1) (revPerm M))

/-- **The subroutines of the calls with the machine's negative-length shortest paths**: at the call
`x`, `negMach` with the identifiers `gs x h` of its piece map; Klein's MSSP, `frRef`, `pstflowW`. -/
noncomputable def machMO (gs : GIdsFam M) (I : Input) : MOFam M :=
  fun x h => ⟨Klein.msspPlaneK (pmap h), frRef _, negMach (gs x h) (pmap h) I,
    STFlow.pstflowW (pmap h)⟩

/-- **They meet their specifications at every call.** -/
theorem oSpecOn_machMO (gs : GIdsFam M) (I : Input) (Reach : MCall M → Prop) :
    OSpecOn M (machMO gs I) Reach :=
  fun x _ h hpl hrot hface => ⟨Klein.msspPlaneK_spec hpl hrot hface, frRef_spec _,
    negMach_spec _ _ _, STFlow.pstflowW_spec hpl⟩

end Fam

section Head

variable {D V : Type w} {F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The whole program with the machine's negative-length shortest paths at every call**:
`mfMain_cMachOC` for the subroutines `machMO gs I₀` (`OSpecOn` discharged by
`oSpecOn_machMO`). The six step specifications ask the subroutine programs for the outputs of
`impl` with `negMach (gs x h) (pmap h) I₀` (the outcome of the run of `negFix` on the piece map of
the call, numbered by `gs x h`), Klein's MSSP, `frRef` and `pstflowW`. -/
theorem mfMain_cMachNM (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {u : D → ℤ} (hu : ∀ d, 0 ≤ u d) {S T : Finset V} (hST : Disjoint S T)
    {n : ℕ} (e : ℕ → _) (hsurj : ∀ d, ∃ i < n, e i = d) (d₀ : _) {x₀ : D}
    (hx₀ : x₀ ∈ nlDarts M) (gs : GIdsFam (lpreMap M)) (I₀ : Input) {C C₀ : ℕ} (hC : 100 ≤ C)
    (hC₀ : 20 ≤ C₀) {I : Input} {W Hb Z : ℕ} {gid : _ → ℕ}
    {sepP cntP fixP c2sP s2cP retP frmP : Stmt} {sT cs : ℕ → ℕ} {sR : ℕ → ℕ → ℕ}
    {cnT rO : MCall (lpreMap M) → ℕ} {fT rtT fmT : MCall (lpreMap M) → ℕ → ℕ}
    {cT s2T : MCall (lpreMap M) → ℕ → ℕ → ℕ} {RS RT : ℕ} (hZ : 2 * Z ≤ W) :
    let pc := pcChoiceE (lpreMap M) (pendQ _) e n d₀
    let sc := fun Hs A W => scChoiceE (lpreMap M) (sepM (lpreMap M)) e n Hs A W
    let τ := decS (lpreMap M) (spSR (lpreMap M) pc sc (pendQ _))
      (spHR (lpreMap M) pc sc (pendQ _))
      (smD (lpreMap M) pc.pick (preTerm (nlTerm M S)) (preTerm (nlTerm M T)))
      (chRot (lpreMap M) (pendQ _)) 100000 univ [] (rootRot (lpreMap M) (pendQ _)) true
    let u' := preCap (fun y => u y.1) (nlTerm M S) (nlTerm M T)
    let S' := preTerm (nlTerm M S)
    let T' := preTerm (nlTerm M T)
    let Reach := Calls (lpreMap M) τ [] (rotPerm (lpreMap M))
    let N := τ.piece.card
    let c := cMach C C₀
    SepPSpec (lpreMap M) Reach gid u' S' T' Z I W sepP sT sR →
    CntPSpec (lpreMap M) Reach gid u' S' T' Z I W cntP cnT rO →
    FixPSpecO (lpreMap M) (machMO gs I₀) Reach gid u' S' T' Z I W fixP fT rO →
    C2SPSpecO (lpreMap M) (machMO gs I₀) Reach gid u' S' T' Z I W c2sP cT rO →
    S2CPSpecO (lpreMap M) (machMO gs I₀) Reach gid u' S' T' Z I W s2cP s2T rO →
    RetPSpecO (lpreMap M) (machMO gs I₀) Reach gid u' S' T' Z I W retP rtT rO →
    FrmPSpecO (lpreMap M) (machMO gs I₀) Reach gid u' S' T' Z I W frmP fmT rO →
    (∀ m, sT m + cs m ≤ C * m * lg m) →
    (∀ l r π Hs σ, Reach (.node l r π, Hs, σ) →
      cnT (.node l r π, Hs, σ) ≤ cs (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card +
        100 * (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card + 100 * Hs.length + 100) →
    (∀ l r π Hs σ (h : SCond (lpreMap M) l r π Hs σ) j πj, Reach (.node l r π, Hs, σ) →
      (xCtxO (lpreMap M) (machMO gs I₀) u' S' T' l r π Hs σ h).L[j]? = some πj →
      fT (.node l r π, Hs, σ) j ≤ c.fixRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
        πj.faces.card πj.k (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) ∧
      (∀ i, cT (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      (∀ i, s2T (.node l r π, Hs, σ) j i ≤
        c.c2sRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          πj.faces.card πj.k) ∧
      rtT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) ∧
      fmT (.node l r π, Hs, σ) j ≤
        c.pushRun (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs).card
          (nOrb (σ * revPerm (lpreMap M)) (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))
          (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs)) +
        c.lin (psize (lpreMap M) σ (pdarts (lpreMap M) (l.piece ∪ r.piece) Hs))) →
    (∀ m k, m ≤ N → k ≤ N → sR m k ≤ RS) → (∀ x, Reach x → rO x ≤ RT) →
    ∀ {REVb SIGb CAPb KRb : ℕ} {en : ℕ → _}, (∀ y, ∃ i < N, en i = y) →
    (∀ i < N, gid (en i) = i) → 0 < Hb → ∀ (c₀ : Config), WordsBounded W c₀ →
    c₀.nreg 6700 = N → c₀.nreg 6701 = REVb → c₀.nreg 6702 = SIGb → c₀.nreg 6703 = CAPb →
    c₀.nreg 6704 = KRb → c₀.nreg 6705 = ntag τ → c₀.nreg 6706 = Z → c₀.nreg 6707 = Hb →
    (∀ i < N, c₀.nmem (REVb + i) < N ∧ en (c₀.nmem (REVb + i)) = (lpreMap M).rev (en i)) →
    (∀ i < N, c₀.nmem (SIGb + i) < N ∧
      en (c₀.nmem (SIGb + i)) = rotPerm (lpreMap M) (en i)) →
    (∀ i < N, (c₀.nmem (CAPb + i) : ℤ) = u' (en i) ∧ c₀.nmem (CAPb + i) ≤ Z) →
    (∀ i < N, c₀.nmem (KRb + i) = lrk S' T' (hunion []) ((lpreMap M).tail (en i))) →
    REVb + N ≤ Hb → SIGb + N ≤ Hb → CAPb + N ≤ Hb → KRb + N ≤ Hb →
    Hb + 9 + 7 * N + (2 * N + 1) * (39 * N + 20 + RS + RT) ≤ W →
    τ.piece = univ ∧
    ∃ c' t, Exec I W (.seq rfProg (driver mtProg mlProg (splitS sepP)
        (nodeSF (stepPO cntP fixP c2sP s2cP retP frmP)))) c₀ c' t ∧
      t ≤ 46 * N + 80 + ((100000 + 11) ^ 2 * 448 * (27 * 102256 + 25) * machK C *
            Fintype.card D * lg (Fintype.card D) ^ 3 +
          (100000 + 11) ^ 2 * 28 * C₀ * Fintype.card D * lg (Fintype.card D) +
        1000 * (2 * N + 1) + 2) ∧
      FOutL (lpreMap M) gid u' S' T' Z (τ, [], rotPerm (lpreMap M))
        (arunLO (lpreMap M) (machMO gs I₀) u' S' T' τ [] (rotPerm (lpreMap M)))
        (Hb + 5) (Hb + 9 + 7 * N) c' ∧
      IsMax M u S T (nlRunO M u S T τ (machMO gs I₀)) := by
  intro pc sc τ u' S' T' Reach N c hsep
  exact mfMain_cMachOC (NO := machMO gs I₀) hM hrot hface hu hST e hsurj d₀ hx₀ hC hC₀ hZ hsep
    (oSpecOn_machMO gs I₀ _)

end Head

end MfDrv

end BKMNW

end PlanarFlow
