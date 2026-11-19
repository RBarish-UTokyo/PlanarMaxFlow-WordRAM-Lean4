module

public import PlanarFlow.BKMNW.NsCall

/-!
# The s-t flow subroutine with explicit choices

`STFlow.pstflowW` (the s-t flow of the subroutine family `NsStep.machMOL`) makes four
**classical choices**: the source `hX.choose ∈ X`, the dart `hY.choose` whose tail is the sink
and whose face is the root of the dual tree, the isolating weight `isoW M t` (`h.choose` of its
existence) and the initial dual tree (`linit`, `h.choose` of a state meeting `LInv`). Maximum
flows are not unique, so the flow depends on these choices, and a machine program (which must make
its own choices) cannot be proved to compute `pstflowW` exactly — which the step specifications
(`C2SPSpecO'`, `S2CPSpecO'`: the program's output **equals** the subroutine's) would require.

This file states the s-t flow with the four choices **explicit**:

* `pcoreFlowT M c ε s t T`: the flow of the perturbed run `lrun` from the state of the dual tree
  `T` (what the machine program `pstProg` computes, `STFlow.pcore_exec`);
  `pstflowT M ε c X Y s d₀ T = restrictR M X Y (pcoreFlowT M (capR M c X Y) ε s (tail d₀) T)`;
* **`pcoreFlowT_spec`**, **`pstflowT_stOut`**: correct (a maximum flow) for every source `s ∈ X`,
  dart `d₀` with tail in `Y`, perturbation `ε` and tree `T` meeting the invariant `LInv` of the
  perturbed run;
* `StChoice M` (the four choices as functions of `(c, X, Y)`), `StChoice.OK`, `StChoice.flow`,
  **`StChoice.spec`** (`STFlowSpec M ch.flow` when the choices are valid);
* **`machMOS gid I chs`**: the subroutines of the calls with the s-t flow of the choices `chs x h`
  (to be the choices made by the machine's s-t flow encoder), Klein's MSSP, `frRef`, `negLay`;
  **`oSpecOn_machMOS`**: they meet their specifications when the choices are valid, so
  `MfDrv.mfMain_cMachOC'` applies to them (as `mfMain_cMachNL'` does to `machMOL`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F}

variable (M) in
/-- The state of the perturbed run of a dual tree. -/
def tSt (c ε : D → ℤ) (T : DTree M) : LSt M := ⟨M.cob (T.psum c), M.cob (T.psum ε), T⟩

variable (M) in
/-- **The flow of the perturbed run from the dual tree `T`.** -/
noncomputable def pcoreFlowT (c ε : D → ℤ) (s t : V) (T : DTree M) : D → ℤ :=
  (lrun M c ε s t (fuel F) (tSt M c ε T)).1.g

/-- **Correctness of the run from an explicit tree** meeting the invariant. -/
theorem pcoreFlowT_spec (hM : M.IsPlane) {c ε : D → ℤ} {s t : V} (hst : s ≠ t) {T : DTree M}
    (hT : LInv c ε s t (tSt M c ε T)) :
    IsPseudo M c (pcoreFlowT M c ε s t T) ∧
      (∀ v, v ≠ s → v ≠ t → M.div (pcoreFlowT M c ε s t T) v = 0) ∧
      NoPath M c (pcoreFlowT M c ε s t T) {s} {t} := by
  obtain ⟨h1, h2, -, h4⟩ := T.chi_spec hM s t
  have hP : IsUnit (M := M) (s := s) (t := t) (T.chi s t) := ⟨h1, h2, h4⟩
  exact lrun_spec hM hst hP hT (n := fuel F) (by unfold fuel; omega)

variable (M) in
/-- **The s-t flow with explicit choices**: source `s`, sink `tail d₀`, perturbation `ε`, initial
dual tree `T`. -/
noncomputable def pstflowT (ε c : D → ℤ) (X Y : Finset V) (s : V) (d₀ : D) (T : DTree M) :
    D → ℤ :=
  restrictR M X Y (pcoreFlowT M (capR M c X Y) ε s (M.tail d₀) T)

/-- **The s-t flow with explicit choices is a maximum flow** (`STOut`) when `s ∈ X`, the tail of
`d₀` is in `Y` and the tree meets the invariant of the perturbed run. -/
theorem pstflowT_stOut (hM : M.IsPlane) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) (πs πt : SPath M)
    (hXY : Disjoint πs.verts πt.verts) {ε : D → ℤ} {s : V} {d₀ : D} {T : DTree M}
    (hs : s ∈ πs.verts) (hd₀ : M.tail d₀ ∈ πt.verts)
    (hT : LInv (capR M c πs.verts πt.verts) ε s (M.tail d₀)
      (tSt M (capR M c πs.verts πt.verts) ε T)) :
    STOut M c πs.verts πt.verts (pstflowT M ε c πs.verts πt.verts s d₀ T) := by
  have hst : s ≠ M.tail d₀ := fun h => disjoint_left.1 hXY hs (h ▸ hd₀)
  obtain ⟨h1, h2, h3⟩ := pcoreFlowT_spec hM hst hT
  exact stOut_restrictR hc πs πt hXY hs hd₀ h1 h2 h3

variable (M) in
/-- **The four choices of the s-t flow**, as functions of the capacities and the terminals. -/
structure StChoice where
  /-- The source. -/
  src : (D → ℤ) → Finset V → Finset V → V
  /-- The dart of the sink (its tail the sink, its face the root of the dual tree). -/
  snk : (D → ℤ) → Finset V → Finset V → D
  /-- The perturbation. -/
  eps : (D → ℤ) → Finset V → Finset V → D → ℤ
  /-- The initial dual tree. -/
  tree : (D → ℤ) → Finset V → Finset V → DTree M

/-- **Valid choices**: wherever the s-t flow is called (nonnegative capacities, disjoint
terminals, `X` nonempty, a dart with tail in `Y`), a source in `X`, a dart with tail in `Y`, and a
tree meeting the invariant of the perturbed run. -/
def StChoice.OK (ch : StChoice M) : Prop :=
  ∀ (c : D → ℤ) (X Y : Finset V), (∀ d, 0 ≤ c d) → Disjoint X Y → X.Nonempty →
    (∃ d, M.tail d ∈ Y) →
    ch.src c X Y ∈ X ∧ M.tail (ch.snk c X Y) ∈ Y ∧
      LInv (capR M c X Y) (ch.eps c X Y) (ch.src c X Y) (M.tail (ch.snk c X Y))
        (tSt M (capR M c X Y) (ch.eps c X Y) (ch.tree c X Y))

/-- The s-t flow of the choices. -/
noncomputable def StChoice.flow (ch : StChoice M) (c : D → ℤ) (X Y : Finset V) : D → ℤ :=
  pstflowT M (ch.eps c X Y) c X Y (ch.src c X Y) (ch.snk c X Y) (ch.tree c X Y)

/-- **Valid choices give an s-t flow subroutine meeting its specification.** -/
theorem StChoice.spec (hM : M.IsPlane) {ch : StChoice M} (hok : ch.OK) : STFlowSpec M ch.flow := by
  intro c πs πt hc hXY
  have hXne : πs.verts.Nonempty := ⟨_, πs.p_mem_init (Nat.zero_le _)⟩
  have hY : (πt.p 0) ∈ πt.verts := πt.p_mem_init (Nat.zero_le _)
  have hne : πs.p 0 ≠ πt.p 0 := fun h => disjoint_left.1 hXY (πs.p_mem_init (Nat.zero_le _))
    (h ▸ hY)
  obtain ⟨d₀, hd₀⟩ := exists_dart_tail hM hne
  obtain ⟨hs, ht, hT⟩ := hok c _ _ hc hXY hXne ⟨d₀, hd₀ ▸ hY⟩
  exact pstflowT_stOut hM hc πs πt hXY hs ht hT

end STFlow

namespace BKMNW

namespace NsStep

open Finset Function Equiv CombMap MfDrv

universe w

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The subroutines of the calls with the s-t flow of explicit choices** `chs x h` (Klein's
MSSP, `frRef`, `negLay`, `(chs x h).flow`). -/
noncomputable def machMOS (gid : D → ℕ) (I : WordRAM.Input)
    (chs : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → STFlow.StChoice (pmap h)) :
    MOFam M :=
  fun x h => ⟨Klein.msspPlaneK (pmap h), frRef _, negLay gid I x h, (chs x h).flow⟩

/-- **They meet their specifications** at the calls where the choices are valid. -/
theorem oSpecOn_machMOS (gid : D → ℕ) (I : WordRAM.Input)
    (chs : (x : MCall M) → (h : PieceInv M x.1.piece x.2.1 x.2.2) → STFlow.StChoice (pmap h))
    (Reach : MCall M → Prop) (hok : ∀ x, Reach x → ∀ h, (chs x h).OK) :
    OSpecOn M (machMOS gid I chs) Reach :=
  fun x hx h hpl hrot hface => ⟨Klein.msspPlaneK_spec hpl hrot hface, frRef_spec _,
    negLay_spec _ _ _ _, STFlow.StChoice.spec hpl (hok x hx h)⟩

end NsStep

end BKMNW

end PlanarFlow
