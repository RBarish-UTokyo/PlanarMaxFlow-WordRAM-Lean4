module

public import PlanarFlow.STFlow.ProgMain
public import PlanarFlow.STFlow.LexTree

/-!
# The perturbed single-source single-sink maximum flow on the machine: end to end

* `pcore_exec`: **the program `pstProg` from any configuration meeting the preconditions**
  (listed in its docstring) halts within `140 (n + 1) + 21 + pstOps · opCostE n + pstExt`
  steps (every executed step counted, the operations of the link-cut trees at their amortised
  cost), printing nothing, with `OUT[d] = rs d · g d`, `g` the flow of `lrun (fuel F)` from the
  given initial state, for any perturbation `ε` with the properties `PertOK` (nonnegative,
  separating the darts of the path, at most `m + 1` steps: `pertOK_lex` for `lexEps`,
  `PlanarFlow.STFlow.pertOK_iso` for the word-size perturbation).
* `pstflowE`, `pstflowE_exec`, `pstflowE_exec_exists`: the same for a family of perturbations
  `E` (`E t` for the sink `t`), with `pstflow = pstflowE (fun _ => lexEps)` (`pstflow_eq_E`);
  `pstflowE_exec_exists` also states that the real memory of the starting configuration holds
  integers of absolute value at most `kH0` (`pReal_int`). The maximum-flow algorithm uses
  `PlanarFlow.STFlow.pstflowW = pstflowE (isoEps M)`, `PlanarFlow.STFlow.pstflowW_exec_exists`.
* `pstflow_exec`: **the same for `pstflow`**: with the capacities `capR c X Y`, the source, sink
  and root face chosen by `pstflow`, the initial state of `linit`, and the restriction
  `RS[d] = 0` on the darts inside `X` or inside `Y` (`1` elsewhere), the program ends with
  `OUT[d] = pstflow M c X Y d`.
* `pstflow_exec_lex`: **the same with any shortest-path tree for the perturbed lengths** as the
  initial tree (`DTree.LexFeas`, a checkable condition): such a tree has the parent darts of the
  tree of `linit` (`linit_par_eq`, `PlanarFlow/STFlow/LexTree.lean`).
* `pstflow_exec_exists`: **the preconditions can be met**: for every plane map with transitive
  rotations and faces, nonnegative capacities and disjoint `X`, `Y` (with `X` nonempty and a dart
  whose tail is in `Y`), an input and a starting configuration from which the program ends with
  `pstflow` in `OUT` within `504 000 000 · m lg m` steps.
* `pst_steps_le`: on `n = 2 N` nodes, `N = #V + #F + #D`, the bound is at most
  `56 000 000 · N lg N`; `pst_steps_le_m`: on a plane map with `m ≥ 1` darts, at most
  `504 000 000 · m lg m ≤ 504 000 000 · m lg² m`, of the form of the budget
  `PlanarFlow.BKMNW.SubCosts.Bounds.stflow`.

**The cost model.** The machine (`WordRAM`) has exact real registers and memory with unit-cost
arithmetic. The keys of the darts (`PlanarFlow/STFlow/ProgKey.lean`) are `N (c - g) + (ε - h)`;
with `lexEps` (`ε d = (4 F + 5) ^ (index of d)`) they are integers of `O(m log m)` bits, which a
word RAM with words of `O(log n)` bits does not hold. The program is stated for every
perturbation with the properties `PertOK`; with the word-size perturbation `isoEps`
(`PlanarFlow/STFlow/IsoDef.lean`, between `1` and `(4 F + 6) #V`) every number of the run is an
integer of absolute value at most `(m + 4) (2 R + 1) (Σ c + 1)`, `R = (F + 1) m (4 F + 6) #V`
(`PlanarFlow.STFlow.isoKeys_bounded`, `PlanarFlow.STFlow.pstflowW_exec_exists`,
`PlanarFlow/STFlow/IsoExec.lean`). The ingredients of the deterministic word-size scheme of
Cabello, Chambers and Erickson for `lexEps` are also proved: the initial tree is determined by
the lexicographic lengths (`linit_par_eq`), every comparison of the run is decided by unperturbed
residual capacities and the largest indices of darts on four paths of the dual tree
(`lslack_lt_iff`, the machine block `cmpS`, `cmp_orun_lred`), and a path-minimum
structure could break ties by these comparisons; that
structure is not implemented, the isolating perturbation making it unnecessary.

**What is given.** The machine has no conversion from naturals to reals, and the initial dual
tree is a shortest-path tree for the lengths `w` (Dijkstra's algorithm, whose machine interface
does not fit this program). So the caller provides: in the input, the map (`KInput` of the dual
map), the darts leaving `s` and `t` (`GB`), the initial dual tree `T₀` and a cotree of it rooted
at `s`, by orders (`KInit`); in the real memory, `w` (twice), the capacities, the restriction,
and the constants `kTh`, `kH0`. For `pstflow_exec` the initial tree is the one chosen by
`linit`; `pstflow_exec_lex` accepts any tree rooted at the same face that is a shortest-path tree
for the lexicographic lengths `(c, ε)` (`DTree.LexFeas`): the perturbed shortest paths are unique
(`linit_par_eq`), so any correct procedure (Dijkstra's algorithm with the comparisons of
Cabello, Chambers and Erickson, Section 6.2, for instance) may compute it.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW Klein DynTree WordRAM WordRAM.Machine WordRAM.Machine.Stmt
  WordRAM.Programs

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F} {nD : ℕ} {σ : D ≃ Fin nD} {n : ℕ} {ιF : F → ℕ} {ιG : D → ℕ}
  {ιV : V → ℕ} {ιE : D → ℕ} {P : Input} {B : ℕ}

/-- **The perturbed run on the machine, end to end, for a given initial state.** The program
`pstProg B nD n` runs from a configuration `c₀` in which

* the input holds the dual map (`KInput` for `M.dual`, on `n` nodes laid out by `Layout`), the
  darts `d₁` leaving `s` and `d₀` leaving `t` (`KBnd`), and the initial dual tree `T₀` (rooted at
  the face of `d₀`, its state `(cob (psum c), cob (psum ε), T₀)` satisfying `LInv`) with a
  cotree `C₀` of it rooted at `s`, by orders (`KInit`);
* the real memory holds `w = N c + ε` in `WT` and `PH` (`N > 2 lexR`), the capacities in `CP`,
  `rs` in `RS`, `kTh` and `kH0`;

within `140 (n + 1) + 21 + pstOps · opCostE n + pstExt` steps; it prints nothing and ends with
`OUT[d] = rs d · g d`, `g` the flow computed by the perturbed run `lrun (fuel F)` from the
initial state. -/
theorem pcore_exec (hWa : 9 * nD + 7 * n + 6 ≤ B) (hB : n + 2 * nD ≤ B) (hB7 : 7 * nD + 3 ≤ B)
    (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1)) (hM : M.IsPlane)
    {c ε : D → ℤ} (hc : ∀ d, 0 ≤ c d) {s t : V} (hst : s ≠ t)
    {d₀ d₁ : D} (hd₀ : M.tail d₀ = t) (hd₁ : M.tail d₁ = s) (hPO : PertOK M c ε s t d₀)
    {T₀ : DTree M}
    (hroot : T₀.root = M.face d₀)
    (hI₀ : LInv c ε s t ⟨M.cob (T₀.psum c), M.cob (T₀.psum ε), T₀⟩)
    {N : ℤ} (hN : 2 * lexR F ε < N) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    (hG : KBnd 2 (fun i => if i = 0 then d₁ else d₀) σ n P) {C₀ : DTree M.dual}
    {vs ts : List F} {fs cs : List V} (hI : KInit M.dual σ ιF ιV n 2 (toDD T₀) C₀ vs ts fs cs P)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) (hCr : C₀.root = s)
    {rs : D → ℝ} {c₀ : Config} (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀)
    (hwt : ∀ d, c₀.rmem (aWT + σ d) = wlen N c ε d)
    (hph : ∀ d, c₀.rmem (aPH nD + σ d) = wlen N c ε d)
    (hcp : ∀ d, c₀.rmem (aCP nD + σ d) = c d) (hrs : ∀ d, c₀.rmem (aRS nD + σ d) = rs d)
    (hth : c₀.rmem (aTH nD) = kTh D F N c ε) (hh0 : c₀.rmem (aH0 nD) = kH0 D F N c ε) :
    ∃ c' steps, Exec P (B + 16 * (n + 1)) (pstProg B nD n) c₀ c' steps ∧
      steps ≤ 140 * (n + 1) + 21 + pstOps (Fintype.card V) (Fintype.card F) nD * opCostE n +
        pstExt (Fintype.card V) (Fintype.card F) nD ∧
      (∀ d, c'.rmem (aOT nD + σ d) = rs d *
        (lrun M c ε s t (fuel F)
          ⟨M.cob (T₀.psum c), M.cob (T₀.psum ε), T₀⟩).1.g d) ∧
      c'.output = c₀.output := by
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  exact lctE_adaptive_exec B n (pstS B nD n) P _ _ hc₀ _ fun cf hcf hS hout hmf _ => by
    have hm : ∀ a, a < B → cf.rmem a = c₀.rmem a := fun a ha => (hmf a (Or.inl ha)).2
    obtain ⟨c', F', G', m', hrun, hm', hOUT, hout'⟩ := pstS_orun le_rfl (by omega) hB hB7 hP hM
      hc hst hd₀ hPO hd₁ hroot hI₀ hN hL hK hG hI hoff hCr (rs := rs) hcf hS
      (fun d => by rw [hm _ (by have := hσ d; unfold aWT; omega)]; exact hwt d)
      (fun d => by rw [hm _ (by have := hσ d; unfold aPH; omega)]; exact hph d)
      (fun d => by rw [hm _ (by have := hσ d; unfold aCP; omega)]; exact hcp d)
      (fun d => by rw [hm _ (by have := hσ d; unfold aRS; omega)]; exact hrs d)
      (by rw [hm _ (by unfold aTH; omega)]; exact hth)
      (by rw [hm _ (by unfold aH0; omega)]; exact hh0)
    exact ⟨c', F', G', m', hrun, hm', hOUT, hout'.trans hout⟩

/-- The state chosen by `linit` is the state of its tree. -/
lemma linit_eq {c ε : D → ℤ} {s t : V} {o : F} {st : LSt M}
    (h : linit M c ε s t o = some st) :
    st = ⟨M.cob (st.T.psum c), M.cob (st.T.psum ε), st.T⟩ := by
  unfold linit at h
  split_ifs at h with hex
  obtain rfl := Option.some.inj h
  obtain ⟨-, -, hg, hh⟩ := hex.choose_spec
  cases hc : hex.choose with
  | mk g h' T =>
    rw [hc] at hg hh
    simp only at hg hh
    rw [hg, hh]

variable (M) in
/-- **The perturbed run for a family of perturbations** `E` (the perturbation `E t` for the sink
`t`): the flow of `lrun (fuel F)` from the state of `linit`. -/
noncomputable def pcoreFlowE (E : V → D → ℤ) (c : D → ℤ) (s t : V) (o : F) : D → ℤ :=
  ((linit M c (E t) s t o).map fun st => (lrun M c (E t) s t (fuel F) st).1.g).getD 0

variable (M) in
open Classical in
/-- **SingleSourceSingleSinkMaxFlow with a family of perturbations** `E`: `pstflow` for `E = lexEps`
(`pstflow_eq_E`), `pstflowW` for `E = isoEps M` (`PlanarFlow.STFlow.pstflowW_eq_E`). -/
noncomputable def pstflowE (E : V → D → ℤ) (c : D → ℤ) (X Y : Finset V) : D → ℤ :=
  if h : X.Nonempty ∧ ∃ d, M.tail d ∈ Y then
    restrictR M X Y
      (pcoreFlowE M E (capR M c X Y) h.1.choose (M.tail h.2.choose) (M.face h.2.choose))
  else 0

lemma pstflow_eq_E (c : D → ℤ) (X Y : Finset V) :
    pstflow M c X Y = pstflowE M (fun _ => lexEps D F) c X Y := by
  unfold pstflow pstflowE pcoreFlow pcoreFlowE pcoreRun
  split_ifs with h
  · cases linit M (capR M c X Y) (lexEps D F) h.1.choose (M.tail h.2.choose) (M.face h.2.choose)
      <;> rfl
  · rfl

open Classical in
/-- **The perturbed implementation of SingleSourceSingleSinkMaxFlow on the machine, for a family
of perturbations `E`** (`pcore_exec` for `pstflowE M E`, the perturbation `E t` for the sink
`t`, with the properties `PertOK`): with `X` nonempty, a dart whose tail is in `Y`, `X` and `Y`
disjoint, the capacities `capR c X Y`, the source `hX.choose`, the sink `tail hY.choose` and the
root face `face hY.choose` chosen by `pstflow`, the initial state `st` of `linit` (its tree in
the input), and the restriction (`RS[d] = 0` inside `X` or inside `Y`, `1` elsewhere), the
program ends with `OUT[d] = pstflowE M E c X Y d`. -/
theorem pstflowE_exec {E : V → D → ℤ} (hWa : 9 * nD + 7 * n + 6 ≤ B) (hB : n + 2 * nD ≤ B)
    (hB7 : 7 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1)) (hM : M.IsPlane)
    {c : D → ℤ} (hc : ∀ d, 0 ≤ c d)
    {X Y : Finset V} (hX : X.Nonempty) (hY : ∃ d, M.tail d ∈ Y) (hXY : Disjoint X Y)
    (hPO : PertOK M (capR M c X Y) (E (M.tail hY.choose)) hX.choose (M.tail hY.choose) hY.choose)
    {st : LSt M} (hlin : linit M (capR M c X Y) (E (M.tail hY.choose)) hX.choose (M.tail hY.choose)
      (M.face hY.choose) = some st) {d₁ : D} (hd₁ : M.tail d₁ = hX.choose)
    {N : ℤ} (hN : 2 * lexR F (E (M.tail hY.choose)) < N) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    (hG : KBnd 2 (fun i => if i = 0 then d₁ else hY.choose) σ n P) {C₀ : DTree M.dual}
    {vs ts : List F} {fs cs : List V} (hI : KInit M.dual σ ιF ιV n 2 (toDD st.T) C₀ vs ts fs cs P)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD st.T).InT (C₀.par x)) (hCr : C₀.root = hX.choose)
    {c₀ : Config} (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀)
    (hwt : ∀ d, c₀.rmem (aWT + σ d) = wlen N (capR M c X Y) (E (M.tail hY.choose)) d)
    (hph : ∀ d, c₀.rmem (aPH nD + σ d) = wlen N (capR M c X Y) (E (M.tail hY.choose)) d)
    (hcp : ∀ d, c₀.rmem (aCP nD + σ d) = capR M c X Y d)
    (hrs : ∀ d, c₀.rmem (aRS nD + σ d) = if Inside M X Y d then 0 else 1)
    (hth : c₀.rmem (aTH nD) = kTh D F N (capR M c X Y) (E (M.tail hY.choose)))
    (hh0 : c₀.rmem (aH0 nD) = kH0 D F N (capR M c X Y) (E (M.tail hY.choose))) :
    ∃ c' steps, Exec P (B + 16 * (n + 1)) (pstProg B nD n) c₀ c' steps ∧
      steps ≤ 140 * (n + 1) + 21 + pstOps (Fintype.card V) (Fintype.card F) nD * opCostE n +
        pstExt (Fintype.card V) (Fintype.card F) nD ∧
      (∀ d, c'.rmem (aOT nD + σ d) = pstflowE M E c X Y d) ∧ c'.output = c₀.output := by
  have hst : hX.choose ≠ M.tail hY.choose := fun h =>
    disjoint_left.1 hXY hX.choose_spec (h ▸ hY.choose_spec)
  obtain ⟨hroot, hIst⟩ := linit_inv _ _ hlin
  have hst₀ := linit_eq hlin
  have hI₀ : LInv (capR M c X Y) (E (M.tail hY.choose)) hX.choose (M.tail hY.choose)
      ⟨M.cob (st.T.psum (capR M c X Y)), M.cob (st.T.psum (E (M.tail hY.choose))), st.T⟩ := by
    rw [← hst₀]; exact hIst
  obtain ⟨c', steps, e, hsteps, hOUT, hout⟩ := pcore_exec hWa hB hB7 hP hM
    (capR_nonneg hc X Y) hst rfl hd₁ hPO
    hroot hI₀ hN hL hK hG hI hoff hCr hc₀ hwt hph hcp hrs
    hth hh0
  refine ⟨c', steps, e, hsteps, fun d => ?_, hout⟩
  rw [hOUT d, ← hst₀]
  have hex : X.Nonempty ∧ ∃ d, M.tail d ∈ Y := ⟨hX, hY⟩
  unfold pstflowE pcoreFlowE
  rw [dite_eq_left hex]
  simp only [hlin, Option.map_some, Option.getD_some, restrictR]
  split_ifs <;> simp

open Classical in
/-- **The perturbed implementation of SingleSourceSingleSinkMaxFlow on the machine**
(`pstflowE_exec` for `pstflow`, the perturbation `lexEps`): the program ends with
`OUT[d] = pstflow M c X Y d`. -/
theorem pstflow_exec (hWa : 9 * nD + 7 * n + 6 ≤ B) (hB : n + 2 * nD ≤ B)
    (hB7 : 7 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1)) (hM : M.IsPlane)
    (hrot : M.RotTrans) (hface : M.FaceTrans) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d)
    {X Y : Finset V} (hX : X.Nonempty) (hY : ∃ d, M.tail d ∈ Y) (hXY : Disjoint X Y)
    {st : LSt M} (hlin : linit M (capR M c X Y) (lexEps D F) hX.choose (M.tail hY.choose)
      (M.face hY.choose) = some st) {d₁ : D} (hd₁ : M.tail d₁ = hX.choose)
    {N : ℤ} (hN : 2 * lexR F (lexEps D F) < N) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    (hG : KBnd 2 (fun i => if i = 0 then d₁ else hY.choose) σ n P) {C₀ : DTree M.dual}
    {vs ts : List F} {fs cs : List V} (hI : KInit M.dual σ ιF ιV n 2 (toDD st.T) C₀ vs ts fs cs P)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD st.T).InT (C₀.par x)) (hCr : C₀.root = hX.choose)
    {c₀ : Config} (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀)
    (hwt : ∀ d, c₀.rmem (aWT + σ d) = wlen N (capR M c X Y) (lexEps D F) d)
    (hph : ∀ d, c₀.rmem (aPH nD + σ d) = wlen N (capR M c X Y) (lexEps D F) d)
    (hcp : ∀ d, c₀.rmem (aCP nD + σ d) = capR M c X Y d)
    (hrs : ∀ d, c₀.rmem (aRS nD + σ d) = if Inside M X Y d then 0 else 1)
    (hth : c₀.rmem (aTH nD) = kTh D F N (capR M c X Y) (lexEps D F))
    (hh0 : c₀.rmem (aH0 nD) = kH0 D F N (capR M c X Y) (lexEps D F)) :
    ∃ c' steps, Exec P (B + 16 * (n + 1)) (pstProg B nD n) c₀ c' steps ∧
      steps ≤ 140 * (n + 1) + 21 + pstOps (Fintype.card V) (Fintype.card F) nD * opCostE n +
        pstExt (Fintype.card V) (Fintype.card F) nD ∧
      (∀ d, c'.rmem (aOT nD + σ d) = pstflow M c X Y d) ∧ c'.output = c₀.output := by
  have hst : hX.choose ≠ M.tail hY.choose := fun h =>
    disjoint_left.1 hXY hX.choose_spec (h ▸ hY.choose_spec)
  rw [pstflow_eq_E]
  exact pstflowE_exec (E := fun _ => lexEps D F) hWa hB hB7 hP hM hc hX hY hXY
    (pertOK_lex hM hrot hface (capR_nonneg hc X Y) hst rfl) hlin hd₁ hN hL hK hG hI hoff hCr
    hc₀ hwt hph hcp hrs hth hh0

/-- The orders of the initialisation only see the root and the parent darts off the root. -/
lemma kInit_congr {T T' : DTree M.dual.dual} {C : DTree M.dual} {vs ts : List F}
    {fs cs : List V} (hr : T.root = T'.root) (hp : ∀ x, x ≠ T.root → T.par x = T'.par x)
    (h : KInit M.dual σ ιF ιV n 2 T C vs ts fs cs P) :
    KInit M.dual σ ιF ιV n 2 T' C vs ts fs cs P := by
  have hd := DTree.depth_eq_of hr hp
  refine ⟨⟨h.oT.fnd, h.oT.fmem, h.oT.ynd, fun y => by rw [h.oT.ymem, hr], ?_⟩, h.oC, h.iv,
    fun i hi => ?_, h.if_, h.ic, h.l0, h.l1, h.l2, h.l3⟩
  · have := h.oT.ypw
    simp only [hd] at this
    exact this
  · rw [h.it i hi, hp _ ((h.oT.ymem _).1 (List.getElem_mem hi))]

open Classical in
/-- **`pstflow_exec` for any shortest-path tree of the perturbed lengths**: the same as
`pstflow_exec`, with the initial dual tree `T₀` in the input any tree rooted at
`face hY.choose` that is a shortest-path tree for the lexicographic lengths
`(capR c X Y, lexEps)` (`DTree.LexFeas`, a checkable condition on its path sums), instead of the
tree chosen by `linit`. Such a tree has the parent darts of the tree of `linit`
(`linit_par_eq`: the perturbed shortest paths are unique), so any correct shortest-path procedure
can supply it. -/
theorem pstflow_exec_lex (hWa : 9 * nD + 7 * n + 6 ≤ B) (hB : n + 2 * nD ≤ B)
    (hB7 : 7 * nD + 3 ≤ B) (hP : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1)) (hM : M.IsPlane)
    (hrot : M.RotTrans) (hface : M.FaceTrans) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d)
    {X Y : Finset V} (hX : X.Nonempty) (hY : ∃ d, M.tail d ∈ Y) (hXY : Disjoint X Y)
    {T₀ : DTree M} (hT₀ : T₀.LexFeas (capR M c X Y) (lexEps D F))
    (hr₀ : T₀.root = M.face hY.choose) {d₁ : D} (hd₁ : M.tail d₁ = hX.choose)
    {N : ℤ} (hN : 2 * lexR F (lexEps D F) < N) (hL : Layout M.dual n ιF ιG ιV ιE)
    (hK : KInput M.dual ∅ 0 σ ιF ιG ιV ιE P)
    (hG : KBnd 2 (fun i => if i = 0 then d₁ else hY.choose) σ n P) {C₀ : DTree M.dual}
    {vs ts : List F} {fs cs : List V} (hI : KInit M.dual σ ιF ιV n 2 (toDD T₀) C₀ vs ts fs cs P)
    (hoff : ∀ x, x ≠ C₀.root → ¬ (toDD T₀).InT (C₀.par x)) (hCr : C₀.root = hX.choose)
    {c₀ : Config} (hc₀ : WordsBounded (B + 16 * (n + 1)) c₀)
    (hwt : ∀ d, c₀.rmem (aWT + σ d) = wlen N (capR M c X Y) (lexEps D F) d)
    (hph : ∀ d, c₀.rmem (aPH nD + σ d) = wlen N (capR M c X Y) (lexEps D F) d)
    (hcp : ∀ d, c₀.rmem (aCP nD + σ d) = capR M c X Y d)
    (hrs : ∀ d, c₀.rmem (aRS nD + σ d) = if Inside M X Y d then 0 else 1)
    (hth : c₀.rmem (aTH nD) = kTh D F N (capR M c X Y) (lexEps D F))
    (hh0 : c₀.rmem (aH0 nD) = kH0 D F N (capR M c X Y) (lexEps D F)) :
    ∃ c' steps, Exec P (B + 16 * (n + 1)) (pstProg B nD n) c₀ c' steps ∧
      steps ≤ 140 * (n + 1) + 21 + pstOps (Fintype.card V) (Fintype.card F) nD * opCostE n +
        pstExt (Fintype.card V) (Fintype.card F) nD ∧
      (∀ d, c'.rmem (aOT nD + σ d) = pstflow M c X Y d) ∧ c'.output = c₀.output := by
  have : Nonempty D := ⟨hY.choose⟩
  obtain ⟨st, hlin, hroot, -⟩ := linit_spec hM (capR_nonneg (M := M) hc X Y)
    (fun d => lexEps_nonneg (F := F) d) hX.choose (M.tail hY.choose) (M.face hY.choose)
  have hr : (toDD T₀).root = (toDD st.T).root := by simp [hr₀, hroot]
  have hp : ∀ x, x ≠ (toDD T₀).root → (toDD T₀).par x = (toDD st.T).par x := fun x hx =>
    linit_par_eq hlin hT₀ hr₀ (by simpa [hr₀] using hx)
  exact pstflow_exec hWa hB hB7 hP hM hrot hface hc hX hY hXY hlin hd₁ hN hL hK hG
    (kInit_congr hr hp hI) (fun x hx h => hoff x hx ((DTree.inT_iff_of hr hp _).2 h)) hCr hc₀
    hwt hph hcp hrs hth hh0

/-- **The step bound is `O(N log N)`** on `n = 2 N` nodes, `N = #V + #F + #D`. -/
theorem pst_steps_le {nV nF nD : ℕ} (hN : 1 ≤ nV + nF + nD) :
    140 * (2 * (nV + nF + nD) + 1) + 21 + pstOps nV nF nD * opCostE (2 * (nV + nF + nD)) +
        pstExt nV nF nD ≤ 56000000 * ((nV + nF + nD) * lg (nV + nF + nD)) := by
  set N := nV + nF + nD with hNdef
  have hl1 : 1 ≤ lg N := one_le_lg N
  have hlog2 : Nat.log 2 (2 * N) = lg N := by
    unfold lg
    rw [mul_comm, Nat.log_mul_base (by norm_num) (by omega)]
  have hops : pstOps nV nF nD ≤ 156 * N := by unfold pstOps; omega
  have hcost : opCostE (2 * N) ≤ 353820 * lg N := by unfold opCostE; rw [hlog2]; omega
  have hext : pstExt nV nF nD ≤ 261 * N := by unfold pstExt; omega
  have h1 : pstOps nV nF nD * opCostE (2 * N) ≤ (156 * N) * (353820 * lg N) :=
    Nat.mul_le_mul hops hcost
  have h2 : N ≤ N * lg N := Nat.le_mul_of_pos_right N (by omega)
  nlinarith

/-- **On a plane map with `m ≥ 1` darts**, with `n = 2 (#V + #F + #D)` nodes and `nD = m`, the
bound is at most `504 000 000 · m lg m`, hence at most `504 000 000 · m lg² m`: the form of the
budget `PlanarFlow.BKMNW.SubCosts.Bounds.stflow` of the maximum-flow algorithm. -/
theorem pst_steps_le_m (hM : M.IsPlane) (hD : 1 ≤ Fintype.card D) :
    140 * (2 * (Fintype.card V + Fintype.card F + Fintype.card D) + 1) + 21 +
        pstOps (Fintype.card V) (Fintype.card F) (Fintype.card D) *
          opCostE (2 * (Fintype.card V + Fintype.card F + Fintype.card D)) +
        pstExt (Fintype.card V) (Fintype.card F) (Fintype.card D) ≤
      504000000 * (Fintype.card D * lg (Fintype.card D)) ∧
    504000000 * (Fintype.card D * lg (Fintype.card D)) ≤
      504000000 * Fintype.card D * lg (Fintype.card D) ^ 2 := by
  set m := Fintype.card D with hm
  have heul := hM.euler
  have hN : Fintype.card V + Fintype.card F + m ≤ 3 * m := by omega
  have h1 := pst_steps_le (nV := Fintype.card V) (nF := Fintype.card F) (nD := m) (by omega)
  have h2 : lg (Fintype.card V + Fintype.card F + m) ≤ 3 * lg m :=
    (lg_mono hN).trans (lg_three_mul m)
  have h3 : (Fintype.card V + Fintype.card F + m) * lg (Fintype.card V + Fintype.card F + m) ≤
      (3 * m) * (3 * lg m) := Nat.mul_le_mul hN h2
  have h4 : lg m ≤ lg m ^ 2 := by have := one_le_lg m; nlinarith
  refine ⟨by nlinarith, ?_⟩
  have : m * lg m ≤ m * lg m ^ 2 := Nat.mul_le_mul_left m h4
  nlinarith

/-! ### The preconditions can be met -/

open Classical in
/-- The real memory of the starting configuration: `w` in `WT` and `PH`, `kTh`, `kH0`, the
capacities in `CP`, the restriction in `RS`. -/
def pReal {nD : ℕ} (σ : D ≃ Fin nD) (w cap : D → ℤ) (rs : D → ℝ) (th h0 : ℤ) (a : ℕ) : ℝ :=
  if h : a < nD then (w (σ.symm ⟨a, h⟩) : ℝ)
  else if h' : a - nD < nD then (w (σ.symm ⟨a - nD, h'⟩) : ℝ)
  else if a = 3 * nD + 1 then (th : ℝ)
  else if a = 3 * nD + 2 then (h0 : ℝ)
  else if h₃ : 3 * nD + 3 ≤ a ∧ a - (3 * nD + 3) < nD then
    (cap (σ.symm ⟨a - (3 * nD + 3), h₃.2⟩) : ℝ)
  else if h₄ : 4 * nD + 3 ≤ a ∧ a - (4 * nD + 3) < nD then rs (σ.symm ⟨a - (4 * nD + 3), h₄.2⟩)
  else 0

open Classical in
/-- **The real memory of the starting configuration holds integers bounded by `W`**, when the
lengths, the capacities and the two constants are, and the restriction is `0` or `1`. -/
lemma pReal_int {nD : ℕ} (σ : D ≃ Fin nD) (w cap : D → ℤ) (rs : D → ℝ)
    (hrs : ∀ d, rs d = 0 ∨ rs d = 1) (th h0 W : ℤ) (hw : ∀ d, |w d| ≤ W)
    (hcap : ∀ d, |cap d| ≤ W) (hth : |th| ≤ W) (hh0 : |h0| ≤ W) (hW : 1 ≤ W) (a : ℕ) :
    ∃ z : ℤ, pReal σ w cap rs th h0 a = z ∧ |z| ≤ W := by
  unfold pReal
  split_ifs
  · exact ⟨_, rfl, hw _⟩
  · exact ⟨_, rfl, hw _⟩
  · exact ⟨_, rfl, hth⟩
  · exact ⟨_, rfl, hh0⟩
  · exact ⟨_, rfl, hcap _⟩
  · rcases hrs (σ.symm ⟨a - (4 * nD + 3), by omega⟩) with h | h
    · exact ⟨0, by rw [h]; simp, by simp; omega⟩
    · exact ⟨1, by rw [h]; simp, by simp; omega⟩
  · exact ⟨0, by simp, by simp; omega⟩

open Classical in
/-- **The perturbed maximum flow on the machine, end to end, for a family of perturbations `E`**
(`pstflowE_exec` with all its preconditions met, for `E` with the properties `PertOK`): for every
plane map with nonnegative capacities, `X` nonempty, a dart whose tail is in `Y`, and `X`, `Y` disjoint, there are an input
(the dual map, the darts leaving the source and the sink, the initial dual tree of `linit` and a
cotree of it, by orders), a word bound and a starting configuration (the perturbed lengths, the
capacities `capR c X Y`, the restriction and the constants in the real memory) from which
`pstProg` runs within `504 000 000 · m lg m` steps (`m` darts) and ends with
`OUT[d] = pstflowE M E c X Y d` for every dart, printing nothing; the real memory of the start
holds integers of absolute value at most `kH0` (with `N = 2 lexR + 1`). -/
theorem pstflowE_exec_exists {E : V → D → ℤ} (hM : M.IsPlane) {c : D → ℤ} (hc : ∀ d, 0 ≤ c d)
    {X Y : Finset V} (hX : X.Nonempty)
    (hY : ∃ d, M.tail d ∈ Y) (hXY : Disjoint X Y)
    (hE : ∀ (s t : V) (d₀ : D), s ≠ t → M.tail d₀ = t → PertOK M (capR M c X Y) (E t) s t d₀) :
    ∃ (n B : ℕ) (P : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card F + Fintype.card V + Fintype.card D) ∧
      Exec P (B + 16 * (n + 1)) (pstProg B (Fintype.card D) n) c₀ c' steps ∧
      steps ≤ 504000000 * (Fintype.card D * lg (Fintype.card D)) ∧
      (∀ d, c'.rmem (aOT (Fintype.card D) + Fintype.equivFin D d) = pstflowE M E c X Y d) ∧
      c'.output = c₀.output ∧
      ∀ a, ∃ z : ℤ, c₀.rmem a = z ∧
        |z| ≤ kH0 D F (2 * lexR F (E (M.tail hY.choose)) + 1) (capR M c X Y)
          (E (M.tail hY.choose)) := by
  have : Nonempty D := ⟨hY.choose⟩
  set s := hX.choose with hs
  set d₀ := hY.choose with hd₀
  set t := M.tail d₀ with ht
  have hst : s ≠ t := fun h => disjoint_left.1 hXY hX.choose_spec (by
    have := hY.choose_spec; rw [← hd₀, ← ht, ← h, hs] at this; exact this)
  set c' := capR M c X Y with hc'
  set ε := E t with hε
  have hPO : PertOK M c' ε s t d₀ := hE s t d₀ hst rfl
  obtain ⟨st, hlin, -, -, -, -⟩ := linit_spec hM (capR_nonneg (M := M) hc X Y)
    hPO.nonneg s t (M.face d₀)
  obtain ⟨d₁, hd₁⟩ := exists_dart_tail hM hst.symm
  obtain ⟨ιv, ιg, ιf, ιe, hL⟩ := exists_layout M.dual
  obtain ⟨C, hCr, hoff⟩ := exists_cotree (M := M.dual) hM.dual (toDD st.T) s
  have hOT := orders_exist (toDD st.T)
  have hOC := orders_exist C
  set vs := (univ : Finset F).toList
  set ts := depthOrder (toDD st.T)
  set fs := (univ : Finset V).toList
  set cs := depthOrder C
  set nD := Fintype.card D with hnD
  set n := 2 * (Fintype.card F + Fintype.card V + Fintype.card D) with hn
  set σ : D ≃ Fin nD := Fintype.equivFin D with hσdef
  set g : ℕ → D := fun i => if i = 0 then d₁ else d₀ with hg
  set P := kInput M.dual ∅ 0 σ ιv ιg ιf ιe n 2 g (toDD st.T) C vs ts fs cs with hP
  set B := P.data.sum + 9 * nD + 7 * n + 6 + n + 2 * nD + 7 * nD + 3 with hB
  set N : ℤ := 2 * lexR F ε + 1 with hN
  set rs : D → ℝ := fun d => if Inside M X Y d then 0 else 1 with hrs
  set c₀ : Config := { initConfig with
    rmem := (pReal σ (wlen N c' ε) c' rs (kTh D F N c' ε) (kH0 D F N c' ε)) } with hc₀
  have hσ : ∀ d : D, (σ d : ℕ) < nD := fun d => (σ d).2
  have hvl := hOT.flen
  have htl := hOT.ylen
  have hfl := hOC.flen
  have hcl := hOC.ylen
  have hFn : 2 * Fintype.card F ≤ n := hL.hv
  have hVn : 2 * Fintype.card V ≤ n := hL.hf
  have hD1 : 1 ≤ nD := Fintype.card_pos_iff.2 ⟨d₀⟩
  have hK : KInput M.dual ∅ 0 σ ιv ιg ιf ιe P := ⟨kInput_rv, kInput_nf, kInput_ne, kInput_ng,
    kInput_nt, kInput_nh, kInput_is, fun d _ => kInput_ln d, kInput_ed hL.dual⟩
  have hG : KBnd 2 g σ n P := fun i hi => kInput_gb hi
  have hI : KInit M.dual σ ιv ιf n 2 (toDD st.T) C vs ts fs cs P := by
    refine ⟨hOT, hOC, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_,
      ?_⟩
    · rw [kInput_iv (by omega)]; simp [List.getD_eq_getElem?_getD, hi]
    · rw [show iIT nD n 2 = iIV nD n 2 + 1 * n by unfold iIT; ring, kInput_it (by omega)]
      simp [List.getD_eq_getElem?_getD, hi]
    · rw [show iIF nD n 2 = iIV nD n 2 + 2 * n by unfold iIF; ring, kInput_if (by omega)]
      simp [List.getD_eq_getElem?_getD, hi]
    · rw [show iIC nD n 2 = iIV nD n 2 + 3 * n by unfold iIC; ring, kInput_ic (by omega)]
      simp [List.getD_eq_getElem?_getD, hi]
    · simpa using kInput_hd (M := M.dual) (S := ∅) (ℓ := 0) (σ := σ) (ιv := ιv) (ιg := ιg)
        (ιf := ιf) (ιe := ιe) (n := n) (k := 2) (g := g) (T := toDD st.T) (C := C) (vs := vs)
        (ts := ts) (fs := fs) (cs := cs) (i := 0) (by norm_num)
    · simpa using kInput_hd (M := M.dual) (S := ∅) (ℓ := 0) (σ := σ) (ιv := ιv) (ιg := ιg)
        (ιf := ιf) (ιe := ιe) (n := n) (k := 2) (g := g) (T := toDD st.T) (C := C) (vs := vs)
        (ts := ts) (fs := fs) (cs := cs) (i := 1) (by norm_num)
    · simpa using kInput_hd (M := M.dual) (S := ∅) (ℓ := 0) (σ := σ) (ιv := ιv) (ιg := ιg)
        (ιf := ιf) (ιe := ιe) (n := n) (k := 2) (g := g) (T := toDD st.T) (C := C) (vs := vs)
        (ts := ts) (fs := fs) (cs := cs) (i := 2) (by norm_num)
    · simpa using kInput_hd (M := M.dual) (S := ∅) (ℓ := 0) (σ := σ) (ιv := ιv) (ιg := ιg)
        (ιf := ιf) (ιe := ιe) (n := n) (k := 2) (g := g) (T := toDD st.T) (C := C) (vs := vs)
        (ts := ts) (fs := fs) (cs := cs) (i := 3) (by norm_num)
  have hPb : ∀ i, P.data.getD i 0 ≤ B + 16 * (n + 1) := fun i => by
    have h1 := layList_le (kRegs M.dual ∅ 0 σ ιv ιg ιf ιe n 2 g (toDD st.T) C vs ts fs cs) i
    rw [← kInput_data, ← hP] at h1
    omega
  have hσs : ∀ d (a : ℕ) (h : a < nD), (σ d : ℕ) = a → σ.symm ⟨a, h⟩ = d := fun d a h e => by
    rw [Equiv.symm_apply_eq]; exact Fin.ext e.symm
  have hwt : ∀ d, c₀.rmem (aWT + σ d) = wlen N c' ε d := fun d => by
    show pReal σ _ _ _ _ _ (aWT + σ d) = _
    simp only [pReal, aWT, zero_add, hσ d, ↓reduceDIte]
    rw [hσs d _ (hσ d) rfl]
  have hph : ∀ d, c₀.rmem (aPH nD + σ d) = wlen N c' ε d := fun d => by
    show pReal σ _ _ _ _ _ (aPH nD + σ d) = _
    have h1 : ¬ nD + (σ d : ℕ) < nD := by omega
    have h2 : nD + (σ d : ℕ) - nD < nD := by have := hσ d; omega
    simp only [pReal, aPH, h1, h2, ↓reduceDIte]
    rw [hσs d _ h2 (by omega)]
  have hcp : ∀ d, c₀.rmem (aCP nD + σ d) = c' d := fun d => by
    show pReal σ _ _ _ _ _ (aCP nD + σ d) = _
    have := hσ d
    have h1 : ¬ 3 * nD + 3 + (σ d : ℕ) < nD := by omega
    have h2 : ¬ 3 * nD + 3 + (σ d : ℕ) - nD < nD := by omega
    have h3 : 3 * nD + 3 + (σ d : ℕ) ≠ 3 * nD + 1 := by omega
    have h4 : 3 * nD + 3 + (σ d : ℕ) ≠ 3 * nD + 2 := by omega
    have h5 : 3 * nD + 3 ≤ 3 * nD + 3 + (σ d : ℕ) ∧ 3 * nD + 3 + (σ d : ℕ) - (3 * nD + 3) < nD :=
      ⟨by omega, by omega⟩
    simp only [pReal, aCP, h1, h2, h3, h4, h5, ↓reduceDIte, ↓reduceIte, and_self]
    rw [hσs d _ h5.2 (by omega)]
  have hrs' : ∀ d, c₀.rmem (aRS nD + σ d) = if Inside M X Y d then 0 else 1 := fun d => by
    show pReal σ _ _ _ _ _ (aRS nD + σ d) = _
    have := hσ d
    have h1 : ¬ 4 * nD + 3 + (σ d : ℕ) < nD := by omega
    have h2 : ¬ 4 * nD + 3 + (σ d : ℕ) - nD < nD := by omega
    have h3 : 4 * nD + 3 + (σ d : ℕ) ≠ 3 * nD + 1 := by omega
    have h4 : 4 * nD + 3 + (σ d : ℕ) ≠ 3 * nD + 2 := by omega
    have h5 : ¬ (3 * nD + 3 ≤ 4 * nD + 3 + (σ d : ℕ) ∧
        4 * nD + 3 + (σ d : ℕ) - (3 * nD + 3) < nD) := by omega
    have h6 : 4 * nD + 3 ≤ 4 * nD + 3 + (σ d : ℕ) ∧ 4 * nD + 3 + (σ d : ℕ) - (4 * nD + 3) < nD :=
      ⟨by omega, by omega⟩
    simp only [pReal, aRS, h1, h2, h3, h4, h5, h6, ↓reduceDIte, ↓reduceIte, and_self]
    rw [hσs d _ h6.2 (by omega)]
  have hth : c₀.rmem (aTH nD) = kTh D F N c' ε := by
    show pReal σ _ _ _ _ _ (aTH nD) = _
    have h1 : ¬ 3 * nD + 1 < nD := by omega
    have h2 : ¬ 3 * nD + 1 - nD < nD := by omega
    simp [pReal, aTH, h1, h2]
  have hh0 : c₀.rmem (aH0 nD) = kH0 D F N c' ε := by
    show pReal σ _ _ _ _ _ (aH0 nD) = _
    have h1 : ¬ 3 * nD + 2 < nD := by omega
    have h2 : ¬ 3 * nD + 2 - nD < nD := by omega
    simp [pReal, aH0, h1, h2]
  have hlr : 0 ≤ lexR F ε := by
    unfold lexR
    have : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => hPO.nonneg d
    positivity
  obtain ⟨c'', steps, e, hsteps, hOUT, hout⟩ := pstflowE_exec (E := E) (by omega) (by omega)
    (by omega) hPb hM hc hX hY hXY hPO hlin hd₁ (N := N)
    (by show 2 * lexR F ε < N; rw [hN]; omega) hL hK hG hI hoff hCr
    (c₀ := c₀) (wordsBounded_initConfig _ : WordsBounded (B + 16 * (n + 1)) c₀) hwt hph hcp hrs'
    hth hh0
  refine ⟨n, B, P, c₀, c'', steps, rfl, e, hsteps.trans ?_, hOUT, hout, fun a => ?_⟩
  · have := (pst_steps_le_m hM (by omega)).1
    rw [hn, show Fintype.card F + Fintype.card V + Fintype.card D =
      Fintype.card V + Fintype.card F + Fintype.card D by ring]
    exact this
  · -- the real memory: integers of absolute value at most `kH0`
    have hc0 : ∀ d, 0 ≤ c' d := capR_nonneg hc X Y
    have hS : 0 ≤ ∑ d, c' d := sum_nonneg fun d _ => hc0 d
    have hE0 : 0 ≤ ∑ d, ε d := sum_nonneg fun d _ => hPO.nonneg d
    have hεle : ∀ d, ε d ≤ lexR F ε := fun d => by
      have h1 : ε d ≤ ∑ d, ε d := single_le_sum (fun d _ => hPO.nonneg d) (mem_univ d)
      unfold lexR; nlinarith
    have hcle : ∀ d, c' d ≤ ∑ d, c' d := fun d => single_le_sum (fun d _ => hc0 d) (mem_univ d)
    have hZ : 0 ≤ kZ D F N c' ε := by unfold kZ; positivity
    have hTh : kTh D F N c' ε ≤ kH0 D F N c' ε := by
      unfold kH0; have : (0 : ℤ) ≤ (Fintype.card D + 2) * kZ D F N c' ε := by positivity
      linarith
    have hNpos : 1 ≤ N := by rw [hN]; omega
    have hw : ∀ d, |wlen N c' ε d| ≤ kH0 D F N c' ε := fun d => by
      have h1 := hεle d
      have h2 : N * c' d ≤ N * ∑ d, c' d := mul_le_mul_of_nonneg_left (hcle d) (by omega)
      have h3 : 0 ≤ N * c' d := mul_nonneg (by omega) (hc0 d)
      rw [abs_le]; unfold wlen
      constructor
      · have := hPO.nonneg d; unfold kH0 kTh at *; linarith
      · unfold kH0 kTh kZ at *; linarith
    have hcap : ∀ d, |c' d| ≤ kH0 D F N c' ε := fun d => by
      rw [abs_of_nonneg (hc0 d)]
      have h2 : ∑ d, c' d ≤ N * ∑ d, c' d := le_mul_of_one_le_left hS hNpos
      unfold kH0 kTh kZ at *
      have := hcle d
      linarith
    obtain ⟨z, hz, hzle⟩ := pReal_int σ (wlen N c' ε) c' rs (fun d => by
        simp only [hrs]; split_ifs <;> simp) (kTh D F N c' ε) (kH0 D F N c' ε)
      (kH0 D F N c' ε) hw hcap (by rw [abs_of_nonneg (by unfold kTh; omega)]; exact hTh)
      (by rw [abs_of_nonneg (by linarith [hTh, show 0 ≤ kTh D F N c' ε by unfold kTh; omega])])
      (by linarith [hTh, show 1 ≤ kTh D F N c' ε by unfold kTh; omega]) a
    exact ⟨z, hz, hzle⟩

open Classical in
/-- **The perturbed maximum flow on the machine, end to end** (`pstflowE_exec_exists` for
`pstflow`, the perturbation `lexEps`): for every plane map with transitive rotations and faces,
nonnegative capacities, `X` nonempty, a dart whose tail is in `Y`, and `X`, `Y` disjoint, there
are an input, a word bound and a starting configuration from which `pstProg` runs within
`504 000 000 · m lg m` steps (`m` darts) and ends with `OUT[d] = pstflow M c X Y d` for every
dart, printing nothing. -/
theorem pstflow_exec_exists (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    {c : D → ℤ} (hc : ∀ d, 0 ≤ c d) {X Y : Finset V} (hX : X.Nonempty)
    (hY : ∃ d, M.tail d ∈ Y) (hXY : Disjoint X Y) :
    ∃ (n B : ℕ) (P : Input) (c₀ c' : Config) (steps : ℕ),
      n = 2 * (Fintype.card F + Fintype.card V + Fintype.card D) ∧
      Exec P (B + 16 * (n + 1)) (pstProg B (Fintype.card D) n) c₀ c' steps ∧
      steps ≤ 504000000 * (Fintype.card D * lg (Fintype.card D)) ∧
      (∀ d, c'.rmem (aOT (Fintype.card D) + Fintype.equivFin D d) = pstflow M c X Y d) ∧
      c'.output = c₀.output := by
  simp only [pstflow_eq_E]
  obtain ⟨n, B, P, c₀, c', steps, h1, h2, h3, h4, h5, -⟩ :=
    pstflowE_exec_exists hM hc hX hY hXY fun s t d₀ hst hd₀ =>
      pertOK_lex hM hrot hface (capR_nonneg hc X Y) hst hd₀
  exact ⟨n, B, P, c₀, c', steps, h1, h2, h3, h4, h5⟩

end STFlow

end PlanarFlow
