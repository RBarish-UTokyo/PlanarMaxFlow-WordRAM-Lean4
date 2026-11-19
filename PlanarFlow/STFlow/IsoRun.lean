module

public import PlanarFlow.STFlow.IsoDef

/-!
# The perturbed algorithm with the word-size perturbation

The single-source single-sink maximum flow `pstflowW`: the perturbed run of
`PlanarFlow/STFlow/Lex.lean` (`linit`, `lrun`, as for `pstflow`) with the perturbation of
polynomial size `isoEps M t = isoL + isoW M t` (`PlanarFlow/STFlow/IsoDef.lean`) for the sink `t`
chosen by the algorithm, in place of `lexEps`. The first coordinate of the run is the algorithm
itself with a particular choice of the bottleneck, so it computes a maximum flow for every
nonnegative perturbation:

* `pcoreFlowW_spec`, `pstflowW_spec`: **`pstflowW` meets `STFlowSpec`** on every plane map.

Its pivot bound (`PlanarFlow/STFlow/IsoCost.lean`, at most `m + 1` steps) and its machine
realization with keys of polynomial size (`PlanarFlow/STFlow/IsoExec.lean`) are proved separately.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

variable (M) in
/-- **The perturbed run with the word-size perturbation** from the initial shortest-path tree of
the dual rooted at `o`. -/
noncomputable def pcoreRunW (c : D → ℤ) (s t : V) (o : F) : Option (LSt M × ℕ × Bool) :=
  (linit M c (isoEps M t) s t o).map (lrun M c (isoEps M t) s t (fuel F))

variable (M) in
/-- The flow computed by `pcoreRunW`. -/
noncomputable def pcoreFlowW (c : D → ℤ) (s t : V) (o : F) : D → ℤ :=
  match pcoreRunW M c s t o with
  | some r => r.1.g
  | none => 0

/-- **Correctness of the run with the word-size perturbation.** -/
theorem pcoreFlowW_spec (hM : M.IsPlane) [Nonempty D] {c : D → ℤ} (hc : ∀ d, 0 ≤ c d)
    {s t : V} (hst : s ≠ t) (o : F) :
    IsPseudo M c (pcoreFlowW M c s t o) ∧
      (∀ v, v ≠ s → v ≠ t → M.div (pcoreFlowW M c s t o) v = 0) ∧
      NoPath M c (pcoreFlowW M c s t o) {s} {t} := by
  obtain ⟨st, hst0, -, hI, -⟩ := linit_spec hM hc (fun d => isoEps_nonneg hM t d) s t o
  obtain ⟨h1, h2, -, h4⟩ := st.T.chi_spec hM s t
  have hP : IsUnit (M := M) (s := s) (t := t) (st.T.chi s t) := ⟨h1, h2, h4⟩
  have := lrun_spec hM hst hP hI (n := fuel F) (by unfold fuel; omega)
  simpa [pcoreFlowW, pcoreRunW, hst0] using this

variable (M) in
open Classical in
/-- **SingleSourceSingleSinkMaxFlow with the word-size perturbation**, from the vertex set `X` to
the vertex set `Y`: as `pstflow`, with `isoEps` in place of `lexEps`. -/
noncomputable def pstflowW (c : D → ℤ) (X Y : Finset V) : D → ℤ :=
  if h : X.Nonempty ∧ ∃ d, M.tail d ∈ Y then
    restrictR M X Y
      (pcoreFlowW M (capR M c X Y) h.1.choose (M.tail h.2.choose) (M.face h.2.choose))
  else 0

/-- **The implementation with the word-size perturbation meets `STFlowSpec`** on every plane
map. -/
theorem pstflowW_spec (hM : M.IsPlane) : STFlowSpec M (pstflowW M) := by
  classical
  intro c πs πt hc hXY
  have hXne : πs.verts.Nonempty := ⟨_, πs.p_mem_init (Nat.zero_le _)⟩
  have hY : (πt.p 0) ∈ πt.verts := πt.p_mem_init (Nat.zero_le _)
  have hne : πs.p 0 ≠ πt.p 0 := fun h => disjoint_left.1 hXY (πs.p_mem_init (Nat.zero_le _))
    (h ▸ hY)
  obtain ⟨d₀, hd₀⟩ := exists_dart_tail hM hne
  have hex : πs.verts.Nonempty ∧ ∃ d, M.tail d ∈ πt.verts := ⟨hXne, d₀, hd₀ ▸ hY⟩
  have : Nonempty D := ⟨d₀⟩
  unfold pstflowW
  simp only [hex, and_self, ↓reduceDIte]
  have hs := hex.1.choose_spec
  have ht := hex.2.choose_spec
  have hst : hex.1.choose ≠ M.tail hex.2.choose := fun h => disjoint_left.1 hXY hs (h ▸ ht)
  obtain ⟨h1, h2, h3⟩ := pcoreFlowW_spec hM (capR_nonneg (M := M) hc πs.verts πt.verts) hst
    (M.face hex.2.choose)
  exact stOut_restrictR hc πs πt hXY hs ht h1 h2 h3

end STFlow

end PlanarFlow
