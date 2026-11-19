module

public import PlanarFlow.Klein.ExecNat
public import PlanarFlow.Klein.IsoExec

/-!
# Klein's masked program on the isolating lengths, on natural words only

`msspPlaneK_maskedNat`: `msspPlaneK_maskedIso` (`PlanarFlow/Klein/IsoExec.lean`) with the
natural-word program `kleinProgMN` (`PlanarFlow/Klein/ExecNat.lean`): for the cut along a simple
path, Klein's masked program on the isolating lengths `len'` of the cut runs **on natural words
only** (no real instruction, `kleinProgMN_natOnly`), with words at most `kleinWN B n Hc`
(`Hc < kleinHI + 1`, polynomial in the size of the cut and the largest isolating length, which
is below `N₁ (ℓ + 1)`), within `4 · 1642500000 (N lg N + p² lg N) + 3` steps, and
`msspPlaneK` at every pair of faces along the path is **read back exactly** from its natural
words: the natural word holding the isolated distance, divided by `N₁` (`kOutN`, the natural
division of `Int`/`ℕ`). No hypothesis bounds the lengths `ℓ`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

section Cuts

variable {M : CombMap D V F} {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
  [DecidableEq V'] [Fintype F'] [DecidableEq F'] {ℓ : D → ℤ} {L : List D}

/-- **The answers of `msspCutK` on the chosen cut, read from integer answers** whose quotients
by `N` are the distances of the cut. -/
theorem msspCutK_eq_outN
    (h : ∃ C : BKMNW.Cut M ℓ L D' V' F', SameReach C.map C.k C.g C.piece (pert C.len))
    {ℓ' : D' → ℤ} {N : ℕ}
    (hdiv : ∀ x v, (odist (pieceGraph h.choose.map h.choose.piece ℓ') x v).map (· / (N : ℤ)) =
      odist (pieceGraph h.choose.map h.choose.piece h.choose.len) x v)
    {x : F} (hx : ∃ j, j < h.choose.k ∧ h.choose.root j = x) (y : F) {t : ℕ} {X : ℕ → V'}
    {fl : ℕ → Bool} {out : ℕ → ℕ → Option ℤ}
    (hd : ∀ j < h.choose.k, fl j = true → ∀ i < t, out (kRank fl j) i =
      odist (pieceGraph h.choose.map h.choose.piece ℓ')
        (tripSrc h.choose.map h.choose.k h.choose.g j) (X i))
    (hfl : fl (Nat.find hx) = true) {i : ℕ} (hi : i < t) (hXi : X i = h.choose.vx y) :
    msspCutK M D' V' F' L ℓ x y = (out (kRank fl (Nat.find hx)) i).map (· / (N : ℤ)) := by
  rw [msspCutK_eq_odist h hx y, hd _ (Nat.find_spec hx).1 hfl i hi, hdiv, hXi]

end Cuts

section PathCut

variable {M : CombMap D V F}

/-- **`msspPlaneK_maskedIso` on natural words only.** For the cut along a simple path `P` of
`p ≥ 1` darts in a plane map with transitive rotations and faces, `N = #V + #F + #D`, there are
isolating lengths `len'` of the chosen cut `C` (`0 < len' d < N₁ (C.len d + 1)` on its piece,
`N₁ = isoN1 #V' #D' #F'`), a bound `Hc` with `kleinHI ≤ Hc < kleinHI + 1` of the compared
differences, an input, a starting configuration `c₀` of the real program and slots such that the
natural-word program `kleinProgMN` runs from `natCfg c₀` with words at most `kleinWN B n Hc`
within `4 · 1642500000 (N lg N + p² lg N) + 3` steps, and **`msspPlaneK` at every pair of faces
along the path is the natural word of the answer divided by `N₁`** (`kOutN`). -/
theorem msspPlaneK_maskedNat (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (P : SPath M) (ℓ : D → ℤ) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) (hk : 0 < P.k) :
    ∃ (C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts))
      (len' : CutD M P.darts → ℤ) (n B kk Hc : ℕ) (Pin : Input) (c₀ d' : Config) (steps : ℕ)
      (slot : F → ℕ),
      Hyp C.map C.k C.g C.piece len' ∧
      (∀ d ∈ C.piece, 0 < len' d ∧ len' d < isoN1 (Fintype.card (CutV M P.darts))
        (Fintype.card (CutD M P.darts)) (Fintype.card (CutF M P.darts)) * (C.len d + 1)) ∧
      kleinHI (CutV M P.darts) (CutF M P.darts) C.piece len' kk ≤ Hc ∧
      (Hc : ℝ) < kleinHI (CutV M P.darts) (CutF M P.darts) C.piece len' kk + 1 ∧
      Exec Pin (kleinWN B n Hc)
        (kleinProgMN B (Fintype.card (CutD M P.darts)) n kk P.faces.card Hc)
        (natCfg 201 (B + 16 * (n + 1)) (2 * Hc + 1) (B + 16 * (n + 1) + 1) c₀) d' steps ∧
      steps ≤ 4 * (1642500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        P.k ^ 2 * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D))) + 3 ∧
      (∀ x ∈ P.faces, ∀ y ∈ P.faces, msspPlaneK M P.darts ℓ x y =
        (kOutN (Fintype.card (CutD M P.darts)) n kk P.faces.card (B + 16 * (n + 1) + 1) d'
          (slot x) (P.faces.toList.idxOf y)).map
          (· / (isoN1 (Fintype.card (CutV M P.darts)) (Fintype.card (CutD M P.darts))
            (Fintype.card (CutF M P.darts)) : ℤ))) ∧
      d'.output = c₀.output := by
  classical
  obtain ⟨C, -, hRe⟩ := cut_hyp_sameReach hM hrot hface P ℓ hnn hk
  have h : ∃ C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts),
      SameReach C.map C.k C.g C.piece (pert C.len) := ⟨C, hRe⟩
  set C' := h.choose with hC'
  obtain ⟨w, -, hwB, hHyp, hlen, hdiv⟩ :=
    C'.hyp.exists_iso (Fintype.equivFin (CutD M P.darts)) (C'.map.face (C'.g 0))
  set ℓ' := isoLen (Fintype.card (CutV M P.darts)) (Fintype.card (CutD M P.darts))
    (Fintype.card (CutF M P.darts)) w (fun d => (Fintype.equivFin (CutD M P.darts) d : ℕ))
    C'.len with hℓ'
  have hιm : ∀ d, ((Fintype.equivFin (CutD M P.darts) d : ℕ)) < Fintype.card (CutD M P.darts) :=
    fun d => (Fintype.equivFin (CutD M P.darts) d).isLt
  have hR₀ : SameReach C'.map C'.k C'.g C'.piece C'.len :=
    sameReach_congr (fun x y => (isPerturb_pert C'.map C'.piece C'.len).reach_iff.symm)
      h.choose_spec
  have hR' : SameReach C'.map C'.k C'.g C'.piece ℓ' :=
    sameReach_congr (fun x y => reach_iso_iff hwB le_rfl hιm C'.hyp.nonneg) hR₀
  set ys := P.faces.toList with hys
  have hyl : ys.length = P.faces.card := Finset.length_toList _
  set X : ℕ → CutV M P.darts := fun i => C'.vx (ys.getD i (M.face (P.d 0))) with hXdef
  have hX : ∀ i < ys.length, ¬ IsRoot C'.map C'.k C'.g (X i) :=
    fun i _ ⟨j, hj, he⟩ => C'.root_ne j hj _ he
  obtain ⟨n, B, Hc, Pin, c₀, d', steps, -, hHc, hHc', e, hsteps, hd, hout⟩ :=
    kleinM_exec_exists_nat hHyp hR' ys.length X hX (cutFlag C')
  rw [hyl] at e hsteps hd
  have hf : kRank (cutFlag C') C'.k ≤ 2 * P.k :=
    (kRank_cutFlag_le C' C'.k).trans P.card_faces_le
  refine ⟨C', ℓ', n, B, C'.k, Hc, Pin, c₀, d', steps, fun x =>
    if hx : ∃ j, j < C'.k ∧ C'.root j = x then kRank (cutFlag C') (Nat.find hx) else 0, hHyp,
    hlen, hHc, hHc', e, hsteps.trans ?_, fun x hx y hy => ?_, hout⟩
  · -- the cost
    set N := Fintype.card V + Fintype.card F + Fintype.card D with hN
    set N' := Fintype.card (CutV M P.darts) + Fintype.card (CutF M P.darts) +
      Fintype.card (CutD M P.darts) with hN'
    have hN1 : 1 ≤ N := by
      have : 0 < Fintype.card D := Fintype.card_pos_iff.2 ⟨P.d 0⟩
      omega
    have hNN : N' ≤ 9 * N := by have := card_cut_le (M := M) P.darts; omega
    have hl : BKMNW.lg N' ≤ 5 * BKMNW.lg N := by
      have h1 := BKMNW.lg_mono (show N' ≤ 16 * N by omega)
      rw [lg_16_mul hN1] at h1
      have := BKMNW.one_le_lg N
      omega
    have ht : P.faces.card ≤ 2 * P.k := P.card_faces_le
    have hft : kRank (cutFlag C') C'.k * P.faces.card ≤ 4 * P.k ^ 2 := by
      have := Nat.mul_le_mul hf ht
      nlinarith
    have a1 : N' * BKMNW.lg N' ≤ 45 * (N * BKMNW.lg N) := by
      have := Nat.mul_le_mul hNN hl
      nlinarith
    have a2 : kRank (cutFlag C') C'.k * P.faces.card * BKMNW.lg N' ≤
        20 * (P.k ^ 2 * BKMNW.lg N) := by
      have := Nat.mul_le_mul hft hl
      nlinarith
    omega
  · -- the answers
    have hxL : x ∈ (P.darts.map M.face).toFinset := hx
    obtain ⟨j, hj, hjx⟩ := C'.srcs x hxL
    have hx' : ∃ j, j < C'.k ∧ C'.root j = x := ⟨j, hj, hjx⟩
    have hyl' : ys.idxOf y < ys.length := List.idxOf_lt_length_iff.2 (Finset.mem_toList.2 hy)
    have hXi : X (ys.idxOf y) = C'.vx y := by
      simp only [hXdef]
      rw [List.getD_eq_getElem?_getD, List.getElem?_idxOf (Finset.mem_toList.2 hy)]
      rfl
    simp only [hx', ↓reduceDIte]
    exact msspCutK_eq_outN h hdiv hx' y hd (cutFlag_find C' hxL hx') (by rw [← hyl]; exact hyl')
      hXi

end PathCut

end Klein

end PlanarFlow
