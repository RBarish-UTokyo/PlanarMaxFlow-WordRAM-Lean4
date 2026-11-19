module

public import PlanarFlow.Klein.ProgExistsMask
public import PlanarFlow.MSSP.Isolate

/-!
# Klein's masked program on the isolating lengths

`PlanarFlow/Klein/ProgExistsMask.lean` runs Klein's program on the cut of the dual graph along a
path with the perturbed lengths `MSSP.pert` (numbers of `Θ(m)` bits). Klein's correctness takes
any lengths meeting `Hyp`; here the program is run on the **isolating lengths**
`MSSP.isoLen n m B w ι ℓ` of `PlanarFlow/MSSP/Isolate.lean` (`n = #V'`, `m = #D'`, `B = #F'` of
the cut, `ι` a numbering of its darts, `w` an isolating weight with `|w| ≤ #F'`), which are
**polynomially bounded**: `0 < isoLen ℓ d < N₁ (ℓ d + 1)`, `N₁ = isoN1 n m B =
(n m + 1)(2 B n + 1)(n + 1)`.

* `sameReach_congr`: `SameReach` depends only on the reachability of the piece.
* `outNI N o`: the integer part of a real answer divided by `N` (the answers of the isolating
  lengths divided by `N₁` are the distances, `MSSP.odist_isoLen`).
* `msspCutK_eq_odist`: the answers of `msspCutK` on the chosen cut are the distances of the cut
  with its own lengths.
* `msspPlaneK_maskedIso`: **`msspPlaneK_masked` with the isolating lengths**: the masked program
  on the chosen cut with lengths `len'` meeting `0 < len' d < N₁ (C.len d + 1)` on the piece runs
  within the same bound of steps and its output holds `msspPlaneK` at every pair of faces along
  the path, read by `outNI N₁`.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace Klein

open Finset CombMap MSSP STFlow DynTree WordRAM WordRAM.Machine BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- `SameReach` depends only on the reachability of the piece. -/
lemma sameReach_congr {M : CombMap D V F} {k : ℕ} {g : ℕ → D} {S : Finset D} {ℓ ℓ' : D → ℤ}
    (h : ∀ x y, Reach (pieceGraph M S ℓ') x y ↔ Reach (pieceGraph M S ℓ) x y)
    (hR : SameReach M k g S ℓ) : SameReach M k g S ℓ' :=
  fun i hi j hj v hv hr => (h _ _).2 (hR i hi j hj v hv ((h _ _).1 hr))

/-- The integer part of an answer divided by `N`. -/
def outNI (N : ℕ) (o : Option ℝ) : Option ℤ := o.map fun r => Int.floor r / (N : ℤ)

lemma outNI_map (N : ℕ) (o : Option ℤ) :
    outNI N (o.map ((↑) : ℤ → ℝ)) = o.map (· / (N : ℤ)) := by
  unfold outNI
  rw [Option.map_map]
  congr 1
  funext z
  simp

section Cuts

variable {M : CombMap D V F} {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V']
  [DecidableEq V'] [Fintype F'] [DecidableEq F'] {ℓ : D → ℤ} {L : List D}

/-- **The answers of `msspCutK` on the chosen cut are the distances of the cut** with its own
lengths, from the source of the first move of the face `x`. -/
theorem msspCutK_eq_odist
    (h : ∃ C : BKMNW.Cut M ℓ L D' V' F', SameReach C.map C.k C.g C.piece (pert C.len))
    {x : F} (hx : ∃ j, j < h.choose.k ∧ h.choose.root j = x) (y : F) :
    msspCutK M D' V' F' L ℓ x y =
      odist (pieceGraph h.choose.map h.choose.piece h.choose.len)
        (tripSrc h.choose.map h.choose.k h.choose.g (Nat.find hx)) (h.choose.vx y) := by
  classical
  simp only [msspCutK, h, ↓reduceDIte, BKMNW.Cut.answerK, hx]
  rw [kleinNN_eq]

/-- **The answers of `msspPlaneK` on the chosen cut are read from the output of the masked
program run on lengths `ℓ'`** whose answers divided by `N` are those of the cut's lengths. -/
theorem msspCutK_eq_outI
    (h : ∃ C : BKMNW.Cut M ℓ L D' V' F', SameReach C.map C.k C.g C.piece (pert C.len))
    {ℓ' : D' → ℤ} {N : ℕ}
    (hdiv : ∀ x v, (odist (pieceGraph h.choose.map h.choose.piece ℓ') x v).map (· / (N : ℤ)) =
      odist (pieceGraph h.choose.map h.choose.piece h.choose.len) x v)
    {x : F} (hx : ∃ j, j < h.choose.k ∧ h.choose.root j = x) (y : F) {t : ℕ} {X : ℕ → V'}
    {fl : ℕ → Bool} {out : ℕ → ℕ → Option ℝ}
    (hd : ∀ j < h.choose.k, fl j = true → ∀ i < t, out (kRank fl j) i =
      (odist (pieceGraph h.choose.map h.choose.piece ℓ')
        (tripSrc h.choose.map h.choose.k h.choose.g j) (X i)).map ((↑) : ℤ → ℝ))
    (hfl : fl (Nat.find hx) = true) {i : ℕ} (hi : i < t) (hXi : X i = h.choose.vx y) :
    msspCutK M D' V' F' L ℓ x y = outNI N (out (kRank fl (Nat.find hx)) i) := by
  rw [msspCutK_eq_odist h hx y, hd _ (Nat.find_spec hx).1 hfl i hi, outNI_map, hdiv, hXi]

end Cuts

section PathCut

variable {M : CombMap D V F}

/-- **`msspPlaneK_masked` on the isolating lengths.** For the cut along a simple path `P` of
`p ≥ 1` darts in a plane map with transitive rotations and faces, `N = #V + #F + #D`, there are
lengths `len'` of the chosen cut `C` with `0 < len' d < N₁ (C.len d + 1)` on its piece
(`N₁ = isoN1 #V' #D' #F'` of the cut: the isolating lengths), an input, a starting configuration,
flags and slots, such that `kleinProgM` on the cut with the lengths `len'` (its input holds them)
runs within `1642500000 (N lg N + p² lg N)` steps, and its output holds **`msspPlaneK` at every
pair of faces along the path**, read by `outNI N₁`: the integer part divided by `N₁`. -/
theorem msspPlaneK_maskedIso (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (P : SPath M) (ℓ : D → ℤ) (hnn : ∀ e, e ∉ P.darts → 0 ≤ ℓ e) (hk : 0 < P.k) :
    ∃ (C : Cut M ℓ P.darts (CutD M P.darts) (CutV M P.darts) (CutF M P.darts))
      (len' : CutD M P.darts → ℤ) (n B kk : ℕ) (Pin : Input) (c₀ c' : Config) (steps : ℕ)
      (fl : ℕ → Bool) (slot : F → ℕ),
      Hyp C.map C.k C.g C.piece len' ∧
      (∀ d ∈ C.piece, 0 < len' d ∧ len' d < isoN1 (Fintype.card (CutV M P.darts))
        (Fintype.card (CutD M P.darts)) (Fintype.card (CutF M P.darts)) * (C.len d + 1)) ∧
      Exec Pin (B + 16 * (n + 1))
        (kleinProgM B (Fintype.card (CutD M P.darts)) n kk P.faces.card) c₀ c' steps ∧
      kRank fl kk ≤ 2 * P.k ∧
      steps ≤ 1642500000 * ((Fintype.card V + Fintype.card F + Fintype.card D) *
          BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D) +
        P.k ^ 2 * BKMNW.lg (Fintype.card V + Fintype.card F + Fintype.card D)) ∧
      (∀ x ∈ P.faces, ∀ y ∈ P.faces, msspPlaneK M P.darts ℓ x y =
        outNI (isoN1 (Fintype.card (CutV M P.darts)) (Fintype.card (CutD M P.darts))
            (Fintype.card (CutF M P.darts)))
          (kOutM (Fintype.card (CutD M P.darts)) n kk P.faces.card c' (slot x)
            (P.faces.toList.idxOf y))) ∧
      c'.output = c₀.output := by
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
  obtain ⟨n, B, Pin, c₀, c', steps, -, e, hsteps, -, hd, hout⟩ :=
    kleinM_exec_exists hHyp hR' ys.length X hX (cutFlag C')
  rw [hyl] at e hsteps hd
  have hf : kRank (cutFlag C') C'.k ≤ 2 * P.k :=
    (kRank_cutFlag_le C' C'.k).trans P.card_faces_le
  refine ⟨C', ℓ', n, B, C'.k, Pin, c₀, c', steps, cutFlag C', fun x =>
    if hx : ∃ j, j < C'.k ∧ C'.root j = x then kRank (cutFlag C') (Nat.find hx) else 0, hHyp,
    hlen, e, hf, hsteps.trans ?_, fun x hx y hy => ?_, hout⟩
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
    exact msspCutK_eq_outI h hdiv hx' y hd (cutFlag_find C' hxL hx') (by rw [← hyl]; exact hyl')
      hXi

end PathCut

end Klein

end PlanarFlow
