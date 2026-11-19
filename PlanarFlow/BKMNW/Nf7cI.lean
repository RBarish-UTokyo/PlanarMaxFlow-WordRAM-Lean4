module

public import PlanarFlow.BKMNW.Nf7cH

/-!
# The final step of `fixP`: the meaning of its words

* **`lab_gv`**: the face labels of the prologue (`olab` of the frame's face walk `NX`) are the
  face identifiers `gv` of the frame's identifiers `layIds` (those of the negative-length call);
* **`face_mem_verts`**: a dart of a map that is not a loop of the dual has both faces among the
  vertices of the kept darts `repsN` of the dual (so the outcome of the negative call lists
  their potentials);
* `potM_miss` (a cell not written by `potP` keeps its value);
* **`ln_word`**: the three cases of `LN[i]` are the words `ℓ (en i) + K` of the lengths
  `ℓ = U − g` of the final call;
* **`fl_word`**: the word `flV` of a frame dart is `Z + (g + cob χ)(en i)` (the final flow).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab NegSSSP NegSSSP.Frame MfDrv NsStep
  WordRAM.Machine

universe w

/-! ### Face labels and identifiers -/

section Lab

variable {D : Type w} {V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {x : MCall M} {m : ℕ} {en : ℕ → D}
  {d : ℕ} {mem : ℕ → ℕ}

/-- **The face labels of the frame are the face identifiers of the negative-length call.** -/
theorem lab_gv (hP : PieceInv M x.1.piece x.2.1 x.2.2) (hl : Lay M gid u S T Z x m en d mem)
    (hm : 0 < m) (hft : (pmap hP).FaceTrans) {j : ℕ} (hj : j < m) :
    olab (nxF d m mem) j = (layIds hP hl hm hft).gv
      ((pmap hP).face (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm j)) := by
  have he := lay_enumOK hP hl hm hft
  rw [gv_face he _ hj]
  unfold labI
  refine olab_congr (fun i hi => ?_) hl.permOn_nx hj
  have h1 := (hl.nx_iter 1 i hi)
  simp only [Function.iterate_one] at h1
  unfold phiI
  have e : (pmap hP).next (layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm i) =
      layEn (pdarts M x.1.piece x.2.1) en m hl.en_mem hm (nxF d m mem i) := by
    apply Subtype.ext
    rw [layEn_val h1.1, h1.2]
    simp only [pmap, subMap_next, layEn_val hi]
    rfl
  rw [e, ixOf_en he h1.1]

end Lab

/-! ### The kept darts of the dual -/

section Reps

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]

/-- **The faces of a dart that is not a loop of the dual are vertices of the kept darts.** -/
theorem face_mem_verts (N : CombMap D V F) (μ : D → ℕ) {y : D} (hy : N.dual.tail y ≠ N.dual.head y) :
    N.dual.tail y ∈ verts N.dual (repsN N.dual μ) ∧
      N.dual.head y ∈ verts N.dual (repsN N.dual μ) := by
  set S := univ.filter fun x => N.dual.tail x = N.dual.tail y ∧ N.dual.head x = N.dual.head y
  have hS : S.Nonempty := ⟨y, by simp [S]⟩
  obtain ⟨x, hx, hmin⟩ := S.exists_min_image (ekeyN N.dual μ) hS
  simp only [S, mem_filter, mem_univ, true_and] at hx
  have hxr : x ∈ repsN N.dual μ := by
    rw [mem_repsN]
    refine ⟨by rw [hx.1, hx.2]; exact hy, fun x' h1 h2 => hmin x' ?_⟩
    simp only [S, mem_filter, mem_univ, true_and]
    exact ⟨h1.trans hx.1, h2.trans hx.2⟩
  unfold verts
  refine ⟨mem_union_left _ (mem_image.2 ⟨x, hxr, hx.1⟩),
    mem_union_right _ (mem_image.2 ⟨x, hxr, hx.2⟩)⟩

end Reps

/-! ### Words -/

/-- A cell that `potP` does not write keeps its value. -/
lemma potM_miss (nm : ℕ → ℕ) {IDb VLb POTb v z : ℕ} (h : ∀ v' < v, nm (IDb + v') + 1 ≠ z) :
    potM nm IDb VLb POTb v (POTb + z) = nm (POTb + z) := by
  induction v with
  | zero => rfl
  | succ v ih =>
    simp only [potM]
    rw [upd_other _ _ _ (by have := h v (by omega); omega)]
    exact ih fun v' hv' => h v' (by omega)

/-- **The words of the lengths of the final call.** -/
theorem ln_word {CP FLW CW CR FW Z K : ℕ} {U f₀ g Ur gd : ℤ}
    (hK : |U - g| ≤ K) :
    -- off the path
    ((CP : ℤ) = U → (FLW : ℤ) = Z + f₀ → g = f₀ →
      ((CP + Z + K - FLW : ℕ) : ℤ) = U - g + K) ∧
    -- the dart `d l` of the path
    ((CW : ℤ) = U → (FW : ℤ) = g + K → |g| ≤ K →
      ((CW + K + K - FW : ℕ) : ℤ) = U - g + K) ∧
    -- its reverse
    ((CR : ℤ) = Ur → (FW : ℤ) = gd + K → g = - gd → |Ur - g| ≤ K →
      ((CR + FW : ℕ) : ℤ) = Ur - g + K) := by
  refine ⟨fun h1 h2 h3 => ?_, fun h1 h2 h3 => ?_, fun h1 h2 h3 h4 => ?_⟩
  · have := (abs_le.1 hK).1
    have hle : FLW ≤ CP + Z + K := by omega
    push_cast [hle]; omega
  · have := (abs_le.1 h3).2
    have hle : FW ≤ CW + K + K := by omega
    push_cast [hle]; omega
  · push_cast; omega

/-- **The word of the final flow of a frame dart.** -/
theorem fl_word {CP Z K LN POTr POTf : ℕ} {U g χr χf : ℤ} {L : ℕ}
    (hCP : (CP : ℤ) = U) (hLN : (LN : ℤ) = U - g + K) (hg : |g| ≤ K)
    (hr : (POTr : ℤ) = χr + L) (hf : (POTf : ℤ) = χf + L) (hfin : 0 ≤ Z + (g + (χr - χf))) :
    ((CP + Z + K + K + POTr - LN - (POTf + K) : ℕ) : ℤ) = Z + (g + (χr - χf)) := by
  have := (abs_le.1 hg).1
  have h1 : LN ≤ CP + Z + K + K + POTr := by omega
  have h2 : POTf + K ≤ CP + Z + K + K + POTr - LN := by omega
  rw [Nat.cast_sub h2, Nat.cast_sub h1]
  push_cast
  omega

end BKMNW

end PlanarFlow
