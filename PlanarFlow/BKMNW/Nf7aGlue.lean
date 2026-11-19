module

public import PlanarFlow.BKMNW.Nf7aPF

/-!
# The prologue of `fixP` at a node call: the meaning of its arrays

At a node call the prologue reads the frame (`Lay`) and the parts of the separator (`SegsOut`
from `Gb = r6807`). With **`callIn d m Gb π j Z mem`** (the natural input of `fpPro`):

* **`callIn_pre`**: the hypotheses of `fpPro_exec` that come from the frame and the parts
  (`hm hZ hns hoff hk`, `RV < m`, the rotation and the face walk are permutations, `PD l < m`);
* **`callIn_pd`**: the index `PD l` is the frame index of the dart `π.segs[j].d l`
  (`en (PD l) = π.segs[j].d l`), hence (with `segsP_get`) of the dart `πj.d l` of the piece map;
* **`callIn_cw`**, **`callIn_cr`**: `CW[l] = u (d l)`, `CR[l] = u (rev (d l))` (the capacities
  `c = U` of FixConservationOnPath);
* **`callIn_fw`**: `FW[l] = F0[l] = FLW[t] + K − Z` is `f₀ (d l) + K` (for `|f₀| ≤ K`);
* **`callIn_dv`**: `DV[l]` is `div f₀ (tail (d l)) + K` (for `|div f₀| ≤ K`);
* **`callIn_as`**: `AS = absSum U` (the sum of the capacities of the piece map).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

open Finset Function Equiv Orbit CombMap OrbLab MfDrv

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {gid : D → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The natural input of the prologue at a node call.** -/
def callIn (d m Gb : ℕ) (π : HSep M) (j Z : ℕ) (mem : ℕ → ℕ) : FpIn :=
  ⟨d, m, Gb, π.segs.length, ((π.segs.take j).map SPath.k).sum, (π.segs.map SPath.k).getD j 0, Z,
    mem⟩

section Call

variable {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}

lemma callIn_k {π : HSep M} {j : ℕ} (hj : j < π.segs.length) (Gb : ℕ) :
    (callIn d m Gb π j Z mem).k = (π.segs[j]).k := by
  simp [callIn, List.getD_eq_getElem?_getD, hj]

/-- **The darts of the path in the frame.** -/
theorem callIn_pd {π : HSep M} {lo hi Gb j : ℕ} (hS : SegsOut M en m π lo hi Gb mem)
    (hj : j < π.segs.length) {l : ℕ} (hl : l < (callIn d m Gb π j Z mem).k) :
    (callIn d m Gb π j Z mem).PD l < m ∧ en ((callIn d m Gb π j Z mem).PD l) = (π.segs[j]).d l := by
  rw [callIn_k hj] at hl
  obtain ⟨-, -, -, h4⟩ := hS
  obtain ⟨-, -, h⟩ := h4 j hj
  have e : (callIn d m Gb π j Z mem).PD l =
      mem (Gb + 1 + 2 * π.segs.length + ((π.segs.take j).map SPath.k).sum + l) := by
    simp only [FpIn.PD, FpIn.PDb, callIn]; congr 1; omega
  rw [e]; exact h l hl

/-- The block of the part `j` lies below the top of the parts. -/
theorem callIn_top {π : HSep M} {lo hi Gb j : ℕ} (hS : SegsOut M en m π lo hi Gb mem)
    (hj : j < π.segs.length) :
    (callIn d m Gb π j Z mem).PDb + (callIn d m Gb π j Z mem).k ≤ hi ∧
      Gb + 1 + j + π.segs.length < hi := by
  obtain ⟨-, -, h3, -⟩ := hS
  have hk := callIn_k (d := d) (m := m) (Z := Z) (mem := mem) hj Gb
  have hs : ((π.segs.take j).map SPath.k).sum + (π.segs[j]).k ≤ (π.segs.map SPath.k).sum := by
    have e : π.segs.take (j + 1) = π.segs.take j ++ [π.segs[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    have := sum_take_le_sum (π.segs.map SPath.k) (j + 1)
    rw [← List.map_take, e, List.map_append, List.sum_append] at this
    simpa using this
  simp only [FpIn.PDb, callIn] at hk ⊢
  constructor <;> omega

/-- **The hypotheses of `fpPro_exec` from the frame and the parts.** -/
theorem callIn_pre (hL : Lay M gid u S T Z x m en d mem) {π : HSep M} {lo hi Gb j : ℕ}
    (hS : SegsOut M en m π lo hi Gb mem) (hj : j < π.segs.length) :
    let p := callIn d m Gb π j Z mem
    p.mem p.d = p.m ∧ p.mem (p.d + 3) = p.Z ∧ p.mem p.Gb = p.ns ∧
      p.mem (p.Gb + 1 + j) = p.off ∧ p.mem (p.Gb + 1 + j + p.ns) = p.k ∧
      (∀ i < p.m, p.RV i < p.m) ∧ PermOn (sgF p.d p.m p.mem) p.m ∧
      PermOn (nxF p.d p.m p.mem) p.m ∧ (∀ l < p.k, p.PD l < p.m) := by
  intro p
  obtain ⟨h1, h2, h3, h4⟩ := hS
  obtain ⟨g1, g2, -⟩ := h4 j hj
  refine ⟨hL.hm, hL.hz, h2, g1, ?_, fun i hi => (hL.rv i hi).1, hL.permOn_sg, hL.permOn_nx,
    fun l hl => (callIn_pd ⟨h1, h2, h3, h4⟩ hj hl).1⟩
  show mem (Gb + 1 + j + π.segs.length) = (π.segs.map SPath.k).getD j 0
  rw [show Gb + 1 + j + π.segs.length = Gb + 1 + π.segs.length + j by omega, g2]
  simp [List.getD_eq_getElem?_getD, hj]

variable (hL : Lay M gid u S T Z x m en d mem) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
include hL

/-- **The capacities of the darts of the path.** -/
theorem callIn_cw {Gb : ℕ} {π : HSep M} {j i : ℕ} (hi : i < m) :
    ((callIn d m Gb π j Z mem).CP i : ℤ) = u (en i) := by
  have := (hL.cp i hi).1
  simp only [FpIn.CP, callIn]
  rw [show d + 4 + m + m + m + i = d + 4 + 3 * m + i by omega]; exact this

/-- The reverse in the frame. -/
theorem callIn_rv {Gb : ℕ} {π : HSep M} {j i : ℕ} (hi : i < m) :
    (callIn d m Gb π j Z mem).RV i < m ∧
      en ((callIn d m Gb π j Z mem).RV i) = M.rev (en i) := hL.rv i hi

/-- **The flow words**: `FLW[i] + K − Z = f₀ (en i) + K` when `|f₀| ≤ K`. -/
theorem callIn_fw {Gb : ℕ} {π : HSep M} {j i K : ℕ}
    {g : SDart (pdarts M x.1.piece x.2.1) → ℤ} (hfl : FLHas Z m d en mem g) (hi : i < m)
    (hK : |g ⟨en i, hL.en_mem i hi⟩| ≤ K) :
    (((callIn d m Gb π j Z mem).FLW i + K - Z : ℕ) : ℤ) = g ⟨en i, hL.en_mem i hi⟩ + K := by
  have h := hfl i hi
  rw [fext_mem g (hL.en_mem i hi)] at h
  have e : (callIn d m Gb π j Z mem).FLW i = mem (d + 4 + 6 * m + i) := by
    simp only [FpIn.FLW, callIn]; congr 1; omega
  rw [e]
  have := (abs_le.1 hK).1
  omega

/-- **The net outflow words**: `DVw l = div f₀ (tail (en (PD l))) + K` when `|div f₀| ≤ K`. -/
theorem callIn_dv {Gb : ℕ} {π : HSep M} {j : ℕ} {g : SDart (pdarts M x.1.piece x.2.1) → ℤ}
    (hfl : FLHas Z m d en mem g) {l : ℕ} (hl : (callIn d m Gb π j Z mem).PD l < m)
    (hK : |(pmap hP).div g ((pmap hP).tail (vDart hL hl))| ≤ (callIn d m Gb π j Z mem).K) :
    ((callIn d m Gb π j Z mem).DVw l : ℤ) =
      (pmap hP).div g ((pmap hP).tail (vDart hL hl)) + (callIn d m Gb π j Z mem).K := by
  have h := dvP_div hL hP hfl hl
  have ef : (fun j => mem (d + 6 * m + 4 + j)) = (callIn d m Gb π j Z mem).FLW := by
    funext i; simp only [FpIn.FLW, callIn]; congr 1; omega
  rw [ef] at h
  have key : ((callIn d m Gb π j Z mem).DVw l : ℤ) =
      ((dvS (olab (sgF d m mem)) (callIn d m Gb π j Z mem).FLW m
          (olab (sgF d m mem) ((callIn d m Gb π j Z mem).PD l)) + (callIn d m Gb π j Z mem).K -
        dvC (olab (sgF d m mem)) m (olab (sgF d m mem) ((callIn d m Gb π j Z mem).PD l)) * Z :
          ℕ) : ℤ) := rfl
  rw [key]
  have := (abs_le.1 hK).1
  generalize (callIn d m Gb π j Z mem).K = K at hK this ⊢
  generalize dvS (olab (sgF d m mem)) (callIn d m Gb π j Z mem).FLW m
    (olab (sgF d m mem) ((callIn d m Gb π j Z mem).PD l)) = A at h ⊢
  generalize dvC (olab (sgF d m mem)) m (olab (sgF d m mem) ((callIn d m Gb π j Z mem).PD l)) = B
    at h ⊢
  have hle : B * Z ≤ A + K := by
    have : ((B * Z : ℕ) : ℤ) ≤ ((A + K : ℕ) : ℤ) := by push_cast; nlinarith
    exact_mod_cast this
  rw [Nat.cast_sub hle]
  push_cast
  linarith

/-- **The sum of the capacities is `absSum` of the capacities of the piece map.** -/
theorem callIn_as {Gb : ℕ} {π : HSep M} {j : ℕ} :
    ((callIn d m Gb π j Z mem).AS : ℤ) =
      SPath.absSum (fun y : SDart (pdarts M x.1.piece x.2.1) => u y.1) := by
  unfold FpIn.AS SPath.absSum
  push_cast
  symm
  refine Finset.sum_bij' (fun y _ => Classical.choose (hL.en_surj y.1 y.2))
    (fun i hi => ⟨en i, hL.en_mem i (mem_range.1 hi)⟩) (fun y _ => ?_) (fun i hi => mem_univ _)
    (fun y _ => ?_) (fun i hi => ?_) (fun y _ => ?_)
  · exact mem_range.2 (Classical.choose_spec (hL.en_surj y.1 y.2)).1
  · exact Subtype.ext (Classical.choose_spec (hL.en_surj y.1 y.2)).2
  · have h1 := Classical.choose_spec (hL.en_surj (en i) (hL.en_mem i (mem_range.1 hi)))
    exact hL.en_inj h1.1 (mem_range.1 hi) h1.2
  · have h1 := Classical.choose_spec (hL.en_surj y.1 y.2)
    rw [callIn_cw hL h1.1, h1.2, abs_of_nonneg]
    rw [← h1.2, ← callIn_cw hL (Gb := Gb) (π := π) (j := j) h1.1]; positivity

end Call

end BKMNW

end PlanarFlow
