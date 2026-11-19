module

public import PlanarFlow.BKMNW.PrSl
public import PlanarFlow.BKMNW.PrWalkP

/-!
# The index-level arrays of a map with loops

For any map on `Fin n` (loops allowed):

* `sgI_val` (`sgI x` is the rotation without loops at `x`, also on a loop), `sgI_iter_val`,
  **`sgI_permOn`**;
* **`phI_piI`**: `phI (piI x) = x`;
* **`vminI_eq_olab`**: on a dart that is not a loop, the least dart of its vertex is the orbit
  label of the rotation without loops (rotations transitive).

For the encoded map `map wf`: `wv_eq_sgI` (the walk computes `sgI`), `rvI_eq`, `phv_eq_phI`,
`cv_eq`, `cf_eq` (the masked flags).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap Feas OrbLab

section GenM

variable {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
variable (M : CombMap (Fin n) V F)

lemma sgI_val {x : ℕ} (hx : x < n) : sgI M x = (nlRot M ⟨x, hx⟩).val := by
  by_cases h : IsNl M x
  · exact sgI_fin M (d := ⟨x, hx⟩) h.2
  · have hm : (⟨x, hx⟩ : Fin n) ∉ nlDarts M := fun hm => h ⟨hx, hm⟩
    unfold sgI; rw [ppDiteF h]
    unfold nlRot; rw [ret_apply_of_not_mem hm]

lemma sgI_iter_val {x : ℕ} (hx : x < n) (j : ℕ) :
    (sgI M)^[j] x = ((nlRot M)^[j] ⟨x, hx⟩).val := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [iterate_succ_apply, iterate_succ_apply, sgI_val M hx, ih (Fin.isLt _)]

lemma sgI_permOn : PermOn (sgI M) n :=
  ⟨fun x hx => sgI_lt_gen M hx, fun x hx y hy e => by
    rw [sgI_val M hx, sgI_val M hy] at e
    exact congrArg Fin.val ((nlRot M).injective (Fin.ext e))⟩

lemma nlRot_iter_mem {d : Fin n} (hd : d ∈ nlDarts M) (j : ℕ) : (nlRot M)^[j] d ∈ nlDarts M := by
  induction j with
  | zero => exact hd
  | succ j ih => rw [iterate_succ_apply']; exact ret_mem ih

lemma tail_nlRot_iter (d : Fin n) (j : ℕ) : M.tail ((nlRot M)^[j] d) = M.tail d := by
  obtain ⟨N, hN⟩ := ret_iterate_eq (π := rotPerm M) (A := nlDarts M) d j
  unfold nlRot; rw [hN]
  exact tail_rot_iterate _ _

lemma phI_piI {x : ℕ} (hx : x < n) : phI M (piI M x) = x := by
  by_cases h : IsNl M x
  · let y : SDart (nlDarts M) := ⟨⟨x, hx⟩, h.2⟩
    have e1 : piI M x = (((nlMap M).toSep nlMap_rotTrans).φ.symm y).1.val := piI_val M y
    rw [e1, phI_phi M]
    simp [y]
  · have e1 : piI M x = x := by unfold piI; rw [ppDiteF h]
    rw [e1, phI_not M h]

lemma vminI_eq_olab (hrot : M.RotTrans) {x : ℕ} (hx : IsNl M x) :
    vminI M x = olab (sgI M) x := by
  have hxn := hx.lt
  unfold vminI; rw [ppDiteT hxn]
  have hex : ∃ y, IsNl M y ∧ tlF M y = some (M.tail ⟨x, hxn⟩) :=
    ⟨x, hx, tlF_fin M ⟨x, hxn⟩⟩
  obtain ⟨hv1, hv2⟩ := vminV_spec M hex
  apply le_antisymm
  · obtain ⟨t, ht⟩ := olab_mem (sgI M) x
    rw [← ht]
    apply vminV_min M hex
    · rw [sgI_iter_val M hxn]; exact (isNl_fin M).2 (nlRot_iter_mem M hx.2 t)
    · rw [sgI_iter_val M hxn, tlF_fin, tail_nlRot_iter]
  · have hlt := hv1.lt
    have htl : M.tail ⟨vminV M (M.tail ⟨x, hxn⟩), hlt⟩ = M.tail ⟨x, hxn⟩ := by
      have := hv2
      rw [show vminV M (M.tail ⟨x, hxn⟩) =
        ((⟨vminV M (M.tail ⟨x, hxn⟩), hlt⟩ : Fin n) : ℕ) from rfl, tlF_fin] at this
      exact Option.some.inj this
    obtain ⟨k, hk⟩ := hrot _ _ htl.symm
    have hmk : (rotPerm M)^[k] ⟨x, hxn⟩ ∈ nlDarts M := by
      rw [show (rotPerm M)^[k] ⟨x, hxn⟩ = M.rot^[k] ⟨x, hxn⟩ from rfl, hk]; exact hv1.2
    obtain ⟨j, hj, -⟩ := ret_reach (π := rotPerm M) (A := nlDarts M) k ⟨x, hxn⟩ hx.2 hmk
    calc olab (sgI M) x ≤ (sgI M)^[j] x := olab_min _ _ _
      _ = vminV M (M.tail ⟨x, hxn⟩) := by
        rw [sgI_iter_val M hxn]
        unfold nlRot; rw [hj]
        exact congrArg Fin.val hk

end GenM

section Enc

variable {d : List ℕ} (wf : Wf d)

lemma fl_mul_fl (p q : Prop) : fl p * fl q = fl (q ∧ p) := by
  classical
  unfold fl; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma rvI_eq {x : ℕ} (hx : x < nd d) : rvI (map wf) x = rv d x := by
  rw [show x = ((⟨x, hx⟩ : Fin (nd d)) : ℕ) from rfl, rvI_fin]; rfl

lemma wv_eq_sgI {x : ℕ} (hx : x < nd d) : wv (rotW d) (NlP d) x = sgI (map wf) x := by
  unfold wv
  by_cases h : NlP d x
  · rw [ppIteT h, sgI_eq_walk wf hx h]
  · rw [ppIteF h, sgI_loop wf h]

lemma phv_eq_phI {x : ℕ} (hx : x < nd d) :
    (if NlP d x then sgI (map wf) (rv d x) else x) = phI (map wf) x := by
  unfold phI
  by_cases h : NlP d x
  · rw [ppIteT h, ppIteT ((isNl_map_iff wf).2 ⟨hx, h⟩), rvI_eq wf hx]
  · rw [ppIteF h, ppIteF (fun h' => h ((isNl_map_iff wf).1 h').2)]

lemma nl_eq {x : ℕ} (hx : x < nd d) : fl (NlP d x) = fl (IsNl (map wf) x) :=
  fl_congr ⟨fun h => (isNl_map_iff wf).2 ⟨hx, h⟩, fun h => ((isNl_map_iff wf).1 h).2⟩

lemma cv_eq (hrot : (map wf).RotTrans) {x : ℕ} (hx : x < nd d) :
    fl (olab (sgI (map wf)) x + 1 = x + 1) * fl (NlP d x) = fl (CvI (map wf) x) := by
  rw [fl_mul_fl]
  apply fl_congr
  constructor
  · rintro ⟨h1, h2⟩
    have hn := (isNl_map_iff wf).2 ⟨hx, h1⟩
    exact ⟨hn, by rw [vminI_eq_olab _ hrot hn]; omega⟩
  · rintro ⟨hn, h2⟩
    rw [vminI_eq_olab _ hrot hn] at h2
    exact ⟨((isNl_map_iff wf).1 hn).2, by omega⟩

lemma cf_eq {x : ℕ} (hx : x < nd d) :
    fl (olab (phI (map wf)) x + 1 = x + 1) * fl (NlP d x) = fl (CfI (map wf) x) := by
  rw [fl_mul_fl]
  apply fl_congr
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(isNl_map_iff wf).2 ⟨hx, h1⟩, by unfold flI; omega⟩
  · rintro ⟨hn, h2⟩
    unfold flI at h2
    exact ⟨((isNl_map_iff wf).1 hn).2, by omega⟩

/-- The total capacity of the darts that are not loops. -/
lemma bigN_eq_sumL : bigN (map wf) (fun i => cp d i) =
    ∑ x ∈ range (nd d), fl (tl d (rv d x) ≠ tl d x) * cp d x := by
  classical
  unfold bigN
  rw [Finset.sum_coe_sort (nlDarts (map wf)) (fun x : Fin (nd d) => cp d x)]
  rw [← Fin.sum_univ_eq_sum_range (fun x => fl (tl d (rv d x) ≠ tl d x) * cp d x)]
  rw [nlDarts, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  have e : ((map wf).head x ≠ (map wf).tail x) ↔ tl d (rv d x) ≠ tl d x :=
    ⟨fun h e => h (Fin.ext e), fun h e => h (congrArg Fin.val e)⟩
  unfold fl
  by_cases h : tl d (rv d x) ≠ tl d x
  · simp [h, e.2 h]
  · have : ¬ ((map wf).head x ≠ (map wf).tail x) := fun h' => h (e.1 h')
    simp only [this, ↓reduceIte, h]; simp

end Enc

end Pp

end BKMNW

end PlanarFlow
