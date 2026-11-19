module

public import PlanarFlow.BKMNW.NsProg

/-!
# From the machine arrays of the negSSSP step to the root frame (pure)

* `card_eq_m` (`Fintype.card D = m`), `kpI` (the keep flag `0`/`1`), **`kflag_eq_kpI`** (the flag
  of pass 2 is `kpI`), `vE_eq`, **`mln_eq`** (the least length of pass 2), `cLG_kpI`, `rLG_kpI`
  (the machine lists are `cLi`, `rLp`), `fLG_eq`, **`dset_rcl`** (the deleted set is the
  closure), `retRep_univ` (the arrays of the face permutation and its inverse represent
  `ret (rotPerm M.dual) univ`);
* **`inP_of_W5`**: the words written by `wrProg` from these arrays are the input part `InP` of the
  root frame for `nsIds`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace NsStep

open Finset Function Equiv Orbit CombMap NegSSSP NegSSSP.Frame OrbLab WordRAM WordRAM.Machine

universe w

variable {D V F : Type w} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F] {M : CombMap D V F} {en : ℕ → D} {m : ℕ}

variable (h : EnumOK M en m) (d₀ : D)
include h

lemma card_eq_m : Fintype.card D = m := by
  have := sum_en h (fun _ => (1 : ℤ))
  simp only [sum_const, card_univ, card_range, nsmul_eq_mul, mul_one] at this
  exact_mod_cast this

variable (M en m) in
/-- The keep flag `0`/`1`. -/
noncomputable def kpI (j : ℕ) : ℕ := if keepB M en m h d₀ j = true then 1 else 0

lemma kpI_le (j : ℕ) : kpI M en m h d₀ j ≤ 1 := by unfold kpI; split_ifs <;> omega

omit h in
lemma vE_eq : vE (rvI M en m) m = fun j => m - ekI M en m j := by
  funext j; unfold vE ekI; omega

/-- **The flag of pass 2 is the keep flag.** -/
theorem kflag_eq_kpI {j : ℕ} (hj : j < m) :
    kflag (labI M en m j + 1) (labI M en m (rvI M en m j) + 1)
      ((grpP (labI M en m) (rvI M en m) (m + 1) m j).sup (vE (rvI M en m) m))
      (vE (rvI M en m) m j) = kpI M en m h d₀ j := by
  rw [kflag_eq, vE_eq]
  have e : grpP (labI M en m) (rvI M en m) (m + 1) m j = grpI M en m j := rfl
  rw [e]
  unfold kpI keepB
  have := mem_repsN_iff h d₀ hj
  by_cases hk : en j ∈ repsN M.dual (nsIds M h d₀).gd
  · rw [decide_eq_true hk]
    obtain ⟨h1, h2⟩ := this.1 hk
    simp only [↓reduceIte]
    rw [iteT ⟨by omega, h2⟩]
  · rw [decide_eq_false hk]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine iteF fun ⟨h1, h2⟩ => hk (this.2 ⟨by omega, h2⟩)

/-- **The least length of pass 2.** -/
theorem mln_eq (ℓ : D → ℤ) (K : ℕ) (hK : ∀ j < m, |ℓ (en j)| ≤ K) {i : ℕ} (hi : i < m) :
    ((2 * K - (grpP (labI M en m) (rvI M en m) (m + 1) m i).sup
      (vL (fun j => (ℓ (en j) + K).toNat) (2 * K)) : ℕ) : ℤ) = minLen M.dual ℓ (en i) + K :=
  minLen_eq h ℓ K (2 * K) (fun j hj => by have := hK j hj; rw [abs_le] at this; omega)
    (fun j hj => by have := hK j hj; rw [abs_le] at this; push_cast; omega) hi

lemma cLG_kpI : cLG (kpI M en m h d₀) m = cLi M en m h d₀ := by
  unfold cLG cLi cLp
  congr 1
  funext j
  unfold kpI
  by_cases hk : keepB M en m h d₀ j = true <;> simp [hk]

lemma rLG_kpI (t : ℕ) : rLG (kpI M en m h d₀) (rvI M en m) (cLi M en m h d₀) t =
    rLp M en m h d₀ t := by
  unfold rLG rLp
  congr 2
  funext x
  unfold kpI
  by_cases hk : keepB M en m h d₀ (rvI M en m x) = true <;> simp [hk]

lemma fLG_eq : cLG (kpI M en m h d₀) m ++ rLG (kpI M en m h d₀) (rvI M en m)
    (cLG (kpI M en m h d₀) m) (cLG (kpI M en m h d₀) m).length = fLi M en m h d₀ := by
  rw [cLG_kpI, rLG_kpI, rLp_full]; rfl

/-- **The deleted set is the closure.** -/
theorem dset_rcl (DF : ℕ → ℕ) (hDF : ∀ j < m, (0 < DF j ↔ j ∉ fLi M en m h d₀)) :
    dset en DF univ m = rcl M.dual (repsN M.dual (nsIds M h d₀).gd) := by
  ext d
  unfold dset
  rw [mem_filter]
  simp only [mem_univ, true_and]
  constructor
  · intro H
    by_contra hd
    have hx := ixOf_lt h d
    have hnot : ixOf en m d ∉ fLi M en m h d₀ := fun hm => hd (by
      have := (mem_fLi_iff h d₀ hx).1 hm
      rwa [en_ixOf h d] at this)
    exact H _ hx ((hDF _ hx).2 hnot) (en_ixOf h d)
  · intro hd j hj hp e
    exact (hDF j hj).1 hp ((mem_fLi_iff h d₀ hj).2 (e ▸ hd))

/-- The face permutation and its inverse represent the first return to everything. -/
theorem retRep_univ (mem : ℕ → ℕ) (NXb PRb : ℕ) (hNX : ∀ i < m, mem (NXb + i) = phiI M en m i)
    (hPR : ∀ i < m, mem (PRb + i) < m ∧ en (mem (PRb + i)) = (rotPerm M.dual).symm (en i)) :
    BKMNW.RetRep en m (rotPerm M.dual) univ mem NXb PRb := fun i hi _ => by
  rw [ret_univ, hNX i hi]
  exact ⟨ixOf_lt h _, (hPR i hi).1, by rw [en_phiI h, rotPerm_dual_apply], (hPR i hi).2⟩

/-- **The words of `wrProg` are the input part of the root frame.** -/
theorem inP_of_W5 (ℓ : D → ℤ) (K : ℕ) (c : Config) (m₀ : ℕ → ℕ) {A RVb NXb LABb MLb POb CDb : ℕ}
    (hLR : LRep (fLi M en m h d₀) m₀ CDb POb m)
    (hRV : ∀ i < m, m₀ (RVb + i) = rvI M en m i)
    (hNX : ∀ i < m, en i ∈ rcl M.dual (repsN M.dual (nsIds M h d₀).gd) →
      m₀ (NXb + i) < m ∧ en (m₀ (NXb + i)) =
        ret (rotPerm M.dual) (rcl M.dual (repsN M.dual (nsIds M h d₀).gd)) (en i))
    (hLAB : ∀ i < m, m₀ (LABb + i) = labI M en m i + 1)
    (hMLN : ∀ i < m, (m₀ (MLb + i) : ℤ) = minLen M.dual ℓ (en i) + K)
    (h0 : c.nmem A = m) (h1 : c.nmem (A + 1) = (cLi M en m h d₀).length)
    (h2 : c.nmem (A + 2) = (fLi M en m h d₀).length) (h3 : c.nmem (A + 3) = rtL M ℓ)
    (hW : ∀ t < (fLi M en m h d₀).length,
      W5 m₀ c.nmem (A + 4) (fLi M en m h d₀).length CDb RVb POb NXb LABb t)
    (hl : ∀ t < (cLi M en m h d₀).length, c.nmem (A + 4 + 5 * (fLi M en m h d₀).length + t) =
      m₀ (MLb + m₀ (CDb + t)) + rtL M ℓ - K) :
    InP (nsIds M h d₀) M.dual (minLen M.dual ℓ) (rtL M ℓ) (Fintype.card D)
      (repsN M.dual (nsIds M h d₀).gd) A
      (A + Frame.fsz (repsN M.dual (nsIds M h d₀).gd).card
        (ck M.dual (repsN M.dual (nsIds M h d₀).gd))) c := by
  set fL := fLi M en m h d₀ with hfL
  have hk := ck_eq h d₀
  have hc := card_eq h d₀
  have hx : ∀ t < fL.length, m₀ (CDb + t) = fL[t]! ∧ fL[t]! < m := fun t ht => by
    rw [hLR.1 t ht, List.getD_eq_getElem _ _ ht, List.getElem!_eq_getElem?_getD,
      List.getElem?_eq_getElem ht, Option.getD_some]
    exact ⟨rfl, fLi_lt h d₀ (List.getElem_mem ht)⟩
  have hget : ∀ t (ht : t < fL.length), fL[t]! = fL[t]'ht := fun t ht => by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
  have hpos : ∀ j < m, j ∈ fL → m₀ (POb + j) - 1 = fL.idxOf j := fun j hj hm => by
    rw [hLR.2 j hj, iteT hm]; omega
  have hrcl : ∀ t (ht : t < fL.length), en fL[t] ∈ rcl M.dual (repsN M.dual (nsIds M h d₀).gd) :=
    fun t ht => (mem_fLi_iff h d₀ (fLi_lt h d₀ (List.getElem_mem ht))).1 (List.getElem_mem ht)
  refine ⟨rfl, by rw [h0, card_eq_m h], by rw [h1, hc], by rw [h2, hk], by rw [h3],
    fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
    fun t ht => ?_⟩
  all_goals (try rw [hk] at ht); (try rw [hk])
  · obtain ⟨b, -, -, -, -⟩ := hW t ht
    obtain ⟨e1, e2⟩ := hx t ht
    rw [b, e1, cδ_eq' h d₀ ht, hget t ht, gd_en h d₀ (by rw [← hget t ht]; exact e2)]
  · obtain ⟨-, b, -, -, -⟩ := hW t ht
    obtain ⟨e1, e2⟩ := hx t ht
    rw [hget t ht] at e1 e2
    have hr := rvI_lt h (fL[t]'ht)
    have hrm : rvI M en m fL[t] ∈ fL := (mem_fLi_iff h d₀ hr).2 (by
      rw [en_rvI h]; exact rev_mem_rcl' (hrcl t ht))
    rw [b, e1, hRV _ e2, hpos _ hr hrm, cα_eq' h d₀ ht]
  · obtain ⟨-, -, b, -, -⟩ := hW t ht
    obtain ⟨e1, e2⟩ := hx t ht
    rw [hget t ht] at e1 e2
    obtain ⟨s1, s2⟩ := hNX _ e2 (hrcl t ht)
    have hsm : m₀ (NXb + fL[t]) ∈ fL := (mem_fLi_iff h d₀ s1).2 (by rw [s2]; exact ret_mem (hrcl t ht))
    rw [b, e1, hpos _ s1 hsm, cσ_eq' h d₀ ht s1 s2]
  · obtain ⟨-, -, -, b, -⟩ := hW t ht
    obtain ⟨e1, e2⟩ := hx t ht
    rw [hget t ht] at e1 e2
    rw [b, e1, hLAB _ e2, cδ_eq' h d₀ ht, gv_dtail h d₀ e2]; rfl
  · obtain ⟨-, -, -, -, b⟩ := hW t ht
    obtain ⟨e1, e2⟩ := hx t ht
    rw [hget t ht] at e1 e2
    rw [b, e1, hRV _ e2, hLAB _ (rvI_lt h _), cδ_eq' h d₀ ht, gv_dhead h d₀ e2]; rfl
  · rw [hc] at ht
    have htf : t < fL.length := by
      have : fL.length = (cLi M en m h d₀).length + (rLi M en m h d₀).length := by
        rw [hfL]; unfold fLi; rw [List.length_append]
      omega
    obtain ⟨e1, e2⟩ := hx t htf
    rw [hget t htf] at e1 e2
    rw [hl t ht, e1]
    have hm := hMLN _ e2
    have hab : |minLen M.dual ℓ (en fL[t])| ≤ rtL M ℓ := by
      unfold rtL
      rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun x _ => abs_nonneg _)]
      exact Finset.single_le_sum (f := fun x => |minLen M.dual ℓ x|)
        (fun x _ => abs_nonneg _) (mem_univ _)
    rw [abs_le] at hab
    have hle : K ≤ m₀ (MLb + fL[t]) + rtL M ℓ := by omega
    rw [cδ_eq' h d₀ htf]
    have : minLen M.dual ℓ (en fL[t]) + (rtL M ℓ : ℤ) =
        ((m₀ (MLb + fL[t]) + rtL M ℓ - K : ℕ) : ℤ) := by
      rw [Nat.cast_sub hle]; push_cast; omega
    rw [this, Int.toNat_natCast]

end NsStep

end BKMNW

end PlanarFlow
