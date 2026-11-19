module

public import PlanarFlow.STFlow.Lex

/-!
# The word-size perturbation of the capacities: definition

The perturbation of polynomial size `isoEps M t d = isoL + isoW M t d` of the perturbed run
(`PlanarFlow/STFlow/Lex.lean`), in place of `lexEps`:

* `isoW M t` (`IsIsoW`): an antisymmetric function with net flow `1` out of every vertex but the
  sink `t` (and `1 - #V` out of `t`), `|isoW| ≤ #V`; it exists (`exists_isIsoW`: the sum of the
  unit flows of a cotree from every vertex to `t`);
* `isoL V F = (4 F + 5) #V`;
* `isoEps_bounds`: `1 ≤ isoEps ≤ (4 F + 6) #V`.

Its properties for the run are proved in `PlanarFlow/STFlow/IsoEps.lean` (the darts of the path
are separated), `PlanarFlow/STFlow/IsoCover.lean` (shortest walks of the cut of the cyclic cover
are unique) and `PlanarFlow/STFlow/IsoCost.lean` (the pivot bound).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-! ### The perturbation -/

variable (M) in
/-- The specification of `w`: antisymmetric, net flow `1` out of every vertex but `t`, at most
`#V` in absolute value. -/
def IsIsoW (t : V) (w : D → ℤ) : Prop :=
  M.IsAntisymm w ∧ (∀ v, M.div w v = if v = t then 1 - (Fintype.card V : ℤ) else 1) ∧
    ∀ d, |w d| ≤ Fintype.card V

lemma div_finsum {ι : Type*} (s : Finset ι) (f : ι → D → ℤ) (v : V) :
    M.div (fun d => ∑ i ∈ s, f i d) v = ∑ i ∈ s, M.div (f i) v := by
  unfold CombMap.div; exact sum_comm

/-- **`w` exists**: the sum of the unit flows from every vertex to `t` in the cotree of a dual
tree. -/
theorem exists_isIsoW (hM : M.IsPlane) [Nonempty D] (t : V) : ∃ w, IsIsoW M t w := by
  classical
  obtain ⟨st, -⟩ := exists_linit (c := fun _ => 0) (ε := fun _ => 0) hM (fun _ => le_rfl)
    (fun _ => le_rfl) t t (M.face (Classical.arbitrary D))
  set T := st.T
  refine ⟨fun d => ∑ v, T.chi v t d, fun d => ?_, fun u => ?_, fun d => ?_⟩
  · simp only [← sum_neg_distrib]
    exact sum_congr rfl fun v _ => (T.chi_spec hM v t).1 d
  · rw [div_finsum]
    simp only [(T.chi_spec hM _ t).2.1, sum_sub_distrib]
    by_cases hu : u = t
    · subst hu; simp
    · simp [hu, Ne.symm hu]
  · calc |∑ v, T.chi v t d| ≤ ∑ v, |T.chi v t d| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _v : V, (1 : ℤ) := sum_le_sum fun v _ => by
          obtain ⟨ha, -, -, hle⟩ := T.chi_spec hM v t
          have h1 := hle d
          have h2 := hle (M.rev d)
          rw [ha d] at h2
          rw [abs_le]; constructor <;> omega
      _ = Fintype.card V := by simp

variable (M) in
open Classical in
/-- **The antisymmetric part of the perturbation** (for the sink `t`). -/
noncomputable def isoW (t : V) : D → ℤ := if h : ∃ w, IsIsoW M t w then h.choose else 0

lemma isoW_spec (hM : M.IsPlane) [Nonempty D] (t : V) : IsIsoW M t (isoW M t) := by
  classical
  have h := exists_isIsoW hM t
  have e : isoW M t = h.choose := by simp [isoW, h]
  rw [e]; exact h.choose_spec

variable (V F) in
/-- The constant part of the perturbation: `(4 F + 5) #V`. -/
def isoL : ℤ := (4 * Fintype.card F + 5) * Fintype.card V

variable (M) in
/-- **The word-size perturbation of the capacities**: `isoL + isoW`, between `1` and
`(4 F + 6) #V`. -/
noncomputable def isoEps (t : V) (d : D) : ℤ := isoL V F + isoW M t d

lemma card_V_pos (M : CombMap D V F) [Nonempty D] : 0 < Fintype.card V :=
  Fintype.card_pos_iff.2 ⟨M.tail (Classical.arbitrary D)⟩

lemma isoEps_bounds (hM : M.IsPlane) [Nonempty D] (t : V) (d : D) :
    1 ≤ isoEps M t d ∧ isoEps M t d ≤ (4 * Fintype.card F + 6) * Fintype.card V := by
  have h := (abs_le.1 ((isoW_spec hM t).2.2 d))
  have hV : (1 : ℤ) ≤ Fintype.card V := by exact_mod_cast (card_V_pos M)
  unfold isoEps isoL
  constructor <;> nlinarith

lemma isoEps_nonneg (hM : M.IsPlane) [Nonempty D] (t : V) (d : D) : 0 ≤ isoEps M t d :=
  le_trans (by norm_num) (isoEps_bounds hM t d).1

end STFlow

end PlanarFlow
