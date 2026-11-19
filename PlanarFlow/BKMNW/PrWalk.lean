module

public import PlanarFlow.BKMNW.PpConv

/-!
# The first return along a permutation array: the walk and its amortised length

For `f` a permutation of `[0, m)` (`PermOn f m`) and a predicate `Q`, `wlk f Q x` is the number
of steps from `x` to the next point of `Q` along the forward orbit of `x` (at least `1`).

* `wlk_pos`, **`wlk_spec`** (`Q (f^[wlk x] x)` when `Q x`, `x < m`), **`wlk_min`**;
* **`sum_wlk_le`**: `∑_{x < m, Q x} (wlk x - 1) ≤ m` — every point outside `Q` is passed by the
  walk of exactly one point of `Q` (the last point of `Q` before it), so the walks of all the
  points of `Q` together take at most `2 m` steps.

For the map of the drawing's encoding (`f = rotW d`, `Q` = not a loop):
**`sgI_eq_walk`**: the rotation of the map without loops at a dart that is not a loop is the end
of the walk, `sgI (map wf) x = (rotW d)^[wlk (rotW d) (NlP d) x] x`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset Function Equiv Orbit CombMap Feas OrbLab

section Walk

variable (f : ℕ → ℕ) (Q : ℕ → Prop) [DecidablePred Q]

/-- **The length of the walk from `x` to the next point of `Q`** (`1` if there is none). -/
noncomputable def wlk (x : ℕ) : ℕ := by
  classical exact if h : ∃ j, 0 < j ∧ Q (f^[j] x) then Nat.find h else 1

variable {f Q} {m : ℕ}

lemma wlk_ex (hp : PermOn f m) {x : ℕ} (hx : x < m) (hq : Q x) : ∃ j, 0 < j ∧ Q (f^[j] x) := by
  obtain ⟨p, hp0, e⟩ := OrbLab.iter_period hp hx
  exact ⟨p, hp0, by rw [e]; exact hq⟩

lemma wlk_pos (x : ℕ) : 0 < wlk f Q x := by
  classical
  unfold wlk
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact one_pos

lemma wlk_spec (hp : PermOn f m) {x : ℕ} (hx : x < m) (hq : Q x) : Q (f^[wlk f Q x] x) := by
  classical
  have h := wlk_ex hp hx hq
  unfold wlk
  rw [ppDiteT h]
  exact (Nat.find_spec h).2

lemma wlk_min (hp : PermOn f m) {x : ℕ} (hx : x < m) (hq : Q x) {j : ℕ} (hj0 : 0 < j)
    (hj : j < wlk f Q x) : ¬ Q (f^[j] x) := by
  classical
  have h := wlk_ex hp hx hq
  unfold wlk at hj
  rw [ppDiteT h] at hj
  exact fun hQ => Nat.find_min h hj ⟨hj0, hQ⟩

/-- The walk is injective: `(x, j) ↦ f^[j] x` on `Q x`, `1 ≤ j < wlk x`. -/
lemma walk_inj (hp : PermOn f m) {x y j k : ℕ} (hx : x < m) (hy : y < m) (hqx : Q x) (hqy : Q y)
    (hj : j < wlk f Q x) (hk : k < wlk f Q y) (hjk : j ≤ k)
    (e : f^[j] x = f^[k] y) : x = y ∧ j = k := by
  have e' : f^[j] x = f^[j] (f^[k - j] y) := by
    rw [← iterate_add_apply, show j + (k - j) = k by omega]; exact e
  have hxy : x = f^[k - j] y := OrbLab.iter_inj hp hx (OrbLab.iter_lt hp hy _) j e'
  rcases Nat.eq_zero_or_pos (k - j) with h0 | h0
  · rw [h0] at hxy; exact ⟨hxy, by omega⟩
  · exact absurd (hxy ▸ hqx) (wlk_min hp hy hqy h0 (by omega))

/-- **The walks of all the points of `Q` take at most `m` extra steps.** -/
theorem sum_wlk_le (hp : PermOn f m) :
    ∑ x ∈ range m, (if Q x then wlk f Q x - 1 else 0) ≤ m := by
  classical
  rw [← Finset.sum_filter]
  have hc : ∀ x ∈ (range m).filter Q, wlk f Q x - 1 = (Ico 1 (wlk f Q x)).card := by
    intro x _; simp
  rw [Finset.sum_congr rfl hc, ← Finset.card_sigma]
  calc _ ≤ (range m).card := by
        refine Finset.card_le_card_of_injOn (fun p => f^[p.2] p.1) ?_ ?_
        · intro p hp'
          simp only [coe_sigma, Set.mem_sigma_iff, coe_filter, mem_range,
            coe_Ico, Set.mem_Ico] at hp'
          have := OrbLab.iter_lt hp hp'.1.1 p.2
          simpa using this
        · rintro ⟨p1, p2⟩ hp' ⟨q1, q2⟩ hq' e
          simp only [coe_sigma, Set.mem_sigma_iff, coe_filter, mem_range,
            coe_Ico, Set.mem_Ico] at hp' hq'
          simp only at e
          obtain ⟨⟨hpx, hpq⟩, hp1, hp2⟩ := hp'
          obtain ⟨⟨hqx, hqq⟩, hq1, hq2⟩ := hq'
          rcases le_total p2 q2 with hle | hle
          · obtain ⟨h1, h2⟩ := walk_inj hp hpx hqx hpq hqq hp2 hq2 hle e
            subst h1; subst h2; rfl
          · obtain ⟨h1, h2⟩ := walk_inj hp hqx hpx hqq hpq hq2 hp2 hle e.symm
            subst h1; subst h2; rfl
    _ = m := card_range m

end Walk

/-! ### The rotation without loops as a walk -/

/-- A dart index that is not a loop of the encoded map. -/
def NlP (d : List ℕ) (x : ℕ) : Prop := tl d (rv d x) ≠ tl d x

instance (d : List ℕ) : DecidablePred (NlP d) := fun x => by unfold NlP; infer_instance

variable {d : List ℕ} (wf : Wf d)

lemma isNl_map_iff {x : ℕ} : IsNl (map wf) x ↔ x < nd d ∧ NlP d x := by
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, fun e => ?_⟩
    rw [mem_nlDarts] at h
    exact h (Fin.ext e)
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rw [mem_nlDarts]
    exact fun e => h (congrArg Fin.val e)

lemma rotPerm_iter_val (x : Fin (nd d)) (k : ℕ) :
    (((rotPerm (map wf))^[k] x : Fin (nd d)) : ℕ) = (rotW d)^[k] x := by
  rw [← map_rot_iter wf x k]
  congr 1

/-- **The rotation of the map without loops is the end of the walk.** -/
theorem sgI_eq_walk {x : ℕ} (hx : x < nd d) (hq : NlP d x) :
    sgI (map wf) x = (rotW d)^[wlk (rotW d) (NlP d) x] x := by
  have hP := rotW_permOn wf
  have hmem : (⟨x, hx⟩ : Fin (nd d)) ∈ nlDarts (map wf) := ((isNl_map_iff wf).2 ⟨hx, hq⟩).2
  have hmemN : ∀ k, (((rotPerm (map wf))^[k] ⟨x, hx⟩ : Fin (nd d)) ∈ nlDarts (map wf) ↔
      NlP d ((rotW d)^[k] x)) := fun k => by
    rw [← rotPerm_iter_val wf ⟨x, hx⟩ k]
    exact ⟨fun h => ((isNl_map_iff wf).1 ((isNl_fin _).2 h)).2,
      fun h => (isNl_fin _).1 ((isNl_map_iff wf).2 ⟨Fin.isLt _, h⟩)⟩
  rw [show x = ((⟨x, hx⟩ : Fin (nd d)) : ℕ) from rfl, sgI_fin _ hmem]
  unfold nlRot
  rw [ret_eq_of hmem (wlk_pos _) ((hmemN _).2 (wlk_spec hP hx hq))
    (fun j hj0 hj h => wlk_min hP hx hq hj0 hj ((hmemN j).1 h))]
  exact rotPerm_iter_val wf _ _

/-- `sgI` on a loop is the identity. -/
lemma sgI_loop {x : ℕ} (hq : ¬ NlP d x) : sgI (map wf) x = x := by
  unfold sgI
  rw [ppDiteF (fun h => hq ((isNl_map_iff wf).1 h).2)]

end Pp

end BKMNW

end PlanarFlow
