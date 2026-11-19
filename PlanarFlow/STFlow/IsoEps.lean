module

public import PlanarFlow.STFlow.LexCmp
public import PlanarFlow.STFlow.IsoDef

/-!
# The word-size perturbation separates the darts of the path

The perturbed run (`PlanarFlow/STFlow/Lex.lean`) compares residual capacities as pairs
`(c - g, ε - h)`; on the darts of the path of the cotree the second coordinates are
`lred ε T - μ` (`linv_slack2`). With `ε = lexEps` (`(4 F + 5)` to the power of the index of the
dart, integers of `O(m log m)` bits) distinct darts have distinct `lred` by base-`(4 F + 5)`
digits (`lred_inj`). This file proves the same for the perturbation of polynomial size
`isoEps M t = isoL + isoW M t` (`PlanarFlow/STFlow/IsoDef.lean`; `isoW` has net flow `1` out of
every vertex but `t`, `isoL = (4 F + 5) #V`), on the darts of the path, which is what the
selection of the bottleneck uses (`lbott_eq_of_key'`, `PlanarFlow/STFlow/ProgKey.lean`):

* `lred_flow`: `lred w T` is a flow of the cotree with the net flows of `w`, for `w`
  antisymmetric;
* `lred_isoW`: for a dart `d` of the path of the cotree from `s` to `t`, `lred (isoW M t) T d` is
  the number of vertices on the side of `d` (`DTree.flow_eq_side`);
* `side_nested`, `side_inj`: the sides of two darts of the path are nested (`DTree.no_cross`),
  and distinct for distinct darts;
* `lred_isoEps_inj`: **two distinct darts of the path have distinct values of
  `lred (isoEps M t) T`**: `lred (isoEps M t) = isoL · lred 1 + lred (isoW M t)`, and the
  multiple of `isoL` cannot compensate a difference of side sizes, which is below `#V ≤ isoL`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

/-! ### The reduced lengths of the perturbation -/

lemma lred_add (f g : D → ℤ) (T : DTree M) (d : D) :
    lred (f + g) T d = lred f T d + lred g T d := by
  simp only [lred, Pi.add_apply, cob]
  rw [T.psum_add, T.psum_add]; ring

lemma lred_isoEps (t : V) (T : DTree M) (d : D) :
    lred (isoEps M t) T d = isoL V F * lred (fun _ => 1) T d + lred (isoW M t) T d := by
  have e : isoEps M t = (fun d => isoL V F * (fun _ => (1 : ℤ)) d) + isoW M t := by
    funext d; simp [isoEps]
  rw [e, lred_add]
  congr 1
  simp only [lred, cob, T.psum_smul]; ring

/-- `lred w T` is a flow of the cotree with the net flows of `w`. -/
lemma lred_flow {w : D → ℤ} (hw : M.IsAntisymm w) (T : DTree M) :
    M.IsAntisymm (lred w T) ∧ T.OffT (lred w T) ∧ ∀ v, M.div (lred w T) v = M.div w v := by
  refine ⟨fun d => ?_, fun d hd => ?_, fun v => ?_⟩
  · simp only [lred]; rw [hw d, M.cob_antisymm _ d]; ring
  · have hpar : ∀ x, x ≠ T.root → lred w T (T.par x) = 0 := fun x hx => by
      simp only [lred, cob]
      rw [T.head_par x hx, T.psum_of_ne w hx, T.up_of_ne hx]; ring
    obtain ⟨x, hx, rfl | rfl⟩ := hd
    · exact hpar x hx
    · simp only [lred]
      rw [hw, M.cob_antisymm _ _]
      have := hpar x hx; simp only [lred] at this; linarith
  · have e : lred w T = w - M.cob (T.psum w) := rfl
    rw [e, show M.div (w - M.cob (T.psum w)) v = M.div w v - M.div (M.cob (T.psum w)) v from by
      unfold CombMap.div; simp [sum_sub_distrib]]
    rw [show M.div (M.cob (T.psum w)) v = 0 from M.div_cob _ v]; ring

lemma not_inT_of_chi {T : DTree M} (hM : M.IsPlane) {s t : V} {d : D} (h : T.chi s t d = 1) :
    ¬ T.InT d := fun hT => by
  rw [(T.chi_spec hM s t).2.2.1 d hT] at h; exact absurd h (by norm_num)

lemma side_of_chi {T : DTree M} (hM : M.IsPlane) {s t : V} {d : D} (h : T.chi s t d = 1) :
    s ∈ T.side d ∧ t ∉ T.side d := by
  obtain ⟨ha, hdiv, hoff, -⟩ := T.chi_spec hM s t
  have := DTree.unit_side hM ha hoff hdiv (not_inT_of_chi hM h)
  rw [h] at this
  exact DTree.ind_sub_eq_one this.symm

/-- **On a dart of the path, `lred w T` is the number of vertices on its side.** -/
theorem lred_isoW (hM : M.IsPlane) [Nonempty D] {s t : V} {T : DTree M} {d : D}
    (h : T.chi s t d = 1) : lred (isoW M t) T d = (T.side d).card := by
  obtain ⟨hw, hdiv, -⟩ := isoW_spec hM t
  obtain ⟨ha, hoff, hd⟩ := lred_flow hw T
  rw [DTree.flow_eq_side hM ha hoff (not_inT_of_chi hM h)]
  have ht := (side_of_chi hM h).2
  have h1 : ∀ v ∈ T.side d, M.div (lred (isoW M t) T) v = 1 := fun v hv => by
    have hvt : v ≠ t := fun e => ht (e ▸ hv)
    rw [hd, hdiv]; simp [hvt]
  rw [sum_congr rfl h1]; simp

/-- **The sides of two darts of the path are nested.** -/
theorem side_nested (hM : M.IsPlane) {s t : V} {T : DTree M} {d₁ d₂ : D}
    (h₁ : T.chi s t d₁ = 1) (h₂ : T.chi s t d₂ = 1) :
    T.side d₁ ⊆ T.side d₂ ∨ T.side d₂ ⊆ T.side d₁ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨u, hu1, hu2⟩ := not_subset.1 h1
  obtain ⟨u', hu1', hu2'⟩ := not_subset.1 h2
  obtain ⟨ρa, ρdiv, ρoff, -⟩ := T.chi_spec hM u' u
  have e₁ := DTree.unit_side hM ρa ρoff ρdiv (not_inT_of_chi hM h₁)
  have e₂ := DTree.unit_side hM ρa ρoff ρdiv (not_inT_of_chi hM h₂)
  simp only [hu2', hu1, ↓reduceIte] at e₁
  simp only [hu1', hu2, ↓reduceIte] at e₂
  exact DTree.no_cross hM h₁ h₂ ρa ρoff ρdiv (by rw [e₁]; norm_num) (by rw [e₂]; norm_num)

/-- **Distinct darts of the path have distinct sides.** -/
theorem side_inj (hM : M.IsPlane) {s t : V} {T : DTree M} {d₁ d₂ : D}
    (h₁ : T.chi s t d₁ = 1) (h₂ : T.chi s t d₂ = 1) (h : T.side d₁ = T.side d₂) : d₁ = d₂ := by
  by_contra hne
  have hnT₂ := not_inT_of_chi hM h₂
  have hrev : d₂ ≠ M.rev d₁ := by
    rintro rfl
    have := (T.chi_spec hM s t).1 d₁
    rw [h₁, h₂] at this; norm_num at this
  have htail : M.tail d₂ ∈ T.side d₁ := by rw [h]; exact DTree.mem_side.2 .refl
  have hhead : M.head d₂ ∉ T.side d₁ := by rw [h]; exact DTree.head_not_mem_side hM hnT₂
  exact hhead (DTree.mem_side.2 ((DTree.mem_side.1 htail).tail
    ⟨d₂, ⟨hnT₂, fun e => hne e.symm, hrev⟩, rfl, rfl⟩))

/-- **The perturbation separates the darts of the path**: two darts of the path of the cotree
from `s` to `t` with the same `lred (isoEps M t) T` are equal. -/
theorem lred_isoEps_inj (hM : M.IsPlane) [Nonempty D] {s t : V} {T : DTree M} {d₁ d₂ : D}
    (h₁ : T.chi s t d₁ = 1) (h₂ : T.chi s t d₂ = 1)
    (h : lred (isoEps M t) T d₁ = lred (isoEps M t) T d₂) : d₁ = d₂ := by
  rw [lred_isoEps, lred_isoEps, lred_isoW hM h₁, lred_isoW hM h₂] at h
  have hb : ∀ {d}, T.chi s t d = 1 → 1 ≤ ((T.side d).card : ℤ) ∧
      ((T.side d).card : ℤ) + 1 ≤ Fintype.card V := by
    intro d hd
    obtain ⟨hs, ht⟩ := side_of_chi hM hd
    have h1 : 1 ≤ (T.side d).card := card_pos.2 ⟨s, hs⟩
    have h2 : (T.side d).card < (univ : Finset V).card :=
      card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨subset_univ _, fun e => ht (e ▸ mem_univ t)⟩)
    rw [card_univ] at h2
    constructor <;> [exact_mod_cast h1; exact_mod_cast h2]
  obtain ⟨a1, a2⟩ := hb h₁
  obtain ⟨b1, b2⟩ := hb h₂
  have hL : (Fintype.card V : ℤ) ≤ isoL V F := by
    unfold isoL; nlinarith [(by positivity : (0 : ℤ) ≤ Fintype.card V)]
  set k := lred (fun _ => (1 : ℤ)) T d₁ - lred (fun _ => (1 : ℤ)) T d₂
  have hk : isoL V F * k = ((T.side d₂).card : ℤ) - (T.side d₁).card := by
    simp only [k]; linarith
  have hk0 : k = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : isoL V F * k ≤ - isoL V F := by nlinarith
      linarith
    · have : isoL V F ≤ isoL V F * k := by nlinarith
      linarith
  rw [hk0, mul_zero] at hk
  have hc : (T.side d₁).card = (T.side d₂).card := by omega
  rcases side_nested hM h₁ h₂ with hs | hs
  · exact side_inj hM h₁ h₂ (eq_of_subset_of_card_le hs hc.symm.le)
  · exact side_inj hM h₁ h₂ (eq_of_subset_of_card_le hs hc.le).symm

end STFlow

end PlanarFlow
