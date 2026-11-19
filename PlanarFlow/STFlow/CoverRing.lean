module

public import PlanarFlow.STFlow.CoverCut

/-!
# The roots around the lift of `t` and the setting of Klein's interval lemma

In the cut of the cyclic cover along the lift of `π` (`PlanarFlow/STFlow/CoverCut.lean`), the
ring of roots passes once around the branch point over `t = p k`, by the rotation of the cover,
starting right after the deleted dart `(rev (d (k - 1)), 0)` (the root `t0`). Going once around
`t` in `M` lowers the sheet by `1` (the net flow of `P` out of `t` is `-1`), so the roots of the
lifts `(d₀, i)` of a dart `d₀` leaving `t` come in the order of decreasing sheets
`-1, -2, …, -K` (`ring_root`): the root of `(d₀, -1 - q)` sits at the position
`j₀ - 1 + q · per` of the ring (`per` the degree of `t`), and these positions are below the
length of the ring (`ring_len`).

* `cutCover`: the cut of the cover, an instance of `PlanarFlow.BKMNW.Cut` built by
  `PlanarFlow.BKMNW.cutOf` from the root `t0`.
* `cutCover_hyp`, `cutCover_sameReach`: **the cut of the cover with the perturbed lengths meets
  `PlanarFlow.MSSP.Hyp` and `PlanarFlow.Klein.SameReach`**, so Klein's interval lemma
  (`PlanarFlow.Klein.tight_interval`) applies to it.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 400000

namespace PlanarFlow

namespace STFlow

open Finset CombMap BKMNW MSSP Klein Function

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] [Fintype F]
  [DecidableEq F]
variable {M : CombMap D V F}

variable (hrot : M.RotTrans) (π : SPath M) (hk : 0 < π.k) (K : ℕ) [NeZero K]

local notation "𝓜" => cover (pathCov hrot π) K
local notation "𝓛" => (liftPath hrot π K hk).darts
local notation "hL" => (liftPath hrot π K hk).rev_mem_darts'

/-- The last dart of `π`, reversed: the dart of the path at `t`. -/
def yT : D := M.rev (π.d (π.k - 1))

include hk in
lemma tail_yT : M.tail (yT π) = π.p π.k := by
  simp [yT, π.head_d _ (by omega : π.k - 1 < π.k), Nat.sub_add_cancel hk]

include hk in
/-- At `t`, only the dart of the path has a nonzero flow. -/
lemma pflow_ne_zero_last {e : D} (he : M.tail e = π.p π.k) (h0 : pflow π e ≠ 0) :
    e = yT π := by
  by_cases hd : e ∈ π.darts
  · obtain ⟨i, hi, rfl | rfl⟩ := π.mem_darts.1 hd
    · rw [π.tail_d i hi] at he
      have := π.inj i hi.le π.k le_rfl he; omega
    · rw [M.tail_rev, π.head_d i hi] at he
      have := π.inj (i + 1) hi π.k le_rfl he
      simp [yT, show i = π.k - 1 by omega]
  · exact absurd (pflow_of_not_mem π hd) h0

include hk in
lemma pflow_yT : pflow π (yT π) = -1 := pflow_rev_d π (by omega : π.k - 1 < π.k)

/-- **The only deleted dart at the lift of `t`** is `(rev (d (k - 1)), 0)`. -/
lemma mem_L_at_t {x : D × ZMod K} (hx : x ∈ 𝓛) (ht : M.tail x.1 = π.p π.k) :
    x = (yT π, 0) := by
  obtain ⟨j, hj, rfl | rfl⟩ := (mem_liftPath_darts hrot π K hk).1 hx
  · simp only at ht
    rw [π.tail_d j hj] at ht
    have := π.inj j hj.le π.k le_rfl ht; omega
  · simp only at ht
    rw [M.tail_rev, π.head_d j hj] at ht
    have := π.inj (j + 1) hj π.k le_rfl ht
    simp [yT, show j = π.k - 1 by omega]

/-- The degree of `t`. -/
noncomputable def perT : ℕ := minimalPeriod M.rot (yT π)

lemma perT_pos : 0 < perT π := BKMNW.rot_period_pos _

include hk in
/-- Around `t`, after `n ≤ deg t` steps from the dart of the path, the sum of `P` is `-1`. -/
lemma rotSum_yT {n : ℕ} (h0 : 0 < n) (h1 : n ≤ perT π) :
    M.rotSum (pflow π) (yT π) n = -1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 1 + m := ⟨n - 1, by omega⟩
  rw [rotSum_add]
  have e1 : M.rotSum (pflow π) (yT π) 1 = -1 := by simp [rotSum, pflow_yT π hk]
  have e2 : M.rotSum (pflow π) (M.rot^[1] (yT π)) m = 0 := by
    refine sum_eq_zero fun i hi => ?_
    have hi' := mem_range.1 hi
    rw [← iterate_add_apply]
    by_contra h
    have := pflow_ne_zero_last π hk (by rw [tail_rot_iterate, tail_yT π hk]) h

    exact BKMNW.rot_iterate_ne (M := M) (x := yT π) (i := i + 1) (by omega)
      (by unfold perT at h1; omega) this
  rw [e1, e2]; ring

include hk in
lemma rotSum_yT_mul (q : ℕ) :
    M.rotSum (pflow π) (yT π) (perT π * q) = -q := by
  rw [perT, rotSum_mul_period, rotSum_yT π hk (BKMNW.rot_period_pos _) le_rfl]; ring

/-- The deleted dart at the lift of `t`. -/
def xT : D × ZMod K := (yT π, 0)

lemma rot_xT_iterate (n : ℕ) :
    (𝓜).rot^[n] (xT π K) =
      (M.rot^[n] (yT π), ((M.rotSum (pflow π) (yT π) n : ℤ) : ZMod K)) := by
  rw [cover_rot_iterate]; simp [xT, pathCov_P]

include hk in
/-- Around the lift of `t`, the rotation returns to the deleted dart only after `K` turns. -/
lemma rot_xT_ne {n : ℕ} (h0 : 0 < n) (h1 : n < K * perT π) :
    (𝓜).rot^[n] (xT π K) ≠ xT π K := by
  intro h
  rw [rot_xT_iterate] at h
  have h1' := congrArg Prod.fst h
  have h2' := congrArg Prod.snd h
  simp only [xT] at h1' h2'
  have hp := perT_pos π
  -- `n` is a multiple of the degree
  have hdvd : perT π ∣ n := by
    have := (isPeriodicPt_iff_minimalPeriod_dvd).1 (show IsPeriodicPt M.rot n (yT π) from h1')
    exact this
  obtain ⟨q, rfl⟩ := hdvd
  rw [rotSum_yT_mul π hk] at h2'
  have hq0 : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at h0
    · exact h
  have hqK : q < K := by
    by_contra h
    have : K * perT π ≤ perT π * q := by nlinarith
    omega
  have : ((q : ℤ) : ZMod K) = 0 := by
    have := congrArg Neg.neg h2'
    simpa using this
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  have := Int.le_of_dvd (by exact_mod_cast hq0) this
  omega

include hk in
lemma tail_xT_rot (n : ℕ) : M.tail ((𝓜).rot^[n] (xT π K)).1 = π.p π.k := by
  rw [rot_xT_iterate]; simp [tail_rot_iterate, tail_yT π hk]

/-- The rotation from the lift of `t` stays off the deleted darts for `K` turns. -/
lemma rot_xT_not_mem {n : ℕ} (h0 : 0 < n) (h1 : n < K * perT π) :
    (𝓜).rot^[n] (xT π K) ∉ 𝓛 := fun h =>
  rot_xT_ne hrot π hk K h0 h1 (mem_L_at_t hrot π hk K h (tail_xT_rot hrot π hk K n))

lemma xT_mem : xT π K ∈ 𝓛 := by
  rw [mem_liftPath_darts]
  refine ⟨π.k - 1, by omega, Or.inr ?_⟩
  rfl

lemma tail_xT_mem_cutS (n : ℕ) : (𝓜).tail ((𝓜).rot^[n] (xT π K)) ∈ cutS 𝓜 𝓛 := by
  rw [tail_rot_iterate]
  exact tail_mem_cutS (xT_mem hrot π hk K)

/-- **The first root of the ring**: the dart after the deleted dart at the lift of `t`. -/
noncomputable def t0T : CutT 𝓜 𝓛 := ⟨(𝓜).rot^[1] (xT π K), tail_xT_mem_cutS hrot π hk K 1⟩

/-- Along the ring from `t0T`, the walk around the path follows the rotation of the cover. -/
lemma tourT_t0T {n : ℕ} (hn : n < K * perT π) :
    ((tourT hL)^[n] (t0T hrot π hk K)).1 = (𝓜).rot^[n + 1] (xT π K) := by
  rw [tourT_iterate_val]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', ih (by omega), tour_of_not_mem (rot_xT_not_mem hrot π hk K
      (by omega) (by omega)), ← iterate_succ_apply' (𝓜).rot]

/-- **The ring is longer than `K` turns around `t`.** -/
lemma ring_len : K * perT π ≤ minimalPeriod (tourT hL) (t0T hrot π hk K) := by
  by_contra h
  push Not at h
  set N := minimalPeriod (tourT hL) (t0T hrot π hk K)
  have hN := minimalPeriod_pos_of_mem_periodicPts
    ((tourT hL).injective.mem_periodicPts (t0T hrot π hk K))
  have e := congrArg Subtype.val (iterate_minimalPeriod (f := tourT hL) (x := t0T hrot π hk K))
  rw [tourT_t0T hrot π hk K (n := N) h] at e
  have e' : (𝓜).rot^[N] (xT π K) = xT π K := by
    apply (𝓜).rot_injective
    rw [iterate_succ_apply'] at e
    exact e
  exact rot_xT_ne hrot π hk K hN h e'

variable {d₀ : D}

include hrot hk in
/-- The position of `d₀` after the dart of the path, around `t`: `0 < j₀ ≤ deg t`. -/
lemma exists_j0 (hd₀ : M.tail d₀ = π.p π.k) : ∃ j, 0 < j ∧ j ≤ perT π ∧ M.rot^[j] (yT π) = d₀ :=
  BKMNW.rot_cover hrot ((tail_yT π hk).trans hd₀.symm)

/-- **The roots of the lifts of `d₀` along the ring**: at the position `j₀ - 1 + q · deg t`
stands the root of `(d₀, -1 - q)`, for `q < K`. -/
lemma ring_root {j : ℕ} (hj0 : 0 < j) (hj1 : j ≤ perT π) (hj : M.rot^[j] (yT π) = d₀) {q : ℕ}
    (hq : q < K) :
    ((tourT hL)^[j - 1 + perT π * q] (t0T hrot π hk K)).1 = (d₀, -1 - (q : ZMod K)) := by
  have hlt : j - 1 + perT π * q < K * perT π := by
    have : perT π * q + perT π ≤ K * perT π := by nlinarith
    omega
  rw [tourT_t0T hrot π hk K hlt, rot_xT_iterate, show j - 1 + perT π * q + 1 = perT π * q + j by
    omega]
  ext
  · simp only
    rw [show perT π * q + j = j + perT π * q by ring, iterate_add_apply, perT, iterate_mul,
      iterate_fixed iterate_minimalPeriod, hj]
  · simp only
    have hfix : M.rot^[perT π * q] (yT π) = yT π := by
      rw [perT, iterate_mul, iterate_fixed iterate_minimalPeriod]
    rw [rotSum_add, rotSum_yT_mul π hk, hfix, rotSum_yT π hk hj0 hj1]
    push_cast; ring

/-! ### The cut of the cover meets the hypotheses of Klein's lemma -/

section Hyp

include hk in
lemma p0_ne_pk : π.p 0 ≠ π.p π.k := fun h => by
  have := π.inj 0 (Nat.zero_le _) π.k le_rfl h; omega

include hk in
lemma div_pflow_s : M.div (pflow π) (π.p 0) = 1 := by
  rw [div_pflow]; simp [(p0_ne_pk π hk).symm]

include hk in
lemma div_pflow_t : M.div (pflow π) (π.p π.k) = -1 := by
  rw [div_pflow]; simp [p0_ne_pk π hk]

include hk in
lemma cover_rotTrans' : (𝓜).RotTrans :=
  cover_rotTrans hrot (div_pflow_s π hk) (div_pflow_t π hk)

/-- Every root of the ring is reached from `t0T`. -/
lemma horbT : ∀ t, ItReach (tourT hL) (t0T hrot π hk K) t := by
  set P := liftPath hrot π K hk
  set t1 : CutT 𝓜 𝓛 := ⟨P.d 0, tail_mem_cutS (P.d_mem 0 hk)⟩
  have horb : ∀ t, ItReach (tourT hL) t1 t := by
    intro t
    obtain ⟨e, he, h⟩ := mem_cutS.1 t.2
    obtain ⟨i, hi, hi'⟩ := P.tail_mem_darts he
    obtain ⟨n, hn⟩ := tour_reach (cover_rotTrans' hrot π hk K) P hk hi (h.symm.trans hi')
    exact ⟨n, Subtype.ext (by rw [tourT_iterate_val]; exact hn)⟩
  obtain ⟨a, ha⟩ := horb (t0T hrot π hk K)
  set N := minimalPeriod (tourT hL) t1
  have hN : 0 < N := minimalPeriod_pos_of_mem_periodicPts
    ((tourT hL).injective.mem_periodicPts t1)
  have hback : ItReach (tourT hL) (t0T hrot π hk K) t1 := by
    refine ⟨N * a - a, ?_⟩
    rw [← ha, ← iterate_add_apply, show N * a - a + a = N * a by
      have : a ≤ N * a := Nat.le_mul_of_pos_left a hN
      omega, iterate_mul, iterate_fixed iterate_minimalPeriod]
  exact fun t => hback.trans (horb t)

lemma htwoT (hK : 2 ≤ K) : tourT hL (t0T hrot π hk K) ≠ t0T hrot π hk K := by
  intro h
  have hK2 : 1 < K * perT π := by have := perT_pos π; nlinarith
  have h1 := congrArg Subtype.val h
  have e := tourT_t0T hrot π hk K (n := 1) hK2
  simp only [iterate_one] at e
  rw [e] at h1
  have : (𝓜).rot (xT π K) = xT π K := by
    apply (𝓜).rot_injective
    exact h1
  exact rot_xT_ne hrot π hk K (n := 1) one_pos hK2 this

lemma hcountT : (𝓛).toFinset.card + 2 = 2 * (cutS 𝓜 𝓛).card := by
  rw [(liftPath hrot π K hk).card_darts, (liftPath hrot π K hk).card_cutS hk]
  simp only [liftPath_k]; ring

variable (hM : M.IsPlane) (hface : M.FaceTrans) (hK : 2 ≤ K) (ℓ : D × ZMod K → ℤ)
  (hnn : ∀ e, e ∉ (liftPath hrot π K hk).darts → 0 ≤ ℓ e)

/-- **The cut of the cover along the lift of `π`**, from the root `t0T`. -/
noncomputable def cutCover : Cut 𝓜 ℓ 𝓛 (CutD 𝓜 𝓛) (CutV 𝓜 𝓛) (CutF 𝓜 𝓛) :=
  cutOf hL (t0T hrot π hk K) ℓ hnn
    (cover_isPlane hM hrot (p0_ne_pk π hk) (div_pflow_s π hk))
    (cover_faceTrans hface) (horbT hrot π hk K) (htwoT hrot π hk K hK) (hcountT hrot π hk K)

include hM hface hK hnn in
/-- **The cut of the cover with the perturbed lengths meets the article's assumptions.** -/
theorem cutCover_hyp :
    Hyp (cutMap hL) (minimalPeriod (tourT hL) (t0T hrot π hk K)) (cutG hL (t0T hrot π hk K))
      (cutPiece 𝓜 𝓛) (pert (cutLen 𝓜 𝓛 ℓ)) :=
  (cutCover hrot π hk K hM hface hK ℓ hnn).hyp.hyp

/-- **The roots of the cut of the cover reach the same vertices.** -/
theorem cutCover_sameReach (ℓ' : CutD 𝓜 𝓛 → ℤ) :
    SameReach (cutMap hL) (minimalPeriod (tourT hL) (t0T hrot π hk K))
      (cutG hL (t0T hrot π hk K)) (cutPiece 𝓜 𝓛) ℓ' :=
  cutOf_sameReach hL ℓ' (t0T hrot π hk K)

end Hyp

end STFlow

end PlanarFlow
