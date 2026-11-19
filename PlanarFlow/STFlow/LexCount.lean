module

public import PlanarFlow.STFlow.CoverTight

/-!
# Each dart enters the dual tree at most once in the perturbed run

This file proves the pivot bound of Borradaile and Klein for the perturbed algorithm
(`PlanarFlow/STFlow/Lex.lean`), by the parametric argument of Erickson (SODA 2010) through the
multiple-source shortest paths of Cabello, Chambers and Erickson (Lemma 3.7, the interval lemma
`PlanarFlow.Klein.tight_interval`), on plane maps with transitive rotations and faces.

## The argument

Fix a simple path `π` from `s` to `t` (`exists_sPath`), its unit flow `P`, `K = 4 F + 4` sheets
and the middle sheet `m = 2 F + 2`. For a face `b` other than the root, its *level* in a tree `T`
is `psum P b` (`|psum P b| < F`); a pivot raises the levels of a subtree by `1` and keeps the
others (`lpivot_facts`), so the level of `b` is nondecreasing along the run, and rises by `1` when
`b` gets a new parent.

In the cut of the cyclic cover (`PlanarFlow/STFlow/CoverRing.lean`), let `r κ` be the root of the
lift `(d₀, m - κ)` of the dart `d₀` leaving `t` whose face is the root of the dual tree. At every
state of the run where `b` has the level `κ`, the lift ending at `(b, m)` of the parent dart of
`b` is **the** tight arc into `(b, m)` for the root `r κ` (`tight_par`, with the uniqueness of
tight arcs `PlanarFlow.MSSP.UniqTight`): the parent dart of `b` is a function of its level
(`par_eq_of_level`). If a dart `d` entered at a step `i`, then left, and entered again at a step
`j`, the levels `κ₁ - 1 < κ₁ < κ' < κ₂` of `b` at the steps `i, i + 1, j, j + 1` would give four
roots in this order along the ring (`ring_root`), for which the lift of `d` is not tight, tight,
not tight, tight: not a cyclic interval, against `PlanarFlow.Klein.tight_interval`.

## Results

* `lenterOnce`: **along the perturbed run, each dart enters the dual tree at most once.**
  `lenterOnce_of`: the same for any perturbation whose parent darts are tight arcs of the cut of
  the cover for some nonnegative lengths (`TightLev`; `tightLev_lex` for `lexEps`,
  `PlanarFlow.STFlow.tightLev_iso` for the word-size perturbation).
* `lsteps_le`: hence every perturbed run takes at most `m + 1` steps (`m` darts).
* `pstflowSteps_le`, `pstflowCost_le`: **the perturbed implementation `pstflow` takes at most
  `m + 1` steps and costs at most `36 K m lg m`** (under the stated costs of its subroutines,
  `STCosts.Bounds`), on every plane map with transitive rotations and faces.
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

/-! ### The trajectory of the perturbed run -/

variable (M) in
/-- **The states of the perturbed run**: `ltraj st i` after `i` steps. -/
noncomputable def ltraj (c ε : D → ℤ) (s t : V) (st : LSt M) : ℕ → LSt M
  | 0 => st
  | i + 1 => (lstep M c ε s t (ltraj c ε s t st i)).1

variable {c ε : D → ℤ} {s t : V}

lemma ltraj_succ' (st : LSt M) (i : ℕ) :
    ltraj M c ε s t st (i + 1) = ltraj M c ε s t (lstep M c ε s t st).1 i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [ltraj, ih, ltraj]

lemma ltraj_inv (hM : M.IsPlane) {st : LSt M} (hI : LInv c ε s t st) (i : ℕ) :
    LInv c ε s t (ltraj M c ε s t st i) := by
  induction i with
  | zero => exact hI
  | succ i ih => exact lstep_inv hM ih

open Classical in
/-- **A step of the perturbed run that does not stop is a pivot** at a dart `e` crossed forward
by the path of the cotree. -/
lemma lpivot_facts (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M}
    (h : (lstep M c ε s t st).2 = false) :
    ∃ e, st.T.chi s t e = 1 ∧ M.face (M.rev e) ≠ st.T.root ∧
      (lstep M c ε s t st).1.T.root = st.T.root ∧
      (∀ x, (lstep M c ε s t st).1.T.par x =
        if x = M.face (M.rev e) then e else st.T.par x) ∧
      ∀ φ x, (lstep M c ε s t st).1.T.psum φ x = st.T.psum φ x +
        if st.T.Anc (M.face (M.rev e)) x then
          st.T.psum φ (M.face e) + φ e - st.T.psum φ (M.face (M.rev e)) else 0 := by
  have hne := pathSet_nonempty hM hst st.T (s := s) (t := t)
  obtain ⟨h1, h2⟩ := lstep_base_of_ne (c := c) (ε := ε) hne
  rw [h2] at h
  obtain ⟨hb, -, hroot, hpar, hps⟩ := stepE_facts h
  have hT : (lstep M c ε s t st).1.T =
      (stepE M c s t st.base (lbott c ε s t st.g st.h st.T hne)).1.T := congrArg St.T h1
  refine ⟨_, lbott_mem c ε s t _ _ _ hne, hb, ?_, ?_, ?_⟩
  · rw [hT, hroot]; rfl
  · intro x; rw [hT, hpar]; rfl
  · intro φ x; rw [hT, hps]; rfl

/-- **Along a run of pivots the root is fixed.** -/
lemma ltraj_root (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M} {j : ℕ}
    (hpiv : ∀ l < j, (lstep M c ε s t (ltraj M c ε s t st l)).2 = false) :
    ∀ l ≤ j, (ltraj M c ε s t st l).T.root = st.T.root := by
  intro l hl
  induction l with
  | zero => rfl
  | succ l ih =>
    obtain ⟨-, -, -, hroot, -⟩ := lpivot_facts hM hst (hpiv l (by omega))
    rw [ltraj, hroot, ih (by omega)]

/-- **A pivot of the perturbed run raises the levels of a subtree by `1`**: for every unit flow
`P` from `s` to `t`, the level `psum P x` of every face rises by `0` or `1`, by `1` for the face
that gets a new parent. -/
lemma lpivot_level (hM : M.IsPlane) (hst : s ≠ t) {st : LSt M}
    (h : (lstep M c ε s t st).2 = false) {P : D → ℤ} (hP : IsUnit (M := M) (s := s) (t := t) P) :
    ∃ e, M.face (M.rev e) ≠ st.T.root ∧
      (lstep M c ε s t st).1.T.par (M.face (M.rev e)) = e ∧
      (∀ x, x ≠ M.face (M.rev e) → (lstep M c ε s t st).1.T.par x = st.T.par x) ∧
      (lstep M c ε s t st).1.T.psum P (M.face (M.rev e)) =
        st.T.psum P (M.face (M.rev e)) + 1 ∧
      ∀ x, st.T.psum P x ≤ (lstep M c ε s t st).1.T.psum P x := by
  classical
  obtain ⟨e, he, hb, -, hpar, hps⟩ := lpivot_facts hM hst h
  have hinc : st.T.psum P (M.face e) + P e - st.T.psum P (M.face (M.rev e)) = 1 := by
    have := chi_eq_psum hM st.T hP.antisymm hP.div_eq e
    omega
  refine ⟨e, hb, by simp [hpar], fun x hx => by simp [hpar, hx], ?_, fun x => ?_⟩
  · rw [hps, hinc]; simp [st.T.anc_self]
  · rw [hps]; split_ifs <;> omega

/-! ### Each dart enters once -/

lemma abs_psum_lt (T : DTree M) {P : D → ℤ} (hP : ∀ d, |P d| ≤ 1) (x : F) :
    |T.psum P x| < Fintype.card F := by
  have := T.abs_psum_le hP x
  have := T.depth_lt_card x
  omega

lemma isUnit_pflow (π : SPath M) :
    IsUnit (M := M) (s := π.p 0) (t := π.p π.k) (pflow π) :=
  ⟨pflow_antisymm π, div_pflow π, fun d => by
    by_cases hd : d ∈ π.darts
    · obtain ⟨j, hj, rfl | rfl⟩ := π.mem_darts.1 hd
      · rw [pflow_d π hj]
      · rw [pflow_rev_d π hj]; omega
    · rw [pflow_of_not_mem π hd]; omega⟩

/-- The number of sheets: `4 F + 4`. -/
def nSheets (F' : Type*) [Fintype F'] : ℕ := 4 * Fintype.card F' + 4

instance nSheets_neZero (F' : Type*) [Fintype F'] : NeZero (nSheets F') :=
  ⟨by unfold nSheets; omega⟩

section Enter

variable (hrot : M.RotTrans) (π : SPath M) (hk : 0 < π.k)

local notation "K₀" => nSheets F
local notation "𝓜" => cover (pathCov hrot π) K₀
local notation "𝓛" => (liftPath hrot π K₀ hk).darts
local notation "hL" => (liftPath hrot π K₀ hk).rev_mem_darts'

/-- The lengths of the cut used in the analysis. -/
local notation "𝒢" => pieceGraph (cutMap hL) (cutPiece 𝓜 𝓛)
  (pert (cutLen 𝓜 𝓛 (covLen F K₀ c (lexEps D F))))

/-- The cut with the lengths `ℓ`, perturbed. -/
local notation "𝒢ℓ" ℓ => pieceGraph (cutMap hL) (cutPiece 𝓜 𝓛) (pert (cutLen 𝓜 𝓛 ℓ))

/-- The sheet of the root for the level `κ`: `m - κ` with `m = 2 F + 2`. -/
def sheetOf (κ : ℤ) : ZMod K₀ := (((2 * Fintype.card F + 2 : ℕ) : ℤ) - κ : ℤ)

lemma val_sheetOf {κ : ℤ} (hκ : |κ| < Fintype.card F) :
    ((sheetOf (F := F) κ).val : ℤ) = 2 * Fintype.card F + 2 - κ := by
  unfold sheetOf
  rw [abs_lt] at hκ
  have h0 : (0 : ℤ) ≤ ((2 * Fintype.card F + 2 : ℕ) : ℤ) - κ := by push_cast; omega
  have h1 : ((2 * Fintype.card F + 2 : ℕ) : ℤ) - κ < (K₀ : ℕ) := by
    unfold nSheets; push_cast; omega
  rw [ZMod.val_intCast, Int.emod_eq_of_lt h0 h1]; push_cast; ring

/-- The range condition of `tight_par` at the sheet of the level of `b`. -/
lemma range_sheetOf (T : DTree M) {b : F} :
    ∀ y, T.Anc y b → 1 ≤ ((sheetOf (F := F) (T.psum (pflow π) b)).val : ℤ) +
        T.psum (pflow π) y ∧
      ((sheetOf (F := F) (T.psum (pflow π) b)).val : ℤ) + T.psum (pflow π) y + 2 ≤ K₀ := by
  intro y _
  have hP : ∀ d, |pflow π d| ≤ 1 := (isUnit_pflow π).abs_le
  have h1 := abs_psum_lt T hP b
  have h2 := abs_psum_lt T hP y
  rw [val_sheetOf h1]
  rw [abs_lt] at h1 h2
  unfold nSheets; push_cast
  constructor <;> omega

/-- The lift of `d` ending at `(b, m)`: `(d, m - P d)`. -/
def liftEnd (d : D) : D × ZMod K₀ :=
  (d, ((2 * Fintype.card F + 2 : ℕ) : ZMod K₀) - (pflow π d : ZMod K₀))

lemma liftEnd_eq_par (T : DTree M) {b : F} (hb : b ≠ T.root) :
    (T.par b, sheetOf (F := F) (T.psum (pflow π) b) +
      ((T.psum (pflow π) (T.up b) : ℤ) : ZMod K₀)) = liftEnd π (T.par b) := by
  unfold liftEnd sheetOf
  rw [T.psum_of_ne _ hb]
  ext
  · rfl
  · push_cast; ring

variable (hM : M.IsPlane) (hface : M.FaceTrans) (hc : ∀ d, 0 ≤ c d)

include hM hface hc

/-- **The parent dart of `b` as a tight arc**: at every state of the perturbed run, the lift of
the parent dart of `b` ending at `(b, m)` is tight for the root of the level of `b`. -/
lemma tight_level {st : LSt M} (hI : LInv c (lexEps D F) (π.p 0) (π.p π.k) st) {d₀ : D}
    (hd₀ : M.tail d₀ = π.p π.k) (hroot : st.T.root = M.face d₀) {b : F} (hb : b ≠ st.T.root) :
    Tight 𝒢 (.inr (rootAt hrot π hk K₀ hd₀ (sheetOf (F := F) (st.T.psum (pflow π) b))))
      (toArc hrot π hk K₀ (liftEnd π (st.T.par b))) := by
  have := tight_par hrot π hk K₀ hM hface (by unfold nSheets; omega)
    (by unfold nSheets lexBase; omega) hc hI hd₀ hroot hb _ (range_sheetOf π st.T)
  rwa [liftEnd_eq_par π st.T hb] at this

omit hM hface hc in
variable (c ε) in
/-- **The tightness of the parent darts in the cut of the cover with the lengths `ℓ`**, at every
state of the run with the perturbation `ε` (`tight_level` for `lexEps`; `tight_parW` for the
word-size perturbation). -/
def TightLev (ℓ : D × ZMod K₀ → ℤ) : Prop :=
  ∀ {st : LSt M}, LInv c ε (π.p 0) (π.p π.k) st → ∀ {d₀ : D} (hd₀ : M.tail d₀ = π.p π.k),
    st.T.root = M.face d₀ → ∀ {b : F}, b ≠ st.T.root →
      Tight (𝒢ℓ ℓ) (.inr (rootAt hrot π hk K₀ hd₀ (sheetOf (F := F) (st.T.psum (pflow π) b))))
        (toArc hrot π hk K₀ (liftEnd π (st.T.par b)))

/-- `tight_level` as `TightLev` for `lexEps`. -/
lemma tightLev_lex : TightLev c (lexEps D F) hrot π hk (covLen F K₀ c (lexEps D F)) :=
  fun hI _ hd₀ hroot _ hb => tight_level hrot π hk hM hface hc hI hd₀ hroot hb

omit hM hface hc in
lemma liftEnd_not_mem (d : D) : liftEnd π d ∉ 𝓛 := by
  intro h
  obtain ⟨j, hj, e | e⟩ := (CombMap.mem_liftPath_darts hrot π K₀ hk).1 h
  · have h1 := congrArg Prod.fst e
    have h2 := congrArg Prod.snd e
    simp only [liftEnd] at h1 h2
    rw [h1, pflow_d π hj] at h2
    have : (((2 * Fintype.card F + 2 : ℕ) : ℤ) : ZMod K₀) = 0 := by
      push_cast at h2 ⊢; linear_combination h2
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    have := Int.le_of_dvd (by positivity) this
    unfold nSheets at this; push_cast at this; omega
  · have h1 := congrArg Prod.fst e
    have h2 := congrArg Prod.snd e
    simp only [liftEnd] at h1 h2
    rw [h1, pflow_rev_d π hj] at h2
    have : (((2 * Fintype.card F + 3 : ℕ) : ℤ) : ZMod K₀) = 0 := by
      push_cast at h2 ⊢; linear_combination h2
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    have := Int.le_of_dvd (by positivity) this
    unfold nSheets at this; push_cast at this; omega

omit hM hface hc in
lemma toArc_liftEnd_inj {d d' : D}
    (h : toArc hrot π hk K₀ (liftEnd π d) = toArc hrot π hk K₀ (liftEnd π d')) : d = d' := by
  rw [toArc_of_not_mem hrot π hk K₀ (liftEnd_not_mem hrot π hk d),
    toArc_of_not_mem hrot π hk K₀ (liftEnd_not_mem hrot π hk d')] at h
  have := congrArg Subtype.val h
  simp only [copyA, Sum.inl.injEq, Subtype.mk.injEq] at this
  exact congrArg Prod.fst this

include hrot hk in
/-- **The parent dart of `b` is a function of its level**, along the perturbed run (for any
perturbation whose parent darts are tight for lengths `ℓ ≥ 0`, `TightLev`). -/
lemma par_eq_of_level {ε : D → ℤ} {ℓ : D × ZMod K₀ → ℤ} (hℓ : ∀ e, 0 ≤ ℓ e)
    (hT : TightLev c ε hrot π hk ℓ) {st st' : LSt M} (hI : LInv c ε (π.p 0) (π.p π.k) st)
    (hI' : LInv c ε (π.p 0) (π.p π.k) st') {d₀ : D} (hd₀ : M.tail d₀ = π.p π.k)
    (hroot : st.T.root = M.face d₀) (hroot' : st'.T.root = M.face d₀) {b : F}
    (hb : b ≠ st.T.root) (hlev : st.T.psum (pflow π) b = st'.T.psum (pflow π) b) :
    st.T.par b = st'.T.par b := by
  have hb' : b ≠ st'.T.root := by rwa [hroot', ← hroot]
  have H := cutCover_hyp hrot π hk K₀ hM hface (by unfold nSheets; omega) ℓ (fun e _ => hℓ e)
  have t1 := hT hI hd₀ hroot hb
  have t2 := hT hI' hd₀ hroot' hb'
  rw [← hlev] at t2
  have e := H.uniq _ _ _ t1 t2 (by
      rw [toArc_of_not_mem hrot π hk K₀ (liftEnd_not_mem hrot π hk _),
        toArc_of_not_mem hrot π hk K₀ (liftEnd_not_mem hrot π hk _), copyA_dst, copyA_dst]
      simp [liftEnd, st.T.head_par b hb, st'.T.head_par b hb'])
    (by
      rw [toArc_of_not_mem hrot π hk K₀ (liftEnd_not_mem hrot π hk _), copyA_dst]
      simp)
  exact toArc_liftEnd_inj hrot π hk e

include hrot hk in
/-- A lift of a dart into `(b, m)` other than the lift of the parent dart is not tight. -/
lemma not_tight_level {ε : D → ℤ} {ℓ : D × ZMod K₀ → ℤ} (hℓ : ∀ e, 0 ≤ ℓ e)
    (hT : TightLev c ε hrot π hk ℓ) {st : LSt M} (hI : LInv c ε (π.p 0) (π.p π.k) st) {d₀ : D}
    (hd₀ : M.tail d₀ = π.p π.k) (hroot : st.T.root = M.face d₀) {d : D}
    (hb : M.face (M.rev d) ≠ st.T.root) (hne : st.T.par (M.face (M.rev d)) ≠ d) :
    ¬ Tight (𝒢ℓ ℓ) (.inr (rootAt hrot π hk K₀ hd₀
      (sheetOf (F := F) (st.T.psum (pflow π) (M.face (M.rev d))))))
      (toArc hrot π hk K₀ (liftEnd π d)) := by
  intro h
  have H := cutCover_hyp hrot π hk K₀ hM hface (by unfold nSheets; omega) ℓ (fun e _ => hℓ e)
  have t1 := hT hI hd₀ hroot hb
  have e := H.uniq _ _ _ t1 h (by
      rw [toArc_of_not_mem hrot π hk K₀ (liftEnd_not_mem hrot π hk _),
        toArc_of_not_mem hrot π hk K₀ (liftEnd_not_mem hrot π hk _), copyA_dst, copyA_dst]
      simp [liftEnd, st.T.head_par _ hb])
    (by
      rw [toArc_of_not_mem hrot π hk K₀ (liftEnd_not_mem hrot π hk _), copyA_dst]
      simp)
  exact hne (toArc_liftEnd_inj hrot π hk e)

omit hM hface hc in
/-- The root of the level `κ` along the ring. -/
lemma ring_level {j₀ : ℕ} (hj0 : 0 < j₀) (hj1 : j₀ ≤ perT π) {d₀ : D}
    (hj : M.rot^[j₀] (yT π) = d₀) (hd₀ : M.tail d₀ = π.p π.k) {κ : ℤ}
    (hκ : |κ| < Fintype.card F) :
    (tourT hL)^[j₀ - 1 + perT π * (2 * Fintype.card F + 1 + κ).toNat] (t0T hrot π hk K₀) =
      rootAt hrot π hk K₀ hd₀ (sheetOf (F := F) κ) := by
  rw [abs_lt] at hκ
  have hq : (2 * Fintype.card F + 1 + κ).toNat < K₀ := by
    unfold nSheets; omega
  apply Subtype.ext
  rw [ring_root hrot π hk K₀ hj0 hj1 hj hq]
  simp only [rootAt, sheetOf]
  ext
  · rfl
  · simp only
    have e : ((2 * Fintype.card F + 1 + κ).toNat : ℤ) = 2 * Fintype.card F + 1 + κ := by omega
    have hK : ((4 * Fintype.card F + 4 : ℕ) : ZMod K₀) = 0 := ZMod.natCast_self K₀
    have e2 : (((2 * Fintype.card F + 1 + κ).toNat : ℕ) : ZMod K₀) =
        (((2 * Fintype.card F + 1 + κ : ℤ)) : ZMod K₀) := by
      rw [← e]; push_cast; rfl
    rw [e2]
    push_cast [Int.cast_natCast] at hK ⊢
    linear_combination -hK

end Enter

/-- **Each dart enters the dual tree at most once** along the perturbed run with any perturbation
whose parent darts are tight in the cut of the cover (`TightLev`), on a plane map with
transitive rotations and faces, from any state satisfying `LInv` rooted at the face of a dart
leaving `t`. -/
theorem lenterOnce_of (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hc : ∀ d, 0 ≤ c d) (hst : s ≠ t) {ε : D → ℤ}
    (hTL : ∀ (π : SPath M) (hk : 0 < π.k), π.p 0 = s → π.p π.k = t →
      ∃ ℓ, (∀ e, 0 ≤ ℓ e) ∧ TightLev c ε hrot π hk ℓ)
    {d₀ : D} (hd₀ : M.tail d₀ = t) {st : LSt M}
    (hI : LInv c ε s t st) (hroot : st.T.root = M.face d₀) (i j : ℕ) (d : D)
    (hij : i < j)
    (hpiv : ∀ l ≤ j, (lstep M c ε s t (ltraj M c ε s t st l)).2 = false)
    (h1 : d ∉ (ltraj M c ε s t st i).T.parSet)
    (h2 : d ∈ (ltraj M c ε s t st (i + 1)).T.parSet)
    (h3 : d ∉ (ltraj M c ε s t st j).T.parSet) :
    d ∉ (ltraj M c ε s t st (j + 1)).T.parSet := by
  classical
  intro h4
  obtain ⟨π, hk, hs, ht⟩ := exists_sPath hM hst
  subst hs ht
  obtain ⟨ℓ₀, hℓ₀, hT₀⟩ := hTL π hk rfl rfl
  set S := ltraj M c ε (π.p 0) (π.p π.k) st with hS
  set P := pflow π
  have hPu := isUnit_pflow π
  have hIS : ∀ τ, LInv c ε (π.p 0) (π.p π.k) (S τ) := ltraj_inv hM hI
  have hrootS : ∀ τ ≤ j + 1, (S τ).T.root = M.face d₀ := fun τ hτ =>
    (ltraj_root hM hst (fun l hl => hpiv l (by omega)) τ hτ).trans hroot
  -- the pivot at `i` brings `d`
  have hpivot : ∀ τ ≤ j, ∀ d', d' ∉ (S τ).T.parSet → d' ∈ (S (τ + 1)).T.parSet →
      M.face (M.rev d') ≠ (S τ).T.root ∧
      (S (τ + 1)).T.par (M.face (M.rev d')) = d' ∧
      (S (τ + 1)).T.psum P (M.face (M.rev d')) = (S τ).T.psum P (M.face (M.rev d')) + 1 := by
    intro τ hτ d' g1 g2
    obtain ⟨e, hbr, hpe, hpo, hle, -⟩ := lpivot_level hM hst (hpiv τ hτ) hPu
    have hde : d' = e := by
      obtain ⟨x, hx, rfl⟩ := DTree.mem_parSet.1 g2
      by_cases hxb : x = M.face (M.rev e)
      · subst hxb; exact hpe
      · exfalso
        have hx' : x ≠ (S τ).T.root := by
          have := (lpivot_facts hM hst (hpiv τ hτ)).choose_spec.2.2.1
          rw [show (S (τ + 1)) = (lstep M c ε _ _ (S τ)).1 from rfl, this] at hx; exact hx
        apply g1
        have : (S (τ + 1)).T.par x = (S τ).T.par x := hpo x hxb
        rw [this]
        exact DTree.mem_parSet.2 ⟨x, hx', rfl⟩
    subst hde
    exact ⟨hbr, hpe, hle⟩
  obtain ⟨hbi, hpi, hli⟩ := hpivot i hij.le d h1 h2
  obtain ⟨hbj, hpj, hlj⟩ := hpivot j le_rfl d h3 h4
  set b := M.face (M.rev d)
  -- the levels of `b`
  set lev : ℕ → ℤ := fun τ => (S τ).T.psum P b
  have hmono : ∀ τ < j + 1, lev τ ≤ lev (τ + 1) := fun τ hτ =>
    (lpivot_level hM hst (hpiv τ (by omega)) hPu).choose_spec.2.2.2.2 b
  have hmono' : ∀ n, i + 1 + n ≤ j → lev (i + 1) ≤ lev (i + 1 + n) := by
    intro n hn
    induction n with
    | zero => exact le_rfl
    | succ n ih => exact (ih (by omega)).trans (hmono _ (by omega))
  have hle1 : lev (i + 1) ≤ lev j := by
    have := hmono' (j - (i + 1)) (by omega)
    rwa [show i + 1 + (j - (i + 1)) = j by omega] at this
  -- the parents of `b`
  have hbroot : ∀ τ ≤ j + 1, b ≠ (S τ).T.root := fun τ hτ => by
    rw [hrootS τ hτ, ← hrootS i (by omega)]; exact hbi
  have hpar_i : (S i).T.par b ≠ d := fun e =>
    h1 (DTree.mem_parSet.2 ⟨b, hbroot i (by omega), e⟩)
  have hpar_j : (S j).T.par b ≠ d := fun e =>
    h3 (DTree.mem_parSet.2 ⟨b, hbroot j (by omega), e⟩)
  have hlt1 : lev (i + 1) < lev j := by
    refine lt_of_le_of_ne hle1 fun e => hpar_j ?_
    rw [← hpi]
    exact (par_eq_of_level hrot π hk hM hface hc hℓ₀ hT₀ (hIS (i + 1)) (hIS j) hd₀
      (hrootS _ (by omega)) (hrootS _ (by omega)) (hbroot _ (by omega)) e).symm
  -- the ring
  have hd₀' : M.tail d₀ = π.p π.k := hd₀
  obtain ⟨j₀, hj0, hj1, hj⟩ := exists_j0 hrot π hk hd₀'
  set K := nSheets F
  obtain ⟨ℓT, hℓT, hTT⟩ := hTL π hk rfl rfl
  set G := pieceGraph (cutMap (liftPath hrot π K hk).rev_mem_darts')
    (cutPiece (cover (pathCov hrot π) K) (liftPath hrot π K hk).darts)
    (pert (cutLen _ _ ℓT))
  have hnn : ∀ e, e ∉ (liftPath hrot π K hk).darts → 0 ≤ ℓT e := fun e _ => hℓT e
  have H := cutCover_hyp hrot π hk K hM hface (by unfold K nSheets; omega) _ hnn
  have hR := cutCover_sameReach hrot π hk K (pert (cutLen _ _ ℓT))
  have hI := tight_interval H hR (toArc hrot π hk K (liftEnd π d))
  set posOf : ℤ → ℕ := fun κ => j₀ - 1 + perT π * (2 * Fintype.card F + 1 + κ).toNat
  have hbound : ∀ τ, |lev τ| < Fintype.card F := fun τ => abs_psum_lt _ hPu.abs_le b
  have hA : ∀ τ ≤ j + 1, (Tight G ((cutMap (liftPath hrot π K hk).rev_mem_darts').tail
      (cutG (liftPath hrot π K hk).rev_mem_darts' (t0T hrot π hk K) (posOf (lev τ))))
      (toArc hrot π hk K (liftEnd π d)) ↔ (S τ).T.par b = d) := by
    intro τ hτ
    have e : (cutMap (liftPath hrot π K hk).rev_mem_darts').tail
        (cutG (liftPath hrot π K hk).rev_mem_darts' (t0T hrot π hk K) (posOf (lev τ))) =
        .inr (rootAt hrot π hk K hd₀' (sheetOf (F := F) (lev τ))) := by
      show Sum.inr _ = _
      rw [ring_level hrot π hk hj0 hj1 hj hd₀' (hbound τ)]
    rw [e]
    constructor
    · intro hT
      by_contra hne
      exact not_tight_level hrot π hk hM hface hc hℓT hTT (hIS τ) hd₀' (hrootS τ hτ)
        (hbroot τ hτ) hne hT
    · intro hpe
      have := hTT (hIS τ) hd₀' (hrootS τ hτ) (hbroot τ hτ)
      rwa [hpe] at this
  have hposlt : ∀ κ κ' : ℤ, |κ| < Fintype.card F → |κ'| < Fintype.card F → κ < κ' →
      posOf κ < posOf κ' := by
    intro κ κ' h h' hlt
    rw [abs_lt] at h h'
    have : (2 * Fintype.card F + 1 + κ).toNat < (2 * Fintype.card F + 1 + κ').toNat := by omega
    have := perT_pos π
    show j₀ - 1 + perT π * _ < j₀ - 1 + perT π * _
    have := Nat.mul_lt_mul_of_pos_left ‹(2 * Fintype.card F + 1 + κ).toNat < _› this
    omega
  have hposK : ∀ κ : ℤ, |κ| < Fintype.card F →
      posOf κ < minimalPeriod (tourT (liftPath hrot π K hk).rev_mem_darts') (t0T hrot π hk K) := by
    intro κ h
    rw [abs_lt] at h
    refine lt_of_lt_of_le ?_ (ring_len hrot π hk K)
    have hq : (2 * Fintype.card F + 1 + κ).toNat + 1 ≤ K := by unfold K nSheets; omega
    have h2 := Nat.mul_le_mul_left (perT π) hq
    show j₀ - 1 + perT π * _ < K * perT π
    rw [mul_comm K]
    rw [Nat.mul_add, mul_one] at h2
    omega
  -- the four levels
  have hAi1 := (hA (i + 1) (by omega)).2 hpi
  have hAj1 := (hA (j + 1) le_rfl).2 hpj
  have hAi := fun h => hpar_i ((hA i (by omega)).1 h)
  have hAj := fun h => hpar_j ((hA j (by omega)).1 h)
  have hli' : lev (i + 1) = lev i + 1 := hli
  have hlj' : lev (j + 1) = lev j + 1 := hlj
  have p1 := hposlt _ _ (hbound i) (hbound (i + 1)) (by omega)
  have p2 := hposlt _ _ (hbound (i + 1)) (hbound j) hlt1
  have p3 := hposlt _ _ (hbound j) (hbound (j + 1)) (by omega)
  rcases hI _ _ (p2.trans p3) (hposK _ (hbound (j + 1))) hAi1 hAj1 with hin | hout
  · exact hAj (hin _ p2.le p3.le)
  · exact hAi (hout _ (hposK _ (hbound i)) (Or.inr p1.le))

/-- **Each dart enters the dual tree at most once** along the perturbed run, on a plane map with
transitive rotations and faces, from any state satisfying `LInv` rooted at the face of a dart
leaving `t`. -/
theorem lenterOnce (hM : M.IsPlane) (hrot : M.RotTrans) (hface : M.FaceTrans)
    (hc : ∀ d, 0 ≤ c d) (hst : s ≠ t) {d₀ : D} (hd₀ : M.tail d₀ = t) {st : LSt M}
    (hI : LInv c (lexEps D F) s t st) (hroot : st.T.root = M.face d₀) (i j : ℕ) (d : D)
    (hij : i < j)
    (hpiv : ∀ l ≤ j, (lstep M c (lexEps D F) s t (ltraj M c (lexEps D F) s t st l)).2 = false)
    (h1 : d ∉ (ltraj M c (lexEps D F) s t st i).T.parSet)
    (h2 : d ∈ (ltraj M c (lexEps D F) s t st (i + 1)).T.parSet)
    (h3 : d ∉ (ltraj M c (lexEps D F) s t st j).T.parSet) :
    d ∉ (ltraj M c (lexEps D F) s t st (j + 1)).T.parSet :=
  lenterOnce_of hM hrot hface hc hst (fun π hk _ _ => ⟨_, fun e => covLen_nonneg _ hc
    (fun d => lexEps_nonneg d) e, tightLev_lex hrot π hk hM hface hc⟩) hd₀ hI hroot i j d hij hpiv
    h1 h2 h3

end STFlow

end PlanarFlow
