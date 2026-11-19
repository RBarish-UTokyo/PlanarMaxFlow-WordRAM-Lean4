module

public import PlanarFlow.BKMNW.NcFzN
public import PlanarFlow.BKMNW.Nf7eWI

/-!
# The prologue of `fixP` on a frame of any map (`MFr`)

The prologue (`fpPro`, `FpIn`) is memory-level; its meaning lemmas (`Nf7aSem`, `Nf7aGlue`,
`NpDivM`, `NpDiv.dvP_div`) are stated for the frame `Lay` of a call of the decomposition. Here
they are restated for the frame **`MFr M en m Z cap f d mem`**, a frame of an arbitrary map `M` (no
subtype of darts: the dart of index `i` is `en i`), and the parts **`SegsL M en m segs lo hi Gb`**:

* `MFr.sg_iter`, `MFr.nx_iter`, `MFr.permOn_sg`, `MFr.permOn_nx`, **`MFr.face_eq_iff`**,
  **`MFr.vert_eq_iff`**, `MFr.div_eq_sum`, **`MFr.dv_div`**, `MFr.tn_one`, **`MFr.tn_iter`**,
  `MFr.card`;
* **`cIn d m Gb segs j Z mem : FpIn`** (`callIn` with a list of paths), `cIn_k`, `cIn_pd`,
  `cIn_top`, **`cIn_pre`**, `cIn_cw`, `cIn_rv`, `cIn_fw`, **`cIn_dv`**, **`cIn_as`**;
* **`segsL_lift`**: the parts of the base map are parts of the map with pendant edges.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace NcFz

open Finset Function Equiv Orbit CombMap OrbLab MfDrv

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {en : ℕ → D} {m Z d : ℕ} {cap f : D → ℤ} {mem : ℕ → ℕ}

/-! ### The frame (dot-notation lemmas on `MFr`) -/

lemma MFr.en_inj (h : MFr M en m Z cap f d mem) {i j : ℕ} (hi : i < m) (hj : j < m)
    (e : en i = en j) : i = j := h.inj i hi j hj e

/-- The iterates of the index array `SG` follow the rotation. -/
lemma MFr.sg_iter (h : MFr M en m Z cap f d mem) :
    ∀ t i, i < m → (sgF d m mem)^[t] i < m ∧ en ((sgF d m mem)^[t] i) = M.rot^[t] (en i)
  | 0, i, hi => ⟨hi, rfl⟩
  | t + 1, i, hi => by
    obtain ⟨h1, h2⟩ := MFr.sg_iter h t i hi
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    obtain ⟨g1, g2⟩ := h.sg _ h1
    refine ⟨g1, ?_⟩
    show en (mem (d + 4 + 2 * m + (sgF d m mem)^[t] i)) = _
    rw [g2, h2]; rfl

/-- The iterates of the face walk `NX[i] = SG[RV[i]]` follow `next`. -/
lemma MFr.nx_iter (h : MFr M en m Z cap f d mem) :
    ∀ t i, i < m → (nxF d m mem)^[t] i < m ∧ en ((nxF d m mem)^[t] i) = M.next^[t] (en i)
  | 0, i, hi => ⟨hi, rfl⟩
  | t + 1, i, hi => by
    obtain ⟨h1, h2⟩ := MFr.nx_iter h t i hi
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    obtain ⟨g1, g2⟩ := h.rv _ h1
    obtain ⟨k1, k2⟩ := h.sg _ g1
    refine ⟨k1, ?_⟩
    show en (mem (d + 4 + 2 * m + mem (d + 4 + m + (nxF d m mem)^[t] i))) = _
    rw [k2, g2, M.rev_rev, h2]

lemma MFr.permOn_sg (h : MFr M en m Z cap f d mem) : PermOn (sgF d m mem) m where
  lt i hi := (h.sg i hi).1
  inj i hi j hj e := by
    have h1 := (h.sg i hi).2
    have h2 := (h.sg j hj).2
    unfold sgF at e
    rw [e, h2] at h1
    exact h.en_inj hi hj (M.rot_injective h1.symm)

lemma MFr.permOn_nx (h : MFr M en m Z cap f d mem) : PermOn (nxF d m mem) m where
  lt i hi := (h.nx_iter 1 i hi).1
  inj i hi j hj e := by
    have h1 := (h.nx_iter 1 i hi).2
    have h2 := (h.nx_iter 1 j hj).2
    simp only [Function.iterate_one] at h1 h2
    rw [e, h2] at h1
    exact h.en_inj hi hj (M.next_injective h1.symm)

/-- **Two darts of the frame have the same face iff their `NX` labels agree.** -/
lemma MFr.face_eq_iff (h : MFr M en m Z cap f d mem) (hft : M.FaceTrans) {i j : ℕ}
    (hi : i < m) (hj : j < m) :
    M.face (en i) = M.face (en j) ↔ olab (nxF d m mem) i = olab (nxF d m mem) j := by
  rw [olab_eq_iff h.permOn_nx hi hj]
  constructor
  · intro e
    obtain ⟨t, ht⟩ := hft _ _ e
    refine ⟨t, h.en_inj (h.nx_iter t i hi).1 hj ?_⟩
    rw [(h.nx_iter t i hi).2, ht]
  · rintro ⟨t, rfl⟩
    rw [(h.nx_iter t i hi).2, NsStep.face_next_iter]

/-- **Two darts of the frame have the same tail iff their `SG` labels agree.** -/
lemma MFr.vert_eq_iff (h : MFr M en m Z cap f d mem) (hrot : M.RotTrans) {i j : ℕ}
    (hi : i < m) (hj : j < m) :
    M.tail (en i) = M.tail (en j) ↔ olab (sgF d m mem) i = olab (sgF d m mem) j := by
  rw [olab_eq_iff h.permOn_sg hi hj]
  constructor
  · intro e
    obtain ⟨t, ht⟩ := hrot _ _ e
    refine ⟨t, h.en_inj (h.sg_iter t i hi).1 hj ?_⟩
    rw [(h.sg_iter t i hi).2, ht]
  · rintro ⟨t, rfl⟩
    rw [(h.sg_iter t i hi).2, M.tail_rot_iterate]

/-- **The net outflow at the tail of `en i`** is the sum of `g` over the darts of the same label. -/
lemma MFr.div_eq_sum (h : MFr M en m Z cap f d mem) (hrot : M.RotTrans) (g : D → ℤ) {i : ℕ}
    (hi : i < m) :
    M.div g (M.tail (en i)) =
      ∑ j ∈ (range m).filter (fun j => olab (sgF d m mem) j = olab (sgF d m mem) i), g (en j) := by
  classical
  unfold CombMap.div
  symm
  refine Finset.sum_bij' (fun j _ => en j) (fun y _ => Classical.choose (h.surj y))
    (fun j hj => ?_) (fun y hy => ?_) (fun j hj => ?_) (fun y hy => ?_) (fun j hj => rfl)
  · obtain ⟨h1, h2⟩ := mem_filter.1 hj
    simp only [mem_filter, mem_univ, true_and]
    exact (h.vert_eq_iff hrot (mem_range.1 h1) hi).2 h2
  · obtain ⟨h1, h2⟩ := Classical.choose_spec (h.surj y)
    simp only [mem_filter, mem_univ, true_and] at hy
    refine mem_filter.2 ⟨mem_range.2 h1, ?_⟩
    rw [← h.vert_eq_iff hrot h1 hi, h2, hy]
  · obtain ⟨h1, -⟩ := mem_filter.1 hj
    obtain ⟨g1, g2⟩ := Classical.choose_spec (h.surj (en j))
    exact h.en_inj g1 (mem_range.1 h1) g2
  · exact (Classical.choose_spec (h.surj y)).2

/-- **The net outflow from the machine's sums** (`dvP`): when the flow array holds `Z + g`. -/
theorem MFr.dv_div (h : MFr M en m Z cap f d mem) (hrot : M.RotTrans) {g : D → ℤ}
    (hfl : ∀ i < m, (mem (d + 4 + 6 * m + i) : ℤ) = Z + g (en i)) {i : ℕ} (hi : i < m) :
    ((dvS (olab (sgF d m mem)) (fun j => mem (d + 6 * m + 4 + j)) m (olab (sgF d m mem) i) : ℕ)
        : ℤ) - Z * (dvC (olab (sgF d m mem)) m (olab (sgF d m mem) i) : ℕ) =
      M.div g (M.tail (en i)) := by
  rw [h.div_eq_sum hrot g hi]
  unfold dvS dvC
  rw [Nat.cast_sum, card_eq_sum_ones, Nat.cast_sum, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 (mem_filter.1 hj).1
  have := hfl j hj'
  rw [show d + 4 + 6 * m + j = d + 6 * m + 4 + j by omega] at this
  simp only [Nat.cast_one, mul_one]
  omega

/-- One step of the walk around a list of darts. -/
lemma MFr.tn_one (h : MFr M en m Z cap f d mem) {Ld : List D} {onm : ℕ → ℕ}
    (hon : ∀ i < m, onm i = 1 ↔ en i ∈ Ld) {i : ℕ} (hi : i < m) :
    tnF d m mem onm i < m ∧ en (tnF d m mem onm i) = tour M Ld (en i) := by
  unfold tnF
  by_cases h1 : onm i = 1
  · have hm := (hon i hi).1 h1
    simp only [h1, ↓reduceIte, tour, hm]
    obtain ⟨a1, a2⟩ := h.nx_iter 1 i hi
    simp only [Function.iterate_one] at a1 a2
    exact ⟨a1, a2⟩
  · have hm : en i ∉ Ld := fun e => h1 ((hon i hi).2 e)
    simp only [h1, ↓reduceIte, tour, hm]
    exact h.sg i hi

/-- **The iterates of the walk** are those of `tour` around the list. -/
lemma MFr.tn_iter (h : MFr M en m Z cap f d mem) {Ld : List D} {onm : ℕ → ℕ}
    (hon : ∀ i < m, onm i = 1 ↔ en i ∈ Ld) {i : ℕ} (hi : i < m) :
    ∀ t, (tnF d m mem onm)^[t] i < m ∧ en ((tnF d m mem onm)^[t] i) = (tour M Ld)^[t] (en i)
  | 0 => ⟨hi, rfl⟩
  | t + 1 => by
    obtain ⟨h1, h2⟩ := MFr.tn_iter h hon hi t
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    obtain ⟨g1, g2⟩ := h.tn_one hon h1
    exact ⟨g1, by rw [g2, h2]⟩

/-- **The map has `m` darts.** -/
lemma MFr.card (h : MFr M en m Z cap f d mem) : Fintype.card D = m := by
  have : (univ : Finset D) = (range m).image en := by
    ext y
    simp only [mem_univ, mem_image, mem_range, true_iff]
    exact h.surj y
  rw [← card_univ, this, card_image_of_injOn (fun i hi j hj e =>
    h.en_inj (mem_range.1 hi) (mem_range.1 hj) e), card_range]

lemma MFr.congr (h : MFr M en m Z cap f d mem) {mem' : ℕ → ℕ}
    (he : ∀ a, d ≤ a → a < d + 4 + 7 * m → mem' a = mem a) : MFr M en m Z cap f d mem' where
  hm := by rw [he _ le_rfl (by omega)]; exact h.hm
  hz := by rw [he _ (by omega) (by omega)]; exact h.hz
  inj := h.inj
  surj := h.surj
  rv i hi := by rw [he _ (by omega) (by omega)]; exact h.rv i hi
  sg i hi := by rw [he _ (by omega) (by omega)]; exact h.sg i hi
  cp i hi := by rw [he _ (by omega) (by omega)]; exact h.cp i hi
  fl i hi := by rw [he _ (by omega) (by omega)]; exact h.fl i hi

end NcFz

namespace F9b

open Finset Function Equiv Orbit CombMap OrbLab MfDrv NcFz

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {en : ℕ → D} {m Z d : ℕ} {cap f : D → ℤ} {mem : ℕ → ℕ}

/-! ### The natural input of the prologue -/

/-- **The natural input of the prologue** on a frame with the parts `segs` (`callIn`). -/
def cIn (d m Gb : ℕ) (segs : List (SPath M)) (j Z : ℕ) (mem : ℕ → ℕ) : FpIn :=
  ⟨d, m, Gb, segs.length, ((segs.take j).map SPath.k).sum, (segs.map SPath.k).getD j 0, Z, mem⟩

variable {segs : List (SPath M)} {lo hi Gb j : ℕ}

lemma cIn_k (hj : j < segs.length) : (cIn d m Gb segs j Z mem).k = (segs[j]).k := by
  simp [cIn, List.getD_eq_getElem?_getD, hj]

/-- **The darts of the path in the frame.** -/
theorem cIn_pd (hS : SegsL M en m segs lo hi Gb mem) (hj : j < segs.length) {l : ℕ}
    (hl : l < (cIn d m Gb segs j Z mem).k) :
    (cIn d m Gb segs j Z mem).PD l < m ∧ en ((cIn d m Gb segs j Z mem).PD l) = (segs[j]).d l := by
  rw [cIn_k hj] at hl
  obtain ⟨-, -, -, h4⟩ := hS
  obtain ⟨-, -, h, -⟩ := h4 j hj
  have e : (cIn d m Gb segs j Z mem).PD l =
      mem (Gb + 1 + 2 * segs.length + ((segs.take j).map SPath.k).sum + l) := by
    simp only [FpIn.PD, FpIn.PDb, cIn]; congr 1; omega
  rw [e]; exact h l hl

/-- The block of the part `j` lies below the top of the parts. -/
theorem cIn_top (hS : SegsL M en m segs lo hi Gb mem) (hj : j < segs.length) :
    (cIn d m Gb segs j Z mem).PDb + (cIn d m Gb segs j Z mem).k ≤ hi ∧
      Gb + 1 + j + segs.length < hi ∧ lo ≤ (cIn d m Gb segs j Z mem).PDb := by
  obtain ⟨h1, -, h3, -⟩ := hS
  have hk := cIn_k (d := d) (m := m) (Z := Z) (mem := mem) (Gb := Gb) hj
  have hs : ((segs.take j).map SPath.k).sum + (segs[j]).k ≤ (segs.map SPath.k).sum := by
    have e : segs.take (j + 1) = segs.take j ++ [segs[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    have := sum_take_le_sum (segs.map SPath.k) (j + 1)
    rw [← List.map_take, e, List.map_append, List.sum_append] at this
    simpa using this
  simp only [FpIn.PDb, cIn] at hk ⊢
  refine ⟨by omega, by omega, by omega⟩

/-- **The hypotheses of `fpPro_exec` from the frame and the parts.** -/
theorem cIn_pre (hL : MFr M en m Z cap f d mem) (hS : SegsL M en m segs lo hi Gb mem)
    (hj : j < segs.length) :
    let p := cIn d m Gb segs j Z mem
    p.mem p.d = p.m ∧ p.mem (p.d + 3) = p.Z ∧ p.mem p.Gb = p.ns ∧
      p.mem (p.Gb + 1 + j) = p.off ∧ p.mem (p.Gb + 1 + j + p.ns) = p.k ∧
      (∀ i < p.m, p.RV i < p.m) ∧ PermOn (sgF p.d p.m p.mem) p.m ∧
      PermOn (nxF p.d p.m p.mem) p.m ∧ (∀ l < p.k, p.PD l < p.m) := by
  intro p
  obtain ⟨h1, h2, h3, h4⟩ := hS
  obtain ⟨g1, g2, -⟩ := h4 j hj
  refine ⟨hL.hm, hL.hz, h2, g1, ?_, fun i hi => (hL.rv i hi).1, hL.permOn_sg, hL.permOn_nx,
    fun l hl => (cIn_pd ⟨h1, h2, h3, h4⟩ hj hl).1⟩
  show mem (Gb + 1 + j + segs.length) = (segs.map SPath.k).getD j 0
  rw [show Gb + 1 + j + segs.length = Gb + 1 + segs.length + j by omega, g2]
  simp [List.getD_eq_getElem?_getD, hj]

variable {D₁ V₁ F₁ : Type} [Fintype D₁] [DecidableEq D₁] [Fintype V₁] [DecidableEq V₁]
  [Fintype F₁] [DecidableEq F₁] {M₁ : CombMap D₁ V₁ F₁} {sg : List (SPath M₁)}

variable (hL : MFr M en m Z cap f d mem)
include hL

/-- **The capacities.** -/
theorem cIn_cw {i : ℕ} (hi : i < m) : ((cIn d m Gb sg j Z mem).CP i : ℤ) = cap (en i) := by
  have := (hL.cp i hi).1
  simp only [FpIn.CP, cIn]
  rw [show d + 4 + m + m + m + i = d + 4 + 3 * m + i by omega]; exact this

/-- The reverse in the frame. -/
theorem cIn_rv {i : ℕ} (hi : i < m) :
    (cIn d m Gb sg j Z mem).RV i < m ∧ en ((cIn d m Gb sg j Z mem).RV i) = M.rev (en i) :=
  hL.rv i hi

/-- **The flow words**: `FLW[i] + K − Z = f (en i) + K` when `|f| ≤ K`. -/
theorem cIn_fw {i K : ℕ} (hi : i < m) (hK : |f (en i)| ≤ K) :
    (((cIn d m Gb sg j Z mem).FLW i + K - Z : ℕ) : ℤ) = f (en i) + K := by
  have h := hL.fl i hi
  have e : (cIn d m Gb sg j Z mem).FLW i = mem (d + 4 + 6 * m + i) := by
    simp only [FpIn.FLW, cIn]; congr 1; omega
  rw [e]
  have := (abs_le.1 hK).1
  omega

/-- **The net outflow words**: `DVw l = div f (tail (en (PD l))) + K` when `|div f| ≤ K`. -/
theorem cIn_dv (hrot : M.RotTrans) {l : ℕ} (hl : (cIn d m Gb sg j Z mem).PD l < m)
    (hK : |M.div f (M.tail (en ((cIn d m Gb sg j Z mem).PD l)))| ≤
      (cIn d m Gb sg j Z mem).K) :
    ((cIn d m Gb sg j Z mem).DVw l : ℤ) =
      M.div f (M.tail (en ((cIn d m Gb sg j Z mem).PD l))) + (cIn d m Gb sg j Z mem).K := by
  have h := hL.dv_div hrot (g := f) hL.fl hl
  have ef : (fun j => mem (d + 6 * m + 4 + j)) = (cIn d m Gb sg j Z mem).FLW := by
    funext i; simp only [FpIn.FLW, cIn]; congr 1; omega
  rw [ef] at h
  have key : ((cIn d m Gb sg j Z mem).DVw l : ℤ) =
      ((dvS (olab (sgF d m mem)) (cIn d m Gb sg j Z mem).FLW m
          (olab (sgF d m mem) ((cIn d m Gb sg j Z mem).PD l)) + (cIn d m Gb sg j Z mem).K -
        dvC (olab (sgF d m mem)) m (olab (sgF d m mem) ((cIn d m Gb sg j Z mem).PD l)) * Z :
          ℕ) : ℤ) := rfl
  rw [key]
  have := (abs_le.1 hK).1
  generalize (cIn d m Gb sg j Z mem).K = K at hK this ⊢
  generalize dvS (olab (sgF d m mem)) (cIn d m Gb sg j Z mem).FLW m
    (olab (sgF d m mem) ((cIn d m Gb sg j Z mem).PD l)) = A at h ⊢
  generalize dvC (olab (sgF d m mem)) m (olab (sgF d m mem) ((cIn d m Gb sg j Z mem).PD l)) = B
    at h ⊢
  have hle : B * Z ≤ A + K := by
    have : ((B * Z : ℕ) : ℤ) ≤ ((A + K : ℕ) : ℤ) := by push_cast; nlinarith
    exact_mod_cast this
  rw [Nat.cast_sub hle]
  push_cast
  linarith

/-- **The sum of the capacities is `absSum cap`.** -/
theorem cIn_as : ((cIn d m Gb sg j Z mem).AS : ℤ) = SPath.absSum cap := by
  unfold FpIn.AS SPath.absSum
  push_cast
  symm
  refine Finset.sum_bij' (fun y _ => Classical.choose (hL.surj y)) (fun i _ => en i)
    (fun y _ => ?_) (fun i hi => mem_univ _) (fun y _ => ?_) (fun i hi => ?_) (fun y _ => ?_)
  · exact mem_range.2 (Classical.choose_spec (hL.surj y)).1
  · exact (Classical.choose_spec (hL.surj y)).2
  · have h1 := Classical.choose_spec (hL.surj (en i))
    exact hL.en_inj h1.1 (mem_range.1 hi) h1.2
  · have h1 := Classical.choose_spec (hL.surj y)
    rw [cIn_cw hL h1.1, h1.2, abs_of_nonneg]
    rw [← h1.2, ← cIn_cw hL (Gb := Gb) (sg := sg) (j := j) h1.1]; positivity

omit hL

/-! ### The parts of the base map in the map with pendant edges -/

section Lift

variable {D₀ V₀ F₀ : Type} [Fintype D₀] [DecidableEq D₀] [Fintype V₀] [DecidableEq V₀]
  [Fintype F₀] [DecidableEq F₀] {M₀ : CombMap D₀ V₀ F₀} {e : V₀ → D₀}
  {he : ∀ v, M₀.tail (e v) = v}

lemma map_k_lift (segs₀ : List (SPath M₀)) :
    (segs₀.map (fun π => π.lift e he)).map SPath.k = segs₀.map SPath.k := by
  simp only [List.map_map]; rfl

/-- **The parts of the base map are parts of the map with pendant edges** (indices `< m ≤ m'`,
the numbering `en' = inl ∘ en` there). -/
theorem segsL_lift {en₀ : ℕ → D₀} {m₀ m' : ℕ} {en' : ℕ → D₀ ⊕ (V₀ × Bool)}
    {segs₀ : List (SPath M₀)} (hS : SegsL M₀ en₀ m₀ segs₀ lo hi Gb mem) (hmm : m₀ ≤ m')
    (hen : ∀ i < m₀, en' i = .inl (en₀ i)) :
    SegsL (M₀.pendant e he) en' m' (segs₀.map (fun π => π.lift e he)) lo hi Gb mem := by
  obtain ⟨h1, h2, h3, h4⟩ := hS
  have hk := map_k_lift (e := e) (he := he) segs₀
  have ht : ∀ j, ((segs₀.map (fun π => π.lift e he)).take j).map SPath.k =
      (segs₀.take j).map SPath.k := fun j => by
    rw [← List.map_take]; exact map_k_lift _
  refine ⟨h1, by rw [List.length_map]; exact h2, by rw [List.length_map, hk]; exact h3,
    fun j hj => ?_⟩
  have hj' : j < segs₀.length := by simpa using hj
  obtain ⟨g1, g2, g3, g4, g5⟩ := h4 j hj'
  simp only [List.length_map, List.getElem_map, ht j, hk]
  refine ⟨g1, g2, fun l hl => ?_, by omega, ?_⟩
  · obtain ⟨a1, a2⟩ := g3 l hl
    exact ⟨by omega, by rw [hen _ a1, a2]; rfl⟩
  · rw [hen _ g4]
    exact congrArg Sum.inl g5

end Lift

end F9b

end BKMNW

end PlanarFlow
