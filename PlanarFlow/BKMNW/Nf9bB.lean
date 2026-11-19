module

public import PlanarFlow.BKMNW.Nf9bA

/-!
# The corners chosen by the prologue of `fixP`, on a frame of any map

`Nf7aCor` (`callIn_on`, `callIn_tt`, `callIn_corners`) for the frame `MFr` and the parts
`SegsL` (a path `πj` of the frame's map with the darts of `segs[j]`):

* `cIn_pdv`, `cIn_on`, `cIn_tw`, **`cIn_tt`** (the walk of the prologue follows `tour` around
  `πj`), `cIn_lab_iff`, `cIn_mk0`;
* **`cIn_corners`**: with `β x = face (en (cw.bt x))`, `b = cw.cnt`: `β x = fixCorner M πj
  (cw.st x)`, `cw.st` increasing and `< fixPer`, `β` injective onto the faces along the path, and
  `β (ix i) = face (en i)` for every frame dart on a face along the path;
* `cIn_bt_lt` (the corner words are frame indices).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace F9b

open Finset Function Equiv Orbit CombMap OrbLab MfDrv NcFz

variable {D V F : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}
variable {en : ℕ → D} {m Z d : ℕ} {cap f : D → ℤ} {mem : ℕ → ℕ}
  {segs : List (SPath M)} {lo hi Gb j : ℕ}

section Corners

variable (hL : MFr M en m Z cap f d mem) (hS : SegsL M en m segs lo hi Gb mem)
  (hj : j < segs.length) {πj : SPath M} (hk : πj.k = (cIn d m Gb segs j Z mem).k)
  (hd : ∀ l < πj.k, πj.d l = (segs[j]).d l)
include hL hS hj hk hd

/-- The frame index `PD l` is the dart `πj.d l`. -/
lemma cIn_pdv {l : ℕ} (hl : l < πj.k) :
    (cIn d m Gb segs j Z mem).PD l < m ∧ en ((cIn d m Gb segs j Z mem).PD l) = πj.d l :=
  ⟨(cIn_pd hS hj (hk ▸ hl)).1, by rw [(cIn_pd hS hj (hk ▸ hl)).2, hd l hl]⟩

/-- **The marks of the darts of the path.** -/
lemma cIn_on {i : ℕ} (hi : i < m) :
    (cIn d m Gb segs j Z mem).ON i = 1 ↔ en i ∈ πj.darts := by
  set p := cIn d m Gb segs j Z mem
  have e : p.ON i = fmk2 (fun _ => 0) p.PD (fun l => p.RV (p.PD l)) p.k i := rfl
  rw [e, fmk2_eq, SPath.mem_darts]
  constructor
  · intro h
    split_ifs at h with hx
    · obtain ⟨l, hl, hl'⟩ := hx
      obtain ⟨h1, h2⟩ := cIn_pdv hL hS hj hk hd (l := l) (by omega)
      refine ⟨l, by omega, ?_⟩
      rcases hl' with rfl | rfl
      · left; exact h2
      · right
        rw [(cIn_rv hL h1).2, h2]
  · rintro ⟨l, hl, hl'⟩
    obtain ⟨h1, h2⟩ := cIn_pdv hL hS hj hk hd hl
    rw [if_pos]
    refine ⟨l, by omega, ?_⟩
    rcases hl' with e | e
    · left; rw [← h2] at e; exact hL.en_inj hi h1 e
    · right
      have h3 := cIn_rv (Gb := Gb) (sg := segs) (j := j) hL h1
      apply hL.en_inj hi h3.1
      rw [h3.2, h2]; exact e

omit hS hj hk hd in
lemma cIn_on_le {i : ℕ} : (cIn d m Gb segs j Z mem).ON i ≤ 1 := fmk2_le_one

omit hS hj hk hd in
/-- The walk on indices is `tnF` with the marks `ON`. -/
lemma cIn_tw : (cIn d m Gb segs j Z mem).tw = tnF d m mem (cIn d m Gb segs j Z mem).ON := by
  funext i
  have := cIn_on_le (d := d) (m := m) (Gb := Gb) (segs := segs) (j := j) (Z := Z) (mem := mem) hL
    (i := i)
  unfold FpIn.tw tnF
  by_cases h : (cIn d m Gb segs j Z mem).ON i = 1
  · simp only [h, ↓reduceIte, show 0 < 1 from by decide]; rfl
  · simp only [h, ↓reduceIte, show ¬ 0 < (cIn d m Gb segs j Z mem).ON i by omega]; rfl

/-- **The walk of the prologue follows `tour` around `πj`.** -/
theorem cIn_tt (hk0 : 0 < πj.k) (n : ℕ) :
    (cIn d m Gb segs j Z mem).tt n < m ∧
      en ((cIn d m Gb segs j Z mem).tt n) = (tour M πj.darts)^[n] (πj.d 0) := by
  obtain ⟨h0, e0⟩ := cIn_pdv hL hS hj hk hd hk0
  have := hL.tn_iter (Ld := πj.darts) (onm := (cIn d m Gb segs j Z mem).ON)
    (fun i hi => cIn_on hL hS hj hk hd hi) h0 n
  rw [e0] at this
  show (cIn d m Gb segs j Z mem).tw^[n] _ < m ∧ en ((cIn d m Gb segs j Z mem).tw^[n] _) = _
  rw [cIn_tw hL]; exact this

omit hS hj hk hd in
/-- Labels and faces. -/
lemma cIn_lab_iff (hft : M.FaceTrans) {i i' : ℕ} (hi : i < m) (hi' : i' < m) :
    (cIn d m Gb segs j Z mem).lab i = (cIn d m Gb segs j Z mem).lab i' ↔
      M.face (en i) = M.face (en i') := by
  rw [hL.face_eq_iff hft hi hi']
  simp only [FpIn.lab, cIn]; omega

/-- **The marks of the faces along the path.** -/
lemma cIn_mk0 (hft : M.FaceTrans) {i : ℕ} (hi : i < m) :
    (cIn d m Gb segs j Z mem).MK0 ((cIn d m Gb segs j Z mem).lab i) = 1 ↔
      M.face (en i) ∈ πj.faces := by
  set p := cIn d m Gb segs j Z mem
  have hlab : p.lab i ≤ m := by
    have := olab_lt hL.permOn_nx hi; simp only [p, FpIn.lab, cIn]; omega
  simp only [FpIn.MK0, show p.lab i ≤ p.m from hlab, ↓reduceIte, fmk2_eq]
  have key : (∃ l < p.k, p.lab i = p.lab (p.PD l) ∨ p.lab i = p.lab (p.RV (p.PD l))) ↔
      M.face (en i) ∈ πj.faces := by
    simp only [SPath.faces, List.mem_toFinset, List.mem_map, SPath.mem_darts]
    constructor
    · rintro ⟨l, hl, e⟩
      obtain ⟨h1, h2⟩ := cIn_pdv hL hS hj hk hd (l := l) (by omega)
      have h3 := cIn_rv (Gb := Gb) (sg := segs) (j := j) hL h1
      rcases e with e | e
      · refine ⟨πj.d l, ⟨l, by omega, Or.inl rfl⟩, ?_⟩
        rw [← h2]; exact ((cIn_lab_iff hL hft hi h1).1 e).symm
      · refine ⟨M.rev (πj.d l), ⟨l, by omega, Or.inr rfl⟩, ?_⟩
        rw [← h2, ← h3.2]; exact ((cIn_lab_iff hL hft hi h3.1).1 e).symm
    · rintro ⟨y, ⟨l, hl, e⟩, hf⟩
      obtain ⟨h1, h2⟩ := cIn_pdv hL hS hj hk hd hl
      have h3 := cIn_rv (Gb := Gb) (sg := segs) (j := j) hL h1
      refine ⟨l, by omega, ?_⟩
      rcases e with rfl | rfl
      · left; rw [← h2] at hf; exact (cIn_lab_iff hL hft hi h1).2 hf.symm
      · right
        rw [← h2, ← h3.2] at hf; exact (cIn_lab_iff hL hft hi h3.1).2 hf.symm
  by_cases h : ∃ l < p.k, p.lab i = p.lab (p.PD l) ∨ p.lab i = p.lab (p.RV (p.PD l))
  · simp only [h, ↓reduceIte, true_iff]; exact key.1 h
  · simp only [h, ↓reduceIte]
    exact ⟨fun e => absurd e (by omega), fun h' => absurd (key.2 h') h⟩

/-- **The corners chosen by the prologue.** -/
theorem cIn_corners (hrot : M.RotTrans) (hft : M.FaceTrans) (hk0 : 0 < πj.k) :
    let p := cIn d m Gb segs j Z mem
    let β : ℕ → F := fun x => M.face (en (p.cw.bt x))
    (∀ x < p.cw.cnt, p.cw.bt x < m ∧ β x = fixCorner M πj (p.cw.st x) ∧
      p.cw.st x < fixPer M πj ∧ β x ∈ πj.faces) ∧
    (∀ x y, x < y → y < p.cw.cnt → p.cw.st x < p.cw.st y) ∧
    (∀ x < p.cw.cnt, ∀ y < p.cw.cnt, β x = β y → x = y) ∧
    (∀ f ∈ πj.faces, ∃ x < p.cw.cnt, β x = f) ∧
    (∀ i < m, M.face (en i) ∈ πj.faces → p.ix i < p.cw.cnt ∧ β (p.ix i) = M.face (en i)) := by
  intro p β
  have htt := cIn_tt hL hS hj hk hd hk0
  have hfc : ∀ n, fixCorner M πj n = M.face (en (p.tt n)) := fun n => by
    unfold fixCorner; rw [(htt n).2]
  set per := fixPer M πj with hper
  have hp0 : 0 < per := fixPer_pos πj
  have hpm : per ≤ m := by
    rw [← hL.card]; exact Function.minimalPeriod_le_card
  have hmod : ∀ n, p.tt n = p.tt (n % per) := fun n => by
    apply hL.en_inj (htt n).1 (htt (n % per)).1
    rw [(htt n).2, (htt (n % per)).2]
    exact (Function.iterate_mod_minimalPeriod_eq).symm
  have h0 : ∀ a, p.MK0 a ≤ 1 := fun a => by
    simp only [FpIn.MK0]; split_ifs
    · exact fmk2_le_one
    · omega
  have hfin := cw_final (fun n => p.lab (p.tt n)) p.tt p.MK0 h0 hp0 hpm
    (fun i => by beta_reduce; rw [← hmod i]) (s := p.cw) rfl
  obtain ⟨f1, f2, f3, f4, f5⟩ := hfin
  have hI := cwRun_inv (fun n => p.lab (p.tt n)) p.tt p.MK0 h0 p.m
  -- `β x` is the face at step `st x`
  have hbt : ∀ x < p.cw.cnt, p.cw.bt x = p.tt (p.cw.st x) := fun x hx => (f1 x hx).2.1
  have hβ : ∀ x < p.cw.cnt, β x = fixCorner M πj (p.cw.st x) := fun x hx => by
    show M.face (en (p.cw.bt x)) = _
    rw [hfc, hbt x hx]
  -- a face along the path is some corner of the walk
  have hcov : ∀ i < m, M.face (en i) ∈ πj.faces →
      2 ≤ p.cw.mks (p.lab i) ∧ p.cw.mks (p.lab i) - 2 < p.cw.cnt ∧
        p.lab (p.tt (p.cw.st (p.cw.mks (p.lab i) - 2))) = p.lab i := fun i hi hf => by
    obtain ⟨b', s', -, hs', -, -, hcov'⟩ := exists_fixCornersInj hrot πj
    obtain ⟨t, ht, e⟩ := hcov' _ hf
    rw [hfc] at e
    have hlab : p.lab (p.tt (s' t)) = p.lab i :=
      (cIn_lab_iff hL hft (htt _).1 hi).2 e
    exact f3 (p.lab i) ((cIn_mk0 hL hS hj hk hd hft hi).2 hf) ⟨s' t, hs' t ht, hlab⟩
  refine ⟨fun x hx => ⟨by rw [hbt x hx]; exact (htt _).1, hβ x hx, (f1 x hx).1, ?_⟩, f2,
    fun x hx y hy e => ?_, fun f hf => ?_, fun i hi hf => ?_⟩
  · obtain ⟨-, hb, hm0, -, -⟩ := f1 x hx
    show M.face (en (p.cw.bt x)) ∈ πj.faces
    rw [hb]
    exact (cIn_mk0 hL hS hj hk hd hft (htt _).1).1 hm0
  · rw [hβ x hx, hβ y hy, hfc, hfc] at e
    exact cw_labels_inj hI hx hy ((cIn_lab_iff hL hft (htt _).1 (htt _).1).2 e)
  · obtain ⟨b', s', -, hs', hmem, -, hcov'⟩ := exists_fixCornersInj hrot πj
    obtain ⟨t, ht, e⟩ := hcov' _ hf
    have hi := (htt (s' t)).1
    have hf' : M.face (en (p.tt (s' t))) ∈ πj.faces := by rw [← hfc]; exact hmem t ht
    obtain ⟨-, c2, c3⟩ := hcov _ hi hf'
    refine ⟨_, c2, ?_⟩
    rw [hβ _ c2, hfc, ← e, hfc]
    exact (cIn_lab_iff hL hft (htt _).1 hi).1 c3
  · obtain ⟨-, c2, c3⟩ := hcov i hi hf
    refine ⟨c2, ?_⟩
    show β (p.cw.mks (p.lab i) - 2) = _
    rw [hβ _ c2, hfc]
    exact (cIn_lab_iff hL hft (htt _).1 hi).1 c3

end Corners

end F9b

end BKMNW

end PlanarFlow
