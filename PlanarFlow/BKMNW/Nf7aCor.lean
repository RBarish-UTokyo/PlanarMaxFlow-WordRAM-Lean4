module

public import PlanarFlow.BKMNW.Nf7aGlue

/-!
# The corners chosen by the prologue of `fixP`

The corner walk of the prologue (`FpIn.cw`, on the machine `cwProg`) walks `m` steps of `tour`
around the path `πj` of the piece map from its first dart and records each face along the path
at its first position. Here, at a node call (`Lay`, `SegsOut`, `πj = (segsP …)[j]`):

* `callIn_on` (the marks `ON` are those of the darts of `πj`), `callIn_tw` (the walk on indices
  is `tnF`), **`callIn_tt`** (`en (tt n) = (tour^[n] (πj.d 0)).1`);
* **`callIn_corners`**: with `β x = face (en (cw.bt x))` and `b = cw.cnt`:
  `β x = fixCorner (pmap h) πj (cw.st x)` with `cw.st` strictly increasing and `< fixPer`
  (so `crossing_fixPath` applies), `β x ∈ πj.faces`, `β` injective on `[0, b)`, every face along
  the path is some `β x`, and for every frame dart `i` whose face is along the path,
  `ix i < b` and `β (ix i) = face (en i)` (the words `ET`, `EH` of the prologue).
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

section Call

variable {x : MCall M} {m : ℕ} {en : ℕ → D} {d : ℕ} {mem : ℕ → ℕ}
  (hL : Lay M gid u S T Z x m en d mem) (hP : PieceInv M x.1.piece x.2.1 x.2.2)
  {π : HSep M} {lo hi Gb j : ℕ} (hS : SegsOut M en m π lo hi Gb mem) (hj : j < π.segs.length)
  {πj : SPath (pmap hP)} (hk : πj.k = (callIn d m Gb π j Z mem).k)
  (hd : ∀ l < πj.k, (πj.d l).1 = (π.segs[j]).d l)
include hL hS hj hk hd

/-- The frame index `PD l` is the dart `πj.d l`. -/
lemma callIn_pdv {l : ℕ} (hl : l < πj.k) :
    ∃ h : (callIn d m Gb π j Z mem).PD l < m, vDart hL h = πj.d l :=
  ⟨(callIn_pd hS hj (hk ▸ hl)).1, Subtype.ext (by
    rw [show (vDart hL _).1 = en _ from rfl, (callIn_pd hS hj (hk ▸ hl)).2, hd l hl])⟩

/-- **The marks of the darts of the path.** -/
lemma callIn_on {i : ℕ} (hi : i < m) :
    (callIn d m Gb π j Z mem).ON i = 1 ↔ vDart hL hi ∈ πj.darts := by
  set p := callIn d m Gb π j Z mem
  have e : p.ON i = fmk2 (fun _ => 0) p.PD (fun l => p.RV (p.PD l)) p.k i := rfl
  rw [e, fmk2_eq, SPath.mem_darts]
  constructor
  · intro h
    split_ifs at h with hx
    · obtain ⟨l, hl, hl'⟩ := hx
      obtain ⟨h1, h2⟩ := callIn_pdv hL hP hS hj hk hd (l := l) (by omega)
      refine ⟨l, by omega, ?_⟩
      rcases hl' with rfl | rfl
      · left; exact h2
      · right
        apply Subtype.ext
        show en (p.RV (p.PD l)) = M.rev (πj.d l).1
        rw [(callIn_rv hL h1).2, ← h2]; rfl
  · rintro ⟨l, hl, hl'⟩
    obtain ⟨h1, h2⟩ := callIn_pdv hL hP hS hj hk hd hl
    rw [if_pos]
    refine ⟨l, by omega, ?_⟩
    rcases hl' with e | e
    · left; rw [← h2] at e; exact hL.en_inj hi h1 (congrArg Subtype.val e)
    · right
      have h3 := callIn_rv (Gb := Gb) (π := π) (j := j) hL h1
      apply hL.en_inj hi h3.1
      have := congrArg Subtype.val e
      rw [h3.2]; exact this.trans (by rw [← h2]; rfl)

omit hS hj hk hd in
lemma callIn_on_le {i : ℕ} : (callIn d m Gb π j Z mem).ON i ≤ 1 := fmk2_le_one

omit hS hj hk hd in
/-- The walk on indices is `tnF` with the marks `ON`. -/
lemma callIn_tw : (callIn d m Gb π j Z mem).tw = tnF d m mem (callIn d m Gb π j Z mem).ON := by
  funext i
  have := callIn_on_le (d := d) (m := m) (Gb := Gb) (π := π) (j := j) (Z := Z) (mem := mem) hL
    (i := i)
  unfold FpIn.tw tnF
  by_cases h : (callIn d m Gb π j Z mem).ON i = 1
  · simp only [h, ↓reduceIte, show 0 < 1 from by decide]; rfl
  · simp only [h, ↓reduceIte, show ¬ 0 < (callIn d m Gb π j Z mem).ON i by omega]; rfl

/-- **The walk of the prologue follows `tour` around `πj`.** -/
theorem callIn_tt (hk0 : 0 < πj.k) (n : ℕ) :
    (callIn d m Gb π j Z mem).tt n < m ∧
      en ((callIn d m Gb π j Z mem).tt n) = ((tour (pmap hP) πj.darts)^[n] (πj.d 0)).1 := by
  obtain ⟨h0, e0⟩ := callIn_pdv hL hP hS hj hk hd hk0
  have := hL.tn_iter hP (Ld := πj.darts) (onm := (callIn d m Gb π j Z mem).ON)
    (fun i hi => callIn_on hL hP hS hj hk hd hi) h0 n
  rw [e0] at this
  show (callIn d m Gb π j Z mem).tw^[n] _ < m ∧ en ((callIn d m Gb π j Z mem).tw^[n] _) = _
  rw [callIn_tw hL]; exact this

/-- Labels and faces. -/
lemma callIn_lab_iff {i i' : ℕ} (hi : i < m) (hi' : i' < m) :
    (callIn d m Gb π j Z mem).lab i = (callIn d m Gb π j Z mem).lab i' ↔
      (pmap hP).face (vDart hL hi) = (pmap hP).face (vDart hL hi') := by
  rw [hL.face_eq_iff hP hi hi']
  simp only [FpIn.lab, callIn]; omega

/-- **The marks of the faces along the path.** -/
lemma callIn_mk0 {i : ℕ} (hi : i < m) :
    (callIn d m Gb π j Z mem).MK0 ((callIn d m Gb π j Z mem).lab i) = 1 ↔
      (pmap hP).face (vDart hL hi) ∈ πj.faces := by
  set p := callIn d m Gb π j Z mem
  have hlab : p.lab i ≤ m := by
    have := olab_lt hL.permOn_nx hi; simp only [p, FpIn.lab, callIn]; omega
  simp only [FpIn.MK0, show p.lab i ≤ p.m from hlab, ↓reduceIte, fmk2_eq]
  have key : (∃ l < p.k, p.lab i = p.lab (p.PD l) ∨ p.lab i = p.lab (p.RV (p.PD l))) ↔
      (pmap hP).face (vDart hL hi) ∈ πj.faces := by
    simp only [SPath.faces, List.mem_toFinset, List.mem_map, SPath.mem_darts]
    constructor
    · rintro ⟨l, hl, e⟩
      obtain ⟨h1, h2⟩ := callIn_pdv hL hP hS hj hk hd (l := l) (by omega)
      have h3 := callIn_rv (Gb := Gb) (π := π) (j := j) hL h1
      rcases e with e | e
      · refine ⟨πj.d l, ⟨l, by omega, Or.inl rfl⟩, ?_⟩
        rw [← h2]; exact ((callIn_lab_iff hL hP hS hj hk hd hi h1).1 e).symm
      · refine ⟨(pmap hP).rev (πj.d l), ⟨l, by omega, Or.inr rfl⟩, ?_⟩
        have hv : vDart hL h3.1 = (pmap hP).rev (πj.d l) := Subtype.ext (by
          show en _ = M.rev (πj.d l).1; rw [h3.2, ← h2]; rfl)
        rw [← hv]; exact ((callIn_lab_iff hL hP hS hj hk hd hi h3.1).1 e).symm
    · rintro ⟨y, ⟨l, hl, e⟩, hf⟩
      obtain ⟨h1, h2⟩ := callIn_pdv hL hP hS hj hk hd hl
      have h3 := callIn_rv (Gb := Gb) (π := π) (j := j) hL h1
      refine ⟨l, by omega, ?_⟩
      rcases e with rfl | rfl
      · left; rw [← h2] at hf; exact (callIn_lab_iff hL hP hS hj hk hd hi h1).2 hf.symm
      · right
        have hv : vDart hL h3.1 = (pmap hP).rev (πj.d l) := Subtype.ext (by
          show en _ = M.rev (πj.d l).1; rw [h3.2, ← h2]; rfl)
        rw [← hv] at hf; exact (callIn_lab_iff hL hP hS hj hk hd hi h3.1).2 hf.symm
  by_cases h : ∃ l < p.k, p.lab i = p.lab (p.PD l) ∨ p.lab i = p.lab (p.RV (p.PD l))
  · simp only [h, ↓reduceIte, true_iff]; exact key.1 h
  · simp only [h, ↓reduceIte]
    exact ⟨fun e => absurd e (by omega), fun h' => absurd (key.2 h') h⟩

/-- **The corners chosen by the prologue.** -/
theorem callIn_corners (hrot : (pmap hP).RotTrans) (hk0 : 0 < πj.k) :
    let p := callIn d m Gb π j Z mem
    let β : ℕ → _ := fun x => if h : p.cw.bt x < m then (pmap hP).face (vDart hL h)
      else (pmap hP).face (πj.d 0)
    (∀ x < p.cw.cnt, β x = fixCorner (pmap hP) πj (p.cw.st x) ∧
      p.cw.st x < fixPer (pmap hP) πj ∧ β x ∈ πj.faces) ∧
    (∀ x y, x < y → y < p.cw.cnt → p.cw.st x < p.cw.st y) ∧
    (∀ x < p.cw.cnt, ∀ y < p.cw.cnt, β x = β y → x = y) ∧
    (∀ f ∈ πj.faces, ∃ x < p.cw.cnt, β x = f) ∧
    (∀ i (hi : i < m), (pmap hP).face (vDart hL hi) ∈ πj.faces →
      p.ix i < p.cw.cnt ∧ β (p.ix i) = (pmap hP).face (vDart hL hi)) := by
  intro p β
  have htt := callIn_tt hL hP hS hj hk hd hk0
  -- the corners along the walk
  have hfc : ∀ n, fixCorner (pmap hP) πj n = (pmap hP).face (vDart hL (htt n).1) := fun n => by
    unfold fixCorner; congr 1; exact (Subtype.ext (htt n).2).symm
  set per := fixPer (pmap hP) πj with hper
  have hp0 : 0 < per := fixPer_pos πj
  have hpm : per ≤ m := by
    rw [← hL.card_sdart]; exact Function.minimalPeriod_le_card
  have hmod : ∀ n, p.tt n = p.tt (n % per) := fun n => by
    apply hL.en_inj (htt n).1 (htt (n % per)).1
    rw [(htt n).2, (htt (n % per)).2]
    congr 1
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
  have hβ : ∀ x < p.cw.cnt, β x = fixCorner (pmap hP) πj (p.cw.st x) := fun x hx => by
    obtain ⟨-, hb, -, -, -⟩ := f1 x hx
    have hlt : p.cw.bt x < m := by rw [hb]; exact (htt _).1
    simp only [β, hlt, ↓reduceDIte]
    rw [hfc]; congr 1; exact Subtype.ext (by simp only [vDart]; rw [hb])
  -- a face along the path is some corner of the walk
  have hcov : ∀ i (hi : i < m), (pmap hP).face (vDart hL hi) ∈ πj.faces →
      2 ≤ p.cw.mks (p.lab i) ∧ p.cw.mks (p.lab i) - 2 < p.cw.cnt ∧
        p.lab (p.tt (p.cw.st (p.cw.mks (p.lab i) - 2))) = p.lab i := fun i hi hf => by
    obtain ⟨b', s', -, hs', -, -, hcov'⟩ := exists_fixCornersInj hrot πj
    obtain ⟨t, ht, e⟩ := hcov' _ hf
    rw [hfc] at e
    have hlab : p.lab (p.tt (s' t)) = p.lab i :=
      (callIn_lab_iff hL hP hS hj hk hd (htt _).1 hi).2 e
    have := f3 (p.lab i) ((callIn_mk0 hL hP hS hj hk hd hi).2 hf) ⟨s' t, hs' t ht, hlab⟩
    exact this
  refine ⟨fun x hx => ⟨hβ x hx, (f1 x hx).1, ?_⟩, f2, fun x hx y hy e => ?_, fun f hf => ?_,
    fun i hi hf => ?_⟩
  · obtain ⟨-, hb, hm0, -, -⟩ := f1 x hx
    rw [hβ x hx, hfc]
    exact (callIn_mk0 hL hP hS hj hk hd (htt _).1).1 hm0
  · rw [hβ x hx, hβ y hy, hfc, hfc] at e
    exact cw_labels_inj hI hx hy ((callIn_lab_iff hL hP hS hj hk hd (htt _).1 (htt _).1).2 e)
  · obtain ⟨b', s', -, hs', hmem, -, hcov'⟩ := exists_fixCornersInj hrot πj
    obtain ⟨t, ht, e⟩ := hcov' _ hf
    have hi := (htt (s' t)).1
    have hf' : (pmap hP).face (vDart hL hi) ∈ πj.faces := by rw [← hfc]; exact hmem t ht
    obtain ⟨-, c2, c3⟩ := hcov _ hi hf'
    refine ⟨_, c2, ?_⟩
    rw [hβ _ c2, hfc, ← e, hfc]
    exact (callIn_lab_iff hL hP hS hj hk hd (htt _).1 hi).1 c3
  · obtain ⟨-, c2, c3⟩ := hcov i hi hf
    refine ⟨c2, ?_⟩
    show β (p.cw.mks (p.lab i) - 2) = _
    rw [hβ _ c2, hfc]
    exact (callIn_lab_iff hL hP hS hj hk hd (htt _).1 hi).1 c3

end Call

end BKMNW

end PlanarFlow
