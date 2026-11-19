module

public import PlanarFlow.BKMNW.NrPchC

/-!
# `pchP`, phase D: the cancellation of the flow cycles

* `nr_conf_bnd` (a conformal flow keeps the bound `|g| ≤ Z`);
* **`nrPass_cpass`**: one run of `nrPass` (`NrPass.lean`) on a map with compact face keys
  (`FKey`) and the flow array `Z + g` writes `Z + cpass Mp fr (face (ed 0)) g`;
* **`pchD = pG13a ; pG13b ; nrPass ; pG14 ; negL ; nrPass ; pG14 ; negL`**, **`pchD_exec`**: the
  flow array `FL` of the frame becomes `Z + cancelR Mp fr (face (ed 0)) g`
  (`cancelR g = -(cpass (-(cpass g)))`: a pass, a negation `FL := 2Z - FL`, a pass, a negation),
  within `2 nrPassCost m nf + 14 m + 30` steps; memory changed only in `FL` and in the scratch
  `[A + 19 m, A + 30 m + 1)`; `r9227` := the number of vertices (`r9275`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv NegSSSP
  Monge.FR

section Pass

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']

/-- **A conformal flow keeps the bound `|g| ≤ Z`.** -/
lemma nr_conf_bnd {Mp : CombMap D' V' F'} {g g' : D' → ℤ} (hg : Mp.IsAntisymm g)
    (hg' : Mp.IsAntisymm g') (h : Conf g g') {Z : ℤ} (hZ : ∀ e, -Z ≤ g e ∧ g e ≤ Z) :
    ∀ e, -Z ≤ g' e ∧ g' e ≤ Z := by
  intro e
  by_cases he : 0 ≤ g e
  · obtain ⟨a, b⟩ := h e he; have := hZ e; constructor <;> omega
  · have hr : 0 ≤ g (Mp.rev e) := by rw [hg e]; omega
    obtain ⟨a, b⟩ := h _ hr
    rw [hg' e] at a b; rw [hg e] at b; have := hZ e; constructor <;> omega

variable {P : Input} {W : ℕ}

/-- **One pass of the cancellation on the machine** writes `Z + cpass g`. -/
theorem nrPass_cpass {Mp : CombMap D' V' F'} (hM : Mp.IsPlane) {fr : FRFun F'} (hfr : FRSpec fr)
    {m n : ℕ} {ed : ℕ → D'} {rv key : ℕ → ℕ} {fk : F' → ℕ} (hK : FKey Mp m n ed rv key fk)
    (hcard : Fintype.card D' ≤ m) (c : Config) (hc : WordsBounded W c) {Gb KY NH Z S Inf : ℕ}
    (r0 : c.nreg 9000 = m) (r1 : c.nreg 9001 = n) (r2 : c.nreg 9002 = Gb)
    (r3 : c.nreg 9003 = KY) (r4 : c.nreg 9004 = NH) (r5 : c.nreg 9005 = Z)
    (r6 : c.nreg 9006 = S) (r7 : c.nreg 9007 = key 0) (r8 : c.nreg 9008 = Inf) (hm : 0 < m)
    (hKY : ∀ i < m, c.nmem (KY + i) = key i) (hNH : ∀ i < m, c.nmem (NH + i) = key (rv i))
    {g : D' → ℤ} (hg : Mp.IsAntisymm g) (hZ : ∀ e, -(Z : ℤ) ≤ g e ∧ g e ≤ Z)
    (hG : ∀ i < m, (c.nmem (Gb + i) : ℤ) = Z + g (ed i)) (hInf : m * Z < Inf)
    (dG : NrSep Gb m S (3 * m + 8 * n + 1)) (dK : NrSep KY m S (3 * m + 8 * n + 1))
    (dN : NrSep NH m S (3 * m + 8 * n + 1)) (d1 : NrSep Gb m KY m) (d2 : NrSep Gb m NH m)
    (wS : S + 3 * m + 8 * n + 1 ≤ W) (wG : Gb + m ≤ W) (wK : KY + m ≤ W) (wN : NH + m ≤ W)
    (wI : 2 * Z + Inf ≤ W) (wm : m + 1 ≤ W) (wn : n + 1 ≤ W) :
    ∃ c' t, Exec P W nrPass c c' t ∧ t ≤ nrPassCost m n ∧
      (∀ i < m, (c'.nmem (Gb + i) : ℤ) = Z + cpass Mp fr (Mp.face (ed 0)) g (ed i)) ∧
      (∀ a, (a < S ∨ S + 3 * m + 8 * n + 1 ≤ a) → (a < Gb ∨ Gb + m ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, x < 1500 ∨ (1520 < x ∧ x < 2500) ∨ (2547 < x ∧ x < 9010) ∨ 9024 < x →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (hK.key_lt 0 hm)
  obtain ⟨c', t, ex, ht, p, pn, ps, pInf, parc, pall, pnh, pln, Dv, hD, hG', mfr, rfr, rr, rm, o⟩ :=
    nrPass_exec (P := P) c hc r0 r1 r2 r3 r4 r5 r6 r7 r8 hm hn (hK.key_lt 0 hm)
      (fun i hi => by
        rw [hKY i hi, hNH i hi]; exact ⟨hK.key_lt i hi, hK.key_lt _ (hK.rv i hi).1⟩)
      (fun i hi => by have := hG i hi; have := hZ (ed i); omega) dG dK dN d1 d2 wS wG wK wN wI
      wm wn
  have hA : DkDual p m ed rv key (canLen g) :=
    ⟨fun y hy i h1 h2 => by
        obtain ⟨a, b⟩ := parc y (by rw [← pn]; exact hy) i h1 h2
        exact ⟨a, by rw [← hKY _ a]; exact b⟩,
      fun j hj => by rw [← hKY j hj]; exact pall j hj,
      fun j hj => by rw [pnh j hj, hNH j hj],
      fun j hj => by
        rw [pln j hj]; have := hG j hj; unfold canLen; omega⟩
  have hInf' : ∑ e, canLen g e < p.Inf := by
    rw [pInf]
    have h1 : ∑ e, canLen g e ≤ ∑ _e : D', (Z : ℤ) :=
      sum_le_sum fun e _ => by unfold canLen; have := hZ e; omega
    have h2 : ∑ _e : D', (Z : ℤ) = (Fintype.card D' : ℤ) * Z := by
      rw [sum_const, card_univ, nsmul_eq_mul]
    have h3 : (Fintype.card D' : ℤ) * Z ≤ (m : ℤ) * Z :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    have h4 : ((m * Z : ℕ) : ℤ) < (Inf : ℤ) := by exact_mod_cast hInf
    push_cast at h4
    omega
  have hcb := nr_conf_bnd hg (cpass_antisymm hg) (cpass_conf hM hfr (Mp.face (ed 0)) hg) hZ
  refine ⟨c', t, ex, ht, fun i hi => ?_, mfr, rfr, rr, rm, o⟩
  have e1 := nr_dk_cpass hM hfr hK hA pn ps hm (by rw [pInf]; exact hD) hInf' (ed i)
  rw [← (hK.rv i hi).2, hK.fkey _ (hK.rv i hi).1, hK.fkey i hi] at e1
  rw [hG' i hi, hNH i hi, hKY i hi]
  have := hG i hi
  have := hcb (ed i)
  omega

end Pass

/-- **Phase D of `pchP`**: the cancellation. -/
def pchD : Stmt :=
  .seq pG13a (.seq pG13b (.seq nrPass (.seq pG14 (.seq negL (.seq nrPass (.seq pG14 negL))))))

section Exec

variable {D' V' F' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
  [Fintype F'] [DecidableEq F']

variable {P : Input} {W : ℕ}

/-- **Phase D of `pchP`** (see the module docstring). -/
theorem pchD_exec {Mp : CombMap D' V' F'} (hM : Mp.IsPlane) {fr : FRFun F'} (hfr : FRSpec fr)
    {m nf : ℕ} {ed : ℕ → D'} {rv key : ℕ → ℕ} {fk : F' → ℕ} (hK : FKey Mp m nf ed rv key fk)
    (hcard : Fintype.card D' ≤ m) (c : Config) (hc : WordsBounded W c) {d A BT FR Kd Z : ℕ}
    (R : PchR c d A BT FR Kd m Z) (hm : 0 < m) (hnf : nf ≤ m) (r26 : c.nreg 9226 = nf)
    (hKY : ∀ i < m, c.nmem (A + 9 * m + i) = key i)
    (hNH : ∀ i < m, c.nmem (A + 10 * m + i) = key (rv i))
    {g : D' → ℤ} (hg : Mp.IsAntisymm g) (hZ : ∀ e, -(Z : ℤ) ≤ g e ∧ g e ≤ Z)
    (hG : ∀ i < m, (c.nmem (d + 4 + 6 * m + i) : ℤ) = Z + g (ed i))
    (hA : d + 4 + 7 * m ≤ A) (w : A + 30 * m + 10 ≤ W) (wI : m * Z + 2 * Z + 1 ≤ W) :
    ∃ c' t, Exec P W pchD c c' t ∧ t ≤ 2 * nrPassCost m nf + 14 * m + 30 ∧
      PchR c' d A BT FR Kd m Z ∧ c'.nreg 9227 = c.nreg 9275 ∧
      (∀ i < m, (c'.nmem (d + 4 + 6 * m + i) : ℤ) =
        Z + cancelR Mp fr (Mp.face (ed 0)) g (ed i)) ∧
      (∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ a) → (a < A + 19 * m ∨ A + 30 * m + 1 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- `pG13a ; pG13b`: the registers of `nrPass`
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a01, a02, a03, a04, a05, a06, a07, a27, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    pG13a_exec (P := P) c hc (by rw [R.r16]; clear * - w hA; omega)
  have R₁ := R.congr (fun x h1 h2 => f₁ x (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega))
    (f₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
  rw [R.r04] at a00; rw [r26] at a01; rw [R.r08] at a02; rw [R.r16] at a03; rw [R.r17] at a04
  rw [R.r05] at a05; rw [R.r25] at a06; rw [R.r16, ← Nat.add_zero (A + 9 * m), hKY 0 hm] at a07
  obtain ⟨c₂, t₂, e₂, ht₂, b08, b30, f₂, m₂, rr₂, rm₂, o₂⟩ :=
    pG13b_exec (P := P) c₁ e₁.wb_right (by rw [R₁.r04, R₁.r05]; clear * - wI; omega)
      (by clear * - w hA; omega) (by rw [R₁.r04, R₁.r05]; clear * - wI; omega)
  have R₂ := R₁.congr (fun x h1 h2 => f₂ x (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega)) (f₂ _ (by decide) (by decide))
  rw [R₁.r04, R₁.r05] at b08
  have k₂ : ∀ x, 9000 ≤ x → x ≤ 9007 → c₂.nreg x = c₁.nreg x := fun x h1 h2 =>
    f₂ x (by clear * - h2; omega) (by clear * - h2; omega)
  have hnf0 : 0 < nf := lt_of_le_of_lt (Nat.zero_le _) (hK.key_lt 0 hm)
  have mem₂ : c₂.nmem = c.nmem := by rw [m₂, m₁]
  -- the first pass
  obtain ⟨c₃, t₃, e₃, ht₃, g₃, k₃, f₃, rr₃, rm₃, o₃⟩ := nrPass_cpass (P := P) hM hfr hK hcard c₂
    e₂.wb_right (Gb := d + 4 + 6 * m) (KY := A + 9 * m) (NH := A + 10 * m) (Z := Z)
    (S := A + 19 * m) (Inf := m * Z + 1) (by rw [k₂ _ (by decide) (by decide)]; exact a00)
    (by rw [k₂ _ (by decide) (by decide)]; exact a01) (by rw [k₂ _ (by decide) (by decide)]; exact a02)
    (by rw [k₂ _ (by decide) (by decide)]; exact a03) (by rw [k₂ _ (by decide) (by decide)]; exact a04)
    (by rw [k₂ _ (by decide) (by decide)]; exact a05) (by rw [k₂ _ (by decide) (by decide)]; exact a06)
    (by rw [k₂ _ (by decide) (by decide)]; exact a07) b08 hm
    (fun i hi => by rw [mem₂]; exact hKY i hi) (fun i hi => by rw [mem₂]; exact hNH i hi)
    hg hZ (fun i hi => by rw [mem₂]; exact hG i hi) (by clear * -; omega)
    (Or.inl (by clear * - hA; omega)) (Or.inl (by clear * -; omega)) (Or.inl (by clear * -; omega))
    (Or.inl (by clear * - hA; omega)) (Or.inl (by clear * - hA; omega))
    (by clear * - w hA hnf; omega) (by clear * - w hA hA; omega) (by clear * - w hA; omega)
    (by clear * - w hA; omega) (by clear * - wI; omega) (by clear * - w hA; omega)
    (by clear * - w hA hnf; omega)
  have R₃ := R₂.congr (fun x h1 h2 => f₃ x (by clear * - h1 h2; omega)) (f₃ _ (by decide))
  set g₁ := cpass Mp fr (Mp.face (ed 0)) g with hg₁
  have a₁ : Mp.IsAntisymm g₁ := cpass_antisymm hg
  have b₁ := nr_conf_bnd hg a₁ (cpass_conf hM hfr (Mp.face (ed 0)) hg) hZ
  -- `pG14 ; negL`
  obtain ⟨c₄, t₄, e₄, ht₄, i81, i82, i83, f₄, m₄, rr₄, rm₄, o₄⟩ :=
    pG14_exec (P := P) c₃ e₃.wb_right (by rw [R₃.r05]; clear * - wI; omega)
  have R₄ := R₃.congr (fun x h1 h2 => f₄ x (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)) (f₄ _ (by decide) (by decide)
    (by decide))
  rw [R₃.r04] at i81; rw [R₃.r08] at i82; rw [R₃.r05] at i83
  obtain ⟨c₅, t₅, e₅, ht₅, v₅, k₅, f₅, rr₅, rm₅, o₅⟩ := negL_exec (P := P) c₄ e₄.wb_right
    i81 i82 i83 (by clear * - w hA; omega) (by clear * - w hA; omega)
  have R₅ := R₄.congr (fun x h1 h2 => f₅ x (by clear * - h1 h2; omega)) (f₅ _ (by decide))
  have hG₅ : ∀ i < m, (c₅.nmem (d + 4 + 6 * m + i) : ℤ) = Z + (-g₁) (ed i) := fun i hi => by
    rw [v₅ i hi, m₄]
    have := g₃ i hi; have := b₁ (ed i)
    simp only [Pi.neg_apply]; omega
  have mem₅ : ∀ a, (a < d + 4 + 6 * m ∨ d + 4 + 7 * m ≤ a) → (a < A + 19 * m ∨ A + 30 * m + 1 ≤ a) →
      c₅.nmem a = c.nmem a := fun a h1 h2 => by
    rw [k₅ a (by clear * - h1; omega), m₄,
      k₃ a (by clear * - h2 hnf; omega) (by clear * - h1; omega), mem₂]
  clear v₅ k₅ i81 i82 i83
  -- the second pass
  have hn₁ : Mp.IsAntisymm (-g₁) := fun e => by simp only [Pi.neg_apply, a₁ e]
  have hb₁ : ∀ e, -(Z : ℤ) ≤ (-g₁) e ∧ (-g₁) e ≤ Z := fun e => by
    have := b₁ e; simp only [Pi.neg_apply]; omega
  have k₅' : ∀ x, 9000 ≤ x → x ≤ 9008 → c₅.nreg x = c₂.nreg x := fun x h1 h2 => by
    rw [f₅ x (by clear * - h2; omega), f₄ x (by clear * - h2; omega) (by clear * - h2; omega)
      (by clear * - h2; omega), f₃ x (by clear * - h1 h2; omega)]
  have mKY : ∀ i < m, c₅.nmem (A + 9 * m + i) = key i := fun i hi => by
    rw [mem₅ _ (by clear * - hA; omega) (by clear * - hi; omega)]; exact hKY i hi
  have mNH : ∀ i < m, c₅.nmem (A + 10 * m + i) = key (rv i) := fun i hi => by
    rw [mem₅ _ (by clear * - hA; omega) (by clear * - hi; omega)]; exact hNH i hi
  obtain ⟨c₆, t₆, e₆, ht₆, g₆, k₆, f₆, rr₆, rm₆, o₆⟩ := nrPass_cpass (P := P) hM hfr hK hcard c₅
    e₅.wb_right (Gb := d + 4 + 6 * m) (KY := A + 9 * m) (NH := A + 10 * m) (Z := Z)
    (S := A + 19 * m) (Inf := m * Z + 1)
    (by rw [k₅' _ (by decide) (by decide), k₂ _ (by decide) (by decide)]; exact a00)
    (by rw [k₅' _ (by decide) (by decide), k₂ _ (by decide) (by decide)]; exact a01)
    (by rw [k₅' _ (by decide) (by decide), k₂ _ (by decide) (by decide)]; exact a02)
    (by rw [k₅' _ (by decide) (by decide), k₂ _ (by decide) (by decide)]; exact a03)
    (by rw [k₅' _ (by decide) (by decide), k₂ _ (by decide) (by decide)]; exact a04)
    (by rw [k₅' _ (by decide) (by decide), k₂ _ (by decide) (by decide)]; exact a05)
    (by rw [k₅' _ (by decide) (by decide), k₂ _ (by decide) (by decide)]; exact a06)
    (by rw [k₅' _ (by decide) (by decide), k₂ _ (by decide) (by decide)]; exact a07)
    (by rw [k₅' _ (by decide) (by decide)]; exact b08) hm mKY mNH
    hn₁ hb₁ hG₅ (by clear * -; omega)
    (Or.inl (by clear * - hA; omega)) (Or.inl (by clear * -; omega)) (Or.inl (by clear * -; omega))
    (Or.inl (by clear * - hA; omega)) (Or.inl (by clear * - hA; omega))
    (by clear * - w hA hnf; omega) (by clear * - w hA hA; omega) (by clear * - w hA; omega)
    (by clear * - w hA; omega) (by clear * - wI; omega) (by clear * - w hA; omega)
    (by clear * - w hA hnf; omega)
  have R₆ := R₅.congr (fun x h1 h2 => f₆ x (by clear * - h1 h2; omega)) (f₆ _ (by decide))
  set g₂ := cpass Mp fr (Mp.face (ed 0)) (-g₁) with hg₂
  have a₂ : Mp.IsAntisymm g₂ := cpass_antisymm hn₁
  have b₂ := nr_conf_bnd hn₁ a₂ (cpass_conf hM hfr (Mp.face (ed 0)) hn₁) hb₁
  -- `pG14 ; negL`
  obtain ⟨c₇, t₇, e₇, ht₇, j81, j82, j83, f₇, m₇, rr₇, rm₇, o₇⟩ :=
    pG14_exec (P := P) c₆ e₆.wb_right (by rw [R₆.r05]; clear * - wI; omega)
  have R₇ := R₆.congr (fun x h1 h2 => f₇ x (by clear * - h1 h2; omega)
    (by clear * - h1 h2; omega) (by clear * - h1 h2; omega)) (f₇ _ (by decide) (by decide)
    (by decide))
  rw [R₆.r04] at j81; rw [R₆.r08] at j82; rw [R₆.r05] at j83
  obtain ⟨c₈, t₈, e₈, ht₈, v₈, k₈, f₈, rr₈, rm₈, o₈⟩ := negL_exec (P := P) c₇ e₇.wb_right
    j81 j82 j83 (by clear * - w hA; omega) (by clear * - w hA; omega)
  have R₈ := R₇.congr (fun x h1 h2 => f₈ x (by clear * - h1 h2; omega)) (f₈ _ (by decide))
  refine ⟨c₈, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (t₇ + t₈)))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ e₈)))))),
    by clear * - ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇ ht₈; omega, R₈, ?_, fun i hi => ?_,
    fun a h1 h2 => ?_, by rw [rr₈, rr₇, rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁], by rw [o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [f₈ _ (by decide), f₇ _ (by decide) (by decide) (by decide), f₆ _ (by decide),
      f₅ _ (by decide), f₄ _ (by decide) (by decide) (by decide), f₃ _ (by decide),
      f₂ _ (by decide) (by decide)]
    exact a27
  · rw [v₈ i hi, m₇]
    have := g₆ i hi; have := b₂ (ed i)
    show _ = (Z : ℤ) + (-(g₂)) (ed i)
    simp only [Pi.neg_apply]; omega
  · rw [k₈ a (by clear * - h1; omega), m₇,
      k₆ a (by clear * - h2 hnf; omega) (by clear * - h1; omega), mem₅ a h1 h2]

end Exec

end BKMNW

end PlanarFlow
