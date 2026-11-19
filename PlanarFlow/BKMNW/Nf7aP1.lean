module

public import PlanarFlow.BKMNW.Nf7aPro
public import PlanarFlow.BKMNW.GatherProg
public import PlanarFlow.BKMNW.MbRun

/-!
# The prologue of `fixP`, part 1: bases, face walk, face labels, vertex labels

**`proP1`** `= pinA ; pinB ; pinC ; mzFill ; gaProg ; olProg ; dvP`: the registers of the layout,
`[FL, FL + 3m + 1)` zeroed, `NX[i] = SG[RV[i]]`, `FL[i] = olab NX i + 1` (face labels),
`dvP` at `DVA` (vertex labels, net outflows, counts). **`proP1_exec`** (`≤ 120 m + 140`
steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs OrbLab MfDrv

/-- **The prologue, part 1.** -/
def proP1 : Stmt :=
  .seq pinA (.seq pinB (.seq pinC (.seq mzFill (.seq gaProg (.seq olProg dvP)))))

/-- The scratch registers of part 1. -/
def scr1 (r : ℕ) : Prop :=
  r = 9371 ∨ (9374 ≤ r ∧ r ≤ 9377) ∨ (9400 ≤ r ∧ r ≤ 9438) ∨ (5030 ≤ r ∧ r ≤ 5035) ∨
    (4470 ≤ r ∧ r ≤ 4477) ∨ (7350 ≤ r ∧ r ≤ 7352) ∨ (7400 ≤ r ∧ r ≤ 7405) ∨
    (8430 ≤ r ∧ r ≤ 8447)

variable {P : Input} {W : ℕ}

/-- The iterates of two functions agreeing on `[0, m)`, from `i < m`, while one maps `[0, m)`
into itself. -/
lemma iter_congr_on {f g : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, f i = g i) (hf : ∀ i < m, f i < m) :
    ∀ t i, i < m → f^[t] i = g^[t] i
  | 0, i, _ => rfl
  | t + 1, i, hi => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← h i hi]
    exact iter_congr_on h hf t _ (hf i hi)

/-- `olab` depends only on the values on `[0, m)` for a permutation of `[0, m)`. -/
lemma olab_congr {f g : ℕ → ℕ} {m : ℕ} (h : ∀ i < m, f i = g i) (hf : PermOn f m) {i : ℕ}
    (hi : i < m) : olab f i = olab g i := by
  have hg : ∀ i < m, g i < m := fun i hi => h i hi ▸ hf.lt i hi
  obtain ⟨t, ht⟩ := olab_mem f i
  obtain ⟨u, hu⟩ := olab_mem g i
  have e1 := olab_min g i t
  have e2 := olab_min f i u
  rw [← iter_congr_on h hf.lt t i hi, ht] at e1
  rw [iter_congr_on h hf.lt u i hi, hu] at e2
  omega

lemma dvS_congr {lab lab' fl fl' : ℕ → ℕ} {i : ℕ} (v : ℕ) (h1 : ∀ j < i, lab j = lab' j)
    (h2 : ∀ j < i, fl j = fl' j) : dvS lab fl i v = dvS lab' fl' i v := by
  unfold dvS
  rw [Finset.filter_congr (fun j hj => by rw [h1 j (Finset.mem_range.1 hj)])]
  exact Finset.sum_congr rfl fun j hj => h2 j (Finset.mem_range.1 (Finset.mem_filter.1 hj).1)

lemma dvC_congr {lab lab' : ℕ → ℕ} {i : ℕ} (v : ℕ) (h1 : ∀ j < i, lab j = lab' j) :
    dvC lab i v = dvC lab' i v := by
  unfold dvC
  rw [Finset.filter_congr (fun j hj => by rw [h1 j (Finset.mem_range.1 hj)])]

/-- **The registers of the layout** after the register blocks. -/
def RegP1 (p : FpIn) (A0 : ℕ) (c : Config) : Prop :=
  c.nreg 9400 = p.m ∧ c.nreg 9403 = A0 ∧ c.nreg 9436 = 1 ∧ c.nreg 9421 = p.Z ∧
    c.nreg 9401 = p.k ∧ c.nreg 9371 = p.k ∧ c.nreg 9402 = p.PDb ∧
    c.nreg 9430 = p.d + 4 + p.m ∧ c.nreg 9431 = p.d + 4 + p.m + p.m ∧
    c.nreg 9434 = p.d + 4 + p.m + p.m + p.m ∧
    c.nreg 9435 = p.d + 4 + p.m + p.m + p.m + p.m + p.m + p.m ∧
    c.nreg 9404 = A0 ∧ c.nreg 9405 = A0 + p.m ∧ c.nreg 9406 = A0 + p.m + p.m ∧
    c.nreg 9407 = A0 + p.m + p.m + p.m ∧ c.nreg 9408 = A0 + p.m + p.m + p.m + p.m + 1 ∧
    c.nreg 9409 = A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m ∧
    c.nreg 9410 = A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m + p.m ∧
    c.nreg 9411 = p.Qb A0 ∧ c.nreg 9374 = p.Qb A0 ∧ c.nreg 9375 = p.Qb A0 + p.k ∧
    c.nreg 9376 = p.Qb A0 + p.k + p.k ∧ c.nreg 9377 = p.Qb A0 + p.k + p.k + p.k ∧
    c.nreg 9412 = p.Qb A0 + p.k + p.k + p.k + p.k + p.k ∧
    c.nreg 9413 = p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k ∧
    c.nreg 9414 = p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k ∧
    c.nreg 9415 = p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k ∧
    c.nreg 9416 = p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k ∧
    c.nreg 9417 = p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k +
      p.k + p.k ∧
    c.nreg 9418 = p.Qb A0 + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k + p.k +
      p.k + p.k + p.k + p.k

/-- `RegP1` depends only on the registers of the layout. -/
lemma RegP1.congr {p : FpIn} {A0 : ℕ} {c c' : Config} (h : RegP1 p A0 c)
    (hr : ∀ r, (r = 9371 ∨ (9374 ≤ r ∧ r ≤ 9377) ∨ (9400 ≤ r ∧ r ≤ 9438)) → r ≠ 9419 →
      r ≠ 9420 → r ≠ 9422 → c'.nreg r = c.nreg r) : RegP1 p A0 c' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [hr _ (by omega) (by omega) (by omega) (by omega)]; assumption)

/-- The register blocks of part 1. -/
def proP1a : Stmt := .seq pinA (.seq pinB pinC)

set_option maxHeartbeats 1600000 in
theorem proP1a_exec (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 j : ℕ}
    (r04 : c.nreg 3004 = p.d) (r06 : c.nreg 3006 = A0) (r07 : c.nreg 6807 = p.Gb)
    (r00 : c.nreg 6800 = j)
    (hm : c.nmem p.d = p.m) (hZ : c.nmem (p.d + 3) = p.Z) (hns : c.nmem p.Gb = p.ns)
    (hoff : c.nmem (p.Gb + 1 + j) = p.off) (hk : c.nmem (p.Gb + 1 + j + p.ns) = p.k)
    (hW1 : A0 + 9 * p.m + 15 * p.k + 1 + p.d + p.Gb + j + p.ns + p.ns + p.off + 8 ≤ W) :
    ∃ c' t, Exec P W proP1a c c' t ∧ t = 63 ∧ RegP1 p A0 c' ∧
      c'.nreg 5030 = 3 * p.m + 1 ∧ c'.nreg 5031 = A0 + p.m ∧ c'.nreg 4470 = p.m ∧
      c'.nreg 4471 = p.d + 4 + p.m ∧ c'.nreg 4472 = p.d + 4 + p.m + p.m ∧ c'.nreg 4473 = A0 ∧
      c'.nreg 7350 = A0 ∧ c'.nreg 7351 = A0 + p.m ∧ c'.nreg 7352 = p.m ∧
      c'.nreg 8430 = A0 + p.m + p.m + p.m + p.m + 1 ∧
      (∀ r, ¬ scr1 r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a03, a36, a21, a01, a71, a02, a30, a31, a34, a35, ak, am, ar,
      arm, ao⟩ := pinA_exec (P := P) c hc r04 r06 r07 r00 hm hZ hns hoff hk (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, b04, b05, b06, b07, b08, b09, b10, b11, b74, b75, b76, b77, b12, b13,
      b14, b15, b16, b17, b18, bk, bm, br, brm, bo⟩ :=
    pinB_exec (P := P) c₁ e₁.wb_right a03 a00 a01 a36 (by omega)
  have q2 : ∀ r, (r < 9374 ∨ 9377 < r) → (r < 9404 ∨ 9418 < r) → c₂.nreg r = c₁.nreg r := bk
  obtain ⟨c₃, t₃, e₃, ht₃, d5030, d5031, d4470, d4471, d4472, d4473, d7350, d7351, d7352, d8430,
      dk, dm, dr, drm, do'⟩ :=
    pinC_exec (P := P) c₂ e₂.wb_right (m := p.m) (by rw [q2 _ (by omega) (by omega), a00])
      (by rw [q2 _ (by omega) (by omega), a36]) (by omega)
  have q3 : ∀ r, (r = 9371 ∨ (9374 ≤ r ∧ r ≤ 9377) ∨ (9400 ≤ r ∧ r ≤ 9438)) →
      c₃.nreg r = c₂.nreg r := fun r hr => dk r (by omega) (by omega) (by omega) (by omega)
        (by omega)
  have R2 : RegP1 p A0 c₂ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first | assumption | (rw [q2 _ (by omega) (by omega)]; assumption)
  refine ⟨c₃, _, e₁.seq (e₂.seq e₃), by omega, R2.congr fun r hr _ _ _ => q3 r hr, d5030, by rw [d5031, b05], d4470,
    by rw [d4471, q2 _ (by omega) (by omega), a30], by rw [d4472, q2 _ (by omega) (by omega), a31],
    by rw [d4473, b04], by rw [d7350, b04], by rw [d7351, b05], d7352, by rw [d8430, b08],
    fun r hr => ?_, by rw [dm, bm, am], by rw [dr, br, ar], by rw [drm, brm, arm],
    by rw [do', bo, ao]⟩
  simp only [scr1] at hr
  rw [dk r (by omega) (by omega) (by omega) (by omega) (by omega), q2 r (by omega) (by omega),
    ak r (by omega) (by omega)]

/-- The memory phases of part 1. -/
def proP1b : Stmt := .seq mzFill (.seq gaProg (.seq olProg dvP))

set_option maxHeartbeats 1600000 in
theorem proP1b_exec (p : FpIn) (c : Config) (hc : WordsBounded W c) {A0 : ℕ}
    (r04 : c.nreg 3004 = p.d) (r5030 : c.nreg 5030 = 3 * p.m + 1) (r5031 : c.nreg 5031 = A0 + p.m)
    (r4470 : c.nreg 4470 = p.m) (r4471 : c.nreg 4471 = p.d + 4 + p.m)
    (r4472 : c.nreg 4472 = p.d + 4 + p.m + p.m) (r4473 : c.nreg 4473 = A0)
    (r7350 : c.nreg 7350 = A0) (r7351 : c.nreg 7351 = A0 + p.m) (r7352 : c.nreg 7352 = p.m)
    (r8430 : c.nreg 8430 = A0 + p.m + p.m + p.m + p.m + 1)
    (hlo : ∀ a < A0, c.nmem a = p.mem a) (hm : p.mem p.d = p.m)
    (hRV : ∀ i < p.m, p.RV i < p.m) (hSG : PermOn (sgF p.d p.m p.mem) p.m)
    (hNX : PermOn (nxF p.d p.m p.mem) p.m) (hfr : p.d + 4 + 7 * p.m ≤ A0)
    (hW1 : A0 + 9 * p.m + 2 ≤ W) (hW2 : ∑ i ∈ range p.m, p.FLW i + 6 ≤ W) :
    ∃ c' t, Exec P W proP1b c c' t ∧ t ≤ 120 * p.m + 60 ∧
      (∀ a < A0, c'.nmem a = p.mem a) ∧
      (∀ i < p.m, c'.nmem (A0 + i) = nxF p.d p.m p.mem i) ∧
      (∀ i < p.m, c'.nmem (A0 + p.m + i) = p.lab i) ∧
      (∀ i < p.m, c'.nmem (A0 + p.m + p.m + i) = 0) ∧
      (∀ a ≤ p.m, c'.nmem (A0 + p.m + p.m + p.m + a) = 0) ∧
      (∀ i < p.m, c'.nmem (A0 + p.m + p.m + p.m + p.m + 1 + i) = p.vl i + 1) ∧
      (∀ v < p.m, c'.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + v) = dvS p.vl p.FLW p.m v ∧
        c'.nmem (A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + v) = dvC p.vl p.m v) ∧
      (∀ a, A0 + p.m + p.m + p.m + p.m + 1 + p.m + p.m + p.m ≤ a → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 4474 ∨ 4477 < r) → (r < 5032 ∨ 5035 < r) → (r < 7350 ∨ 7352 < r) →
        (r < 7400 ∨ 7405 < r) → (r < 8431 ∨ 8447 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  -- mzFill
  obtain ⟨c₄, t₄, e₄, ht₄, z₄, k₄, n₄, rr₄, rm₄, o₄⟩ :=
    mzFill_exec (P := P) c hc (len := 3 * p.m + 1) (Zb := A0 + p.m) r5030 r5031 (by omega)
      (by omega)
  have lo4 : ∀ a < A0, c₄.nmem a = p.mem a := fun a ha => by rw [k₄ _ (Or.inl (by omega)), hlo a ha]
  -- gaProg
  obtain ⟨c₅, t₅, e₅, ht₅, g₅, k₅, n₅, rr₅, rm₅, o₅⟩ :=
    gaProg_exec (P := P) c₄ e₄.wb_right (m := p.m) (IXb := p.d + 4 + p.m)
      (Ab := p.d + 4 + p.m + p.m) (OUTb := A0)
      (by rw [n₄ _ (by omega), r4470]) (by rw [n₄ _ (by omega), r4471])
      (by rw [n₄ _ (by omega), r4472]) (by rw [n₄ _ (by omega), r4473]) (by omega) (by omega)
      (by omega)
      (fun j hj => by
        rw [lo4 _ (by omega)]
        have := hRV j hj; simp only [FpIn.RV] at this; omega)
      (fun j hj => by omega)
      (fun j hj => by
        rw [lo4 _ (by omega)]
        have := hRV j hj; simp only [FpIn.RV] at this; omega)
  have lo5 : ∀ a < A0, c₅.nmem a = p.mem a := fun a ha => by
    rw [k₅ _ (fun h => by omega)]; exact lo4 a ha
  have e2m : p.d + 4 + p.m + p.m = p.d + 4 + 2 * p.m := by ring
  have hNX5 : ∀ i < p.m, c₅.nmem (A0 + i) = nxF p.d p.m p.mem i := fun i hi => by
    have := hRV i hi; simp only [FpIn.RV] at this
    rw [g₅ i hi, lo4 (p.d + 4 + p.m + i) (by omega)]
    rw [lo4 _ (by omega)]
    simp only [nxF, e2m]
  -- olProg
  have n5 : ∀ r, (r < 4474 ∨ 4477 < r) → (r < 5032 ∨ 5035 < r) → c₅.nreg r = c.nreg r :=
    fun r h1 h2 => by rw [n₅ r h1, n₄ r h2]
  obtain ⟨c₆, t₆, e₆, ht₆, l₆, k₆, n₆, rr₆, rm₆, o₆⟩ :=
    olProg_exec (P := P) (W := W) hNX (Pb := A0) (Lb := A0 + p.m) (by omega) (by omega)
      (by omega) c₅ e₅.wb_right (by rw [n5 _ (by omega) (by omega), r7350])
      (by rw [n5 _ (by omega) (by omega), r7351])
      (by rw [n5 _ (by omega) (by omega), r7352]) hNX5
      (fun x hx => by rw [k₅ _ (fun h => by omega)]; exact z₄ x (by omega))
  have lo6 : ∀ a < A0, c₆.nmem a = p.mem a := fun a ha => by
    rw [k₆ _ (Or.inl (by omega))]; exact lo5 a ha
  -- dvP
  have n6 : ∀ r, (r < 7400 ∨ 7405 < r) → (r < 4474 ∨ 4477 < r) → (r < 5032 ∨ 5035 < r) →
      c₆.nreg r = c.nreg r := fun r h1 h2 h3 => by rw [n₆ r h1, n5 r h2 h3]
  have hsg6 : ∀ i < p.m, sgF p.d p.m c₆.nmem i = sgF p.d p.m p.mem i := fun i hi => by
    simp only [sgF]; exact lo6 _ (by omega)
  have hSG6 : PermOn (sgF p.d p.m c₆.nmem) p.m :=
    ⟨fun i hi => by rw [hsg6 i hi]; exact hSG.lt i hi,
      fun i hi j hj e => hSG.inj i hi j hj (by rw [← hsg6 i hi, ← hsg6 j hj]; exact e)⟩
  have hfl6 : ∀ j < p.m, c₆.nmem (p.d + 6 * p.m + 4 + j) = p.FLW j := fun j hj => by
    rw [lo6 _ (by omega)]; simp only [FpIn.FLW]; congr 1; ring
  have hsum6 : ∑ j ∈ range p.m, c₆.nmem (p.d + 6 * p.m + 4 + j) = ∑ j ∈ range p.m, p.FLW j :=
    Finset.sum_congr rfl fun j hj => hfl6 j (Finset.mem_range.1 hj)
  obtain ⟨c₇, t₇, e₇, ht₇, v₇, w₇, k₇, n₇, rr₇, rm₇, o₇⟩ :=
    dvP_exec (P := P) c₆ e₆.wb_right (d := p.d) (A := A0 + p.m + p.m + p.m + p.m + 1) (m := p.m)
      (by rw [n6 _ (by omega) (by omega) (by omega), r04])
      (by rw [n6 _ (by omega) (by omega) (by omega), r8430])
      (by rw [lo6 _ (by omega)]; exact hm) hSG6 (by omega) (by omega) (by omega)
      (by rw [hsum6]; omega)
  have hvl : ∀ i < p.m, olab (sgF p.d p.m c₆.nmem) i = p.vl i := fun i hi =>
    olab_congr hsg6 hSG6 hi
  refine ⟨c₇, _, e₄.seq (e₅.seq (e₆.seq e₇)), by omega, fun a ha => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun a ha => ?_, fun i hi => ?_, fun v hv => ?_,
    fun a ha => ?_, fun r h1 h2 h3 h4 h5 => ?_, rr₇.trans (rr₆.trans (rr₅.trans rr₄)),
    rm₇.trans (rm₆.trans (rm₅.trans rm₄)), o₇.trans (o₆.trans (o₅.trans o₄))⟩
  · rw [k₇ _ (Or.inl (by omega))]; exact lo6 a ha
  · rw [k₇ _ (Or.inl (by omega)), k₆ _ (Or.inl (by omega))]; exact hNX5 i hi
  · rw [k₇ _ (Or.inl (by omega)), l₆ i hi]; rfl
  · rw [k₇ _ (Or.inl (by omega)), k₆ _ (Or.inr (by omega)), k₅ _ (fun h => by omega)]
    have := z₄ (p.m + i) (by omega); rw [← this]; congr 1; omega
  · rw [k₇ _ (Or.inl (by omega)), k₆ _ (Or.inr (by omega)), k₅ _ (fun h => by omega)]
    have := z₄ (p.m + p.m + a) (by omega); rw [← this]; congr 1; omega
  · rw [v₇ i hi, hvl i hi]
  · obtain ⟨w1, w2⟩ := w₇ v hv
    exact ⟨by rw [w1]; exact dvS_congr v (fun j hj => hvl j hj) (fun j hj => hfl6 j hj),
      by rw [w2]; exact dvC_congr v (fun j hj => hvl j hj)⟩
  · rw [k₇ _ (Or.inr (by omega)), k₆ _ (Or.inr (by omega)), k₅ _ (fun h => by omega),
      k₄ _ (Or.inr (by omega))]
  · rw [n₇ r h3 h4 h5, n6 r h4 h1 h2]

end BKMNW

end PlanarFlow
