module

public import PlanarFlow.BKMNW.SepX
public import PlanarFlow.BKMNW.LevelProg

/-!
# The copy phase of the extended split: the children's records into their frames

After the front of the split (`spFront sepP`, the separator program writing the children's
records from `Xb = r6501`) and the two child frames written by `sfChild` (the left at `h + 5`,
ending at `el = r6553`, the right at `el + 5` with `mr` darts), **`spRec`**:

* stores the left child's pointer `mem el := Xb + 2` (its record stays where the separator
  program wrote it: the left child's frame becomes `[h + 5, Yb - 5)`, `Yb = Xb + 2 + zl + zr + 5`);
* copies the right child's frame (`4 + 6 mr` cells) from `el + 5` to `Yb`, stores its pointer
  `mem (Yb + 4 + 7 mr) := Yb + 5 + 7 mr` and copies its record (`zr` cells) there;
* `r2998 := Yb - 5`, `r2999 := Yb + 5 + 7 mr + zr` (the ends of the two child frames).

Lemmas: `Lay.shift`, `RArr.shift`, `LayR.shift`, `RecAt.shift` (a frame / a record copied to
another place is a frame / a record there), the blocks `spRX1`, `spRX2`, `spRX3`, **`spRec_exec`**
(`42 mr + 7 zr + 70` steps). Registers `5450 … 5472` and those of `cpArr` (`4910 … 4916`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace MfDrv

open Finset Function Equiv Orbit WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  NegSSSP.Driver

universe w

variable {D : Type w} {V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ} {ds : DSys M}

/-! ### Frames and records copied elsewhere -/

/-- **A frame copied to `d'` is a frame there.** -/
lemma Lay.shift {x : MCall M} {m : ℕ} {en : ℕ → D} {d d' : ℕ} {mem mem' : ℕ → ℕ}
    (h : Lay M gid u S T Z x m en d mem) (he : ∀ a < 4 + 6 * m, mem' (d' + a) = mem (d + a)) :
    Lay M gid u S T Z x m en d' mem' := by
  have E : ∀ a b b', a < 4 + 6 * m → b = d + a → b' = d' + a → mem' b' = mem b := by
    intro a b b' ha hb hb'; subst hb hb'; exact he a ha
  exact {
    hm := by rw [E 0 d d' (by omega) rfl rfl]; exact h.hm
    hk := by rw [E 1 (d + 1) (d' + 1) (by omega) rfl rfl]; exact h.hk
    tag := by rw [E 2 (d + 2) (d' + 2) (by omega) rfl rfl]; exact h.tag
    hz := by rw [E 3 (d + 3) (d' + 3) (by omega) rfl rfl]; exact h.hz
    en_mem := h.en_mem
    en_surj := h.en_surj
    en_mono := h.en_mono
    gd := fun i hi => by rw [E (4 + i) (d + 4 + i) _ (by omega) (by omega) (by omega)]; exact h.gd i hi
    rv := fun i hi => by
      rw [E (4 + m + i) (d + 4 + m + i) _ (by omega) (by omega) (by omega)]; exact h.rv i hi
    sg := fun i hi => by
      rw [E (4 + 2 * m + i) (d + 4 + 2 * m + i) _ (by omega) (by omega) (by omega)]
      exact h.sg i hi
    cp := fun i hi => by
      rw [E (4 + 3 * m + i) (d + 4 + 3 * m + i) _ (by omega) (by omega) (by omega)]
      exact h.cp i hi
    kr := fun i hi => by
      rw [E (4 + 4 * m + i) (d + 4 + 4 * m + i) _ (by omega) (by omega) (by omega)]
      exact h.kr i hi
    hl := fun i hi => by
      rw [E (4 + 5 * m + i) (d + 4 + 5 * m + i) _ (by omega) (by omega) (by omega)]
      exact h.hl i hi }

/-- **The arrays of a record copied to `R'`.** -/
lemma RArr.shift {x : MCall M} {m n R R' : ℕ} {g : ℕ → D} {mem mem' : ℕ → ℕ}
    (h : RArr M gid ν S T x m n R g mem)
    (he : ∀ a < 3 + 6 * n + m, mem' (R' + a) = mem (R + a)) :
    RArr M gid ν S T x m n R' g mem' := by
  have E : ∀ a b b', a < 3 + 6 * n + m → b = R + a → b' = R' + a → mem' b' = mem b := by
    intro a b b' ha hb hb'; subst hb hb'; exact he a ha
  have F : ∀ i < m, mem' (R' + 3 + 6 * n + i) = mem (R + 3 + 6 * n + i) := fun i hi =>
    E (3 + 6 * n + i) _ _ (by omega) (by omega) (by omega)
  exact {
    g_mem := h.g_mem
    g_surj := h.g_surj
    g_mono := h.g_mono
    gp := fun i hi => by rw [E (3 + i) (R + 3 + i) _ (by omega) (by omega) (by omega)]; exact h.gp i hi
    rp := fun i hi => by
      rw [E (3 + n + i) (R + 3 + n + i) _ (by omega) (by omega) (by omega)]; exact h.rp i hi
    hp := fun i hi => by
      rw [E (3 + 2 * n + i) (R + 3 + 2 * n + i) _ (by omega) (by omega) (by omega)]
      exact h.hp i hi
    kp := fun i hi => by
      rw [E (3 + 3 * n + i) (R + 3 + 3 * n + i) _ (by omega) (by omega) (by omega)]
      exact h.kp i hi
    vp := fun i hi => by
      rw [E (3 + 4 * n + i) (R + 3 + 4 * n + i) _ (by omega) (by omega) (by omega)]
      exact h.vp i hi
    fx := fun i hi => by rw [F i hi]; exact h.fx i hi
    fx_mem := fun i hi => by rw [F i hi]; exact h.fx_mem i hi
    fx_surj := fun y hy => by
      obtain ⟨i, hi, e⟩ := h.fx_surj y hy
      exact ⟨i, hi, by rw [F i hi]; exact e⟩
    fx_mono := fun i j hij hj => by rw [F i (by omega), F j hj]; exact h.fx_mono i j hij hj }

/-- **A record copied to `R'` is a record there.** -/
lemma LayR.shift {x : MCall M} {m n R R' : ℕ} {g : ℕ → D} {mem mem' : ℕ → ℕ}
    (h : LayR M ds gid ν S T x m n R g mem)
    (he : ∀ a < rszL (mem (R + 1)) n m, mem' (R' + a) = mem (R + a)) :
    LayR M ds gid ν S T x m n R' g mem' := by
  have h3 := three_le_rszL (mem (R + 1)) n m
  have e0 : mem' R' = mem R := by have := he 0 (by omega); simpa using this
  have e1 : mem' (R' + 1) = mem (R + 1) := he 1 (by omega)
  have e2 : mem' (R' + 2) = mem (R + 2) := he 2 (by omega)
  have hsz : mem (R + 1) < 2 → rszL (mem (R + 1)) n m = 3 + 6 * n + m := fun hp => by
    unfold rszL; rw [iteT hp]
  refine ⟨by rw [e0]; exact h.hn, by rw [e1]; exact h.hph, by rw [e2]; exact h.hb, ?_,
    fun hp => ?_⟩
  · have hph := h.ph
    rw [e1, e2]
    rcases hph with ⟨h0, st, hx, hs⟩ | h1 | h2
    · refine Or.inl ⟨h0, st, hx, fun i hi hg => ?_⟩
      have hsz' := hsz (by omega)
      have := he (3 + 5 * n + i) (by omega)
      rw [show R' + 3 + 5 * n + i = R' + (3 + 5 * n + i) by omega, this,
        show R + (3 + 5 * n + i) = R + 3 + 5 * n + i by omega]
      exact hs i hi hg
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h2)
  · rw [e1] at hp
    exact (h.arr hp).shift fun a ha => he a (by rw [hsz hp]; exact ha)

/-- **A record copied to `R'` is a record there** (`RecAt`). -/
lemma RecAt.shift {x : MCall M} {R R' z : ℕ} {mem mem' : ℕ → ℕ}
    (h : RecAt M ds gid ν S T x R z mem) (he : ∀ a < z, mem' (R' + a) = mem (R + a)) :
    RecAt M ds gid ν S T x R' z mem' := by
  obtain ⟨hz, n, g, hzn, hR⟩ := h
  have h3 := three_le_rszL (mem (R + 1)) n (pdarts M x.1.piece x.2.1).card
  have e1 : mem' (R' + 1) = mem (R + 1) := he 1 (by omega)
  exact ⟨hz, n, g, by rw [e1]; exact hzn, hR.shift fun a ha => he a (by omega)⟩

/-! ### The program -/

/-- The left pointer, the addresses, and the registers of the first copy. -/
def spRX1 : Stmt := block [.copyN 5450 6501, .loadN 5451 5450, .constN 5452 1,
  .addN 5453 5450 5452, .loadN 5454 5453, .constN 5455 2, .addN 5456 5450 5455,
  .storeN 6553 5456, .addN 5457 5456 5451, .addN 5458 5457 5454, .constN 5459 5,
  .addN 5460 5458 5459, .addN 5461 6553 5459, .loadN 5462 5461, .constN 5463 6,
  .mulN 5464 5463 5462, .constN 5465 4, .addN 5466 5464 5465,
  .copyN 4910 5466, .copyN 4911 5461, .copyN 4912 5460]

/-- The right pointer, and the registers of the second copy. -/
def spRX2 : Stmt := block [.constN 5467 7, .mulN 5468 5467 5462, .addN 5469 5460 5465,
  .addN 5470 5469 5468, .addN 5471 5470 5452, .storeN 5470 5471,
  .copyN 4910 5454, .copyN 4911 5457, .copyN 4912 5471]

/-- The ends of the child frames. -/
def spRX3 : Stmt := block [.addN 5472 5471 5454, .subN 2998 5460 5459, .copyN 2999 5472]

/-- **The copy phase of the extended split** (see the module docstring). -/
def spRec : Stmt := .seq spRX1 (.seq cpArr (.seq spRX2 (.seq cpArr spRX3)))

section Exec

variable {I : Input} {W : ℕ}

theorem spRX1_exec (c : Config) (hc : WordsBounded W c) {Xb el zl zr mr : ℕ}
    (r01 : c.nreg 6501 = Xb) (r53 : c.nreg 6553 = el) (h0 : c.nmem Xb = zl)
    (h1 : c.nmem (Xb + 1) = zr) (h5 : c.nmem (el + 5) = mr) (hel : el + 5 ≠ Xb ∧ el + 5 ≠ Xb + 1)
    (hel' : el ≠ Xb ∧ el ≠ Xb + 1)
    (w : Xb + 2 + zl + zr + 5 + 6 * mr + 4 ≤ W) (w' : el + 5 ≤ W) :
    ∃ c' t, Exec I W spRX1 c c' t ∧ t = 21 ∧ c'.nreg 5451 = zl ∧ c'.nreg 5452 = 1 ∧
      c'.nreg 5454 = zr ∧ c'.nreg 5457 = Xb + 2 + zl ∧ c'.nreg 5459 = 5 ∧
      c'.nreg 5460 = Xb + 2 + zl + zr + 5 ∧ c'.nreg 5462 = mr ∧ c'.nreg 5465 = 4 ∧
      c'.nreg 4910 = 6 * mr + 4 ∧ c'.nreg 4911 = el + 5 ∧
      c'.nreg 4912 = Xb + 2 + zl + zr + 5 ∧
      c'.nmem = upd c.nmem el (Xb + 2) ∧
      (∀ x, (x < 4910 ∨ (4912 < x ∧ x < 5450) ∨ 5466 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hXb : Xb ≤ W := r01 ▸ hc.1 6501
  unfold spRX1
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r01, r53, h0, h1, h5]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r01, r53, h0, h1, h5])
    try omega

theorem spRX2_exec (c : Config) (hc : WordsBounded W c) {Yb mr zr Rs : ℕ}
    (r52 : c.nreg 5452 = 1) (r54 : c.nreg 5454 = zr) (r57 : c.nreg 5457 = Rs)
    (r60 : c.nreg 5460 = Yb) (r62 : c.nreg 5462 = mr) (r65 : c.nreg 5465 = 4)
    (w : Yb + 5 + 7 * mr ≤ W) (w7 : 7 ≤ W) :
    ∃ c' t, Exec I W spRX2 c c' t ∧ t = 9 ∧ c'.nreg 5471 = Yb + 5 + 7 * mr ∧
      c'.nreg 4910 = zr ∧ c'.nreg 4911 = Rs ∧ c'.nreg 4912 = Yb + 5 + 7 * mr ∧
      c'.nmem = upd c.nmem (Yb + 4 + 7 * mr) (Yb + 5 + 7 * mr) ∧
      (∀ x, (x < 4910 ∨ (4912 < x ∧ x < 5467) ∨ 5471 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h54 : zr ≤ W := r54 ▸ hc.1 5454
  have h57 : Rs ≤ W := r57 ▸ hc.1 5457
  unfold spRX2
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r52, r54, r57, r60, r62, r65]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r52, r54, r57, r60, r62, r65])
    try omega
  all_goals (congr 1; omega)

theorem spRX3_exec (c : Config) (hc : WordsBounded W c) {Yb Rr zr : ℕ}
    (r54 : c.nreg 5454 = zr) (r59 : c.nreg 5459 = 5) (r60 : c.nreg 5460 = Yb)
    (r71 : c.nreg 5471 = Rr) (w : Rr + zr ≤ W) :
    ∃ c' t, Exec I W spRX3 c c' t ∧ t = 3 ∧ c'.nreg 2998 = Yb - 5 ∧ c'.nreg 2999 = Rr + zr ∧
      (∀ x, x ≠ 2998 → x ≠ 2999 → x ≠ 5472 → c'.nreg x = c.nreg x) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h60 : Yb ≤ W := r60 ▸ hc.1 5460
  unfold spRX3
  exec_block
  all_goals try omega
  all_goals
    try (config_simp; simp (disch := omega) only [upd_other, upd_same, r54, r59, r60, r71]; omega)
  refine ⟨rfl, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r54, r59, r60, r71])
    try omega

set_option maxHeartbeats 1000000 in
/-- **The copy phase** (see the module docstring): from `r6501 = Xb`, `r6553 = el`, the sizes
`zl = mem Xb`, `zr = mem (Xb + 1)` and `mr = mem (el + 5)`, with `el + 9 + 6 mr ≤ Xb`. -/
theorem spRec_exec (c : Config) (hc : WordsBounded W c) {Xb el zl zr mr : ℕ}
    (r01 : c.nreg 6501 = Xb) (r53 : c.nreg 6553 = el) (h0 : c.nmem Xb = zl)
    (h1 : c.nmem (Xb + 1) = zr) (h5 : c.nmem (el + 5) = mr) (hel : el + 9 + 6 * mr ≤ Xb)
    (w : Xb + 2 + zl + zr + 10 + 7 * mr + zr ≤ W) :
    ∃ c' t, Exec I W spRec c c' t ∧ t ≤ 42 * mr + 7 * zr + 70 ∧
      c'.nreg 2998 = Xb + 2 + zl + zr ∧ c'.nreg 2999 = Xb + 2 + zl + zr + 10 + 7 * mr + zr ∧
      c'.nmem el = Xb + 2 ∧
      (∀ a < 4 + 6 * mr, c'.nmem (Xb + 2 + zl + zr + 5 + a) = c.nmem (el + 5 + a)) ∧
      c'.nmem (Xb + 2 + zl + zr + 5 + 4 + 7 * mr) = Xb + 2 + zl + zr + 5 + 5 + 7 * mr ∧
      (∀ a < zr, c'.nmem (Xb + 2 + zl + zr + 5 + 5 + 7 * mr + a) = c.nmem (Xb + 2 + zl + a)) ∧
      (∀ a, a ≠ el → a < Xb + 2 + zl + zr + 5 → c'.nmem a = c.nmem a) ∧
      (∀ x, x ≠ 2998 → x ≠ 2999 → (x < 4910 ∨ (4916 < x ∧ x < 5450) ∨ 5472 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set Yb := Xb + 2 + zl + zr + 5 with hYb
  obtain ⟨c₁, t₁, e₁, ht₁, a51, a52, a54, a57, a59, a60, a62, a65, a10, a11, a12, m1, n1, rr1,
    rm1, o1⟩ := spRX1_exec (I := I) c hc r01 r53 h0 h1 h5 (by omega) (by omega) (by omega)
    (by omega)
  -- the copy of the right child's frame
  obtain ⟨c₂, t₂, e₂, ht₂, cp2, mm2, nn2, rr2, rm2, o2⟩ := cpArr_exec (P := I) c₁ e₁.wb_right
    a10 a11 a12 ⟨Or.inl (by omega), by omega, by omega, by omega⟩
  have q2 : ∀ x, (x < 4913 ∨ 4916 < x) → c₂.nreg x = c₁.nreg x := nn2
  obtain ⟨c₃, t₃, e₃, ht₃, b71, b10, b11, b12, m3, n3, rr3, rm3, o3⟩ := spRX2_exec (I := I) c₂
    e₂.wb_right (Yb := Yb) (mr := mr) (zr := zr) (Rs := Xb + 2 + zl)
    (by rw [q2 _ (by omega)]; exact a52) (by rw [q2 _ (by omega)]; exact a54)
    (by rw [q2 _ (by omega)]; exact a57) (by rw [q2 _ (by omega)]; exact a60)
    (by rw [q2 _ (by omega)]; exact a62) (by rw [q2 _ (by omega)]; exact a65) (by omega)
    (by omega)
  -- the copy of the right child's record
  obtain ⟨c₄, t₄, e₄, ht₄, cp4, mm4, nn4, rr4, rm4, o4⟩ := cpArr_exec (P := I) c₃ e₃.wb_right
    b10 b11 b12 ⟨Or.inl (by omega), by omega, by omega, by omega⟩
  have q4 : ∀ x, (x < 4913 ∨ 4916 < x) → c₄.nreg x = c₃.nreg x := nn4
  obtain ⟨c₅, t₅, e₅, ht₅, f98, f99, n5, m5, rr5, rm5, o5⟩ := spRX3_exec (I := I) c₄ e₄.wb_right
    (Yb := Yb) (Rr := Yb + 5 + 7 * mr) (zr := zr)
    (by rw [q4 _ (by omega), n3 _ (by omega), q2 _ (by omega)]; exact a54)
    (by rw [q4 _ (by omega), n3 _ (by omega), q2 _ (by omega)]; exact a59)
    (by rw [q4 _ (by omega), n3 _ (by omega), q2 _ (by omega)]; exact a60)
    (by rw [q4 _ (by omega)]; exact b71) (by omega)
  -- the memory
  have M3 : ∀ a, a ≠ Yb + 4 + 7 * mr → c₃.nmem a = c₂.nmem a := fun a ha => by
    rw [m3, upd_other _ _ _ ha]
  have M1 : ∀ a, a ≠ el → c₁.nmem a = c.nmem a := fun a ha => by rw [m1, upd_other _ _ _ ha]
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega, by rw [f98]; omega,
    by rw [f99], ?_, fun a ha => ?_, ?_, fun a ha => ?_, fun a ha1 ha2 => ?_,
    fun x h1 h2 hx => ?_, by rw [rr5, rr4, rr3, rr2, rr1], by rw [rm5, rm4, rm3, rm2, rm1],
    by rw [o5, o4, o3, o2, o1]⟩
  · rw [m5, mm4 _ (Or.inl (by omega)), M3 _ (by omega), mm2 _ (Or.inl (by omega)), m1, upd_same]
  · rw [m5, mm4 _ (Or.inl (by omega)), M3 _ (by omega), cp2 a (by omega), M1 _ (by omega)]
  · rw [m5, mm4 _ (Or.inl (by omega)), m3, upd_same]
  · rw [m5, cp4 a ha, M3 _ (by omega), mm2 _ (Or.inl (by omega)), M1 _ (by omega)]
  · rw [m5, mm4 _ (Or.inl (by omega)), M3 _ (by omega), mm2 _ (Or.inl (by omega)), M1 _ ha1]
  · rw [n5 x h1 h2 (by omega), q4 _ (by omega), n3 _ (by omega), q2 _ (by omega),
      n1 _ (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
