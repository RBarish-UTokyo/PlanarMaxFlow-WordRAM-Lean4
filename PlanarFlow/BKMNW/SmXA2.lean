module

public import PlanarFlow.BKMNW.SmXA

/-!
# The small separator program, stage A: the run and its meaning

* `smAG_exec` (the gathers through `FX` and the copy, on the machine);
* `smArr_of_rArr` (the record's arrays, with the ones at `A`, are the arrays `SmArr` of `smStep`);
* `pk_first` (`PkMin`: the choice is the dart of least index in the record's enumeration);
* `smFill_exec`, **`smXA0_exec`** (the set-up: `SmRegs`, the inputs of `smStep`, the ones).
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

variable {gid : D → ℕ} {ν : V → ℕ} {u : D → ℤ} {S T : Finset V} {Z : ℕ}

/-- **The record's arrays are the arrays of `smStep`** (with ones at `A`). -/
lemma smArr_of_rArr {x : MCall M} {m n R A : ℕ} {g : ℕ → D} {mem : ℕ → ℕ}
    (h : RArr M gid ν S T x m n R g mem) (hone : ∀ i < n, mem (A + i) = 1) (hν : Injective ν)
    (hpw : x.2.1.Pairwise Disjoint) :
    SmArr M mem n A (R + 3 + n) (R + 3 + 2 * n) (R + 3 + 3 * n) (R + 3 + 4 * n) g x.1.piece
      x.2.1 S T ν where
  inj i hi j hj e := h.g_inj hi hj e
  surj := h.g_surj
  pf i hi := by rw [hone i hi]; exact ⟨fun _ => h.g_mem i hi, fun _ => one_ne_zero⟩
  rv := h.rp
  th := h.hp
  kr := h.kp
  vt := h.vp
  νinj := hν
  pw := hpw

/-- **The choice is the first dart in the record's order.** -/
lemma pk_first {x : MCall M} {m n R : ℕ} {g : ℕ → D} {mem : ℕ → ℕ} {pk : Finset D → D}
    (h : RArr M gid ν S T x m n R g mem) (hpk : PkMin gid pk) :
    ∀ X ⊆ x.1.piece, ∀ i < n, g i ∈ X → (∀ j < i, g j ∉ X) → pk X = g i := by
  intro X hX i hi hgi hmin
  obtain ⟨hmem, hle⟩ := hpk X ⟨_, hgi⟩
  obtain ⟨j, hj, hgj⟩ := h.g_surj _ (hX hmem)
  have h1 := hle _ hgi
  rw [← hgj] at h1 ⊢
  rcases lt_trichotomy j i with hji | rfl | hji
  · exact absurd (hgj ▸ hmem) (hmin j hji)
  · rfl
  · have := h.g_mono i j hji hj; omega

section Exec

variable {I : Input} {W : ℕ}

theorem smAGr_exec (c : Config) (hc : WordsBounded W c) {k a b : ℕ}
    (r27 : c.nreg 5527 = k) (r23 : c.nreg 5523 = a) (r26 : c.nreg 5526 = b) :
    ∃ c' t, Exec I W (block [.copyN 4910 5527, .copyN 4911 5523, .copyN 4912 5526]) c c' t ∧
      t = 3 ∧ c'.nreg 4910 = k ∧ c'.nreg 4911 = a ∧ c'.nreg 4912 = b ∧
      (∀ x, x ≠ 4910 → x ≠ 4911 → x ≠ 4912 → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have := hc.1 5527; have := hc.1 5523; have := hc.1 5526
  exec_block
  all_goals try (config_simp; simp (disch := omega) only [upd_other, upd_same]; omega)
  refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
  all_goals
    try config_simp
    try (simp (disch := omega) only [upd_other, upd_same, r27, r23, r26])
    try omega

set_option maxHeartbeats 1000000 in
/-- **The outputs of `SepPSpec` on the machine**: three gathers through `FX` and a copy. -/
theorem smAG_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb A : ℕ}
    (hR : SmRegs c d m k R n Sb A) (hfx : ∀ i < m, c.nmem (R + 3 + 6 * n + i) < n)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (w : A + 4 * n + k + 2 ≤ W) :
    ∃ c' t, Exec I W smAG c c' t ∧ t ≤ 27 * m + 7 * k + 50 ∧
      (∀ i < m, c'.nmem (Sb + i) = c.nmem (A + n + c.nmem (R + 3 + 6 * n + i))) ∧
      (∀ i < m, c'.nmem (Sb + m + i) = c.nmem (A + 2 * n + c.nmem (R + 3 + 6 * n + i))) ∧
      (∀ i < m, c'.nmem (Sb + 2 * m + i) = c.nmem (A + 3 * n + c.nmem (R + 3 + 6 * n + i))) ∧
      (∀ j < k + 2, c'.nmem (Sb + 3 * m + j) = c.nmem (A + 4 * n + j)) ∧
      (∀ a, (a < Sb ∨ Sb + 3 * m + k + 2 ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4910 ∨ (4916 < x ∧ x < 6210) ∨ 6217 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hA := hR.hA
  have FX : ∀ j < m, A + n + c.nmem (R + 3 + 6 * n + j) < A + 2 * n := fun j hj => by
    have := hfx j hj; omega
  obtain ⟨c₁, t₁, e₁, ht₁, g1, mm1, nn1, rr1, rm1, o1'⟩ := ggProg_exec (P := I) c hc
    (a := 5501) (b := 5516) (cc := 5507) (dd := 5505) (by omega) (by omega) (by omega)
    (by omega) hR.r01 hR.r16 hR.r07 hR.r05 (by omega) (by omega) (by omega)
    (fun j hj => by have := FX j hj; omega) (fun j hj => by omega)
    (fun j hj => by have := FX j hj; omega)
  have q1 : ∀ x, (x < 6210 ∨ 6217 < x) → c₁.nreg x = c.nreg x := nn1
  have hR1 : SmRegs c₁ d m k R n Sb A := hR.congr fun x hx => q1 x (by unfold smReg at hx; omega)
  have M1 : ∀ a, (a < Sb ∨ Sb + m ≤ a) → c₁.nmem a = c.nmem a := fun a ha => mm1 a (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, g2, mm2, nn2, rr2, rm2, o2⟩ := ggProg_exec (P := I) c₁ e₁.wb_right
    (a := 5501) (b := 5516) (cc := 5521) (dd := 5524) (by omega) (by omega) (by omega)
    (by omega) hR1.r01 hR1.r16 hR1.r21 hR1.r24 (by omega) (by omega) (by omega)
    (fun j hj => by rw [M1 _ (by omega)]; have := hfx j hj; omega) (fun j hj => by omega)
    (fun j hj => by rw [M1 _ (by omega)]; have := hfx j hj; omega)
  have q2 : ∀ x, (x < 6210 ∨ 6217 < x) → c₂.nreg x = c₁.nreg x := nn2
  have hR2 : SmRegs c₂ d m k R n Sb A := hR1.congr fun x hx => q2 x (by unfold smReg at hx; omega)
  have M2 : ∀ a, (a < Sb + m ∨ Sb + 2 * m ≤ a) → c₂.nmem a = c₁.nmem a := fun a ha =>
    mm2 a (by omega)
  obtain ⟨c₃, t₃, e₃, ht₃, g3, mm3, nn3, rr3, rm3, o3⟩ := ggProg_exec (P := I) c₂ e₂.wb_right
    (a := 5501) (b := 5516) (cc := 5522) (dd := 5525) (by omega) (by omega) (by omega)
    (by omega) hR2.r01 hR2.r16 hR2.r22 hR2.r25 (by omega) (by omega) (by omega)
    (fun j hj => by rw [M2 _ (by omega), M1 _ (by omega)]; have := hfx j hj; omega)
    (fun j hj => by omega)
    (fun j hj => by rw [M2 _ (by omega), M1 _ (by omega)]; have := hfx j hj; omega)
  have q3 : ∀ x, (x < 6210 ∨ 6217 < x) → c₃.nreg x = c₂.nreg x := nn3
  have hR3 : SmRegs c₃ d m k R n Sb A := hR2.congr fun x hx => q3 x (by unfold smReg at hx; omega)
  have M3 : ∀ a, (a < Sb + 2 * m ∨ Sb + 3 * m ≤ a) → c₃.nmem a = c₂.nmem a := fun a ha =>
    mm3 a (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, v10, v11, v12, nn4, mm4, rr4, rm4, o4⟩ := smAGr_exec (I := I) c₃
    e₃.wb_right hR3.r27 hR3.r23 hR3.r26
  obtain ⟨c₅, t₅, e₅, ht₅, cp5, mm5, nn5, rr5, rm5, o5⟩ := cpArr_exec (P := I) c₄ e₄.wb_right
    v10 v11 v12 ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  have K : ∀ a, (a < Sb ∨ Sb + 3 * m ≤ a) → c₃.nmem a = c.nmem a := fun a ha => by
    rw [M3 a (by omega), M2 a (by omega), M1 a (by omega)]
  have M5 : ∀ a, (a < Sb + 3 * m ∨ Sb + 3 * m + (k + 2) ≤ a) → c₅.nmem a = c₃.nmem a :=
    fun a ha => by rw [mm5 a ha, mm4]
  refine ⟨c₅, _, .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), by omega, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, fun a ha => ?_, fun x hx => ?_,
    by rw [rr5, rr4, rr3, rr2, rr1], by rw [rm5, rm4, rm3, rm2, rm1], by rw [o5, o4, o3, o2, o1']⟩
  · rw [M5 _ (by omega), M3 _ (by omega), M2 _ (by omega), g1 i hi]
  · rw [M5 _ (by omega), M3 _ (by omega), g2 i hi, M1 _ (by omega), M1 _ (by omega)]
  · rw [M5 _ (by omega), g3 i hi, M2 _ (by omega), M1 _ (by omega), M2 _ (by omega),
      M1 _ (by omega)]
  · rw [cp5 j hj, mm4, K _ (by omega)]
  · rcases ha with ha | ha
    · rw [M5 _ (by omega), K _ (Or.inl ha)]
    · rw [M5 _ (by omega), K _ (Or.inr (by omega))]
  · rw [nn5 x (by omega), nn4 x (by omega) (by omega) (by omega), q3 x (by omega),
      q2 x (by omega), q1 x (by omega)]

theorem smFill_exec (c : Config) (hc : WordsBounded W c) {n A : ℕ}
    (r04 : c.nreg 5504 = n) (r06 : c.nreg 5506 = A) (r21 : c.nreg 6521 = 1)
    (w : A + n + 1 ≤ W) :
    ∃ c' t, Exec I W smFill c c' t ∧ t ≤ 6 * n + 3 ∧ (∀ i < n, c'.nmem (A + i) = 1) ∧
      (∀ a, ¬ (A ≤ a ∧ a < A + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have h1 : (1 : ℕ) ≤ W := by omega
  obtain ⟨c₄, t₄, e₄, ht₄, f4, mm4, nn4, rr4, rm4, o4⟩ := mapRun_exec (P := I) c hc
    (vb := block [.constN 6523 1]) (bnd := 5504) (ob := 5506) (m := n) (Ob := A) (B := 1)
    (fun _ => 1) r04 r21 r06 (by omega) (by omega) (by unfold vscr; omega)
    (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
    (fun i hi c' hw h20 hr hm' => by
      obtain ⟨c'', k', e', hk'', v, nn, mm, rr, rm, oo⟩ := cst_exec (P := I) (r := 6523) (v := 1)
        c' hw h1
      exact ⟨c'', k', e', by omega, v, fun x hx => nn x (by unfold vscr at hx; omega), mm, rr,
        rm, oo⟩)
  exact ⟨c₄, t₄, e₄, by omega, f4, mm4, nn4, rr4, rm4, o4⟩

set_option maxHeartbeats 2000000 in
/-- **The set-up of stage A**: the registers `SmRegs`, the inputs of `smStep`, the ones at `A`. -/
theorem smXA0_exec (c : Config) (hc : WordsBounded W c) {d m k R n Sb : ℕ}
    (r4 : c.nreg 3004 = d) (r50 : c.nreg 6500 = Sb) (hm : c.nmem d = m)
    (hk : c.nmem (d + 1) = k) (hR : c.nmem (d + 7 * m + 4) = R) (hn : c.nmem R = n)
    (o1 : R + 3 + 6 * n + m ≤ Sb) (o2 : d + 7 * m + 4 < R)
    (w : Sb + 22 * m + 22 * n + 8 * k + 20 ≤ W) (hW : 21 ≤ W) :
    ∃ c' t, Exec I W smXA0 c c' t ∧ t ≤ 6 * n + 70 ∧
      SmRegs c' d m k R n Sb (Sb + 21 * m + 4 * k + 2) ∧ c'.nreg 6521 = 1 ∧
      c'.nreg 5300 = n ∧ c'.nreg 5301 = Sb + 21 * m + 4 * k + 2 ∧ c'.nreg 5302 = R + 3 + n ∧
      c'.nreg 5303 = R + 3 + 2 * n ∧ c'.nreg 5304 = R + 3 + 3 * n ∧
      c'.nreg 5305 = R + 3 + 4 * n ∧ c'.nreg 5306 = Sb + 21 * m + 4 * k + 2 + n ∧
      c'.nreg 5307 = k ∧
      (∀ i < n, c'.nmem (Sb + 21 * m + 4 * k + 2 + i) = 1) ∧
      (∀ a, (a < Sb + 21 * m + 4 * k + 2 ∨ Sb + 21 * m + 4 * k + 2 + n ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, x < 3013 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a00, a01, a02, a03, a04, a05, n1, m1, rr1, rm1, o1'⟩ :=
    smA0_exec (I := I) c hc r4 r50 hm hk hR hn (by omega) hW
  obtain ⟨c₂, t₂, e₂, ht₂, a06, a07, a21, a22, a23, a08, a09, a28, a10, a30, a31, a11, n2, m2, rr2,
    rm2, o2'⟩ := smA1_exec (I := I) c₁ e₁.wb_right a01 a02 a04 a05 (by omega) hW
  have q21 : ∀ x, (5500 ≤ x ∧ x ≤ 5505) → c₂.nreg x = c₁.nreg x := fun x hx =>
    n2 x (by clear * - hx; omega)
  obtain ⟨c₃, t₃, e₃, ht₃, a17, a12, a13, a14, a15, a16, a24, a25, a26, a27, s0, s1, s2, s3, s4,
    s5, s6, s7, o21, n3, m3, rr3, rm3, o3'⟩ := smA2_exec (I := I) c₂ e₂.wb_right
    ((q21 5501 (by decide)).trans a01) ((q21 5502 (by decide)).trans a02)
    ((q21 5503 (by decide)).trans a03) ((q21 5504 (by decide)).trans a04)
    ((q21 5505 (by decide)).trans a05) a06 a07 (by omega) (by omega) hW
  have E1 : ∀ x, 5500 ≤ x → x ≤ 5505 → c₃.nreg x = c₁.nreg x := fun x h1 h2 => by
    rw [n3 x (by clear * - h1 h2; omega), n2 x (by clear * - h1 h2; omega)]
  have E2 : ∀ x, ((5506 ≤ x ∧ x ≤ 5511) ∨ (5521 ≤ x ∧ x ≤ 5523) ∨ x = 5528 ∨ x = 5530 ∨
      x = 5531) → c₃.nreg x = c₂.nreg x := fun x hx => n3 x (by clear * - hx; omega)
  have hR3 : SmRegs c₃ d m k R n Sb (Sb + 21 * m + 4 * k + 2) :=
    ⟨rfl, (E1 5500 (by decide) (by decide)).trans a00, (E1 5501 (by decide) (by decide)).trans a01,
      (E1 5502 (by decide) (by decide)).trans a02, (E1 5503 (by decide) (by decide)).trans a03,
      (E1 5504 (by decide) (by decide)).trans a04, (E1 5505 (by decide) (by decide)).trans a05,
      (E2 5506 (by decide)).trans a06, (E2 5507 (by decide)).trans a07,
      (E2 5521 (by decide)).trans a21, (E2 5522 (by decide)).trans a22,
      (E2 5523 (by decide)).trans a23, (E2 5508 (by decide)).trans a08,
      (E2 5509 (by decide)).trans a09, (E2 5528 (by decide)).trans a28,
      (E2 5510 (by decide)).trans a10, (E2 5530 (by decide)).trans a30,
      (E2 5531 (by decide)).trans a31, (E2 5511 (by decide)).trans a11,
      a17, a12, a13, a14, a15, a16, a24, a25, a26, a27⟩
  -- the ones
  clear E1 E2
  have wf : Sb + 21 * m + 4 * k + 2 + n + 1 ≤ W := by clear * - w; omega
  obtain ⟨c₄, t₄, e₄, ht₄, f4, mm4, nn4, rr4, rm4, o4⟩ := smFill_exec (I := I) c₃ e₃.wb_right
    hR3.r04 hR3.r06 o21 wf
  have q43 : ∀ x, ¬ vscr x → x ≠ 6522 → x ≠ 6520 → c₄.nreg x = c₃.nreg x := nn4
  have Q : ∀ x, (5299 < x ∧ x < 5308) → c₄.nreg x = c₃.nreg x := fun x hx =>
    q43 x (by clear * - hx; unfold vscr; omega) (by clear * - hx; omega) (by clear * - hx; omega)
  have hR4 : SmRegs c₄ d m k R n Sb (Sb + 21 * m + 4 * k + 2) :=
    hR3.congr fun x hx => q43 x (by clear * - hx; unfold vscr; unfold smReg at hx; omega)
      (by clear * - hx; unfold smReg at hx; omega) (by clear * - hx; unfold smReg at hx; omega)
  have ht : t₁ + (t₂ + (t₃ + t₄)) ≤ 6 * n + 70 := by
    clear * - ht₁ ht₂ ht₃ ht₄; omega
  refine ⟨c₄, _, by unfold smXA0; exact .seq e₁ (.seq e₂ (.seq e₃ e₄)), ht, hR4,
    (q43 6521 (by unfold vscr; decide) (by decide) (by decide)).trans o21,
    (Q 5300 (by decide)).trans s0, (Q 5301 (by decide)).trans s1,
    (Q 5302 (by decide)).trans s2, (Q 5303 (by decide)).trans s3,
    (Q 5304 (by decide)).trans s4, (Q 5305 (by decide)).trans s5,
    (Q 5306 (by decide)).trans s6, (Q 5307 (by decide)).trans s7, f4,
    fun a ha => by rw [mm4 a (by clear * - ha; omega), m3, m2, m1], fun x hx => ?_,
    by rw [rr4, rr3, rr2, rr1], by rw [rm4, rm3, rm2, rm1], by rw [o4, o3', o2', o1']⟩
  rw [q43 x (by clear * - hx; unfold vscr; omega) (by clear * - hx; omega)
    (by clear * - hx; omega), n3 x (by clear * - hx; omega), n2 x (by clear * - hx; omega),
    n1 x (by clear * - hx; omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
