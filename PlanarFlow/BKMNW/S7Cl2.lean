module

public import PlanarFlow.BKMNW.S7Cl

/-!
# Stage 7 of `sepL` (II'): the classes `clsF` on the record, composed

* `clS1`, `clS2` (the bases of `clsProg` from `Cb = r7140`: `YT | YH | NF | R2 | TK | Y2 |
  LS (nk) | OFF | ADJ | LAB | Q | ID`, `RV = RP` of the record), `ClRegs`;
* **`s7Cl = clS1 ; clS2 ; zfill LS ; zfill LAB ; cpArr NF ; clsProg`**, **`s7Cl_exec`**
  (`205 n + 6 nk + 70` steps): `ID[i] = ID[j] ↔ e j ∈ clsF … (e i)` and `ID[i] < 3 (2 n + nk)`
  at `IDb = Cb + 12 n + nk + 2`; memory below `Cb + 2 n`, on `TK = Cb + 4 n` and from
  `Cb + 13 n + nk + 2` kept.

Registers `7100 = n`, `7106 = RPb`, `7140 = Cb`, `7141 = nk`, `7142 = NFsrc`, `7143 = K`,
`6521 = 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

namespace MfDrv

/-- The bases of `clsProg` (first half). -/
def clS1 : Stmt :=
  block [.copyN 4440 7100, .copyN 4441 7106, .copyN 4442 7140, .addN 4443 7140 7100,
    .addN 4444 4443 7100, .addN 4445 4444 7100, .addN 4447 4445 7100, .addN 4446 4447 7100,
    .addN 4424 4446 7100, .addN 4425 4424 7141, .addN 4426 4425 7100, .addN 4426 4426 6521,
    .addN 4403 4426 7100, .addN 4403 4403 7100, .addN 4403 4403 7100]

/-- The bases of `clsProg` (second half). -/
def clS2 : Stmt :=
  block [.addN 4404 4403 7100,
    .addN 4449 4404 7100, .addN 4449 4449 6521, .copyN 4448 4403, .copyN 4450 7143,
    .copyN 4420 7100, .copyN 4421 4445, .copyN 4422 4447, .copyN 4423 4446, .copyN 4400 7100,
    .copyN 4401 4425, .copyN 4402 4426, .copyN 4910 7100, .copyN 4911 7142, .copyN 4912 4444]

/-- **The classes on the record** (see the module docstring). -/
def s7Cl : Stmt :=
  .seq (.seq clS1 clS2) (.seq (zfill 7141 4424) (.seq (zfill 4400 4403) (.seq cpArr clsProg)))

/-- The registers of `clsProg` (and of the zero fills and the copy) after `clS1 ; clS2`. -/
structure ClRegs (c : Config) (n nk RPb Cb NFs K : ℕ) : Prop where
  q0 : c.nreg 4440 = n
  q1 : c.nreg 4441 = RPb
  q2 : c.nreg 4442 = Cb
  q3 : c.nreg 4443 = Cb + n
  q4 : c.nreg 4444 = Cb + 2 * n
  q5 : c.nreg 4445 = Cb + 3 * n
  q6 : c.nreg 4446 = Cb + 5 * n
  q7 : c.nreg 4447 = Cb + 4 * n
  q8 : c.nreg 4448 = Cb + 10 * n + nk + 1
  q9 : c.nreg 4449 = Cb + 12 * n + nk + 2
  q10 : c.nreg 4450 = K
  u0 : c.nreg 4420 = n
  u1 : c.nreg 4421 = Cb + 3 * n
  u2 : c.nreg 4422 = Cb + 4 * n
  u3 : c.nreg 4423 = Cb + 5 * n
  u4 : c.nreg 4424 = Cb + 6 * n
  u5 : c.nreg 4425 = Cb + 6 * n + nk
  u6 : c.nreg 4426 = Cb + 7 * n + nk + 1
  v0 : c.nreg 4400 = n
  v1 : c.nreg 4401 = Cb + 6 * n + nk
  v2 : c.nreg 4402 = Cb + 7 * n + nk + 1
  v3 : c.nreg 4403 = Cb + 10 * n + nk + 1
  v4 : c.nreg 4404 = Cb + 11 * n + nk + 1
  p0 : c.nreg 4910 = n
  p1 : c.nreg 4911 = NFs
  p2 : c.nreg 4912 = Cb + 2 * n

lemma ClRegs.congr {c c' : Config} {n nk RPb Cb NFs K : ℕ} (h : ClRegs c n nk RPb Cb NFs K)
    (e : ∀ x, ((4400 ≤ x ∧ x ≤ 4404) ∨ (4420 ≤ x ∧ x ≤ 4426) ∨ (4440 ≤ x ∧ x ≤ 4450) ∨
      (4910 ≤ x ∧ x ≤ 4912)) → c'.nreg x = c.nreg x) : ClRegs c' n nk RPb Cb NFs K := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, u0, u1, u2, u3, u4, u5, u6, v0, v1, v2,
    v3, v4, p0, p1, p2⟩ := h
  exact ⟨by rw [e _ (by omega)]; exact q0, by rw [e _ (by omega)]; exact q1,
    by rw [e _ (by omega)]; exact q2, by rw [e _ (by omega)]; exact q3,
    by rw [e _ (by omega)]; exact q4, by rw [e _ (by omega)]; exact q5,
    by rw [e _ (by omega)]; exact q6, by rw [e _ (by omega)]; exact q7,
    by rw [e _ (by omega)]; exact q8, by rw [e _ (by omega)]; exact q9,
    by rw [e _ (by omega)]; exact q10, by rw [e _ (by omega)]; exact u0,
    by rw [e _ (by omega)]; exact u1, by rw [e _ (by omega)]; exact u2,
    by rw [e _ (by omega)]; exact u3, by rw [e _ (by omega)]; exact u4,
    by rw [e _ (by omega)]; exact u5, by rw [e _ (by omega)]; exact u6,
    by rw [e _ (by omega)]; exact v0, by rw [e _ (by omega)]; exact v1,
    by rw [e _ (by omega)]; exact v2, by rw [e _ (by omega)]; exact v3,
    by rw [e _ (by omega)]; exact v4, by rw [e _ (by omega)]; exact p0,
    by rw [e _ (by omega)]; exact p1, by rw [e _ (by omega)]; exact p2⟩

section Exec

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 2000000 in
theorem clS1_exec (c : Config) (hc : WordsBounded W c) {n nk RPb Cb : ℕ}
    (r00 : c.nreg 7100 = n) (r06 : c.nreg 7106 = RPb) (r40 : c.nreg 7140 = Cb)
    (r41 : c.nreg 7141 = nk) (r21 : c.nreg 6521 = 1) (w : Cb + 14 * n + nk + 2 ≤ W) :
    ∃ c' t, Exec P W clS1 c c' t ∧ t = 15 ∧
      c'.nreg 4440 = n ∧ c'.nreg 4441 = RPb ∧ c'.nreg 4442 = Cb ∧ c'.nreg 4443 = Cb + n ∧
      c'.nreg 4444 = Cb + 2 * n ∧ c'.nreg 4445 = Cb + 3 * n ∧ c'.nreg 4446 = Cb + 5 * n ∧
      c'.nreg 4447 = Cb + 4 * n ∧ c'.nreg 4424 = Cb + 6 * n ∧
      c'.nreg 4425 = Cb + 6 * n + nk ∧ c'.nreg 4426 = Cb + 7 * n + nk + 1 ∧
      c'.nreg 4403 = Cb + 10 * n + nk + 1 ∧
      c'.nmem = c.nmem ∧
      (∀ x, (x < 4403 ∨ (4403 < x ∧ x < 4424) ∨ (4426 < x ∧ x < 4440) ∨ 4447 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold clS1
  exec_block
  all_goals try (config_simp; (try simp only [r00, r06, r40, r41, r21]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun x hx => ?_, rfl, rfl,
    rfl⟩
  all_goals try (config_simp; (try simp only [r00, r06, r40, r41, r21]); done)
  all_goals try (config_simp; (try simp only [r00, r06, r40, r41, r21]); omega)
  · config_simp; simp (disch := omega) only [upd_other]

set_option maxHeartbeats 2000000 in
theorem clS2_exec (c : Config) (hc : WordsBounded W c) {n nk Cb NFs K : ℕ}
    (r00 : c.nreg 7100 = n) (r42 : c.nreg 7142 = NFs) (r43 : c.nreg 7143 = K)
    (r21 : c.nreg 6521 = 1) (q4 : c.nreg 4444 = Cb + 2 * n) (q5 : c.nreg 4445 = Cb + 3 * n)
    (q6 : c.nreg 4446 = Cb + 5 * n) (q7 : c.nreg 4447 = Cb + 4 * n)
    (u5 : c.nreg 4425 = Cb + 6 * n + nk) (u6 : c.nreg 4426 = Cb + 7 * n + nk + 1)
    (v3 : c.nreg 4403 = Cb + 10 * n + nk + 1) (w : Cb + 14 * n + nk + 2 ≤ W) :
    ∃ c' t, Exec P W clS2 c c' t ∧ t = 15 ∧
      c'.nreg 4404 = Cb + 11 * n + nk + 1 ∧ c'.nreg 4449 = Cb + 12 * n + nk + 2 ∧
      c'.nreg 4448 = Cb + 10 * n + nk + 1 ∧ c'.nreg 4450 = K ∧
      c'.nreg 4420 = n ∧ c'.nreg 4421 = Cb + 3 * n ∧ c'.nreg 4422 = Cb + 4 * n ∧
      c'.nreg 4423 = Cb + 5 * n ∧ c'.nreg 4400 = n ∧ c'.nreg 4401 = Cb + 6 * n + nk ∧
      c'.nreg 4402 = Cb + 7 * n + nk + 1 ∧
      c'.nreg 4910 = n ∧ c'.nreg 4911 = NFs ∧ c'.nreg 4912 = Cb + 2 * n ∧
      c'.nmem = c.nmem ∧
      (∀ x, (x < 4400 ∨ x = 4403 ∨ (4404 < x ∧ x < 4420) ∨ (4423 < x ∧ x < 4448) ∨
        (4450 < x ∧ x < 4910) ∨ 4912 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold clS2
  exec_block
  all_goals try (config_simp; (try simp only [r00, r42, r43, r21, q4, q5, q6, q7, u5, u6, v3]); omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, fun x hx => ?_,
    rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r00, r42, r43, r21, q4, q5, q6, q7, u5, u6, v3]); done)
  all_goals try (config_simp; (try simp only [r00, r42, r43, r21, q4, q5, q6, q7, u5, u6, v3]); omega)
  · config_simp; simp (disch := omega) only [upd_other]

set_option maxHeartbeats 1000000 in
theorem clS_exec (c : Config) (hc : WordsBounded W c) {n nk RPb Cb NFs K : ℕ}
    (r00 : c.nreg 7100 = n) (r06 : c.nreg 7106 = RPb) (r40 : c.nreg 7140 = Cb)
    (r41 : c.nreg 7141 = nk) (r42 : c.nreg 7142 = NFs) (r43 : c.nreg 7143 = K)
    (r21 : c.nreg 6521 = 1) (w : Cb + 14 * n + nk + 2 ≤ W) :
    ∃ c' t, Exec P W (.seq clS1 clS2) c c' t ∧ t = 30 ∧ ClRegs c' n nk RPb Cb NFs K ∧
      c'.nmem = c.nmem ∧
      (∀ x, (x < 4400 ∨ (4404 < x ∧ x < 4420) ∨ (4426 < x ∧ x < 4440) ∨ (4450 < x ∧ x < 4910) ∨
        4912 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, m1, n1, rr1, rm1,
    o1⟩ := clS1_exec (P := P) c hc r00 r06 r40 r41 r21 w
  obtain ⟨c₂, t₂, e₂, ht₂, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, m2, n2,
    rr2, rm2, o2⟩ := clS2_exec (P := P) c₁ e₁.wb_right (n := n) (nk := nk) (Cb := Cb)
    (NFs := NFs) (K := K)
    (by rw [n1 _ (by omega)]; exact r00) (by rw [n1 _ (by omega)]; exact r42)
    (by rw [n1 _ (by omega)]; exact r43) (by rw [n1 _ (by omega)]; exact r21) a4 a5 a6 a7 a9 a10
    a11 w
  have k : ∀ x, ((4440 ≤ x ∧ x ≤ 4447) ∨ (4424 ≤ x ∧ x ≤ 4426) ∨ x = 4403) →
      c₂.nreg x = c₁.nreg x := fun x hx => n2 x (by omega)
  refine ⟨c₂, t₁ + t₂, .seq e₁ e₂, by omega,
    { q0 := by rw [k _ (by omega)]; exact a0, q1 := by rw [k _ (by omega)]; exact a1,
      q2 := by rw [k _ (by omega)]; exact a2, q3 := by rw [k _ (by omega)]; exact a3,
      q4 := by rw [k _ (by omega)]; exact a4, q5 := by rw [k _ (by omega)]; exact a5,
      q6 := by rw [k _ (by omega)]; exact a6, q7 := by rw [k _ (by omega)]; exact a7,
      q8 := b2, q9 := b1, q10 := b3, u0 := b4, u1 := b5, u2 := b6, u3 := b7,
      u4 := by rw [k _ (by omega)]; exact a8, u5 := by rw [k _ (by omega)]; exact a9,
      u6 := by rw [k _ (by omega)]; exact a10, v0 := b8, v1 := b9, v2 := b10,
      v3 := by rw [k _ (by omega)]; exact a11, v4 := b0, p0 := b11, p1 := b12, p2 := b13 },
    by rw [m2, m1], fun x hx => by rw [n2 x (by omega), n1 x (by omega)], by rw [rr2, rr1],
    by rw [rm2, rm1], by rw [o2, o1]⟩

set_option maxHeartbeats 4000000 in
/-- **The classes on the record** (see the module docstring). -/
theorem s7Cl_exec {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    [Fintype F] [DecidableEq F] {M : CombMap D V F} {Ps Nf : Finset D} {Hs : List (Finset V)}
    {K : ℕ} {ρ : HPath M} {e : ℕ → D} (c : Config) (hc : WordsBounded W c)
    {n nk RPb Cb NFs : ℕ}
    (r00 : c.nreg 7100 = n) (r06 : c.nreg 7106 = RPb) (r40 : c.nreg 7140 = Cb)
    (r41 : c.nreg 7141 = nk) (r42 : c.nreg 7142 = NFs) (r43 : c.nreg 7143 = K)
    (r21 : c.nreg 6521 = 1)
    (hE : ClsEnum M Ps Nf Hs (newHole Hs ρ.mverts) n e (fun i => c.nmem (RPb + i))
      (fun i => c.nmem (Cb + 4 * n + i)) (fun i => c.nmem (Cb + i))
      (fun i => c.nmem (Cb + n + i)) (fun i => c.nmem (NFs + i)))
    (hNf : Nf ⊆ Ps) (hY : HClosed Hs (newHole Hs ρ.mverts)) (hC : IsCls Ps (clsF M Ps Nf Hs K ρ))
    (hTK : ∀ i < n, c.nmem (Cb + 4 * n + i) < nk)
    (lay : RPb + n ≤ Cb ∧ NFs + n ≤ Cb ∧ Cb + 14 * n + nk + 2 ≤ W)
    (hW : 3 * (n + nk) + 2 ≤ W) :
    ∃ c' t, Exec P W s7Cl c c' t ∧ t ≤ 205 * n + 6 * nk + 70 ∧
      (∀ i < n, ∀ j < n, (c'.nmem (Cb + 12 * n + nk + 2 + i) =
        c'.nmem (Cb + 12 * n + nk + 2 + j) ↔ e j ∈ clsF M Ps Nf Hs K ρ (e i))) ∧
      (∀ i < n, c'.nmem (Cb + 12 * n + nk + 2 + i) < 3 * (2 * n + nk)) ∧
      (∀ a, (a < Cb + 2 * n ∨ (Cb + 4 * n ≤ a ∧ a < Cb + 5 * n) ∨ Cb + 13 * n + nk + 2 ≤ a) →
        c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4400 ∨ (4467 < x ∧ x < 4910) ∨ (4916 < x ∧ x < 6520) ∨ x = 6521 ∨
        6529 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3⟩ := lay
  unfold s7Cl
  obtain ⟨c₁, t₁, e₁, ht₁, hR1, m1, n1, rr1, rm1, o1⟩ :=
    clS_exec (P := P) c hc r00 r06 r40 r41 r42 r43 r21 l3
  have k21 : c₁.nreg 6521 = 1 := by rw [n1 _ (by omega)]; exact r21
  have k41 : c₁.nreg 7141 = nk := by rw [n1 _ (by omega)]; exact r41
  obtain ⟨c₂, t₂, e₂, ht₂, f2, fm2, fn2, fr2, frm2, fo2⟩ := zfill_exec (P := P) c₁ e₁.wb_right
    (bnd := 7141) (ob := 4424) (m := nk) (Ob := Cb + 6 * n) k41 k21 hR1.u4 (by omega) (by omega)
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
  have hR2 : ClRegs c₂ n nk RPb Cb NFs K := hR1.congr fun x hx =>
    fn2 x (by unfold vscr; omega) (by omega) (by omega)
  have k21' : c₂.nreg 6521 = 1 := by
    rw [fn2 _ (by unfold vscr; omega) (by omega) (by omega)]; exact k21
  obtain ⟨c₃, t₃, e₃, ht₃, f3, fm3, fn3, fr3, frm3, fo3⟩ := zfill_exec (P := P) c₂ e₂.wb_right
    (bnd := 4400) (ob := 4403) (m := n) (Ob := Cb + 10 * n + nk + 1) hR2.v0 k21' hR2.v3
    (by omega) (by omega)
    (by unfold vscr; omega) (by unfold vscr; omega) (by omega) (by omega) (by omega) (by omega)
  have hR3 : ClRegs c₃ n nk RPb Cb NFs K := hR2.congr fun x hx =>
    fn3 x (by unfold vscr; omega) (by omega) (by omega)
  obtain ⟨c₄, t₄, e₄, ht₄, f4, fm4, fn4, fr4, frm4, fo4⟩ := cpArr_exec (P := P) c₃ e₃.wb_right
    hR3.p0 hR3.p1 hR3.p2 ⟨Or.inl (by omega), by omega, by omega, by omega⟩
  have hR4 : ClRegs c₄ n nk RPb Cb NFs K := hR3.congr fun x hx => fn4 x (by omega)
  -- the memory before `clsProg`
  have M4 : ∀ a, (a < Cb + 3 * n ∨ (Cb + 4 * n ≤ a ∧ a < Cb + 6 * n) ∨
      (Cb + 6 * n + nk ≤ a ∧ a < Cb + 10 * n + nk + 1) ∨ Cb + 11 * n + nk + 1 ≤ a) →
      ¬ (Cb + 2 * n ≤ a ∧ a < Cb + 3 * n) → c₄.nmem a = c.nmem a := fun a h1 h2 => by
    rw [fm4 a (by omega), fm3 a (by omega), fm2 a (by omega), m1]
  have NF4 : ∀ i < n, c₄.nmem (Cb + 2 * n + i) = c.nmem (NFs + i) := fun i hi => by
    rw [f4 i hi, fm3 _ (by omega), fm2 _ (by omega), m1]
  have hE4 : ClsEnum M Ps Nf Hs (newHole Hs ρ.mverts) n e (fun i => c₄.nmem (RPb + i))
      (fun i => c₄.nmem (Cb + 4 * n + i)) (fun i => c₄.nmem (Cb + i))
      (fun i => c₄.nmem (Cb + n + i)) (fun i => c₄.nmem (Cb + 2 * n + i)) := by
    refine ⟨hE.mem, hE.surj, hE.inj, fun i hi => ?_, fun i hi => ?_, fun i hi j hj => ?_,
      fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rw [M4 _ (by omega) (by omega)]; exact hE.rvlt i hi
    · rw [M4 _ (by omega) (by omega)]; exact hE.rvin i hi
    · rw [M4 _ (by omega) (by omega), M4 (Cb + 4 * n + j) (by omega) (by omega)]
      exact hE.key i hi j hj
    · rw [M4 _ (by omega) (by omega)]; exact hE.yt i hi
    · rw [M4 _ (by omega) (by omega)]; exact hE.yh i hi
    · rw [NF4 i hi]; exact hE.nf i hi
  have hTK4 : ∀ i < n, c₄.nmem (Cb + 4 * n + i) < nk := fun i hi => by
    rw [M4 _ (by omega) (by omega)]; exact hTK i hi
  have hLS4 : ∀ k < nk, c₄.nmem (Cb + 6 * n + k) = 0 := fun k hk => by
    rw [fm4 _ (by omega), fm3 _ (by omega)]; exact f2 k hk
  have hLAB4 : ∀ u < n, c₄.nmem (Cb + 10 * n + nk + 1 + u) = 0 := fun u hu => by
    rw [fm4 _ (by omega)]; exact f3 u hu
  obtain ⟨c₅, t₅, e₅, ht₅, H1, H2, H3, n5, rr5, rm5, o5⟩ := clsProg_clsF' (P := P) c₄ e₄.wb_right
    (n := n) (nk := nk) (RVb := RPb) (YTb := Cb) (YHb := Cb + n) (NFb := Cb + 2 * n)
    (R2b := Cb + 3 * n) (TKb := Cb + 4 * n) (Y2b := Cb + 5 * n) (LSb := Cb + 6 * n)
    (OFFb := Cb + 6 * n + nk) (ADJb := Cb + 7 * n + nk + 1) (LABb := Cb + 10 * n + nk + 1)
    (Qb := Cb + 11 * n + nk + 1) (IDb := Cb + 12 * n + nk + 2)
    ⟨by omega, by omega, by omega, by omega, ⟨by omega, by omega, by omega, by omega, by omega⟩,
      ⟨by omega, by omega, by omega, by omega⟩, by omega, by omega, hW⟩
    hE4 hNf hY hC hTK4 hLS4 hLAB4 hR4.q0 hR4.q1 hR4.q2 hR4.q3 hR4.q4 hR4.q5 hR4.q6 hR4.q7
    hR4.q8 hR4.q9 hR4.q10 hR4.u0 hR4.u1 hR4.u2 hR4.u3 hR4.u4 hR4.u5 hR4.u6 hR4.v0 hR4.v1
    hR4.v2 hR4.v3 hR4.v4
  refine ⟨c₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
    by omega, H1, H2, fun a ha => ?_, fun x hx => ?_, by rw [rr5, fr4, fr3, fr2, rr1],
    by rw [rm5, frm4, frm3, frm2, rm1], by rw [o5, fo4, fo3, fo2, o1]⟩
  · rw [H3 a (by omega)]
    rw [fm4 a (by omega), fm3 a (by omega), fm2 a (by omega), m1]
  · rw [n5 x (by omega), fn4 x (by omega), fn3 x (by unfold vscr; omega) (by omega) (by omega),
      fn2 x (by unfold vscr; omega) (by omega) (by omega), n1 x (by omega)]

end Exec

end MfDrv

end BKMNW

end PlanarFlow
