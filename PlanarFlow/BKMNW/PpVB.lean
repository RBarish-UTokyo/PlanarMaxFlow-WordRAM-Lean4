module

public import PlanarFlow.BKMNW.PpSort
public import PlanarFlow.BKMNW.LinMap

/-!
# Value blocks of the preprocessing: the slot functions on the machine

The preprocessing program computes, for every slot `s < 7 n`, the slot functions of `PpIdx.lean`
(`revS`, `rotS`, `rtS`, `capS`, `krS`, `keyS`) by map loops (`mapProg`) whose value block reads
the per-dart arrays (`RV = rvI`, `SG = sgI`, `PI = piI`, the flags `CV`, `CF` of `CvI`, `CfI`, the
face labels `FL = flI`, the capacities, the terminal flags, the tail numbers). This file has the
value blocks and their specifications.

Registers: `8700` `n`, `8701` `3 n`, `8702` `5 n`, `8703` `7 n`, `8704` `1`, `8705` `2`, `8706`
`3`, `8707` `K`, `8708` `BIG`; array bases `8710 … 8719`; the slot `s` in `8740` (the counter of
the map loop); the decoded slot `q = s / 3`, `r = s % 3`, `x₁ = (s - 3 n) / 2`, `b₁ = (s - 3 n) % 2`,
`x₂ = (s - 5 n) / 2` in `8750 … 8754`; scratch `8755 … 8779`; the value in `8744`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace Pp

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The scratch registers of the value blocks (and the value register `8744`). -/
def pscr (x : ℕ) : Prop := 8744 ≤ x ∧ x ≤ 8779

/-- The constant registers of the value blocks. -/
structure KRegs (n K BIG : ℕ) (c : Config) : Prop where
  rn : c.nreg 8700 = n
  r3 : c.nreg 8701 = 3 * n
  r5 : c.nreg 8702 = 5 * n
  r7 : c.nreg 8703 = 7 * n
  one : c.nreg 8704 = 1
  two : c.nreg 8705 = 2
  three : c.nreg 8706 = 3
  rk : c.nreg 8707 = K
  rbig : c.nreg 8708 = BIG

/-- The postcondition of a value block computing `val` into `8744` within `B` steps. -/
def VBPost (c : Config) (val B : ℕ) (c' : Config) (k : ℕ) : Prop :=
  k ≤ B ∧ c'.nreg 8744 = val ∧ (∀ x, ¬ pscr x → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output

/-- **The decoding of the slot** `s = r8740`. -/
def decB : Stmt :=
  block [.divN 8750 8740 8706, .modN 8751 8740 8706, .subN 8756 8740 8701, .divN 8752 8756 8705,
    .modN 8753 8756 8705, .subN 8756 8740 8702, .divN 8754 8756 8705]

/-- The frame goal of a value block after a straight-line leaf. -/
macro "vbframe" : tactic =>
  `(tactic| (unfold pscr at *; config_simp; simp (disch := omega) only [upd_other]))

variable {P : Input} {W : ℕ}

/-- The registers after the decoding. -/
structure Dec (s n : ℕ) (c c₁ : Config) : Prop where
  q : c₁.nreg 8750 = s / 3
  r : c₁.nreg 8751 = s % 3
  x1 : c₁.nreg 8752 = (s - 3 * n) / 2
  b1 : c₁.nreg 8753 = (s - 3 * n) % 2
  x2 : c₁.nreg 8754 = (s - 5 * n) / 2
  fr : ∀ x, x < 8750 ∨ 8756 < x → c₁.nreg x = c.nreg x
  m : c₁.nmem = c.nmem
  rr : c₁.rreg = c.rreg
  rm : c₁.rmem = c.rmem
  o : c₁.output = c.output

/-- **Sequencing a value block after the decoding.** -/
theorem vb_dec {t : Stmt} {c : Config} (hc : WordsBounded W c) {n K BIG s val B : ℕ}
    (hK : KRegs n K BIG c) (hs : c.nreg 8740 = s)
    (h : ∀ c₁, WordsBounded W c₁ → Dec s n c c₁ → KRegs n K BIG c₁ → c₁.nreg 8740 = s →
      ∃ c' k, Exec P W t c₁ c' k ∧ VBPost c₁ val B c' k) :
    ∃ c' k, Exec P W (.seq decB t) c c' k ∧ VBPost c val (B + 7) c' k := by
  obtain ⟨c₁, k₁, e₁, hk₁, hd⟩ : ∃ c₁ k₁, Exec P W decB c c₁ k₁ ∧ k₁ = 7 ∧ Dec s n c c₁ := by
    unfold decB
    exec_block
    refine ⟨rfl, ?_⟩
    have h3 := hK.three; have h2 := hK.two; have h31 := hK.r3; have h5 := hK.r5
    refine ⟨?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩ <;>
    · config_simp
      try simp (disch := omega) only [upd_other, upd_same, hs, h3, h2, h31, h5]
  have hK₁ : KRegs n K BIG c₁ := by
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hK
    exact ⟨by rw [hd.fr _ (by omega)]; exact a1, by rw [hd.fr _ (by omega)]; exact a2,
      by rw [hd.fr _ (by omega)]; exact a3, by rw [hd.fr _ (by omega)]; exact a4,
      by rw [hd.fr _ (by omega)]; exact a5, by rw [hd.fr _ (by omega)]; exact a6,
      by rw [hd.fr _ (by omega)]; exact a7, by rw [hd.fr _ (by omega)]; exact a8,
      by rw [hd.fr _ (by omega)]; exact a9⟩
  obtain ⟨c', k₂, e₂, hk₂, hv, hf, hm, hr, hrm, ho⟩ :=
    h c₁ e₁.wb_right hd hK₁ (by rw [hd.fr _ (by omega)]; exact hs)
  refine ⟨c', k₁ + k₂, .seq e₁ e₂, by omega, hv, fun x hx => ?_, by rw [hm, hd.m],
    by rw [hr, hd.rr], by rw [hrm, hd.rm], by rw [ho, hd.o]⟩
  rw [hf x hx]
  unfold pscr at hx
  exact hd.fr x (by omega)

/-! ### The reversal -/

/-- **The value block of `revS`.** -/
def vbRev : Stmt := .seq decB (.ifLtN 8740 8701
  (.ifLtN 8751 8704 (block [.addN 8757 8710 8750, .loadN 8744 8757, .mulN 8744 8744 8706])
    (.ifLtN 8751 8705 (block [.addN 8744 8740 8704]) (block [.subN 8744 8740 8704])))
  (.ifLtN 8753 8704 (block [.addN 8744 8740 8704]) (block [.subN 8744 8740 8704])))

theorem vbRev_exec {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (c : Config) (hc : WordsBounded W c) {K BIG s RVb : ℕ}
    (hK : KRegs n K BIG c) (hs : c.nreg 8740 = s) (hs7 : s < 7 * n) (hb : c.nreg 8710 = RVb)
    (hA : ∀ x < n, c.nmem (RVb + x) = rvI M x) (hA' : ∀ x < n, rvI M x < n)
    (hW : RVb + 7 * n + 3 ≤ W) :
    ∃ c' k, Exec P W vbRev c c' k ∧ VBPost c (revS M s) 13 c' k := by
  unfold vbRev
  refine vb_dec (B := 6) hc hK hs (fun c₁ hc₁ hd hK₁ hs₁ => ?_)
  have hb₁ : c₁.nreg 8710 = RVb := by rw [hd.fr _ (by omega)]; exact hb
  have hA₁ : ∀ x < n, c₁.nmem (RVb + x) = rvI M x := fun x hx => by rw [hd.m]; exact hA x hx
  have o1 := hK₁.one; have o3 := hK₁.three; have o31 := hK₁.r3; have hq := hd.q; have hr := hd.r
  have hb1 := hd.b1
  by_cases h3 : s < 3 * n
  · refine spec_ifLtN_true (by rw [hs₁, hK₁.r3]; exact h3) ?_
    by_cases hr0 : s % 3 < 1
    · refine spec_ifLtN_true (by rw [hd.r, hK₁.one]; exact hr0) ?_
      have hq' : s / 3 < n := by omega
      have hv := hA₁ _ hq'
      have hv' := hA' _ hq'
      exec_block
      · config_simp; rw [hb₁, hq]; omega
      · config_simp; rw [hb₁, hq, hv, o3]; omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [hb₁, hq, hv, o3]
        unfold revS; rw [ppIteT h3, ppIteT (by omega)]; ring
      · unfold pscr at hx; config_simp; simp (disch := omega) only [upd_other]
    · refine spec_ifLtN_false (by rw [hd.r, hK₁.one]; exact hr0) ?_
      by_cases hr1 : s % 3 < 2
      · refine spec_ifLtN_true (by rw [hd.r, hK₁.two]; exact hr1) ?_
        exec_block
        · config_simp; rw [hs₁, o1]; omega
        refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [hs₁, o1]
          unfold revS; rw [ppIteT h3, ppIteF (by omega), ppIteT (by omega)]
        · unfold pscr at hx; config_simp; simp (disch := omega) only [upd_other]
      · refine spec_ifLtN_false (by rw [hd.r, hK₁.two]; exact hr1) ?_
        exec_block
        refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [hs₁, o1]
          unfold revS; rw [ppIteT h3, ppIteF (by omega), ppIteF (by omega)]
        · unfold pscr at hx; config_simp; simp (disch := omega) only [upd_other]
  · refine spec_ifLtN_false (by rw [hs₁, hK₁.r3]; exact h3) ?_
    by_cases hp : (s - 3 * n) % 2 < 1
    · refine spec_ifLtN_true (by rw [hd.b1, hK₁.one]; exact hp) ?_
      exec_block
      · config_simp; rw [hs₁, o1]; omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [hs₁, o1]
        unfold revS; rw [ppIteF h3, ppIteT (by omega)]
      · unfold pscr at hx; config_simp; simp (disch := omega) only [upd_other]
    · refine spec_ifLtN_false (by rw [hd.b1, hK₁.one]; exact hp) ?_
      exec_block
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [hs₁, o1]
        unfold revS; rw [ppIteF h3, ppIteF (by omega)]
      · unfold pscr at hx; config_simp; simp (disch := omega) only [upd_other]

/-! ### The rotation and the root rotation -/

/-- **The value block of `rotS`.** -/
def vbRot : Stmt := .seq decB (.ifLtN 8740 8701
  (.ifLtN 8751 8704
    (block [.addN 8757 8711 8750, .loadN 8744 8757, .mulN 8744 8744 8706, .addN 8744 8744 8704])
    (.ifLtN 8751 8705
      (.seq (block [.addN 8757 8713 8750, .loadN 8758 8757])
        (.ifLtN 8758 8704 (block [.mulN 8744 8750 8706])
          (block [.mulN 8744 8750 8705, .addN 8744 8744 8701])))
      (.seq (block [.addN 8757 8712 8750, .loadN 8759 8757, .addN 8757 8714 8759,
          .loadN 8758 8757])
        (.ifLtN 8758 8704 (block [.mulN 8744 8759 8706, .addN 8744 8744 8705])
          (block [.mulN 8744 8759 8705, .addN 8744 8744 8702])))))
  (.ifLtN 8740 8702
    (.ifLtN 8753 8704 (block [.mulN 8744 8752 8706]) (block [.copyN 8744 8740]))
    (.ifLtN 8753 8704 (block [.mulN 8744 8754 8706, .addN 8744 8744 8705])
      (block [.copyN 8744 8740]))))

/-- The flag of a proposition. -/
noncomputable def fl (p : Prop) : ℕ := by classical exact if p then 1 else 0

lemma fl_lt_one {p : Prop} : fl p < 1 ↔ ¬ p := by
  unfold fl; split_ifs with h <;> simp [h]

lemma fl_le_one (p : Prop) : fl p ≤ 1 := by unfold fl; split_ifs <;> omega

/-- The per-dart arrays read by the value blocks of the rotations. -/
structure RotArrs {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (c : Config) (SGb PIb CVb CFb : ℕ) : Prop where
  bsg : c.nreg 8711 = SGb
  bpi : c.nreg 8712 = PIb
  bcv : c.nreg 8713 = CVb
  bcf : c.nreg 8714 = CFb
  sg : ∀ x < n, c.nmem (SGb + x) = sgI M x
  pi : ∀ x < n, c.nmem (PIb + x) = piI M x
  cv : ∀ x < n, c.nmem (CVb + x) = fl (CvI M x)
  cf : ∀ x < n, c.nmem (CFb + x) = fl (CfI M x)
  sg_lt : ∀ x < n, sgI M x < n
  pi_lt : ∀ x < n, piI M x < n

lemma RotArrs.congr {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    {M : CombMap (Fin n) V F} {c c₁ : Config} {SGb PIb CVb CFb : ℕ}
    (h : RotArrs M c SGb PIb CVb CFb) (hr : ∀ x, x < 8750 → c₁.nreg x = c.nreg x)
    (hm : c₁.nmem = c.nmem) : RotArrs M c₁ SGb PIb CVb CFb :=
  ⟨by rw [hr _ (by omega)]; exact h.bsg, by rw [hr _ (by omega)]; exact h.bpi,
    by rw [hr _ (by omega)]; exact h.bcv, by rw [hr _ (by omega)]; exact h.bcf,
    fun x hx => by rw [hm]; exact h.sg x hx, fun x hx => by rw [hm]; exact h.pi x hx,
    fun x hx => by rw [hm]; exact h.cv x hx, fun x hx => by rw [hm]; exact h.cf x hx,
    h.sg_lt, h.pi_lt⟩

theorem vbRot_exec {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (c : Config) (hc : WordsBounded W c) {K BIG s SGb PIb CVb CFb : ℕ}
    (hK : KRegs n K BIG c) (hs : c.nreg 8740 = s) (hs7 : s < 7 * n)
    (hA : RotArrs M c SGb PIb CVb CFb)
    (hW : SGb + PIb + CVb + CFb + 7 * n + 3 ≤ W) :
    ∃ c' k, Exec P W vbRot c c' k ∧ VBPost c (rotS M s) 20 c' k := by
  unfold vbRot
  refine vb_dec (B := 13) hc hK hs (fun c₁ hc₁ hd hK₁ hs₁ => ?_)
  have hA₁ := hA.congr (fun x hx => hd.fr x (Or.inl hx)) hd.m
  have o1 := hK₁.one; have o2 := hK₁.two; have o3 := hK₁.three; have o31 := hK₁.r3
  have o5 := hK₁.r5
  have hq := hd.q; have hr := hd.r; have hb1 := hd.b1; have hx1 := hd.x1; have hx2 := hd.x2
  have bsg := hA₁.bsg; have bpi := hA₁.bpi; have bcv := hA₁.bcv; have bcf := hA₁.bcf
  by_cases h3 : s < 3 * n
  · refine spec_ifLtN_true (by rw [hs₁, o31]; exact h3) ?_
    have hq' : s / 3 < n := by omega
    by_cases hr0 : s % 3 < 1
    · refine spec_ifLtN_true (by rw [hr, o1]; exact hr0) ?_
      have hv := hA₁.sg _ hq'
      have hv' := hA₁.sg_lt _ hq'
      exec_block
      · config_simp; rw [bsg, hq]; omega
      · config_simp; rw [bsg, hq, hv, o3]; omega
      · config_simp; rw [bsg, hq, hv, o3, o1]; omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [bsg, hq, hv, o3, o1]
        unfold rotS; rw [ppIteT h3, ppIteT (by omega)]; ring
      · vbframe
    · refine spec_ifLtN_false (by rw [hr, o1]; exact hr0) ?_
      by_cases hr1 : s % 3 < 2
      · refine spec_ifLtN_true (by rw [hr, o2]; exact hr1) ?_
        have hv := hA₁.cv _ hq'
        refine spec_seq ?_
        exec_block
        · config_simp; rw [bcv, hq]; omega
        by_cases hf : CvI M (s / 3)
        · refine spec_ifLtN_false ?_ ?_
          · config_simp; rw [bcv, hq, hv, o1, fl_lt_one]; exact not_not.2 hf
          exec_block
          · config_simp; rw [hq, o2]; omega
          · config_simp; rw [hq, o2, o31]; omega
          refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
          · config_simp; rw [hq, o2, o31]
            unfold rotS; rw [ppIteT h3, ppIteF (by omega), ppIteT (by omega), ppIteT hf]; ring
          · vbframe
        · refine spec_ifLtN_true ?_ ?_
          · config_simp; rw [bcv, hq, hv, o1, fl_lt_one]; exact hf
          exec_block
          · config_simp; rw [hq, o3]; omega
          refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
          · config_simp; rw [hq, o3]
            unfold rotS; rw [ppIteT h3, ppIteF (by omega), ppIteT (by omega), ppIteF hf]; ring
          · vbframe
      · refine spec_ifLtN_false (by rw [hr, o2]; exact hr1) ?_
        have hp := hA₁.pi _ hq'
        have hp' := hA₁.pi_lt _ hq'
        have hv := hA₁.cf _ hp'
        refine spec_seq ?_
        exec_block
        · config_simp; rw [bpi, hq]; omega
        · config_simp; rw [bpi, hq, hp, bcf]; omega
        by_cases hf : CfI M (piI M (s / 3))
        · refine spec_ifLtN_false ?_ ?_
          · config_simp; rw [bpi, hq, hp, bcf, hv, o1, fl_lt_one]; exact not_not.2 hf
          exec_block
          · config_simp; rw [bpi, hq, hp, o2]; omega
          · config_simp; rw [bpi, hq, hp, o2, o5]; omega
          refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
          · config_simp; rw [bpi, hq, hp, o2, o5]
            unfold rotS; rw [ppIteT h3, ppIteF (by omega), ppIteF (by omega), ppIteT hf]; ring
          · vbframe
        · refine spec_ifLtN_true ?_ ?_
          · config_simp; rw [bpi, hq, hp, bcf, hv, o1, fl_lt_one]; exact hf
          exec_block
          · config_simp; rw [bpi, hq, hp, o3]; omega
          · config_simp; rw [bpi, hq, hp, o3, o2]; omega
          refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
          · config_simp; rw [bpi, hq, hp, o3, o2]
            unfold rotS; rw [ppIteT h3, ppIteF (by omega), ppIteF (by omega), ppIteF hf]; ring
          · vbframe
  · refine spec_ifLtN_false (by rw [hs₁, o31]; exact h3) ?_
    by_cases h5 : s < 5 * n
    · refine spec_ifLtN_true (by rw [hs₁, o5]; exact h5) ?_
      by_cases hp : (s - 3 * n) % 2 < 1
      · refine spec_ifLtN_true (by rw [hb1, o1]; exact hp) ?_
        exec_block
        · config_simp; rw [hx1, o3]; omega
        refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [hx1, o3]
          unfold rotS; rw [ppIteF h3, ppIteT h5, ppIteT (by omega)]; ring
        · vbframe
      · refine spec_ifLtN_false (by rw [hb1, o1]; exact hp) ?_
        exec_block
        refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [hs₁]
          unfold rotS; rw [ppIteF h3, ppIteT h5, ppIteF (by omega)]
        · vbframe
    · refine spec_ifLtN_false (by rw [hs₁, o5]; exact h5) ?_
      by_cases hp : (s - 3 * n) % 2 < 1
      · refine spec_ifLtN_true (by rw [hb1, o1]; exact hp) ?_
        exec_block
        · config_simp; rw [hx2, o3]; omega
        · config_simp; rw [hx2, o3, o2]; omega
        refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [hx2, o3, o2]
          unfold rotS; rw [ppIteF h3, ppIteF h5, ppIteT (by omega)]; ring
        · vbframe
      · refine spec_ifLtN_false (by rw [hb1, o1]; exact hp) ?_
        exec_block
        refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [hs₁]
          unfold rotS; rw [ppIteF h3, ppIteF h5, ppIteF (by omega)]
        · vbframe

/-- **The value block of `rtS`.** -/
def vbRt : Stmt := .seq decB (.ifLtN 8740 8701
  (.ifLtN 8751 8704
    (block [.addN 8757 8711 8750, .loadN 8744 8757, .mulN 8744 8744 8706, .addN 8744 8744 8704])
    (.ifLtN 8751 8705 (block [.subN 8744 8740 8704])
      (block [.addN 8757 8712 8750, .loadN 8759 8757, .mulN 8744 8759 8706,
        .addN 8744 8744 8705])))
  (block [.copyN 8744 8740]))

theorem vbRt_exec {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (c : Config) (hc : WordsBounded W c) {K BIG s SGb PIb CVb CFb : ℕ}
    (hK : KRegs n K BIG c) (hs : c.nreg 8740 = s) (hs7 : s < 7 * n)
    (hA : RotArrs M c SGb PIb CVb CFb)
    (hW : SGb + PIb + CVb + CFb + 7 * n + 3 ≤ W) :
    ∃ c' k, Exec P W vbRt c c' k ∧ VBPost c (rtS M s) 16 c' k := by
  unfold vbRt
  refine vb_dec (B := 9) hc hK hs (fun c₁ hc₁ hd hK₁ hs₁ => ?_)
  have hA₁ := hA.congr (fun x hx => hd.fr x (Or.inl hx)) hd.m
  have o1 := hK₁.one; have o2 := hK₁.two; have o3 := hK₁.three; have o31 := hK₁.r3
  have hq := hd.q; have hr := hd.r
  have bsg := hA₁.bsg; have bpi := hA₁.bpi
  by_cases h3 : s < 3 * n
  · refine spec_ifLtN_true (by rw [hs₁, o31]; exact h3) ?_
    have hq' : s / 3 < n := by omega
    by_cases hr0 : s % 3 < 1
    · refine spec_ifLtN_true (by rw [hr, o1]; exact hr0) ?_
      have hv := hA₁.sg _ hq'
      have hv' := hA₁.sg_lt _ hq'
      exec_block
      · config_simp; rw [bsg, hq]; omega
      · config_simp; rw [bsg, hq, hv, o3]; omega
      · config_simp; rw [bsg, hq, hv, o3, o1]; omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [bsg, hq, hv, o3, o1]
        unfold rtS; rw [ppIteT h3, ppIteT (by omega)]; ring
      · vbframe
    · refine spec_ifLtN_false (by rw [hr, o1]; exact hr0) ?_
      by_cases hr1 : s % 3 < 2
      · refine spec_ifLtN_true (by rw [hr, o2]; exact hr1) ?_
        exec_block
        refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [hs₁, o1]
          unfold rtS; rw [ppIteT h3, ppIteF (by omega), ppIteT (by omega)]
        · vbframe
      · refine spec_ifLtN_false (by rw [hr, o2]; exact hr1) ?_
        have hp := hA₁.pi _ hq'
        have hp' := hA₁.pi_lt _ hq'
        exec_block
        · config_simp; rw [bpi, hq]; omega
        · config_simp; rw [bpi, hq, hp, o3]; omega
        · config_simp; rw [bpi, hq, hp, o3, o2]; omega
        refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [bpi, hq, hp, o3, o2]
          unfold rtS; rw [ppIteT h3, ppIteF (by omega), ppIteF (by omega)]; ring
        · vbframe
  · refine spec_ifLtN_false (by rw [hs₁, o31]; exact h3) ?_
    exec_block
    refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [hs₁]
      unfold rtS; rw [ppIteF h3]
    · vbframe

/-! ### Capacities, ranks, keys -/

lemma tlIn_union {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (S T : Finset V) (x : ℕ) :
    TlIn M (S ∪ T) x ↔ TlIn M S x ∨ TlIn M T x := by
  unfold TlIn
  constructor
  · rintro ⟨h, hm⟩; rcases Finset.mem_union.1 hm with h1 | h1
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨h, h1⟩
  · rintro (⟨h, h1⟩ | ⟨h, h1⟩)
    · exact ⟨h, Finset.mem_union_left _ h1⟩
    · exact ⟨h, Finset.mem_union_right _ h1⟩

/-- The per-dart arrays of the capacities and the terminals. -/
structure CapArrs {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (cpN : Fin n → ℕ) (S T : Finset V) (c : Config)
    (CPb TSb TTb : ℕ) : Prop where
  bcp : c.nreg 8716 = CPb
  bts : c.nreg 8717 = TSb
  btt : c.nreg 8718 = TTb
  cp : ∀ x < n, c.nmem (CPb + x) = xt cpN x
  ts : ∀ x < n, c.nmem (TSb + x) = fl (TlIn M S x)
  tt : ∀ x < n, c.nmem (TTb + x) = fl (TlIn M T x)

lemma CapArrs.congr {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    {M : CombMap (Fin n) V F} {cpN : Fin n → ℕ} {S T : Finset V} {c c₁ : Config} {CPb TSb TTb : ℕ}
    (h : CapArrs M cpN S T c CPb TSb TTb) (hr : ∀ x, x < 8750 → c₁.nreg x = c.nreg x)
    (hm : c₁.nmem = c.nmem) : CapArrs M cpN S T c₁ CPb TSb TTb :=
  ⟨by rw [hr _ (by omega)]; exact h.bcp, by rw [hr _ (by omega)]; exact h.bts,
    by rw [hr _ (by omega)]; exact h.btt, fun x hx => by rw [hm]; exact h.cp x hx,
    fun x hx => by rw [hm]; exact h.ts x hx, fun x hx => by rw [hm]; exact h.tt x hx⟩

/-- **The value block of `capS`.** -/
def vbCap : Stmt := .seq decB (.ifLtN 8740 8701
  (.ifLtN 8751 8704 (block [.addN 8757 8716 8750, .loadN 8744 8757]) (block [.constN 8744 0]))
  (.ifLtN 8740 8702
    (.seq (block [.addN 8757 8717 8752, .loadN 8758 8757, .addN 8757 8718 8752,
        .loadN 8759 8757, .addN 8758 8758 8759])
      (.ifLtN 8758 8704 (block [.constN 8744 0]) (block [.copyN 8744 8708])))
    (block [.constN 8744 0])))

theorem vbCap_exec {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (cpN : Fin n → ℕ) (S T : Finset V) (c : Config)
    (hc : WordsBounded W c) {K s CPb TSb TTb : ℕ}
    (hK : KRegs n K (bigN M cpN) c) (hs : c.nreg 8740 = s) (hs7 : s < 7 * n)
    (hA : CapArrs M cpN S T c CPb TSb TTb) (hW : CPb + TSb + TTb + 7 * n + 3 ≤ W) :
    ∃ c' k, Exec P W vbCap c c' k ∧ VBPost c (capS M cpN S T s) 18 c' k := by
  unfold vbCap
  refine vb_dec (B := 11) hc hK hs (fun c₁ hc₁ hd hK₁ hs₁ => ?_)
  have hA₁ := hA.congr (fun x hx => hd.fr x (Or.inl hx)) hd.m
  have o1 := hK₁.one; have o31 := hK₁.r3; have o5 := hK₁.r5; have obig := hK₁.rbig
  have hq := hd.q; have hr := hd.r; have hx1 := hd.x1
  have bcp := hA₁.bcp; have bts := hA₁.bts; have btt := hA₁.btt
  by_cases h3 : s < 3 * n
  · refine spec_ifLtN_true (by rw [hs₁, o31]; exact h3) ?_
    have hq' : s / 3 < n := by omega
    by_cases hr0 : s % 3 < 1
    · refine spec_ifLtN_true (by rw [hr, o1]; exact hr0) ?_
      have hv := hA₁.cp _ hq'
      exec_block
      · config_simp; rw [bcp, hq]; omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [bcp, hq, hv]
        unfold capS; rw [ppIteT h3, ppIteT (by omega)]
      · vbframe
    · refine spec_ifLtN_false (by rw [hr, o1]; exact hr0) ?_
      exec_block
      · omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp
        unfold capS; rw [ppIteT h3, ppIteF (by omega)]
      · vbframe
  · refine spec_ifLtN_false (by rw [hs₁, o31]; exact h3) ?_
    by_cases h5 : s < 5 * n
    · refine spec_ifLtN_true (by rw [hs₁, o5]; exact h5) ?_
      have hx' : (s - 3 * n) / 2 < n := by omega
      have h1 := hA₁.ts _ hx'
      have h2 := hA₁.tt _ hx'
      have f1 := fl_le_one (TlIn M S ((s - 3 * n) / 2))
      have f2 := fl_le_one (TlIn M T ((s - 3 * n) / 2))
      refine spec_seq ?_
      exec_block
      · config_simp; rw [bts, hx1]; omega
      · config_simp; rw [btt, hx1]; omega
      · config_simp; rw [bts, btt, hx1, h1, h2]; omega
      by_cases hf : TlIn M (S ∪ T) ((s - 3 * n) / 2)
      · have hf' : ¬ fl (TlIn M S ((s - 3 * n) / 2)) + fl (TlIn M T ((s - 3 * n) / 2)) < 1 := by
          rcases (tlIn_union M S T _).1 hf with h | h
          · have := (fl_lt_one (p := TlIn M S ((s - 3 * n) / 2))).not.2 (not_not.2 h); omega
          · have := (fl_lt_one (p := TlIn M T ((s - 3 * n) / 2))).not.2 (not_not.2 h); omega
        refine spec_ifLtN_false ?_ ?_
        · config_simp; rw [bts, btt, hx1, h1, h2, o1]; exact hf'
        exec_block
        refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; rw [obig]
          unfold capS; rw [ppIteF h3, ppIteT h5, ppIteT hf]
        · vbframe
      · have hf' : fl (TlIn M S ((s - 3 * n) / 2)) + fl (TlIn M T ((s - 3 * n) / 2)) < 1 := by
          have a1 := (fl_lt_one (p := TlIn M S ((s - 3 * n) / 2))).2
            (fun h => hf ((tlIn_union M S T _).2 (Or.inl h)))
          have a2 := (fl_lt_one (p := TlIn M T ((s - 3 * n) / 2))).2
            (fun h => hf ((tlIn_union M S T _).2 (Or.inr h)))
          omega
        refine spec_ifLtN_true ?_ ?_
        · config_simp; rw [bts, btt, hx1, h1, h2, o1]; exact hf'
        exec_block
        · omega
        refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp
          unfold capS; rw [ppIteF h3, ppIteT h5, ppIteF hf]
        · vbframe
    · refine spec_ifLtN_false (by rw [hs₁, o5]; exact h5) ?_
      exec_block
      · omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp
        unfold capS; rw [ppIteF h3, ppIteF h5]
      · vbframe

/-- **The value block of `krS`.** -/
def vbKr : Stmt := .seq decB (.ifLtN 8740 8701 (block [.constN 8744 3])
  (.ifLtN 8740 8702
    (.ifLtN 8753 8704 (block [.constN 8744 3])
      (.seq (block [.addN 8757 8717 8752, .loadN 8758 8757])
        (.ifLtN 8758 8704
          (.seq (block [.addN 8757 8718 8752, .loadN 8758 8757])
            (.ifLtN 8758 8704 (block [.constN 8744 3]) (block [.constN 8744 2])))
          (block [.constN 8744 0]))))
    (block [.constN 8744 3])))

theorem vbKr_exec {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (cpN : Fin n → ℕ) (S T : Finset V) (c : Config)
    (hc : WordsBounded W c) {K BIG s CPb TSb TTb : ℕ}
    (hK : KRegs n K BIG c) (hs : c.nreg 8740 = s) (hs7 : s < 7 * n)
    (hA : CapArrs M cpN S T c CPb TSb TTb) (hW : CPb + TSb + TTb + 7 * n + 3 ≤ W) :
    ∃ c' k, Exec P W vbKr c c' k ∧ VBPost c (krS M S T s) 20 c' k := by
  unfold vbKr
  refine vb_dec (B := 13) hc hK hs (fun c₁ hc₁ hd hK₁ hs₁ => ?_)
  have hA₁ := hA.congr (fun x hx => hd.fr x (Or.inl hx)) hd.m
  have o1 := hK₁.one; have o31 := hK₁.r3; have o5 := hK₁.r5
  have hb1 := hd.b1; have hx1 := hd.x1
  have bts := hA₁.bts; have btt := hA₁.btt
  have h3 : ∀ v, v ≤ 3 → v ≤ W := fun v hv => by omega
  by_cases h3n : s < 3 * n
  · refine spec_ifLtN_true (by rw [hs₁, o31]; exact h3n) ?_
    exec_block
    · omega
    refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; unfold krS; rw [ppIteF (by omega)]
    · vbframe
  · refine spec_ifLtN_false (by rw [hs₁, o31]; exact h3n) ?_
    by_cases h5 : s < 5 * n
    · refine spec_ifLtN_true (by rw [hs₁, o5]; exact h5) ?_
      by_cases hp : (s - 3 * n) % 2 < 1
      · refine spec_ifLtN_true (by rw [hb1, o1]; exact hp) ?_
        exec_block
        · omega
        refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
        · config_simp; unfold krS; rw [ppIteF (by omega)]
        · vbframe
      · refine spec_ifLtN_false (by rw [hb1, o1]; exact hp) ?_
        have hx' : (s - 3 * n) / 2 < n := by omega
        have e1 := hA₁.ts _ hx'
        have e2 := hA₁.tt _ hx'
        have hc3 : 3 * n ≤ s ∧ s < 5 * n ∧ (s - 3 * n) % 2 = 1 := ⟨by omega, h5, by omega⟩
        refine spec_seq ?_
        exec_block
        · config_simp; rw [bts, hx1]; omega
        by_cases hS : TlIn M S ((s - 3 * n) / 2)
        · refine spec_ifLtN_false ?_ ?_
          · config_simp; rw [bts, hx1, e1, o1, fl_lt_one]; exact not_not.2 hS
          exec_block
          · omega
          refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
          · config_simp; unfold krS; rw [ppIteT hc3, ppIteT hS]
          · vbframe
        · refine spec_ifLtN_true ?_ ?_
          · config_simp; rw [bts, hx1, e1, o1, fl_lt_one]; exact hS
          refine spec_seq ?_
          exec_block
          · config_simp; rw [btt, hx1]; omega
          by_cases hT : TlIn M T ((s - 3 * n) / 2)
          · refine spec_ifLtN_false ?_ ?_
            · config_simp; rw [btt, hx1, e2, o1, fl_lt_one]; exact not_not.2 hT
            exec_block
            · omega
            refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
            · config_simp; unfold krS; rw [ppIteT hc3, ppIteF hS, ppIteT hT]
            · vbframe
          · refine spec_ifLtN_true ?_ ?_
            · config_simp; rw [btt, hx1, e2, o1, fl_lt_one]; exact hT
            exec_block
            · omega
            refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
            · config_simp; unfold krS; rw [ppIteT hc3, ppIteF hS, ppIteF hT]
            · vbframe
    · refine spec_ifLtN_false (by rw [hs₁, o5]; exact h5) ?_
      exec_block
      · omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; unfold krS; rw [ppIteF (by omega)]
      · vbframe

/-- The per-dart arrays of the keys: the face labels and the numbers of the tails. -/
structure KeyArrs {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (vn : V → ℕ) (K : ℕ) (c : Config) (FLb VTb : ℕ) : Prop where
  bfl : c.nreg 8715 = FLb
  bvt : c.nreg 8719 = VTb
  fl : ∀ x < n, c.nmem (FLb + x) = flI M x
  vt : ∀ x < n, c.nmem (VTb + x) = xt (fun d => vn (M.tail d)) x
  fl_lt : ∀ x < n, flI M x < n
  vt_lt : ∀ x < n, xt (fun d => vn (M.tail d)) x < K

lemma KeyArrs.congr {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    {M : CombMap (Fin n) V F} {vn : V → ℕ} {K : ℕ} {c c₁ : Config} {FLb VTb : ℕ}
    (h : KeyArrs M vn K c FLb VTb) (hr : ∀ x, x < 8750 → c₁.nreg x = c.nreg x)
    (hm : c₁.nmem = c.nmem) : KeyArrs M vn K c₁ FLb VTb :=
  ⟨by rw [hr _ (by omega)]; exact h.bfl, by rw [hr _ (by omega)]; exact h.bvt,
    fun x hx => by rw [hm]; exact h.fl x hx, fun x hx => by rw [hm]; exact h.vt x hx,
    h.fl_lt, h.vt_lt⟩

/-- **The value block of `keyS`.** -/
def vbKey : Stmt := .seq decB (.ifLtN 8740 8701
  (.ifLtN 8751 8705
    (block [.addN 8757 8719 8750, .loadN 8744 8757, .mulN 8744 8744 8705])
    (block [.addN 8757 8715 8750, .loadN 8744 8757, .addN 8744 8744 8707, .mulN 8744 8744 8705]))
  (.ifLtN 8740 8702
    (block [.addN 8757 8719 8752, .loadN 8744 8757, .mulN 8744 8744 8705, .addN 8744 8744 8753])
    (block [.addN 8744 8707 8754, .mulN 8744 8744 8705, .addN 8744 8744 8753])))

theorem vbKey_exec {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (vn : V → ℕ) (c : Config) (hc : WordsBounded W c)
    {K BIG s FLb VTb : ℕ} (hK : KRegs n K BIG c) (hs : c.nreg 8740 = s) (hs7 : s < 7 * n)
    (hA : KeyArrs M vn K c FLb VTb) (hW : FLb + VTb + 2 * K + 14 * n + 3 ≤ W) :
    ∃ c' k, Exec P W vbKey c c' k ∧ VBPost c (keyS M vn K s) 14 c' k := by
  unfold vbKey
  refine vb_dec (B := 7) hc hK hs (fun c₁ hc₁ hd hK₁ hs₁ => ?_)
  have hA₁ := hA.congr (fun x hx => hd.fr x (Or.inl hx)) hd.m
  have o1 := hK₁.one; have o2 := hK₁.two; have o31 := hK₁.r3; have o5 := hK₁.r5
  have ok := hK₁.rk
  have hq := hd.q; have hr := hd.r; have hb1 := hd.b1; have hx1 := hd.x1; have hx2 := hd.x2
  have bfl := hA₁.bfl; have bvt := hA₁.bvt
  by_cases h3 : s < 3 * n
  · refine spec_ifLtN_true (by rw [hs₁, o31]; exact h3) ?_
    have hq' : s / 3 < n := by omega
    by_cases hr1 : s % 3 < 2
    · refine spec_ifLtN_true (by rw [hr, o2]; exact hr1) ?_
      have hv := hA₁.vt _ hq'
      have hv' := hA₁.vt_lt _ hq'
      exec_block
      · config_simp; rw [bvt, hq]; omega
      · config_simp; rw [bvt, hq, hv, o2]; omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [bvt, hq, hv, o2]
        unfold keyS; rw [ppIteT h3, ppIteF (by omega)]; ring
      · vbframe
    · refine spec_ifLtN_false (by rw [hr, o2]; exact hr1) ?_
      have hv := hA₁.fl _ hq'
      have hv' := hA₁.fl_lt _ hq'
      exec_block
      · config_simp; rw [bfl, hq]; omega
      · config_simp; rw [bfl, hq, hv, ok]; omega
      · config_simp; rw [bfl, hq, hv, ok, o2]; omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [bfl, hq, hv, ok, o2]
        unfold keyS; rw [ppIteT h3, ppIteT (by omega)]; ring
      · vbframe
  · refine spec_ifLtN_false (by rw [hs₁, o31]; exact h3) ?_
    by_cases h5 : s < 5 * n
    · refine spec_ifLtN_true (by rw [hs₁, o5]; exact h5) ?_
      have hx' : (s - 3 * n) / 2 < n := by omega
      have hv := hA₁.vt _ hx'
      have hv' := hA₁.vt_lt _ hx'
      exec_block
      · config_simp; rw [bvt, hx1]; omega
      · config_simp; rw [bvt, hx1, hv, o2]; omega
      · config_simp; rw [bvt, hx1, hv, o2, hb1]; omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [bvt, hx1, hv, o2, hb1]
        unfold keyS; rw [ppIteF h3, ppIteT h5]; ring
      · vbframe
    · refine spec_ifLtN_false (by rw [hs₁, o5]; exact h5) ?_
      exec_block
      · config_simp; rw [ok, hx2]; omega
      · config_simp; rw [ok, hx2, o2]; omega
      · config_simp; rw [ok, hx2, o2, hb1]; omega
      refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [ok, hx2, o2, hb1]
        unfold keyS; rw [ppIteF h3, ppIteF h5, show (s - 3 * n) % 2 = (s - 5 * n) % 2 by omega]
        ring
      · vbframe

/-! ### The sort items -/

section Item

variable {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
  (M : CombMap (Fin n) V F)

open Classical in
/-- **The sort key of a slot**: its key if it is valid, `KM` otherwise. -/
noncomputable def kapS (vn : V → ℕ) (K KM s : ℕ) : ℕ := if ValidS M s then keyS M vn K s else KM

/-- **The sort item of a slot**: its sort key times `7 n`, plus the slot. -/
noncomputable def itS (vn : V → ℕ) (K KM s : ℕ) : ℕ := kapS M vn K KM s * (7 * n) + s

/-- The arrays read by the value block of the items. -/
structure ItArrs (vn : V → ℕ) (K : ℕ) (c : Config) (KYb NLb CVb CFb KM : ℕ) : Prop where
  bky : c.nreg 8721 = KYb
  bnl : c.nreg 8720 = NLb
  bcv : c.nreg 8713 = CVb
  bcf : c.nreg 8714 = CFb
  km : c.nreg 8709 = KM
  ky : ∀ s < 7 * n, c.nmem (KYb + s) = keyS M vn K s
  nl : ∀ x < n, c.nmem (NLb + x) = fl (IsNl M x)
  cv : ∀ x < n, c.nmem (CVb + x) = fl (CvI M x)
  cf : ∀ x < n, c.nmem (CFb + x) = fl (CfI M x)

variable {M}

lemma ItArrs.congr {vn : V → ℕ} {K : ℕ} {c c₁ : Config} {KYb NLb CVb CFb KM : ℕ}
    (h : ItArrs M vn K c KYb NLb CVb CFb KM) (hr : ∀ x, x < 8750 → c₁.nreg x = c.nreg x)
    (hm : c₁.nmem = c.nmem) : ItArrs M vn K c₁ KYb NLb CVb CFb KM :=
  ⟨by rw [hr _ (by omega)]; exact h.bky, by rw [hr _ (by omega)]; exact h.bnl,
    by rw [hr _ (by omega)]; exact h.bcv, by rw [hr _ (by omega)]; exact h.bcf,
    by rw [hr _ (by omega)]; exact h.km,
    fun x hx => by rw [hm]; exact h.ky x hx, fun x hx => by rw [hm]; exact h.nl x hx,
    fun x hx => by rw [hm]; exact h.cv x hx, fun x hx => by rw [hm]; exact h.cf x hx⟩

end Item

/-- The validity flag of the slot into `8758`. -/
def itFlag : Stmt := .ifLtN 8740 8701 (block [.addN 8757 8720 8750, .loadN 8758 8757])
  (.ifLtN 8740 8702 (block [.addN 8757 8713 8752, .loadN 8758 8757])
    (block [.addN 8757 8714 8754, .loadN 8758 8757]))

/-- The item from the key and the flag. -/
def itFin : Stmt := .seq (block [.addN 8757 8721 8740, .loadN 8745 8757])
  (.seq (.ifLtN 8758 8704 (block [.copyN 8746 8709]) (block [.copyN 8746 8745]))
    (block [.mulN 8744 8746 8703, .addN 8744 8744 8740]))

/-- **The value block of the items** (the keys `KY` computed before). -/
def vbItem : Stmt := .seq decB (.seq itFlag itFin)

theorem itFlag_exec {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (vn : V → ℕ) (c₁ : Config) (hc₁ : WordsBounded W c₁)
    {K BIG s KYb NLb CVb CFb KM : ℕ} (hK₁ : KRegs n K BIG c₁) (hs₁ : c₁.nreg 8740 = s)
    (hs7 : s < 7 * n) (hd : c₁.nreg 8750 = s / 3 ∧ c₁.nreg 8752 = (s - 3 * n) / 2 ∧
      c₁.nreg 8754 = (s - 5 * n) / 2) (hA₁ : ItArrs M vn K c₁ KYb NLb CVb CFb KM)
    (hW : NLb + CVb + CFb + 7 * n ≤ W) :
    ∃ c₂ k, Exec P W itFlag c₁ c₂ k ∧ k ≤ 6 ∧ c₂.nreg 8758 = fl (ValidS M s) ∧
      (∀ x, x ≠ 8757 → x ≠ 8758 → c₂.nreg x = c₁.nreg x) ∧ c₂.nmem = c₁.nmem ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
  obtain ⟨hq, hx1, hx2⟩ := hd
  have o31 := hK₁.r3; have o5 := hK₁.r5
  have bnl := hA₁.bnl; have bcv := hA₁.bcv; have bcf := hA₁.bcf
  unfold itFlag
  by_cases h3 : s < 3 * n
  · refine spec_ifLtN_true (by rw [hs₁, o31]; exact h3) ?_
    have hq' : s / 3 < n := by omega
    have hv := hA₁.nl _ hq'
    have hvf : fl (IsNl M (s / 3)) = fl (ValidS M s) := by
      congr 1; apply propext; unfold ValidS
      constructor
      · intro h; exact Or.inl ⟨h3, h⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        · exact h
        · omega
        · omega
    exec_block
    · config_simp; rw [bnl, hq]; omega
    refine ⟨by omega, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [bnl, hq, hv, hvf]
    · config_simp; simp (disch := omega) only [upd_other]
  · refine spec_ifLtN_false (by rw [hs₁, o31]; exact h3) ?_
    by_cases h5 : s < 5 * n
    · refine spec_ifLtN_true (by rw [hs₁, o5]; exact h5) ?_
      have hx' : (s - 3 * n) / 2 < n := by omega
      have hv := hA₁.cv _ hx'
      have hvf : fl (CvI M ((s - 3 * n) / 2)) = fl (ValidS M s) := by
        congr 1; apply propext; unfold ValidS
        constructor
        · intro h; exact Or.inr (Or.inl ⟨by omega, h5, h⟩)
        · rintro (⟨h, -⟩ | ⟨-, -, h⟩ | ⟨h, -⟩)
          · omega
          · exact h
          · omega
      exec_block
      · config_simp; rw [bcv, hx1]; omega
      refine ⟨by omega, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [bcv, hx1, hv, hvf]
      · config_simp; simp (disch := omega) only [upd_other]
    · refine spec_ifLtN_false (by rw [hs₁, o5]; exact h5) ?_
      have hx' : (s - 5 * n) / 2 < n := by omega
      have hv := hA₁.cf _ hx'
      have hvf : fl (CfI M ((s - 5 * n) / 2)) = fl (ValidS M s) := by
        congr 1; apply propext; unfold ValidS
        constructor
        · intro h; exact Or.inr (Or.inr ⟨by omega, hs7, h⟩)
        · rintro (⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩)
          · omega
          · omega
          · exact h
      exec_block
      · config_simp; rw [bcf, hx2]; omega
      refine ⟨by omega, ?_, fun x h1 h2 => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; rw [bcf, hx2, hv, hvf]
      · config_simp; simp (disch := omega) only [upd_other]

theorem itFin_exec {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (vn : V → ℕ) (d : Config) (hd : WordsBounded W d)
    {K s KYb KM : ℕ} (d58 : d.nreg 8758 = fl (ValidS M s)) (d40 : d.nreg 8740 = s)
    (d04 : d.nreg 8704 = 1) (d09 : d.nreg 8709 = KM) (d03 : d.nreg 8703 = 7 * n)
    (d21 : d.nreg 8721 = KYb) (hky : d.nmem (KYb + s) = keyS M vn K s) (hs7 : s < 7 * n)
    (hkey : keyS M vn K s ≤ KM) (hW : KYb + (KM + 1) * (7 * n) + 3 ≤ W) :
    ∃ c' k, Exec P W itFin d c' k ∧ k ≤ 7 ∧ c'.nreg 8744 = itS M vn K KM s ∧
      (∀ x, ¬ pscr x → c'.nreg x = d.nreg x) ∧ c'.nmem = d.nmem ∧
      c'.rreg = d.rreg ∧ c'.rmem = d.rmem ∧ c'.output = d.output := by
  have hmul : (KM + 1) * (7 * n) = KM * (7 * n) + 7 * n := by ring
  have hkm : keyS M vn K s * (7 * n) ≤ KM * (7 * n) := Nat.mul_le_mul_right _ hkey
  unfold itFin
  refine spec_seq ?_
  exec_block
  · config_simp; rw [d21, d40]; omega
  refine spec_seq ?_
  by_cases hv : ValidS M s
  · have h1 : ¬ d.nreg 8758 < d.nreg 8704 := by rw [d58, d04, fl_lt_one]; exact not_not.2 hv
    refine spec_ifLtN_false (by config_simp; exact h1) ?_
    exec_block
    · config_simp; rw [d21, d40, hky, d03]; omega
    · config_simp; rw [d21, d40, hky, d03]; omega
    refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [d21, d40, hky, d03]; unfold itS kapS; rw [ppIteT hv]
    · vbframe
  · have h1 : d.nreg 8758 < d.nreg 8704 := by rw [d58, d04, fl_lt_one]; exact hv
    refine spec_ifLtN_true (by config_simp; exact h1) ?_
    exec_block
    · config_simp; rw [d09, d03]; omega
    · config_simp; rw [d09, d03, d40]; omega
    refine ⟨by omega, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; rw [d09, d03, d40]; unfold itS kapS; rw [ppIteF hv]
    · vbframe

theorem vbItem_exec {n : ℕ} {V F : Type} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F]
    (M : CombMap (Fin n) V F) (vn : V → ℕ) (c : Config) (hc : WordsBounded W c)
    {K BIG s KYb NLb CVb CFb KM : ℕ} (hK : KRegs n K BIG c) (hs : c.nreg 8740 = s)
    (hs7 : s < 7 * n) (hA : ItArrs M vn K c KYb NLb CVb CFb KM)
    (hkey : keyS M vn K s ≤ KM) (hW : KYb + NLb + CVb + CFb + (KM + 1) * (7 * n) + 3 ≤ W) :
    ∃ c' k, Exec P W vbItem c c' k ∧ VBPost c (itS M vn K KM s) 20 c' k := by
  unfold vbItem
  refine vb_dec (B := 13) hc hK hs (fun c₁ hc₁ hd hK₁ hs₁ => ?_)
  have hA₁ := hA.congr (fun x hx => hd.fr x (Or.inl hx)) hd.m
  have h7 : 7 * n ≤ (KM + 1) * (7 * n) := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨c₂, k₂, e₂, hk₂, f58, fr2, m2, rr2, rm2, o2⟩ := itFlag_exec M vn c₁ hc₁ hK₁ hs₁ hs7
    ⟨hd.q, hd.x1, hd.x2⟩ hA₁ (by omega)
  obtain ⟨c₃, k₃, e₃, hk₃, v3, fr3, m3, rr3, rm3, o3⟩ := itFin_exec M vn c₂ e₂.wb_right f58
    (by rw [fr2 _ (by omega) (by omega), hs₁]) (by rw [fr2 _ (by omega) (by omega), hK₁.one])
    (by rw [fr2 _ (by omega) (by omega), hA₁.km]) (by rw [fr2 _ (by omega) (by omega), hK₁.r7])
    (by rw [fr2 _ (by omega) (by omega), hA₁.bky]) (by rw [m2]; exact hA₁.ky s hs7) hs7 hkey
    (by omega)
  refine ⟨c₃, k₂ + k₃, .seq e₂ e₃, by omega, v3, fun x hx => ?_, by rw [m3, m2],
    by rw [rr3, rr2], by rw [rm3, rm2], by rw [o3, o2]⟩
  rw [fr3 x hx, fr2 x (by unfold pscr at hx; omega) (by unfold pscr at hx; omega)]

end Pp

end BKMNW

end PlanarFlow
