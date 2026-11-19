module

public import PlanarFlow.BKMNW.KeepProg
public import PlanarFlow.BKMNW.ScertLoop
public import PlanarFlow.BKMNW.ClsProg

/-!
# The preparation of a hole test on the machine

Before the cut-vertex test of the hole `g = Hs[j]` (`cutProg_cutH`) at a level of `scertD`, the
inputs of `ccProg` are written from the per-index arrays of the piece (an enumeration `e` of a
superset `B` of the current darts `N`): the flags `NF[i] ≠ 0 ↔ e i ∈ N`, the hole numbers
`TH[i] = j + 1 ↔ tail (e i) ∈ Hs[j]` and the reverse indices `RV0` of `B`. One branch-free scan
writes

* `YF[i] = 1 - [e i ∈ N] + [tail ∈ g]` (nonzero iff `tail ∈ g ∨ e i ∉ N`),
* `GN[i] = [e i ∈ N] · [tail ∉ g]`,
* `RV[i] = RV0[i]` if `e i, rev (e i) ∈ N`, else `i` (the darts outside `N` isolated),
* `LAB[i] = 0`, `LS[i] = 0` (the arrays `ccProg` needs zeroed; class keys `< n`).

* `phA` (16 instrs), `phB` (18 instrs), **`phProg`** (registers `4840 = n`, `4841 = NFb`,
  `4842 = THb`, `4843 = RV0b`, `4845 = J1`, `4846 = YFb`, `4847 = GNb`, `4848 = RVb`,
  `4849 = LABb`, `4866 = LSb`; written `4853 … 4865`), **`phProg_exec`** (`36 n + 5` steps);
* **`phProg_cg`**: the arrays meet `CgEnumSub M B N Hs g n e RV TK YF`, the flags `GN` of
  `cutProg_cutH`, and `LAB`, `LS` are zero.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset Relation WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The values, purely -/

/-- `[th ≠ J1]`. -/
def phNe (th J1 : ℕ) : ℕ := (th - J1 + (J1 - th)) / (th - J1 + (J1 - th))

/-- The flag `YF`: `1 - [nf ≠ 0] + [th = J1]`. -/
def phYF (nf th J1 : ℕ) : ℕ := 1 - nf / nf + (1 - phNe th J1)

/-- The flag `GN`: `[nf ≠ 0] · [th ≠ J1]`. -/
def phGN (nf th J1 : ℕ) : ℕ := nf / nf * phNe th J1

/-- The pair flag `[nfr ≠ 0] · [nf ≠ 0]`. -/
def phB (nf nfr : ℕ) : ℕ := nfr / nfr * (nf / nf)

/-- The reverse slot: `rv` on a pair inside `N`, else `i`. -/
def phRV (nf nfr rv i : ℕ) : ℕ := phB nf nfr * rv + (1 - phB nf nfr) * i

lemma phNe_eq (th J1 : ℕ) : phNe th J1 = if th = J1 then 0 else 1 := ne_sgn th J1

lemma phYF_pos (nf th J1 : ℕ) : 0 < phYF nf th J1 ↔ (th = J1 ∨ nf = 0) := by
  unfold phYF; rw [phNe_eq, sgn_eq]; split_ifs <;> omega

lemma phGN_ne (nf th J1 : ℕ) : phGN nf th J1 ≠ 0 ↔ (nf ≠ 0 ∧ th ≠ J1) := by
  unfold phGN; rw [phNe_eq, sgn_eq]; split_ifs <;> simp_all

lemma phB_le (nf nfr : ℕ) : phB nf nfr ≤ 1 := by
  unfold phB; rw [sgn_eq, sgn_eq]; split_ifs <;> omega

lemma phRV_eq (nf nfr rv i : ℕ) : phRV nf nfr rv i = if nf ≠ 0 ∧ nfr ≠ 0 then rv else i := by
  unfold phRV phB; rw [sgn_eq, sgn_eq]; split_ifs <;> simp_all

lemma phRV_le (nf nfr rv i : ℕ) : phRV nf nfr rv i ≤ rv + i := by
  rw [phRV_eq]; split_ifs <;> omega

/-! ### The program -/

/-- The flags of index `i` (`4853 = 1`, `4854 = i`): `4855 = [nf ≠ 0]`, `4857 = [th ≠ J1]`,
`4858 = [th = J1]`, `4859 = rv`, `4860 = [nf ≠ 0 ∧ nf[rv] ≠ 0]`. -/
def phA : Stmt :=
  block [.addN 4855 4841 4854, .loadN 4855 4855, .divN 4855 4855 4855,
    .addN 4856 4842 4854, .loadN 4856 4856,
    .subN 4857 4856 4845, .subN 4858 4845 4856, .addN 4857 4857 4858, .divN 4857 4857 4857,
    .subN 4858 4853 4857,
    .addN 4859 4843 4854, .loadN 4859 4859,
    .addN 4860 4841 4859, .loadN 4860 4860, .divN 4860 4860 4860, .mulN 4860 4860 4855]

/-- The writes of index `i` (`4865 = 0`). -/
def phB' : Stmt :=
  block [.subN 4862 4853 4855, .addN 4862 4862 4858, .addN 4863 4846 4854, .storeN 4863 4862,
    .mulN 4862 4855 4857, .addN 4863 4847 4854, .storeN 4863 4862,
    .mulN 4862 4860 4859, .subN 4864 4853 4860, .mulN 4864 4864 4854, .addN 4862 4862 4864,
    .addN 4863 4848 4854, .storeN 4863 4862,
    .addN 4863 4849 4854, .storeN 4863 4865,
    .addN 4863 4866 4854, .storeN 4863 4865,
    .addN 4854 4854 4853]

/-- **The preparation of a hole test.** -/
def phProg : Stmt :=
  .seq (block [.constN 4853 1, .constN 4854 0, .constN 4865 0])
    (.whileLtN 4854 4840 (.seq phA phB'))

section Exec

variable {P : Input} {W : ℕ}

theorem phA_exec (c : Config) (hc : WordsBounded W c) {NFb THb RV0b J1 i : ℕ}
    (r1 : c.nreg 4841 = NFb) (r2 : c.nreg 4842 = THb) (r3 : c.nreg 4843 = RV0b)
    (r5 : c.nreg 4845 = J1) (r6 : c.nreg 4853 = 1) (r7 : c.nreg 4854 = i)
    (w1 : NFb + i ≤ W) (w2 : THb + i ≤ W) (w3 : RV0b + i ≤ W)
    (w4 : NFb + c.nmem (RV0b + i) ≤ W) (w5 : 1 ≤ W) :
    ∃ c' t, Exec P W phA c c' t ∧ t = 16 ∧
      c'.nreg 4855 = c.nmem (NFb + i) / c.nmem (NFb + i) ∧
      c'.nreg 4857 = phNe (c.nmem (THb + i)) J1 ∧
      c'.nreg 4858 = 1 - phNe (c.nmem (THb + i)) J1 ∧
      c'.nreg 4859 = c.nmem (RV0b + i) ∧
      c'.nreg 4860 = phB (c.nmem (NFb + i)) (c.nmem (NFb + c.nmem (RV0b + i))) ∧
      (∀ x, (x < 4855 ∨ 4860 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hth := hc.2 (THb + i)
  have hJ := hc.1 4845
  rw [r5] at hJ
  have hb := phB_le (c.nmem (NFb + i)) (c.nmem (NFb + c.nmem (RV0b + i)))
  have hne : (c.nmem (THb + i) - J1 + (J1 - c.nmem (THb + i))) /
      (c.nmem (THb + i) - J1 + (J1 - c.nmem (THb + i))) = phNe (c.nmem (THb + i)) J1 := rfl
  have hbb : c.nmem (NFb + c.nmem (RV0b + i)) / c.nmem (NFb + c.nmem (RV0b + i)) *
      (c.nmem (NFb + i) / c.nmem (NFb + i)) =
      phB (c.nmem (NFb + i)) (c.nmem (NFb + c.nmem (RV0b + i))) := rfl
  unfold phA
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r5, r6, r7, hne, hbb]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; simp only [r1, r2, r3, r5, r6, r7, hne, hbb]; done)
  · obtain ⟨a1, a2, a3, a4, a5, a6⟩ : x ≠ 4855 ∧ x ≠ 4856 ∧ x ≠ 4857 ∧ x ≠ 4858 ∧
        x ≠ 4859 ∧ x ≠ 4860 := by omega
    simp only [Config.nreg_mk, upd_other _ _ _ a1, upd_other _ _ _ a2, upd_other _ _ _ a3,
      upd_other _ _ _ a4, upd_other _ _ _ a5, upd_other _ _ _ a6]

theorem phB'_exec (c : Config) (hc : WordsBounded W c) {YFb GNb RVb LABb LSb i a b ne rv : ℕ}
    (r6 : c.nreg 4846 = YFb) (r7 : c.nreg 4847 = GNb) (r8 : c.nreg 4848 = RVb)
    (r9 : c.nreg 4849 = LABb) (r10 : c.nreg 4866 = LSb) (r11 : c.nreg 4853 = 1)
    (r12 : c.nreg 4854 = i) (r13 : c.nreg 4865 = 0) (q1 : c.nreg 4855 = a)
    (q2 : c.nreg 4857 = ne) (q3 : c.nreg 4858 = 1 - ne) (q4 : c.nreg 4859 = rv)
    (q5 : c.nreg 4860 = b) (ha : a ≤ 1) (hne : ne ≤ 1) (hb : b ≤ 1)
    (w1 : YFb + i ≤ W) (w2 : GNb + i ≤ W) (w3 : RVb + i ≤ W) (w4 : LABb + i ≤ W)
    (w5 : LSb + i ≤ W) (w6 : rv + i + 2 ≤ W) :
    ∃ c' t, Exec P W phB' c c' t ∧ t = 18 ∧ c'.nreg 4854 = i + 1 ∧
      c'.nmem = upd (upd (upd (upd (upd c.nmem (YFb + i) (1 - a + (1 - ne))) (GNb + i)
        (a * ne)) (RVb + i) (b * rv + (1 - b) * i)) (LABb + i) 0) (LSb + i) 0 ∧
      (∀ x, x ≠ 4854 → x ≠ 4862 → x ≠ 4863 → x ≠ 4864 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hbr : b * rv ≤ rv := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h <;> simp [h]
  have hbi : (1 - b) * i ≤ i := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with h | h <;> simp [h]
  have han : a * ne ≤ 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ha with h | h <;> simp [h] <;> omega
  unfold phB'
  exec_block
  all_goals try (config_simp; simp only [r6, r7, r8, r9, r10, r11, r12, r13, q1, q2, q3, q4, q5]; omega)
  refine ⟨rfl, ?_, ?_, fun x h1 h2 h3 h4 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r11, r12]
  · config_simp; simp only [r6, r7, r8, r9, r10, r11, r12, r13, q1, q2, q3, q4, q5]
  · simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3,
      upd_other _ _ _ h4]

/-- **The preparation scan on the machine**: within `36 n + 5` steps `YF[i] = phYF NF[i] TH[i]
J1`, `GN[i] = phGN …`, `RV[i] = phRV NF[i] NF[RV0[i]] RV0[i] i`, `LAB[i] = LS[i] = 0`; memory
outside the five output arrays, registers outside `4853 … 4865`, reals and output kept. -/
theorem phProg_exec (c : Config) (hc : WordsBounded W c)
    {n NFb THb RV0b J1 YFb GNb RVb LABb LSb : ℕ}
    (r0 : c.nreg 4840 = n) (r1 : c.nreg 4841 = NFb) (r2 : c.nreg 4842 = THb)
    (r3 : c.nreg 4843 = RV0b) (r5 : c.nreg 4845 = J1) (r6 : c.nreg 4846 = YFb)
    (r7 : c.nreg 4847 = GNb) (r8 : c.nreg 4848 = RVb) (r9 : c.nreg 4849 = LABb)
    (r10 : c.nreg 4866 = LSb)
    (hrv : ∀ i < n, c.nmem (RV0b + i) < n)
    (lay : NFb + n ≤ GNb ∧ THb + n ≤ GNb ∧ RV0b + n ≤ GNb ∧ GNb + n ≤ RVb ∧ RVb + n ≤ YFb ∧
      YFb + n ≤ LSb ∧ LSb + n ≤ LABb ∧ LABb + n ≤ W ∧ 2 * n + 2 ≤ W) :
    ∃ c' t, Exec P W phProg c c' t ∧ t ≤ 36 * n + 5 ∧
      (∀ i < n, c'.nmem (YFb + i) = phYF (c.nmem (NFb + i)) (c.nmem (THb + i)) J1) ∧
      (∀ i < n, c'.nmem (GNb + i) = phGN (c.nmem (NFb + i)) (c.nmem (THb + i)) J1) ∧
      (∀ i < n, c'.nmem (RVb + i) =
        phRV (c.nmem (NFb + i)) (c.nmem (NFb + c.nmem (RV0b + i))) (c.nmem (RV0b + i)) i) ∧
      (∀ i < n, c'.nmem (LABb + i) = 0) ∧ (∀ i < n, c'.nmem (LSb + i) = 0) ∧
      (∀ a, ¬ (YFb ≤ a ∧ a < YFb + n) → ¬ (GNb ≤ a ∧ a < GNb + n) →
        ¬ (RVb ≤ a ∧ a < RVb + n) → ¬ (LABb ≤ a ∧ a < LABb + n) →
        ¬ (LSb ≤ a ∧ a < LSb + n) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4853 ∨ 4865 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9⟩ := lay
  unfold phProg
  obtain ⟨c₁, k₁, e₁, hk₁, g3, g4, g5, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 4853 1, .constN 4854 0, .constN 4865 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 4853 = 1 ∧ c₁.nreg 4854 = 0 ∧ c₁.nreg 4865 = 0 ∧
      (∀ x, x ≠ 4853 → x ≠ 4854 → x ≠ 4865 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x h1 h2 h3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    simp only [Config.nreg_mk, upd_other _ _ _ h1, upd_other _ _ _ h2, upd_other _ _ _ h3]
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 4853 ∨ 4865 < x) → c₁.nreg x = c.nreg x := fun x hx =>
    gn₁ x (by omega) (by omega) (by omega)
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 4854 ∨ 4865 < x ∨ x = 4865) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (YFb + j) = phYF (m₀ (NFb + j)) (m₀ (THb + j)) J1) ∧
    (∀ j < i, c'.nmem (GNb + j) = phGN (m₀ (NFb + j)) (m₀ (THb + j)) J1) ∧
    (∀ j < i, c'.nmem (RVb + j) = phRV (m₀ (NFb + j)) (m₀ (NFb + m₀ (RV0b + j))) (m₀ (RV0b + j)) j) ∧
    (∀ j < i, c'.nmem (LABb + j) = 0) ∧ (∀ j < i, c'.nmem (LSb + j) = 0) ∧
    (∀ a, ¬ (YFb ≤ a ∧ a < YFb + i) → ¬ (GNb ≤ a ∧ a < GNb + i) →
      ¬ (RVb ≤ a ∧ a < RVb + i) → ¬ (LABb ≤ a ∧ a < LABb + i) →
      ¬ (LSb ≤ a ∧ a < LSb + i) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h54, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10⟩ := tgRange (P := P)
    (a := 4854) (b := 4840) (body := .seq phA phB') J (B := 34) c₁ hw₁ g4
    (by rw [q _ (by omega), r0]) (Nat.zero_le n)
    ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), fun j hj => absurd hj (by omega),
      fun j hj => absurd hj (by omega), fun a _ _ _ _ _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h54 h40 ⟨j1, j2, j3, j4, j5, j6, j7, j8, j9, j10⟩ => by
      have f : ∀ x, (x < 4854 ∨ 4865 < x ∨ x = 4865) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (NFb + i) = m₀ (NFb + i) := j7 _ (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have e2 : c'.nmem (THb + i) = m₀ (THb + i) := j7 _ (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have e3 : c'.nmem (RV0b + i) = m₀ (RV0b + i) := j7 _ (by omega) (by omega) (by omega)
        (by omega) (by omega)
      have hrvi := hrv i hhi
      have e4 : c'.nmem (NFb + m₀ (RV0b + i)) = m₀ (NFb + m₀ (RV0b + i)) := j7 _ (by omega)
        (by omega) (by omega) (by omega) (by omega)
      obtain ⟨c₃, t₁, x₁, ht₁, a55, a57, a58, a59, a60, an₁, am₁, ar₁, arm₁, ao₁⟩ :=
        phA_exec (P := P) c' hw (by rw [f _ (by omega), q _ (by omega), r1])
          (by rw [f _ (by omega), q _ (by omega), r2]) (by rw [f _ (by omega), q _ (by omega), r3])
          (by rw [f _ (by omega), q _ (by omega), r5]) (by rw [f _ (by omega), g3]) h54
          (by omega) (by omega) (by omega) (by rw [e3]; omega) (by omega)
      have hw₃ := x₁.wb_right
      have hne := phNe_eq (c'.nmem (THb + i)) J1
      have hne1 : phNe (c'.nmem (THb + i)) J1 ≤ 1 := by rw [hne]; split_ifs <;> omega
      have ha1 : c'.nmem (NFb + i) / c'.nmem (NFb + i) ≤ 1 := by rw [sgn_eq]; split_ifs <;> omega
      obtain ⟨c₄, t₂, x₂, ht₂, b54, bm, bn, br, brm, bo⟩ := phB'_exec (P := P) c₃ hw₃
        (by rw [an₁ _ (by omega), f _ (by omega), q _ (by omega), r6])
        (by rw [an₁ _ (by omega), f _ (by omega), q _ (by omega), r7])
        (by rw [an₁ _ (by omega), f _ (by omega), q _ (by omega), r8])
        (by rw [an₁ _ (by omega), f _ (by omega), q _ (by omega), r9])
        (by rw [an₁ _ (by omega), f _ (by omega), q _ (by omega), r10])
        (by rw [an₁ _ (by omega), f _ (by omega), g3]) (by rw [an₁ _ (by omega), h54])
        (by rw [an₁ _ (by omega), f _ (by omega), g5]) a55 a57 a58 a59 a60 ha1 hne1
        (phB_le _ _) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by rw [e3]; omega)
      refine ⟨c₄, t₁ + t₂, .seq x₁ x₂, by omega, b54,
        by rw [bn _ (by omega) (by omega) (by omega) (by omega), an₁ _ (by omega)]; exact h40,
        fun x hx => by
          rw [bn _ (by omega) (by omega) (by omega) (by omega), an₁ _ (by omega), f x hx], ?_⟩
      rw [am₁] at bm
      rw [e1, e2, e3, e4] at bm
      refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
        fun a h1 h2 h3 h4 h5 => ?_, by rw [br, ar₁, j8], by rw [brm, arm₁, j9],
        by rw [bo, ao₁, j10]⟩
      · rw [bm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega)]; exact j2 j hj
        · rw [upd_same]; rfl
      · rw [bm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact j3 j hj
        · rw [upd_same]; rfl
      · rw [bm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]; exact j4 j hj
        · rw [upd_same]; rfl
      · rw [bm, upd_other _ _ _ (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact j5 j hj
        · rw [upd_same]
      · rw [bm]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
            upd_other _ _ _ (by omega)]; exact j6 j hj
        · rw [upd_same]
      · rw [bm, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega),
          upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
        exact j7 a (by omega) (by omega) (by omega) (by omega) (by omega))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, j4, j5, j6,
    fun a h1 h2 h3 h4 h5 => j7 a (by omega) (by omega) (by omega) (by omega) (by omega),
    fun x hx => by rw [j1 x (by omega), q x hx], by rw [j8, gr₁], by rw [j9, grm₁],
    by rw [j10, go₁]⟩

end Exec

/-! ### The inputs of the hole test -/

section Sem

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The arrays of the preparation are the inputs of the hole test**: for an enumeration `e` of
`B ⊇ N` with reverse indices `rv0`, flags `nf i ≠ 0 ↔ e i ∈ N`, hole numbers
`th i = J1 ↔ tail (e i) ∈ g` and class keys, the arrays `phRV`, `phYF` meet `CgEnumSub` and
`phGN` flags the darts of `N` off `g`. -/
theorem ph_cg {B N : Finset D} {Hs : List (Finset V)} {g : Finset V} {n : ℕ} {e : ℕ → D}
    (hmem : ∀ i < n, e i ∈ B) (hsurj : ∀ d ∈ B, ∃ i < n, e i = d)
    (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j) (hsub : N ⊆ B)
    {rv0 nf th key : ℕ → ℕ} {J1 : ℕ}
    (hrv0 : ∀ i < n, rv0 i < n ∧ e (rv0 i) = M.rev (e i))
    (hnf : ∀ i < n, (nf i ≠ 0 ↔ e i ∈ N)) (hth : ∀ i < n, (th i = J1 ↔ M.tail (e i) ∈ g))
    (hkey : ∀ i < n, ∀ j < n, (key i = key j ↔ HRel Hs (M.tail (e i)) (M.tail (e j)))) :
    CgEnumSub M B N Hs g n e (fun i => phRV (nf i) (nf (rv0 i)) (rv0 i) i) key
      (fun i => decide (0 < phYF (nf i) (th i) J1)) ∧
    ∀ i < n, (phGN (nf i) (th i) J1 ≠ 0 ↔ e i ∈ N ∧ M.tail (e i) ∉ g) := by
  refine ⟨⟨hmem, hsurj, hinj, hsub, fun i hi => ?_, fun i hi h1 h2 => ?_, fun i hi h => ?_,
    hkey, fun i hi => ?_⟩, fun i hi => ?_⟩
  · rw [phRV_eq]; split_ifs
    · exact (hrv0 i hi).1
    · exact hi
  · obtain ⟨hlt, he⟩ := hrv0 i hi
    have a1 : nf i ≠ 0 := (hnf i hi).2 h1
    have a2 : nf (rv0 i) ≠ 0 := (hnf _ hlt).2 (by rw [he]; exact h2)
    rw [phRV_eq]
    simp only [ne_eq, a1, a2, not_false_eq_true, and_self, ↓reduceIte]
    exact he
  · obtain ⟨hlt, he⟩ := hrv0 i hi
    rw [phRV_eq]
    split_ifs with hc
    · exact absurd ⟨(hnf i hi).1 hc.1, by rw [← he]; exact (hnf _ hlt).1 hc.2⟩ h
    · rfl
  · rw [decide_eq_true_iff, phYF_pos, hth i hi]
    have := hnf i hi
    tauto
  · rw [phGN_ne, hnf i hi, ne_eq, hth i hi]

end Sem

/-! ### Preparation and test -/

section Test

variable {P : Input} {W : ℕ}
variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {M : CombMap D V F}

/-- **The test of one hole**: the preparation, then the cut-vertex test. -/
def phCut : Stmt := .seq phProg cutProg

/-- **The cut-vertex test of the hole `g` from the per-index arrays of the piece**: inputs `NF`,
`TH`, `RV0` below `GN`; layout `GN | RV | TK | YF | LS (n) | OFF | ADJ | LAB | Q` (`CgLay`,
`BfLay`), the class keys `TK[i] < n`; within `160 n + 28` steps `r4767 ≠ 0 ↔ CutH M N Hs g`,
memory below `GN`, the array `TK` and above `Q + n` kept. -/
theorem phCut_cutH {B N : Finset D} {Hs : List (Finset V)} (hd : Hs.Pairwise Disjoint)
    {g : Finset V} (hg : g ∈ Hs) {e : ℕ → D}
    {n NFb THb RV0b J1 GNb RVb TKb YFb LSb OFFb ADJb LABb Qb : ℕ} (hmem : ∀ i < n, e i ∈ B)
    (hsurj : ∀ d ∈ B, ∃ i < n, e i = d) (hinj : ∀ i < n, ∀ j < n, e i = e j → i = j)
    (hsub : N ⊆ B) (c : Config) (hc : WordsBounded W c)
    (hL : CgLay n n RVb TKb YFb LSb OFFb ADJb) (hB : BfLay n (3 * n) OFFb ADJb LABb Qb W)
    (hGN : GNb + n ≤ RVb) (hin : NFb + n ≤ GNb ∧ THb + n ≤ GNb ∧ RV0b + n ≤ GNb)
    (hW : 2 * n + 2 ≤ W)
    (hrv0 : ∀ i < n, c.nmem (RV0b + i) < n ∧ e (c.nmem (RV0b + i)) = M.rev (e i))
    (hnf : ∀ i < n, (c.nmem (NFb + i) ≠ 0 ↔ e i ∈ N))
    (hth : ∀ i < n, (c.nmem (THb + i) = J1 ↔ M.tail (e i) ∈ g))
    (hTK : ∀ i < n, c.nmem (TKb + i) < n)
    (hkey : ∀ i < n, ∀ j < n, (c.nmem (TKb + i) = c.nmem (TKb + j) ↔
      HRel Hs (M.tail (e i)) (M.tail (e j))))
    (p0 : c.nreg 4840 = n) (p1 : c.nreg 4841 = NFb) (p2 : c.nreg 4842 = THb)
    (p3 : c.nreg 4843 = RV0b) (p5 : c.nreg 4845 = J1) (p6 : c.nreg 4846 = YFb)
    (p7 : c.nreg 4847 = GNb) (p8 : c.nreg 4848 = RVb) (p9 : c.nreg 4849 = LABb)
    (p10 : c.nreg 4866 = LSb)
    (r0 : c.nreg 4420 = n) (r1 : c.nreg 4421 = RVb) (r2 : c.nreg 4422 = TKb)
    (r3 : c.nreg 4423 = YFb) (r4 : c.nreg 4424 = LSb) (r5 : c.nreg 4425 = OFFb)
    (r6 : c.nreg 4426 = ADJb) (s0 : c.nreg 4400 = n) (s1 : c.nreg 4401 = OFFb)
    (s2 : c.nreg 4402 = ADJb) (s3 : c.nreg 4403 = LABb) (s4 : c.nreg 4404 = Qb)
    (u0 : c.nreg 4760 = n) (u1 : c.nreg 4761 = GNb) (u2 : c.nreg 4762 = LABb) :
    ∃ c' k, Exec P W phCut c c' k ∧ k ≤ 160 * n + 28 ∧
      (c'.nreg 4767 ≠ 0 ↔ CutH M N Hs g) ∧
      (∀ a, (a < GNb ∨ (TKb ≤ a ∧ a < TKb + n) ∨ Qb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 4405 ∨ (4436 < x ∧ x < 4763) ∨ (4771 < x ∧ x < 4853) ∨ 4865 < x) →
        c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hLc := hL
  have hBc := hB
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  obtain ⟨b1, b2, b3, b4⟩ := hB
  obtain ⟨h1, h2, h3⟩ := hin
  obtain ⟨c₁, k₁, e₁, hk₁, H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩ := phProg_exec (P := P) c hc
    p0 p1 p2 p3 p5 p6 p7 p8 p9 p10 (fun i hi => (hrv0 i hi).1)
    ⟨by omega, by omega, by omega, hGN, by omega, by omega, by omega, by omega, hW⟩
  have hw₁ := e₁.wb_right
  have fr : ∀ a, (a < GNb ∨ (TKb ≤ a ∧ a < TKb + n) ∨ Qb + n ≤ a) → c₁.nmem a = c.nmem a :=
    fun a ha => H6 a (by omega) (by omega) (by omega) (by omega) (by omega)
  have q : ∀ x, (x < 4853 ∨ 4865 < x) → c₁.nreg x = c.nreg x := H7
  obtain ⟨hE, hGNf⟩ := ph_cg (M := M) (Hs := Hs) (g := g) hmem hsurj hinj hsub hrv0 hnf hth hkey
  obtain ⟨c₂, k₂, e₂, hk₂, G1, G2, G3, G4, G5, G6⟩ := cutProg_cutH (P := P) (M := M) (B := B)
    (N := N) hd hg c₁ hw₁ hLc hBc hGN hW
    (fun i hi => by rw [fr _ (by omega)]; exact hTK i hi)
    (CgEnumSub.congr hE (fun i hi => by rw [H3 i hi])
      (fun i hi => by simp only [cgKey]; rw [fr _ (by omega)])
      (fun i hi => by simp only [cgYf]; rw [H1 i hi]))
    (fun i hi => by rw [H2 i hi]; exact hGNf i hi)
    (fun k hk => H5 k hk) H4
    (by rw [q _ (by omega), r0]) (by rw [q _ (by omega), r1]) (by rw [q _ (by omega), r2])
    (by rw [q _ (by omega), r3]) (by rw [q _ (by omega), r4]) (by rw [q _ (by omega), r5])
    (by rw [q _ (by omega), r6]) (by rw [q _ (by omega), s0]) (by rw [q _ (by omega), s1])
    (by rw [q _ (by omega), s2]) (by rw [q _ (by omega), s3]) (by rw [q _ (by omega), s4])
    (by rw [q _ (by omega), u0]) (by rw [q _ (by omega), u1]) (by rw [q _ (by omega), u2])
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, G1, fun a ha => ?_, fun x hx => ?_,
    by rw [G4, H8], by rw [G5, H9], by rw [G6, H10]⟩
  · rw [G2 a (by omega) (by omega) (by omega), fr a ha]
  · rw [G3 x (by omega), q x (by omega)]

end Test

end BKMNW

end PlanarFlow
