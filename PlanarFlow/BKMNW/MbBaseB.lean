module

public import PlanarFlow.BKMNW.MbBaseA

/-!
# Miller's base, stage B: copying the separator out and restoring the work area

`mbB := mbP3 ; gcp ; mbP4 ; gcp ; mbP5 ; cpArr`: the `k = r641` cycle codes from `r640` to
`Hb + 8 n`, the `m = r5012` face marks from `r642` to `Hb + 11 n` (both read with the memory above
`Wr = r5040` as `0`, i.e. from `mbCut Wr`), then the saved copy of `[0, Wr]` back from `SVb`.

* `mbP3`, `mbP4`, `mbP5`, **`mbB`**, the block lemmas, **`mbB_exec`** (`8 k + 8 m + 7 (Wr + 1)
  + 40` steps); written `5100 … 5109`, `5212`, `5213`, `4910 … 4916`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The registers of the copy of the cycle codes. -/
def mbP3 : Stmt :=
  block [.copyN 5100 641, .copyN 5101 640, .constN 5212 8, .mulN 5213 5000 5212,
    .addN 5102 5004 5213, .copyN 5109 5040]

/-- The registers of the copy of the face marks. -/
def mbP4 : Stmt :=
  block [.copyN 5100 5012, .copyN 5101 642, .constN 5212 11, .mulN 5213 5000 5212,
    .addN 5102 5004 5213]

/-- The registers of the restoration. -/
def mbP5 : Stmt := block [.copyN 4910 5045, .copyN 4911 5046, .constN 4912 0]

/-- **Stage B of Miller's base.** -/
def mbB : Stmt := .seq mbP3 (.seq gcp (.seq mbP4 (.seq gcp (.seq mbP5 cpArr))))

section Exec

variable {P : Input} {W : ℕ}

set_option maxHeartbeats 800000 in
/-- **Stage B**: the cycle codes at `Hb + 8 n`, the face marks at `Hb + 11 n` (from the memory cut
at `Wr`), the work area `[0, Wr]` restored from `SVb`; memory above `Wr` off the two copies kept;
registers outside `4910 … 4916`, `5100 … 5109`, `5212`, `5213` kept. -/
theorem mbB_exec (d : Config) (hd : WordsBounded W d) {k p0 p2 n Hb m Wr SVb : ℕ}
    (r641 : d.nreg 641 = k) (r640 : d.nreg 640 = p0) (r642 : d.nreg 642 = p2)
    (r00 : d.nreg 5000 = n) (r04 : d.nreg 5004 = Hb) (r12 : d.nreg 5012 = m)
    (r40 : d.nreg 5040 = Wr) (r45 : d.nreg 5045 = Wr + 1) (r46 : d.nreg 5046 = SVb)
    (lay : Wr < Hb ∧ k ≤ 3 * n ∧ m ≤ n ∧ Hb + 13 * n ≤ SVb ∧ SVb + Wr + 1 ≤ W ∧ 12 ≤ W) :
    ∃ d' t, Exec P W mbB d d' t ∧ t ≤ 8 * k + 8 * m + 7 * (Wr + 1) + 40 ∧
      (∀ l < k, d'.nmem (Hb + 8 * n + l) = (mbCut Wr d).nmem (p0 + l)) ∧
      (∀ q < m, d'.nmem (Hb + 11 * n + q) = (mbCut Wr d).nmem (p2 + q)) ∧
      (∀ a ≤ Wr, d'.nmem a = d.nmem (SVb + a)) ∧
      (∀ a, Wr < a → ¬ (Hb + 8 * n ≤ a ∧ a < Hb + 8 * n + k) →
        ¬ (Hb + 11 * n ≤ a ∧ a < Hb + 11 * n + m) → d'.nmem a = d.nmem a) ∧
      (∀ x, (x < 4910 ∨ (4916 < x ∧ x < 5100) ∨ (5109 < x ∧ x < 5212) ∨ 5213 < x) →
        d'.nreg x = d.nreg x) ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := lay
  have h8 : n * 8 = 8 * n := by ring
  have h11 : n * 11 = 11 * n := by ring
  -- the registers of the first copy
  obtain ⟨c₁, t₁, e₁, ht₁, a0, a1, a2, a9, an₁, am₁, ar₁, arm₁, ao₁⟩ : ∃ c₁ t₁,
      Exec P W mbP3 d c₁ t₁ ∧ t₁ = 6 ∧ c₁.nreg 5100 = k ∧ c₁.nreg 5101 = p0 ∧
      c₁.nreg 5102 = Hb + 8 * n ∧ c₁.nreg 5109 = Wr ∧
      (∀ x, x ≠ 5100 → x ≠ 5101 → x ≠ 5102 → x ≠ 5109 → x ≠ 5212 → x ≠ 5213 →
        c₁.nreg x = d.nreg x) ∧ c₁.nmem = d.nmem ∧
      c₁.rreg = d.rreg ∧ c₁.rmem = d.rmem ∧ c₁.output = d.output := by
    unfold mbP3
    exec_block
    all_goals try (config_simp; (try simp only [r641, r640, r00, r04, r40, h8]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x a1 a2 a3 a4 a5 a6 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; (try simp only [r641, r640, r00, r04, r40, h8]); done)
    all_goals try (config_simp; (try simp only [r641, r640, r00, r04, r40, h8]); omega)
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  obtain ⟨c₂, t₂, e₂, ht₂, g1, gm₂, gn₂, gr₂, grm₂, go₂⟩ :=
    gcp_exec (P := P) c₁ hw₁ a0 a1 a2 a9 (by omega) (by omega) (by omega) (by omega)
  have hw₂ := e₂.wb_right
  -- the registers of the second copy
  obtain ⟨c₃, t₃, e₃, ht₃, b0, b1, b2, bn₃, bm₃, br₃, brm₃, bo₃⟩ : ∃ c₃ t₃,
      Exec P W mbP4 c₂ c₃ t₃ ∧ t₃ = 5 ∧ c₃.nreg 5100 = m ∧ c₃.nreg 5101 = p2 ∧
      c₃.nreg 5102 = Hb + 11 * n ∧
      (∀ x, x ≠ 5100 → x ≠ 5101 → x ≠ 5102 → x ≠ 5212 → x ≠ 5213 → c₃.nreg x = c₂.nreg x) ∧
      c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    have q12 : c₂.nreg 5012 = m := by
      rw [gn₂ _ (by omega), an₁ _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), r12]
    have q42 : c₂.nreg 642 = p2 := by
      rw [gn₂ _ (by omega), an₁ _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), r642]
    have q00 : c₂.nreg 5000 = n := by
      rw [gn₂ _ (by omega), an₁ _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), r00]
    have q04 : c₂.nreg 5004 = Hb := by
      rw [gn₂ _ (by omega), an₁ _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega), r04]
    unfold mbP4
    exec_block
    all_goals try (config_simp; (try simp only [q12, q42, q00, q04, h11]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a1 a2 a3 a4 a5 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; (try simp only [q12, q42, q00, q04, h11]); done)
    all_goals try (config_simp; (try simp only [q12, q42, q00, q04, h11]); omega)
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₃ := e₃.wb_right
  have q09 : c₃.nreg 5109 = Wr := by rw [bn₃ _ (by omega) (by omega) (by omega) (by omega)
    (by omega), gn₂ _ (by omega), a9]
  obtain ⟨c₄, t₄, e₄, ht₄, f1, fm₄, fn₄, fr₄, frm₄, fo₄⟩ :=
    gcp_exec (P := P) c₃ hw₃ b0 b1 b2 q09 (by omega) (by omega) (by omega) (by omega)
  have hw₄ := e₄.wb_right
  -- the restoration
  have q45 : c₄.nreg 5045 = Wr + 1 := by
    rw [fn₄ _ (by omega), bn₃ _ (by omega) (by omega) (by omega) (by omega) (by omega),
      gn₂ _ (by omega), an₁ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      r45]
  have q46 : c₄.nreg 5046 = SVb := by
    rw [fn₄ _ (by omega), bn₃ _ (by omega) (by omega) (by omega) (by omega) (by omega),
      gn₂ _ (by omega), an₁ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      r46]
  obtain ⟨c₅, t₅, e₅, ht₅, u0, u1, u2, un₅, um₅, ur₅, urm₅, uo₅⟩ : ∃ c₅ t₅,
      Exec P W mbP5 c₄ c₅ t₅ ∧ t₅ = 3 ∧ c₅.nreg 4910 = Wr + 1 ∧ c₅.nreg 4911 = SVb ∧
      c₅.nreg 4912 = 0 ∧ (∀ x, x ≠ 4910 → x ≠ 4911 → x ≠ 4912 → c₅.nreg x = c₄.nreg x) ∧
      c₅.nmem = c₄.nmem ∧ c₅.rreg = c₄.rreg ∧ c₅.rmem = c₄.rmem ∧ c₅.output = c₄.output := by
    unfold mbP5
    exec_block
    all_goals try (config_simp; (try simp only [q45, q46]); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a1 a2 a3 => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; (try simp only [q45, q46]); done)
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₅ := e₅.wb_right
  obtain ⟨c₆, t₆, e₆, ht₆, v1, vm₆, vn₆, vr₆, vrm₆, vo₆⟩ :=
    cpArr_exec (P := P) c₅ hw₅ u0 u1 u2 ⟨Or.inr (by omega), by omega, by omega, by omega⟩
  -- the memory
  have m₄ : ∀ a, a ≤ Wr → c₄.nmem a = d.nmem a := fun a ha => by
    rw [fm₄ a (Or.inl (by omega)), bm₃, gm₂ a (Or.inl (by omega)), am₁]
  refine ⟨c₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), by omega, fun l hl => ?_, fun q hq => ?_,
    fun a ha => ?_, fun a h1 h2 h3 => ?_, fun x hx => ?_, ?_, ?_, ?_⟩
  · have hc6 : c₆.nmem (Hb + 8 * n + l) = c₄.nmem (Hb + 8 * n + l) := by
      rw [vm₆ _ (Or.inr (by omega)), um₅]
    rw [hc6, fm₄ _ (Or.inl (by omega)), bm₃, g1 l hl, am₁]
    simp only [mbCut]
  · have hc6 : c₆.nmem (Hb + 11 * n + q) = c₄.nmem (Hb + 11 * n + q) := by
      rw [vm₆ _ (Or.inr (by omega)), um₅]
    rw [hc6, f1 q hq]
    simp only [mbCut]
    split_ifs with h
    · rw [bm₃, gm₂ _ (Or.inl (by omega)), am₁]
    · rfl
  · have := v1 a (by omega)
    rw [zero_add] at this
    rw [this, um₅, fm₄ _ (Or.inr (by omega)), bm₃, gm₂ _ (Or.inr (by omega)), am₁]
  · rw [vm₆ _ (Or.inr (by omega)), um₅, fm₄ _ (by omega), bm₃, gm₂ _ (by omega), am₁]
  · rw [vn₆ _ (by omega), un₅ _ (by omega) (by omega) (by omega), fn₄ _ (by omega),
      bn₃ _ (by omega) (by omega) (by omega) (by omega) (by omega), gn₂ _ (by omega),
      an₁ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [vr₆, ur₅, fr₄, br₃, gr₂, ar₁]
  · rw [vrm₆, urm₅, frm₄, brm₃, grm₂, arm₁]
  · rw [vo₆, uo₅, fo₄, bo₃, go₂, ao₁]

end Exec

end BKMNW

end PlanarFlow
