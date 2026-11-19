module

public import PlanarFlow.BKMNW.StMapB

/-!
# The map part of the s-t flow encoding: stages A, B, C

* **`smA_exec`**: the layout registers, `RV` copied to `β`, the face permutation
  `NX[i] = RT[RV[i]]` at `S`;
* **`smB_exec`**: the orbit labels `olab f + 1` of `NX` at `S + m` and `olab g + 1` of `RT` at
  `S + 2m` (`f`, `g` permutations of `[0, m)`);
* **`smC_exec`**: `NT` (`= LABF`) at `β + 4m`, `NF` (`= LABV + 2m`) at `β + m`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

namespace StEnc

open Finset Function CombMap WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs
  OrbLab NsStep

variable {P : Input} {W : ℕ}

lemma smScr_of {r : ℕ} (hr : ¬ SmScr r) : (r < 7705 ∨ 7737 < r) ∧ (r < 4910 ∨ 4916 < r) ∧
    (r < 6210 ∨ 6217 < r) ∧ (r < 5030 ∨ 5035 < r) ∧ (r < 7350 ∨ 7352 < r) ∧
    (r < 7400 ∨ 7405 < r) ∧ (r < 1800 ∨ 1816 < r) := by
  unfold SmScr at hr; omega

/-- **Stage A**: the layout, `RV` at `β`, `NX[i] = RT[RV[i]]` at `S`. -/
theorem smA_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb S β : ℕ}
    (r00 : c.nreg 7700 = m) (r01 : c.nreg 7701 = RVb) (r02 : c.nreg 7702 = RTb)
    (r03 : c.nreg 7703 = S) (r04 : c.nreg 7704 = β)
    (hRV : ∀ i < m, c.nmem (RVb + i) < m) (hRT : ∀ i < m, c.nmem (RTb + i) < m)
    (l1 : RVb + m ≤ S) (l2 : RTb + m ≤ S) (l3 : S + 3 * m ≤ β) (w : β + 12 * m + 1 ≤ W) :
    ∃ c' t, Exec P W smA c c' t ∧ t ≤ 16 * m + 30 ∧ SmRegs c' m RVb RTb S β ∧
      (∀ i < m, c'.nmem (β + i) = c.nmem (RVb + i)) ∧
      (∀ i < m, c'.nmem (S + i) = c.nmem (RTb + c.nmem (RVb + i))) ∧
      (∀ a, ¬ (S ≤ a ∧ a < S + m) → ¬ (β ≤ a ∧ a < β + m) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ SmScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smA smRV smNX
  obtain ⟨c₁, t₁, e₁, ht₁, L₁, n₁, m₁, rr₁, rm₁, o₁⟩ :=
    smL_exec (P := P) c hc r00 r01 r02 r03 r04 (by omega) (by omega) (by omega)
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := id L₁
  obtain ⟨c₂, t₂, e₂, ht₂, b0, b1, b2, n₂, m₂, rr₂, rm₂, o₂⟩ := setRV_exec (P := P) c₁ e₁.wb_right
  obtain ⟨c₃, t₃, e₃, ht₃, g1, g2, n₃, rr₃, rm₃, o₃⟩ := cpArr_exec (P := P) c₂ e₂.wb_right
    (n := m) (Sb := RVb) (Db := β) (by rw [b0, a0]) (by rw [b1, a1]) (by rw [b2, a4])
    ⟨Or.inl (by omega), by omega, by omega, by omega⟩
  obtain ⟨c₄, t₄, e₄, ht₄, s0, s1, s2, s3, n₄, m₄, rr₄, rm₄, o₄⟩ := setNX_exec (P := P) c₃
    e₃.wb_right
  have k3 : ∀ a, a < β → c₃.nmem a = c.nmem a := fun a ha => by rw [g2 a (by omega), m₂, m₁]
  obtain ⟨c₅, t₅, e₅, ht₅, h1, h2, n₅, rr₅, rm₅, o₅⟩ := lgProg_exec (P := P) c₄ e₄.wb_right
    (m := m) (IXb := RVb) (Ab := RTb) (OUTb := S)
    (by rw [s0, n₃ _ (by omega), n₂ _ (by omega), a0])
    (by rw [s1, n₃ _ (by omega), n₂ _ (by omega), a1])
    (by rw [s2, n₃ _ (by omega), n₂ _ (by omega), a2])
    (by rw [s3, n₃ _ (by omega), n₂ _ (by omega), a3]) (by omega) (by omega) (by omega)
    (fun j hj => by rw [m₄, k3 _ (by omega)]; have := hRV j hj; omega)
    (fun j hj => by omega)
    (fun j hj => by rw [m₄, k3 _ (by omega)]; have := hRV j hj; omega)
  refine ⟨c₅, t₁ + ((t₂ + t₃) + (t₄ + t₅)), .seq e₁ (.seq (.seq e₂ e₃) (.seq e₄ e₅)), by omega,
    ?_, fun i hi => ?_, fun i hi => ?_, fun a ha hb => ?_, fun r hr => ?_,
    by rw [rr₅, rr₄, rr₃, rr₂, rr₁], by rw [rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₅, o₄, o₃, o₂, o₁]⟩
  · exact L₁.of fun r h1 h2 => by rw [n₅ r (by omega), n₄ r (by omega), n₃ r (by omega),
      n₂ r (by omega)]
  · rw [h2 _ (by omega), m₄, g1 i hi, m₂, m₁]
  · have e1 : c₃.nmem (RVb + i) = c.nmem (RVb + i) := k3 _ (by omega)
    rw [h1 i hi, m₄, e1, k3 _ (by have := hRV i hi; omega)]
  · rw [h2 a (by omega), m₄, g2 a (by omega), m₂, m₁]
  · obtain ⟨q1, q2, q3, -⟩ := smScr_of hr
    rw [n₅ r (by omega), n₄ r (by omega), n₃ r (by omega), n₂ r (by omega), n₁ r (by omega)]

/-- **Stage B**: the orbit labels of `NX` (at `S`, the values of `f`) at `S + m` and of `RT`
(the values of `g`) at `S + 2m`. -/
theorem smB_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb S β : ℕ} {f g : ℕ → ℕ}
    (hL : SmRegs c m RVb RTb S β) (hf : PermOn f m) (hg : PermOn g m)
    (hNX : ∀ i < m, c.nmem (S + i) = f i) (hRT : ∀ i < m, c.nmem (RTb + i) = g i)
    (l2 : RTb + m ≤ S) (w : S + 3 * m ≤ W) (w' : 2 * m + 1 ≤ W) :
    ∃ c' t, Exec P W smB c c' t ∧ t ≤ 50 * m + 30 ∧
      (∀ i < m, c'.nmem (S + m + i) = olab f i + 1) ∧
      (∀ i < m, c'.nmem (S + 2 * m + i) = olab g i + 1) ∧
      (∀ a, (a < S + m ∨ S + 3 * m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ SmScr r → c'.nreg r = c.nreg r) ∧ SmRegs c' m RVb RTb S β ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨a0, a1, a2, a3, a4, a6, a7, -, -, -, -, -, -, -, -, a16, -, -, -⟩ := id hL
  unfold smB smZL smLF smLV
  obtain ⟨c₁, t₁, e₁, ht₁, z0, z1, n₁, m₁, rr₁, rm₁, o₁⟩ := setZ_exec (P := P) c hc 7716 7706
  obtain ⟨c₂, t₂, e₂, ht₂, y1, y2, n₂, rr₂, rm₂, o₂⟩ := mzFill_exec (P := P) c₁ e₁.wb_right
    (len := 2 * m) (Zb := S + m) (by rw [z0, a16])
    (by rw [z1, upd_other _ _ _ (by omega), a6]) (by omega) (by omega)
  have q2 : ∀ r, 7700 ≤ r → r ≤ 7722 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [n₂ r (by omega), n₁ r (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, x0, x1, x2, n₃, m₃, rr₃, rm₃, o₃⟩ := setO3_exec (P := P) c₂
    e₂.wb_right 7703 7706 7700 (by simp) (by simp) (by simp)
  obtain ⟨c₄, t₄, e₄, ht₄, l1, l2', n₄, rr₄, rm₄, o₄⟩ := olProg_exec (P := P) (f := f) (m := m)
    hf (Pb := S) (Lb := S + m) (by omega) (by omega) (by omega) c₃ e₃.wb_right
    (by rw [x0, q2 _ (by omega) (by omega), a3]) (by rw [x1, q2 _ (by omega) (by omega), a6])
    (by rw [x2, q2 _ (by omega) (by omega), a0])
    (fun x hx => by rw [m₃, y2 _ (by omega), m₁]; exact hNX x hx)
    (fun x hx => by rw [m₃, show S + m + x = S + m + x by rfl]; exact y1 x (by omega))
  have q4 : ∀ r, 7700 ≤ r → r ≤ 7722 → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    rw [n₄ r (by omega), n₃ r (by omega), q2 r h1 h2]
  obtain ⟨c₅, t₅, e₅, ht₅, v0, v1, v2, n₅, m₅, rr₅, rm₅, o₅⟩ := setO3_exec (P := P) c₄
    e₄.wb_right 7702 7707 7700 (by simp) (by simp) (by simp)
  obtain ⟨c₆, t₆, e₆, ht₆, k1, k2, n₆, rr₆, rm₆, o₆⟩ := olProg_exec (P := P) (f := g) (m := m)
    hg (Pb := RTb) (Lb := S + 2 * m) (by omega) (by omega) (by omega) c₅ e₅.wb_right
    (by rw [v0, q4 _ (by omega) (by omega), a2]) (by rw [v1, q4 _ (by omega) (by omega), a7])
    (by rw [v2, q4 _ (by omega) (by omega), a0])
    (fun x hx => by
      rw [m₅, l2' _ (by omega), m₃, y2 _ (by omega), m₁]; exact hRT x hx)
    (fun x hx => by
      rw [m₅, l2' _ (by omega), m₃]
      have := y1 (m + x) (by omega)
      rwa [show S + m + (m + x) = S + 2 * m + x by ring] at this)
  refine ⟨c₆, (t₁ + t₂) + ((t₃ + t₄) + (t₅ + t₆)),
    .seq (.seq e₁ e₂) (.seq (.seq e₃ e₄) (.seq e₅ e₆)), by omega, fun i hi => ?_,
    k1, fun a ha => ?_, fun r hr => ?_, ?_, by rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁], by rw [o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · rw [k2 _ (by omega), m₅]; exact l1 i hi
  · rw [k2 a (by omega), m₅, l2' a (by omega), m₃, y2 a (by omega), m₁]
  · obtain ⟨-, -, -, q4', q5, q6, -⟩ := smScr_of hr
    rw [n₆ r (by omega), n₅ r (by omega), n₄ r (by omega), n₃ r (by omega), n₂ r (by omega),
      n₁ r (by omega)]
  · exact hL.of fun r h1 h2 => by
      rw [n₆ r (by omega), n₅ r (by omega), q4 r h1 h2]

/-- **Stage C**: `NT` (the face labels at `S + m`) at `β + 4m`, `NF` (the vertex labels at
`S + 2m`, plus `2m`) at `β + m`. -/
theorem smC_exec (c : Config) (hc : WordsBounded W c) {m RVb RTb S β : ℕ}
    (hL : SmRegs c m RVb RTb S β) (l3 : S + 3 * m ≤ β) (w : β + 12 * m + 1 ≤ W)
    (hV : ∀ i < m, c.nmem (S + 2 * m + i) + 2 * m ≤ W) :
    ∃ c' t, Exec P W smC c c' t ∧ t ≤ 15 * m + 20 ∧
      (∀ i < m, c'.nmem (β + 4 * m + i) = c.nmem (S + m + i)) ∧
      (∀ i < m, c'.nmem (β + m + i) = c.nmem (S + 2 * m + i) + 2 * m) ∧
      (∀ a, ¬ (β + m ≤ a ∧ a < β + 2 * m) → ¬ (β + 4 * m ≤ a ∧ a < β + 5 * m) →
        c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ SmScr r → c'.nreg r = c.nreg r) ∧ SmRegs c' m RVb RTb S β ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨a0, a1, a2, a3, a4, a6, a7, a8, -, -, a9, -, -, -, -, a16, -, -, -⟩ := id hL
  unfold smC smNT smNF
  obtain ⟨c₁, t₁, e₁, ht₁, b0, b1, b2, n₁, m₁, rr₁, rm₁, o₁⟩ := setC3_exec (P := P) c hc 7700 7706
    7709 (by omega) (by omega) (by omega)
  obtain ⟨c₂, t₂, e₂, ht₂, g1, g2, n₂, rr₂, rm₂, o₂⟩ := cpArr_exec (P := P) c₁ e₁.wb_right
    (n := m) (Sb := S + m) (Db := β + 4 * m) (by rw [b0, a0]) (by rw [b1, a6]) (by rw [b2, a9])
    ⟨Or.inl (by omega), by omega, by omega, by omega⟩
  have q2 : ∀ r, 7700 ≤ r → r ≤ 7722 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [n₂ r (by omega), n₁ r (by omega)]
  obtain ⟨c₃, t₃, e₃, ht₃, s0, s1, s2, s3, n₃, m₃, rr₃, rm₃, o₃⟩ := setNF_exec (P := P) c₂
    e₂.wb_right
  obtain ⟨c₄, t₄, e₄, ht₄, h1, h2, n₄, rr₄, rm₄, o₄⟩ := laProg_exec (P := P) c₃ e₃.wb_right
    (m := m) (Ab := S + 2 * m) (OUTb := β + m) (K := 2 * m)
    (by rw [s0, q2 _ (by omega) (by omega), a0]) (by rw [s1, q2 _ (by omega) (by omega), a7])
    (by rw [s2, q2 _ (by omega) (by omega), a8]) (by rw [s3, q2 _ (by omega) (by omega), a16])
    (by omega) (by omega) (by omega)
    (fun j hj => by rw [m₃, g2 _ (by omega), m₁]; exact hV j hj) (Or.inl (by omega))
  refine ⟨c₄, (t₁ + t₂) + (t₃ + t₄), .seq (.seq e₁ e₂) (.seq e₃ e₄), by omega, fun i hi => ?_,
    fun i hi => ?_, fun a ha hb => ?_, fun r hr => ?_, ?_, by rw [rr₄, rr₃, rr₂, rr₁],
    by rw [rm₄, rm₃, rm₂, rm₁], by rw [o₄, o₃, o₂, o₁]⟩
  · rw [h2 _ (by omega), m₃, g1 i hi, m₁]
  · rw [h1 i hi, m₃, g2 _ (by omega), m₁]
  · rw [h2 a (by omega), m₃, g2 a (by omega), m₁]
  · obtain ⟨q1, q2', -⟩ := smScr_of hr
    rw [n₄ r (by omega), n₃ r (by omega), n₂ r (by omega), n₁ r (by omega)]
  · exact hL.of fun r h1 h2 => by rw [n₄ r (by omega), n₃ r (by omega), q2 r h1 h2]

end StEnc

end BKMNW

end PlanarFlow
