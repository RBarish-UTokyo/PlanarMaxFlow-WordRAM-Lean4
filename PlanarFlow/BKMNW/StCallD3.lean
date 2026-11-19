module

public import PlanarFlow.BKMNW.StCallD2

/-!
# The run stage of the s-t flow call, part 3: the read-back and the clearing

**`stD3_exec`**: `stD3` writes `O[i] = rdv Z H Mo (W[β₀ + 6m + 3 + i])` at `Ob` (`rdbProg`),
clears the logged cells (`lgClr`), the residues `[β₀, β₀ + 5m + 3)` and the image
`[ib, ib + len)` (`mzFill`), within `costD3 m j = 222 m + 6 j + 112` steps; every other cell is
kept outside `[Ob, Ob + m)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace PlanarFlow

namespace BKMNW

namespace StCall

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP StEnc

variable {P : Input} {W : ℕ}

/-- The cost of `stD3`. -/
def costD3 (m j : ℕ) : ℕ := 222 * m + 6 * j + 112

set_option maxHeartbeats 800000 in
/-- **The read-back and the clearing** (see the module docstring). -/
theorem stD3_exec (c : Config) (hc : WordsBounded W c) {m Sb ib Ob Z p j H Wz : ℕ}
    (hL : StL c.nreg m Sb) (r00 : c.nreg 9100 = m) (r07 : c.nreg 9107 = ib)
    (r08 : c.nreg 9108 = Ob) (r09 : c.nreg 9109 = Z) (r10 : c.nreg 9110 = p)
    (r45 : c.nreg 9145 = H) (r46 : c.nreg 9146 = STFlow.pstM H) (r50 : c.nreg 9150 = p + j)
    (hlog : ∀ i < j, c.nmem (p + i) ≤ Wz) (hp : Wz < p) (hO : Wz < Ob) (hOp : Ob + m ≤ p)
    (hZ : ∀ i < m, Z + c.nmem (107 * m + 49 + i) ≤ W) (hib : ib + (37 * m + 13) ≤ Wz)
    (hr : 108 * m + 49 ≤ Wz) (hOW : Ob + m ≤ W) :
    ∃ c' t, Exec P W stD3 c c' t ∧ t ≤ costD3 m j ∧
      (∀ i < m, c'.nmem (Ob + i) = rdv Z H (STFlow.pstM H) (c.nmem (107 * m + 49 + i))) ∧
      (∀ a, ((∃ i < j, c.nmem (p + i) = a) ∨ (101 * m + 46 ≤ a ∧ a < 106 * m + 49) ∨
        (ib ≤ a ∧ a < ib + (37 * m + 13))) → c'.nmem a = 0) ∧
      (∀ a, (∀ i < j, c.nmem (p + i) ≠ a) → (a < 101 * m + 46 ∨ 106 * m + 49 ≤ a) →
        (a < ib ∨ ib + (37 * m + 13) ≤ a) → (a < Ob ∨ Ob + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 2923 ∨ 2929 < r) → (r < 5030 ∨ 5035 < r) → (r < 9130 ∨ 9140 < r) →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hpW : p + j ≤ W := r50 ▸ WordsBounded.nreg hc 9150
  -- 1. the registers of the read-back
  obtain ⟨c₁, e₁, v₁, f₁, m₁, r₁, rm₁, o₁⟩ := cpL_exec (P := P) stSD4 (by decide) (by decide) c hc
  -- 2. the read-back
  obtain ⟨c₂, t₂, e₂, ht₂, O₂, K₂, R₂, rr₂, rm₂, o₂⟩ := rdbProg_exec (P := P) c₁ e₁.wb_right
    (m := m) (Ib := 107 * m + 49) (Ob := Ob) (Z := Z) (H := H) (Mo := STFlow.pstM H)
    (by rw [v₁ (9130, 9100) (by simp [stSD4]), r00])
    (by rw [v₁ (9131, 9180) (by simp [stSD4]), hL.ob])
    (by rw [v₁ (9132, 9108) (by simp [stSD4]), r08])
    (by rw [v₁ (9133, 9109) (by simp [stSD4]), r09])
    (by rw [v₁ (9134, 9145) (by simp [stSD4]), r45])
    (by rw [v₁ (9135, 9146) (by simp [stSD4]), r46]) (Or.inl (by omega)) (by omega) hOW
    (by omega) (fun i hi => by rw [m₁]; exact hZ i hi)
  have k₂ : ∀ r, (r < 9130 ∨ 9140 < r) → c₂.nreg r = c.nreg r := fun r hr => by
    rw [R₂ r (by omega), f₁ r (by simp only [stSD4, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]; omega)]
  have mlog : ∀ i < j, c₂.nmem (p + i) = c.nmem (p + i) := fun i hi => by
    rw [K₂ _ (Or.inr (by omega)), m₁]
  -- 3. the registers of the clearing of the log
  obtain ⟨c₃, e₃, v₃, f₃, m₃, r₃, rm₃, o₃⟩ := cpL_exec (P := P) stSD5 (by decide) (by decide) c₂
    e₂.wb_right
  -- 4. the clearing of the log
  obtain ⟨c₄, t₄, e₄, ht₄, Z₄, K₄, R₄, rr₄, rm₄, o₄⟩ := lgClr_exec (P := P) c₃ e₃.wb_right
    (p := p) (j := j) (Ws := Wz)
    (by rw [v₃ (2924, 9110) (by simp [stSD5]), k₂ _ (by omega), r10])
    (by rw [v₃ (2925, 9150) (by simp [stSD5]), k₂ _ (by omega), r50])
    (by rw [v₃ (2926, 9182) (by simp [stSD5]), k₂ _ (by omega), hL.one])
    (fun i hi => by rw [m₃, mlog i hi]; exact hlog i hi) hp
  have k₄ : ∀ r, (r < 2923 ∨ 2929 < r) → (r < 9130 ∨ 9140 < r) → c₄.nreg r = c.nreg r :=
    fun r h1 h2 => by
      rw [R₄ r (by omega) (by omega), f₃ r (by simp only [stSD5, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false]; omega), k₂ r h2]
  -- 5. the residues
  obtain ⟨c₅, e₅, v₅, f₅, m₅, r₅, rm₅, o₅⟩ := cpL_exec (P := P) stSD6 (by decide) (by decide) c₄
    e₄.wb_right
  obtain ⟨c₆, t₆, e₆, ht₆, Z₆, K₆, R₆, rr₆, rm₆, o₆⟩ := mzFill_exec (P := P) c₅ e₅.wb_right
    (len := 5 * m + 3) (Zb := 101 * m + 46)
    (by rw [v₅ (5030, 9181) (by simp [stSD6]), k₄ _ (by omega) (by omega), hL.rl])
    (by rw [v₅ (5031, 9163) (by simp [stSD6]), k₄ _ (by omega) (by omega), hL.b0])
    (by omega) (by omega)
  have k₆ : ∀ r, (r < 2923 ∨ 2929 < r) → (r < 5030 ∨ 5035 < r) → (r < 9130 ∨ 9140 < r) →
      c₆.nreg r = c.nreg r := fun r h1 h2 h3 => by
    rw [R₆ r (by omega), f₅ r (by simp only [stSD6, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]; omega), k₄ r h1 h3]
  -- 6. the image
  obtain ⟨c₇, e₇, v₇, f₇, m₇, r₇, rm₇, o₇⟩ := cpL_exec (P := P) stSD7 (by decide) (by decide) c₆
    e₆.wb_right
  obtain ⟨c₈, t₈, e₈, ht₈, Z₈, K₈, R₈, rr₈, rm₈, o₈⟩ := mzFill_exec (P := P) c₇ e₇.wb_right
    (len := 37 * m + 13) (Zb := ib)
    (by rw [v₇ (5030, 9161) (by simp [stSD7]), k₆ _ (by omega) (by omega) (by omega), hL.len])
    (by rw [v₇ (5031, 9107) (by simp [stSD7]), k₆ _ (by omega) (by omega) (by omega), r07])
    (by omega) (by omega)
  have m84 : ∀ a, (a < 101 * m + 46 ∨ 106 * m + 49 ≤ a) → (a < ib ∨ ib + (37 * m + 13) ≤ a) →
      c₈.nmem a = c₄.nmem a := fun a h1 h2 => by
    rw [K₈ a h2, m₇, K₆ a (by omega), m₅]
  refine ⟨c₈, _, e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq (e₆.seq (e₇.seq e₈)))))), ?_,
    fun i hi => ?_, fun a ha => ?_, fun a h1 h2 h3 h4 => ?_, fun r h1 h2 h3 => ?_,
    by rw [rr₈, r₇, rr₆, r₅, rr₄, r₃, rr₂, r₁], by rw [rm₈, rm₇, rm₆, rm₅, rm₄, rm₃, rm₂, rm₁],
    by rw [o₈, o₇, o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · simp only [stSD4, stSD5, stSD6, stSD7, List.length_cons, List.length_nil, costD3]
    omega
  · have hne : ∀ i' < j, c₃.nmem (p + i') ≠ Ob + i := fun i' hi' e => by
      have := hlog i' hi'; rw [m₃, mlog i' hi'] at e; omega
    rw [m84 _ (by omega) (by omega), K₄ _ hne, m₃, O₂ i hi, m₁]
  · rcases ha with ⟨i, hi, hia⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases hr' : 101 * m + 46 ≤ a ∧ a < 106 * m + 49
      · by_cases hi' : ib ≤ a ∧ a < ib + (37 * m + 13)
        · have := Z₈ (a - ib) (by omega); rwa [show ib + (a - ib) = a by omega] at this
        · rw [K₈ a (by omega), m₇]
          have := Z₆ (a - (101 * m + 46)) (by omega)
          rwa [show 101 * m + 46 + (a - (101 * m + 46)) = a by omega] at this
      · by_cases hi' : ib ≤ a ∧ a < ib + (37 * m + 13)
        · have := Z₈ (a - ib) (by omega); rwa [show ib + (a - ib) = a by omega] at this
        · rw [m84 a (by omega) (by omega)]
          exact Z₄ a ⟨i, hi, by rw [m₃, mlog i hi]; exact hia⟩
    · by_cases hi' : ib ≤ a ∧ a < ib + (37 * m + 13)
      · have := Z₈ (a - ib) (by omega); rwa [show ib + (a - ib) = a by omega] at this
      · rw [K₈ a (by omega), m₇]
        have := Z₆ (a - (101 * m + 46)) (by omega)
        rwa [show 101 * m + 46 + (a - (101 * m + 46)) = a by omega] at this
    · have := Z₈ (a - ib) (by omega); rwa [show ib + (a - ib) = a by omega] at this
  · rw [m84 a h2 h3, K₄ a (fun i hi => by rw [m₃, mlog i hi]; exact h1 i hi), m₃, K₂ a h4, m₁]
  · rw [R₈ r (by omega), f₇ r (by simp only [stSD7, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false]; omega), k₆ r h1 h2 h3]

end StCall

end BKMNW

end PlanarFlow
