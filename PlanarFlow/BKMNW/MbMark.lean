module

public import PlanarFlow.BKMNW.MbOut

/-!
# Miller's base, step 4: the classes on the separator cycle

The `k` codes of the separator cycle (`stCode`: `3 q` for the dart `old q`, `3 q + 1` for the
spoke `up (φ q)`, `3 q + 2` for the spoke `down q`) are read from `CY`; a code `3 q` marks the
class key `TKc[q]` of the compacted dart `q`, a code `3 q + 1` the key `TKc[CR[q]]` of its reverse
(the vertex of `φ q` is that of `α q`); a code `3 q + 2` (a face centre) marks nothing.

* `kmHit` (the key a code marks), `kmP0`, `kmP1`, `kmBody`, **`kmk`**, `kmBody_exec`,
  **`kmk_exec`** (`17 k + 6` steps): `KM[x] ≠ 0 ↔ ∃ l < k, kmHit … l x` for `x < n` (from a zero
  `KM`); registers `5130 = k`, `5131 = CYb`, `5132 = TKCb`, `5133 = CRb`, `5134 = KMb`, written
  `5135 … 5142`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-! ### The marks of the cycle codes -/

/-- **The key marked by the code number `l`**: `TKc[q]` for the code `3 q`, `TKc[CR[q]]` for the
code `3 q + 1`. -/
def kmHit (m : ℕ → ℕ) (CYb TKCb CRb l x : ℕ) : Prop :=
  (m (CYb + l) % 3 = 0 ∧ m (TKCb + m (CYb + l) / 3) = x) ∨
  (m (CYb + l) % 3 = 1 ∧ m (TKCb + m (CRb + m (CYb + l) / 3)) = x)

/-- The mark of a code `3 q`. -/
def kmP0 : Stmt := block [.addN 5142 5132 5140, .loadN 5142 5142, .addN 5142 5134 5142,
  .storeN 5142 5135]

/-- The mark of a code `3 q + 1`. -/
def kmP1 : Stmt := block [.addN 5142 5133 5140, .loadN 5142 5142, .addN 5142 5132 5142,
  .loadN 5142 5142, .addN 5142 5134 5142, .storeN 5142 5135]

/-- One code (`5135 = 1`, `5136 = 3`, `5137 = 2`, `5138 = l`). -/
def kmBody : Stmt :=
  .seq (block [.addN 5139 5131 5138, .loadN 5139 5139, .divN 5140 5139 5136,
    .modN 5141 5139 5136])
    (.seq (.ifLtN 5141 5135 kmP0 (.ifLtN 5141 5137 kmP1 .skip)) (block [.addN 5138 5138 5135]))

/-- **The marks of the cycle codes.** -/
def kmk : Stmt :=
  .seq (block [.constN 5135 1, .constN 5136 3, .constN 5137 2, .constN 5138 0])
    (.whileLtN 5138 5130 kmBody)

section Km

variable {P : Input} {W : ℕ}

theorem kmBody_exec (c : Config) (hc : WordsBounded W c) {CYb TKCb CRb KMb l : ℕ}
    (r1 : c.nreg 5131 = CYb) (r2 : c.nreg 5132 = TKCb) (r3 : c.nreg 5133 = CRb)
    (r4 : c.nreg 5134 = KMb) (r5 : c.nreg 5135 = 1) (r6 : c.nreg 5136 = 3)
    (r7 : c.nreg 5137 = 2) (r8 : c.nreg 5138 = l)
    (w1 : CYb + l ≤ W) (w2 : TKCb + c.nmem (CYb + l) / 3 ≤ W)
    (w3 : CRb + c.nmem (CYb + l) / 3 ≤ W)
    (w4 : KMb + c.nmem (TKCb + c.nmem (CYb + l) / 3) ≤ W)
    (w5 : TKCb + c.nmem (CRb + c.nmem (CYb + l) / 3) ≤ W)
    (w6 : KMb + c.nmem (TKCb + c.nmem (CRb + c.nmem (CYb + l) / 3)) ≤ W) (w7 : l + 1 ≤ W) :
    ∃ c' t, Exec P W kmBody c c' t ∧ t ≤ 15 ∧ c'.nreg 5138 = l + 1 ∧
      c'.nmem = (if c.nmem (CYb + l) % 3 = 0 then
          upd c.nmem (KMb + c.nmem (TKCb + c.nmem (CYb + l) / 3)) 1
        else if c.nmem (CYb + l) % 3 = 1 then
          upd c.nmem (KMb + c.nmem (TKCb + c.nmem (CRb + c.nmem (CYb + l) / 3))) 1
        else c.nmem) ∧
      (∀ x, (x < 5138 ∨ 5142 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set v := c.nmem (CYb + l) with hv
  obtain ⟨c₁, t₁, e₁, ht₁, a9, a0, a1, an₁, am₁, ar₁, arm₁, ao₁⟩ : ∃ c₁ t₁,
      Exec P W (block [.addN 5139 5131 5138, .loadN 5139 5139, .divN 5140 5139 5136,
        .modN 5141 5139 5136]) c c₁ t₁ ∧ t₁ = 4 ∧
      c₁.nreg 5139 = v ∧ c₁.nreg 5140 = v / 3 ∧ c₁.nreg 5141 = v % 3 ∧
      (∀ x, (x < 5139 ∨ 5141 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    have hvW : v ≤ W := hc.2 _
    exec_block
    all_goals try (config_simp; simp only [r1, r6, r8, ← hv]; omega)
    all_goals try (config_simp; simp only [r1, r6, r8, ← hv]; first
      | exact (Nat.div_le_self _ _).trans hvW
      | exact (Nat.mod_le _ _).trans hvW)
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; simp only [r1, r6, r8, ← hv]; done)
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have k : ∀ x, (x < 5139 ∨ 5141 < x) → c₁.nreg x = c.nreg x := an₁
  have k2 : c₁.nreg 5132 = TKCb := by rw [k _ (by omega), r2]
  have k3 : c₁.nreg 5133 = CRb := by rw [k _ (by omega), r3]
  have k4 : c₁.nreg 5134 = KMb := by rw [k _ (by omega), r4]
  have k5 : c₁.nreg 5135 = 1 := by rw [k _ (by omega), r5]
  have k7 : c₁.nreg 5137 = 2 := by rw [k _ (by omega), r7]
  obtain ⟨c₂, t₂, e₂, ht₂, bm₂, bn₂, br₂, brm₂, bo₂⟩ : ∃ c₂ t₂,
      Exec P W (.ifLtN 5141 5135 kmP0 (.ifLtN 5141 5137 kmP1 .skip)) c₁ c₂ t₂ ∧ t₂ ≤ 9 ∧
      (c₂.nmem = if v % 3 = 0 then upd c.nmem (KMb + c.nmem (TKCb + v / 3)) 1
        else if v % 3 = 1 then upd c.nmem (KMb + c.nmem (TKCb + c.nmem (CRb + v / 3))) 1
        else c.nmem) ∧
      (∀ x, x ≠ 5142 → c₂.nreg x = c₁.nreg x) ∧
      c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
    by_cases h0 : v % 3 = 0
    · have hlt : c₁.nreg 5141 < c₁.nreg 5135 := by rw [a1, k5, h0]; omega
      obtain ⟨c₂, t₂, e₂, ht₂, pm, pn, pr, prm, po⟩ : ∃ c₂ t₂, Exec P W kmP0 c₁ c₂ t₂ ∧
          t₂ = 4 ∧ c₂.nmem = upd c.nmem (KMb + c.nmem (TKCb + v / 3)) 1 ∧
          (∀ x, x ≠ 5142 → c₂.nreg x = c₁.nreg x) ∧
          c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
        unfold kmP0
        exec_block
        all_goals try (config_simp; simp only [k2, k4, k5, a0, am₁]; omega)
        refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
        · config_simp; simp only [k2, k4, k5, a0, am₁]
        · config_simp; simp only [upd_apply]; split_ifs <;> omega
      exact ⟨c₂, t₂ + 1, .ifLtN_true hlt e₂, by omega, by rw [pm, iteT h0], pn, pr, prm, po⟩
    · have hnlt : ¬ c₁.nreg 5141 < c₁.nreg 5135 := by rw [a1, k5]; omega
      by_cases h1 : v % 3 = 1
      · have hlt : c₁.nreg 5141 < c₁.nreg 5137 := by rw [a1, k7, h1]; omega
        obtain ⟨c₂, t₂, e₂, ht₂, pm, pn, pr, prm, po⟩ : ∃ c₂ t₂, Exec P W kmP1 c₁ c₂ t₂ ∧
            t₂ = 6 ∧ c₂.nmem = upd c.nmem (KMb + c.nmem (TKCb + c.nmem (CRb + v / 3))) 1 ∧
            (∀ x, x ≠ 5142 → c₂.nreg x = c₁.nreg x) ∧
            c₂.rreg = c₁.rreg ∧ c₂.rmem = c₁.rmem ∧ c₂.output = c₁.output := by
          unfold kmP1
          exec_block
          all_goals try (config_simp; simp only [k2, k3, k4, k5, a0, am₁]; omega)
          refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
          · config_simp; simp only [k2, k3, k4, k5, a0, am₁]
          · config_simp; simp only [upd_apply]; split_ifs <;> omega
        exact ⟨c₂, t₂ + 1 + 2, .ifLtN_false hnlt (.ifLtN_true hlt e₂), by omega,
          by rw [pm, iteF h0, iteT h1], pn, pr, prm, po⟩
      · have hnlt' : ¬ c₁.nreg 5141 < c₁.nreg 5137 := by rw [a1, k7]; omega
        exact ⟨c₁, 0 + 2 + 2, .ifLtN_false hnlt (.ifLtN_false hnlt' (.skip hw₁)), by omega,
          by rw [am₁, iteF h0, iteF h1], fun _ _ => rfl, rfl, rfl, rfl⟩
  have hw₂ := e₂.wb_right
  have h38 : c₂.nreg 5138 = l := by rw [bn₂ _ (by omega), k _ (by omega), r8]
  have h35 : c₂.nreg 5135 = 1 := by rw [bn₂ _ (by omega), k5]
  obtain ⟨c₃, t₃, e₃, ht₃, d38, dn₃, dm₃, dr₃, drm₃, do₃⟩ : ∃ c₃ t₃,
      Exec P W (block [.addN 5138 5138 5135]) c₂ c₃ t₃ ∧ t₃ = 1 ∧ c₃.nreg 5138 = l + 1 ∧
      (∀ x, x ≠ 5138 → c₃.nreg x = c₂.nreg x) ∧ c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧
      c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    exec_block
    all_goals try (config_simp; simp only [h38, h35]; omega)
    refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [h38, h35]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  refine ⟨c₃, t₁ + (t₂ + t₃), .seq e₁ (.seq e₂ e₃), by omega, d38, by rw [dm₃, bm₂],
    fun x hx => ?_, by rw [dr₃, br₂, ar₁], by rw [drm₃, brm₂, arm₁], by rw [do₃, bo₂, ao₁]⟩
  rw [dn₃ _ (by omega), bn₂ _ (by omega), k _ (by omega)]

/-- **The marks of the cycle codes**: with `KM` zero on `[KMb, KMb + n)`, the codes `< 3 m`, the
reverses `CR[q] < m` and the keys `TKc[q] < n` (`q < m`), all three arrays below `KMb`, within
`17 k + 6` steps `KM[x] ≠ 0 ↔ ∃ l < k, kmHit … l x` for `x < n`; memory outside
`[KMb, KMb + n)`, registers outside `5135 … 5142`, reals and output kept. -/
theorem kmk_exec (c : Config) (hc : WordsBounded W c) {k m n CYb TKCb CRb KMb : ℕ}
    (r0 : c.nreg 5130 = k) (r1 : c.nreg 5131 = CYb) (r2 : c.nreg 5132 = TKCb)
    (r3 : c.nreg 5133 = CRb) (r4 : c.nreg 5134 = KMb)
    (lay : CYb + k ≤ KMb ∧ TKCb + m ≤ KMb ∧ CRb + m ≤ KMb ∧ KMb + n ≤ W ∧ k + 3 ≤ W)
    (hcy : ∀ l < k, c.nmem (CYb + l) < 3 * m) (hcr : ∀ q < m, c.nmem (CRb + q) < m)
    (htk : ∀ q < m, c.nmem (TKCb + q) < n) (hz : ∀ x < n, c.nmem (KMb + x) = 0) :
    ∃ c' t, Exec P W kmk c c' t ∧ t ≤ 17 * k + 6 ∧
      (∀ x < n, (c'.nmem (KMb + x) ≠ 0 ↔ ∃ l < k, kmHit c.nmem CYb TKCb CRb l x)) ∧
      (∀ a, (a < KMb ∨ KMb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 5135 ∨ 5142 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨l1, l2, l3, l4, l5⟩ := lay
  unfold kmk
  obtain ⟨c₁, k₁, e₁, hk₁, g5, g6, g7, g8, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 5135 1, .constN 5136 3, .constN 5137 2, .constN 5138 0]) c c₁ k₁ ∧
      k₁ = 4 ∧ c₁.nreg 5135 = 1 ∧ c₁.nreg 5136 = 3 ∧ c₁.nreg 5137 = 2 ∧ c₁.nreg 5138 = 0 ∧
      (∀ x, (x < 5135 ∨ 5138 < x) → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
    all_goals try (config_simp; done)
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 5135 ∨ 5138 < x) → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 5138 ∨ 5142 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ x < n, (c'.nmem (KMb + x) ≠ 0 ↔ ∃ l < i, kmHit m₀ CYb TKCb CRb l x)) ∧
    (∀ a, (a < KMb ∨ KMb + n ≤ a) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h38, j1, j2, j3, j4, j5, j6⟩ := tgRange (P := P)
    (a := 5138) (b := 5130) (body := kmBody) J (B := 15) c₁ hw₁ g8
    (by rw [q _ (by omega), r0]) (Nat.zero_le k)
    ⟨fun _ _ => rfl, fun x hx => by
      rw [gm₁, hz x hx]; simp only [ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
      intro l hl; omega, fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h38 h30 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 5138 ∨ 5142 < x) → c'.nreg x = c₁.nreg x := j1
      have eY : c'.nmem (CYb + i) = m₀ (CYb + i) := j3 _ (Or.inl (by omega))
      have hq : m₀ (CYb + i) / 3 < m := by have := hcy i hhi; omega
      have eT : c'.nmem (TKCb + m₀ (CYb + i) / 3) = m₀ (TKCb + m₀ (CYb + i) / 3) :=
        j3 _ (Or.inl (by omega))
      have eR : c'.nmem (CRb + m₀ (CYb + i) / 3) = m₀ (CRb + m₀ (CYb + i) / 3) :=
        j3 _ (Or.inl (by omega))
      have hr : m₀ (CRb + m₀ (CYb + i) / 3) < m := hcr _ hq
      have eT' : c'.nmem (TKCb + m₀ (CRb + m₀ (CYb + i) / 3)) =
          m₀ (TKCb + m₀ (CRb + m₀ (CYb + i) / 3)) := j3 _ (Or.inl (by omega))
      have ht1 := htk _ hq
      have ht2 := htk _ hr
      obtain ⟨c'', t, ex, ht, h38', hm', hn', hr', hrm', ho'⟩ :=
        kmBody_exec (P := P) c' hw (CYb := CYb) (TKCb := TKCb) (CRb := CRb) (KMb := KMb)
          (by rw [f _ (by omega), q _ (by omega), r1]) (by rw [f _ (by omega), q _ (by omega), r2])
          (by rw [f _ (by omega), q _ (by omega), r3]) (by rw [f _ (by omega), q _ (by omega), r4])
          (by rw [f _ (by omega), g5]) (by rw [f _ (by omega), g6]) (by rw [f _ (by omega), g7])
          h38 (by omega) (by rw [eY]; omega) (by rw [eY]; omega) (by rw [eY, eT]; omega)
          (by rw [eY, eR]; omega) (by rw [eY, eR, eT']; omega) (by omega)
      rw [eY, eT, eR, eT'] at hm'
      refine ⟨c'', t, ex, ht, h38', by rw [hn' _ (by omega)]; exact h30,
        fun x hx => by rw [hn' x hx, f x hx], fun x hx => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · have step : (∃ l < i + 1, kmHit m₀ CYb TKCb CRb l x) ↔
            (∃ l < i, kmHit m₀ CYb TKCb CRb l x) ∨ kmHit m₀ CYb TKCb CRb i x := by
          constructor
          · rintro ⟨l, hl, h⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl | rfl
            · exact Or.inl ⟨l, hl, h⟩
            · exact Or.inr h
          · rintro (⟨l, hl, h⟩ | h)
            · exact ⟨l, by omega, h⟩
            · exact ⟨i, by omega, h⟩
        rw [step, ← j2 x hx, hm']
        unfold kmHit
        split_ifs with h0 h1
        · by_cases hxe : m₀ (TKCb + m₀ (CYb + i) / 3) = x
          · subst hxe; simp [h0]
          · rw [upd_other _ _ _ (by omega)]; simp [hxe, h0]
        · by_cases hxe : m₀ (TKCb + m₀ (CRb + m₀ (CYb + i) / 3)) = x
          · subst hxe; simp [h1]
          · rw [upd_other _ _ _ (by omega)]; simp [hxe, h0, h1]
        · simp [h0, h1]
      · rw [hm']
        split_ifs
        · rw [upd_other _ _ _ (by omega)]; exact j3 a ha
        · rw [upd_other _ _ _ (by omega)]; exact j3 a ha
        · exact j3 a ha)
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3,
    fun x hx => by rw [j1 x (by omega), q x (by omega)], by rw [j4, gr₁], by rw [j5, grm₁],
    by rw [j6, go₁]⟩

end Km

end BKMNW

end PlanarFlow
