module

public import PlanarFlow.BKMNW.NcTf
public import PlanarFlow.BKMNW.IteR23

/-!
# The run of the terminal-flag program `tfP`

`tfZ_loop`, `tfM_loop`, `tfG_loop` (the three loops), **`tfP_exec`** (see `NcTf.lean`).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PlanarFlow

namespace BKMNW

namespace NcStep

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs NegSSSP

variable {P : Input} {W : ℕ}

/-- **The vertex label `v` is hit**: the label of the first vertex `s`, or of the tail or the head
of one of the first `K` darts of the list. -/
def tfHit (mem : ℕ → ℕ) (LABb Lb RVb K s v : ℕ) : Prop :=
  mem (LABb + s) = v ∨ ∃ t < K, mem (LABb + mem (Lb + t)) = v ∨
    mem (LABb + mem (RVb + mem (Lb + t))) = v

open Classical in
/-- The flag of a label. -/
noncomputable def tfFlag (mem : ℕ → ℕ) (LABb Lb RVb K s v : ℕ) : ℕ :=
  if tfHit mem LABb Lb RVb K s v then 1 else 0

/-- The zero loop. -/
theorem tfZ_loop (c : Config) (hc : WordsBounded W c) {Vb n : ℕ} (r04 : c.nreg 9704 = Vb)
    (r07 : c.nreg 9707 = 0) (r06 : c.nreg 9706 = 1) (r11 : c.nreg 9711 = 0)
    (r12 : c.nreg 9712 = n) (w1 : Vb + n ≤ W) :
    ∃ c' k, Exec P W (.whileLtN 9707 9712 tfZ) c c' k ∧ k ≤ 5 * n + 2 ∧
      (∀ e < n, c'.nmem (Vb + e) = 0) ∧ (∀ a, (a < Vb ∨ Vb + n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9707 → r ≠ 9708 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Vb + e) = 0) ∧ (∀ a, (a < Vb ∨ Vb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9707 → r ≠ 9708 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, j1, j2, j3, jr, jrm, jo⟩ := forLoop_exec (P := P) (a := 9707)
    (bR := 9712) (body := tfZ) J (K := 3) (n := n) c hc r07 r12
    ⟨fun e he => absurd he (by omega), fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb ⟨j1, j2, j3, jr, jrm, jo⟩ => by
      obtain ⟨c'', k, ex, hk, hm, h07, hn, hr, hrm, ho⟩ := tfZ_exec (P := P) c' hw
        (by rw [j3 _ (by omega) (by omega), r04]) ha (by rw [j3 _ (by omega) (by omega), r06])
        (by rw [j3 _ (by omega) (by omega), r11]) (by omega) (by omega)
      refine ⟨c'', k, ex, by omega, h07, by rw [hn _ (by omega) (by omega)]; exact hb,
        fun e he => ?_, fun a h => ?_, fun r h1 h2 => by rw [hn r h1 h2, j3 r h1 h2],
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [iteF (by omega)]; exact j1 e he
        · rw [iteT rfl]
      · rw [hm, upd_apply, iteF (by omega)]; exact j2 a (by omega))
  exact ⟨c₂, k₂, e₂, hk₂, j1, j2, j3, jr, jrm, jo⟩

/-- The mark loop. -/
theorem tfM_loop (c₀ c : Config) (hc : WordsBounded W c) {m LABb Lb Vb RVb K s : ℕ}
    (r01 : c.nreg 9701 = LABb) (r02 : c.nreg 9702 = Lb) (r03 : c.nreg 9703 = K)
    (r04 : c.nreg 9704 = Vb) (r13 : c.nreg 9713 = RVb) (r07 : c.nreg 9707 = 0)
    (r06 : c.nreg 9706 = 1)
    (hLAB : ∀ i < m, c₀.nmem (LABb + i) ≤ m) (hL : ∀ t < K, c₀.nmem (Lb + t) < m)
    (hRV : ∀ i < m, c₀.nmem (RVb + i) < m) (hs : s < m)
    (o1 : LABb + m ≤ Vb) (o2 : Lb + K ≤ Vb) (o3 : RVb + m ≤ Vb) (w1 : Vb + m + 1 ≤ W)
    (wK : K + 1 ≤ W)
    (h0 : ∀ v ≤ m, c.nmem (Vb + v) = if c₀.nmem (LABb + s) = v then 1 else 0)
    (hk0 : ∀ a, (a < Vb ∨ Vb + m < a) → c.nmem a = c₀.nmem a) :
    ∃ c' k, Exec P W (.whileLtN 9707 9703 tfM) c c' k ∧ k ≤ 15 * K + 2 ∧
      (∀ v ≤ m, c'.nmem (Vb + v) = tfFlag c₀.nmem LABb Lb RVb K s v) ∧
      (∀ a, (a < Vb ∨ Vb + m < a) → c'.nmem a = c₀.nmem a) ∧
      (∀ r, r ≠ 9707 → r ≠ 9708 → r ≠ 9709 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ v ≤ m, c'.nmem (Vb + v) = tfFlag c₀.nmem LABb Lb RVb i s v) ∧
      (∀ a, (a < Vb ∨ Vb + m < a) → c'.nmem a = c₀.nmem a) ∧
      (∀ r, r ≠ 9707 → r ≠ 9708 → r ≠ 9709 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  have hJ0 : J 0 c := by
    refine ⟨fun v hv => ?_, hk0, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    rw [h0 v hv]
    unfold tfFlag tfHit
    congr 1
    apply propext
    constructor
    · exact Or.inl
    · rintro (h | ⟨t, ht, -⟩)
      · exact h
      · omega
  obtain ⟨c₂, k₂, e₂, hk₂, -, j1, j2, j3, jr, jrm, jo⟩ := forLoop_exec (P := P) (a := 9707)
    (bR := 9703) (body := tfM) J (K := 13) (n := K) c hc r07 r03 hJ0
    (fun i c' hi hw ha hb ⟨j1, j2, j3, jr, jrm, jo⟩ => by
      have q01 : c'.nreg 9701 = LABb := by rw [j3 _ (by omega) (by omega) (by omega), r01]
      have q02 : c'.nreg 9702 = Lb := by rw [j3 _ (by omega) (by omega) (by omega), r02]
      have q04 : c'.nreg 9704 = Vb := by rw [j3 _ (by omega) (by omega) (by omega), r04]
      have q13 : c'.nreg 9713 = RVb := by rw [j3 _ (by omega) (by omega) (by omega), r13]
      have q06 : c'.nreg 9706 = 1 := by rw [j3 _ (by omega) (by omega) (by omega), r06]
      have eL : c'.nmem (Lb + i) = c₀.nmem (Lb + i) := j2 _ (Or.inl (by omega))
      have hLi := hL i hi
      have eR : c'.nmem (RVb + c₀.nmem (Lb + i)) = c₀.nmem (RVb + c₀.nmem (Lb + i)) :=
        j2 _ (Or.inl (by omega))
      have hRi := hRV _ hLi
      have eA1 : c'.nmem (LABb + c₀.nmem (Lb + i)) = c₀.nmem (LABb + c₀.nmem (Lb + i)) :=
        j2 _ (Or.inl (by omega))
      have eA2 : c'.nmem (LABb + c₀.nmem (RVb + c₀.nmem (Lb + i))) =
          c₀.nmem (LABb + c₀.nmem (RVb + c₀.nmem (Lb + i))) := j2 _ (Or.inl (by omega))
      have hA1 := hLAB _ hLi
      have hA2 := hLAB _ hRi
      obtain ⟨c'', k, ex, hk, hm, h07, hn, hr, hrm, ho⟩ := tfM_exec (P := P) c' hw q01 q02 q04
        q13 ha q06 (by omega) (by rw [eL]; omega) (by rw [eL]; omega) (by rw [eL, eR]; omega)
        (by rw [eL, eA1]; omega) (by rw [eL, eR, eA2]; omega) (by rw [eL, eA1, eR]; omega)
        (by omega)
      rw [eL, eA1, eR, eA2] at hm
      refine ⟨c'', k, ex, by omega, h07,
        by rw [hn _ (by omega) (by omega) (by omega)]; exact hb, fun v hv => ?_, fun a h => ?_,
        fun r h1 h2 h3 => by rw [hn r h1 h2 h3, j3 r h1 h2 h3],
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply, upd_apply, j1 v hv]
        unfold tfFlag
        have key : tfHit c₀.nmem LABb Lb RVb (i + 1) s v ↔
            (tfHit c₀.nmem LABb Lb RVb i s v ∨ c₀.nmem (LABb + c₀.nmem (Lb + i)) = v ∨
              c₀.nmem (LABb + c₀.nmem (RVb + c₀.nmem (Lb + i))) = v) := by
          unfold tfHit
          constructor
          · rintro (h | ⟨t, ht, h⟩)
            · exact Or.inl (Or.inl h)
            · rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
              · exact Or.inl (Or.inr ⟨t, ht, h⟩)
              · exact Or.inr h
          · rintro ((h | ⟨t, ht, h⟩) | h)
            · exact Or.inl h
            · exact Or.inr ⟨t, by omega, h⟩
            · exact Or.inr ⟨i, by omega, h⟩
        by_cases h1 : Vb + v = Vb + c₀.nmem (LABb + c₀.nmem (RVb + c₀.nmem (Lb + i)))
        · rw [iteT h1, iteT (key.2 (Or.inr (Or.inr (by omega))))]
        · rw [iteF h1]
          by_cases h2 : Vb + v = Vb + c₀.nmem (LABb + c₀.nmem (Lb + i))
          · rw [iteT h2, iteT (key.2 (Or.inr (Or.inl (by omega))))]
          · rw [iteF h2]
            by_cases h3 : tfHit c₀.nmem LABb Lb RVb i s v
            · rw [iteT h3, iteT (key.2 (Or.inl h3))]
            · rw [iteF h3, iteF (fun h => by
                rcases key.1 h with h | h | h
                · exact h3 h
                · omega
                · omega)]
      · rw [hm, upd_apply, upd_apply, iteF (by omega), iteF (by omega)]; exact j2 a h)
  exact ⟨c₂, k₂, e₂, hk₂, j1, j2, j3, jr, jrm, jo⟩

/-- The gather loop. -/
theorem tfG_loop (c : Config) (hc : WordsBounded W c) {m LABb Vb Fb : ℕ}
    (r01 : c.nreg 9701 = LABb) (r04 : c.nreg 9704 = Vb) (r05 : c.nreg 9705 = Fb)
    (r07 : c.nreg 9707 = 0) (r06 : c.nreg 9706 = 1) (r00 : c.nreg 9700 = m)
    (hLAB : ∀ i < m, c.nmem (LABb + i) ≤ m) (o1 : LABb + m ≤ Fb) (o2 : Vb + m + 1 ≤ Fb)
    (w1 : Fb + m ≤ W) :
    ∃ c' k, Exec P W (.whileLtN 9707 9700 tfG) c c' k ∧ k ≤ 9 * m + 2 ∧
      (∀ e < m, c'.nmem (Fb + e) = c.nmem (Vb + c.nmem (LABb + e))) ∧
      (∀ a, (a < Fb ∨ Fb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9707 → r ≠ 9708 → r ≠ 9709 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ e < i, c'.nmem (Fb + e) = c.nmem (Vb + c.nmem (LABb + e))) ∧
      (∀ a, (a < Fb ∨ Fb + i ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, r ≠ 9707 → r ≠ 9708 → r ≠ 9709 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, -, j1, j2, j3, jr, jrm, jo⟩ := forLoop_exec (P := P) (a := 9707)
    (bR := 9700) (body := tfG) J (K := 7) (n := m) c hc r07 r00
    ⟨fun e he => absurd he (by omega), fun _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl⟩
    (fun i c' hi hw ha hb ⟨j1, j2, j3, jr, jrm, jo⟩ => by
      have eA : c'.nmem (LABb + i) = c.nmem (LABb + i) := j2 _ (Or.inl (by omega))
      have hA := hLAB i hi
      have eV : c'.nmem (Vb + c.nmem (LABb + i)) = c.nmem (Vb + c.nmem (LABb + i)) :=
        j2 _ (Or.inl (by omega))
      obtain ⟨c'', k, ex, hk, hm, h07, hn, hr, hrm, ho⟩ := tfG_exec (P := P) c' hw
        (by rw [j3 _ (by omega) (by omega) (by omega), r01])
        (by rw [j3 _ (by omega) (by omega) (by omega), r04])
        (by rw [j3 _ (by omega) (by omega) (by omega), r05]) ha
        (by rw [j3 _ (by omega) (by omega) (by omega), r06]) (by omega) (by rw [eA]; omega)
        (by omega) (by omega)
      rw [eA, eV] at hm
      refine ⟨c'', k, ex, by omega, h07,
        by rw [hn _ (by omega) (by omega) (by omega)]; exact hb, fun e he => ?_, fun a h => ?_,
        fun r h1 h2 h3 => by rw [hn r h1 h2 h3, j3 r h1 h2 h3],
        by rw [hr, jr], by rw [hrm, jrm], by rw [ho, jo]⟩
      · rw [hm, upd_apply]
        rcases Nat.lt_succ_iff_lt_or_eq.1 he with he | rfl
        · rw [iteF (by omega)]; exact j1 e he
        · rw [iteT rfl]
      · rw [hm, upd_apply, iteF (by omega)]; exact j2 a (by omega))
  exact ⟨c₂, k₂, e₂, hk₂, j1, j2, j3, jr, jrm, jo⟩

/-- **The terminal-flag program**: `F[i] = tfFlag … (LAB[i])` for `i < m` (see `NcTf.lean`). -/
theorem tfP_exec (c : Config) (hc : WordsBounded W c) {m LABb Lb K Vb Fb RVb s : ℕ}
    (r00 : c.nreg 9700 = m) (r01 : c.nreg 9701 = LABb) (r02 : c.nreg 9702 = Lb)
    (r03 : c.nreg 9703 = K) (r04 : c.nreg 9704 = Vb) (r05 : c.nreg 9705 = Fb)
    (r13 : c.nreg 9713 = RVb) (r14 : c.nreg 9714 = s)
    (hLAB : ∀ i < m, c.nmem (LABb + i) ≤ m) (hL : ∀ t < K, c.nmem (Lb + t) < m)
    (hRV : ∀ i < m, c.nmem (RVb + i) < m) (hs : s < m)
    (o1 : LABb + m ≤ Vb) (o2 : Lb + K ≤ Vb) (o3 : RVb + m ≤ Vb) (o4 : Vb + m + 1 ≤ Fb)
    (w1 : Fb + m ≤ W) (wK : K + 1 ≤ W) :
    ∃ c' k, Exec P W tfP c c' k ∧ k ≤ 5 * (m + 1) + 15 * K + 9 * m + 25 ∧
      (∀ i < m, c'.nmem (Fb + i) = tfFlag c.nmem LABb Lb RVb K s (c.nmem (LABb + i))) ∧
      (∀ a, (a < Vb ∨ Fb + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ TfScr r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  classical
  -- constants
  obtain ⟨c₁, k₁, e₁, hk₁, a06, a11, a07, a12, f₁, m₁, rr₁, rm₁, o₁⟩ :=
    tfInit_exec (P := P) c hc r00 (by omega)
  have g₁ : ∀ r, 9700 ≤ r → r ≤ 9705 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁ r (by unfold TfScr; omega)
  -- zeros
  obtain ⟨c₂, k₂, e₂, hk₂, z₂, n₂, f₂, rr₂, rm₂, o₂⟩ := tfZ_loop (P := P) c₁ e₁.wb_right
    (by rw [g₁ _ (by omega) (by omega), r04]) a07 a06 a11 a12 (by omega)
  -- the first vertex
  have eS : c₂.nmem (LABb + s) = c.nmem (LABb + s) := by
    rw [n₂ _ (Or.inl (by omega)), m₁]
  have hS := hLAB s hs
  obtain ⟨c₃, k₃, e₃, hk₃, m₃, b07, f₃, rr₃, rm₃, o₃⟩ := tfS_exec (P := P) c₂ e₂.wb_right
    (by rw [f₂ _ (by omega) (by omega), g₁ _ (by omega) (by omega), r01])
    (by rw [f₂ _ (by omega) (by omega), g₁ _ (by omega) (by omega), r04])
    (by rw [f₂ _ (by omega) (by omega), f₁ _ (by unfold TfScr; omega), r14])
    (by rw [f₂ _ (by omega) (by omega), a06]) (by omega) (by rw [eS]; omega)
  rw [eS] at m₃
  have q : ∀ r, ¬ TfScr r → c₃.nreg r = c.nreg r := fun r hr => by
    unfold TfScr at hr
    rw [f₃ r (by omega) (by omega), f₂ r (by omega) (by omega), f₁ r (by unfold TfScr; omega)]
  have q06 : c₃.nreg 9706 = 1 := by
    rw [f₃ _ (by omega) (by omega), f₂ _ (by omega) (by omega), a06]
  -- the marks
  obtain ⟨c₄, k₄, e₄, hk₄, v₄, n₄, f₄, rr₄, rm₄, o₄⟩ := tfM_loop (P := P) c c₃ e₃.wb_right
    (m := m) (s := s) (by rw [q _ (by unfold TfScr; omega), r01])
    (by rw [q _ (by unfold TfScr; omega), r02]) (by rw [q _ (by unfold TfScr; omega), r03])
    (by rw [q _ (by unfold TfScr; omega), r04]) (by rw [q _ (by unfold TfScr; omega), r13])
    b07 q06 hLAB hL hRV hs o1 o2 o3 (by omega) wK
    (fun v hv => by
      rw [m₃, upd_apply]
      by_cases h : Vb + v = Vb + c.nmem (LABb + s)
      · rw [iteT h, iteT (by omega)]
      · rw [iteF h, iteF (by omega), z₂ v (by omega)])
    (fun a ha => by
      rw [m₃, upd_apply, iteF (by omega), n₂ a (by omega), m₁])
  -- reset
  obtain ⟨c₅, k₅, e₅, hk₅, b07', f₅, m₅, rr₅, rm₅, o₅⟩ := tfR_exec (P := P) c₄ e₄.wb_right
  have q' : ∀ r, ¬ TfScr r → c₅.nreg r = c.nreg r := fun r hr => by
    have := hr; unfold TfScr at this
    rw [f₅ r (by omega), f₄ r (by omega) (by omega) (by omega), q r hr]
  -- the gather
  have hLAB₅ : ∀ i < m, c₅.nmem (LABb + i) ≤ m := fun i hi => by
    rw [m₅, n₄ _ (Or.inl (by omega))]; exact hLAB i hi
  obtain ⟨c₆, k₆, e₆, hk₆, g₆, n₆, f₆, rr₆, rm₆, o₆⟩ := tfG_loop (P := P) c₅ e₅.wb_right
    (m := m) (by rw [q' _ (by unfold TfScr; omega), r01])
    (by rw [q' _ (by unfold TfScr; omega), r04]) (by rw [q' _ (by unfold TfScr; omega), r05])
    b07' (by rw [f₅ _ (by omega), f₄ _ (by omega) (by omega) (by omega), q06])
    (by rw [q' _ (by unfold TfScr; omega), r00]) hLAB₅ (by omega) o4 w1
  refine ⟨c₆, k₁ + (k₂ + (k₃ + (k₄ + (k₅ + k₆)))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ e₆)))), by omega, fun i hi => ?_,
    fun a ha => ?_, fun r hr => ?_, by rw [rr₆, rr₅, rr₄, rr₃, rr₂, rr₁],
    by rw [rm₆, rm₅, rm₄, rm₃, rm₂, rm₁], by rw [o₆, o₅, o₄, o₃, o₂, o₁]⟩
  · have eA : c₄.nmem (LABb + i) = c.nmem (LABb + i) := n₄ _ (Or.inl (by omega))
    have hA := hLAB i hi
    rw [g₆ i hi, m₅, eA, v₄ _ hA]
  · rw [n₆ a (by omega), m₅]
    exact n₄ a (by omega)
  · have := hr; unfold TfScr at this
    rw [f₆ r (by omega) (by omega) (by omega), q' r hr]

end NcStep

end BKMNW

end PlanarFlow
