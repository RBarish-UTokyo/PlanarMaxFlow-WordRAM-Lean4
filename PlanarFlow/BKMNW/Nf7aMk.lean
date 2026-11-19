module

public import PlanarFlow.BKMNW.Nf7aWalk

/-!
# The marks of the darts and of the faces of the path

**`fmkProg`**: for `l < k`, with `t = PD[l]` (the frame index of the dart `d l`) and
`r = RV[t]` (its reverse): `ON[t] := 1`, `ON[r] := 1`, `MK[FL[t]] := 1`, `MK[FL[r]] := 1`.
Registers: `9401 = k`, `9402 = PD`, `9405 = FL`, `9406 = ON`, `9407 = MK`, `9430 = RV`,
`9436 = 1`; written `9450 … 9455`.

* `fmk2` (the marks after `l` steps, recursively) and **`fmk2_eq`** (`fmk2 … l i = 1` at the
  marked places, the start elsewhere);
* `fmkBody_exec` (`17` steps), **`fmkProg_exec`** (`19 k + 3` steps).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The marks after `l` steps: `1` at `x l'`, `y l'` (`l' < l`), the start elsewhere. -/
def fmk2 (base x y : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => base
  | l + 1 => fun i => if i = x l ∨ i = y l then 1 else fmk2 base x y l i

/-- **The marks after `l` steps.** -/
theorem fmk2_eq (base x y : ℕ → ℕ) (l i : ℕ) :
    fmk2 base x y l i = if ∃ l' < l, i = x l' ∨ i = y l' then 1 else base i := by
  induction l with
  | zero => simp [fmk2]
  | succ l ih =>
    simp only [fmk2, ih]
    by_cases h : i = x l ∨ i = y l
    · simp only [h, ↓reduceIte]
      rw [if_pos ⟨l, by omega, h⟩]
    · simp only [h, ↓reduceIte]
      by_cases h' : ∃ l' < l, i = x l' ∨ i = y l'
      · obtain ⟨l', hl', e⟩ := h'
        rw [if_pos ⟨l', hl', e⟩, if_pos ⟨l', by omega, e⟩]
      · rw [if_neg h', if_neg]
        rintro ⟨l', hl', e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hl' with hl' | rfl
        · exact h' ⟨l', hl', e⟩
        · exact h e

/-! ### The program -/

/-- One step: the two darts and their two faces. -/
def fmkBody : Stmt :=
  block [.addN 9451 9402 9450, .loadN 9451 9451, .addN 9452 9430 9451, .loadN 9452 9452,
    .addN 9453 9405 9451, .loadN 9453 9453, .addN 9454 9405 9452, .loadN 9454 9454,
    .addN 9455 9406 9451, .storeN 9455 9436, .addN 9455 9406 9452, .storeN 9455 9436,
    .addN 9455 9407 9453, .storeN 9455 9436, .addN 9455 9407 9454, .storeN 9455 9436,
    .addN 9450 9450 9436]

/-- **The marks.** -/
def fmkProg : Stmt := .seq (block [.constN 9450 0]) (.whileLtN 9450 9401 fmkBody)

variable {P : Input} {W : ℕ}

theorem fmkBody_exec (c : Config) (hc : WordsBounded W c) {PDb RVb FLb ONb MKb l : ℕ}
    (r02 : c.nreg 9402 = PDb) (r05 : c.nreg 9405 = FLb) (r06 : c.nreg 9406 = ONb)
    (r07 : c.nreg 9407 = MKb) (r30 : c.nreg 9430 = RVb) (r36 : c.nreg 9436 = 1)
    (r50 : c.nreg 9450 = l)
    (h1 : PDb + l ≤ W) (h2 : RVb + c.nmem (PDb + l) ≤ W) (h3 : FLb + c.nmem (PDb + l) ≤ W)
    (h4 : FLb + c.nmem (RVb + c.nmem (PDb + l)) ≤ W) (h5 : ONb + c.nmem (PDb + l) ≤ W)
    (h6 : ONb + c.nmem (RVb + c.nmem (PDb + l)) ≤ W)
    (h7 : MKb + c.nmem (FLb + c.nmem (PDb + l)) ≤ W)
    (h8 : MKb + c.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l))) ≤ W) (h9 : l + 1 ≤ W) :
    ∃ c' k, Exec P W fmkBody c c' k ∧ k = 17 ∧ c'.nreg 9450 = l + 1 ∧
      c'.nmem = upd (upd (upd (upd c.nmem (ONb + c.nmem (PDb + l)) 1)
        (ONb + c.nmem (RVb + c.nmem (PDb + l))) 1) (MKb + c.nmem (FLb + c.nmem (PDb + l))) 1)
        (MKb + c.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l)))) 1 ∧
      (∀ r, (r < 9450 ∨ 9455 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold fmkBody
  exec_block
  all_goals try ((try config_simp); (try simp only [r02, r05, r06, r07, r30, r36, r50]); omega)
  refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  all_goals config_simp
  all_goals try (simp only [r02, r05, r06, r07, r30, r36, r50])
  all_goals first | (simp only [upd_apply]; split_ifs <;> omega) |
    (funext a; simp only [upd_apply]; split_ifs <;> omega) | rfl

/-- **The marks on the machine**: from the dart indices `PD[l] < m` (`l < k`), the reverses
`RV[i] < m` and the labels `FL[i] ≤ m` (`i < m`), the regions `[ON, ON + m)` and `[MK, MK + m]`
disjoint from each other and from the read arrays: within `19 k + 3` steps the marks
`ON[i] = fmk2 ON₀ PD RP k i` (`i < m`) and `MK[a] = fmk2 MK₀ FT FR k a` (`a ≤ m`), all other
memory kept. -/
theorem fmkProg_exec (c : Config) (hc : WordsBounded W c) {k m PDb RVb FLb ONb MKb : ℕ}
    (r01 : c.nreg 9401 = k) (r02 : c.nreg 9402 = PDb) (r05 : c.nreg 9405 = FLb)
    (r06 : c.nreg 9406 = ONb) (r07 : c.nreg 9407 = MKb) (r30 : c.nreg 9430 = RVb)
    (r36 : c.nreg 9436 = 1)
    (hPD : ∀ l < k, c.nmem (PDb + l) < m) (hRV : ∀ i < m, c.nmem (RVb + i) < m)
    (hFL : ∀ i < m, c.nmem (FLb + i) ≤ m)
    (dW : ∀ a, (ONb ≤ a ∧ a < ONb + m) ∨ (MKb ≤ a ∧ a ≤ MKb + m) →
      (a < PDb ∨ PDb + k ≤ a) ∧ (a < RVb ∨ RVb + m ≤ a) ∧ (a < FLb ∨ FLb + m ≤ a))
    (dOM : ONb + m ≤ MKb ∨ MKb + m < ONb)
    (hW : PDb + RVb + FLb + ONb + MKb + k + m + 1 ≤ W) :
    ∃ c' t, Exec P W fmkProg c c' t ∧ t ≤ 19 * k + 3 ∧
      (∀ i < m, c'.nmem (ONb + i) = fmk2 (fun i => c.nmem (ONb + i)) (fun l => c.nmem (PDb + l))
      (fun l => c.nmem (RVb + c.nmem (PDb + l))) k i) ∧
      (∀ a ≤ m, c'.nmem (MKb + a) = fmk2 (fun a => c.nmem (MKb + a))
        (fun l => c.nmem (FLb + c.nmem (PDb + l)))
      (fun l => c.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l)))) k a) ∧
      (∀ a, ¬ (ONb ≤ a ∧ a < ONb + m) → ¬ (MKb ≤ a ∧ a ≤ MKb + m) → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 9450 ∨ 9455 < r) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, k₁, e₁, hk₁, a50, ak, am, ar, arm, ao⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 9450 0]) c c₁ k₁ ∧ k₁ = 1 ∧ c₁.nreg 9450 = 0 ∧
      (∀ r, r ≠ 9450 → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have hRP : ∀ l < k, c.nmem (RVb + c.nmem (PDb + l)) < m := fun l hl => hRV _ (hPD l hl)
  let J : ℕ → Config → Prop := fun l c' =>
    (∀ i < m, c'.nmem (ONb + i) = fmk2 (fun i => c.nmem (ONb + i)) (fun l => c.nmem (PDb + l))
      (fun l => c.nmem (RVb + c.nmem (PDb + l))) l i) ∧
    (∀ a ≤ m, c'.nmem (MKb + a) = fmk2 (fun a => c.nmem (MKb + a))
      (fun l => c.nmem (FLb + c.nmem (PDb + l)))
      (fun l => c.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l)))) l a) ∧
    (∀ a, ¬ (ONb ≤ a ∧ a < ONb + m) → ¬ (MKb ≤ a ∧ a ≤ MKb + m) → c'.nmem a = c.nmem a) ∧
    (∀ r, (r < 9450 ∨ 9455 < r) → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h50, j1, j2, j3, j4, j5, j6, j7⟩ := tgRange (P := P)
    (a := 9450) (b := 9401) (body := fmkBody) J (lo := 0) (hi := k) (B := 17) c₁ e₁.wb_right a50
    (by rw [ak _ (by omega), r01]) (Nat.zero_le _)
    ⟨fun i _ => by rw [am]; rfl, fun a _ => by rw [am]; rfl, fun a _ _ => by rw [am],
      fun r hr => ak r (by omega), ar, arm, ao⟩
    (fun l c' _ hl hw h50 h01 ⟨j1, j2, j3, j4, j5, j6, j7⟩ => by
      have ePD : c'.nmem (PDb + l) = c.nmem (PDb + l) :=
        j3 _ (fun h => by have := (dW _ (Or.inl h)).1; omega)
          (fun h => by have := (dW _ (Or.inr h)).1; omega)
      have ht := hPD l hl
      have hr := hRP l hl
      have eRV : c'.nmem (RVb + c.nmem (PDb + l)) = c.nmem (RVb + c.nmem (PDb + l)) :=
        j3 _ (fun h => by have := (dW _ (Or.inl h)).2.1; omega)
          (fun h => by have := (dW _ (Or.inr h)).2.1; omega)
      have eFT : c'.nmem (FLb + c.nmem (PDb + l)) = c.nmem (FLb + c.nmem (PDb + l)) :=
        j3 _ (fun h => by have := (dW _ (Or.inl h)).2.2; omega)
          (fun h => by have := (dW _ (Or.inr h)).2.2; omega)
      have eFR : c'.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l))) =
          c.nmem (FLb + c.nmem (RVb + c.nmem (PDb + l))) :=
        j3 _ (fun h => by have := (dW _ (Or.inl h)).2.2; omega)
          (fun h => by have := (dW _ (Or.inr h)).2.2; omega)
      have hft := hFL _ ht
      have hfr := hFL _ hr
      obtain ⟨c'', t, ex, htt, b50, bm, bk, br, brm, bo⟩ :=
        fmkBody_exec (P := P) c' hw (PDb := PDb) (RVb := RVb) (FLb := FLb) (ONb := ONb)
          (MKb := MKb) (l := l) (by rw [j4 _ (by omega), r02])
          (by rw [j4 _ (by omega), r05])
          (by rw [j4 _ (by omega), r06])
          (by rw [j4 _ (by omega), r07])
          (by rw [j4 _ (by omega), r30])
          (by rw [j4 _ (by omega), r36]) h50
          (by omega) (by rw [ePD]; omega) (by rw [ePD]; omega) (by rw [ePD, eRV]; omega)
          (by rw [ePD]; omega) (by rw [ePD, eRV]; omega) (by rw [ePD, eFT]; omega)
          (by rw [ePD, eRV, eFR]; omega) (by omega)
      rw [ePD, eRV, eFT, eFR] at bm
      refine ⟨c'', t, ex, htt.le, b50, by rw [bk _ (by omega)]; exact h01,
        fun i hi => ?_, fun a ha => ?_, fun a h1 h2 => ?_, fun r hr => by rw [bk r hr]; exact j4 r hr,
        by rw [br, j5], by rw [brm, j6], by rw [bo, j7]⟩
      · rw [bm]
        have d1 := dOM
        simp only [upd_apply, fmk2]
        rw [← j1 i hi]
        split_ifs <;> first | rfl | omega
      · rw [bm]
        have d1 := dOM
        simp only [upd_apply, fmk2]
        rw [← j2 a ha]
        split_ifs <;> first | rfl | omega
      · rw [bm]
        simp only [upd_apply]
        split_ifs <;> first | omega | exact j3 a h1 h2)
  refine ⟨c₂, _, e₁.seq e₂, by rw [hk₁]; simp only [Nat.sub_zero] at hk₂; omega, j1, j2, j3,
    fun r hr => by rw [j4 r hr], j5, j6, j7⟩

end BKMNW

end PlanarFlow
