module

public import PlanarFlow.BKMNW.SmProg

/-!
# One step of `smD` on the machine: the choice of the case

After the classification scan `smA` (`SmProg.lean`), `smDsp` computes the node bit
`5360 = smNode cP cI gX gY gB` (`#P ≥ 3`, a dart of `smB`, and `smX ≠ ∅ ∨ smY = ∅ ∨` a dart inside
a hole) and, at a node, the words of the split in `5364 … 5371` (`SmSel`): the index `a` of the
dart `x`, the index `a'` of its reverse, `up` (the path is the dart `x`, else the point
`tail x`), `lpm` (the left piece is the piece map, else the piece without `x`, `rev x`), the vertex
numbers `v1`, `v2` of `tail x`, `head x`, the hole labels `t1`, `t2` of `tail x`, `head x`:

* peel (`gX = 1`): `(aX, aXr, 1, 0, vX, vXh, 0, hX)`;
* dump (`gX = 0`, `gY = 1`): `(aY, 0, 0, 1, vY, 0, tY, 0)`;
* pendant edge / edge (`gX = gY = 0`): `(aB, aBr, 1 - wB, 0, vB, vBh, 0, hB)`.

Registers written: `5360 … 5375`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open Finset WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

/-- The node bit. -/
abbrev smNode (cP cI gX gY gB : ℕ) : ℕ :=
  smAnd (smAnd (smSg (cP - 2)) gB) (smSg ((1 - gY) + gX + smSg cI))

/-- The words of the split in `5364 … 5371`. -/
def SmSel (c : Config) (a a' up lpm v1 v2 t1 t2 : ℕ) : Prop :=
  c.nreg 5364 = a ∧ c.nreg 5365 = a' ∧ c.nreg 5366 = up ∧ c.nreg 5367 = lpm ∧
    c.nreg 5368 = v1 ∧ c.nreg 5369 = v2 ∧ c.nreg 5370 = t1 ∧ c.nreg 5371 = t2

/-- The node bit into `5360`. -/
def smD0 : Stmt :=
  block [.subN 5372 5315 5311, .subN 5373 5372 5310, .subN 5372 5372 5373,
    .subN 5374 5316 5310, .subN 5373 5316 5374,
    .subN 5374 5310 5323, .addN 5374 5374 5317, .addN 5374 5374 5373, .subN 5375 5374 5310,
    .subN 5374 5374 5375,
    .subN 5375 5310 5327, .subN 5360 5372 5375, .subN 5375 5310 5374, .subN 5360 5360 5375]

/-- The peel. -/
def smBrX : Stmt :=
  block [.copyN 5364 5318, .copyN 5365 5319, .constN 5366 1, .constN 5367 0, .copyN 5368 5320,
    .copyN 5369 5321, .constN 5370 0, .copyN 5371 5322]

/-- The dump. -/
def smBrY : Stmt :=
  block [.copyN 5364 5324, .constN 5365 0, .constN 5366 0, .constN 5367 1, .copyN 5368 5325,
    .constN 5369 0, .copyN 5370 5326, .constN 5371 0]

/-- The pendant edge or the edge. -/
def smBrB : Stmt :=
  block [.copyN 5364 5328, .copyN 5365 5329, .subN 5366 5310 5332, .constN 5367 0,
    .copyN 5368 5330, .copyN 5369 5331, .constN 5370 0, .copyN 5371 5333]

/-- A leaf: all words `0`. -/
def smBr0 : Stmt :=
  block [.constN 5364 0, .constN 5365 0, .constN 5366 0, .constN 5367 0, .constN 5368 0,
    .constN 5369 0, .constN 5370 0, .constN 5371 0]

/-- **The choice of the case.** -/
def smDsp : Stmt :=
  .seq smD0 (.ifLtN 5313 5360 (.ifLtN 5313 5317 smBrX (.ifLtN 5313 5323 smBrY smBrB)) smBr0)

section Dsp

variable {P : Input} {W : ℕ}

theorem smD0_exec (c : Config) (hc : WordsBounded W c) (hW : 3 ≤ W)
    (r10 : c.nreg 5310 = 1) (r11 : c.nreg 5311 = 2) (g1 : c.nreg 5317 ≤ 1)
    (g2 : c.nreg 5323 ≤ 1) :
    ∃ c' t, Exec P W smD0 c c' t ∧ t = 14 ∧
      c'.nreg 5360 = smNode (c.nreg 5315) (c.nreg 5316) (c.nreg 5317) (c.nreg 5323) (c.nreg 5327) ∧
      (∀ x, (x < 5360 ∨ 5375 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smD0
  exec_block
  all_goals try (config_simp; (try simp only [r10, r11]); omega)
  refine ⟨rfl, ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [r10, r11]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem smBrX_exec (c : Config) (hc : WordsBounded W c) (hW : 2 ≤ W) :
    ∃ c' t, Exec P W smBrX c c' t ∧ t = 8 ∧
      SmSel c' (c.nreg 5318) (c.nreg 5319) 1 0 (c.nreg 5320) (c.nreg 5321) 0 (c.nreg 5322) ∧
      (∀ x, (x < 5364 ∨ 5371 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smBrX SmSel
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem smBrY_exec (c : Config) (hc : WordsBounded W c) (hW : 2 ≤ W) :
    ∃ c' t, Exec P W smBrY c c' t ∧ t = 8 ∧
      SmSel c' (c.nreg 5324) 0 0 1 (c.nreg 5325) 0 (c.nreg 5326) 0 ∧
      (∀ x, (x < 5364 ∨ 5371 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smBrY SmSel
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem smBrB_exec (c : Config) (hc : WordsBounded W c) (hW : 2 ≤ W)
    (r10 : c.nreg 5310 = 1) :
    ∃ c' t, Exec P W smBrB c c' t ∧ t = 8 ∧
      SmSel c' (c.nreg 5328) (c.nreg 5329) (1 - c.nreg 5332) 0 (c.nreg 5330) (c.nreg 5331) 0
        (c.nreg 5333) ∧
      (∀ x, (x < 5364 ∨ 5371 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smBrB SmSel
  exec_block
  all_goals try (config_simp; (try simp only [r10]); omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; (try simp only [r10]); done)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem smBr0_exec (c : Config) (hc : WordsBounded W c) (hW : 2 ≤ W) :
    ∃ c' t, Exec P W smBr0 c c' t ∧ t = 8 ∧ SmSel c' 0 0 0 0 0 0 0 0 ∧
      (∀ x, (x < 5364 ∨ 5371 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold smBr0 SmSel
  exec_block
  all_goals try (config_simp; omega)
  refine ⟨rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  all_goals try (config_simp; done)
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The choice of the case** (see the module docstring), within `27` steps. -/
theorem smDsp_exec (c : Config) (hc : WordsBounded W c) (hW : 3 ≤ W)
    (r10 : c.nreg 5310 = 1) (r11 : c.nreg 5311 = 2) (r13 : c.nreg 5313 = 0)
    (g1 : c.nreg 5317 ≤ 1) (g2 : c.nreg 5323 ≤ 1) :
    ∃ c' t, Exec P W smDsp c c' t ∧ t ≤ 27 ∧
      c'.nreg 5360 = smNode (c.nreg 5315) (c.nreg 5316) (c.nreg 5317) (c.nreg 5323)
        (c.nreg 5327) ∧ c'.nreg 5366 ≤ 1 ∧ c'.nreg 5367 ≤ 1 ∧
      (c'.nreg 5360 ≠ 0 → c.nreg 5317 = 1 →
        SmSel c' (c.nreg 5318) (c.nreg 5319) 1 0 (c.nreg 5320) (c.nreg 5321) 0 (c.nreg 5322)) ∧
      (c'.nreg 5360 ≠ 0 → c.nreg 5317 = 0 → c.nreg 5323 = 1 →
        SmSel c' (c.nreg 5324) 0 0 1 (c.nreg 5325) 0 (c.nreg 5326) 0) ∧
      (c'.nreg 5360 ≠ 0 → c.nreg 5317 = 0 → c.nreg 5323 = 0 →
        SmSel c' (c.nreg 5328) (c.nreg 5329) (1 - c.nreg 5332) 0 (c.nreg 5330) (c.nreg 5331) 0
          (c.nreg 5333)) ∧
      (∀ x, (x < 5360 ∨ 5375 < x) → c'.nreg x = c.nreg x) ∧ c'.nmem = c.nmem ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨c₁, t₁, e₁, ht₁, a60, an₁, am₁, ar₁, arm₁, ao₁⟩ :=
    smD0_exec (P := P) c hc hW r10 r11 g1 g2
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 5360 ∨ 5375 < x) → c₁.nreg x = c.nreg x := an₁
  have h13 : c₁.nreg 5313 = 0 := by rw [q _ (by omega), r13]
  -- the selection on `c₁`
  have sel : ∀ (s : Stmt) (a a' up lpm v1 v2 t1 t2 : ℕ),
      (∃ c' t, Exec P W s c₁ c' t ∧ t = 8 ∧ SmSel c' a a' up lpm v1 v2 t1 t2 ∧
        (∀ x, (x < 5364 ∨ 5371 < x) → c'.nreg x = c₁.nreg x) ∧ c'.nmem = c₁.nmem ∧
        c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output) →
      ∃ c' t, Exec P W s c₁ c' t ∧ t = 8 ∧ SmSel c' a a' up lpm v1 v2 t1 t2 ∧
        (∀ x, (x < 5364 ∨ 5371 < x) → c'.nreg x = c₁.nreg x) ∧ c'.nmem = c₁.nmem ∧
        c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := fun _ _ _ _ _ _ _ _ _ h => h
  by_cases hn : c₁.nreg 5360 = 0
  · have hlt : ¬ c₁.nreg 5313 < c₁.nreg 5360 := by rw [h13, hn]; omega
    obtain ⟨c₂, t₂, e₂, ht₂, hs, bn, bm, br, brm, bo⟩ := smBr0_exec (P := P) c₁ hw₁ (by omega)
    have h60 : c₂.nreg 5360 = c₁.nreg 5360 := bn _ (by omega)
    refine ⟨c₂, t₁ + (t₂ + 2), .seq e₁ (.ifLtN_false hlt e₂), by omega, by rw [h60, a60],
      by have := hs.2.2.1; omega, by have := hs.2.2.2.1; omega,
      fun h => absurd (h60 ▸ hn) h, fun h => absurd (h60 ▸ hn) h, fun h => absurd (h60 ▸ hn) h,
      fun x hx => by rw [bn x (by omega), q x hx], by rw [bm, am₁], by rw [br, ar₁],
      by rw [brm, arm₁], by rw [bo, ao₁]⟩
  have hlt : c₁.nreg 5313 < c₁.nreg 5360 := by rw [h13]; omega
  rcases Nat.lt_or_ge (c.nreg 5317) 1 with hx | hx
  · have hx0 : c.nreg 5317 = 0 := by omega
    have hlt2 : ¬ c₁.nreg 5313 < c₁.nreg 5317 := by rw [h13, q _ (by omega), hx0]; omega
    rcases Nat.lt_or_ge (c.nreg 5323) 1 with hy | hy
    · have hy0 : c.nreg 5323 = 0 := by omega
      have hlt3 : ¬ c₁.nreg 5313 < c₁.nreg 5323 := by rw [h13, q _ (by omega), hy0]; omega
      obtain ⟨c₂, t₂, e₂, ht₂, hs, bn, bm, br, brm, bo⟩ := smBrB_exec (P := P) c₁ hw₁ (by omega)
        (by rw [q _ (by omega), r10])
      refine ⟨c₂, t₁ + (t₂ + 2 + 2 + 1), .seq e₁ (.ifLtN_true hlt (.ifLtN_false hlt2
        (.ifLtN_false hlt3 e₂))), by omega, by rw [bn _ (by omega), a60],
        by have := hs.2.2.1; omega, by have := hs.2.2.2.1; omega,
        fun _ h => absurd h (by omega), fun _ _ h => absurd h (by omega), fun _ _ _ => ?_,
        fun x hx => by rw [bn x (by omega), q x hx], by rw [bm, am₁], by rw [br, ar₁],
        by rw [brm, arm₁], by rw [bo, ao₁]⟩
      simpa only [q _ (show (5328 : ℕ) < 5360 ∨ _ from Or.inl (by omega)),
        q _ (show (5329 : ℕ) < 5360 ∨ _ from Or.inl (by omega)),
        q _ (show (5330 : ℕ) < 5360 ∨ _ from Or.inl (by omega)),
        q _ (show (5331 : ℕ) < 5360 ∨ _ from Or.inl (by omega)),
        q _ (show (5332 : ℕ) < 5360 ∨ _ from Or.inl (by omega)),
        q _ (show (5333 : ℕ) < 5360 ∨ _ from Or.inl (by omega))] using hs
    · have hy1 : c.nreg 5323 = 1 := by omega
      have hlt3 : c₁.nreg 5313 < c₁.nreg 5323 := by rw [h13, q _ (by omega), hy1]; omega
      obtain ⟨c₂, t₂, e₂, ht₂, hs, bn, bm, br, brm, bo⟩ := smBrY_exec (P := P) c₁ hw₁ (by omega)
      refine ⟨c₂, t₁ + (t₂ + 1 + 2 + 1), .seq e₁ (.ifLtN_true hlt (.ifLtN_false hlt2
        (.ifLtN_true hlt3 e₂))), by omega, by rw [bn _ (by omega), a60],
        by have := hs.2.2.1; omega, by have := hs.2.2.2.1; omega,
        fun _ h => absurd h (by omega), fun _ _ _ => ?_, fun _ _ h => absurd h (by omega),
        fun x hx => by rw [bn x (by omega), q x hx], by rw [bm, am₁], by rw [br, ar₁],
        by rw [brm, arm₁], by rw [bo, ao₁]⟩
      simpa only [q _ (show (5324 : ℕ) < 5360 ∨ _ from Or.inl (by omega)),
        q _ (show (5325 : ℕ) < 5360 ∨ _ from Or.inl (by omega)),
        q _ (show (5326 : ℕ) < 5360 ∨ _ from Or.inl (by omega))] using hs
  · have hx1 : c.nreg 5317 = 1 := by omega
    have hlt2 : c₁.nreg 5313 < c₁.nreg 5317 := by rw [h13, q _ (by omega), hx1]; omega
    obtain ⟨c₂, t₂, e₂, ht₂, hs, bn, bm, br, brm, bo⟩ := smBrX_exec (P := P) c₁ hw₁ (by omega)
    refine ⟨c₂, t₁ + (t₂ + 1 + 1), .seq e₁ (.ifLtN_true hlt (.ifLtN_true hlt2 e₂)), by omega,
      by rw [bn _ (by omega), a60], by have := hs.2.2.1; omega, by have := hs.2.2.2.1; omega,
      fun _ _ => ?_, fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega),
      fun x hx => by rw [bn x (by omega), q x hx], by rw [bm, am₁], by rw [br, ar₁],
      by rw [brm, arm₁], by rw [bo, ao₁]⟩
    simpa only [q _ (show (5318 : ℕ) < 5360 ∨ _ from Or.inl (by omega)),
      q _ (show (5319 : ℕ) < 5360 ∨ _ from Or.inl (by omega)),
      q _ (show (5320 : ℕ) < 5360 ∨ _ from Or.inl (by omega)),
      q _ (show (5321 : ℕ) < 5360 ∨ _ from Or.inl (by omega)),
      q _ (show (5322 : ℕ) < 5360 ∨ _ from Or.inl (by omega))] using hs

end Dsp

end BKMNW

end PlanarFlow
