module

public import PlanarFlow.BKMNW.LinLoops

/-!
# The index map of a child's darts in its parent's numbering, and a copy-scatter

The frames of the max-flow driver number the darts of a piece map in the increasing order of a
global numbering (`PlanarFlow/BKMNW/MfFrame.lean`, the array `GID`). The darts of a child call
are darts of the parent call, so the parent index of every child dart is found by **one merge**
of the two sorted arrays `GID`.

* **`lxProg`** (merge; registers `6600 = m`, `6601 = GPb`, `6602 = mc`, `6603 = GCb`,
  `6604 = ILb`; scratch `6605 … 6610`): for `i < m`, if `j < mc` and `GC[j] = GP[i]` then
  `IL[j] := i`, `j := j + 1`. **`lxProg_exec`** (`15 m + 5` steps): with `GP` strictly increasing
  on `[0, m)`, `GC` strictly increasing on `[0, mc)` and every `GC[k]` among the `GP[i]`,
  `IL[k] < m` and `GP[IL[k]] = GC[k]` for every `k < mc`.
* **`lcsProg`** (copy-scatter `OUT[IX[j]] := V[j]`, `j < mc`; registers `6620 = mc`,
  `6621 = IXb`, `6622 = Vb`, `6623 = OUTb`; scratch `6624 … 6627`), **`lcsProg_exec`**
  (`9 mc + 4` steps; `IX` injective).
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace PlanarFlow

namespace BKMNW

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs

section Exec

variable {P : Input} {W : ℕ}

/-! ### The merge -/

/-- The write of a found index: `IL[j] := i`, `j := j + 1`. -/
def lxHit : Stmt := block [.addN 6608 6604 6607, .storeN 6608 6606, .addN 6607 6607 6605]

/-- `gp := GP[i]`, `gc := GC[j]`; if `j < mc` and `gc = gp`: `IL[j] := i`, `j := j + 1`;
`i := i + 1`. -/
def lxBody : Stmt :=
  .seq (block [.addN 6608 6601 6606, .loadN 6609 6608, .addN 6608 6603 6607, .loadN 6610 6608])
    (.seq (.ifLtN 6607 6602 (.ifLtN 6609 6610 .skip (.ifLtN 6610 6609 .skip lxHit)) .skip)
      (block [.addN 6606 6606 6605]))

/-- **The merge**: the parent index `IL[j]` of every child entry `GC[j]`. -/
def lxProg : Stmt :=
  .seq (block [.constN 6605 1, .constN 6606 0, .constN 6607 0]) (.whileLtN 6606 6600 lxBody)

theorem lxHit_exec (c : Config) (hc : WordsBounded W c) {ILb i j : ℕ}
    (r4 : c.nreg 6604 = ILb) (r5 : c.nreg 6605 = 1) (r6 : c.nreg 6606 = i)
    (r7 : c.nreg 6607 = j) (w1 : ILb + j ≤ W) (w2 : j + 1 ≤ W) :
    ∃ c' t, Exec P W lxHit c c' t ∧ t = 3 ∧ c'.nreg 6607 = j + 1 ∧
      c'.nmem = upd c.nmem (ILb + j) i ∧
      (∀ x, x ≠ 6607 → x ≠ 6608 → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lxHit
  exec_block
  all_goals try (config_simp; simp only [r4, r5, r6, r7]; omega)
  refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r5, r7]
  · config_simp; simp only [r4, r6, r7]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

theorem lxBody_exec (c : Config) (hc : WordsBounded W c) {GPb mc GCb ILb i j : ℕ}
    (r1 : c.nreg 6601 = GPb) (r2 : c.nreg 6602 = mc) (r3 : c.nreg 6603 = GCb)
    (r4 : c.nreg 6604 = ILb) (r5 : c.nreg 6605 = 1) (r6 : c.nreg 6606 = i)
    (r7 : c.nreg 6607 = j) (w1 : GPb + i ≤ W) (w2 : GCb + j ≤ W) (w3 : ILb + j ≤ W)
    (w4 : i + 1 ≤ W) (w5 : j + 1 ≤ W) :
    ∃ c' t, Exec P W lxBody c c' t ∧ t ≤ 13 ∧ c'.nreg 6606 = i + 1 ∧
      c'.nreg 6607 = (if j < mc ∧ c.nmem (GCb + j) = c.nmem (GPb + i) then j + 1 else j) ∧
      c'.nmem = (if j < mc ∧ c.nmem (GCb + j) = c.nmem (GPb + i) then upd c.nmem (ILb + j) i
        else c.nmem) ∧
      (∀ x, (x < 6606 ∨ 6610 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lxBody
  obtain ⟨c₁, k₁, e₁, hk₁, g9, g10, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.addN 6608 6601 6606, .loadN 6609 6608, .addN 6608 6603 6607,
        .loadN 6610 6608]) c c₁ k₁ ∧ k₁ = 4 ∧
      c₁.nreg 6609 = c.nmem (GPb + i) ∧ c₁.nreg 6610 = c.nmem (GCb + j) ∧
      (∀ x, x ≠ 6608 → x ≠ 6609 → x ≠ 6610 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try (config_simp; simp only [r1, r3, r6, r7]; omega)
    refine ⟨rfl, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [r1, r6]
    · config_simp; simp only [r3, r7]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q1 : ∀ x, x ≠ 6608 → x ≠ 6609 → x ≠ 6610 → c₁.nreg x = c.nreg x := gn₁
  -- the increment of `i`, from any state
  have inc : ∀ d : Config, WordsBounded W d → d.nreg 6606 = i → d.nreg 6605 = 1 →
      ∃ d' t, Exec P W (block [.addN 6606 6606 6605]) d d' t ∧ t = 1 ∧ d'.nreg 6606 = i + 1 ∧
        (∀ x, x ≠ 6606 → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem ∧ d'.rreg = d.rreg ∧
        d'.rmem = d.rmem ∧ d'.output = d.output := fun d hd s6 s5 => by
    exec_block
    all_goals try (config_simp; simp only [s5, s6]; omega)
    refine ⟨rfl, ?_, fun x a => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp; simp only [s5, s6]
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have s5 : c₁.nreg 6605 = 1 := by rw [q1 _ (by omega) (by omega) (by omega), r5]
  have s6 : c₁.nreg 6606 = i := by rw [q1 _ (by omega) (by omega) (by omega), r6]
  have s7 : c₁.nreg 6607 = j := by rw [q1 _ (by omega) (by omega) (by omega), r7]
  have s2 : c₁.nreg 6602 = mc := by rw [q1 _ (by omega) (by omega) (by omega), r2]
  have s4 : c₁.nreg 6604 = ILb := by rw [q1 _ (by omega) (by omega) (by omega), r4]
  by_cases hj : j < mc
  · have t0 : c₁.nreg 6607 < c₁.nreg 6602 := by rw [s7, s2]; exact hj
    rcases lt_trichotomy (c.nmem (GPb + i)) (c.nmem (GCb + j)) with hlt | heq | hgt
    · -- `gp < gc`: no hit
      have hne : ¬ (j < mc ∧ c.nmem (GCb + j) = c.nmem (GPb + i)) := fun h => by omega
      obtain ⟨c₃, k₃, e₃, hk₃, h6, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₁ hw₁ s6 s5
      have t1 : c₁.nreg 6609 < c₁.nreg 6610 := by rw [g9, g10]; exact hlt
      refine ⟨c₃, k₁ + ((0 + 1) + 1 + k₃),
        .seq e₁ (.seq (.ifLtN_true t0 (.ifLtN_true t1 (.skip hw₁))) e₃), by omega, h6,
        by rw [iteF hne, gn₃ _ (by omega), s7], by rw [iteF hne, gm₃, gm₁], fun x hx => ?_,
        by rw [gr₃, gr₁], by rw [grm₃, grm₁], by rw [go₃, go₁]⟩
      rw [gn₃ x (by omega), q1 x (by omega) (by omega) (by omega)]
    · -- `gp = gc`: the hit
      have hyes : j < mc ∧ c.nmem (GCb + j) = c.nmem (GPb + i) := ⟨hj, heq.symm⟩
      have t1 : ¬ c₁.nreg 6609 < c₁.nreg 6610 := by rw [g9, g10]; omega
      have t2 : ¬ c₁.nreg 6610 < c₁.nreg 6609 := by rw [g9, g10]; omega
      obtain ⟨c₂, k₂, e₂, hk₂, h7, gm₂, gn₂, gr₂, grm₂, go₂⟩ :=
        lxHit_exec (P := P) c₁ hw₁ s4 s5 s6 s7 w3 w5
      obtain ⟨c₃, k₃, e₃, hk₃, h6, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₂ e₂.wb_right
        (by rw [gn₂ _ (by omega) (by omega), s6]) (by rw [gn₂ _ (by omega) (by omega), s5])
      refine ⟨c₃, k₁ + ((k₂ + 2 + 2) + 1 + k₃),
        .seq e₁ (.seq (.ifLtN_true t0 (.ifLtN_false t1 (.ifLtN_false t2 e₂))) e₃), by omega, h6,
        by rw [iteT hyes, gn₃ _ (by omega), h7], by rw [iteT hyes, gm₃, gm₂, gm₁],
        fun x hx => ?_, by rw [gr₃, gr₂, gr₁], by rw [grm₃, grm₂, grm₁], by rw [go₃, go₂, go₁]⟩
      rw [gn₃ x (by omega), gn₂ x (by omega) (by omega), q1 x (by omega) (by omega) (by omega)]
    · -- `gc < gp`: no hit
      have hne : ¬ (j < mc ∧ c.nmem (GCb + j) = c.nmem (GPb + i)) := fun h => by omega
      obtain ⟨c₃, k₃, e₃, hk₃, h6, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₁ hw₁ s6 s5
      have t1 : ¬ c₁.nreg 6609 < c₁.nreg 6610 := by rw [g9, g10]; omega
      have t2 : c₁.nreg 6610 < c₁.nreg 6609 := by rw [g9, g10]; exact hgt
      refine ⟨c₃, k₁ + (((0 + 1) + 2) + 1 + k₃),
        .seq e₁ (.seq (.ifLtN_true t0 (.ifLtN_false t1 (.ifLtN_true t2 (.skip hw₁)))) e₃),
        by omega, h6, by rw [iteF hne, gn₃ _ (by omega), s7], by rw [iteF hne, gm₃, gm₁],
        fun x hx => ?_, by rw [gr₃, gr₁], by rw [grm₃, grm₁], by rw [go₃, go₁]⟩
      rw [gn₃ x (by omega), q1 x (by omega) (by omega) (by omega)]
  · have hne : ¬ (j < mc ∧ c.nmem (GCb + j) = c.nmem (GPb + i)) := fun h => hj h.1
    have t0 : ¬ c₁.nreg 6607 < c₁.nreg 6602 := by rw [s7, s2]; exact hj
    obtain ⟨c₃, k₃, e₃, hk₃, h6, gn₃, gm₃, gr₃, grm₃, go₃⟩ := inc c₁ hw₁ s6 s5
    refine ⟨c₃, k₁ + ((0 + 2) + k₃), .seq e₁ (.seq (.ifLtN_false t0 (.skip hw₁)) e₃),
      by omega, h6, by rw [iteF hne, gn₃ _ (by omega), s7], by rw [iteF hne, gm₃, gm₁],
      fun x hx => ?_, by rw [gr₃, gr₁], by rw [grm₃, grm₁], by rw [go₃, go₁]⟩
    rw [gn₃ x (by omega), q1 x (by omega) (by omega) (by omega)]

/-- **The merge** (see the module docstring): within `15 m + 5` steps, `IL[k] < m` and
`GP[IL[k]] = GC[k]` for every `k < mc`; memory outside `[ILb, ILb + mc)`, registers outside
`6605 … 6610`, reals and output kept. -/
theorem lxProg_exec (c : Config) (hc : WordsBounded W c) {m GPb mc GCb ILb : ℕ}
    (r0 : c.nreg 6600 = m) (r1 : c.nreg 6601 = GPb) (r2 : c.nreg 6602 = mc)
    (r3 : c.nreg 6603 = GCb) (r4 : c.nreg 6604 = ILb)
    (w1 : GPb + m ≤ W) (w2 : GCb + mc ≤ W) (w3 : ILb + mc ≤ W) (w4 : m + 1 ≤ W)
    (w5 : mc + 1 ≤ W)
    (d1 : ILb + mc ≤ GPb ∨ GPb + m ≤ ILb) (d2 : ILb + mc ≤ GCb ∨ GCb + mc ≤ ILb)
    (hp : ∀ i j, i < j → j < m → c.nmem (GPb + i) < c.nmem (GPb + j))
    (hq : ∀ k k', k < k' → k' < mc → c.nmem (GCb + k) < c.nmem (GCb + k'))
    (hex : ∀ k < mc, ∃ i < m, c.nmem (GPb + i) = c.nmem (GCb + k)) :
    ∃ c' t, Exec P W lxProg c c' t ∧ t ≤ 15 * m + 5 ∧
      (∀ k < mc, c'.nmem (ILb + k) < m ∧ c.nmem (GPb + c'.nmem (ILb + k)) = c.nmem (GCb + k)) ∧
      (∀ a, ¬ (ILb ≤ a ∧ a < ILb + mc) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6605 ∨ 6610 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lxProg
  obtain ⟨c₁, k₁, e₁, hk₁, g5, g6, g7, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6605 1, .constN 6606 0, .constN 6607 0]) c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 6605 = 1 ∧ c₁.nreg 6606 = 0 ∧ c₁.nreg 6607 = 0 ∧
      (∀ x, x ≠ 6605 → x ≠ 6606 → x ≠ 6607 → c₁.nreg x = c.nreg x) ∧
      c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, ?_, fun x a b d => ?_, rfl, rfl, rfl, rfl⟩
    all_goals config_simp
    simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, (x < 6605 ∨ 6607 < x) → c₁.nreg x = c.nreg x := fun x hx =>
    gn₁ x (by omega) (by omega) (by omega)
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6606 ∨ 6610 < x) → c'.nreg x = c₁.nreg x) ∧ c'.nreg 6607 ≤ mc ∧
    (∀ k < c'.nreg 6607, c'.nmem (ILb + k) < i ∧ m₀ (GPb + c'.nmem (ILb + k)) = m₀ (GCb + k)) ∧
    (∀ k, c'.nreg 6607 ≤ k → k < mc → ∀ i' < i, m₀ (GPb + i') ≠ m₀ (GCb + k)) ∧
    (∀ a, ¬ (ILb ≤ a ∧ a < ILb + mc) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h76, j1, j2, j3, j4, j5, j6, j7, j8⟩ := lnRange (P := P)
    (a := 6606) (b := 6600) (body := lxBody) J (B := 13) c₁ hw₁ g6 (by rw [q _ (by omega), r0])
    (Nat.zero_le m) ⟨fun _ _ => rfl, by rw [g7]; omega, fun k hk => absurd hk (by omega),
      fun k _ _ i' hi' => absurd hi' (by omega), fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h76 h70 ⟨j1, j2, j3, j4, j5, j6, j7, j8⟩ => by
      have f : ∀ x, (x < 6606 ∨ 6610 < x) → c'.nreg x = c₁.nreg x := j1
      set j := c'.nreg 6607 with hjdef
      have eP : c'.nmem (GPb + i) = m₀ (GPb + i) := j5 _ (by omega)
      obtain ⟨c'', t, ex, ht, h76', h77', hm', hn', hr', hrm', ho'⟩ := lxBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega), r3])
        (by rw [f _ (by omega), q _ (by omega), r4])
        (by rw [f _ (by omega), g5]) h76 rfl (by omega) (by omega) (by omega) (by omega)
        (by omega)
      refine ⟨c'', t, ex, ht, h76', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], ?_, ?_, ?_, ?_, by rw [hr', j6], by rw [hrm', j7],
        by rw [ho', j8]⟩
      · rw [h77']; split_ifs with hc <;> omega
      · by_cases hhit : j < mc ∧ c'.nmem (GCb + j) = c'.nmem (GPb + i)
        · have eC : c'.nmem (GCb + j) = m₀ (GCb + j) := j5 _ (by omega)
          rw [h77', iteT hhit, hm', iteT hhit]
          intro k hk
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
          · rw [upd_other _ _ _ (by omega)]
            obtain ⟨a1, a2⟩ := j3 k hk
            exact ⟨by omega, a2⟩
          · rw [upd_same]
            exact ⟨by omega, by rw [← eP, ← hhit.2, eC]⟩
        · rw [h77', iteF hhit, hm', iteF hhit]
          intro k hk
          obtain ⟨a1, a2⟩ := j3 k hk
          exact ⟨by omega, a2⟩
      · by_cases hhit : j < mc ∧ c'.nmem (GCb + j) = c'.nmem (GPb + i)
        · have eC : c'.nmem (GCb + j) = m₀ (GCb + j) := j5 _ (by omega)
          rw [h77', iteT hhit]
          intro k hk1 hk2 i' hi'
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
          · exact j4 k (by omega) hk2 i' hi'
          · have := hq j k (by omega) hk2
            rw [← eP, ← hhit.2, eC]; omega
        · rw [h77', iteF hhit]
          intro k hk1 hk2 i' hi'
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
          · exact j4 k hk1 hk2 i' hi'
          · intro hEq
            rcases Nat.lt_or_ge j k with hjk | hjk
            · -- `GC[j] < GC[k] = GP[i']`: `GC[j]` was found below `i'`
              obtain ⟨i'', hi'', he''⟩ := hex j (by omega)
              have h1 := hq j k hjk hk2
              rcases lt_trichotomy i'' i' with h | h | h
              · exact j4 j le_rfl (by omega) i'' h he''
              · subst h
                have eC : c'.nmem (GCb + j) = m₀ (GCb + j) := j5 _ (by omega)
                omega
              · have := hp i' i'' h hi''; omega
            · have hk : k = j := by omega
              rw [hk] at hk2 hEq
              have eC : c'.nmem (GCb + j) = m₀ (GCb + j) := j5 _ (by omega)
              exact hhit ⟨hk2, by rw [eC, eP]; exact hEq.symm⟩
      · intro a ha
        rw [hm']
        split_ifs
        · rw [upd_other _ _ _ (fun h => ha ⟨by omega, by omega⟩)]; exact j5 a ha
        · exact j5 a ha)
  have hjm : c₂.nreg 6607 = mc := by
    by_contra hne
    obtain ⟨i', hi', he'⟩ := hex (c₂.nreg 6607) (by omega)
    exact j4 _ le_rfl (by omega) i' hi' he'
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, fun k hk => j3 k (by omega), j5,
    fun x hx => ?_, by rw [j6, gr₁], by rw [j7, grm₁], by rw [j8, go₁]⟩
  rw [j1 x (by omega), q x (by omega)]

/-! ### The copy-scatter -/

/-- `OUT[IX[j]] := V[j]`. -/
def lcsBody : Stmt :=
  block [.addN 6625 6621 6624, .loadN 6625 6625, .addN 6625 6623 6625, .addN 6626 6622 6624,
    .loadN 6626 6626, .storeN 6625 6626, .addN 6624 6624 6627]

/-- **The copy-scatter** `OUT[IX[j]] := V[j]`, `j < mc`. -/
def lcsProg : Stmt :=
  .seq (block [.constN 6627 1, .constN 6624 0]) (.whileLtN 6624 6620 lcsBody)

theorem lcsBody_exec (c : Config) (hc : WordsBounded W c) {IXb Vb OUTb j : ℕ}
    (r1 : c.nreg 6621 = IXb) (r2 : c.nreg 6622 = Vb) (r3 : c.nreg 6623 = OUTb)
    (r7 : c.nreg 6627 = 1) (r4 : c.nreg 6624 = j)
    (w1 : IXb + j ≤ W) (w2 : Vb + j ≤ W) (w3 : OUTb + c.nmem (IXb + j) ≤ W) (w4 : j + 1 ≤ W) :
    ∃ c' k, Exec P W lcsBody c c' k ∧ k = 7 ∧ c'.nreg 6624 = j + 1 ∧
      c'.nmem = upd c.nmem (OUTb + c.nmem (IXb + j)) (c.nmem (Vb + j)) ∧
      (∀ x, (x < 6624 ∨ 6626 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lcsBody
  exec_block
  all_goals try (config_simp; simp only [r1, r2, r3, r4, r7]; omega)
  refine ⟨rfl, ?_, ?_, fun x hx => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [r4, r7]
  · config_simp; simp only [r1, r2, r3, r4]
  · config_simp; simp only [upd_apply]; split_ifs <;> omega

/-- **The copy-scatter**: with `IX` injective on `[0, mc)`, its targets in `OUT` disjoint from
`IX` and `V`, within `9 mc + 4` steps `OUT[IX[j]] = V[j]` for `j < mc`; the other memory,
registers outside `6624 … 6627`, reals and output kept. -/
theorem lcsProg_exec (c : Config) (hc : WordsBounded W c) {mc IXb Vb OUTb : ℕ}
    (r0 : c.nreg 6620 = mc) (r1 : c.nreg 6621 = IXb) (r2 : c.nreg 6622 = Vb)
    (r3 : c.nreg 6623 = OUTb)
    (w1 : IXb + mc ≤ W) (w2 : Vb + mc ≤ W) (w4 : mc + 1 ≤ W)
    (hIX : ∀ j < mc, OUTb + c.nmem (IXb + j) ≤ W)
    (hinj : ∀ i < mc, ∀ j < mc, c.nmem (IXb + i) = c.nmem (IXb + j) → i = j)
    (d1 : ∀ i < mc, ∀ j < mc, OUTb + c.nmem (IXb + i) ≠ IXb + j)
    (d2 : ∀ i < mc, ∀ j < mc, OUTb + c.nmem (IXb + i) ≠ Vb + j) :
    ∃ c' k, Exec P W lcsProg c c' k ∧ k ≤ 9 * mc + 4 ∧
      (∀ j < mc, c'.nmem (OUTb + c.nmem (IXb + j)) = c.nmem (Vb + j)) ∧
      (∀ a, (∀ j < mc, a ≠ OUTb + c.nmem (IXb + j)) → c'.nmem a = c.nmem a) ∧
      (∀ x, (x < 6624 ∨ 6627 < x) → c'.nreg x = c.nreg x) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold lcsProg
  obtain ⟨c₁, k₁, e₁, hk₁, g7, g4, gn₁, gm₁, gr₁, grm₁, go₁⟩ : ∃ c₁ k₁,
      Exec P W (block [.constN 6627 1, .constN 6624 0]) c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 6627 = 1 ∧ c₁.nreg 6624 = 0 ∧
      (∀ x, x ≠ 6627 → x ≠ 6624 → c₁.nreg x = c.nreg x) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    all_goals try ((try config_simp); omega)
    refine ⟨rfl, ?_, ?_, fun x a b => ?_, rfl, rfl, rfl, rfl⟩
    · config_simp
    · config_simp
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hw₁ := e₁.wb_right
  have q : ∀ x, x ≠ 6627 → x ≠ 6624 → c₁.nreg x = c.nreg x := gn₁
  set m₀ := c.nmem with hm₀
  let J : ℕ → Config → Prop := fun i c' =>
    (∀ x, (x < 6624 ∨ 6626 < x) → c'.nreg x = c₁.nreg x) ∧
    (∀ j < i, c'.nmem (OUTb + m₀ (IXb + j)) = m₀ (Vb + j)) ∧
    (∀ a, (∀ j < i, a ≠ OUTb + m₀ (IXb + j)) → c'.nmem a = m₀ a) ∧
    c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output
  obtain ⟨c₂, k₂, e₂, hk₂, hw₂, h74, j1, j2, j3, j4, j5, j6⟩ := lnRange (P := P) (a := 6624)
    (b := 6620) (body := lcsBody) J (B := 7) c₁ hw₁ g4 (by rw [q _ (by omega) (by omega), r0])
    (Nat.zero_le mc) ⟨fun _ _ => rfl, fun j hj => absurd hj (by omega),
      fun a _ => by rw [gm₁], rfl, rfl, rfl⟩
    (fun i c' hlo hhi hw h74 h70 ⟨j1, j2, j3, j4, j5, j6⟩ => by
      have f : ∀ x, (x < 6624 ∨ 6626 < x) → c'.nreg x = c₁.nreg x := j1
      have e1 : c'.nmem (IXb + i) = m₀ (IXb + i) :=
        j3 _ (fun j hj h => d1 j (by omega) i hhi h.symm)
      have e2 : c'.nmem (Vb + i) = m₀ (Vb + i) :=
        j3 _ (fun j hj h => d2 j (by omega) i hhi h.symm)
      obtain ⟨c'', t, ex, ht, h74', hm', hn', hr', hrm', ho'⟩ := lcsBody_exec (P := P) c' hw
        (by rw [f _ (by omega), q _ (by omega) (by omega), r1])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r2])
        (by rw [f _ (by omega), q _ (by omega) (by omega), r3])
        (by rw [f _ (by omega), g7]) h74 (by omega) (by omega) (by rw [e1]; exact hIX i hhi)
        (by omega)
      rw [e1, e2] at hm'
      refine ⟨c'', t, ex, ht.le, h74', by rw [hn' _ (by omega)]; exact h70,
        fun x hx => by rw [hn' x hx, f x hx], fun j hj => ?_, fun a ha => ?_,
        by rw [hr', j4], by rw [hrm', j5], by rw [ho', j6]⟩
      · rw [hm']
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · rw [upd_other _ _ _ (fun h => by have := hinj j (by omega) i hhi (by omega); omega)]
          exact j2 j hj
        · rw [upd_same]
      · rw [hm', upd_other _ _ _ (ha i (by omega))]
        exact j3 a (fun j hj => ha j (by omega)))
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, j2, j3, fun x hx => ?_, by rw [j4, gr₁],
    by rw [j5, grm₁], by rw [j6, go₁]⟩
  rw [j1 x (by omega), q x (by omega) (by omega)]

end Exec

end BKMNW

end PlanarFlow
