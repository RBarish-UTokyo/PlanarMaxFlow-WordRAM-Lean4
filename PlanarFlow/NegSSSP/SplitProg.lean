module

public import PlanarFlow.NegSSSP.DecM
public import PlanarFlow.NegSSSP.LinNode

/-!
# The split of a piece by the cut of its large component, on the machine

In the large-component case the split of the machine (`PlanarFlow.NegSSSP.splitM`) is
`cutPair P K A₀`: the cut `A₀`, `K \ A₀` of the component `K`, the rest `P \ K` joined to the
smaller part (`splitM_big`). Here it is assembled on the machine from the darts of the piece
numbered `0, …, m - 1` (`IsEnum m e P`), a flag per dart (in `K` or not) and the marks of the cut
read through an index per dart, as `sepRun` leaves them (`sep_run_cutOK`: the darts of `K` marked
`1` at `B₀ + 22 m'` under the numbering `c` of the piece map).

* `joinProg`: counts the darts of `K` and those of `A₀`, then writes a side per dart: for a dart
  of `K` its mark, for a dart of the rest the side of the smaller part (`joinProg_exec`,
  `38 m + 11` steps).
* `joinProg_cutPair`: **the sides written are those of `cutPair P K A₀`**: `0` exactly on the
  first part; `joinProg_splitM`: in the large-component case, those of `splitM`.

Not done here: the flags of the large component (the components of the piece, `pcomp`) and the
index of each dart in the numbering of the piece map; the grouping `grp` of the small-component
case.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace PlanarFlow

namespace NegSSSP

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Monge Finset

variable {P : Input} {W : ℕ}

/-! ### The program -/

/-- Counting: `r788 += [K x]`, `r787 += [K x ∧ mark x = 1]` (`r781` the base of the flags,
`r782` of the indices, `r792` of the marks, `r790 = 2`, `r784` the counter). -/
def jcBody : Stmt :=
  .seq (block [.addN 785 781 784, .loadN 786 785]) <|
  .seq (.ifLtN 786 10 .skip
    (.seq (.instr (.addN 788 788 10)) <|
      .seq (block [.addN 785 782 784, .loadN 786 785, .addN 785 792 786, .loadN 786 785])
        (.ifLtN 786 10 .skip (.ifLtN 786 790 (.instr (.addN 787 787 10)) .skip))))
    (.instr (.addN 784 784 10))

/-- Writing the side of the dart `x` at `Ob + x` (`r783 = Ob`): its mark for a dart of `K`, the
side of the smaller part otherwise (`r789 = 2 a₀`, `r791 = k + 1`). -/
def joBody : Stmt :=
  .seq (block [.addN 785 781 784, .loadN 786 785]) <|
  .seq (.ifLtN 786 10
      (.ifLtN 789 791 (.instr (.constN 786 0)) (.instr (.constN 786 1)))
      (.seq (block [.addN 785 782 784, .loadN 786 785, .addN 785 792 786, .loadN 786 785])
        (.ifLtN 786 10 (.instr (.constN 786 1))
          (.ifLtN 786 790 (.instr (.constN 786 0)) (.instr (.constN 786 1))))))
    (block [.addN 785 783 784, .storeN 785 786, .addN 784 784 10])

/-- **The split by the cut of the large component** (`r780 = m`). -/
def joinProg : Stmt :=
  .seq (block [.constN 790 2, .constN 787 0, .constN 788 0, .constN 784 0]) <|
  .seq (.whileLtN 784 780 jcBody) <|
  .seq (block [.addN 789 787 787, .addN 791 788 10, .constN 784 0]) (.whileLtN 784 780 joBody)

/-- The flag of the dart `x` in the configuration `c`. -/
def jFlag (Kb : ℕ) (c : Config) (x : ℕ) : ℕ := c.nmem (Kb + x)

/-- The mark of the dart `x`, read through its index. -/
def jMark (Ib Zb : ℕ) (c : Config) (x : ℕ) : ℕ := c.nmem (Zb + c.nmem (Ib + x))

/-- The darts of `K` below `i`. -/
def jK (Kb : ℕ) (c : Config) (i : ℕ) : ℕ := ((range i).filter fun x => jFlag Kb c x ≠ 0).card

/-- The darts of `A₀` below `i`. -/
def jA (Kb Ib Zb : ℕ) (c : Config) (i : ℕ) : ℕ :=
  ((range i).filter fun x => jFlag Kb c x ≠ 0 ∧ jMark Ib Zb c x = 1).card

/-- The side written for the dart `x`. -/
def jSide (m Kb Ib Zb : ℕ) (c : Config) (x : ℕ) : ℕ :=
  if jFlag Kb c x = 0 then (if 2 * jA Kb Ib Zb c m ≤ jK Kb c m then 0 else 1)
  else if jMark Ib Zb c x = 1 then 0 else 1

/-- The registers of `joinProg`. -/
structure JoinIn (m Kb Ib Ob Zb : ℕ) (c : Config) : Prop where
  r10 : c.nreg 10 = 1
  r780 : c.nreg 780 = m
  r781 : c.nreg 781 = Kb
  r782 : c.nreg 782 = Ib
  r783 : c.nreg 783 = Ob
  r792 : c.nreg 792 = Zb

/-- The layout of `joinProg`: the output `[Ob, Ob + m)` apart from the flags `[Kb, Kb + m)`, the
indices `[Ib, Ib + m)` and the marks read. -/
structure JoinLay (m Kb Ib Ob Zb W : ℕ) (c : Config) : Prop where
  oK : Ob + m ≤ Kb ∨ Kb + m ≤ Ob
  oI : Ob + m ≤ Ib ∨ Ib + m ≤ Ob
  oZ : ∀ x < m, c.nmem (Kb + x) ≠ 0 →
    (Zb + c.nmem (Ib + x) < Ob ∨ Ob + m ≤ Zb + c.nmem (Ib + x))
  wZ : ∀ x < m, c.nmem (Kb + x) ≠ 0 → Zb + c.nmem (Ib + x) ≤ W
  wK : Kb + m ≤ W
  wI : Ib + m ≤ W
  wO : Ob + m ≤ W
  wm : 2 * m + 2 ≤ W

/-- The frame of `joinProg`. -/
structure JFr (c c' : Config) : Prop where
  nreg : ∀ r, r < 784 ∨ 792 ≤ r → c'.nreg r = c.nreg r
  rreg : c'.rreg = c.rreg
  rmem : c'.rmem = c.rmem
  out : c'.output = c.output

theorem JFr.trans {c c' c'' : Config} (h : JFr c c') (h' : JFr c' c'') : JFr c c'' :=
  ⟨fun r hr => (h'.nreg r hr).trans (h.nreg r hr), h'.rreg.trans h.rreg, h'.rmem.trans h.rmem,
    h'.out.trans h.out⟩

lemma filter_range_succ_card (p : ℕ → Prop) [DecidablePred p] (i : ℕ) :
    ((range (i + 1)).filter p).card = ((range i).filter p).card + if p i then 1 else 0 := by
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => by simp at h')]
  · rfl

/-- One step of the count. -/
theorem jcBody_exec {Kb Ib Zb i : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (e781 : c₁.nreg 781 = Kb) (e782 : c₁.nreg 782 = Ib) (e792 : c₁.nreg 792 = Zb)
    (e10 : c₁.nreg 10 = 1) (e790 : c₁.nreg 790 = 2) (ha : c₁.nreg 784 = i)
    (wK : Kb + i ≤ W) (wI : Ib + i ≤ W) (wZ : c₁.nmem (Kb + i) ≠ 0 → Zb + c₁.nmem (Ib + i) ≤ W)
    (w7 : c₁.nreg 787 + 1 ≤ W) (w8 : c₁.nreg 788 + 1 ≤ W) (wi : i + 1 ≤ W) :
    ∃ c' s, Exec P W jcBody c₁ c' s ∧ s ≤ 16 ∧ c'.nreg 784 = i + 1 ∧
      c'.nreg 788 = c₁.nreg 788 + (if c₁.nmem (Kb + i) ≠ 0 then 1 else 0) ∧
      c'.nreg 787 = c₁.nreg 787 +
        (if c₁.nmem (Kb + i) ≠ 0 ∧ c₁.nmem (Zb + c₁.nmem (Ib + i)) = 1 then 1 else 0) ∧
      (∀ r, r < 784 ∨ 788 < r → c'.nreg r = c₁.nreg r) ∧ c'.nmem = c₁.nmem ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  unfold jcBody
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [e781, ha]); omega)
  refine spec_seq ?_
  by_cases hz : c₁.nmem (Kb + i) = 0
  · refine spec_ifLtN_true (by config_simp; simp only [e781, e10, ha, hz]; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› 784 784 10 (by config_simp; simp only [e10, ha]; omega))
      fun _ => ?_
    config_simp
    simp only [e10, ha, hz]
    and_intros
    all_goals first | omega |
      (intro r hr; simp only [upd_apply]; split_ifs <;> omega) | simp
  · refine spec_ifLtN_false (by config_simp; simp only [e781, e10, ha]; omega) ?_
    refine spec_seq ?_
    refine spec_instr (Exec.addN ‹_› 788 788 10 (by config_simp; simp only [e10]; omega))
      fun _ => ?_
    refine spec_seq ?_
    have wZ' := wZ hz
    exec_block
    all_goals try ((try config_simp); (try simp only [e781, e782, e792, e10, ha]); omega)
    by_cases hm0 : c₁.nmem (Zb + c₁.nmem (Ib + i)) = 0
    · refine spec_ifLtN_true (by config_simp; simp only [e782, e792, e10, ha, hm0]; omega) ?_
      refine spec_skip ‹_› ?_
      refine spec_instr (Exec.addN ‹_› 784 784 10 (by config_simp; simp only [e10, ha]; omega))
        fun _ => ?_
      config_simp
      simp only [e10, ha, hz, hm0]
      and_intros
      all_goals first | omega |
        (intro r hr; simp only [upd_apply]; split_ifs <;> omega) | simp
    · refine spec_ifLtN_false (by config_simp; simp only [e782, e792, e10, ha]; omega) ?_
      by_cases hm1 : c₁.nmem (Zb + c₁.nmem (Ib + i)) = 1
      · refine spec_ifLtN_true (by config_simp; simp only [e782, e792, e790, ha, hm1]; omega) ?_
        refine spec_instr (Exec.addN ‹_› 787 787 10 (by config_simp; simp only [e10]; omega))
          fun _ => ?_
        refine spec_instr (Exec.addN ‹_› 784 784 10 (by config_simp; simp only [e10, ha]; omega))
          fun _ => ?_
        config_simp
        simp only [e10, ha, hz, hm1]
        and_intros
        all_goals first | omega |
          (intro r hr; simp only [upd_apply]; split_ifs <;> omega) | simp
      · refine spec_ifLtN_false (by config_simp; simp only [e782, e792, e790, ha]; omega) ?_
        refine spec_skip ‹_› ?_
        refine spec_instr (Exec.addN ‹_› 784 784 10 (by config_simp; simp only [e10, ha]; omega))
          fun _ => ?_
        config_simp
        simp only [e10, ha, hz, hm1]
        and_intros
        all_goals first | omega |
          (intro r hr; simp only [upd_apply]; split_ifs <;> omega) | simp

/-- One step of the writing of the sides. -/
theorem joBody_exec {Kb Ib Ob Zb i : ℕ} (c₁ : Config) (hw : WordsBounded W c₁)
    (e781 : c₁.nreg 781 = Kb) (e782 : c₁.nreg 782 = Ib) (e783 : c₁.nreg 783 = Ob)
    (e792 : c₁.nreg 792 = Zb) (e10 : c₁.nreg 10 = 1) (e790 : c₁.nreg 790 = 2)
    (ha : c₁.nreg 784 = i) (wK : Kb + i ≤ W) (wI : Ib + i ≤ W) (wO : Ob + i ≤ W)
    (wZ : c₁.nmem (Kb + i) ≠ 0 → Zb + c₁.nmem (Ib + i) ≤ W) (wi : i + 1 ≤ W) :
    ∃ c' s, Exec P W joBody c₁ c' s ∧ s ≤ 16 ∧ c'.nreg 784 = i + 1 ∧
      (∀ r, r < 784 ∨ 786 < r → c'.nreg r = c₁.nreg r) ∧
      c'.nmem = upd c₁.nmem (Ob + i)
        (if c₁.nmem (Kb + i) = 0 then (if c₁.nreg 789 < c₁.nreg 791 then 0 else 1)
          else if c₁.nmem (Zb + c₁.nmem (Ib + i)) = 1 then 0 else 1) ∧
      c'.rreg = c₁.rreg ∧ c'.rmem = c₁.rmem ∧ c'.output = c₁.output := by
  unfold joBody
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [e781, ha]); omega)
  refine spec_seq ?_
  by_cases hz : c₁.nmem (Kb + i) = 0
  · refine spec_ifLtN_true (by config_simp; simp only [e781, e10, ha, hz]; omega) ?_
    by_cases hs : c₁.nreg 789 < c₁.nreg 791
    · refine spec_ifLtN_true (by config_simp; exact hs) ?_
      refine spec_instr (Exec.constN ‹_› 786 0 (by omega)) fun _ => ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e783, e10, ha]); omega)
      config_simp
      simp only [e783, e10, ha, hz, hs]
      and_intros
      all_goals first | omega |
        (intro r hr; simp only [upd_apply]; split_ifs <;> omega) | simp
    · refine spec_ifLtN_false (by config_simp; exact hs) ?_
      refine spec_instr (Exec.constN ‹_› 786 1 (by omega)) fun _ => ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e783, e10, ha]); omega)
      config_simp
      simp only [e783, e10, ha, hz, hs]
      and_intros
      all_goals first | omega |
        (intro r hr; simp only [upd_apply]; split_ifs <;> omega) | simp
  · refine spec_ifLtN_false (by config_simp; simp only [e781, e10, ha]; omega) ?_
    have wZ' := wZ hz
    refine spec_seq ?_
    exec_block
    all_goals try ((try config_simp); (try simp only [e781, e782, e792, ha]); omega)
    by_cases hm0 : c₁.nmem (Zb + c₁.nmem (Ib + i)) = 0
    · refine spec_ifLtN_true (by config_simp; simp only [e782, e792, e10, ha, hm0]; omega) ?_
      refine spec_instr (Exec.constN ‹_› 786 1 (by omega)) fun _ => ?_
      exec_block
      all_goals try ((try config_simp); (try simp only [e783, e10, ha]); omega)
      config_simp
      simp only [e782, e783, e792, e10, ha, hz, hm0]
      and_intros
      all_goals first | omega |
        (intro r hr; simp only [upd_apply]; split_ifs <;> omega) | simp
    · refine spec_ifLtN_false (by config_simp; simp only [e782, e792, e10, ha]; omega) ?_
      by_cases hm1 : c₁.nmem (Zb + c₁.nmem (Ib + i)) = 1
      · refine spec_ifLtN_true (by config_simp; simp only [e782, e792, e790, ha, hm1]; omega) ?_
        refine spec_instr (Exec.constN ‹_› 786 0 (by omega)) fun _ => ?_
        exec_block
        all_goals try ((try config_simp); (try simp only [e783, e10, ha]); omega)
        config_simp
        simp only [e782, e783, e792, e10, ha, hz, hm1]
        and_intros
        all_goals first | omega |
          (intro r hr; simp only [upd_apply]; split_ifs <;> omega) | simp
      · refine spec_ifLtN_false (by config_simp; simp only [e782, e792, e790, ha]; omega) ?_
        refine spec_instr (Exec.constN ‹_› 786 1 (by omega)) fun _ => ?_
        exec_block
        all_goals try ((try config_simp); (try simp only [e783, e10, ha]); omega)
        config_simp
        simp only [e782, e783, e792, e10, ha, hz, hm1]
        and_intros
        all_goals first | omega |
          (intro r hr; simp only [upd_apply]; split_ifs <;> omega) | simp

lemma jA_le (Kb Ib Zb : ℕ) (c : Config) (i : ℕ) : jA Kb Ib Zb c i ≤ i :=
  (card_filter_le _ _).trans (card_range i).le

lemma jK_le (Kb : ℕ) (c : Config) (i : ℕ) : jK Kb c i ≤ i :=
  (card_filter_le _ _).trans (card_range i).le

/-- **The split by the cut of the large component on the machine.** From the flags of the darts
`x < m` at `Kb + x` (`≠ 0` for a dart of `K`) and their marks `Z[I[x]]` (`1` for a dart of the
first part of the cut), `joinProg` counts the darts `k` of `K` and `a₀` of the first part, and
writes at `Ob + x` the side `jSide`: for a dart of `K`, `0` exactly when its mark is `1`; for a
dart of the rest, `0` exactly when `2 a₀ ≤ k`. Within `38 m + 11` steps. -/
theorem joinProg_exec {m Kb Ib Ob Zb : ℕ} (c : Config) (hc : WordsBounded W c)
    (hL : JoinLay m Kb Ib Ob Zb W c) (hI : JoinIn m Kb Ib Ob Zb c) :
    ∃ c' t, Exec P W joinProg c c' t ∧ t ≤ 38 * m + 11 ∧
      (∀ x < m, c'.nmem (Ob + x) = jSide m Kb Ib Zb c x) ∧
      (∀ a, (a < Ob ∨ Ob + m ≤ a) → c'.nmem a = c.nmem a) ∧ JFr c c' := by
  have := hL.oK; have := hL.oI; have := hL.wK; have := hL.wI; have := hL.wO; have := hL.wm
  unfold joinProg
  refine spec_seq ?_
  exec_block
  all_goals try omega
  -- the count
  let J : ℕ → Config → Prop := fun i c' =>
    JFr c c' ∧ c'.nmem = c.nmem ∧ c'.nreg 790 = 2 ∧ c'.nreg 787 = jA Kb Ib Zb c i ∧
      c'.nreg 788 = jK Kb c i
  refine spec_seq ?_
  refine spec_use (forLoop_exec (P := P) (a := 784) (bR := 780) (body := jcBody) J (K := 16)
    (n := m) _ ‹_› (by config_simp) (by config_simp; exact hI.r780) ?_
    (fun i c₁ hi hw ha hb ⟨fr, fm, f790, f787, f788⟩ => ?_)) ?_
  · refine ⟨⟨fun r hr => ?_, rfl, rfl, rfl⟩, rfl, by config_simp, by config_simp; simp [jA],
      by config_simp; simp [jK]⟩
    config_simp; simp only [upd_apply]; split_ifs <;> omega
  · have g : ∀ r, r < 784 → c₁.nreg r = c.nreg r := fun r hr => fr.nreg r (by omega)
    have e781 := (g 781 (by omega)).trans hI.r781
    have e782 := (g 782 (by omega)).trans hI.r782
    have e792 := (fr.nreg 792 (by omega)).trans hI.r792
    have e10 := (g 10 (by omega)).trans hI.r10
    have hA := jA_le Kb Ib Zb c i
    have hK := jK_le Kb c i
    obtain ⟨c', s, hex, hs, h784, h788, h787, hreg, hmem, hrr, hrm, hout⟩ :=
      jcBody_exec (P := P) c₁ hw e781 e782 e792 e10 f790 ha (by omega) (by omega)
        (fun h => by rw [fm] at h ⊢; exact hL.wZ i hi h) (by omega) (by omega) (by omega)
    refine ⟨c', s, hex, hs, h784, by rw [hreg 780 (by omega)]; exact hb,
      fr.trans ⟨fun r hr => hreg r (by omega), hrr, hrm, hout⟩, hmem.trans fm,
      by rw [hreg 790 (by omega)]; exact f790, ?_, ?_⟩
    · rw [h787, f787, fm]
      unfold jA
      rw [filter_range_succ_card]
      rfl
    · rw [h788, f788, fm]
      unfold jK
      rw [filter_range_succ_card]
      rfl
  intro c₂ k₂ hk₂ hw₂ ⟨_, fr₂, fm₂, f790₂, f787₂, f788₂⟩
  have hA := jA_le Kb Ib Zb c m
  have hK := jK_le Kb c m
  have e10₂ := (fr₂.nreg 10 (by omega)).trans hI.r10
  refine spec_seq ?_
  exec_block
  all_goals try ((try config_simp); (try simp only [f787₂, f788₂, e10₂]); omega)
  -- the sides
  let J' : ℕ → Config → Prop := fun i c' =>
    JFr c c' ∧ c'.nreg 789 = 2 * jA Kb Ib Zb c m ∧ c'.nreg 791 = jK Kb c m + 1 ∧
      c'.nreg 790 = 2 ∧ (∀ a, (a < Ob ∨ Ob + m ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ x < i, c'.nmem (Ob + x) = jSide m Kb Ib Zb c x)
  refine spec_use (forLoop_exec (P := P) (a := 784) (bR := 780) (body := joBody) J' (K := 16)
    (n := m) _ ‹_› (by config_simp)
    (by config_simp; rw [fr₂.nreg 780 (by omega)]; exact hI.r780) ?_
    (fun i c₁ hi hw ha hb ⟨fr, f789, f791, f790, fo, fv⟩ => ?_)) ?_
  · refine ⟨fr₂.trans ⟨fun r hr => ?_, rfl, rfl, rfl⟩, ?_, ?_, ?_, fun a _ => ?_,
      fun x hx => absurd hx (by omega)⟩
    · config_simp; simp only [upd_apply]; split_ifs <;> omega
    · config_simp; simp only [f787₂]; omega
    · config_simp; simp only [f788₂, e10₂]
    · config_simp; exact f790₂
    · config_simp; rw [fm₂]
  · have g : ∀ r, r < 784 → c₁.nreg r = c.nreg r := fun r hr => fr.nreg r (by omega)
    have e781 := (g 781 (by omega)).trans hI.r781
    have e782 := (g 782 (by omega)).trans hI.r782
    have e783 := (g 783 (by omega)).trans hI.r783
    have e792 := (fr.nreg 792 (by omega)).trans hI.r792
    have e10 := (g 10 (by omega)).trans hI.r10
    have xK : c₁.nmem (Kb + i) = c.nmem (Kb + i) := fo _ (by omega)
    have xI : c₁.nmem (Ib + i) = c.nmem (Ib + i) := fo _ (by omega)
    obtain ⟨c', s, hex, hs, h784, hreg, hmem, hrr, hrm, hout⟩ :=
      joBody_exec (P := P) c₁ hw e781 e782 e783 e792 e10 f790 ha (by omega) (by omega)
        (by omega) (fun h => by rw [xK] at h; rw [xI]; exact hL.wZ i hi h) (by omega)
    refine ⟨c', s, hex, hs, h784, by rw [hreg 780 (by omega)]; exact hb,
      fr.trans ⟨fun r hr => hreg r (by omega), hrr, hrm, hout⟩,
      by rw [hreg 789 (by omega)]; exact f789, by rw [hreg 791 (by omega)]; exact f791,
      by rw [hreg 790 (by omega)]; exact f790, fun a ha' => ?_, fun x hx => ?_⟩
    · rw [hmem, upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega)), fo a ha']
    · rw [hmem, upd_apply]
      by_cases hxi : Ob + x = Ob + i
      · have hxi' : x = i := by omega
        subst hxi'
        rw [ite_eq_left_of_eq_true _ _ (eq_true hxi)]
        unfold jSide jFlag jMark
        rw [xK, xI, f789, f791]
        by_cases hz : c.nmem (Kb + x) = 0
        · simp only [hz, ↓reduceIte]
          by_cases h2 : 2 * jA Kb Ib Zb c m ≤ jK Kb c m
          · rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega)),
              ite_eq_left_of_eq_true _ _ (eq_true h2)]
          · rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
              ite_eq_right_of_eq_false _ _ (eq_false h2)]
        · have xZ : c₁.nmem (Zb + c.nmem (Ib + x)) = c.nmem (Zb + c.nmem (Ib + x)) :=
            fo _ (by have := hL.oZ x hi hz; omega)
          simp only [hz, ↓reduceIte, xZ]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hxi), fv x (by omega)]
  intro c₄ k₄ hk₄ hw₄ ⟨_, fr₄, _, _, _, fo₄, fv₄⟩
  exact ⟨by omega, fv₄, fo₄, fr₄⟩

/-! ### The sides are those of `cutPair` -/

section Bridge

variable {D : Type*} [DecidableEq D]

/-- The second part of `cutPair` is the rest of the piece. -/
lemma cutPair_snd {Pc K A₀ : Finset D} (hKP : K ⊆ Pc) (hA : A₀ ⊆ K) :
    (cutPair Pc K A₀).2 = Pc \ (cutPair Pc K A₀).1 := by
  unfold cutPair
  split_ifs
  · ext d; simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨hKP h1, by tauto⟩
    · rintro ⟨h1, h2⟩; exact ⟨by tauto, fun h => h2 (Or.inl h)⟩
  · ext d; simp only [mem_sdiff, mem_union]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨hKP h1, h2⟩
      · exact ⟨h1, fun h => h2 (hA h)⟩
    · rintro ⟨h1, h2⟩
      by_cases h : d ∈ K
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨h1, h⟩

lemma image_filter_enum {Pc S : Finset D} {m : ℕ} {e : ℕ → D} (he : IsEnum m e Pc) (hS : S ⊆ Pc)
    {p : ℕ → Prop} [DecidablePred p] (hp : ∀ x < m, (p x ↔ e x ∈ S)) :
    S.card = ((range m).filter p).card := by
  have : S = ((range m).filter p).image e := by
    ext d
    simp only [mem_image, mem_filter, mem_range]
    constructor
    · intro hd
      obtain ⟨x, hx, rfl⟩ := he.surj d (hS hd)
      exact ⟨x, ⟨hx, (hp x hx).2 hd⟩, rfl⟩
    · rintro ⟨x, ⟨hx, h⟩, rfl⟩
      exact (hp x hx).1 h
  rw [this, card_image_of_injOn fun x hx x' hx' h =>
    he.inj x (by simpa using (mem_filter.1 hx).1) x' (by simpa using (mem_filter.1 hx').1) h]

/-- **The sides written by `joinProg` are those of `cutPair`**: for the darts of the piece `Pc`
numbered by `e`, with the flags of the darts of `K ⊆ Pc` and the marks of the first part
`A₀ ⊆ K`, the side of the dart `x` is `0` exactly when `e x` is in the first part of
`cutPair Pc K A₀` (the second part is the rest, `cutPair_snd`): the split of the machine in the
large-component case (`splitM_big`). -/
theorem joinProg_cutPair {Pc K A₀ : Finset D} {m : ℕ} {e : ℕ → D} (he : IsEnum m e Pc)
    (hKP : K ⊆ Pc) (hA : A₀ ⊆ K) {Kb Ib Zb : ℕ} {c : Config}
    (hK : ∀ x < m, (c.nmem (Kb + x) ≠ 0 ↔ e x ∈ K))
    (hA₀ : ∀ x < m, e x ∈ K → (e x ∈ A₀ ↔ c.nmem (Zb + c.nmem (Ib + x)) = 1)) :
    ∀ x < m, jSide m Kb Ib Zb c x = if e x ∈ (cutPair Pc K A₀).1 then 0 else 1 := by
  have cK : K.card = jK Kb c m := image_filter_enum he hKP fun x hx => hK x hx
  have cA : A₀.card = jA Kb Ib Zb c m := image_filter_enum he (hA.trans hKP) fun x hx => by
    constructor
    · rintro ⟨h1, h2⟩
      have hk := (hK x hx).1 h1
      exact (hA₀ x hx hk).2 h2
    · intro h
      have hk := hA h
      exact ⟨(hK x hx).2 hk, (hA₀ x hx hk).1 h⟩
  have cD : (K \ A₀).card = K.card - A₀.card := card_sdiff_of_subset hA
  have cle : A₀.card ≤ K.card := card_le_card hA
  intro x hx
  unfold jSide jFlag jMark cutPair
  by_cases hk : c.nmem (Kb + x) = 0
  · have hxK : e x ∉ K := fun h => (hK x hx).2 h hk
    have hxA : e x ∉ A₀ := fun h => hxK (hA h)
    have hxP : e x ∈ Pc := he.mem x hx
    by_cases h2 : 2 * jA Kb Ib Zb c m ≤ jK Kb c m
    · have hle : A₀.card ≤ (K \ A₀).card := by omega
      simp only [hk, h2, hle, ↓reduceIte, mem_union, mem_sdiff, hxP, hxK, not_false_eq_true,
        and_self, or_true]
    · have hle : ¬ A₀.card ≤ (K \ A₀).card := by omega
      simp only [hk, h2, hle, ↓reduceIte, hxA]
  · have hxK : e x ∈ K := (hK x hx).1 hk
    have hiff := hA₀ x hx hxK
    by_cases hm : c.nmem (Zb + c.nmem (Ib + x)) = 1
    · have hxA : e x ∈ A₀ := hiff.2 hm
      split_ifs <;> simp_all
    · have hxA : e x ∉ A₀ := fun h => hm (hiff.1 h)
      split_ifs <;> simp_all

end Bridge

section Node

variable {D V F : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F] {N : CombMap D V F}

/-- **The sides written by `joinProg` are those of the split of the machine** in the
large-component case: for a dart `x₀` of a component `K = pcomp N Pc x₀` of more than three
quarters of the darts of the piece and a cut `cut K ⊆ K` (`CutOK` gives it), with the flags of
`K` and the marks of `cut K`, the side of the dart `x` is `0` exactly when `e x` is in the first
part of `splitM N ord cut Pc`. -/
theorem joinProg_splitM {ord : Finset D → List D} (hL : OrdOK ord) (cut : Finset D → Finset D)
    {Pc : Finset D} {x₀ : D} (hx₀ : x₀ ∈ Pc) (hb : 3 * Pc.card / 4 < (pcomp N Pc x₀).card)
    (hA : cut (pcomp N Pc x₀) ⊆ pcomp N Pc x₀) {m : ℕ} {e : ℕ → D} (he : IsEnum m e Pc)
    {Kb Ib Zb : ℕ} {c : Config} (hK : ∀ x < m, (c.nmem (Kb + x) ≠ 0 ↔ e x ∈ pcomp N Pc x₀))
    (hA₀ : ∀ x < m, e x ∈ pcomp N Pc x₀ →
      (e x ∈ cut (pcomp N Pc x₀) ↔ c.nmem (Zb + c.nmem (Ib + x)) = 1)) :
    ∀ x < m, jSide m Kb Ib Zb c x = if e x ∈ (splitM N ord cut Pc).1 then 0 else 1 := by
  rw [splitM_big hL cut hx₀ hb]
  exact joinProg_cutPair he (pcomp_subset Pc x₀) hA hK hA₀

end Node

end NegSSSP

end PlanarFlow
